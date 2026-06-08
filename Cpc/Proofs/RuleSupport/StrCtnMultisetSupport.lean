import Cpc.Proofs.RuleSupport.StrOverlapSupport
import Cpc.Proofs.RuleSupport.SetsEvalOpSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

/-!
Support for `str-ctn-multiset-subset`.

The CPC side condition is a syntactic multiset check.  The helpers below expose
just enough semantic counting to connect it to `str.contains`: if the needle
occurs as a contiguous native sequence, each value occurs in the haystack at
least as often as it does in the needle.
-/

noncomputable def valueCount (v : SmtValue) (xs : List SmtValue) : Nat :=
  xs.countP (fun w => native_veq w v)

noncomputable def seqTermValueCount (M : SmtModel) (v : SmtValue) (t : Term) : Nat :=
  match __smtx_model_eval M (__eo_to_smt t) with
  | SmtValue.Seq s => valueCount v (native_unpack_seq s)
  | _ => 0

noncomputable def eoListSeqValueCount (M : SmtModel) (v : SmtValue) : Term -> Nat
  | Term.Apply (Term.Apply _ x) xs =>
      seqTermValueCount M v x + eoListSeqValueCount M v xs
  | _ => 0

noncomputable def flatSeqValueCount (M : SmtModel) (v : SmtValue) : Term -> Nat
  | Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) xs =>
      seqTermValueCount M v x + flatSeqValueCount M v xs
  | x =>
      if __str_is_empty x = Term.Boolean true then 0 else seqTermValueCount M v x

theorem valueCount_append (v : SmtValue) (xs ys : List SmtValue) :
    valueCount v (xs ++ ys) = valueCount v xs + valueCount v ys := by
  simp [valueCount, List.countP_append]

theorem valueCount_sublist_le {v : SmtValue} {xs ys : List SmtValue}
    (h : xs.Sublist ys) :
    valueCount v xs <= valueCount v ys := by
  simpa [valueCount] using h.countP_le (p := fun w => native_veq w v)

theorem valueCount_take_le (v : SmtValue) (xs : List SmtValue) (n : Nat) :
    valueCount v (xs.take n) <= valueCount v xs :=
  valueCount_sublist_le (List.take_sublist n xs)

theorem valueCount_drop_le (v : SmtValue) (xs : List SmtValue) (n : Nat) :
    valueCount v (xs.drop n) <= valueCount v xs :=
  valueCount_sublist_le (List.drop_sublist n xs)

theorem valueCount_take_add_drop_le (v : SmtValue) :
    ∀ (xs : List SmtValue) (n m : Nat), n ≤ m ->
      valueCount v (xs.take n) + valueCount v (xs.drop m) <= valueCount v xs
  | [], _, _, _ => by simp [valueCount]
  | _ :: xs, 0, m, _ => by
      simp [valueCount]
      exact valueCount_drop_le v (_ :: xs) m
  | a :: xs, n + 1, m + 1, h => by
      have hnm : n ≤ m := Nat.succ_le_succ_iff.mp h
      have ih := valueCount_take_add_drop_le v xs n m hnm
      change valueCount v (a :: xs.take n) + valueCount v (xs.drop m) <=
        valueCount v (a :: xs)
      unfold valueCount at ih ⊢
      rw [List.countP_cons, List.countP_cons]
      by_cases hHead : native_veq a v = true
      · simp [hHead] at ih ⊢
        omega
      · simp [hHead] at ih ⊢
        omega

theorem valueCount_extract_le (v : SmtValue) (xs : List SmtValue) (i n : native_Int) :
    valueCount v (native_seq_extract xs i n) <= valueCount v xs := by
  unfold native_seq_extract
  dsimp only
  by_cases hCond :
      (decide (i < 0) || decide (n ≤ 0) || decide (i ≥ Int.ofNat xs.length)) = true
  · rw [if_pos hCond]
    simp [valueCount]
  · rw [if_neg hCond]
    exact Nat.le_trans (valueCount_take_le v (xs.drop i.toNat) _)
      (valueCount_drop_le v xs i.toNat)

theorem valueCount_replace_le (v : SmtValue) (xs pat repl : List SmtValue) :
    valueCount v (native_seq_replace xs pat repl) <= valueCount v xs + valueCount v repl := by
  cases pat with
  | nil =>
      unfold native_seq_replace
      rw [valueCount_append]
      omega
  | cons p ps =>
      unfold native_seq_replace
      by_cases hIdx : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [hIdx]
      · simp [hIdx]
        let idx := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        rw [valueCount_append, valueCount_append]
        have hSplit :
            valueCount v (xs.take idx) +
              valueCount v (xs.drop (idx + (ps.length + 1))) <= valueCount v xs := by
          simpa [idx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            valueCount_take_add_drop_le v xs idx (idx + (ps.length + 1)) (by omega)
        change valueCount v (xs.take idx) +
            (valueCount v repl + valueCount v (xs.drop (idx + (ps.length + 1)))) <=
          valueCount v xs + valueCount v repl
        omega

theorem valueCount_contains_le {hay needle : List SmtValue}
    (v : SmtValue) (h : native_seq_contains hay needle = true) :
    valueCount v needle <= valueCount v hay := by
  rcases native_seq_contains_decomp_exists hay needle h with ⟨pre, post, rfl⟩
  rw [valueCount_append, valueCount_append]
  omega

theorem valueCount_cons (v x : SmtValue) (xs : List SmtValue) :
    valueCount v (x :: xs) =
      valueCount v xs + if native_veq x v = true then 1 else 0 := by
  simp [valueCount, List.countP_cons]

theorem valueCount_singleton (v x : SmtValue) :
    valueCount v [x] = if native_veq x v = true then 1 else 0 := by
  rw [valueCount_cons]
  simp [valueCount]

theorem seqTermValueCount_atom (M : SmtModel) (v a : SmtValue) (t : Term) (s : SmtSeq)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq s)
    (hUnpack : native_unpack_seq s = [a]) :
    seqTermValueCount M v t = if native_veq a v = true then 1 else 0 := by
  unfold seqTermValueCount
  rw [hEval]
  simp [hUnpack, valueCount_singleton]

theorem seqTermValueCount_of_atom_shape (M : SmtModel) (v a : SmtValue) (t : Term)
    (hShape : (∃ ch, t = Term.String [ch]) ∨
      (∃ e, t = Term.Apply (Term.UOp UserOp.seq_unit) e))
    (hVal : seqElemVal M t = a) :
    seqTermValueCount M v t = if native_veq a v = true then 1 else 0 := by
  rcases hShape with ⟨ch, rfl⟩ | ⟨e, rfl⟩
  · obtain ⟨s, hEval, hUnpack⟩ := eval_charAtom M ch
    exact seqTermValueCount_atom M v a (Term.String [ch]) s hEval (by simpa [hVal] using hUnpack)
  · obtain ⟨s, hEval, hUnpack⟩ := eval_seqUnitAtom M e
    exact seqTermValueCount_atom M v a (Term.Apply (Term.UOp UserOp.seq_unit) e) s hEval
      (by simpa [hVal] using hUnpack)

theorem valueCount_map_seqElemVal_eq_sum (M : SmtModel) (v : SmtValue) :
    ∀ atoms : List Term,
      valueCount v (atoms.map (seqElemVal M)) =
        atoms.foldr (fun a acc =>
          (if native_veq (seqElemVal M a) v = true then 1 else 0) + acc) 0
  | [] => by simp [valueCount]
  | a :: atoms => by
      rw [List.map_cons, valueCount_cons, valueCount_map_seqElemVal_eq_sum M v atoms]
      simp [List.foldr_cons, Nat.add_comm]

theorem flatSeqValueCount_of_empty (M : SmtModel) (v : SmtValue) (e : Term)
    (he : __str_is_empty e = Term.Boolean true) :
    flatSeqValueCount M v e = 0 := by
  rcases str_is_empty_cases e he with ⟨U, rfl⟩ | rfl
  · simp [flatSeqValueCount, __str_is_empty]
  · simp [flatSeqValueCount, __str_is_empty]

theorem flatSeqValueCount_atomChainTerm (M : SmtModel) (v : SmtValue)
    (ex : Term) (hex : __str_is_empty ex = Term.Boolean true) :
    ∀ atoms : List Term,
      (∀ a ∈ atoms, (∃ ch, a = Term.String [ch]) ∨
        (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)) ->
      flatSeqValueCount M v (atomChainTerm atoms ex) =
        atoms.foldr (fun a acc =>
          (if native_veq (seqElemVal M a) v = true then 1 else 0) + acc) 0
  | [], _ => by
      simpa [atomChainTerm] using flatSeqValueCount_of_empty M v ex hex
  | a :: atoms, hShape => by
      rw [atomChainTerm_cons]
      have hTail := flatSeqValueCount_atomChainTerm M v ex hex atoms
        (fun b hb => hShape b (by simp [hb]))
      have hAtomShape : (∃ ch, a = Term.String [ch]) ∨
          (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e) :=
        hShape a (by simp)
      simp [flatSeqValueCount,
        seqTermValueCount_of_atom_shape M v (seqElemVal M a) a hAtomShape rfl,
        hTail, List.foldr_cons]

theorem introWordView_flatSeqValueCount (M : SmtModel) (v : SmtValue)
    (t : Term) (S : SmtSeq) (T : SmtType)
    (vw : IntroWordView M t S T) :
    flatSeqValueCount M v (__str_flatten (__str_nary_intro t)) =
      valueCount v (native_unpack_seq S) := by
  rw [vw.hflat, flatSeqValueCount_atomChainTerm M v vw.ex vw.hexEmpty vw.atoms vw.hAtomShape,
    vw.hunp, valueCount_map_seqElemVal_eq_sum]

theorem str_multiset_overapprox_word_charChain_sound (M : SmtModel) (v : SmtValue) :
    ∀ w : native_String,
      SetsEvalOpSupport.IsTL (__str_multiset_overapprox_word (charChainTerm w)) ∧
        eoListSeqValueCount M v (__str_multiset_overapprox_word (charChainTerm w)) =
          valueCount v (w.map SmtValue.Char)
  | [] => by
      have hWord :
          __str_multiset_overapprox_word (charChainTerm []) =
            Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
              (__eo_typeof (Term.String [])) := by
        change __eo_ite (__str_is_empty (Term.String []))
            (__eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil)
              (__eo_typeof (Term.String [])))
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.String []))
              (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons)
                (__eo_typeof (Term.String [])))) = _
        rw [show __str_is_empty (Term.String []) = Term.Boolean true by rfl, eo_ite_true]
        change __eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil)
            (__eo_typeof (Term.String [])) =
          Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
            (__eo_typeof (Term.String []))
        rw [show __eo_typeof (Term.String []) =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) by rfl]
        rfl
      constructor
      · rw [hWord]
        trivial
      · rw [hWord]
        rfl
  | ch :: rest => by
      obtain ⟨hTailTL, hTailCount⟩ :=
        str_multiset_overapprox_word_charChain_sound M v rest
      have hTailNe :
          __str_multiset_overapprox_word (charChainTerm rest) ≠ Term.Stuck :=
        SetsEvalOpSupport.isTL_ne_stuck hTailTL
      have hCons :
          __str_multiset_overapprox_word (charChainTerm (ch :: rest)) =
            Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.String [ch]))
              (__str_multiset_overapprox_word (charChainTerm rest)) := by
        change __eo_mk_apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.String [ch]))
            (__str_multiset_overapprox_word (charChainTerm rest)) = _
        exact SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hTailNe
      constructor
      · rw [hCons]
        exact ⟨by simp, hTailTL⟩
      · rw [hCons]
        simp [eoListSeqValueCount, hTailCount]
        have hAtom :
            seqTermValueCount M v (Term.String [ch]) =
              if native_veq (SmtValue.Char ch) v = true then 1 else 0 := by
          have hShape : (∃ c, Term.String [ch] = Term.String [c]) ∨
              (∃ e, Term.String [ch] = Term.Apply (Term.UOp UserOp.seq_unit) e) :=
            Or.inl ⟨ch, rfl⟩
          exact seqTermValueCount_of_atom_shape M v (SmtValue.Char ch)
            (Term.String [ch]) hShape rfl
        rw [hAtom, valueCount_cons]
        omega

theorem seqTermValueCount_of_eval_seq (M : SmtModel) (v : SmtValue)
    (t : Term) (s : SmtSeq)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq s) :
    seqTermValueCount M v t = valueCount v (native_unpack_seq s) := by
  unfold seqTermValueCount
  rw [hEval]

theorem seqTermValueCount_eval_nil_of_empty (M : SmtModel) (v : SmtValue)
    (t : Term) (s : SmtSeq)
    (hEmpty : __str_is_empty t = Term.Boolean true)
    (hEval : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq s) :
    seqTermValueCount M v t = 0 := by
  rw [seqTermValueCount_of_eval_seq M v t s hEval]
  rw [str_is_empty_eval_unpack_nil M t s hEmpty hEval]
  rfl

theorem eoListSeqValueCount_cons (M : SmtModel) (v : SmtValue)
    (f x xs : Term) :
    eoListSeqValueCount M v (Term.Apply (Term.Apply f x) xs) =
      seqTermValueCount M v x + eoListSeqValueCount M v xs := rfl

theorem eoListSeqValueCount_nil_typed (M : SmtModel) (v : SmtValue) (T : Term) :
    eoListSeqValueCount M v (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) = 0 := rfl

theorem eoListSeqValueCount_mk_apply_cons (M : SmtModel) (v : SmtValue)
    (x xs : Term) (hx : x ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck) :
    eoListSeqValueCount M v
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) =
      seqTermValueCount M v x + eoListSeqValueCount M v xs := by
  rw [SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hxs]
  rfl

theorem eoListSeqValueCount_concat_rec
    (M : SmtModel) (v : SmtValue) :
    ∀ L R : Term, SetsEvalOpSupport.IsElemList L -> R ≠ Term.Stuck ->
      eoListSeqValueCount M v (__eo_list_concat_rec L R) =
        eoListSeqValueCount M v L + eoListSeqValueCount M v R := by
  intro L R hL hR
  induction L, R using __eo_list_concat_rec.induct with
  | case1 z =>
      exact absurd hL (by simp [SetsEvalOpSupport.IsElemList])
  | case2 t ht =>
      exact absurd rfl hR
  | case3 f x y z hz ih =>
      obtain ⟨hf, hx, hy⟩ := hL
      have hTailNe : __eo_list_concat_rec y z ≠ Term.Stuck :=
        SetsEvalOpSupport.concat_rec_ne_stuck y z hy hR
      rw [SetsEvalOpSupport.concat_rec_cons f x y z hR,
        SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hTailNe]
      simp [eoListSeqValueCount, ih hy hR, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm]
  | case4 nil z hns hzs hncons =>
      have hEq : __eo_list_concat_rec nil z = z := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      rw [hEq]
      have hNil : eoListSeqValueCount M v nil = 0 := by
        cases nil <;> simp_all [eoListSeqValueCount]
      simp [hNil]

theorem eoListSeqValueCount_erase_rec_le
    (M : SmtModel) (v : SmtValue) :
    ∀ L a : Term, SetsEvalOpSupport.IsElemList L -> a ≠ Term.Stuck ->
      eoListSeqValueCount M v L <=
        eoListSeqValueCount M v (__eo_list_erase_rec L a) + seqTermValueCount M v a := by
  intro L a hL ha
  induction L, a using __eo_list_erase_rec.induct with
  | case1 z =>
      exact absurd hL (by simp [SetsEvalOpSupport.IsElemList])
  | case2 s hs =>
      exact absurd rfl ha
  | case3 f x y t ht ih =>
      obtain ⟨hf, hx, hy⟩ := hL
      rw [SetsEvalOpSupport.erase_rec_cons f x y t ha]
      rw [eo_eq_val x t hx ha]
      cases hteq : native_teq t x
      · have hTail := ih hy ha
        have hErTail : SetsEvalOpSupport.IsElemList (__eo_list_erase_rec y t) :=
          SetsEvalOpSupport.erase_rec_isElemList y t hy ha
        have hErTailNe : __eo_list_erase_rec y t ≠ Term.Stuck :=
          SetsEvalOpSupport.isElemList_ne_stuck hErTail
        rw [eo_ite_false,
          SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hErTailNe]
        simp [eoListSeqValueCount]
        omega
      · have htx : t = x := of_decide_eq_true hteq
        subst htx
        rw [eo_ite_true]
        simp [eoListSeqValueCount]
        omega
  | case4 nil t hns hts hncons =>
      have hEq : __eo_list_erase_rec nil t = nil := by
        unfold __eo_list_erase_rec
        split <;> simp_all
      rw [hEq]
      omega

theorem eoListSeqValueCount_erase_le
    (M : SmtModel) (v : SmtValue)
    (L a : Term)
    (hTL : SetsEvalOpSupport.IsTL L)
    (ha : a ≠ Term.Stuck) :
    eoListSeqValueCount M v L <=
      eoListSeqValueCount M v
          (__eo_list_erase (Term.UOp UserOp._at__at_TypedList_cons) L a) +
        seqTermValueCount M v a := by
  rw [show __eo_list_erase (Term.UOp UserOp._at__at_TypedList_cons) L a =
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L)
        (Term.Boolean true) (__eo_list_erase_rec L a) from rfl,
    SetsEvalOpSupport.isTL_is_list L hTL, SetsEvalOpSupport.req_tt]
  exact eoListSeqValueCount_erase_rec_le M v L a
    (SetsEvalOpSupport.isTL_isElemList L hTL) ha

theorem typedList_nil_isTL (T : Term) :
    SetsEvalOpSupport.IsTL (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) := by
  trivial

theorem mk_typedList_cons_isTL (x xs : Term)
    (hx : x ≠ Term.Stuck) (hxs : SetsEvalOpSupport.IsTL xs) :
    SetsEvalOpSupport.IsTL
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) := by
  rw [SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp)
    (SetsEvalOpSupport.isTL_ne_stuck hxs)]
  exact ⟨hx, hxs⟩

theorem eoListSeqValueCount_concat
    (M : SmtModel) (v : SmtValue) (L R : Term)
    (hL : SetsEvalOpSupport.IsTL L) (hR : SetsEvalOpSupport.IsTL R) :
    eoListSeqValueCount M v
        (__eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons) L R) =
      eoListSeqValueCount M v L + eoListSeqValueCount M v R := by
  rw [show __eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons) L R =
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L)
        (Term.Boolean true)
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) R)
          (Term.Boolean true) (__eo_list_concat_rec L R)) from rfl,
    SetsEvalOpSupport.isTL_is_list L hL, SetsEvalOpSupport.req_tt,
    SetsEvalOpSupport.isTL_is_list R hR, SetsEvalOpSupport.req_tt]
  exact eoListSeqValueCount_concat_rec M v L R
    (SetsEvalOpSupport.isTL_isElemList L hL)
    (SetsEvalOpSupport.isTL_ne_stuck hR)

theorem eo_list_concat_isTL (L R : Term)
    (hL : SetsEvalOpSupport.IsTL L) (hR : SetsEvalOpSupport.IsTL R) :
    SetsEvalOpSupport.IsTL
      (__eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons) L R) := by
  rw [show __eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons) L R =
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L)
        (Term.Boolean true)
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) R)
          (Term.Boolean true) (__eo_list_concat_rec L R)) from rfl,
    SetsEvalOpSupport.isTL_is_list L hL, SetsEvalOpSupport.req_tt,
    SetsEvalOpSupport.isTL_is_list R hR, SetsEvalOpSupport.req_tt]
  exact SetsEvalOpSupport.isTL_concat_rec L hL R hR

theorem eval_seq_of_type (M : SmtModel) (hM : model_total_typed M)
    (t : Term) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    ∃ S : SmtSeq, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq S := by
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Seq T := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by
          unfold term_has_non_none_type
          rw [hTy]
          exact seq_ne_none T)
  rcases seq_value_canonical hValTy with ⟨S, hEval⟩
  exact ⟨S, hEval⟩

theorem valueCount_string_eval (M : SmtModel) (v : SmtValue)
    (w : native_String) (S : SmtSeq)
    (hEval : __smtx_model_eval M (__eo_to_smt (Term.String w)) = SmtValue.Seq S) :
    valueCount v (native_unpack_seq S) = valueCount v (w.map SmtValue.Char) := by
  have hEval' := eval_string M w
  rw [hEval] at hEval'
  injection hEval' with hS
  rw [hS, unpack_pack_string_map]

theorem eo_is_str_true_cases (t : Term)
    (h : __eo_is_str t = Term.Boolean true) :
    ∃ w, t = Term.String w := by
  cases t <;> simp [__eo_is_str, __eo_is_str_internal, native_teq,
    SmtEval.native_and, SmtEval.native_not] at h
  · rename_i w
    exact ⟨w, rfl⟩

theorem eo_is_str_boolean_of_ne_stuck (t : Term) (ht : t ≠ Term.Stuck) :
    ∃ b, __eo_is_str t = Term.Boolean b := by
  unfold __eo_is_str
  exact ⟨native_and (native_not (native_teq t Term.Stuck))
    (native_teq (__eo_is_str_internal t) (Term.Boolean true)), rfl⟩

theorem eo_typeof_ne_stuck_of_smt_seq_type (t : Term) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    __eo_typeof t ≠ Term.Stuck := by
  have hEoTy :
      __eo_to_smt_type (__eo_typeof t) = SmtType.Seq T :=
    TranslationProofs.eo_to_smt_type_typeof_of_smt_type t hTy (by simp)
  intro hSt
  rw [hSt] at hEoTy
  simp [__eo_to_smt_type] at hEoTy

theorem eo_nil_typedList_eq (T : Term) (hT : T ≠ Term.Stuck) :
    __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) T =
      Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T := by
  cases T <;> simp [__eo_nil, __eo_nil__at__at_TypedList_cons] at hT ⊢

theorem str_multiset_overapprox_sound
    (M : SmtModel) (hM : model_total_typed M) (v : SmtValue) :
    ∀ (t : Term) (S : SmtSeq) (T : SmtType),
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq S ->
      SetsEvalOpSupport.IsTL (__str_multiset_overapprox t) ∧
        valueCount v (native_unpack_seq S) <=
          eoListSeqValueCount M v (__str_multiset_overapprox t) := by
  intro t
  induction t using __str_multiset_overapprox.induct with
  | case1 =>
      intro S T hTy _
      change __smtx_typeof SmtTerm.None = SmtType.Seq T at hTy
      simp at hTy
  | case2 s ss ihS ihSs =>
      intro S T hTy hEval
      obtain ⟨hsTy, hssTy⟩ := strConcat_args_of_seq_type s ss T hTy
      obtain ⟨⟨Ss, hSs⟩, ⟨Sss, hSss⟩⟩ :=
        strConcat_args_eval_seq_of_concat_eval_seq M s ss ⟨S, hEval⟩
      obtain ⟨hTLs, hBounds⟩ := ihS Ss T hsTy hSs
      obtain ⟨hTLss, hBoundss⟩ := ihSs Sss T hssTy hSss
      obtain ⟨Sxy, hSxy, hUnpack⟩ := concat_unpack M s ss Ss Sss hSs hSss
      have hSeq : S = Sxy := by
        rw [hEval] at hSxy
        injection hSxy
      constructor
      · exact eo_list_concat_isTL (__str_multiset_overapprox s)
          (__str_multiset_overapprox ss) hTLs hTLss
      · change valueCount v (native_unpack_seq S) <=
          eoListSeqValueCount M v
            (__eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons)
              (__str_multiset_overapprox s) (__str_multiset_overapprox ss))
        rw [eoListSeqValueCount_concat M v _ _ hTLs hTLss]
        rw [hSeq, hUnpack, valueCount_append]
        omega
  | case3 s n m ihS =>
      intro S T hTy hEval
      have hTy' :
          __smtx_typeof
              (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n) (__eo_to_smt m)) =
            SmtType.Seq T := by
        simpa using hTy
      obtain ⟨U, hsTy, _hnTy, _hmTy⟩ :=
        str_substr_args_of_non_none
          (by
            unfold term_has_non_none_type
            rw [hTy']
            exact seq_ne_none T)
      obtain ⟨Ss, hSs⟩ := eval_seq_of_type M hM s U hsTy
      obtain ⟨hTLs, hBounds⟩ := ihS Ss U hsTy hSs
      constructor
      · exact hTLs
      · change valueCount v (native_unpack_seq S) <=
          eoListSeqValueCount M v (__str_multiset_overapprox s)
        rw [show __eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n) m) =
              SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n) (__eo_to_smt m) by rfl]
          at hEval
        simp only [__smtx_model_eval] at hEval
        rw [hSs] at hEval
        cases hn : __smtx_model_eval M (__eo_to_smt n) <;>
          simp [__smtx_model_eval_str_substr, hn] at hEval
        case Numeral i =>
          cases hm : __smtx_model_eval M (__eo_to_smt m) <;>
            simp [hm] at hEval
          case Numeral j =>
            have hExtract :
                valueCount v (native_unpack_seq S) <=
                  valueCount v (native_unpack_seq Ss) := by
              rw [← hEval, Smtm.native_unpack_pack_seq]
              exact valueCount_extract_le v (native_unpack_seq Ss) i j
            omega
  | case4 s pat repl ihS ihRepl =>
      intro S T hTy hEval
      have hTy' :
          __smtx_typeof
              (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat)
                (__eo_to_smt repl)) =
            SmtType.Seq T := by
        simpa using hTy
      obtain ⟨U, hsTy, hpatTy, hreplTy⟩ :=
        seq_triop_args_of_non_none (op := SmtTerm.str_replace)
          (typeof_str_replace_eq (__eo_to_smt s) (__eo_to_smt pat) (__eo_to_smt repl))
          (by
            unfold term_has_non_none_type
            rw [hTy']
            exact seq_ne_none T)
      obtain ⟨Ss, hSs⟩ := eval_seq_of_type M hM s U hsTy
      obtain ⟨Spat, hSpat⟩ := eval_seq_of_type M hM pat U hpatTy
      obtain ⟨Srepl, hSrepl⟩ := eval_seq_of_type M hM repl U hreplTy
      obtain ⟨hTLs, hBounds⟩ := ihS Ss U hsTy hSs
      obtain ⟨hTLrepl, hBoundrepl⟩ := ihRepl Srepl U hreplTy hSrepl
      constructor
      · exact eo_list_concat_isTL (__str_multiset_overapprox s)
          (__str_multiset_overapprox repl) hTLs hTLrepl
      · rw [show __eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) pat) repl) =
              SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat) (__eo_to_smt repl) by rfl]
          at hEval
        simp only [__smtx_model_eval] at hEval
        rw [hSs, hSpat, hSrepl] at hEval
        simp [__smtx_model_eval_str_replace] at hEval
        change valueCount v (native_unpack_seq S) <=
          eoListSeqValueCount M v
            (__eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons)
              (__str_multiset_overapprox s) (__str_multiset_overapprox repl))
        rw [eoListSeqValueCount_concat M v _ _ hTLs hTLrepl]
        have hReplace :
            valueCount v (native_unpack_seq S) <=
              valueCount v (native_unpack_seq Ss) +
                valueCount v (native_unpack_seq Srepl) := by
          rw [← hEval, Smtm.native_unpack_pack_seq]
          exact valueCount_replace_le v (native_unpack_seq Ss)
            (native_unpack_seq Spat) (native_unpack_seq Srepl)
        omega
  | case5 s =>
      intro S T hTy hEval
      have hsNe : s ≠ Term.Stuck := by
        intro hs
        subst hs
        change __smtx_typeof SmtTerm.None = SmtType.Seq T at hTy
        simp at hTy
      have hTyNe : __eo_typeof s ≠ Term.Stuck :=
        eo_typeof_ne_stuck_of_smt_seq_type s T hTy
      by_cases hEmptyTrue : __str_is_empty s = Term.Boolean true
      · have hOver :
            __str_multiset_overapprox s =
              Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof s) := by
          unfold __str_multiset_overapprox
          split <;> try simp_all
          rw [eo_ite_true,
            SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hTyNe]
        constructor
        · rw [hOver]
          trivial
        · rw [hOver]
          have hCount0 := seqTermValueCount_eval_nil_of_empty M v s S hEmptyTrue hEval
          rw [seqTermValueCount_of_eval_seq M v s S hEval] at hCount0
          simp [hCount0]
      · obtain ⟨bEmpty, hEmptyBool⟩ := str_is_empty_boolean_of_ne_stuck s hsNe
        have hEmptyFalse : __str_is_empty s = Term.Boolean false := by
          cases bEmpty <;> simp_all
        by_cases hStrTrue : __eo_is_str s = Term.Boolean true
        · obtain ⟨w, rfl⟩ := eo_is_str_true_cases s hStrTrue
          have hOver :
              __str_multiset_overapprox (Term.String w) =
                __str_multiset_overapprox_word (charChainTerm w) := by
            change __eo_ite (__str_is_empty (Term.String w))
                (__eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil)
                  (__eo_typeof (Term.String w)))
                (__eo_ite (__eo_is_str (Term.String w))
                  (__str_multiset_overapprox_word
                    (__str_flatten (__str_nary_intro (Term.String w))))
                  (__eo_mk_apply
                    (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                      (Term.String w))
                    (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons)
                      (__eo_typeof (Term.String w))))) = _
            rw [hEmptyFalse, eo_ite_false,
              show __eo_is_str (Term.String w) = Term.Boolean true by
                simp [__eo_is_str, __eo_is_str_internal, native_teq,
                  SmtEval.native_and, SmtEval.native_not],
              eo_ite_true, flatten_nary_intro_string]
          obtain ⟨hWordTL, hWordCount⟩ :=
            str_multiset_overapprox_word_charChain_sound M v w
          constructor
          · rwa [hOver]
          · rw [hOver, hWordCount, valueCount_string_eval M v w S hEval]
            omega
        · obtain ⟨bStr, hStrBool⟩ := eo_is_str_boolean_of_ne_stuck s hsNe
          have hStrFalse : __eo_is_str s = Term.Boolean false := by
            cases bStr <;> simp_all
          let nil := Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof s)
          have hNilEq :
              __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof s) = nil := by
            exact eo_nil_typedList_eq (__eo_typeof s) hTyNe
          have hNilTL : SetsEvalOpSupport.IsTL nil := by
            dsimp [nil]
            trivial
          have hNilNe : nil ≠ Term.Stuck := SetsEvalOpSupport.isTL_ne_stuck hNilTL
          have hOver :
              __str_multiset_overapprox s =
                Term.Apply
                  (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s) nil := by
            unfold __str_multiset_overapprox
            split <;> try simp_all
            rw [eo_ite_false, eo_ite_false,
              SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp)
                (SetsEvalOpSupport.isTL_ne_stuck hNilTL)]
          constructor
          · rw [hOver]
            exact ⟨hsNe, hNilTL⟩
          · rw [hOver]
            simp [eoListSeqValueCount, seqTermValueCount_of_eval_seq M v s S hEval]

def AtomTerm (a : Term) : Prop :=
  (∃ ch, a = Term.String [ch]) ∨
    (∃ e, a = Term.Apply (Term.UOp UserOp.seq_unit) e)

def NoAtomOverlapElem (M : SmtModel) (hM : model_total_typed M)
    (T : SmtType) (x : Term) : Prop :=
  ∀ a : Term, AtomTerm a ->
    __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
    __eo_ite (__eo_eq a x) (Term.Boolean false)
        (__are_distinct_terms_type a x (__eo_typeof a)) =
      Term.Boolean true ->
    seqTermValueCount M (seqElemVal M a) x = 0

def NoAtomOverlapList (M : SmtModel) (hM : model_total_typed M)
    (T : SmtType) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs =>
      NoAtomOverlapElem M hM T x ∧ NoAtomOverlapList M hM T xs
  | _ => True

def AtomTypedList (T : SmtType) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs =>
      AtomTerm x ∧ __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
        AtomTypedList T xs
  | Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) _ => True
  | _ => False

theorem eo_ite_eq_false_guard_true_local {a b d : Term} :
    __eo_ite (__eo_eq a b) (Term.Boolean false) d = Term.Boolean true ->
    __eo_eq a b = Term.Boolean false ∧ d = Term.Boolean true := by
  intro h
  unfold __eo_ite at h
  by_cases ht : native_teq (__eo_eq a b) (Term.Boolean true) = true
  · simp [ht, native_ite] at h
  · by_cases hf : native_teq (__eo_eq a b) (Term.Boolean false) = true
    · have hEq : __eo_eq a b = Term.Boolean false := by
        simpa [native_teq] using hf
      simp [ht, hf, native_ite] at h
      exact ⟨hEq, h⟩
    · simp [ht, hf, native_ite] at h

theorem eo_ite_then_eq_true_local {g X : Term}
    (h : __eo_ite g X (Term.Boolean false) = Term.Boolean true) :
    g = Term.Boolean true ∧ X = Term.Boolean true := by
  unfold __eo_ite at h
  cases hg : native_teq g (Term.Boolean true)
  · rw [hg] at h
    simp only [native_ite] at h
    cases hg2 : native_teq g (Term.Boolean false) <;> rw [hg2] at h <;>
      simp at h
  · rw [hg] at h
    simp only [native_ite] at h
    exact ⟨by simpa [native_teq] using hg, h⟩

theorem eo_ite_true_cases_local {c t e : Term} :
    __eo_ite c t e = Term.Boolean true ->
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h
  case Boolean b =>
    cases b <;> simp at h
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl ⟨rfl, h⟩

theorem term_ne_stuck_of_smt_seq_type (a : Term) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T) :
    a ≠ Term.Stuck := by
  intro h
  subst h
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hTy
  simp at hTy

theorem noAtomOverlapElem_atom
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType)
    (x : Term)
    (hxAtom : AtomTerm x)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    NoAtomOverlapElem M hM T x := by
  intro a haAtom haTy hGuard
  obtain ⟨hEqFalse, hDistinct⟩ :=
    eo_ite_eq_false_guard_true_local hGuard
  have hvFalse :
      native_veq (seqElemVal M a) (seqElemVal M x) = false := by
    exact shaped_atoms_sound M hM T [a] [x]
      (by intro b hb; simp at hb; subst hb; exact haTy)
      (by intro b hb; simp at hb; subst hb; exact hxTy)
      (by intro b hb; simp at hb; subst hb; exact haAtom)
      (by intro b hb; simp at hb; subst hb; exact hxAtom)
      a (by simp) x (by simp) hEqFalse hDistinct
  have hxCount :
      seqTermValueCount M (seqElemVal M a) x =
        if native_veq (seqElemVal M x) (seqElemVal M a) = true then 1 else 0 := by
    exact seqTermValueCount_of_atom_shape M (seqElemVal M a) (seqElemVal M x)
      x hxAtom rfl
  rw [hxCount]
  have hvFalse' : native_veq (seqElemVal M x) (seqElemVal M a) = false :=
    native_veq_false_symm hvFalse
  rw [hvFalse']
  simp

theorem seq_distinct_terms_not_true_of_not_shapes_local {a b U : Term} :
    (¬ ∃ V, b = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)) ->
    (¬ ∃ V, a = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V)) ->
    (¬ ∃ e₁ tail₁ e₂ tail₂,
      a = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁ ∧
      b = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂) ->
    (¬ ∃ e₁ tail e₂,
      a = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail ∧
      b = Term.Apply (Term.UOp UserOp.seq_unit) e₂) ->
    (¬ ∃ e₁ e₂ tail,
      a = Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
      b = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail) ->
    (¬ ∃ e₁ e₂,
      a = Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
      b = Term.Apply (Term.UOp UserOp.seq_unit) e₂) ->
    __seq_distinct_terms a b U ≠ Term.Boolean true := by
  intro hbEmpty haEmpty hConcatConcat hConcatUnit hUnitConcat hUnitUnit hDistinct
  rw [__seq_distinct_terms.eq_def] at hDistinct
  split at hDistinct <;> try cases hDistinct
  all_goals
    first
    | exact hbEmpty ⟨_, rfl⟩
    | exact haEmpty ⟨_, rfl⟩
    | exact hConcatConcat ⟨_, _, _, _, rfl, rfl⟩
    | exact hConcatUnit ⟨_, _, _, rfl, rfl⟩
    | exact hUnitConcat ⟨_, _, _, rfl, rfl⟩
    | exact hUnitUnit ⟨_, _, rfl, rfl⟩

theorem are_distinct_terms_type_seq_true_seq_distinct_local
    {a b U : Term} :
    U ≠ Term.UOp UserOp.Char ->
    __are_distinct_terms_type a b
        (Term.Apply (Term.UOp UserOp.Seq) U) =
      Term.Boolean true ->
    __seq_distinct_terms a b U = Term.Boolean true := by
  intro hU hDistinct
  by_cases ha : a = Term.Stuck
  · subst a
    simp [__are_distinct_terms_type.eq_def] at hDistinct
  by_cases hb : b = Term.Stuck
  · subst b
    simp [__are_distinct_terms_type.eq_def] at hDistinct
  have hSeq :
      __are_distinct_terms_type a b
          (Term.Apply (Term.UOp UserOp.Seq) U) =
        __seq_distinct_terms a b U := by
    rw [__are_distinct_terms_type.eq_def]
    split <;> simp_all
  rwa [hSeq] at hDistinct

theorem seqUnit_opaque_distinct_false
    (e x : Term)
    (hxNotAtom : ¬ AtomTerm x)
    (hEmptyFalse : __str_is_empty x = Term.Boolean false)
    (hNoConcat : ∀ s ss : Term,
      x ≠ Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) ss)
    (hDistinct :
      __are_distinct_terms_type (Term.Apply (Term.UOp UserOp.seq_unit) e) x
          (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) e)) =
        Term.Boolean true) :
    False := by
  have hbEmpty :
      ¬ ∃ V, x = Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V) := by
    rintro ⟨V, rfl⟩
    simp [__str_is_empty] at hEmptyFalse
  have haEmpty :
      ¬ ∃ V, Term.Apply (Term.UOp UserOp.seq_unit) e =
        Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) V) := by
    rintro ⟨V, h⟩
    simp [Term.seq_empty] at h
  have hConcatConcat :
      ¬ ∃ e₁ tail₁ e₂ tail₂,
        Term.Apply (Term.UOp UserOp.seq_unit) e =
          mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail₁ ∧
        x = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail₂ := by
    rintro ⟨e₁, tail₁, e₂, tail₂, hA, _⟩
    simp [mkConcat] at hA
  have hConcatUnit :
      ¬ ∃ e₁ tail e₂,
        Term.Apply (Term.UOp UserOp.seq_unit) e =
          mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₁) tail ∧
        x = Term.Apply (Term.UOp UserOp.seq_unit) e₂ := by
    rintro ⟨e₁, tail, e₂, hA, _⟩
    simp [mkConcat] at hA
  have hUnitConcat :
      ¬ ∃ e₁ e₂ tail,
        Term.Apply (Term.UOp UserOp.seq_unit) e =
          Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
        x = mkConcat (Term.Apply (Term.UOp UserOp.seq_unit) e₂) tail := by
    rintro ⟨e₁, e₂, tail, _hA, hX⟩
    exact hNoConcat _ _ hX
  have hUnitUnit :
      ¬ ∃ e₁ e₂,
        Term.Apply (Term.UOp UserOp.seq_unit) e =
          Term.Apply (Term.UOp UserOp.seq_unit) e₁ ∧
        x = Term.Apply (Term.UOp UserOp.seq_unit) e₂ := by
    rintro ⟨e₁, e₂, _hA, hX⟩
    exact hxNotAtom (Or.inr ⟨e₂, hX⟩)
  have hSeqNot :
      __seq_distinct_terms (Term.Apply (Term.UOp UserOp.seq_unit) e) x
        (__eo_typeof e) ≠ Term.Boolean true :=
    seq_distinct_terms_not_true_of_not_shapes_local hbEmpty haEmpty
      hConcatConcat hConcatUnit hUnitConcat hUnitUnit
  change __are_distinct_terms_type (Term.Apply (Term.UOp UserOp.seq_unit) e) x
      (__eo_typeof_seq_unit (__eo_typeof e)) = Term.Boolean true at hDistinct
  by_cases hStuck : __eo_typeof e = Term.Stuck
  · rw [hStuck] at hDistinct
    cases x <;> simp [__eo_typeof_seq_unit, __are_distinct_terms_type.eq_def]
      at hDistinct
  have hSeqTy :
      __eo_typeof_seq_unit (__eo_typeof e) =
        Term.Apply (Term.UOp UserOp.Seq) (__eo_typeof e) := by
    cases hE : __eo_typeof e <;>
      simp [__eo_typeof_seq_unit, hE] at hStuck ⊢
  rw [hSeqTy] at hDistinct
  by_cases hChar : __eo_typeof e = Term.UOp UserOp.Char
  · rw [hChar] at hDistinct
    change __are_distinct_terms_type (Term.Apply (Term.UOp UserOp.seq_unit) e) x
        (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) =
      Term.Boolean true at hDistinct
    cases x <;> simp [__are_distinct_terms_type, __eo_and, __eo_is_str,
      __eo_is_str_internal, native_teq, SmtEval.native_and,
      SmtEval.native_not] at hDistinct
  · have hSeq := are_distinct_terms_type_seq_true_seq_distinct_local
      (a := Term.Apply (Term.UOp UserOp.seq_unit) e) (b := x)
      (U := __eo_typeof e) hChar hDistinct
    exact hSeqNot hSeq

theorem noAtomOverlapElem_opaque
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType)
    (x : Term)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hStrFalse : __eo_is_str x = Term.Boolean false)
    (hEmptyFalse : __str_is_empty x = Term.Boolean false)
    (hNoConcat : ∀ s ss : Term,
      x ≠ Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) ss) :
    NoAtomOverlapElem M hM T x := by
  intro a haAtom haTy hGuard
  by_cases hxAtom : AtomTerm x
  · exact noAtomOverlapElem_atom M hM T x hxAtom hxTy a haAtom haTy hGuard
  · obtain ⟨_hEqFalse, hDistinct⟩ :=
      eo_ite_eq_false_guard_true_local hGuard
    exfalso
    rcases haAtom with ⟨ch, rfl⟩ | ⟨e, rfl⟩
    · rw [strChar_typeof ch] at hDistinct
      have hAnd :
          __eo_and (__eo_is_str (Term.String [ch])) (__eo_is_str x) =
            Term.Boolean true := by
        cases x <;> simp [__are_distinct_terms_type] at hDistinct ⊢
        all_goals exact hDistinct
      obtain ⟨_, hxStrTrue⟩ := eo_and_true_split _ _ hAnd
      rw [hStrFalse] at hxStrTrue
      cases hxStrTrue
    · exact seqUnit_opaque_distinct_false e x hxAtom hEmptyFalse hNoConcat hDistinct

theorem noAtomOverlapList_distinct_zero
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType) :
    ∀ L : Term, SetsEvalOpSupport.IsTL L -> NoAtomOverlapList M hM T L ->
      ∀ a : Term, AtomTerm a ->
        __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
        __are_distinct_terms_list_rec a L (__eo_typeof a) = Term.Boolean true ->
        eoListSeqValueCount M (seqElemVal M a) L = 0 := by
  intro L
  induction L using SetsEvalOpSupport.IsTL.induct with
  | case1 x y ih =>
      intro hTL hNo a haAtom haTy hDist
      obtain ⟨hxNe, hyTL⟩ := hTL
      obtain ⟨hElem, hTailNo⟩ := hNo
      have haNe : a ≠ Term.Stuck := term_ne_stuck_of_smt_seq_type a T haTy
      have hTyNe : __eo_typeof a ≠ Term.Stuck :=
        eo_typeof_ne_stuck_of_smt_seq_type a T haTy
      rw [SetsEvalOpSupport.distinct_list_rec_cons a x y (__eo_typeof a) haNe hTyNe]
        at hDist
      obtain ⟨hGuard, hTailDist⟩ := eo_ite_then_eq_true_local hDist
      have hxZero := hElem a haAtom haTy hGuard
      have hyZero := ih hyTL hTailNo a haAtom haTy hTailDist
      simp [eoListSeqValueCount, hxZero, hyZero]
  | case2 U =>
      intro _ _ a _ _ _
      rfl
  | case3 t _ _ =>
      intro hTL
      exact absurd hTL (by cases t <;> simp_all [SetsEvalOpSupport.IsTL])

theorem noAtomOverlapList_concat_rec
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType) :
    ∀ L R : Term, SetsEvalOpSupport.IsTL L -> SetsEvalOpSupport.IsTL R ->
      NoAtomOverlapList M hM T L -> NoAtomOverlapList M hM T R ->
      NoAtomOverlapList M hM T (__eo_list_concat_rec L R) := by
  intro L
  induction L using SetsEvalOpSupport.IsTL.induct with
  | case1 x y ih =>
      intro R hL hR hNoL hNoR
      obtain ⟨hxNe, hyTL⟩ := hL
      obtain ⟨hElem, hTailNo⟩ := hNoL
      have hTailConcatNe :
          __eo_list_concat_rec y R ≠ Term.Stuck :=
        SetsEvalOpSupport.concat_rec_ne_stuck y R
          (SetsEvalOpSupport.isTL_isElemList y hyTL)
          (SetsEvalOpSupport.isTL_ne_stuck hR)
      rw [SetsEvalOpSupport.concat_rec_cons
        (Term.UOp UserOp._at__at_TypedList_cons) x y R
        (SetsEvalOpSupport.isTL_ne_stuck hR),
        SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hTailConcatNe]
      exact ⟨hElem, ih R hyTL hR hTailNo hNoR⟩
  | case2 U =>
      intro R hL hR _ hNoR
      have hEq :
          __eo_list_concat_rec
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) U) R = R := by
        unfold __eo_list_concat_rec
        split <;> simp_all
      rw [hEq]
      exact hNoR
  | case3 t _ _ =>
      intro R hL
      exact absurd hL (by cases t <;> simp_all [SetsEvalOpSupport.IsTL])

theorem noAtomOverlapList_concat
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType)
    (L R : Term)
    (hL : SetsEvalOpSupport.IsTL L) (hR : SetsEvalOpSupport.IsTL R)
    (hNoL : NoAtomOverlapList M hM T L)
    (hNoR : NoAtomOverlapList M hM T R) :
    NoAtomOverlapList M hM T
      (__eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons) L R) := by
  rw [show __eo_list_concat (Term.UOp UserOp._at__at_TypedList_cons) L R =
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L)
        (Term.Boolean true)
        (__eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) R)
          (Term.Boolean true) (__eo_list_concat_rec L R)) from rfl,
    SetsEvalOpSupport.isTL_is_list L hL, SetsEvalOpSupport.req_tt,
    SetsEvalOpSupport.isTL_is_list R hR, SetsEvalOpSupport.req_tt]
  exact noAtomOverlapList_concat_rec M hM T L R hL hR hNoL hNoR

theorem str_multiset_overapprox_word_charChain_noAtom
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType)
    (w : native_String)
    (hAtomTy : ∀ a ∈ w.map (fun ch => Term.String [ch]),
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T) :
    NoAtomOverlapList M hM T
      (__str_multiset_overapprox_word (charChainTerm w)) := by
  induction w with
  | nil =>
      have hWord :
          __str_multiset_overapprox_word (charChainTerm []) =
            Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
              (__eo_typeof (Term.String [])) := by
        change __eo_ite (__str_is_empty (Term.String []))
            (__eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil)
              (__eo_typeof (Term.String [])))
            (__eo_mk_apply
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.String []))
              (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons)
                (__eo_typeof (Term.String [])))) = _
        rw [show __str_is_empty (Term.String []) = Term.Boolean true by rfl,
          eo_ite_true]
        change __eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil)
            (__eo_typeof (Term.String [])) =
          Term.Apply (Term.UOp UserOp._at__at_TypedList_nil)
            (__eo_typeof (Term.String []))
        rw [show __eo_typeof (Term.String []) =
          Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) by rfl]
        rfl
      rw [hWord]
      trivial
  | cons ch rest ih =>
      have hTailAtomTy : ∀ a ∈ rest.map (fun ch => Term.String [ch]),
          __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := by
        intro a ha
        exact hAtomTy a (by simp [ha])
      have hTailNo := ih hTailAtomTy
      obtain ⟨hTailTL, _⟩ :=
        str_multiset_overapprox_word_charChain_sound M (SmtValue.Boolean false) rest
      have hTailNe :
          __str_multiset_overapprox_word (charChainTerm rest) ≠ Term.Stuck :=
        SetsEvalOpSupport.isTL_ne_stuck hTailTL
      have hCons :
          __str_multiset_overapprox_word (charChainTerm (ch :: rest)) =
            Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                (Term.String [ch]))
              (__str_multiset_overapprox_word (charChainTerm rest)) := by
        change __eo_mk_apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) (Term.String [ch]))
            (__str_multiset_overapprox_word (charChainTerm rest)) = _
        exact SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hTailNe
      rw [hCons]
      constructor
      · have hHeadTy :
            __smtx_typeof (__eo_to_smt (Term.String [ch])) = SmtType.Seq T :=
          hAtomTy (Term.String [ch]) (by simp)
        exact noAtomOverlapElem_atom M hM T (Term.String [ch])
          (Or.inl ⟨ch, rfl⟩) hHeadTy
      · exact hTailNo

theorem str_multiset_overapprox_noAtom
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ (t : Term) (T : SmtType),
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
      SetsEvalOpSupport.IsTL (__str_multiset_overapprox t) ∧
        NoAtomOverlapList M hM T (__str_multiset_overapprox t) := by
  intro t
  induction t using __str_multiset_overapprox.induct with
  | case1 =>
      intro T hTy
      change __smtx_typeof SmtTerm.None = SmtType.Seq T at hTy
      simp at hTy
  | case2 s ss ihS ihSs =>
      intro T hTy
      obtain ⟨hsTy, hssTy⟩ := strConcat_args_of_seq_type s ss T hTy
      obtain ⟨hTLs, hNoS⟩ := ihS T hsTy
      obtain ⟨hTLss, hNoSs⟩ := ihSs T hssTy
      constructor
      · exact eo_list_concat_isTL (__str_multiset_overapprox s)
          (__str_multiset_overapprox ss) hTLs hTLss
      · exact noAtomOverlapList_concat M hM T
          (__str_multiset_overapprox s) (__str_multiset_overapprox ss)
          hTLs hTLss hNoS hNoSs
  | case3 s n m ihS =>
      intro T hTy
      have hTy' :
          __smtx_typeof
              (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n) (__eo_to_smt m)) =
            SmtType.Seq T := by
        simpa using hTy
      obtain ⟨U, hsTy, _hnTy, _hmTy⟩ :=
        str_substr_args_of_non_none
          (by
            unfold term_has_non_none_type
            rw [hTy']
            exact seq_ne_none T)
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hTy']
          rw [typeof_str_substr_eq]
          simp [__smtx_typeof_str_substr, hsTy, _hnTy, _hmTy]
        injection hSeq with h
      subst U
      change SetsEvalOpSupport.IsTL (__str_multiset_overapprox s) ∧
        NoAtomOverlapList M hM T (__str_multiset_overapprox s)
      exact ihS T hsTy
  | case4 s pat repl ihS ihRepl =>
      intro T hTy
      have hTy' :
          __smtx_typeof
              (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt pat)
                (__eo_to_smt repl)) =
            SmtType.Seq T := by
        simpa using hTy
      obtain ⟨U, hsTy, _hpatTy, hreplTy⟩ :=
        seq_triop_args_of_non_none (op := SmtTerm.str_replace)
          (typeof_str_replace_eq (__eo_to_smt s) (__eo_to_smt pat) (__eo_to_smt repl))
          (by
            unfold term_has_non_none_type
            rw [hTy']
            exact seq_ne_none T)
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hTy']
          rw [typeof_str_replace_eq]
          simp [__smtx_typeof_seq_op_3, hsTy, _hpatTy, hreplTy,
            native_Teq, native_ite]
        injection hSeq with h
      subst U
      obtain ⟨hTLs, hNoS⟩ := ihS T hsTy
      obtain ⟨hTLrepl, hNoRepl⟩ := ihRepl T hreplTy
      constructor
      · exact eo_list_concat_isTL (__str_multiset_overapprox s)
          (__str_multiset_overapprox repl) hTLs hTLrepl
      · exact noAtomOverlapList_concat M hM T
          (__str_multiset_overapprox s) (__str_multiset_overapprox repl)
          hTLs hTLrepl hNoS hNoRepl
  | case5 s _hNotStuck hNotConcat _hNotSubstr _hNotReplace =>
      intro T hTy
      have hsNe : s ≠ Term.Stuck := by
        intro hs
        subst hs
        change __smtx_typeof SmtTerm.None = SmtType.Seq T at hTy
        simp at hTy
      have hTyNe : __eo_typeof s ≠ Term.Stuck :=
        eo_typeof_ne_stuck_of_smt_seq_type s T hTy
      by_cases hEmptyTrue : __str_is_empty s = Term.Boolean true
      · have hOver :
            __str_multiset_overapprox s =
              Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof s) := by
          unfold __str_multiset_overapprox
          split <;> try simp_all
          rw [eo_ite_true,
            SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hTyNe]
        constructor
        · rw [hOver]
          trivial
        · rw [hOver]
          trivial
      · obtain ⟨bEmpty, _hEmptyBool⟩ := str_is_empty_boolean_of_ne_stuck s hsNe
        have hEmptyFalse : __str_is_empty s = Term.Boolean false := by
          cases bEmpty <;> simp_all
        by_cases hStrTrue : __eo_is_str s = Term.Boolean true
        · obtain ⟨w, rfl⟩ := eo_is_str_true_cases s hStrTrue
          have hOver :
              __str_multiset_overapprox (Term.String w) =
                __str_multiset_overapprox_word (charChainTerm w) := by
            change __eo_ite (__str_is_empty (Term.String w))
                (__eo_mk_apply (Term.UOp UserOp._at__at_TypedList_nil)
                  (__eo_typeof (Term.String w)))
                (__eo_ite (__eo_is_str (Term.String w))
                  (__str_multiset_overapprox_word
                    (__str_flatten (__str_nary_intro (Term.String w))))
                  (__eo_mk_apply
                    (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons)
                      (Term.String w))
                    (__eo_nil (Term.UOp UserOp._at__at_TypedList_cons)
                      (__eo_typeof (Term.String w))))) = _
            rw [hEmptyFalse, eo_ite_false,
              show __eo_is_str (Term.String w) = Term.Boolean true by
                simp [__eo_is_str, __eo_is_str_internal, native_teq,
                  SmtEval.native_and, SmtEval.native_not],
              eo_ite_true, flatten_nary_intro_string]
          obtain ⟨hWordTL, _⟩ :=
            str_multiset_overapprox_word_charChain_sound M (SmtValue.Boolean false) w
          constructor
          · rwa [hOver]
          · rw [hOver]
            exact str_multiset_overapprox_word_charChain_noAtom M hM T w
              (charAtoms_type w T hTy)
        · obtain ⟨bStr, _hStrBool⟩ := eo_is_str_boolean_of_ne_stuck s hsNe
          have hStrFalse : __eo_is_str s = Term.Boolean false := by
            cases bStr <;> simp_all
          let nil := Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof s)
          have hNilEq :
              __eo_nil (Term.UOp UserOp._at__at_TypedList_cons) (__eo_typeof s) = nil := by
            exact eo_nil_typedList_eq (__eo_typeof s) hTyNe
          have hNilTL : SetsEvalOpSupport.IsTL nil := by
            dsimp [nil]
            trivial
          have hOver :
              __str_multiset_overapprox s =
                Term.Apply
                  (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s) nil := by
            unfold __str_multiset_overapprox
            split <;> try simp_all
            rw [eo_ite_false, eo_ite_false,
              SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp)
                (SetsEvalOpSupport.isTL_ne_stuck hNilTL)]
          constructor
          · rw [hOver]
            exact ⟨hsNe, hNilTL⟩
          · rw [hOver]
            constructor
            · exact noAtomOverlapElem_opaque M hM T s hTy hStrFalse
                hEmptyFalse (fun a b h => hNotConcat a b h)
            · trivial

theorem erase_rec_isTL :
    ∀ L a : Term, SetsEvalOpSupport.IsTL L -> a ≠ Term.Stuck ->
      SetsEvalOpSupport.IsTL (__eo_list_erase_rec L a) := by
  intro L
  induction L using SetsEvalOpSupport.IsTL.induct with
  | case1 x y ih =>
      intro a hL ha
      obtain ⟨hxNe, hyTL⟩ := hL
      have hTailTL := ih a hyTL ha
      have hTailNe : __eo_list_erase_rec y a ≠ Term.Stuck :=
        SetsEvalOpSupport.isTL_ne_stuck hTailTL
      rw [SetsEvalOpSupport.erase_rec_cons
        (Term.UOp UserOp._at__at_TypedList_cons) x y a ha,
        eo_eq_val x a hxNe ha]
      cases hteq : native_teq a x
      · rw [eo_ite_false,
          SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hTailNe]
        exact ⟨hxNe, hTailTL⟩
      · rw [eo_ite_true]
        exact hyTL
  | case2 U =>
      intro a hL ha
      have hEq :
          __eo_list_erase_rec
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) U) a =
            Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) U := by
        unfold __eo_list_erase_rec
        split <;> simp_all
      rw [hEq]
      trivial
  | case3 t _ _ =>
      intro a hL
      exact absurd hL (by cases t <;> simp_all [SetsEvalOpSupport.IsTL])

theorem noAtomOverlapList_erase_rec
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType) :
    ∀ L a : Term, SetsEvalOpSupport.IsTL L -> NoAtomOverlapList M hM T L ->
      a ≠ Term.Stuck ->
      NoAtomOverlapList M hM T (__eo_list_erase_rec L a) := by
  intro L
  induction L using SetsEvalOpSupport.IsTL.induct with
  | case1 x y ih =>
      intro a hL hNo ha
      obtain ⟨hxNe, hyTL⟩ := hL
      obtain ⟨hElem, hTailNo⟩ := hNo
      have hTailNoEr := ih a hyTL hTailNo ha
      have hTailTL : SetsEvalOpSupport.IsTL (__eo_list_erase_rec y a) :=
        erase_rec_isTL y a hyTL ha
      have hTailNe : __eo_list_erase_rec y a ≠ Term.Stuck :=
        SetsEvalOpSupport.isTL_ne_stuck hTailTL
      rw [SetsEvalOpSupport.erase_rec_cons
        (Term.UOp UserOp._at__at_TypedList_cons) x y a ha,
        eo_eq_val x a hxNe ha]
      cases hteq : native_teq a x
      · rw [eo_ite_false,
          SetsEvalOpSupport.mk_apply_of_ne_stuck (by simp) hTailNe]
        exact ⟨hElem, hTailNoEr⟩
      · rw [eo_ite_true]
        exact hTailNo
  | case2 U =>
      intro a hL hNo ha
      have hEq :
          __eo_list_erase_rec
              (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) U) a =
            Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) U := by
        unfold __eo_list_erase_rec
        split <;> simp_all
      rw [hEq]
      exact hNo
  | case3 t _ _ =>
      intro a hL
      exact absurd hL (by cases t <;> simp_all [SetsEvalOpSupport.IsTL])

theorem noAtomOverlapList_erase
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType)
    (L a : Term)
    (hL : SetsEvalOpSupport.IsTL L)
    (hNoL : NoAtomOverlapList M hM T L)
    (ha : a ≠ Term.Stuck) :
    NoAtomOverlapList M hM T
      (__eo_list_erase (Term.UOp UserOp._at__at_TypedList_cons) L a) := by
  rw [show __eo_list_erase (Term.UOp UserOp._at__at_TypedList_cons) L a =
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L)
        (Term.Boolean true) (__eo_list_erase_rec L a) from rfl,
    SetsEvalOpSupport.isTL_is_list L hL, SetsEvalOpSupport.req_tt]
  exact noAtomOverlapList_erase_rec M hM T L a hL hNoL ha

theorem erase_isTL (L a : Term)
    (hL : SetsEvalOpSupport.IsTL L) (ha : a ≠ Term.Stuck) :
    SetsEvalOpSupport.IsTL
      (__eo_list_erase (Term.UOp UserOp._at__at_TypedList_cons) L a) := by
  rw [show __eo_list_erase (Term.UOp UserOp._at__at_TypedList_cons) L a =
      __eo_requires (__eo_is_list (Term.UOp UserOp._at__at_TypedList_cons) L)
        (Term.Boolean true) (__eo_list_erase_rec L a) from rfl,
    SetsEvalOpSupport.isTL_is_list L hL, SetsEvalOpSupport.req_tt]
  exact erase_rec_isTL L a hL ha

theorem atomTypedList_cons (T : SmtType) (x xs : Term)
    (hxAtom : AtomTerm x)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxs : AtomTypedList T xs) :
    AtomTypedList T
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) := by
  exact ⟨hxAtom, hxTy, hxs⟩

theorem typedList_cons_isTL (x xs : Term)
    (hx : x ≠ Term.Stuck) (hxs : SetsEvalOpSupport.IsTL xs) :
    SetsEvalOpSupport.IsTL
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) := by
  exact ⟨hx, hxs⟩

theorem str_multiset_subset_strict_concat_eq
    (s ss xs nr : Term)
    (hxs : xs ≠ Term.Stuck) (hnr : nr ≠ Term.Stuck) :
    __str_is_multiset_subset_strict
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) ss) xs nr =
      let xs' := __eo_list_erase (Term.UOp UserOp._at__at_TypedList_cons) xs s
      __str_is_multiset_subset_strict ss xs'
        (__eo_ite (__eo_eq xs xs')
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s) nr)
          nr) := by
  cases xs <;> first | exact absurd rfl hxs | (cases nr <;> first | exact absurd rfl hnr | rfl)

theorem str_multiset_subset_strict_empty_eq
    (emp xs nr : Term)
    (hemp : __str_is_empty emp = Term.Boolean true)
    (hxs : xs ≠ Term.Stuck) (hnr : nr ≠ Term.Stuck) :
    __str_is_multiset_subset_strict emp xs nr =
      __str_is_multiset_subset_strict_done xs nr := by
  rcases str_is_empty_cases emp hemp with ⟨U, rfl⟩ | rfl
  · cases xs <;> first | exact absurd rfl hxs | (
      cases nr <;> first | exact absurd rfl hnr | (
        change __eo_ite (Term.Boolean true)
            (__str_is_multiset_subset_strict_done _ _) _ =
          __str_is_multiset_subset_strict_done _ _
        rfl))
  · cases xs <;> first | exact absurd rfl hxs | (
      cases nr <;> first | exact absurd rfl hnr | (
        change __eo_ite (Term.Boolean true)
            (__str_is_multiset_subset_strict_done _ _) _ =
          __str_is_multiset_subset_strict_done _ _
        rfl))

theorem atomTypedList_cons_count_pos
    (M : SmtModel) (T : SmtType) (s : Term)
    (hsAtom : AtomTerm s) :
    seqTermValueCount M (seqElemVal M s) s = 1 := by
  rw [seqTermValueCount_of_atom_shape M (seqElemVal M s) (seqElemVal M s) s hsAtom rfl]
  simp [native_veq]

theorem str_multiset_subset_strict_done_cons_eq
    (xs s rest : Term) (hxs : xs ≠ Term.Stuck) :
    __str_is_multiset_subset_strict_done xs
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s) rest) =
      __eo_ite (__eo_is_z (__str_value_len s))
        (__eo_ite
          (__eo_and (__eo_gt (__str_value_len s) (Term.Numeral 0))
            (__are_distinct_terms_list_rec s xs (__eo_typeof s)))
          (Term.Boolean true)
          (__str_is_multiset_subset_strict_done xs rest))
        (__str_is_multiset_subset_strict_done xs rest) := by
  cases xs <;> first | exact absurd rfl hxs | rfl

theorem str_multiset_subset_strict_done_nil_eq
    (xs U : Term) (hxs : xs ≠ Term.Stuck) :
    __str_is_multiset_subset_strict_done xs
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) U) =
      Term.Boolean false := by
  cases xs <;> first | exact absurd rfl hxs | rfl

theorem str_is_multiset_subset_strict_done_count_lt
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType) :
    ∀ xs nr : Term,
      SetsEvalOpSupport.IsTL xs ->
      NoAtomOverlapList M hM T xs ->
      SetsEvalOpSupport.IsTL nr ->
      AtomTypedList T nr ->
      __str_is_multiset_subset_strict_done xs nr = Term.Boolean true ->
      ∃ v : SmtValue,
        eoListSeqValueCount M v xs < eoListSeqValueCount M v nr := by
  intro xs nr hXsTL hNoXs hNrTL hAtoms hDone
  induction nr using SetsEvalOpSupport.IsTL.induct generalizing xs with
  | case1 s rest ih =>
      obtain ⟨_hsNe, hRestTL⟩ := hNrTL
      obtain ⟨hsAtom, hsTy, hRestAtoms⟩ := hAtoms
      rw [str_multiset_subset_strict_done_cons_eq xs s rest
        (SetsEvalOpSupport.isTL_ne_stuck hXsTL)] at hDone
      change __eo_ite (__eo_is_z (__str_value_len s))
          (__eo_ite
            (__eo_and (__eo_gt (__str_value_len s) (Term.Numeral 0))
              (__are_distinct_terms_list_rec s xs (__eo_typeof s)))
            (Term.Boolean true)
            (__str_is_multiset_subset_strict_done xs rest))
          (__str_is_multiset_subset_strict_done xs rest) =
        Term.Boolean true at hDone
      let finishRec
          (hRec : __str_is_multiset_subset_strict_done xs rest = Term.Boolean true) :
          ∃ v : SmtValue,
            eoListSeqValueCount M v xs <
              eoListSeqValueCount M v
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) s)
                  rest) := by
        obtain ⟨v, hv⟩ := ih xs hXsTL hNoXs hRestTL hRestAtoms hRec
        refine ⟨v, ?_⟩
        simp [eoListSeqValueCount]
        omega
      rcases eo_ite_true_cases_local hDone with ⟨_hZ, hInner⟩ | ⟨_hNZ, hRec⟩
      · rcases eo_ite_true_cases_local hInner with ⟨hAnd, _⟩ | ⟨_hAndFalse, hRec⟩
        · obtain ⟨_hGt, hDistinct⟩ := eo_and_true_split _ _ hAnd
          let v := seqElemVal M s
          have hXsZero :
              eoListSeqValueCount M v xs = 0 :=
            noAtomOverlapList_distinct_zero M hM T xs hXsTL hNoXs
              s hsAtom hsTy hDistinct
          have hsOne : seqTermValueCount M v s = 1 :=
            atomTypedList_cons_count_pos M T s hsAtom
          refine ⟨v, ?_⟩
          rw [hXsZero]
          simp [eoListSeqValueCount, hsOne]
          omega
        · exact finishRec hRec
      · exact finishRec hRec
  | case2 U =>
      rw [str_multiset_subset_strict_done_nil_eq xs U
        (SetsEvalOpSupport.isTL_ne_stuck hXsTL)] at hDone
      cases hDone
  | case3 t _ _ =>
      exact absurd hNrTL (by cases t <;> simp_all [SetsEvalOpSupport.IsTL])

theorem str_is_multiset_subset_strict_atomChain_count_lt
    (M : SmtModel) (hM : model_total_typed M) (T : SmtType) :
    ∀ atoms : List Term, ∀ ex xs nr : Term,
      __str_is_empty ex = Term.Boolean true ->
      (∀ a ∈ atoms, AtomTerm a) ->
      (∀ a ∈ atoms, __smtx_typeof (__eo_to_smt a) = SmtType.Seq T) ->
      SetsEvalOpSupport.IsTL xs ->
      NoAtomOverlapList M hM T xs ->
      SetsEvalOpSupport.IsTL nr ->
      AtomTypedList T nr ->
      __str_is_multiset_subset_strict (atomChainTerm atoms ex) xs nr =
        Term.Boolean true ->
      ∃ v : SmtValue,
        eoListSeqValueCount M v xs <
          flatSeqValueCount M v (atomChainTerm atoms ex) +
            eoListSeqValueCount M v nr
  | [], ex, xs, nr, hExEmpty, _hAtoms, _hAtomTy, hXsTL, hNoXs, hNrTL, hNrAtoms,
      hStrict => by
      have hDone :
          __str_is_multiset_subset_strict_done xs nr = Term.Boolean true := by
        rw [← str_multiset_subset_strict_empty_eq ex xs nr hExEmpty
          (SetsEvalOpSupport.isTL_ne_stuck hXsTL)
          (SetsEvalOpSupport.isTL_ne_stuck hNrTL)]
        simpa [atomChainTerm] using hStrict
      obtain ⟨v, hv⟩ :=
        str_is_multiset_subset_strict_done_count_lt M hM T xs nr
          hXsTL hNoXs hNrTL hNrAtoms hDone
      refine ⟨v, ?_⟩
      rw [show atomChainTerm [] ex = ex from rfl,
        flatSeqValueCount_of_empty M v ex hExEmpty]
      omega
  | a :: atoms, ex, xs, nr, hExEmpty, hAtoms, hAtomTy, hXsTL, hNoXs, hNrTL,
      hNrAtoms, hStrict => by
      have haAtom : AtomTerm a := hAtoms a (by simp)
      have haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T := hAtomTy a (by simp)
      have haNe : a ≠ Term.Stuck := term_ne_stuck_of_smt_seq_type a T haTy
      have hNrNe : nr ≠ Term.Stuck := SetsEvalOpSupport.isTL_ne_stuck hNrTL
      rw [atomChainTerm_cons] at hStrict
      rw [str_multiset_subset_strict_concat_eq a (atomChainTerm atoms ex) xs nr
        (SetsEvalOpSupport.isTL_ne_stuck hXsTL) hNrNe] at hStrict
      let xs' := __eo_list_erase (Term.UOp UserOp._at__at_TypedList_cons) xs a
      have hXs'TL : SetsEvalOpSupport.IsTL xs' := erase_isTL xs a hXsTL haNe
      have hNoXs' : NoAtomOverlapList M hM T xs' :=
        noAtomOverlapList_erase M hM T xs a hXsTL hNoXs haNe
      have hXs'Ne : xs' ≠ Term.Stuck := SetsEvalOpSupport.isTL_ne_stuck hXs'TL
      rw [show __eo_list_erase (Term.UOp UserOp._at__at_TypedList_cons) xs a = xs' from rfl]
        at hStrict
      change __str_is_multiset_subset_strict (atomChainTerm atoms ex) xs'
          (__eo_ite (__eo_eq xs xs')
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) a) nr)
            nr) =
        Term.Boolean true at hStrict
      rw [eo_eq_val xs xs' (SetsEvalOpSupport.isTL_ne_stuck hXsTL) hXs'Ne] at hStrict
      cases hEq : native_teq xs' xs
      · rw [hEq, eo_ite_false] at hStrict
        obtain ⟨v, hv⟩ :=
          str_is_multiset_subset_strict_atomChain_count_lt M hM T atoms ex xs' nr
            hExEmpty
            (fun b hb => hAtoms b (by simp [hb]))
            (fun b hb => hAtomTy b (by simp [hb]))
            hXs'TL hNoXs' hNrTL hNrAtoms hStrict
        have hErase :=
          eoListSeqValueCount_erase_le M v xs a hXsTL haNe
        change eoListSeqValueCount M v xs <=
            eoListSeqValueCount M v xs' + seqTermValueCount M v a at hErase
        refine ⟨v, ?_⟩
        rw [atomChainTerm_cons]
        simp [flatSeqValueCount]
        omega
      · have hxsEq : xs' = xs := of_decide_eq_true hEq
        rw [hEq, eo_ite_true] at hStrict
        have hNrConsTL :
            SetsEvalOpSupport.IsTL
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) a) nr) :=
          typedList_cons_isTL a nr haNe hNrTL
        have hNrConsAtoms :
            AtomTypedList T
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) a) nr) :=
          atomTypedList_cons T a nr haAtom haTy hNrAtoms
        obtain ⟨v, hv⟩ :=
          str_is_multiset_subset_strict_atomChain_count_lt M hM T atoms ex xs'
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) a) nr)
            hExEmpty
            (fun b hb => hAtoms b (by simp [hb]))
            (fun b hb => hAtomTy b (by simp [hb]))
            hXs'TL hNoXs' hNrConsTL hNrConsAtoms hStrict
        refine ⟨v, ?_⟩
        rw [atomChainTerm_cons]
        simp [flatSeqValueCount, eoListSeqValueCount] at hv ⊢
        rw [hxsEq] at hv
        omega

axiom str_is_multiset_subset_strict_flat_count_lt
    (M : SmtModel) (hM : model_total_typed M)
    (needle : Term) (S : SmtSeq) (T : SmtType) (xs nrTy : Term)
    (hNeedleTy : __smtx_typeof (__eo_to_smt needle) = SmtType.Seq T)
    (hNeedleEval : __smtx_model_eval M (__eo_to_smt needle) = SmtValue.Seq S)
    (hXsTL : SetsEvalOpSupport.IsTL xs)
    (hNoXs : NoAtomOverlapList M hM T xs)
    (hStrict :
      __str_is_multiset_subset_strict
          (__str_flatten (__str_nary_intro needle)) xs
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) nrTy) =
        Term.Boolean true) :
    ∃ v : SmtValue,
      eoListSeqValueCount M v xs < valueCount v (native_unpack_seq S)

theorem str_ctn_multiset_subset_contains_false
    (M : SmtModel) (hM : model_total_typed M)
    (hay needle : Term) (T : SmtType)
    (hHayTy : __smtx_typeof (__eo_to_smt hay) = SmtType.Seq T)
    (hNeedleTy : __smtx_typeof (__eo_to_smt needle) = SmtType.Seq T)
    (hStrict :
      __str_is_multiset_subset_strict
        (__str_flatten (__str_nary_intro needle))
        (__str_multiset_overapprox hay)
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) (__eo_typeof hay)) =
      Term.Boolean true) :
    __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) hay) needle)) =
      SmtValue.Boolean false := by
  obtain ⟨Shay, hHayEval⟩ := eval_seq_of_type M hM hay T hHayTy
  obtain ⟨Sneedle, hNeedleEval⟩ := eval_seq_of_type M hM needle T hNeedleTy
  obtain ⟨hOverTL, hNoOver⟩ :=
    str_multiset_overapprox_noAtom M hM hay T hHayTy
  obtain ⟨v, hStrictCount⟩ :=
    str_is_multiset_subset_strict_flat_count_lt M hM needle Sneedle T
      (__str_multiset_overapprox hay) (__eo_typeof hay)
      hNeedleTy hNeedleEval hOverTL hNoOver hStrict
  have hContainsFalse :
      native_seq_contains (native_unpack_seq Shay) (native_unpack_seq Sneedle) =
        false := by
    cases hc : native_seq_contains (native_unpack_seq Shay) (native_unpack_seq Sneedle)
    · rfl
    · have hNeedleHay :
          valueCount v (native_unpack_seq Sneedle) <=
            valueCount v (native_unpack_seq Shay) :=
        valueCount_contains_le v hc
      have hHayOver :
          valueCount v (native_unpack_seq Shay) <=
            eoListSeqValueCount M v (__str_multiset_overapprox hay) :=
        (str_multiset_overapprox_sound M hM v hay Shay T hHayTy hHayEval).2
      omega
  rw [strContains_eval_eq M hay needle Shay Sneedle hHayEval hNeedleEval,
    hContainsFalse]

end RuleProofs
