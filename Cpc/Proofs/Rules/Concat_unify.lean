import Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev concatUnifyNormalize (rev x : Term) : Term :=
  __eo_ite rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x))
    (__str_nary_intro x)

private abbrev concatUnifyHead (rev x : Term) : Term :=
  __eo_list_nth (Term.UOp UserOp.str_concat) (concatUnifyNormalize rev x)
    (Term.Numeral 0)

private abbrev concatUnifyBody (rev s t s1 t1 : Term) : Term :=
  __eo_requires (concatUnifyHead rev s) s1
    (__eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1))

private abbrev mkStrLen (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_len) x

private theorem smt_seq_rel_pack_prefix_of_eq_length (T : SmtType) :
    ∀ xs ys xs' ys' : List SmtValue,
      xs.length = ys.length ->
      RuleProofs.smt_seq_rel (native_pack_seq T (xs ++ xs'))
        (native_pack_seq T (ys ++ ys')) ->
      RuleProofs.smt_seq_rel (native_pack_seq T xs)
        (native_pack_seq T ys)
  | [], [], xs', ys', _hLen, _hRel => by
      simp [native_pack_seq, RuleProofs.smt_seq_rel, __smtx_model_eval_eq]
  | [], _ :: _, xs', ys', hLen, _hRel => by
      cases hLen
  | _ :: _, [], xs', ys', hLen, _hRel => by
      cases hLen
  | x :: xs, y :: ys, xs', ys', hLen, hRel => by
      have hTailLen : xs.length = ys.length := by
        simpa using Nat.succ.inj hLen
      simp [RuleProofs.smt_seq_rel, native_pack_seq,
        __smtx_model_eval_eq, native_veq, SmtEval.native_and] at hRel ⊢
      exact ⟨hRel.1,
        smt_seq_rel_pack_prefix_of_eq_length T xs ys xs' ys' hTailLen
          hRel.2⟩

private theorem smt_seq_rel_pack_suffix_of_eq_length (T : SmtType) :
    ∀ xs ys sx sy : List SmtValue,
      sx.length = sy.length ->
      RuleProofs.smt_seq_rel (native_pack_seq T (xs ++ sx))
        (native_pack_seq T (ys ++ sy)) ->
      RuleProofs.smt_seq_rel (native_pack_seq T sx)
        (native_pack_seq T sy)
  | [], [], sx, sy, _hLen, hRel => by
      simpa using hRel
  | [], y :: ys, sx, sy, hLen, hRel => by
      have hTotal := smt_seq_rel_pack_length_eq T T sx ((y :: ys) ++ sy) hRel
      simp at hTotal
      omega
  | x :: xs, [], sx, sy, hLen, hRel => by
      have hTotal := smt_seq_rel_pack_length_eq T T ((x :: xs) ++ sx) sy hRel
      simp at hTotal
      omega
  | x :: xs, y :: ys, sx, sy, hLen, hRel => by
      simp [RuleProofs.smt_seq_rel, native_pack_seq,
        __smtx_model_eval_eq, native_veq, SmtEval.native_and] at hRel
      exact smt_seq_rel_pack_suffix_of_eq_length T xs ys sx sy hLen hRel.2

private theorem seq_unpack_length_eq_of_str_len_eq
    (M : SmtModel) (hM : model_total_typed M) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hLen : eo_interprets M (mkEq (mkStrLen x) (mkStrLen y)) true) :
    ∃ sx sy : SmtSeq,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ∧
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ∧
      (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  have hLenRel := RuleProofs.eo_interprets_eq_rel M (mkStrLen x)
    (mkStrLen y) hLen
  have hLenEq :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
    have hxLenTranslate :
        __eo_to_smt (mkStrLen x) = SmtTerm.str_len (__eo_to_smt x) := by
      rfl
    have hyLenTranslate :
        __eo_to_smt (mkStrLen y) = SmtTerm.str_len (__eo_to_smt y) := by
      rfl
    rw [hxLenTranslate, hyLenTranslate] at hLenRel
    rw [__smtx_model_eval.eq_78, __smtx_model_eval.eq_78] at hLenRel
    unfold RuleProofs.smt_value_rel at hLenRel
    simp [hxEval, hyEval, __smtx_model_eval_str_len, __smtx_model_eval_eq,
      native_seq_len] at hLenRel
    unfold native_veq at hLenRel
    simp at hLenRel
    exact_mod_cast hLenRel
  exact ⟨sx, sy, hxEval, hyEval, hLenEq⟩

private theorem smt_value_rel_str_concat_heads_of_len_eq
    (M : SmtModel) (hM : model_total_typed M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x xs)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y ys))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hxsValTy := smt_model_eval_preserves_type M hM (__eo_to_smt xs)
    (SmtType.Seq T) hxsTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hxsValTy with ⟨sxs, hxsEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hLenXY :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length :=
    hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
    at hRel
  rw [hxEval, hxsEval, hyEval, hysEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sxs)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sys))) =
      SmtValue.Boolean true at hRel
  rw [hsxElem, hsyElem] at hRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  change RuleProofs.smt_seq_rel
    (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sxs))
    (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sys)) at hRel
  have hHeadPack :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sx))
        (native_pack_seq T (native_unpack_seq sy)) :=
    smt_seq_rel_pack_prefix_of_eq_length T (native_unpack_seq sx)
      (native_unpack_seq sy) (native_unpack_seq sxs)
      (native_unpack_seq sys) hLenXY hRel
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hHeadPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy)))

private theorem smt_value_rel_str_concat_tails_of_len_eq
    (M : SmtModel) (hM : model_total_typed M) (xs x ys y : Term)
    (T : SmtType)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hLen :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat xs x)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat ys y))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hRel
  have hxsValTy := smt_model_eval_preserves_type M hM (__eo_to_smt xs)
    (SmtType.Seq T) hxsTy (seq_ne_none T) (type_inhabited_seq T)
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hysValTy := smt_model_eval_preserves_type M hM (__eo_to_smt ys)
    (SmtType.Seq T) hysTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxsValTy with ⟨sxs, hxsEval⟩
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hysValTy with ⟨sys, hysEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  have hsxsTy : __smtx_typeof_seq_value sxs = SmtType.Seq T := by
    simpa [hxsEval, __smtx_typeof_value] using hxsValTy
  have hsysTy : __smtx_typeof_seq_value sys = SmtType.Seq T := by
    simpa [hysEval, __smtx_typeof_value] using hysValTy
  have hsxsElem : __smtx_elem_typeof_seq_value sxs = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxsTy
  have hsysElem : __smtx_elem_typeof_seq_value sys = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsysTy
  have hLenXY :
      (native_unpack_seq sx).length = (native_unpack_seq sy).length :=
    hLen sx sy hxEval hyEval
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
    at hRel
  rw [hxsEval, hxEval, hysEval, hyEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sxs)
      (native_unpack_seq sxs ++ native_unpack_seq sx)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sys)
      (native_unpack_seq sys ++ native_unpack_seq sy))) =
      SmtValue.Boolean true at hRel
  rw [hsxsElem, hsysElem] at hRel
  rw [hxEval, hyEval]
  change RuleProofs.smt_seq_rel sx sy
  change RuleProofs.smt_seq_rel
    (native_pack_seq T (native_unpack_seq sxs ++ native_unpack_seq sx))
    (native_pack_seq T (native_unpack_seq sys ++ native_unpack_seq sy)) at hRel
  have hTailPack :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sx))
        (native_pack_seq T (native_unpack_seq sy)) :=
    smt_seq_rel_pack_suffix_of_eq_length T (native_unpack_seq sxs)
      (native_unpack_seq sys) (native_unpack_seq sx)
      (native_unpack_seq sy) hLenXY hRel
  exact RuleProofs.smt_seq_rel_trans sx
    (native_pack_seq T (native_unpack_seq sx)) sy
    (smt_seq_rel_pack_unpack T sx)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sy)) sy hTailPack
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy)))

private theorem eo_interprets_str_concat_heads_of_len_eq_of_seq
    (M : SmtModel) (hM : model_total_typed M) (x xs y ys : Term)
    (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hLen : eo_interprets M (mkEq (mkStrLen x) (mkStrLen y)) true)
    (hEq : eo_interprets M (mkEq (mkConcat x xs) (mkConcat y ys)) true) :
    eo_interprets M (mkEq x y) true := by
  rcases seq_unpack_length_eq_of_str_len_eq M hM x y T hxTy hyTy hLen with
    ⟨sx0, sy0, hxEval0, hyEval0, hLen0⟩
  have hLenEval :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
    intro sx sy hxEval hyEval
    rw [hxEval] at hxEval0
    injection hxEval0 with hsx
    rw [hyEval] at hyEval0
    injection hyEval0 with hsy
    subst sx0
    subst sy0
    exact hLen0
  have hRel := RuleProofs.eo_interprets_eq_rel M
    (mkConcat x xs) (mkConcat y ys) hEq
  have hXYRel :=
    smt_value_rel_str_concat_heads_of_len_eq M hM x xs y ys T hxTy
      hxsTy hyTy hysTy hLenEval hRel
  have hXYBool : RuleProofs.eo_has_bool_type (mkEq x y) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hxTy, hyTy]
    · rw [hxTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M x y hXYBool hXYRel

private theorem eo_interprets_str_concat_tails_of_len_eq_of_seq
    (M : SmtModel) (hM : model_total_typed M) (xs x ys y : Term)
    (T : SmtType)
    (hxsTy : __smtx_typeof (__eo_to_smt xs) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hysTy : __smtx_typeof (__eo_to_smt ys) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hLen : eo_interprets M (mkEq (mkStrLen x) (mkStrLen y)) true)
    (hEq : eo_interprets M (mkEq (mkConcat xs x) (mkConcat ys y)) true) :
    eo_interprets M (mkEq x y) true := by
  rcases seq_unpack_length_eq_of_str_len_eq M hM x y T hxTy hyTy hLen with
    ⟨sx0, sy0, hxEval0, hyEval0, hLen0⟩
  have hLenEval :
      (sx sy : SmtSeq) ->
        __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx ->
        __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy ->
        (native_unpack_seq sx).length = (native_unpack_seq sy).length := by
    intro sx sy hxEval hyEval
    rw [hxEval] at hxEval0
    injection hxEval0 with hsx
    rw [hyEval] at hyEval0
    injection hyEval0 with hsy
    subst sx0
    subst sy0
    exact hLen0
  have hRel := RuleProofs.eo_interprets_eq_rel M
    (mkConcat xs x) (mkConcat ys y) hEq
  have hXYRel :=
    smt_value_rel_str_concat_tails_of_len_eq M hM xs x ys y T hxsTy
      hxTy hysTy hyTy hLenEval hRel
  have hXYBool : RuleProofs.eo_has_bool_type (mkEq x y) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hxTy, hyTy]
    · rw [hxTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M x y hXYBool hXYRel

private theorem list_nth_zero_eq_cons_of_ne_stuck (f a x : Term)
    (hNthEq : __eo_list_nth f a (Term.Numeral 0) = x)
    (hNthNe : __eo_list_nth f a (Term.Numeral 0) ≠ Term.Stuck) :
    ∃ tail,
      a = Term.Apply (Term.Apply f x) tail ∧
        __eo_is_list f tail = Term.Boolean true := by
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_list_nth_rec a (Term.Numeral 0)) ≠ Term.Stuck := by
    simpa [__eo_list_nth] using hNthNe
  have hList : __eo_is_list f a = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_nth_rec a (Term.Numeral 0)) hReq
  have hRecNe : __eo_list_nth_rec a (Term.Numeral 0) ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_list f a)
      (Term.Boolean true) (__eo_list_nth_rec a (Term.Numeral 0)) hReq
  have hReqEq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
          (__eo_list_nth_rec a (Term.Numeral 0)) =
        __eo_list_nth_rec a (Term.Numeral 0) :=
    eo_requires_eq_result_of_ne_stuck (__eo_is_list f a)
      (Term.Boolean true) (__eo_list_nth_rec a (Term.Numeral 0)) hReq
  have hRecEq : __eo_list_nth_rec a (Term.Numeral 0) = x := by
    rw [__eo_list_nth] at hNthEq
    rw [hReqEq] at hNthEq
    exact hNthEq
  cases a with
  | Stuck =>
      simp [__eo_list_nth_rec] at hRecNe
  | Apply g tail =>
      cases g with
      | Apply f' head =>
          have hHead : head = x := by
            simpa [__eo_list_nth_rec] using hRecEq
          have hFEq : f' = f :=
            eo_is_list_cons_head_eq_of_true f f' head tail hList
          subst head
          subst f'
          exact ⟨tail, rfl,
            eo_is_list_tail_true_of_cons_self f x tail hList⟩
      | _ =>
          simp [__eo_list_nth_rec] at hRecNe
  | _ =>
      simp [__eo_list_nth_rec] at hRecNe

private theorem eo_prog_concat_unify_eq_of_ne_stuck
    (rev s t s1 t1 : Term)
    (hProg :
      __eo_prog_concat_unify rev (Proof.pf (mkEq s t))
          (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) ≠ Term.Stuck) :
    __eo_prog_concat_unify rev (Proof.pf (mkEq s t))
        (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) =
      mkEq s1 t1 ∧
      concatUnifyHead rev s = s1 ∧ concatUnifyHead rev t = t1 := by
  have hProgBody :
      __eo_prog_concat_unify rev (Proof.pf (mkEq s t))
          (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) =
        concatUnifyBody rev s t s1 t1 := by
    cases rev
    case Stuck =>
      exact False.elim (hProg rfl)
    all_goals
      simp [__eo_prog_concat_unify, concatUnifyBody, concatUnifyHead,
        concatUnifyNormalize, mkEq]
  have hBodyNe : concatUnifyBody rev s t s1 t1 ≠ Term.Stuck := by
    simpa [hProgBody] using hProg
  have hHeadS :
      concatUnifyHead rev s = s1 :=
    eo_requires_eq_of_ne_stuck (concatUnifyHead rev s) s1
      (__eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1)) hBodyNe
  have hInnerNe :
      __eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1) ≠
        Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (concatUnifyHead rev s) s1
      (__eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1)) hBodyNe
  have hHeadT :
      concatUnifyHead rev t = t1 :=
    eo_requires_eq_of_ne_stuck (concatUnifyHead rev t) t1
      (mkEq s1 t1) hInnerNe
  have hOuterEq :
      concatUnifyBody rev s t s1 t1 =
        __eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1) :=
    eo_requires_eq_result_of_ne_stuck (concatUnifyHead rev s) s1
      (__eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1)) hBodyNe
  have hInnerEq :
      __eo_requires (concatUnifyHead rev t) t1 (mkEq s1 t1) =
        mkEq s1 t1 :=
    eo_requires_eq_result_of_ne_stuck (concatUnifyHead rev t) t1
      (mkEq s1 t1) hInnerNe
  exact ⟨by rw [hProgBody, hOuterEq, hInnerEq], hHeadS, hHeadT⟩

private theorem len_eq_seq_types_of_bool (x y : Term)
    (hLenBool : RuleProofs.eo_has_bool_type (mkEq (mkStrLen x) (mkStrLen y))) :
    ∃ T U,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt y) = SmtType.Seq U := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkStrLen x) (mkStrLen y) hLenBool with
    ⟨hSame, hLeftNN⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt (mkStrLen y)) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  have hLeftTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    simpa [mkStrLen] using hLeftNN
  have hRightTerm : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    simpa [mkStrLen] using hRightNN
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt x)) hLeftTerm with
    ⟨T, hxTy⟩
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt y)) hRightTerm with
    ⟨U, hyTyU⟩
  exact ⟨T, U, hxTy, hyTyU⟩

private theorem str_nary_intro_cons_seq_types_of_head_seq
    (x head tail : Term) (T : SmtType)
    (hIntroEq : __str_nary_intro x = mkConcat head tail)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T := by
  have hIntroNe : __str_nary_intro x ≠ Term.Stuck := by
    rw [hIntroEq]
    simp [mkConcat]
  by_cases hConcat : ∃ h tl : Term, x = mkConcat h tl
  · rcases hConcat with ⟨h, tl, rfl⟩
    have hEq : mkConcat h tl = mkConcat head tail := by
      simpa [str_nary_intro_concat_eq] using hIntroEq
    injection hEq with hFun hTailEq
    injection hFun with _ hHeadEq
    subst head
    subst tail
    rcases str_concat_args_of_non_none h tl hxNN with ⟨U, hhTy, htlTy⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hhTy, hHeadTy]
      injection hSeq
    exact ⟨smt_typeof_str_concat_of_seq h tl T
        (by simpa [hUT] using hhTy) (by simpa [hUT] using htlTy),
      by simpa [hUT] using htlTy⟩
  · rcases str_nary_intro_not_str_concat_cases_typeof_empty x hConcat hIntroNe with
      hIntroSelf | ⟨hIntroCons, _hEmptyNil⟩
    · rw [hIntroSelf] at hIntroEq
      exact False.elim (hConcat ⟨head, tail, hIntroEq⟩)
    · rw [hIntroCons] at hIntroEq
      injection hIntroEq with hFun hTailEq
      injection hFun with _ hHeadEq
      subst head
      subst tail
      have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := hHeadTy
      rcases smt_seq_component_wf_of_non_none_type (__eo_to_smt x) T
          hxTy with
        ⟨hTInh, hTWf⟩
      have hEmptyNN :
          __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
            SmtType.None :=
        seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T hxTy
          hTInh hTWf
      exact ⟨hxTy,
        by
          simpa using smt_typeof_seq_empty_typeof x T hxTy hEmptyNN⟩

private theorem eo_interprets_concat_unify_false
    (M : SmtModel) (hM : model_total_typed M)
    (s t s1 t1 : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hLenBool :
      RuleProofs.eo_has_bool_type (mkEq (mkStrLen s1) (mkStrLen t1)))
    (hFinalBool : RuleProofs.eo_has_bool_type (mkEq s1 t1))
    (hProg :
      __eo_prog_concat_unify (Term.Boolean false) (Proof.pf (mkEq s t))
          (Proof.pf (mkEq (mkStrLen s1) (mkStrLen t1))) ≠ Term.Stuck)
    (hST : eo_interprets M (mkEq s t) true)
    (hLen : eo_interprets M (mkEq (mkStrLen s1) (mkStrLen t1)) true) :
    eo_interprets M (mkEq s1 t1) true := by
  rcases eo_prog_concat_unify_eq_of_ne_stuck
      (Term.Boolean false) s t s1 t1 hProg with
    ⟨_, hHeadS, hHeadT⟩
  rcases len_eq_seq_types_of_bool s1 t1 hLenBool with
    ⟨T, _U, hs1Ty, _ht1TyU⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s1 t1 hFinalBool with
    ⟨hS1T1Same, hS1NN⟩
  have ht1Ty : __smtx_typeof (__eo_to_smt t1) = SmtType.Seq T := by
    rw [← hS1T1Same, hs1Ty]
  have hs1Ne : s1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s1 hS1NN
  have hT1NN :
      __smtx_typeof (__eo_to_smt t1) ≠ SmtType.None := by
    rw [ht1Ty]
    exact seq_ne_none T
  have ht1Ne : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1NN
  have hNthSEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) = s1 := by
    simpa [concatUnifyHead, concatUnifyNormalize, eo_ite_false] using hHeadS
  have hNthTEq :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) = t1 := by
    simpa [concatUnifyHead, concatUnifyNormalize, eo_ite_false] using hHeadT
  have hNthSNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro s)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthSEq]
    exact hs1Ne
  have hNthTNe :
      __eo_list_nth (Term.UOp UserOp.str_concat) (__str_nary_intro t)
          (Term.Numeral 0) ≠ Term.Stuck := by
    rw [hNthTEq]
    exact ht1Ne
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro s) s1
      hNthSEq hNthSNe with
    ⟨sTail, hIntroS, _hSTailList⟩
  rcases list_nth_zero_eq_cons_of_ne_stuck
      (Term.UOp UserOp.str_concat) (__str_nary_intro t) t1
      hNthTEq hNthTNe with
    ⟨tTail, hIntroT, _hTTailList⟩
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s t hPremBool with
    ⟨hSTSameTy, hSNN⟩
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSTSameTy]
    exact hSNN
  have hIntroSEq : __str_nary_intro s = mkConcat s1 sTail := hIntroS
  have hIntroTEq : __str_nary_intro t = mkConcat t1 tTail := hIntroT
  rcases str_nary_intro_cons_seq_types_of_head_seq s s1 sTail T
      hIntroSEq hs1Ty hSNN with
    ⟨hsTy, hsTailTy⟩
  rcases str_nary_intro_cons_seq_types_of_head_seq t t1 tTail T
      hIntroTEq ht1Ty hTNN with
    ⟨htTy, htTailTy⟩
  have hIntroSNe : __str_nary_intro s ≠ Term.Stuck := by
    rw [hIntroSEq]
    simp [mkConcat]
  have hIntroTNe : __str_nary_intro t ≠ Term.Stuck := by
    rw [hIntroTEq]
    simp [mkConcat]
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T := by
    rw [hIntroSEq]
    exact smt_typeof_str_concat_of_seq s1 sTail T hs1Ty hsTailTy
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T := by
    rw [hIntroTEq]
    exact smt_typeof_str_concat_of_seq t1 tTail T ht1Ty htTailTy
  have hIntroBool :
      RuleProofs.eo_has_bool_type
        (mkEq (__str_nary_intro s) (__str_nary_intro t)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hIntroSTy, hIntroTTy]
    · rw [hIntroSTy]
      exact seq_ne_none T
  have hIntroEq :
      eo_interprets M (mkEq (__str_nary_intro s) (__str_nary_intro t)) true :=
    eo_interprets_str_nary_intro_congr_of_seq M hM s t T hsTy htTy
      hIntroSNe hIntroTNe hST hIntroBool
  have hConcatEq :
      eo_interprets M (mkEq (mkConcat s1 sTail) (mkConcat t1 tTail)) true := by
    simpa [hIntroSEq, hIntroTEq] using hIntroEq
  exact eo_interprets_str_concat_heads_of_len_eq_of_seq M hM
    s1 sTail t1 tTail T hs1Ty hsTailTy ht1Ty htTailTy hLen hConcatEq

theorem cmd_step_concat_unify_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_unify args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_unify args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_unify args premises) :=
by
  sorry
