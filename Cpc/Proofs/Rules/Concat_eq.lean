import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.TypePreservation.Helpers
import Cpc.Proofs.TypePreservation.SeqStringRegex

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev mkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev mkConcat (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y

private theorem seq_ne_none (T : SmtType) : SmtType.Seq T ≠ SmtType.None := by
  intro h
  cases h

private theorem smtx_model_eval_str_concat_term_eq (M : SmtModel) (x y : Term) :
    __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
      __smtx_model_eval_str_concat (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  rw [show __eo_to_smt (mkConcat x y) =
      SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y) by
    rfl]
  rw [__smtx_model_eval.eq_79]

private theorem str_concat_args_of_non_none (x y : Term) :
    __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None ->
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  intro h
  have h' :
      term_has_non_none_type (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) := by
    simpa [term_has_non_none_type, mkConcat] using h
  exact seq_binop_args_of_non_none (op := SmtTerm.str_concat)
    (typeof_str_concat_eq (__eo_to_smt x) (__eo_to_smt y)) h'

private theorem eval_seq_empty_of_type (M : SmtModel) (A : Term) (T : SmtType) :
    __eo_to_smt_type A = SmtType.Seq T ->
    __smtx_model_eval M (__eo_to_smt (__seq_empty A)) =
      SmtValue.Seq (SmtSeq.empty T) := by
  intro hA
  by_cases hSpecial : A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst hSpecial
    simp [__eo_to_smt_type, __smtx_typeof_guard] at hA
    cases hA
    change __smtx_model_eval M (SmtTerm.String "") =
      SmtValue.Seq (SmtSeq.empty SmtType.Char)
    rw [__smtx_model_eval.eq_4]
    simp [native_pack_string, __smtx_ssm_char_values_of_string, native_pack_seq]
  · by_cases hStuck : A = Term.Stuck
    · subst hStuck
      simp [__eo_to_smt_type] at hA
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault]
      rw [show __eo_to_smt (Term.seq_empty A) =
          __eo_to_smt_seq_empty (__eo_to_smt_type A) by
        rfl]
      rw [hA]
      change __smtx_model_eval M (SmtTerm.seq_empty T) =
        SmtValue.Seq (SmtSeq.empty T)
      rw [__smtx_model_eval.eq_77]

private theorem eval_seq_empty_typeof (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  exact eval_seq_empty_of_type M (__eo_typeof x) T hA

private theorem eq_of_eo_eq_true_local (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem eo_ite_true (x y : Term) :
    __eo_ite (Term.Boolean true) x y = x := by
  rfl

private theorem eo_ite_false (x y : Term) :
    __eo_ite (Term.Boolean false) x y = y := by
  rfl

private theorem eo_ite_cases_of_ne_stuck (c x y : Term) :
    __eo_ite c x y ≠ Term.Stuck ->
    c = Term.Boolean true ∨ c = Term.Boolean false := by
  intro h
  by_cases hTrue : native_teq c (Term.Boolean true) = true
  · left
    simpa [native_teq] using hTrue
  · by_cases hFalse : native_teq c (Term.Boolean false) = true
    · right
      simpa [native_teq] using hFalse
    · simp [__eo_ite, hTrue, hFalse, SmtEval.native_ite] at h

private theorem eo_requires_self_eq_of_ne_stuck (x z : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_requires x x z = z := by
  simp [__eo_requires, hx, native_teq, SmtEval.native_ite, SmtEval.native_not]

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  by_cases hxy : native_teq x y = true
  · by_cases hxOk : native_not (native_teq x Term.Stuck) = true
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite]
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite] at h
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

private theorem pair_first_pair (x y : Term) :
    __pair_first (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) x) y) = x := by
  rfl

private theorem pair_second_pair (x y : Term) :
    __pair_second (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) x) y) = y := by
  rfl

private theorem str_strip_prefix_concat_of_eo_eq_true
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean true) :
    __str_strip_prefix (mkConcat t t2) (mkConcat u s2) =
      __str_strip_prefix t2 s2 := by
  change __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
    (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      __str_strip_prefix t2 s2
  rw [h, eo_ite_true]

private theorem str_strip_prefix_concat_of_eo_eq_false
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean false) :
    __str_strip_prefix (mkConcat t t2) (mkConcat u s2) =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) (mkConcat t t2))
        (mkConcat u s2) := by
  change __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
    (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) (mkConcat t t2))
        (mkConcat u s2)
  rw [h, eo_ite_false]
  simp [__eo_l_1___str_strip_prefix]

private theorem smt_seq_rel_pack_append_cancel (T : SmtType) :
    ∀ xs ys zs : List SmtValue,
      RuleProofs.smt_seq_rel
          (native_pack_seq T (xs ++ ys)) (native_pack_seq T (xs ++ zs)) ->
      RuleProofs.smt_seq_rel (native_pack_seq T ys) (native_pack_seq T zs)
  | [], _, _, h => h
  | _ :: xs, ys, zs, h => by
      apply smt_seq_rel_pack_append_cancel T xs ys zs
      unfold RuleProofs.smt_seq_rel at h ⊢
      simpa [native_pack_seq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_and, RuleProofs.smtx_model_eval_eq_refl] using h

private theorem smt_seq_rel_pack_length_eq (T U : SmtType) :
    ∀ xs ys : List SmtValue,
      RuleProofs.smt_seq_rel (native_pack_seq T xs) (native_pack_seq U ys) ->
      xs.length = ys.length
  | [], [], _ => rfl
  | [], _ :: _, h => by
      unfold RuleProofs.smt_seq_rel at h
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq] at h
  | _ :: _, [], h => by
      unfold RuleProofs.smt_seq_rel at h
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq] at h
  | _ :: xs, _ :: ys, h => by
      have ht : RuleProofs.smt_seq_rel (native_pack_seq T xs) (native_pack_seq U ys) := by
        unfold RuleProofs.smt_seq_rel at h ⊢
        simp [native_pack_seq, __smtx_model_eval_eq, native_veq,
          SmtEval.native_and] at h ⊢
        exact h.2
      exact congrArg Nat.succ (smt_seq_rel_pack_length_eq T U xs ys ht)

private theorem smt_seq_rel_pack_append_right_cancel (T : SmtType) :
    ∀ ys zs xs : List SmtValue,
      RuleProofs.smt_seq_rel
          (native_pack_seq T (ys ++ xs)) (native_pack_seq T (zs ++ xs)) ->
      RuleProofs.smt_seq_rel (native_pack_seq T ys) (native_pack_seq T zs)
  | [], [], _, _ => by
      unfold RuleProofs.smt_seq_rel
      simp [native_pack_seq, __smtx_model_eval_eq]
  | [], z :: zs, xs, h => by
      have hLen := smt_seq_rel_pack_length_eq T T xs ((z :: zs) ++ xs) h
      simp at hLen
      omega
  | y :: ys, [], xs, h => by
      have hLen := smt_seq_rel_pack_length_eq T T ((y :: ys) ++ xs) xs h
      simp at hLen
      omega
  | _ :: ys, _ :: zs, xs, h => by
      have ht :
          RuleProofs.smt_seq_rel
            (native_pack_seq T (ys ++ xs)) (native_pack_seq T (zs ++ xs)) := by
        unfold RuleProofs.smt_seq_rel at h ⊢
        simp [native_pack_seq, __smtx_model_eval_eq, native_veq,
          SmtEval.native_and] at h ⊢
        exact h.2
      unfold RuleProofs.smt_seq_rel at h ⊢
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_and] at h ⊢
      exact ⟨h.1, smt_seq_rel_pack_append_right_cancel T ys zs xs ht⟩

private theorem smt_seq_rel_pack_unpack (T : SmtType) :
    (s : SmtSeq) -> RuleProofs.smt_seq_rel s (native_pack_seq T (native_unpack_seq s))
  | SmtSeq.empty _ => by
      unfold RuleProofs.smt_seq_rel
      simp [native_unpack_seq, native_pack_seq, __smtx_model_eval_eq]
  | SmtSeq.cons v vs => by
      have ih := smt_seq_rel_pack_unpack T vs
      unfold RuleProofs.smt_seq_rel at ih ⊢
      simp [native_unpack_seq, native_pack_seq, __smtx_model_eval_eq,
        native_veq, SmtEval.native_and, RuleProofs.smtx_model_eval_eq_refl, ih]

private theorem smt_value_rel_str_concat_right_empty
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hEmpty := eval_seq_empty_typeof M x T hxTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hEmpty]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ []))) (SmtValue.Seq sx) =
      SmtValue.Boolean true
  rw [List.append_nil, hsxElem]
  change RuleProofs.smt_seq_rel (native_pack_seq T (native_unpack_seq sx)) sx
  exact RuleProofs.smt_seq_rel_symm sx (native_pack_seq T (native_unpack_seq sx))
    (smt_seq_rel_pack_unpack T sx)

private theorem smt_value_rel_str_concat_left_empty
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat (__seq_empty (__eo_typeof x)) x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hEmpty := eval_seq_empty_typeof M x T hxTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hEmpty]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value (SmtSeq.empty T))
      ([] ++ native_unpack_seq sx))) (SmtValue.Seq sx) =
      SmtValue.Boolean true
  simp [__smtx_elem_typeof_seq_value]
  change RuleProofs.smt_seq_rel (native_pack_seq T (native_unpack_seq sx)) sx
  exact RuleProofs.smt_seq_rel_symm sx (native_pack_seq T (native_unpack_seq sx))
    (smt_seq_rel_pack_unpack T sx)

private theorem smt_value_rel_str_nary_intro_ite
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (mkConcat x (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (mkConcat x (__seq_empty (__eo_typeof x))))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (mkConcat x (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x))
  · rw [hCond, eo_ite_false]
    exact smt_value_rel_str_concat_right_empty M hM x T hxTy

private theorem smt_value_rel_str_nary_elim_concat_ite
    (M : SmtModel) (hM : model_total_typed M) (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) ≠
        Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))))
      (__smtx_model_eval M (__eo_to_smt (mkConcat t ss))) := by
  have hConcatNN : __smtx_typeof (__eo_to_smt (mkConcat t ss)) ≠ SmtType.None := by
    rw [hConcatTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none t ss hConcatNN with ⟨U, htTy, hssTy⟩
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) hElim with
    hCond | hCond
  · have hEmptyEq := eq_of_eo_eq_true_local ss (__seq_empty (__eo_typeof t)) hCond
    have hssEq : ss = __seq_empty (__eo_typeof t) := hEmptyEq.symm
    subst ss
    rw [hCond, eo_ite_true]
    exact RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt (mkConcat t (__seq_empty (__eo_typeof t)))))
      (__smtx_model_eval M (__eo_to_smt t))
      (smt_value_rel_str_concat_right_empty M hM t U htTy)
  · rw [hCond, eo_ite_false]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (mkConcat t ss)))

private theorem smt_value_rel_str_nary_elim_requires
    (M : SmtModel) (t : Term)
    (hElim : __eo_requires t (__seq_empty (__eo_typeof t)) t ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_requires t (__seq_empty (__eo_typeof t)) t)))
      (__smtx_model_eval M (__eo_to_smt t)) := by
  rw [eo_requires_eq_result_of_ne_stuck t (__seq_empty (__eo_typeof t)) t hElim]
  exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt t))

private theorem eo_interprets_str_concat_right_empty_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x (__seq_empty (__eo_typeof x))) x)) :
    eo_interprets M (mkEq (mkConcat x (__seq_empty (__eo_typeof x))) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat x (__seq_empty (__eo_typeof x))) x hBool
    (smt_value_rel_str_concat_right_empty M hM x T hxTy)

private theorem eo_interprets_str_concat_left_empty_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat (__seq_empty (__eo_typeof x)) x) x)) :
    eo_interprets M (mkEq (mkConcat (__seq_empty (__eo_typeof x)) x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat (__seq_empty (__eo_typeof x)) x) x hBool
    (smt_value_rel_str_concat_left_empty M hM x T hxTy)

private theorem eo_interprets_str_nary_intro_ite_eq_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (mkConcat x (__seq_empty (__eo_typeof x))) ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (mkConcat x (__seq_empty (__eo_typeof x))))
        x)) :
    eo_interprets M
      (mkEq
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (mkConcat x (__seq_empty (__eo_typeof x))))
        x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (mkConcat x (__seq_empty (__eo_typeof x)))) x hBool
    (smt_value_rel_str_nary_intro_ite M hM x T hxTy hIntro)

private theorem eo_interprets_str_nary_elim_concat_ite_eq_of_bool
    (M : SmtModel) (hM : model_total_typed M) (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) ≠
        Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))
        (mkConcat t ss))) :
    eo_interprets M
      (mkEq
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))
        (mkConcat t ss)) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))
    (mkConcat t ss) hBool
    (smt_value_rel_str_nary_elim_concat_ite M hM t ss T hConcatTy hElim)

private theorem eo_interprets_str_nary_elim_requires_eq_of_bool
    (M : SmtModel) (t : Term)
    (hElim : __eo_requires t (__seq_empty (__eo_typeof t)) t ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__eo_requires t (__seq_empty (__eo_typeof t)) t) t)) :
    eo_interprets M
      (mkEq (__eo_requires t (__seq_empty (__eo_typeof t)) t) t) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__eo_requires t (__seq_empty (__eo_typeof t)) t) t hBool
    (smt_value_rel_str_nary_elim_requires M t hElim)

private theorem smt_seq_rel_concat_left_cancel (T : SmtType) (sx sy sz : SmtSeq) :
    RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sz)) ->
    RuleProofs.smt_seq_rel sy sz := by
  intro h
  have hTail := smt_seq_rel_pack_append_cancel T (native_unpack_seq sx)
    (native_unpack_seq sy) (native_unpack_seq sz) h
  exact RuleProofs.smt_seq_rel_trans sy (native_pack_seq T (native_unpack_seq sy)) sz
    (smt_seq_rel_pack_unpack T sy)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sz)) sz hTail
      (RuleProofs.smt_seq_rel_symm sz (native_pack_seq T (native_unpack_seq sz))
        (smt_seq_rel_pack_unpack T sz)))

private theorem smt_seq_rel_concat_right_cancel (T : SmtType) (sx sy sz : SmtSeq) :
    RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sz ++ native_unpack_seq sx)) ->
    RuleProofs.smt_seq_rel sy sz := by
  intro h
  have hTail := smt_seq_rel_pack_append_right_cancel T (native_unpack_seq sy)
    (native_unpack_seq sz) (native_unpack_seq sx) h
  exact RuleProofs.smt_seq_rel_trans sy (native_pack_seq T (native_unpack_seq sy)) sz
    (smt_seq_rel_pack_unpack T sy)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sz)) sz hTail
      (RuleProofs.smt_seq_rel_symm sz (native_pack_seq T (native_unpack_seq sz))
        (smt_seq_rel_pack_unpack T sz)))

private theorem smt_value_rel_str_concat_left_cancel
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x y)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x z))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y) (SmtType.Seq T)
    hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z) (SmtType.Seq T)
    hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hyEval, hzEval] at hRel
  rw [hyEval, hzEval]
  change RuleProofs.smt_seq_rel sy sz
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sy)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sz))) =
      SmtValue.Boolean true at hRel
  exact smt_seq_rel_concat_left_cancel (__smtx_elem_typeof_seq_value sx) sx sy sz hRel

private theorem smt_value_rel_str_concat_right_cancel
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat y x)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat z x))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y) (SmtType.Seq T)
    hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z) (SmtType.Seq T)
    hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hszTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
    simpa [hzEval, __smtx_typeof_value] using hzValTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hszElem : __smtx_elem_typeof_seq_value sz = T :=
    elem_typeof_seq_value_of_typeof_seq_value hszTy
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hyEval, hzEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sx)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sz)
      (native_unpack_seq sz ++ native_unpack_seq sx))) =
      SmtValue.Boolean true at hRel
  rw [hsyElem, hszElem] at hRel
  rw [hyEval, hzEval]
  change RuleProofs.smt_seq_rel sy sz
  exact smt_seq_rel_concat_right_cancel T sx sy sz hRel

private theorem eo_interprets_str_concat_left_cancel
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) :
    eo_interprets M (mkEq (mkConcat x y) (mkConcat x z)) true ->
    eo_interprets M (mkEq y z) true := by
  intro h
  have hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat x y) (mkConcat x z)) :=
    RuleProofs.eo_has_bool_type_of_interprets_true M _ h
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat x y) (mkConcat x z) hBool with ⟨hSame, hLeftNN⟩
  rcases str_concat_args_of_non_none x y hLeftNN with ⟨T, hxTy, hyTy⟩
  have hRightNN : __smtx_typeof (__eo_to_smt (mkConcat x z)) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases str_concat_args_of_non_none x z hRightNN with ⟨U, hxTyU, hzTyU⟩
  have hUT : U = T := by
    have hSeq : SmtType.Seq T = SmtType.Seq U := by
      rw [← hxTy, ← hxTyU]
    injection hSeq with hTU
    exact hTU.symm
  have hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    simpa [hUT] using hzTyU
  have hRel := RuleProofs.eo_interprets_eq_rel M (mkConcat x y) (mkConcat x z) h
  have hTailRel := smt_value_rel_str_concat_left_cancel M hM x y z T hxTy hyTy hzTy hRel
  have hYZBool : RuleProofs.eo_has_bool_type (mkEq y z) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hyTy, hzTy]
    · rw [hyTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M y z hYZBool hTailRel

private theorem eo_interprets_str_concat_right_cancel
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) :
    eo_interprets M (mkEq (mkConcat y x) (mkConcat z x)) true ->
    eo_interprets M (mkEq y z) true := by
  intro h
  have hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat y x) (mkConcat z x)) :=
    RuleProofs.eo_has_bool_type_of_interprets_true M _ h
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat y x) (mkConcat z x) hBool with ⟨hSame, hLeftNN⟩
  rcases str_concat_args_of_non_none y x hLeftNN with ⟨T, hyTy, hxTy⟩
  have hRightNN : __smtx_typeof (__eo_to_smt (mkConcat z x)) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases str_concat_args_of_non_none z x hRightNN with ⟨U, hzTyU, hxTyU⟩
  have hUT : U = T := by
    have hSeq : SmtType.Seq T = SmtType.Seq U := by
      rw [← hxTy, ← hxTyU]
    injection hSeq with hTU
    exact hTU.symm
  have hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    simpa [hUT] using hzTyU
  have hRel := RuleProofs.eo_interprets_eq_rel M (mkConcat y x) (mkConcat z x) h
  have hTailRel := smt_value_rel_str_concat_right_cancel M hM x y z T hxTy hyTy hzTy hRel
  have hYZBool : RuleProofs.eo_has_bool_type (mkEq y z) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hyTy, hzTy]
    · rw [hyTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M y z hYZBool hTailRel

theorem cmd_step_concat_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_eq args premises) :=
by
  sorry
