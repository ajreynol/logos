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

private abbrev mkPair (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) x) y

private abbrev concatEqNormalize (rev x : Term) : Term :=
  __eo_ite rev (__eo_list_rev (Term.UOp UserOp.str_concat) x) x

private abbrev concatEqStrip (rev s t : Term) : Term :=
  __str_strip_prefix (concatEqNormalize rev (__str_nary_intro s))
    (concatEqNormalize rev (__str_nary_intro t))

private abbrev concatEqLhs (rev s t : Term) : Term :=
  __str_nary_elim (concatEqNormalize rev (__pair_first (concatEqStrip rev s t)))

private abbrev concatEqRhs (rev s t : Term) : Term :=
  __str_nary_elim (concatEqNormalize rev (__pair_second (concatEqStrip rev s t)))

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

private theorem smt_typeof_str_concat_of_seq (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Seq T
  rw [typeof_str_concat_eq (__eo_to_smt x) (__eo_to_smt y)]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, hxTy, hyTy]

private theorem eq_bool_right_seq_of_left_seq (x y : Term) (T : SmtType)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x y))
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hBool with
    ⟨hSame, _⟩
  rw [← hSame, hxTy]

private theorem eq_bool_left_seq_of_right_seq (x y : Term) (T : SmtType)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x y))
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hBool with
    ⟨hSame, _⟩
  rw [hSame, hyTy]

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

private theorem smt_typeof_seq_empty_of_type (A : Term) (T : SmtType) :
    __eo_to_smt_type A = SmtType.Seq T ->
    __smtx_typeof (__eo_to_smt (__seq_empty A)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (__seq_empty A)) = SmtType.Seq T := by
  intro hA hEmptyNN
  by_cases hSpecial : A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst hSpecial
    simp [__eo_to_smt_type, __smtx_typeof_guard] at hA
    cases hA
    change __smtx_typeof (SmtTerm.String "") = SmtType.Seq SmtType.Char
    rw [__smtx_typeof.eq_4]
  · by_cases hStuck : A = Term.Stuck
    · subst hStuck
      simp [__eo_to_smt_type] at hA
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault] at hEmptyNN
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) ≠
        SmtType.None at hEmptyNN
      rw [hA] at hEmptyNN
      change __smtx_typeof (SmtTerm.seq_empty T) ≠ SmtType.None at hEmptyNN
      rw [hDefault]
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
        SmtType.Seq T
      rw [hA]
      exact TranslationProofs.smtx_typeof_seq_empty_of_non_none T hEmptyNN

private theorem smt_typeof_seq_empty_typeof (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  exact smt_typeof_seq_empty_of_type (__eo_typeof x) T hA hEmptyNN

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

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

private theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h hStuck
  subst x
  simp [__eo_requires, native_teq, SmtEval.native_ite, SmtEval.native_not] at h

private theorem eo_requires_result_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro h
  rw [← eo_requires_eq_result_of_ne_stuck x y z h]
  exact h

private theorem eo_is_ok_ne_stuck_of_true (x : Term) :
    __eo_is_ok x = Term.Boolean true ->
    x ≠ Term.Stuck := by
  intro h hx
  subst x
  simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at h

private theorem eo_is_ok_true_of_ne_stuck (x : Term) :
    x ≠ Term.Stuck ->
    __eo_is_ok x = Term.Boolean true := by
  intro hNe
  cases x <;> simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at hNe ⊢

private theorem eo_get_nil_rec_ne_stuck_of_is_list_true (f x : Term) :
    __eo_is_list f x = Term.Boolean true ->
    __eo_get_nil_rec f x ≠ Term.Stuck := by
  intro h
  have hOk : __eo_is_ok (__eo_get_nil_rec f x) = Term.Boolean true := by
    cases f <;> cases x <;>
      simp [__eo_is_list] at h ⊢ <;> exact h
  exact eo_is_ok_ne_stuck_of_true (__eo_get_nil_rec f x) hOk

private theorem eo_is_list_true_of_get_nil_rec_ne_stuck (f x : Term) :
    __eo_get_nil_rec f x ≠ Term.Stuck ->
    __eo_is_list f x = Term.Boolean true := by
  intro hRec
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst f
    simp [__eo_get_nil_rec] at hRec
  have hX : x ≠ Term.Stuck := by
    intro hX
    subst x
    simp [__eo_get_nil_rec] at hRec
  simp [__eo_is_list, eo_is_ok_true_of_ne_stuck (__eo_get_nil_rec f x) hRec]

private theorem eo_is_list_cons_head_eq_of_true (f g x y : Term) :
    __eo_is_list f (Term.Apply (Term.Apply g x) y) = Term.Boolean true ->
    g = f := by
  intro h
  have hRec :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f
      (Term.Apply (Term.Apply g x) y) h
  have hReq :
      __eo_requires f g (__eo_get_nil_rec f y) ≠ Term.Stuck := by
    cases f <;> simp [__eo_get_nil_rec] at hRec ⊢ <;> exact hRec
  exact (eo_requires_eq_of_ne_stuck f g (__eo_get_nil_rec f y) hReq).symm

private theorem eo_is_list_tail_true_of_cons_self (f x y : Term) :
    __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true ->
    __eo_is_list f y = Term.Boolean true := by
  intro h
  have hRec :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f
      (Term.Apply (Term.Apply f x) y) h
  have hReq :
      __eo_requires f f (__eo_get_nil_rec f y) ≠ Term.Stuck := by
    cases f <;> simp [__eo_get_nil_rec] at hRec ⊢ <;> exact hRec
  have hTail : __eo_get_nil_rec f y ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck f f (__eo_get_nil_rec f y) hReq
  exact eo_is_list_true_of_get_nil_rec_ne_stuck f y hTail

private theorem eo_get_nil_rec_cons_self_eq_of_tail_list (f x y : Term)
    (hF : f ≠ Term.Stuck)
    (hTail : __eo_is_list f y = Term.Boolean true) :
    __eo_get_nil_rec f (Term.Apply (Term.Apply f x) y) =
      __eo_get_nil_rec f y := by
  cases f <;> simp [__eo_get_nil_rec] at hF ⊢
  all_goals
    simp [__eo_requires, native_teq, native_ite, SmtEval.native_ite,
      SmtEval.native_not]

private theorem eo_is_list_cons_self_true_of_tail_list (f x y : Term)
    (hF : f ≠ Term.Stuck)
    (hTail : __eo_is_list f y = Term.Boolean true) :
    __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true := by
  have hRec : __eo_get_nil_rec f y ≠ Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f y hTail
  have hGet :
      __eo_get_nil_rec f (Term.Apply (Term.Apply f x) y) ≠ Term.Stuck := by
    rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTail]
    exact hRec
  exact eo_is_list_true_of_get_nil_rec_ne_stuck f
    (Term.Apply (Term.Apply f x) y) hGet

private theorem eo_list_rev_is_list_true_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
        (__eo_list_rev_rec a (__eo_get_nil_rec f a)) ≠ Term.Stuck := by
    simpa [__eo_list_rev] using h
  exact eo_requires_eq_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
    (__eo_list_rev_rec a (__eo_get_nil_rec f a)) hReq

private theorem eo_list_rev_rec_ne_stuck_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    __eo_list_rev_rec a (__eo_get_nil_rec f a) ≠ Term.Stuck := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
        (__eo_list_rev_rec a (__eo_get_nil_rec f a)) ≠ Term.Stuck := by
    simpa [__eo_list_rev] using h
  exact eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
    (__eo_list_rev_rec a (__eo_get_nil_rec f a)) hReq

private theorem eo_list_rev_eq_rec_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    __eo_list_rev f a = __eo_list_rev_rec a (__eo_get_nil_rec f a) := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
        (__eo_list_rev_rec a (__eo_get_nil_rec f a)) ≠ Term.Stuck := by
    simpa [__eo_list_rev] using h
  simpa [__eo_list_rev] using
    eo_requires_eq_result_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_rev_rec a (__eo_get_nil_rec f a)) hReq

private theorem eo_list_rev_arg_ne_stuck_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    a ≠ Term.Stuck := by
  intro h ha
  subst a
  cases f <;>
    simp [__eo_list_rev, __eo_is_list, __eo_requires, native_ite, native_teq] at h

private theorem eo_list_rev_rec_cons (f x y acc : Term)
    (hAcc : acc ≠ Term.Stuck) :
    __eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc =
      __eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc) := by
  cases acc <;> simp [__eo_list_rev_rec] at hAcc ⊢

private theorem eo_list_rev_cons_eq_of_tail_list (f x y : Term)
    (hF : f ≠ Term.Stuck)
    (hTail : __eo_is_list f y = Term.Boolean true) :
    __eo_list_rev f (Term.Apply (Term.Apply f x) y) =
      __eo_list_rev_rec y (Term.Apply (Term.Apply f x)
        (__eo_get_nil_rec f y)) := by
  have hRec : __eo_get_nil_rec f y ≠ Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f y hTail
  have hConsList :
      __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list f x y hF hTail
  rw [__eo_list_rev]
  rw [hConsList]
  rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
    (__eo_list_rev_rec (Term.Apply (Term.Apply f x) y)
      (__eo_get_nil_rec f (Term.Apply (Term.Apply f x) y))) (by decide)]
  rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTail]
  exact eo_list_rev_rec_cons f x y (__eo_get_nil_rec f y) hRec

private theorem eo_list_rev_cons_tail_list_of_ne_stuck (f x y : Term)
    (hRev : __eo_list_rev f (Term.Apply (Term.Apply f x) y) ≠
      Term.Stuck) :
    __eo_is_list f y = Term.Boolean true := by
  have hList :
      __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck f (Term.Apply (Term.Apply f x) y)
      hRev
  exact eo_is_list_tail_true_of_cons_self f x y hList

private theorem eo_list_rev_cons_eq_of_ne_stuck (f x y : Term)
    (hRev : __eo_list_rev f (Term.Apply (Term.Apply f x) y) ≠
      Term.Stuck) :
    __eo_list_rev f (Term.Apply (Term.Apply f x) y) =
      __eo_list_rev_rec y (Term.Apply (Term.Apply f x)
        (__eo_get_nil_rec f y)) := by
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst f
    simp [__eo_list_rev, __eo_is_list, __eo_requires, native_teq,
      native_ite, SmtEval.native_ite] at hRev
  have hTail := eo_list_rev_cons_tail_list_of_ne_stuck f x y hRev
  exact eo_list_rev_cons_eq_of_tail_list f x y hF hTail

private theorem eo_list_rev_str_concat_cons_eq_of_ne_stuck (x y : Term)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat x y) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat x y) =
      __eo_list_rev_rec y
        (mkConcat x (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y)) := by
  exact eo_list_rev_cons_eq_of_ne_stuck (Term.UOp UserOp.str_concat) x y hRev

private theorem eo_list_rev_rec_cons_ne_stuck_of_ne_stuck (f x y acc : Term) :
    __eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc ≠ Term.Stuck ->
    __eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc) ≠ Term.Stuck := by
  intro h
  have hAcc : acc ≠ Term.Stuck := by
    intro hAcc
    subst acc
    simp [__eo_list_rev_rec] at h
  simpa [eo_list_rev_rec_cons f x y acc hAcc] using h

private theorem eo_list_rev_rec_acc_ne_stuck_of_ne_stuck (a acc : Term) :
    __eo_list_rev_rec a acc ≠ Term.Stuck ->
    acc ≠ Term.Stuck := by
  intro h hAcc
  subst acc
  cases a <;> simp [__eo_list_rev_rec] at h

private theorem smt_typeof_get_nil_rec_str_concat_of_seq_aux (f a : Term) :
    f = Term.UOp UserOp.str_concat ->
    ∀ T : SmtType,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __eo_get_nil_rec f a ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__eo_get_nil_rec f a)) = SmtType.Seq T := by
  intro hf
  induction f, a using __eo_get_nil_rec.induct with
  | case1 a =>
      intro T hList haTy hGet
      cases hf
  | case2 f hF =>
      intro T hList haTy hGet
      simp [__eo_get_nil_rec] at hGet
  | case3 f g x y hF ih =>
      intro T hList haTy hGet
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      have hReq :
          __eo_requires f f (__eo_get_nil_rec f y) ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hTailGet : __eo_get_nil_rec f y ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck f f (__eo_get_nil_rec f y) hReq
      subst f
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [haTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with ⟨U, hxTy, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTy hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, haTy]
        injection hSeq
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hIH := ih rfl T hTailList hyTy hTailGet
      simpa [__eo_get_nil_rec,
        eo_requires_eq_result_of_ne_stuck (Term.UOp UserOp.str_concat)
          (Term.UOp UserOp.str_concat)
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y) hReq] using hIH
  | case4 f nil hF hNil hNot =>
      intro T hList haTy hGet
      have hReq :
          __eo_requires (__eo_is_list_nil f nil) (Term.Boolean true) nil ≠
            Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      simpa [__eo_get_nil_rec,
        eo_requires_eq_result_of_ne_stuck
          (__eo_is_list_nil f nil) (Term.Boolean true) nil hReq] using haTy

private theorem smt_typeof_get_nil_rec_str_concat_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hGet :
      __eo_get_nil_rec (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a)) =
      SmtType.Seq T :=
  smt_typeof_get_nil_rec_str_concat_of_seq_aux
    (Term.UOp UserOp.str_concat) a rfl T hList haTy hGet

private theorem smt_typeof_list_rev_eq_rec_of_ne_stuck (f a : Term)
    (hRev : __eo_list_rev f a ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_list_rev f a)) =
      __smtx_typeof
        (__eo_to_smt (__eo_list_rev_rec a (__eo_get_nil_rec f a))) := by
  rw [eo_list_rev_eq_rec_of_ne_stuck f a hRev]

private theorem smt_typeof_list_rev_rec_cons_eq
    (f x y acc : Term) (hAcc : acc ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc)) =
      __smtx_typeof
        (__eo_to_smt (__eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc))) := by
  rw [eo_list_rev_rec_cons f x y acc hAcc]

private theorem smt_typeof_list_rev_rec_str_concat_of_seq_aux
    (f a acc : Term) :
    f = Term.UOp UserOp.str_concat ->
    ∀ T : SmtType,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T ->
      __eo_list_rev_rec a acc ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__eo_list_rev_rec a acc)) =
        SmtType.Seq T := by
  intro hf
  induction a, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      intro T hList haTy hAccTy hRev
      simp [__eo_list_rev_rec] at hRev
  | case2 a hA =>
      intro T hList haTy hAccTy hRev
      simp [__eo_list_rev_rec] at hRev
  | case3 g x y acc hAcc ih =>
      intro T hList haTy hAccTy hRev
      subst f
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hList
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [haTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with
        ⟨U, hxTy, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTy hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, haTy]
        injection hSeq
      have hxTyT : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        simpa [hUT] using hxTy
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hNewAccTy :
          __smtx_typeof (__eo_to_smt (mkConcat x acc)) = SmtType.Seq T :=
        smt_typeof_str_concat_of_seq x acc T hxTyT hAccTy
      have hTailRev :
          __eo_list_rev_rec y (mkConcat x acc) ≠ Term.Stuck := by
        simpa [__eo_list_rev_rec] using hRev
      have hIH := ih T hTailList hyTy hNewAccTy hTailRev
      simpa [__eo_list_rev_rec] using hIH
  | case4 nil acc hNil hAcc hNot =>
      intro T hList haTy hAccTy hRev
      simpa [__eo_list_rev_rec] using hAccTy

private theorem smt_typeof_list_rev_rec_str_concat_of_seq
    (a acc : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T)
    (hRev : __eo_list_rev_rec a acc ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_list_rev_rec a acc)) = SmtType.Seq T :=
  smt_typeof_list_rev_rec_str_concat_of_seq_aux
    (Term.UOp UserOp.str_concat) a acc rfl T hList haTy hAccTy hRev

private theorem smt_typeof_list_rev_str_concat_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.str_concat) a)) =
      SmtType.Seq T := by
  have hGet : __eo_get_nil_rec (Term.UOp UserOp.str_concat) a ≠
      Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat) a
      hList
  have hGetTy :
      __smtx_typeof
          (__eo_to_smt (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a)) =
        SmtType.Seq T :=
    smt_typeof_get_nil_rec_str_concat_of_seq a T hList haTy hGet
  have hRec :
      __eo_list_rev_rec a (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a) ≠
        Term.Stuck :=
    eo_list_rev_rec_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat) a hRev
  rw [smt_typeof_list_rev_eq_rec_of_ne_stuck
    (Term.UOp UserOp.str_concat) a hRev]
  exact smt_typeof_list_rev_rec_str_concat_of_seq a
    (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a) T hList haTy hGetTy hRec

private theorem eo_mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem eo_mk_apply_fun_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    f ≠ Term.Stuck := by
  intro hf
  subst f
  simp [__eo_mk_apply] at h

private theorem eo_mk_apply_arg_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

private theorem eo_ite_then_ne_stuck_of_ne_stuck (c x y : Term)
    (h : __eo_ite c x y ≠ Term.Stuck)
    (hc : c = Term.Boolean true) :
    x ≠ Term.Stuck := by
  subst c
  simpa [eo_ite_true] using h

private theorem eo_ite_else_ne_stuck_of_ne_stuck (c x y : Term)
    (h : __eo_ite c x y ≠ Term.Stuck)
    (hc : c = Term.Boolean false) :
    y ≠ Term.Stuck := by
  subst c
  simpa [eo_ite_false] using h

private theorem str_nary_intro_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_nary_intro x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_nary_intro] at h

private theorem str_nary_elim_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_nary_elim x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_nary_elim] at h

private theorem pair_first_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __pair_first x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__pair_first] at h

private theorem pair_second_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __pair_second x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__pair_second] at h

private theorem str_strip_prefix_left_ne_stuck_of_ne_stuck (x y : Term)
    (h : __str_strip_prefix x y ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_strip_prefix] at h

private theorem str_strip_prefix_right_ne_stuck_of_ne_stuck (x y : Term)
    (h : __str_strip_prefix x y ≠ Term.Stuck) :
    y ≠ Term.Stuck := by
  intro hy
  subst y
  cases x <;> simp [__str_strip_prefix] at h

private theorem eo_prog_concat_eq_eq_of_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) =
      mkEq (concatEqLhs rev s t) (concatEqRhs rev s t) := by
  have hRev : rev ≠ Term.Stuck := by
    intro h
    subst rev
    simp [__eo_prog_concat_eq] at hProg
  have hProg' :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
          (concatEqRhs rev s t) ≠ Term.Stuck := by
    cases rev <;>
      simp [__eo_prog_concat_eq, concatEqLhs, concatEqRhs, concatEqStrip,
        concatEqNormalize] at hRev hProg ⊢
    all_goals first | exact hProg | contradiction
  have hInner :
      __eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) ≠
        Term.Stuck := by
    exact eo_mk_apply_fun_ne_stuck_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
        (concatEqRhs rev s t) hProg'
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) =
        Term.Apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq)
      (concatEqLhs rev s t) hInner
  have hOuterEq :
      __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) =
        Term.Apply (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
          (concatEqRhs rev s t) := by
    cases rev <;>
      simp [__eo_prog_concat_eq, concatEqLhs, concatEqRhs, concatEqStrip,
        concatEqNormalize] at hRev hProg' ⊢
    all_goals first
      | exact eo_mk_apply_eq_apply_of_ne_stuck _ _ hProg'
      | contradiction
  rw [hOuterEq, hInnerEq]

private theorem eo_prog_concat_eq_mk_apply_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
      (concatEqRhs rev s t) ≠ Term.Stuck := by
  have hRev : rev ≠ Term.Stuck := by
    intro h
    subst rev
    simp [__eo_prog_concat_eq] at hProg
  cases rev <;>
    simp [__eo_prog_concat_eq, concatEqLhs, concatEqRhs, concatEqStrip,
      concatEqNormalize] at hRev hProg ⊢
  all_goals first | exact hProg | contradiction

private theorem concatEqLhs_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqLhs rev s t ≠ Term.Stuck := by
  have hApply := eo_prog_concat_eq_mk_apply_ne_stuck rev s t hProg
  have hInner :
      __eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck
      (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
      (concatEqRhs rev s t) hApply
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq)
    (concatEqLhs rev s t) hInner

private theorem concatEqRhs_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqRhs rev s t ≠ Term.Stuck := by
  have hApply := eo_prog_concat_eq_mk_apply_ne_stuck rev s t hProg
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
    (concatEqRhs rev s t) hApply

private theorem concatEq_rev_cases_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  have hLhs := concatEqLhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  have hNorm :
      concatEqNormalize rev (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
    str_nary_elim_arg_ne_stuck_of_ne_stuck
      (concatEqNormalize rev (__pair_first (concatEqStrip rev s t))) hLhs
  exact eo_ite_cases_of_ne_stuck rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first (concatEqStrip rev s t)))
    (__pair_first (concatEqStrip rev s t)) hNorm

private theorem concatEqStrip_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqStrip rev s t ≠ Term.Stuck := by
  have hLhs := concatEqLhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  have hNorm :
      concatEqNormalize rev (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
    str_nary_elim_arg_ne_stuck_of_ne_stuck
      (concatEqNormalize rev (__pair_first (concatEqStrip rev s t))) hLhs
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevFirst :
        __eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first (concatEqStrip rev s t)))
        (__pair_first (concatEqStrip rev s t)) hNorm hRev
    have hFirst : __pair_first (concatEqStrip rev s t) ≠ Term.Stuck :=
      eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip rev s t)) hRevFirst
    exact pair_first_arg_ne_stuck_of_ne_stuck (concatEqStrip rev s t) hFirst
  · have hFirst : __pair_first (concatEqStrip rev s t) ≠ Term.Stuck :=
      eo_ite_else_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first (concatEqStrip rev s t)))
        (__pair_first (concatEqStrip rev s t)) hNorm hRev
    exact pair_first_arg_ne_stuck_of_ne_stuck (concatEqStrip rev s t) hFirst

private theorem concatEqNormalize_first_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__pair_first (concatEqStrip rev s t)) ≠
      Term.Stuck := by
  have hLhs := concatEqLhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_nary_elim_arg_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__pair_first (concatEqStrip rev s t))) hLhs

private theorem concatEqNormalize_second_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__pair_second (concatEqStrip rev s t)) ≠
      Term.Stuck := by
  have hRhs := concatEqRhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_nary_elim_arg_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__pair_second (concatEqStrip rev s t))) hRhs

private theorem concatEqStrip_first_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __pair_first (concatEqStrip rev s t) ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_first_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevFirst :
        __eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first (concatEqStrip rev s t)))
        (__pair_first (concatEqStrip rev s t)) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_first (concatEqStrip rev s t)) hRevFirst
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip rev s t)))
      (__pair_first (concatEqStrip rev s t)) hNorm hRev

private theorem concatEqStrip_second_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __pair_second (concatEqStrip rev s t) ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_second_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevSecond :
        __eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_second (concatEqStrip rev s t)) ≠ Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_second (concatEqStrip rev s t)))
        (__pair_second (concatEqStrip rev s t)) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_second (concatEqStrip rev s t)) hRevSecond
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_second (concatEqStrip rev s t)))
      (__pair_second (concatEqStrip rev s t)) hNorm hRev

private theorem concatEqNormalize_left_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__str_nary_intro s) ≠ Term.Stuck := by
  have hStrip := concatEqStrip_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_strip_prefix_left_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__str_nary_intro s))
    (concatEqNormalize rev (__str_nary_intro t)) hStrip

private theorem concatEqNormalize_right_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__str_nary_intro t) ≠ Term.Stuck := by
  have hStrip := concatEqStrip_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_strip_prefix_right_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__str_nary_intro s))
    (concatEqNormalize rev (__str_nary_intro t)) hStrip

private theorem str_nary_intro_left_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __str_nary_intro s ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_left_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevIntro :
        __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
          Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__str_nary_intro s) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntro
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      (__str_nary_intro s) hNorm hRev

private theorem str_nary_intro_right_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __str_nary_intro t ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_right_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevIntro :
        __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
          Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
        (__str_nary_intro t) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevIntro
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      (__str_nary_intro t) hNorm hRev

private theorem eo_prog_concat_eq_premise_eq_shape_of_ne_stuck (rev x1 : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf x1) ≠ Term.Stuck) :
    ∃ s t, x1 = mkEq s t := by
  cases x1 with
  | Apply f t =>
      cases f with
      | Apply g s =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  exact ⟨s, t, rfl⟩
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_eq] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_eq] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_eq] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_eq] at hProg

private theorem pair_first_pair (x y : Term) :
    __pair_first (mkPair x y) = x := by
  rfl

private theorem pair_second_pair (x y : Term) :
    __pair_second (mkPair x y) = y := by
  rfl

private theorem concatEqNormalize_false (x : Term) :
    concatEqNormalize (Term.Boolean false) x = x := by
  rfl

private theorem concatEqNormalize_true (x : Term) :
    concatEqNormalize (Term.Boolean true) x =
      __eo_list_rev (Term.UOp UserOp.str_concat) x := by
  rfl

private theorem concatEqStrip_false (s t : Term) :
    concatEqStrip (Term.Boolean false) s t =
      __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) := by
  rfl

private theorem concatEqStrip_true (s t : Term) :
    concatEqStrip (Term.Boolean true) s t =
      __str_strip_prefix
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)) := by
  rfl

private theorem concatEqLhs_false (s t : Term) :
    concatEqLhs (Term.Boolean false) s t =
      __str_nary_elim
        (__pair_first (__str_strip_prefix (__str_nary_intro s) (__str_nary_intro t))) := by
  rfl

private theorem concatEqRhs_false (s t : Term) :
    concatEqRhs (Term.Boolean false) s t =
      __str_nary_elim
        (__pair_second (__str_strip_prefix (__str_nary_intro s) (__str_nary_intro t))) := by
  rfl

private theorem concatEqLhs_true (s t : Term) :
    concatEqLhs (Term.Boolean true) s t =
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first
            (__str_strip_prefix
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))))) := by
  rfl

private theorem concatEqRhs_true (s t : Term) :
    concatEqRhs (Term.Boolean true) s t =
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_second
            (__str_strip_prefix
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))))) := by
  rfl

private theorem concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_left_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_right_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_rev_first_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip (Term.Boolean true) s t)) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_first_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_rev_second_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_second (concatEqStrip (Term.Boolean true) s t)) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_second_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_intro_left_is_list_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
      Term.Boolean true := by
  exact eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
    (__str_nary_intro s)
    (concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg)

private theorem concatEq_true_intro_right_is_list_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
      Term.Boolean true := by
  exact eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
    (__str_nary_intro t)
    (concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg)

private theorem concatEq_true_strip_first_is_list_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip (Term.Boolean true) s t)) =
      Term.Boolean true := by
  exact eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
    (__pair_first (concatEqStrip (Term.Boolean true) s t))
    (concatEq_true_rev_first_ne_stuck_of_prog_ne_stuck s t hProg)

private theorem concatEq_true_strip_second_is_list_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__pair_second (concatEqStrip (Term.Boolean true) s t)) =
      Term.Boolean true := by
  exact eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
    (__pair_second (concatEqStrip (Term.Boolean true) s t))
    (concatEq_true_rev_second_ne_stuck_of_prog_ne_stuck s t hProg)

private theorem eo_interprets_strip_prefix_pair_of_eq
    (M : SmtModel) (x y : Term)
    (hXY : eo_interprets M (mkEq x y) true)
    (hStrip : __str_strip_prefix x y = mkPair x y) :
    eo_interprets M
      (mkEq (__pair_first (__str_strip_prefix x y))
        (__pair_second (__str_strip_prefix x y))) true := by
  rw [hStrip]
  simpa [mkPair, pair_first_pair, pair_second_pair] using hXY

private theorem eo_interprets_eq_symm_local
    (M : SmtModel) (x y : Term)
    (hXY : eo_interprets M (mkEq x y) true) :
    eo_interprets M (mkEq y x) true := by
  have hBool : RuleProofs.eo_has_bool_type (mkEq y x) :=
    RuleProofs.eo_has_bool_type_eq_symm x y
      (RuleProofs.eo_has_bool_type_of_interprets_true M (mkEq x y) hXY)
  exact RuleProofs.eo_interprets_eq_of_rel M y x hBool
    (RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))
      (RuleProofs.eo_interprets_eq_rel M x y hXY))

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
      mkPair (mkConcat t t2) (mkConcat u s2) := by
  change __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
    (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      mkPair (mkConcat t t2) (mkConcat u s2)
  rw [h, eo_ite_false]
  simp [__eo_l_1___str_strip_prefix, mkPair]

private theorem pair_first_str_strip_prefix_concat_of_eo_eq_true
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean true) :
    __pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      __pair_first (__str_strip_prefix t2 s2) := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 h]

private theorem pair_second_str_strip_prefix_concat_of_eo_eq_true
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean true) :
    __pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      __pair_second (__str_strip_prefix t2 s2) := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 h]

private theorem pair_first_str_strip_prefix_concat_of_eo_eq_false
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean false) :
    __pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      mkConcat t t2 := by
  rw [str_strip_prefix_concat_of_eo_eq_false t u t2 s2 h]
  rfl

private theorem pair_second_str_strip_prefix_concat_of_eo_eq_false
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean false) :
    __pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      mkConcat u s2 := by
  rw [str_strip_prefix_concat_of_eo_eq_false t u t2 s2 h]
  rfl

private theorem eo_interprets_str_strip_prefix_concat_false
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean false)
    (hXY : eo_interprets M (mkEq (mkConcat t t2) (mkConcat u s2)) true) :
    eo_interprets M
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))) true := by
  exact eo_interprets_strip_prefix_pair_of_eq M (mkConcat t t2) (mkConcat u s2)
    hXY (str_strip_prefix_concat_of_eo_eq_false t u t2 s2 hCond)

private theorem eo_interprets_str_strip_prefix_concat_true_of_tail
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean true)
    (hTail : eo_interprets M
      (mkEq (__pair_first (__str_strip_prefix t2 s2))
        (__pair_second (__str_strip_prefix t2 s2))) true) :
    eo_interprets M
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))) true := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond]
  exact hTail

private theorem eo_interprets_rev_strip_prefix_concat_true_of_tail
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean true)
    (hTail :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2)))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))) true := by
  rw [pair_first_str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond]
  rw [pair_second_str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond]
  exact hTail

private theorem eo_interprets_rev_strip_prefix_concat_false_of_eq
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean false)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))) true := by
  rw [pair_first_str_strip_prefix_concat_of_eo_eq_false t u t2 s2 hCond]
  rw [pair_second_str_strip_prefix_concat_of_eo_eq_false t u t2 s2 hCond]
  exact hXY

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

private theorem native_unpack_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq, native_unpack_pack_seq T xs]

private theorem elem_typeof_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue,
      __smtx_elem_typeof_seq_value (native_pack_seq T xs) = T
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, __smtx_elem_typeof_seq_value,
        elem_typeof_pack_seq T xs]

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

private theorem smt_value_rel_str_concat_assoc
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat (mkConcat x y) z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (mkConcat y z)))) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z)
    (SmtType.Seq T) hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq M (mkConcat x y) z]
  rw [smtx_model_eval_str_concat_term_eq M x y]
  rw [smtx_model_eval_str_concat_term_eq M x (mkConcat y z)]
  rw [smtx_model_eval_str_concat_term_eq M y z]
  rw [hxEval, hyEval, hzEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat,
    native_unpack_pack_seq, elem_typeof_pack_seq, hsxElem, hsyElem,
    List.append_assoc, RuleProofs.smtx_model_eval_eq_refl]

private theorem eo_interprets_str_concat_assoc
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    eo_interprets M
      (mkEq (mkConcat (mkConcat x y) z) (mkConcat x (mkConcat y z)))
      true := by
  have hXYTy : __smtx_typeof (__eo_to_smt (mkConcat x y)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x y T hxTy hyTy
  have hYZTy : __smtx_typeof (__eo_to_smt (mkConcat y z)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y z T hyTy hzTy
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat (mkConcat x y) z)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (mkConcat x y) z T hXYTy hzTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat x (mkConcat y z))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x (mkConcat y z) T hxTy hYZTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat (mkConcat x y) z) (mkConcat x (mkConcat y z))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat (mkConcat x y) z) (mkConcat x (mkConcat y z)) hBool
    (smt_value_rel_str_concat_assoc M hM x y z T hxTy hyTy hzTy)

private theorem eo_interprets_str_concat_assoc_symm
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    eo_interprets M
      (mkEq (mkConcat x (mkConcat y z)) (mkConcat (mkConcat x y) z))
      true := by
  have hXYTy : __smtx_typeof (__eo_to_smt (mkConcat x y)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x y T hxTy hyTy
  have hYZTy : __smtx_typeof (__eo_to_smt (mkConcat y z)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y z T hyTy hzTy
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat x (mkConcat y z))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x (mkConcat y z) T hxTy hYZTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat (mkConcat x y) z)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (mkConcat x y) z T hXYTy hzTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x (mkConcat y z)) (mkConcat (mkConcat x y) z)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat x (mkConcat y z)) (mkConcat (mkConcat x y) z) hBool
    (RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt (mkConcat (mkConcat x y) z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (mkConcat y z))))
      (smt_value_rel_str_concat_assoc M hM x y z T hxTy hyTy hzTy))

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

private theorem smt_value_rel_str_nary_intro_default
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x))))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x))
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    rw [hCond, eo_ite_false, hApplyEq]
    exact smt_value_rel_str_concat_right_empty M hM x T hxTy

private theorem smt_value_rel_str_nary_intro
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  cases x with
  | Stuck =>
      simp [__str_nary_intro] at hIntro
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simp [__str_nary_intro]
                exact RuleProofs.smt_value_rel_refl
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_concat) t) a)))
              · change RuleProofs.smt_value_rel
                  (__smtx_model_eval M (__eo_to_smt (__str_nary_intro
                    (Term.Apply (Term.Apply (Term.UOp op) t) a))))
                  (__smtx_model_eval M (__eo_to_smt
                    (Term.Apply (Term.Apply (Term.UOp op) t) a)))
                simp [__str_nary_intro, hop] at hIntro ⊢
                exact smt_value_rel_str_nary_intro_default M hM
                  (Term.Apply (Term.Apply (Term.UOp op) t) a) T hxTy hIntro
          | _ =>
              simp [__str_nary_intro] at hIntro ⊢
              exact smt_value_rel_str_nary_intro_default M hM
                _ T hxTy hIntro
      | _ =>
          simp [__str_nary_intro] at hIntro ⊢
          exact smt_value_rel_str_nary_intro_default M hM
            _ T hxTy hIntro
  | _ =>
      simp [__str_nary_intro] at hIntro ⊢
      exact smt_value_rel_str_nary_intro_default M hM _ T hxTy hIntro

private theorem smt_typeof_str_nary_intro_default_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x))))) ≠ SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))))) = SmtType.Seq T := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact hxTy
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    have hApplyNN :
        __smtx_typeof
          (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))) ≠
            SmtType.None := by
      simpa [hCond, eo_ite_false, hApplyEq] using hIntroNN
    rcases str_concat_args_of_non_none x (__seq_empty (__eo_typeof x)) hApplyNN with
      ⟨U, hxTyU, hEmptyTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hxTyU, hxTy]
      injection hSeq
    have hEmptyTy :
        __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
          SmtType.Seq T := by
      simpa [hUT] using hEmptyTyU
    rw [hCond, eo_ite_false, hApplyEq]
    exact smt_typeof_str_concat_of_seq x (__seq_empty (__eo_typeof x)) T
      hxTy hEmptyTy

private theorem smt_typeof_str_nary_intro_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN : __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
      SmtType.None) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T := by
  have hIntro : __str_nary_intro x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation (__str_nary_intro x) hIntroNN
  cases x with
  | Stuck =>
      simp [__str_nary_intro] at hIntro
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simpa [__str_nary_intro] using hxTy
              · change __smtx_typeof
                    (__eo_to_smt (__str_nary_intro
                      (Term.Apply (Term.Apply (Term.UOp op) t) a))) =
                    SmtType.Seq T
                simp [__str_nary_intro, hop] at hIntroNN hIntro ⊢
                exact smt_typeof_str_nary_intro_default_of_seq
                  (Term.Apply (Term.Apply (Term.UOp op) t) a) T hxTy hIntroNN
                  hIntro
          | _ =>
              simp [__str_nary_intro] at hIntroNN hIntro ⊢
              exact smt_typeof_str_nary_intro_default_of_seq _ T hxTy
                hIntroNN hIntro
      | _ =>
          simp [__str_nary_intro] at hIntroNN hIntro ⊢
          exact smt_typeof_str_nary_intro_default_of_seq _ T hxTy hIntroNN hIntro
  | _ =>
      simp [__str_nary_intro] at hIntroNN hIntro ⊢
      exact smt_typeof_str_nary_intro_default_of_seq _ T hxTy hIntroNN hIntro

private theorem smt_typeof_str_nary_intro_default_of_seq_ne_stuck
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x))))) ≠ SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))))) = SmtType.Seq T := by
  exact smt_typeof_str_nary_intro_default_of_seq x T hxTy hIntroNN hIntro

private theorem smt_typeof_str_nary_intro_of_seq_ne_stuck
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN : __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
      SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T := by
  exact smt_typeof_str_nary_intro_of_seq x T hxTy hIntroNN

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

private theorem smt_value_rel_str_nary_elim
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  cases x with
  | Stuck =>
      simp [__str_nary_elim] at hElim
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simp [__str_nary_elim] at hElim ⊢
                exact smt_value_rel_str_nary_elim_concat_ite M hM t a T hxTy hElim
              · simp [__str_nary_elim, hop] at hElim ⊢
                exact smt_value_rel_str_nary_elim_requires M _ hElim
          | _ =>
              simp [__str_nary_elim] at hElim ⊢
              exact smt_value_rel_str_nary_elim_requires M _ hElim
      | _ =>
          simp [__str_nary_elim] at hElim ⊢
          exact smt_value_rel_str_nary_elim_requires M _ hElim
  | _ =>
      simp [__str_nary_elim] at hElim ⊢
      exact smt_value_rel_str_nary_elim_requires M _ hElim

private theorem smt_typeof_str_nary_elim_concat_of_seq (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElimNN :
      __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
          (mkConcat t ss))) ≠ SmtType.None)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss))) = SmtType.Seq T := by
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) ≠ SmtType.None := by
    rw [hConcatTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none t ss hConcatNN with ⟨U, htTyU, hssTyU⟩
  have hConcatTyU :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq t ss U htTyU hssTyU
  have hUT : U = T := by
    have hSeq : SmtType.Seq U = SmtType.Seq T := by
      rw [← hConcatTyU, hConcatTy]
    injection hSeq
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    simpa [hUT] using htTyU
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) hElim with
    hCond | hCond
  · rw [hCond, eo_ite_true]
    exact htTy
  · rw [hCond, eo_ite_false]
    exact hConcatTy

private theorem smt_typeof_str_nary_elim_requires_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __eo_requires x (__seq_empty (__eo_typeof x)) x ≠ Term.Stuck) :
    __smtx_typeof
      (__eo_to_smt (__eo_requires x (__seq_empty (__eo_typeof x)) x)) =
        SmtType.Seq T := by
  rw [eo_requires_eq_result_of_ne_stuck x (__seq_empty (__eo_typeof x)) x hElim]
  exact hxTy

private theorem smt_typeof_str_nary_elim_concat_of_seq_ne_stuck
    (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss))) = SmtType.Seq T := by
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) ≠ SmtType.None := by
    rw [hConcatTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none t ss hConcatNN with ⟨U, htTyU, hssTyU⟩
  have hConcatTyU :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq t ss U htTyU hssTyU
  have hUT : U = T := by
    have hSeq : SmtType.Seq U = SmtType.Seq T := by
      rw [← hConcatTyU, hConcatTy]
    injection hSeq
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    simpa [hUT] using htTyU
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) hElim with
    hCond | hCond
  · rw [hCond, eo_ite_true]
    exact htTy
  · rw [hCond, eo_ite_false]
    exact hConcatTy

private theorem smt_typeof_str_nary_elim_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElimNN : __smtx_typeof (__eo_to_smt (__str_nary_elim x)) ≠
      SmtType.None) :
    __smtx_typeof (__eo_to_smt (__str_nary_elim x)) = SmtType.Seq T := by
  have hElim : __str_nary_elim x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation (__str_nary_elim x) hElimNN
  cases x with
  | Stuck =>
      simp [__str_nary_elim] at hElim
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simp [__str_nary_elim] at hElimNN hElim ⊢
                exact smt_typeof_str_nary_elim_concat_of_seq t a T hxTy
                  hElimNN hElim
              · simp [__str_nary_elim, hop] at hElimNN hElim ⊢
                exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
          | _ =>
              simp [__str_nary_elim] at hElimNN hElim ⊢
              exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
      | _ =>
          simp [__str_nary_elim] at hElimNN hElim ⊢
          exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
  | _ =>
      simp [__str_nary_elim] at hElimNN hElim ⊢
      exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim

private theorem smt_typeof_str_nary_elim_of_seq_ne_stuck
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_elim x)) = SmtType.Seq T := by
  cases x with
  | Stuck =>
      simp [__str_nary_elim] at hElim
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simp [__str_nary_elim] at hElim ⊢
                exact smt_typeof_str_nary_elim_concat_of_seq_ne_stuck
                  t a T hxTy hElim
              · simp [__str_nary_elim, hop] at hElim ⊢
                exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
          | _ =>
              simp [__str_nary_elim] at hElim ⊢
              exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
      | _ =>
          simp [__str_nary_elim] at hElim ⊢
          exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
  | _ =>
      simp [__str_nary_elim] at hElim ⊢
      exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim

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

private theorem eo_interprets_str_nary_intro_eq_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (__str_nary_intro x) x)) :
    eo_interprets M (mkEq (__str_nary_intro x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (__str_nary_intro x) x hBool
    (smt_value_rel_str_nary_intro M hM x T hxTy hIntro)

private theorem eo_interprets_str_nary_elim_eq_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (__str_nary_elim x) x)) :
    eo_interprets M (mkEq (__str_nary_elim x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (__str_nary_elim x) x hBool
    (smt_value_rel_str_nary_elim M hM x T hxTy hElim)

private theorem eo_interprets_str_nary_intro_congr_of_seq
    (M : SmtModel) (hM : model_total_typed M) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hIntroX : __str_nary_intro x ≠ Term.Stuck)
    (hIntroY : __str_nary_intro y ≠ Term.Stuck)
    (hXY : eo_interprets M (mkEq x y) true)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_intro x) (__str_nary_intro y))) :
    eo_interprets M (mkEq (__str_nary_intro x) (__str_nary_intro y)) true := by
  have hXRel := smt_value_rel_str_nary_intro M hM x T hxTy hIntroX
  have hYRel := smt_value_rel_str_nary_intro M hM y T hyTy hIntroY
  have hXYRel := RuleProofs.eo_interprets_eq_rel M x y hXY
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y))) hXRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y))) hXYRel
        (RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y)))
          (__smtx_model_eval M (__eo_to_smt y)) hYRel))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_intro x) (__str_nary_intro y) hBool hRel

private theorem eo_interprets_str_nary_elim_congr_of_seq
    (M : SmtModel) (hM : model_total_typed M) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hElimX : __str_nary_elim x ≠ Term.Stuck)
    (hElimY : __str_nary_elim y ≠ Term.Stuck)
    (hXY : eo_interprets M (mkEq x y) true)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim x) (__str_nary_elim y))) :
    eo_interprets M (mkEq (__str_nary_elim x) (__str_nary_elim y)) true := by
  have hXRel := smt_value_rel_str_nary_elim M hM x T hxTy hElimX
  have hYRel := smt_value_rel_str_nary_elim M hM y T hyTy hElimY
  have hXYRel := RuleProofs.eo_interprets_eq_rel M x y hXY
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim x)))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim x)))
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y))) hXRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y))) hXYRel
        (RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y)))
          (__smtx_model_eval M (__eo_to_smt y)) hYRel))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim x) (__str_nary_elim y) hBool hRel

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

private theorem eo_interprets_str_concat_tails_of_head_eo_eq_true
    (M : SmtModel) (hM : model_total_typed M) (t u t2 s2 : Term)
    (hHead : __eo_eq t u = Term.Boolean true) :
    eo_interprets M (mkEq (mkConcat t t2) (mkConcat u s2)) true ->
    eo_interprets M (mkEq t2 s2) true := by
  intro h
  have hUT : u = t := eq_of_eo_eq_true_local t u hHead
  subst u
  exact eo_interprets_str_concat_left_cancel M hM t t2 s2 h

private theorem eo_interprets_str_strip_prefix_concat_step
    (M : SmtModel) (hM : model_total_typed M) (t u t2 s2 : Term)
    (hXY : eo_interprets M (mkEq (mkConcat t t2) (mkConcat u s2)) true)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hTail :
      eo_interprets M (mkEq t2 s2) true ->
      __str_strip_prefix t2 s2 ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type
        (mkEq (__pair_first (__str_strip_prefix t2 s2))
          (__pair_second (__str_strip_prefix t2 s2))) ->
      eo_interprets M
        (mkEq (__pair_first (__str_strip_prefix t2 s2))
          (__pair_second (__str_strip_prefix t2 s2))) true)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2))))) :
    eo_interprets M
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))) true := by
  have hIte :
      __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
        Term.Stuck := by
    simpa [__str_strip_prefix] using hStrip
  rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
      (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
    hCond | hCond
  · have hTailEq :=
      eo_interprets_str_concat_tails_of_head_eo_eq_true M hM t u t2 s2 hCond hXY
    have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
      simpa [hCond, eo_ite_true] using hIte
    have hTailBool : RuleProofs.eo_has_bool_type
        (mkEq (__pair_first (__str_strip_prefix t2 s2))
          (__pair_second (__str_strip_prefix t2 s2))) := by
      simpa [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond] using hBool
    exact eo_interprets_str_strip_prefix_concat_true_of_tail M t u t2 s2 hCond
      (hTail hTailEq hTailNonStuck hTailBool)
  · exact eo_interprets_str_strip_prefix_concat_false M t u t2 s2 hCond hXY

private theorem eo_interprets_str_strip_prefix_result
    (M : SmtModel) (hM : model_total_typed M) (x y : Term)
    (hXY : eo_interprets M (mkEq x y) true)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__pair_first (__str_strip_prefix x y))
        (__pair_second (__str_strip_prefix x y)))) :
    eo_interprets M
      (mkEq (__pair_first (__str_strip_prefix x y))
        (__pair_second (__str_strip_prefix x y))) true := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    exact eo_interprets_str_strip_prefix_concat_step M hM t u t2 s2
      hXY hStrip
      (eo_interprets_str_strip_prefix_result M hM t2 s2) hBool
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair, pair_second_pair]
      using hXY
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem str_strip_prefix_result_types_of_seq
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__pair_first (__str_strip_prefix x y))) =
        SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__pair_second (__str_strip_prefix x y))) =
        SmtType.Seq T := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    have hLeftNN :
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) ≠ SmtType.None := by
      rw [hxTy]
      exact seq_ne_none T
    have hRightNN :
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) ≠ SmtType.None := by
      rw [hyTy]
      exact seq_ne_none T
    rcases str_concat_args_of_non_none t t2 hLeftNN with ⟨U, htTy, ht2TyU⟩
    rcases str_concat_args_of_non_none u s2 hRightNN with ⟨V, huTy, hs2TyV⟩
    have hLeftTyU :
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq U :=
      smt_typeof_str_concat_of_seq t t2 U htTy ht2TyU
    have hRightTyV :
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq V :=
      smt_typeof_str_concat_of_seq u s2 V huTy hs2TyV
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hLeftTyU, hxTy]
      injection hSeq
    have hVT : V = T := by
      have hSeq : SmtType.Seq V = SmtType.Seq T := by
        rw [← hRightTyV, hyTy]
      injection hSeq
    have ht2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T := by
      simpa [hUT] using ht2TyU
    have hs2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T := by
      simpa [hVT] using hs2TyV
    have hIte :
        __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
      hCond | hCond
    · have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      rw [hCond, eo_ite_true]
      exact str_strip_prefix_result_types_of_seq t2 s2 T ht2Ty hs2Ty hTailNonStuck
    · rw [hCond, eo_ite_false]
      simpa [mkPair, pair_first_pair, pair_second_pair] using And.intro hxTy hyTy
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair, pair_second_pair]
      using And.intro hxTy hyTy
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem concatEq_false_has_bool_type_of_seq
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) := by
  let strip := __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t)
  have hIntroSNonStuck :
      __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroTNonStuck :
      __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq s T hsTy hIntroSNN
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq t T htTy hIntroTNN
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) ≠
      Term.Stuck
    simpa [concatEqStrip_false] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hStripTypes :
      __smtx_typeof (__eo_to_smt (__pair_first strip)) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__pair_second strip)) = SmtType.Seq T :=
    str_strip_prefix_result_types_of_seq (__str_nary_intro s) (__str_nary_intro t)
      T hIntroSTy hIntroTTy hStripNonStuck
  have hElimFirstNonStuck :
      __str_nary_elim (__pair_first strip) ≠ Term.Stuck := by
    simpa [strip, concatEqLhs_false] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hElimSecondNonStuck :
      __str_nary_elim (__pair_second strip) ≠ Term.Stuck := by
    simpa [strip, concatEqRhs_false] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hElimFirstTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_first strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (__pair_first strip) T
      hStripTypes.1 hElimFirstNonStuck
  have hElimSecondTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_second strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (__pair_second strip) T
      hStripTypes.2 hElimSecondNonStuck
  have hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__pair_first strip))
        (__str_nary_elim (__pair_second strip))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimFirstTy, hElimSecondTy]
    · rw [hElimFirstTy]
      exact seq_ne_none T
  simpa [strip, concatEqLhs_false, concatEqRhs_false] using hFinalBool

private theorem eo_interprets_concat_eq_false_of_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hPrem : eo_interprets M (mkEq s t) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t))) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) true := by
  let strip := __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t)
  have hIntroSNonStuck :
      __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroTNonStuck :
      __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq s T hsTy hIntroSNN
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq t T htTy hIntroTNN
  have hIntroBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_intro s) (__str_nary_intro t)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hIntroSTy, hIntroTTy]
    · rw [hIntroSTy]
      exact seq_ne_none T
  have hIntroEq : eo_interprets M
      (mkEq (__str_nary_intro s) (__str_nary_intro t)) true :=
    eo_interprets_str_nary_intro_congr_of_seq M hM s t T
      hsTy htTy hIntroSNonStuck hIntroTNonStuck hPrem hIntroBool
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) ≠
      Term.Stuck
    simpa [concatEqStrip_false] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hStripTypes :
      __smtx_typeof (__eo_to_smt (__pair_first strip)) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__pair_second strip)) = SmtType.Seq T :=
    str_strip_prefix_result_types_of_seq (__str_nary_intro s) (__str_nary_intro t)
      T hIntroSTy hIntroTTy hStripNonStuck
  have hStripBool : RuleProofs.eo_has_bool_type
      (mkEq (__pair_first strip) (__pair_second strip)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hStripTypes.1, hStripTypes.2]
    · rw [hStripTypes.1]
      exact seq_ne_none T
  have hStripEq : eo_interprets M
      (mkEq (__pair_first strip) (__pair_second strip)) true :=
    eo_interprets_str_strip_prefix_result M hM
      (__str_nary_intro s) (__str_nary_intro t) hIntroEq hStripNonStuck
      hStripBool
  have hElimFirstNonStuck :
      __str_nary_elim (__pair_first strip) ≠ Term.Stuck := by
    simpa [strip, concatEqLhs_false] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hElimSecondNonStuck :
      __str_nary_elim (__pair_second strip) ≠ Term.Stuck := by
    simpa [strip, concatEqRhs_false] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (concatEqLhs (Term.Boolean false) s t)
      (concatEqRhs (Term.Boolean false) s t) hFinalBool with
    ⟨hFinalSame, hFinalLeftNN⟩
  have hElimFirstNN :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_first strip))) ≠
        SmtType.None := by
    simpa [strip, concatEqLhs_false] using hFinalLeftNN
  have hElimSecondNN :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_second strip))) ≠
        SmtType.None := by
    have hRightNN :
        __smtx_typeof (__eo_to_smt (concatEqRhs (Term.Boolean false) s t)) ≠
          SmtType.None := by
      rw [← hFinalSame]
      exact hFinalLeftNN
    simpa [strip, concatEqRhs_false] using hRightNN
  have hElimFirstTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_first strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq (__pair_first strip) T
      hStripTypes.1 hElimFirstNN
  have hElimSecondTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_second strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq (__pair_second strip) T
      hStripTypes.2 hElimSecondNN
  have hFinalBool' : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__pair_first strip))
        (__str_nary_elim (__pair_second strip))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimFirstTy, hElimSecondTy]
    · rw [hElimFirstTy]
      exact seq_ne_none T
  have hFinal :=
    eo_interprets_str_nary_elim_congr_of_seq M hM
      (__pair_first strip) (__pair_second strip) T
      hStripTypes.1 hStripTypes.2 hElimFirstNonStuck hElimSecondNonStuck
      hStripEq hFinalBool'
  simpa [strip, concatEqLhs_false, concatEqRhs_false] using hFinal

private theorem eo_interprets_concat_eq_false_of_seq'
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hPrem : eo_interprets M (mkEq s t) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) true := by
  have hFinalBool :=
    concatEq_false_has_bool_type_of_seq s t T hsTy htTy hIntroSNN hIntroTNN
      hProg
  exact eo_interprets_concat_eq_false_of_seq M hM s t T hsTy htTy
    hIntroSNN hIntroTNN hPrem hProg hFinalBool

private theorem concatEq_true_has_bool_type_of_seq
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) := by
  let revS := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)
  let revT := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)
  let strip := __str_strip_prefix revS revT
  have hIntroSNonStuck : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroTNonStuck : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq s T hsTy hIntroSNN
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq t T htTy hIntroTNN
  have hRevSNonStuck : revS ≠ Term.Stuck := by
    simpa [revS] using
      concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevTNonStuck : revT ≠ Term.Stuck := by
    simpa [revT] using
      concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hIntroSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevSNonStuck
  have hIntroTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevTNonStuck
  have hRevSTy : __smtx_typeof (__eo_to_smt revS) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro s) T
      hIntroSList hIntroSTy hRevSNonStuck
  have hRevTTy : __smtx_typeof (__eo_to_smt revT) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro t) T
      hIntroTList hIntroTTy hRevTNonStuck
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix revS revT ≠ Term.Stuck
    simpa [strip, revS, revT, concatEqStrip_true] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hStripTypes :
      __smtx_typeof (__eo_to_smt (__pair_first strip)) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__pair_second strip)) = SmtType.Seq T :=
    str_strip_prefix_result_types_of_seq revS revT T hRevSTy hRevTTy
      hStripNonStuck
  have hFirstRevNonStuck :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first strip) ≠
        Term.Stuck := by
    simpa [strip, concatEqStrip_true] using
      concatEq_true_rev_first_ne_stuck_of_prog_ne_stuck s t hProg
  have hSecondRevNonStuck :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__pair_second strip) ≠
        Term.Stuck := by
    simpa [strip, concatEqStrip_true] using
      concatEq_true_rev_second_ne_stuck_of_prog_ne_stuck s t hProg
  have hFirstList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__pair_first strip) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_first strip) hFirstRevNonStuck
  have hSecondList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__pair_second strip) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_second strip) hSecondRevNonStuck
  have hFirstRevTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first strip))) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__pair_first strip) T hFirstList
      hStripTypes.1 hFirstRevNonStuck
  have hSecondRevTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second strip))) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__pair_second strip) T hSecondList
      hStripTypes.2 hSecondRevNonStuck
  have hElimFirstNonStuck :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first strip)) ≠ Term.Stuck := by
    simpa [strip, concatEqLhs_true] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hElimSecondNonStuck :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second strip)) ≠ Term.Stuck := by
    simpa [strip, concatEqRhs_true] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hElimFirstTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_first strip)))) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first strip)) T
      hFirstRevTy hElimFirstNonStuck
  have hElimSecondTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_second strip)))) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_second strip)) T
      hSecondRevTy hElimSecondNonStuck
  have hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first strip)))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second strip)))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimFirstTy, hElimSecondTy]
    · rw [hElimFirstTy]
      exact seq_ne_none T
  simpa [strip, revS, revT, concatEqLhs_true, concatEqRhs_true] using
    hFinalBool

private theorem concatEq_true_has_bool_type_of_left_seq
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact concatEq_true_has_bool_type_of_seq s t T hsTy htTy hIntroSNN
    hIntroTNN hProg

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

private theorem eo_interprets_str_concat_heads_of_tail_eo_eq_true
    (M : SmtModel) (hM : model_total_typed M) (t u t2 s2 : Term)
    (hTail : __eo_eq t u = Term.Boolean true) :
    eo_interprets M (mkEq (mkConcat t2 t) (mkConcat s2 u)) true ->
    eo_interprets M (mkEq t2 s2) true := by
  intro h
  have hUT : u = t := eq_of_eo_eq_true_local t u hTail
  subst u
  exact eo_interprets_str_concat_right_cancel M hM t t2 s2 h

private theorem eo_interprets_rev_tails_of_head_eo_eq_true
    (M : SmtModel) (hM : model_total_typed M) (t u t2 s2 : Term)
    (hHead : __eo_eq t u = Term.Boolean true) :
    eo_interprets M
      (mkEq
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2)) t)
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)) u))
      true ->
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  exact eo_interprets_str_concat_heads_of_tail_eo_eq_true M hM t u
    (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
    (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)) hHead

private theorem eo_typeof_eq_operands_same_of_bool (x y : Term)
    (hTy : __eo_typeof (mkEq x y) = Term.Bool) :
    __eo_typeof x = __eo_typeof y ∧
      __eo_typeof x ≠ Term.Stuck ∧
      __eo_typeof y ≠ Term.Stuck := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at hTy
  by_cases hx : __eo_typeof x = Term.Stuck
  · simp [hx, __eo_typeof_eq] at hTy
  by_cases hy : __eo_typeof y = Term.Stuck
  · simp [hy, __eo_typeof_eq] at hTy
  have hReq :
      __eo_requires (__eo_eq (__eo_typeof x) (__eo_typeof y))
        (Term.Boolean true) Term.Bool = Term.Bool := by
    simpa [hx, hy, __eo_typeof_eq] using hTy
  have hReqNonStuck :
      __eo_requires (__eo_eq (__eo_typeof x) (__eo_typeof y))
        (Term.Boolean true) Term.Bool ≠ Term.Stuck := by
    rw [hReq]
    intro h
    cases h
  have hEq :
      __eo_eq (__eo_typeof x) (__eo_typeof y) = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_eq (__eo_typeof x) (__eo_typeof y))
      (Term.Boolean true) Term.Bool hReqNonStuck
  have hSame : __eo_typeof x = __eo_typeof y :=
    (eq_of_eo_eq_true_local (__eo_typeof x) (__eo_typeof y) hEq).symm
  exact ⟨hSame, hx, hy⟩

private theorem concatEq_result_operands_same_eo_type (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck)
    (hTy :
      __eo_typeof (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) =
        Term.Bool) :
    __eo_typeof (concatEqLhs rev s t) = __eo_typeof (concatEqRhs rev s t) ∧
      __eo_typeof (concatEqLhs rev s t) ≠ Term.Stuck ∧
      __eo_typeof (concatEqRhs rev s t) ≠ Term.Stuck := by
  have hProgEq := eo_prog_concat_eq_eq_of_ne_stuck rev s t hProg
  have hOutTy :
      __eo_typeof (mkEq (concatEqLhs rev s t) (concatEqRhs rev s t)) =
        Term.Bool := by
    simpa [hProgEq] using hTy
  exact eo_typeof_eq_operands_same_of_bool
    (concatEqLhs rev s t) (concatEqRhs rev s t) hOutTy

private theorem step_concat_eq_false_of_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean false) s t hProg
  have hFinalBool :=
    concatEq_false_has_bool_type_of_seq s t T hsTy htTy hIntroSNN hIntroTNN
      hProg
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq]
    exact eo_interprets_concat_eq_false_of_seq' M hM s t T hsTy htTy
      hIntroSNN hIntroTNN hPrem hProg
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) hFinalBool

private theorem step_concat_eq_false_of_left_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_false_of_seq M hM s t T hsTy htTy
    hIntroSNN hIntroTNN hProg

private theorem step_concat_eq_core
    (M : SmtModel) (hM : model_total_typed M)
    (rev s t : Term)
    (hRevTrans : RuleProofs.eo_has_smt_translation rev)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck)
    (hResultTy :
      __eo_typeof (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) =
        Term.Bool) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) := by
  have hProgEq := eo_prog_concat_eq_eq_of_ne_stuck rev s t hProg
  have hRevCases := concatEq_rev_cases_of_prog_ne_stuck rev s t hProg
  have hOutEoTypes := concatEq_result_operands_same_eo_type rev s t hProg hResultTy
  by_cases hFalseSeq :
      rev = Term.Boolean false ∧
        ∃ T,
          __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
          __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None ∧
          __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None
  · rcases hFalseSeq with ⟨hRev, T, hsTy, hIntroSNN, hIntroTNN⟩
    subst rev
    exact step_concat_eq_false_of_left_seq M hM s t T hPremBool hsTy
      hIntroSNN hIntroTNN hProg
  · -- Remaining core: the `rev = true` suffix-canceling branch, plus the
    -- side-condition proof that a successful `rev = false` step supplies the
    -- sequence/intro-translation package consumed above.
    sorry

theorem cmd_step_concat_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_eq args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_eq args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  let X1 := __eo_state_proven_nth s n1
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    have hArgs : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                      simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                    exact hArgs.1
                  have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
                    hPremisesBool X1 (by simp [X1, premiseTermList])
                  have hProgConcatEq :
                      __eo_prog_concat_eq a1 (Proof.pf X1) ≠ Term.Stuck := by
                    change __eo_prog_concat_eq a1
                      (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                    simpa [X1] using hProg
                  rcases eo_prog_concat_eq_premise_eq_shape_of_ne_stuck a1 X1
                      hProgConcatEq with ⟨lhs, rhs, hX1Eq⟩
                  have hStateEq :
                      __eo_state_proven_nth s n1 = mkEq lhs rhs := by
                    simpa [X1] using hX1Eq
                  have hPremEqBool : RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
                    simpa [X1, hStateEq] using hX1Bool
                  have hProgRule :
                      __eo_prog_concat_eq a1 (Proof.pf (mkEq lhs rhs)) ≠
                        Term.Stuck := by
                    simpa [X1, hStateEq] using hProgConcatEq
                  have hResultTyRule :
                      __eo_typeof
                        (__eo_prog_concat_eq a1 (Proof.pf (mkEq lhs rhs))) =
                        Term.Bool := by
                    change __eo_typeof
                      (__eo_prog_concat_eq a1
                        (Proof.pf (__eo_state_proven_nth s n1))) = Term.Bool at hResultTy
                    simpa [hStateEq] using hResultTy
                  change StepRuleProperties M [__eo_state_proven_nth s n1]
                    (__eo_prog_concat_eq a1
                      (Proof.pf (__eo_state_proven_nth s n1)))
                  rw [hStateEq]
                  exact step_concat_eq_core M hM a1 lhs rhs hA1Trans
                    hPremEqBool hProgRule hResultTyRule
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
