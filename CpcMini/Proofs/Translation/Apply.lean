import CpcMini.Proofs.Translation.Datatypes
import CpcMini.Proofs.TypePreservation.CoreArith

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Derives `smtx_typeof_apply_generic` from `head_not_special`. -/
private theorem smtx_typeof_apply_generic_of_head_not_special
    (f x : SmtTerm)
    (hNot : f ≠ SmtTerm.TheoryOp SmtTheoryOp.not)
    (hOr : ∀ y, f ≠ SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.or) y)
    (hAnd : ∀ y, f ≠ SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) y)
    (hImp : ∀ y, f ≠ SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) y)
    (hDtSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hDtTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  exact __smtx_typeof.eq_18 f x
    hNot
    (by intro y hEq; exact hOr y hEq)
    (by intro y hEq; exact hAnd y hEq)
    (by intro y hEq; exact hImp y hEq)
    (by intro s d i j hEq; exact hDtSel s d i j hEq)
    (by intro s d i hEq; exact hDtTester s d i hEq)

/-- Shows that generic EO application translation satisfies `generic_apply_type`. -/
private theorem eo_to_smt_ne_bare_theory_op
    (t : Term) (op : SmtTheoryOp) :
    __eo_to_smt t ≠ SmtTerm.TheoryOp op := by
  intro h
  cases t with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h
      | Var s T =>
          cases s <;> rw [__eo_to_smt.eq_def] at h <;> cases h
      | _ =>
          rw [__eo_to_smt.eq_def] at h
          cases h
  | Var s T =>
      cases s <;> rw [__eo_to_smt.eq_def] at h <;> cases h
  | _ =>
      rw [__eo_to_smt.eq_def] at h
      cases h

private theorem eo_to_smt_ne_partial_theory_or
    (t : Term) (y : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.or) y := by
  intro h
  cases t with
  | Apply f x =>
      cases f with
      | Apply g y' =>
          cases g <;> rw [__eo_to_smt.eq_def] at h
          all_goals
            try cases h
          case Apply a b =>
            injection h with hHead hArg
            exact eo_to_smt_ne_bare_theory_op (Term.Apply (Term.Apply a b) y') SmtTheoryOp.or hHead
      | Var s T =>
          cases s <;> rw [__eo_to_smt.eq_def] at h <;> cases h
      | _ =>
          rw [__eo_to_smt.eq_def] at h
          cases h
  | Var s T =>
      cases s <;> rw [__eo_to_smt.eq_def] at h <;> cases h
  | _ =>
      rw [__eo_to_smt.eq_def] at h
      cases h

private theorem eo_to_smt_ne_partial_theory_and
    (t : Term) (y : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) y := by
  intro h
  cases t with
  | Apply f x =>
      cases f with
      | Apply g y' =>
          cases g <;> rw [__eo_to_smt.eq_def] at h
          all_goals
            try cases h
          case Apply a b =>
            injection h with hHead hArg
            exact eo_to_smt_ne_bare_theory_op (Term.Apply (Term.Apply a b) y') SmtTheoryOp.and hHead
      | Var s T =>
          cases s <;> rw [__eo_to_smt.eq_def] at h <;> cases h
      | _ =>
          rw [__eo_to_smt.eq_def] at h
          cases h
  | Var s T =>
      cases s <;> rw [__eo_to_smt.eq_def] at h <;> cases h
  | _ =>
      rw [__eo_to_smt.eq_def] at h
      cases h

private theorem eo_to_smt_ne_partial_theory_imp
    (t : Term) (y : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) y := by
  intro h
  cases t with
  | Apply f x =>
      cases f with
      | Apply g y' =>
          cases g <;> rw [__eo_to_smt.eq_def] at h
          all_goals
            try cases h
          case Apply a b =>
            injection h with hHead hArg
            exact eo_to_smt_ne_bare_theory_op (Term.Apply (Term.Apply a b) y') SmtTheoryOp.imp hHead
      | Var s T =>
          cases s <;> rw [__eo_to_smt.eq_def] at h <;> cases h
      | _ =>
          rw [__eo_to_smt.eq_def] at h
          cases h
  | Var s T =>
      cases s <;> rw [__eo_to_smt.eq_def] at h <;> cases h
  | _ =>
      rw [__eo_to_smt.eq_def] at h
      cases h

theorem eo_to_smt_apply_generic_type
    (f x : Term)
    (hNoSel : ∀ s d i j, f ≠ Term.DtSel s d i j) :
    generic_apply_type (__eo_to_smt f) (__eo_to_smt x) := by
  apply smtx_typeof_apply_generic_of_head_not_special
  · exact eo_to_smt_ne_bare_theory_op f SmtTheoryOp.not
  · exact eo_to_smt_ne_partial_theory_or f
  · exact eo_to_smt_ne_partial_theory_and f
  · exact eo_to_smt_ne_partial_theory_imp f
  · intro s d i j
    exact eo_to_smt_ne_dt_sel f hNoSel s d i j
  · intro s d i
    exact eo_to_smt_ne_dt_tester f s d i

/-- Computes `__smtx_typeof` for `translation_not_of_non_none`. -/
theorem smtx_typeof_translation_not_of_non_none
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
    cases h : __smtx_typeof (__eo_to_smt x) <;>
      simp [__smtx_typeof.eq_6, native_ite, native_Teq, h] at hNonNone
    simp
  simp [__smtx_typeof.eq_6, native_ite, native_Teq, hArg]

/-- Computes `__smtx_typeof` for `translation_or_of_non_none`. -/
theorem smtx_typeof_translation_or_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.or) (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none
    (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.or) t1) t2)
    (__smtx_typeof.eq_7 (__eo_to_smt x) (__eo_to_smt y)) hApplyNN
  simp [__smtx_typeof.eq_7, native_ite, native_Teq, hArgs.1, hArgs.2]

/-- Computes `__smtx_typeof` for `translation_and_of_non_none`. -/
theorem smtx_typeof_translation_and_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none
    (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) t1) t2)
    (__smtx_typeof.eq_8 (__eo_to_smt x) (__eo_to_smt y)) hApplyNN
  simp [__smtx_typeof.eq_8, native_ite, native_Teq, hArgs.1, hArgs.2]

/-- Computes `__smtx_typeof` for `translation_imp_of_non_none`. -/
theorem smtx_typeof_translation_imp_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none
    (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) t1) t2)
    (__smtx_typeof.eq_9 (__eo_to_smt x) (__eo_to_smt y)) hApplyNN
  simp [__smtx_typeof.eq_9, native_ite, native_Teq, hArgs.1, hArgs.2]

/-- Computes `__smtx_typeof` for `translation_eq_of_non_none`. -/
theorem smtx_typeof_translation_eq_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.eq x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.eq x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  simpa using
    eq_term_typeof_of_non_none (t1 := __eo_to_smt x) (t2 := __eo_to_smt y) hApplyNN

/-- Extracts the common non-`None` operand type from a non-`None` SMT equality type. -/
theorem smtx_typeof_eq_non_none
    {T U : SmtType}
    (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    T = U ∧ T ≠ SmtType.None := by
  by_cases hNone : T = SmtType.None
  · subst hNone
    exfalso
    exact h (by simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq])
  · by_cases hEq : T = U
    · exact ⟨hEq, hNone⟩
    · exfalso
      exact h (by
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, hNone, hEq])

end TranslationProofs
