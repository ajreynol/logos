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
    (hDtSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hDtTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  cases f <;> try rfl
  case DtSel s d i j =>
      exact False.elim (hDtSel s d i j rfl)
  case DtTester s d i =>
      exact False.elim (hDtTester s d i rfl)

/-- Shows that generic EO application translation satisfies `generic_apply_type`. -/
theorem eo_to_smt_apply_generic_type
    (f x : Term)
    (hNoSel : ∀ s d i j, f ≠ Term.DtSel s d i j) :
    generic_apply_type (__eo_to_smt f) (__eo_to_smt x) := by
  apply smtx_typeof_apply_generic_of_head_not_special
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
      simp [__smtx_typeof, native_ite, native_Teq, h] at hNonNone
    simp
  simp [__smtx_typeof, native_ite, native_Teq, hArg]

/-- Computes `__smtx_typeof` for `translation_or_of_non_none`. -/
theorem smtx_typeof_translation_or_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl hApplyNN
  simp [__smtx_typeof, native_ite, native_Teq, hArgs.1, hArgs.2]

/-- Computes `__smtx_typeof` for `translation_and_of_non_none`. -/
theorem smtx_typeof_translation_and_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl hApplyNN
  simp [__smtx_typeof, native_ite, native_Teq, hArgs.1, hArgs.2]

/-- Computes `__smtx_typeof` for `translation_imp_of_non_none`. -/
theorem smtx_typeof_translation_imp_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl hApplyNN
  simp [__smtx_typeof, native_ite, native_Teq, hArgs.1, hArgs.2]

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
