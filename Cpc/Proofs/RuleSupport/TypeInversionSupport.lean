import Cpc.Proofs.RuleSupport.Support

/-! Shared compositional inversion lemmas for EO type-checking functions. -/

open Eo
open SmtEval

set_option linter.unusedVariables false

namespace RuleProofs

/-- A successful EO equality-type check identifies equal, non-stuck operands.

This proof deliberately avoids a Cartesian case split over both `Term`
arguments.  Several rule proofs used to duplicate that expensive split. -/
theorem eo_typeof_eq_bool_same (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B ∧ A ≠ Term.Stuck := by
  have hEq : A = B := support_eo_typeof_eq_bool_operands_eq A B h
  have hA : A ≠ Term.Stuck := by
    intro hStuck
    have hBStuck : B = Term.Stuck := hEq ▸ hStuck
    subst A
    subst B
    simp [__eo_typeof_eq] at h
  exact ⟨hEq, hA⟩

/-- A non-stuck EO equality-type check is necessarily Boolean. -/
theorem eo_typeof_eq_eq_bool_of_ne_stuck (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  have hA : A ≠ Term.Stuck := by
    intro hStuck
    subst A
    exact h rfl
  have hB : B ≠ Term.Stuck := by
    intro hStuck
    subst B
    simp [__eo_typeof_eq] at h
  have hReqNe :
      __eo_requires (__eo_eq A B) (Term.Boolean true) Term.Bool ≠
        Term.Stuck := by
    simpa [__eo_typeof_eq, hA, hB] using h
  have hBA : B = A :=
    support_eq_of_eo_eq_true A B
      (support_eo_requires_cond_eq_of_non_stuck hReqNe)
  subst B
  simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite,
    native_teq, native_not]

/-- Invert a non-stuck EO equality-type check. -/
theorem eo_typeof_eq_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    A = B ∧ A ≠ Term.Stuck := by
  exact eo_typeof_eq_bool_same A B
    (eo_typeof_eq_eq_bool_of_ne_stuck A B h)

/-- The EO arithmetic-type predicate recognizes exactly `Int` and `Real`.

Only the single inspected operand is split here; callers do not enumerate a
cross-product of two `Term`s and two `UserOp`s. -/
theorem is_arith_type_true_cases (A : Term)
    (h : __is_arith_type A = Term.Boolean true) :
    A = Term.Int ∨ A = Term.Real := by
  cases A <;> simp [__is_arith_type] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

/-- A non-stuck EO arithmetic-relation type check is necessarily Boolean. -/
theorem eo_typeof_lt_eq_bool_of_ne_stuck (A B : Term)
    (h : __eo_typeof_lt A B ≠ Term.Stuck) :
    __eo_typeof_lt A B = Term.Bool := by
  have hA : A ≠ Term.Stuck := by
    intro hStuck
    subst A
    exact h rfl
  have hB : B ≠ Term.Stuck := by
    intro hStuck
    subst B
    simp [__eo_typeof_lt] at h
  have hReqNe :
      __eo_requires (__eo_eq A B) (Term.Boolean true)
        (__eo_requires (__is_arith_type A) (Term.Boolean true) Term.Bool) ≠
        Term.Stuck := by
    simpa [__eo_typeof_lt, hA, hB] using h
  have hBA : B = A :=
    support_eq_of_eo_eq_true A B
      (support_eo_requires_cond_eq_of_non_stuck hReqNe)
  subst B
  have hInnerNe :
      __eo_requires (__is_arith_type A) (Term.Boolean true) Term.Bool ≠
        Term.Stuck := by
    simpa [__eo_requires, __eo_eq, hA, native_ite, native_teq, native_not]
      using hReqNe
  have hArith : __is_arith_type A = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hInnerNe
  rcases is_arith_type_true_cases A hArith with rfl | rfl <;> rfl

/-- A successful EO arithmetic-relation type check has matching arithmetic
operand types. -/
theorem eo_typeof_lt_bool_cases (A B : Term)
    (h : __eo_typeof_lt A B = Term.Bool) :
    (A = Term.Int ∧ B = Term.Int) ∨
      (A = Term.Real ∧ B = Term.Real) := by
  have hNe : __eo_typeof_lt A B ≠ Term.Stuck := by
    rw [h]
    exact Term.noConfusion
  have hA : A ≠ Term.Stuck := by
    intro hStuck
    subst A
    simp [__eo_typeof_lt] at h
  have hB : B ≠ Term.Stuck := by
    intro hStuck
    subst B
    simp [__eo_typeof_lt] at h
  have hReqNe :
      __eo_requires (__eo_eq A B) (Term.Boolean true)
        (__eo_requires (__is_arith_type A) (Term.Boolean true) Term.Bool) ≠
        Term.Stuck := by
    simpa [__eo_typeof_lt, hA, hB] using hNe
  have hBA : B = A :=
    support_eq_of_eo_eq_true A B
      (support_eo_requires_cond_eq_of_non_stuck hReqNe)
  subst B
  have hInnerNe :
      __eo_requires (__is_arith_type A) (Term.Boolean true) Term.Bool ≠
        Term.Stuck := by
    simpa [__eo_requires, __eo_eq, hA, native_ite, native_teq, native_not]
      using hReqNe
  have hArith : __is_arith_type A = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hInnerNe
  rcases is_arith_type_true_cases A hArith with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- Invert a successful EO `ite` type check without enumerating the three-way
Cartesian product of its operand types. -/
theorem eo_typeof_ite_eq_nonstuck_args
    (C A B T : Term)
    (h : __eo_typeof_ite C A B = T)
    (hT : T ≠ Term.Stuck) :
    C = Term.Bool ∧ A = T ∧ B = T := by
  have hA : A ≠ Term.Stuck := by
    intro hStuck
    subst A
    simp [__eo_typeof_ite] at h
    exact hT h.symm
  have hB : B ≠ Term.Stuck := by
    intro hStuck
    subst B
    simp [__eo_typeof_ite] at h
    exact hT h.symm
  have hIteNe : __eo_typeof_ite C A B ≠ Term.Stuck := by
    rw [h]
    exact hT
  have hC : C = Term.Bool := by
    cases C <;> simp [__eo_typeof_ite] at hIteNe ⊢
  subst C
  have hReqNe :
      __eo_requires (__eo_eq A B) (Term.Boolean true) A ≠ Term.Stuck := by
    simpa [__eo_typeof_ite, hA, hB] using hIteNe
  have hBA : B = A :=
    support_eq_of_eo_eq_true A B
      (support_eo_requires_cond_eq_of_non_stuck hReqNe)
  subst B
  have hRed : __eo_typeof_ite Term.Bool A A = A := by
    simp [__eo_typeof_ite, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  rw [hRed] at h
  exact ⟨rfl, h, h⟩

/-- Invert any non-stuck EO `ite` type check. -/
theorem eo_typeof_ite_args_of_ne_stuck (C A B : Term)
    (h : __eo_typeof_ite C A B ≠ Term.Stuck) :
    C = Term.Bool ∧ A = B ∧ A ≠ Term.Stuck := by
  have hArgs := eo_typeof_ite_eq_nonstuck_args C A B
    (__eo_typeof_ite C A B) rfl h
  exact ⟨hArgs.1, hArgs.2.1.trans hArgs.2.2.symm,
    hArgs.2.1 ▸ h⟩

/-- A well-formed `ite` with identical branches has that branch type. -/
theorem eo_typeof_ite_bool_self (T : Term) (hT : T ≠ Term.Stuck) :
    __eo_typeof_ite Term.Bool T T = T := by
  simp [__eo_typeof_ite, __eo_requires, __eo_eq, native_ite, native_teq,
    native_not]

end RuleProofs
