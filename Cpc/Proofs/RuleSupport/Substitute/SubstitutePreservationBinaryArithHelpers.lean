module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationShared
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationShared
public import Cpc.Proofs.RuleSupport.TypedListSubstitutionSupport
import all Cpc.Proofs.RuleSupport.TypedListSubstitutionSupport

public section

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open TypedListSubstitutionSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

namespace SubstitutePreservationSupport

theorem smt_typeof_eq_self_ne_none_of_ne_none
    {T : SmtType}
    (hT : T ≠ SmtType.None) :
    __smtx_typeof_eq T T ≠ SmtType.None := by
  cases T <;> simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
    native_Teq] at hT ⊢

private theorem eo_arith_arg_types_of_requires_ne_stuck
    {A B C : Term}
    (h :
      __eo_requires (__eo_eq A B) (Term.Boolean true)
          (__eo_requires (__is_arith_type A) (Term.Boolean true) C) ≠
        Term.Stuck) :
    (A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) ∨
      (A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real) := by
  have hEqCond : __eo_eq A B = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck h
  have hEq : B = A := support_eq_of_eo_eq_true A B hEqCond
  subst B
  cases A <;>
    simp [__eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
      native_not, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;>
      simp [__eo_requires, __eo_eq, __is_arith_type, native_ite, native_teq,
        native_not, SmtEval.native_not] at h ⊢

theorem eo_typeof_plus_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_plus A B ≠ Term.Stuck) :
    (A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) ∨
      (A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real) := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_plus] at h
  by_cases hB : B = Term.Stuck
  · subst B
    simp [__eo_typeof_plus, hA] at h
  · exact eo_arith_arg_types_of_requires_ne_stuck (by
      simpa [__eo_typeof_plus, hA, hB] using h)

theorem eo_typeof_lt_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_lt A B ≠ Term.Stuck) :
    (A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) ∨
      (A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real) := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_lt] at h
  by_cases hB : B = Term.Stuck
  · subst B
    simp [__eo_typeof_lt, hA] at h
  · exact eo_arith_arg_types_of_requires_ne_stuck (by
      simpa [__eo_typeof_lt, hA, hB] using h)

theorem eo_typeof_lt_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_lt A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_lt_arg_types_of_ne_stuck h with
    ⟨hA, hB⟩ | ⟨hA, hB⟩
  · constructor
    · rw [hA]
      decide
    · rw [hB]
      decide
  · constructor
    · rw [hA]
      decide
    · rw [hB]
      decide

theorem smt_arith_ret_bool_non_none_of_eo_typeof_lt_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_lt (__eo_typeof X) (__eo_typeof Y) ≠ Term.Stuck) :
    __smtx_typeof_arith_overload_op_2_ret
        (__smtx_typeof (__eo_to_smt X)) (__smtx_typeof (__eo_to_smt Y))
        SmtType.Bool ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_lt_arg_types_of_ne_stuck hApp with
    ⟨hXTy, hYTy⟩ | ⟨hXTy, hYTy⟩
  · rw [hXSmt, hYSmt, hXTy, hYTy]
    simp [__eo_to_smt_type, __smtx_typeof_arith_overload_op_2_ret]
  · rw [hXSmt, hYSmt, hXTy, hYTy]
    simp [__eo_to_smt_type, __smtx_typeof_arith_overload_op_2_ret]

theorem eo_typeof_div_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_div A B ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int := by
  cases A <;> cases B <;> simp [__eo_typeof_div] at h ⊢
  case UOp.UOp opA opB =>
    cases opA <;> cases opB <;> simp at h ⊢

theorem eo_typeof_divisible_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_divisible A B ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int := by
  cases A <;> cases B <;> simp [__eo_typeof_divisible] at h ⊢
  case UOp.UOp opA opB =>
    cases opA <;> cases opB <;> simp at h ⊢

theorem eo_int_binop_args_not_stuck
    {A B : Term}
    (hArgs : A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  constructor
  · rw [hArgs.1]
    decide
  · rw [hArgs.2]
    decide

theorem eo_typeof_qdiv_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_qdiv A B ≠ Term.Stuck) :
    (A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) ∨
      (A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real) := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_qdiv] at h
  by_cases hB : B = Term.Stuck
  · subst B
    simp [__eo_typeof_qdiv, hA] at h
  · exact eo_arith_arg_types_of_requires_ne_stuck (by
      simpa [__eo_typeof_qdiv, hA, hB] using h)

theorem eo_typeof_qdiv_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_qdiv A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_qdiv_arg_types_of_ne_stuck h with
    ⟨hA, hB⟩ | ⟨hA, hB⟩
  · constructor
    · rw [hA]
      decide
    · rw [hB]
      decide
  · constructor
    · rw [hA]
      decide
    · rw [hB]
      decide

theorem smt_arith_ret_real_non_none_of_eo_typeof_qdiv_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_qdiv (__eo_typeof X) (__eo_typeof Y) ≠ Term.Stuck) :
    __smtx_typeof_arith_overload_op_2_ret
        (__smtx_typeof (__eo_to_smt X)) (__smtx_typeof (__eo_to_smt Y))
        SmtType.Real ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_qdiv_arg_types_of_ne_stuck hApp with
    ⟨hXTy, hYTy⟩ | ⟨hXTy, hYTy⟩
  · rw [hXSmt, hYSmt, hXTy, hYTy]
    simp [__eo_to_smt_type, __smtx_typeof_arith_overload_op_2_ret]
  · rw [hXSmt, hYSmt, hXTy, hYTy]
    simp [__eo_to_smt_type, __smtx_typeof_arith_overload_op_2_ret]

end SubstitutePreservationSupport
