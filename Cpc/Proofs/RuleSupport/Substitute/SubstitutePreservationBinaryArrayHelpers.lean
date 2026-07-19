module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinarySelectHelpers
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinarySelectHelpers

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

theorem eo_typeof_array_deq_diff_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_array_deq_diff A B ≠ Term.Stuck) :
    ∃ I E, A = Term.Apply (Term.Apply (Term.UOp UserOp.Array) I) E ∧
      B = Term.Apply (Term.Apply (Term.UOp UserOp.Array) I) E := by
  cases A <;> cases B <;>
    simp [__eo_typeof__at_array_deq_diff] at h ⊢
  case Apply.Apply f E g F =>
    cases f <;> cases g <;>
      simp [__eo_typeof__at_array_deq_diff] at h ⊢
    case Apply.Apply f I g J =>
      cases f <;> cases g <;>
        simp [__eo_typeof__at_array_deq_diff] at h ⊢
      case UOp.UOp opA opB =>
        cases opA <;> cases opB <;>
          simp [__eo_typeof__at_array_deq_diff] at h ⊢
        have hReq :
            __eo_requires (__eo_and (__eo_eq I J) (__eo_eq E F))
                (Term.Boolean true) I ≠
              Term.Stuck := by
          simpa [__eo_typeof__at_array_deq_diff] using h
        have hAnd :
            __eo_and (__eo_eq I J) (__eo_eq E F) = Term.Boolean true :=
          support_eo_requires_cond_eq_of_non_stuck hReq
        have hI : J = I :=
          support_eq_of_eo_eq_true I J
            (eo_and_eq_true_cases hAnd).1
        have hE : F = E :=
          support_eq_of_eo_eq_true E F
            (eo_and_eq_true_cases hAnd).2
        exact ⟨hI.symm, hE.symm⟩

theorem eo_typeof_array_deq_diff_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_array_deq_diff A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_array_deq_diff_arg_types_of_ne_stuck h with
    ⟨I, E, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_array_deq_diff_non_none_of_eo_typeof_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof__at_array_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt_array_deq_diff (__eo_to_smt X)
          (__smtx_typeof (__eo_to_smt X)) (__eo_to_smt Y)
          (__smtx_typeof (__eo_to_smt Y))) ≠ SmtType.None := by
  rcases eo_typeof_array_deq_diff_arg_types_of_ne_stuck hApp with
    ⟨I, E, hXTy, hYTy⟩
  have hXSmt :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) I) E) := by
    have hMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
    rw [hXTy] at hMatch
    exact hMatch
  have hYSmt :
      __smtx_typeof (__eo_to_smt Y) =
        __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) I) E) := by
    have hMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
    rw [hYTy] at hMatch
    exact hMatch
  have hArrayNN :
      __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) I) E) ≠
        SmtType.None := by
    simpa [hXTy] using
      eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
  have hArraySmt :
      __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) I) E) =
        SmtType.Map (__eo_to_smt_type I) (__eo_to_smt_type E) := by
    cases hISmt : __eo_to_smt_type I <;>
      cases hESmt : __eo_to_smt_type E <;>
      simp [TranslationProofs.eo_to_smt_type_array, __smtx_typeof_guard,
        native_ite, native_and, native_Teq, hISmt, hESmt] at hArrayNN ⊢
  rw [hXSmt, hYSmt, hArraySmt]
  change
    __smtx_typeof (SmtTerm.map_diff (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None
  rw [typeof_map_diff_eq, hXSmt, hYSmt, hArraySmt]
  cases hISmt : __eo_to_smt_type I <;>
    cases hESmt : __eo_to_smt_type E <;>
      simp [TranslationProofs.eo_to_smt_type_array, __smtx_typeof_map_diff,
        __smtx_typeof_guard, native_ite, native_and, native_Teq, hISmt, hESmt]
      at hArrayNN ⊢

end SubstitutePreservationSupport
