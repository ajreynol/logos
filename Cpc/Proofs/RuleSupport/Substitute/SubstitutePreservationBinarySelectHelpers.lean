module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryArithHelpers
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryArithHelpers

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

theorem eo_typeof_select_arg_types_of_ne_stuck
    {A I : Term}
    (h : __eo_typeof_select A I ≠ Term.Stuck) :
    ∃ E : Term,
      A = Term.Apply (Term.Apply (Term.UOp UserOp.Array) I) E := by
  by_cases hI : I = Term.Stuck
  · subst I
    simp [__eo_typeof_select] at h
  · cases A with
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | UOp op =>
                cases op with
                | Array =>
                    have hReq :
                        __eo_requires (__eo_eq y I) (Term.Boolean true) x ≠
                          Term.Stuck := by
                      simpa [__eo_typeof_select, hI] using h
                    have hEq : I = y :=
                      support_eq_of_eo_eq_true y I
                        (support_eo_requires_cond_eq_of_non_stuck hReq)
                    exact ⟨x, by simp [hEq]⟩
                | _ =>
                    simp [__eo_typeof_select] at h
            | _ =>
                simp [__eo_typeof_select] at h
        | _ =>
            simp [__eo_typeof_select] at h
    | _ =>
        simp [__eo_typeof_select] at h

theorem eo_typeof_select_args_not_stuck_of_ne_stuck
    {A I : Term}
    (h : __eo_typeof_select A I ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ I ≠ Term.Stuck := by
  rcases eo_typeof_select_arg_types_of_ne_stuck h with ⟨E, hA⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hStuck] at h
    simp [__eo_typeof_select] at h

theorem smt_select_non_none_of_eo_typeof_select_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_select (__eo_typeof X) (__eo_typeof Y) ≠ Term.Stuck) :
    __smtx_typeof
        (SmtTerm.select (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_select_arg_types_of_ne_stuck hApp with
    ⟨E, hXTy⟩
  have hXTyNN :
      __eo_to_smt_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.Array) (__eo_typeof Y))
            E) ≠
        SmtType.None := by
    simpa [hXTy] using
      eo_to_smt_typeof_ne_none_of_has_smt_translation X hXTrans
  rw [typeof_select_eq, hXSmt, hYSmt, hXTy]
  cases hYTySmt : __eo_to_smt_type (__eo_typeof Y) <;>
    cases hESmt : __eo_to_smt_type E <;>
    simp [TranslationProofs.eo_to_smt_type_array, __smtx_typeof_select,
      __smtx_typeof_guard, native_ite, native_Teq, hYTySmt, hESmt] at hXTyNN ⊢

end SubstitutePreservationSupport
