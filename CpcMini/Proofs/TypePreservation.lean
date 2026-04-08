import CpcMini.Proofs.TypePreservation.CoreArith
import CpcMini.Proofs.TypePreservation.Datatypes

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Main type-preservation theorem for evaluation of supported SMT terms in total typed models. -/
theorem supported_type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  cases hs with
  | boolean b =>
      exact typeof_value_model_eval_boolean M b
  | numeral n =>
      exact typeof_value_model_eval_numeral M n
  | rational q =>
      exact typeof_value_model_eval_rational M q
  | string s =>
      exact typeof_value_model_eval_string M s
  | binary w n =>
      exact typeof_value_model_eval_binary M w n ht
  | var s T hT =>
      exact typeof_value_model_eval_var M hM s T hT
  | uconst s T hT =>
      exact typeof_value_model_eval_uconst M hM s T hT
  | ite htc hsc ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_ite M _ _ _ ht
        (supported_type_preservation M hM _ htc hsc)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «exists» s T body =>
      exact typeof_value_model_eval_exists M s T body ht
  | «forall» s T body =>
      exact typeof_value_model_eval_forall M s T body ht
  | choice s T body =>
      exact typeof_value_model_eval_choice M s T body ht
  | «not» ht1 hs1 =>
      exact typeof_value_model_eval_not M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | «or» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_or M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «and» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_and M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «imp» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_imp M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | eq t1 t2 =>
      exact typeof_value_model_eval_eq M t1 t2 ht
  | dt_cons s d i =>
      exact typeof_value_model_eval_dt_cons M s d i
  | dt_sel ht1 hT htx hsx =>
      exact typeof_value_model_eval_dt_sel M hM _ _ _ _ _ ht1 hT
        (supported_type_preservation M hM _ htx hsx)
  | dt_tester s d i x =>
      exact typeof_value_model_eval_dt_tester M s d i x ht
  | @apply f x hTy hEval htf hsf htx hsx =>
      have hTy' :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTy']
        exact hNone
      rw [hEval M, hTy']
      exact typeof_value_model_eval_apply_generic M f x hNN
        (supported_type_preservation M hM f htf hsf)
        (supported_type_preservation M hM x htx hsx)

/-- Restates supported type preservation using an inhabited-type hypothesis. -/
theorem supported_type_preservation_of_inhabited_type
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hti : term_has_inhabited_type t)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t :=
  supported_type_preservation M hM t ht hs

/-- Shows that total typed SMT models exist. -/
theorem total_typed_model_nonvacuous :
    ∃ M : SmtModel, model_total_typed M :=
  exists_total_typed_model

end Smtm
