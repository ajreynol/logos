import CpcMini.Spec
import CpcMini.Proofs.SmtModelLemmas
import CpcMini.Proofs.TypePreservation

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem smt_model_eval_preserves_type
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (T : SmtType) :
  __smtx_typeof t = T ->
  smt_type_inhabited T ->
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  sorry

theorem smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
  __smtx_typeof t = SmtType.Bool ->
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  sorry

theorem smt_model_eval_preserves_type_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (T : SmtType)
    (hTy : __smtx_typeof t = T)
    (hNonNone : T ≠ SmtType.None)
    (hInh : smt_type_inhabited T)
    (hs : supported_preservation_term t) :
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact hNonNone
  have hTermInh : term_has_inhabited_type t := by
    unfold term_has_inhabited_type type_inhabited
    rw [hTy]
    simpa [smt_type_inhabited] using hInh
  simpa [hTy] using
    supported_type_preservation_of_inhabited_type M hM t hNN hTermInh hs

theorem smt_model_eval_bool_is_boolean_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool)
    (hs : supported_preservation_term t) :
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool :=
    smt_model_eval_preserves_type_of_supported M hM t SmtType.Bool hTy (by simp)
      smt_type_inhabited_bool hs
  exact bool_value_canonical hPres

namespace RuleProofs

theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = T ->
  __smtx_typeof s = __eo_to_smt_type T := by
  sorry

end RuleProofs
