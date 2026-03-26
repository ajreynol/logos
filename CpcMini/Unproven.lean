import CpcMini.Spec
import CpcMini.SmtModelLemmas

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem smt_model_eval_preserves_type
    (M : SmtModel) (hM : smt_model_well_typed M)
    (t : SmtTerm) (T : SmtType) :
  __smtx_typeof t = T ->
  smt_type_inhabited T ->
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  sorry

theorem smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : smt_model_well_typed M)
    (t : SmtTerm) :
  __smtx_typeof t = SmtType.Bool ->
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  sorry

namespace RuleProofs

theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  s ≠ SmtTerm.None ->
  __eo_typeof t = Term.Bool ->
  __smtx_typeof s = SmtType.Bool := by
  sorry

end RuleProofs
