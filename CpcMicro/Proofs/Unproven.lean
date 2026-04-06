import CpcMicro.Spec

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = T ->
  __smtx_typeof s = __eo_to_smt_type T := by
  sorry

end RuleProofs
