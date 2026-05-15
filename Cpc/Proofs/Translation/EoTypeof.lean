import Cpc.Proofs.Translation.EoTypeofCore
import Cpc.Proofs.Translation.Full

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/--
Recovers the EO translated type from an SMT typing equality.

The induction proving the translation typing theorem lives in `Full`, after the
application cases have access to the bridge-free helpers from `EoTypeofCore`.
-/
theorem eo_to_smt_type_typeof_of_smt_type
    (t : Term) {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof t) = T := by
  exact eo_to_smt_type_typeof_of_smt_type_from_full t h hT

end TranslationProofs
