import CpcMicro.Proofs.Translation.Base

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/- Datatype-specific SMT translation helpers were removed from `CpcMicro.Spec`. -/

end TranslationProofs
