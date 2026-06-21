import Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- The previous property theorem for `str_overlap_endpoints_replace` was
   removed. The generated endpoint rule is false under the current string
   utility semantics; the endpoint block can still affect the replacement even
   when the one-sided overlap guard passes. -/
