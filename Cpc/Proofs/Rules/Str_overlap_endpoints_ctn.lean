import Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- The previous property theorem for `str_overlap_endpoints_ctn` was removed.
   The generated endpoint rule is false under the current string utility
   semantics; in particular the one-sided endpoint overlap guard can pass while
   the endpoint block is still needed for the occurrence. -/
