import Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- The previous property theorem for `str_overlap_endpoints_indexof` was
   removed. The generated endpoint rule is false under the current string
   utility semantics; the endpoint block can still determine the first
   occurrence even when the one-sided overlap guard passes. -/
