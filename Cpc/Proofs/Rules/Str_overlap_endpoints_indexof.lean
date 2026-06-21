import Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- The generated endpoint rule is false under the current string utility
   semantics: the endpoint block can still determine the first occurrence even
   when the one-sided overlap guard passes. Keep the theorem exported for
   downstream rule tables until the source rule/guard is repaired. -/
theorem cmd_step_str_overlap_endpoints_indexof_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_endpoints_indexof args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_overlap_endpoints_indexof args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_endpoints_indexof args premises) :=
by
  sorry
