import Cpc.Proofs.Support

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem cmd_step_re_range_non_singleton_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_range_non_singleton_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_range_non_singleton_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_range_non_singleton_2 args premises) :=
by
  sorry
