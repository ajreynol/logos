import Cpc.Proofs.Support

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem cmd_step_ite_not_cond_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_not_cond args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.ite_not_cond args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_not_cond args premises) :=
by
  sorry
