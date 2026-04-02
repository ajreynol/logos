import Cpc.Proofs.Rules.Support

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem cmd_step_modus_ponens_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.modus_ponens args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.modus_ponens args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.modus_ponens args premises) :=
by
  sorry
