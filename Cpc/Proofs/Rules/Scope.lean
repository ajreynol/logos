import Cpc.Proofs.Rules.Support

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem cmd_step_pop_scope_properties
    (x1 : Term) (s : CState) (args : CArgList) (premises : CIndexList) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof x1 = Term.Bool ->
  AllHaveSmtTranslation (premiseTermList s premises) ->
  AllTypeofBool (premiseTermList s premises) ->
  __eo_cmd_step_pop_proven s CRule.scope args x1 premises ≠ Term.Stuck ->
  StepPopRuleProperties x1 (premiseTermList s premises)
    (__eo_cmd_step_pop_proven s CRule.scope args x1 premises) :=
by
  sorry
