import Cpc.Proofs.Rules.Support

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem cmd_step_and_intro_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.and_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.and_intro args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.and_intro args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.and_intro args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      refine ⟨?_, ?_⟩
      · intro hTrue
        change eo_interprets M (__eo_mk_premise_list Term.and premises s) true
        rw [mk_premise_list_and_eq_premiseAndFormulaList]
        exact premiseAndFormulaList_true_of_all_true M
          (premiseTermList s premises) hTrue
      · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
          (by
            change RuleProofs.eo_has_bool_type (__eo_mk_premise_list Term.and premises s)
            rw [mk_premise_list_and_eq_premiseAndFormulaList]
            exact premiseAndFormulaList_has_bool_type
              (premiseTermList s premises) hPremisesBool)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
