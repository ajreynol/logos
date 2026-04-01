import Cpc.Proofs.Rules.Support

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

open RuleProofs

theorem cmd_step_pop_scope_properties
    (x1 : Term) (s : CState) (args : CArgList) (premises : CIndexList) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_typeof x1 = Term.Bool ->
  AllHaveSmtTranslation (premiseTermList s premises) ->
  AllTypeofBool (premiseTermList s premises) ->
  __eo_cmd_step_pop_proven s CRule.scope args x1 premises ≠ Term.Stuck ->
  StepPopRuleProperties x1 (premiseTermList s premises)
    (__eo_cmd_step_pop_proven s CRule.scope args x1 premises) := by
  sorry

theorem cmd_step_process_scope_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.process_scope args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.process_scope args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.process_scope args premises) := by
  sorry

theorem cmd_step_ite_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_eq args premises) := by
  sorry

theorem cmd_step_split_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.split args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.split args premises) := by
  sorry

theorem cmd_step_resolution_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.resolution args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.resolution args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.resolution args premises) := by
  sorry

theorem cmd_step_chain_resolution_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.chain_resolution args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.chain_resolution args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.chain_resolution args premises) := by
  sorry

theorem cmd_step_chain_m_resolution_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.chain_m_resolution args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.chain_m_resolution args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.chain_m_resolution args premises) := by
  sorry

theorem cmd_step_factoring_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.factoring args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.factoring args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.factoring args premises) := by
  sorry

theorem cmd_step_reordering_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.reordering args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.reordering args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.reordering args premises) := by
  sorry

theorem cmd_step_eq_resolve_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_resolve args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.eq_resolve args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_resolve args premises) := by
  sorry

theorem cmd_step_modus_ponens_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.modus_ponens args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.modus_ponens args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.modus_ponens args premises) := by
  sorry

theorem cmd_step_not_not_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_not_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_not_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_not_elim args premises) := by
  sorry

theorem cmd_step_contra_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.contra args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.contra args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.contra args premises) := by
  sorry

theorem cmd_step_and_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.and_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.and_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.and_elim args premises) := by
  sorry

theorem cmd_step_and_intro_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.and_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.and_intro args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.and_intro args premises) := by
  sorry

theorem cmd_step_not_or_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_or_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_or_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_or_elim args premises) := by
  sorry

theorem cmd_step_implies_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.implies_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.implies_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.implies_elim args premises) := by
  sorry

theorem cmd_step_not_implies_elim1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_implies_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_implies_elim1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_implies_elim1 args premises) := by
  sorry

theorem cmd_step_not_implies_elim2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_implies_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_implies_elim2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_implies_elim2 args premises) := by
  sorry

theorem cmd_step_equiv_elim1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.equiv_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.equiv_elim1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.equiv_elim1 args premises) := by
  sorry

theorem cmd_step_equiv_elim2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.equiv_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.equiv_elim2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.equiv_elim2 args premises) := by
  sorry

theorem cmd_step_not_equiv_elim1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_equiv_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_equiv_elim1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_equiv_elim1 args premises) := by
  sorry

theorem cmd_step_not_equiv_elim2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_equiv_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_equiv_elim2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_equiv_elim2 args premises) := by
  sorry

theorem cmd_step_xor_elim1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.xor_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.xor_elim1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.xor_elim1 args premises) := by
  sorry

theorem cmd_step_xor_elim2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.xor_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.xor_elim2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.xor_elim2 args premises) := by
  sorry

theorem cmd_step_not_xor_elim1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_xor_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_xor_elim1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_xor_elim1 args premises) := by
  sorry

theorem cmd_step_not_xor_elim2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_xor_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_xor_elim2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_xor_elim2 args premises) := by
  sorry

theorem cmd_step_ite_elim1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_elim1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_elim1 args premises) := by
  sorry

theorem cmd_step_ite_elim2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_elim2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_elim2 args premises) := by
  sorry

theorem cmd_step_not_ite_elim1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_ite_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_ite_elim1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_ite_elim1 args premises) := by
  sorry

theorem cmd_step_not_ite_elim2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_ite_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_ite_elim2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_ite_elim2 args premises) := by
  sorry

theorem cmd_step_not_and_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.not_and args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.not_and args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.not_and args premises) := by
  sorry

theorem cmd_step_cnf_and_pos_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_and_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_and_pos args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_and_pos args premises) := by
  sorry

theorem cmd_step_cnf_and_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_and_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_and_neg args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_and_neg args premises) := by
  sorry

theorem cmd_step_cnf_or_pos_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_or_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_or_pos args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_or_pos args premises) := by
  sorry

theorem cmd_step_cnf_or_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_or_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_or_neg args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_or_neg args premises) := by
  sorry

theorem cmd_step_cnf_implies_pos_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_implies_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_implies_pos args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_implies_pos args premises) := by
  sorry

theorem cmd_step_cnf_implies_neg1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_implies_neg1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_implies_neg1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_implies_neg1 args premises) := by
  sorry

theorem cmd_step_cnf_implies_neg2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_implies_neg2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_implies_neg2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_implies_neg2 args premises) := by
  sorry

theorem cmd_step_cnf_equiv_pos1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_equiv_pos1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_equiv_pos1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_equiv_pos1 args premises) := by
  sorry

theorem cmd_step_cnf_equiv_pos2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_equiv_pos2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_equiv_pos2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_equiv_pos2 args premises) := by
  sorry

theorem cmd_step_cnf_equiv_neg1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_equiv_neg1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_equiv_neg1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_equiv_neg1 args premises) := by
  sorry

theorem cmd_step_cnf_equiv_neg2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_equiv_neg2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_equiv_neg2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_equiv_neg2 args premises) := by
  sorry

theorem cmd_step_cnf_xor_pos1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_xor_pos1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_xor_pos1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_xor_pos1 args premises) := by
  sorry

theorem cmd_step_cnf_xor_pos2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_xor_pos2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_xor_pos2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_xor_pos2 args premises) := by
  sorry

theorem cmd_step_cnf_xor_neg1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_xor_neg1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_xor_neg1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_xor_neg1 args premises) := by
  sorry

theorem cmd_step_cnf_xor_neg2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_xor_neg2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_xor_neg2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_xor_neg2 args premises) := by
  sorry

theorem cmd_step_cnf_ite_pos1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_ite_pos1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_ite_pos1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_ite_pos1 args premises) := by
  sorry

theorem cmd_step_cnf_ite_pos2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_ite_pos2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_ite_pos2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_ite_pos2 args premises) := by
  sorry

theorem cmd_step_cnf_ite_pos3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_ite_pos3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_ite_pos3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_ite_pos3 args premises) := by
  sorry

theorem cmd_step_cnf_ite_neg1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_ite_neg1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_ite_neg1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_ite_neg1 args premises) := by
  sorry

theorem cmd_step_cnf_ite_neg2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_ite_neg2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_ite_neg2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_ite_neg2 args premises) := by
  sorry

theorem cmd_step_cnf_ite_neg3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cnf_ite_neg3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cnf_ite_neg3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cnf_ite_neg3 args premises) := by
  sorry

theorem cmd_step_arrays_read_over_write_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arrays_read_over_write args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arrays_read_over_write args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arrays_read_over_write args premises) := by
  sorry

theorem cmd_step_arrays_read_over_write_contra_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arrays_read_over_write_contra args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arrays_read_over_write_contra args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arrays_read_over_write_contra args premises) := by
  sorry

theorem cmd_step_arrays_read_over_write_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arrays_read_over_write_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arrays_read_over_write_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arrays_read_over_write_1 args premises) := by
  sorry

theorem cmd_step_arrays_ext_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arrays_ext args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arrays_ext args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arrays_ext args premises) := by
  sorry

theorem cmd_step_refl_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.refl args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.refl args premises) := by
  sorry

theorem cmd_step_symm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.symm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.symm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.symm args premises) := by
  sorry

theorem cmd_step_trans_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.trans args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.trans args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.trans args premises) := by
  sorry

theorem cmd_step_cong_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.cong args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.cong args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.cong args premises) := by
  sorry

theorem cmd_step_nary_cong_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.nary_cong args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.nary_cong args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.nary_cong args premises) := by
  sorry

theorem cmd_step_pairwise_cong_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.pairwise_cong args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.pairwise_cong args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.pairwise_cong args premises) := by
  sorry

theorem cmd_step_true_intro_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.true_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.true_intro args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.true_intro args premises) := by
  sorry

theorem cmd_step_true_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.true_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.true_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.true_elim args premises) := by
  sorry

theorem cmd_step_false_intro_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.false_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.false_intro args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.false_intro args premises) := by
  sorry

theorem cmd_step_false_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.false_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.false_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.false_elim args premises) := by
  sorry

theorem cmd_step_ho_cong_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ho_cong args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ho_cong args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ho_cong args premises) := by
  sorry

theorem cmd_step_distinct_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.distinct_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_elim args premises) := by
  sorry

theorem cmd_step_distinct_true_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_true args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.distinct_true args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_true args premises) := by
  sorry

theorem cmd_step_distinct_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.distinct_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_false args premises) := by
  sorry

theorem cmd_step_arith_sum_ub_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_sum_ub args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_sum_ub args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_sum_ub args premises) := by
  sorry

theorem cmd_step_arith_mult_pos_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mult_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_mult_pos args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mult_pos args premises) := by
  sorry

theorem cmd_step_arith_mult_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mult_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_mult_neg args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mult_neg args premises) := by
  sorry

theorem cmd_step_arith_trichotomy_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_trichotomy args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_trichotomy args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_trichotomy args premises) := by
  sorry

theorem cmd_step_int_tight_ub_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.int_tight_ub args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.int_tight_ub args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.int_tight_ub args premises) := by
  sorry

theorem cmd_step_int_tight_lb_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.int_tight_lb args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.int_tight_lb args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.int_tight_lb args premises) := by
  sorry

theorem cmd_step_arith_mult_tangent_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mult_tangent args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_mult_tangent args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mult_tangent args premises) := by
  sorry

theorem cmd_step_arith_mult_sign_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mult_sign args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_mult_sign args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mult_sign args premises) := by
  sorry

theorem cmd_step_arith_mult_abs_comparison_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mult_abs_comparison args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_mult_abs_comparison args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mult_abs_comparison args premises) := by
  sorry

theorem cmd_step_arith_reduction_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_reduction args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_reduction args premises) := by
  sorry

theorem cmd_step_arith_poly_norm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_poly_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_poly_norm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_poly_norm args premises) := by
  sorry

theorem cmd_step_arith_poly_norm_rel_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_poly_norm_rel args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_poly_norm_rel args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_poly_norm_rel args premises) := by
  sorry

theorem cmd_step_bv_repeat_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_repeat_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_repeat_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_repeat_elim args premises) := by
  sorry

theorem cmd_step_bv_smulo_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_smulo_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_smulo_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_smulo_elim args premises) := by
  sorry

theorem cmd_step_bv_umulo_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_umulo_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_umulo_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_umulo_elim args premises) := by
  sorry

theorem cmd_step_bv_bitwise_slicing_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_bitwise_slicing args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_bitwise_slicing args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_bitwise_slicing args premises) := by
  sorry

theorem cmd_step_bv_bitblast_step_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_bitblast_step args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_bitblast_step args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_bitblast_step args premises) := by
  sorry

theorem cmd_step_bv_poly_norm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_poly_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_poly_norm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_poly_norm args premises) := by
  sorry

theorem cmd_step_bv_poly_norm_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_poly_norm_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_poly_norm_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_poly_norm_eq args premises) := by
  sorry

theorem cmd_step_string_length_pos_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_length_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.string_length_pos args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_length_pos args premises) := by
  sorry

theorem cmd_step_string_length_non_empty_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_length_non_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.string_length_non_empty args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_length_non_empty args premises) := by
  sorry

theorem cmd_step_concat_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.concat_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_eq args premises) := by
  sorry

theorem cmd_step_concat_unify_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_unify args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.concat_unify args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_unify args premises) := by
  sorry

theorem cmd_step_concat_csplit_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_csplit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.concat_csplit args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_csplit args premises) := by
  sorry

theorem cmd_step_concat_split_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.concat_split args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_split args premises) := by
  sorry

theorem cmd_step_concat_lprop_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_lprop args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.concat_lprop args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_lprop args premises) := by
  sorry

theorem cmd_step_concat_cprop_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_cprop args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.concat_cprop args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_cprop args premises) := by
  sorry

theorem cmd_step_string_decompose_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_decompose args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.string_decompose args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_decompose args premises) := by
  sorry

theorem cmd_step_exists_string_length_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.exists_string_length args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.exists_string_length args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.exists_string_length args premises) := by
  sorry

theorem cmd_step_string_code_inj_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_code_inj args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.string_code_inj args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_code_inj args premises) := by
  sorry

theorem cmd_step_string_seq_unit_inj_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_seq_unit_inj args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.string_seq_unit_inj args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_seq_unit_inj args premises) := by
  sorry

theorem cmd_step_re_inter_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_inter args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter args premises) := by
  sorry

theorem cmd_step_re_concat_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_concat args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat args premises) := by
  sorry

theorem cmd_step_re_unfold_pos_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_unfold_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_unfold_pos args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_unfold_pos args premises) := by
  sorry

theorem cmd_step_re_unfold_neg_concat_fixed_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_unfold_neg_concat_fixed args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_unfold_neg_concat_fixed args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_unfold_neg_concat_fixed args premises) := by
  sorry

theorem cmd_step_re_unfold_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_unfold_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_unfold_neg args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_unfold_neg args premises) := by
  sorry

theorem cmd_step_string_ext_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_ext args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.string_ext args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_ext args premises) := by
  sorry

theorem cmd_step_string_reduction_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.string_reduction args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_reduction args premises) := by
  sorry

theorem cmd_step_string_eager_reduction_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_eager_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.string_eager_reduction args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_eager_reduction args premises) := by
  sorry

theorem cmd_step_arith_string_pred_entail_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_string_pred_entail args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_string_pred_entail args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_string_pred_entail args premises) := by
  sorry

theorem cmd_step_arith_string_pred_safe_approx_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_string_pred_safe_approx args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_string_pred_safe_approx args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_string_pred_safe_approx args premises) := by
  sorry

theorem cmd_step_str_in_re_eval_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_eval args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_eval args premises) := by
  sorry

theorem cmd_step_str_in_re_consume_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_consume args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_consume args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_consume args premises) := by
  sorry

theorem cmd_step_re_loop_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_loop_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_loop_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_loop_elim args premises) := by
  sorry

theorem cmd_step_re_eq_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_eq_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_eq_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_eq_elim args premises) := by
  sorry

theorem cmd_step_re_inter_inclusion_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter_inclusion args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_inter_inclusion args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter_inclusion args premises) := by
  sorry

theorem cmd_step_re_union_inclusion_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_union_inclusion args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_union_inclusion args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_union_inclusion args premises) := by
  sorry

theorem cmd_step_str_in_re_concat_star_char_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_concat_star_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_concat_star_char args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_concat_star_char args premises) := by
  sorry

theorem cmd_step_str_in_re_sigma_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_sigma args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_sigma args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_sigma args premises) := by
  sorry

theorem cmd_step_str_in_re_sigma_star_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_sigma_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_sigma_star args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_sigma_star args premises) := by
  sorry

theorem cmd_step_str_ctn_multiset_subset_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_ctn_multiset_subset args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_ctn_multiset_subset args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_ctn_multiset_subset args premises) := by
  sorry

theorem cmd_step_str_overlap_split_ctn_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_split_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_overlap_split_ctn args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_split_ctn args premises) := by
  sorry

theorem cmd_step_str_overlap_endpoints_ctn_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_endpoints_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises) := by
  sorry

theorem cmd_step_str_overlap_endpoints_indexof_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_endpoints_indexof args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_overlap_endpoints_indexof args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_endpoints_indexof args premises) := by
  sorry

theorem cmd_step_str_overlap_endpoints_replace_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_endpoints_replace args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_overlap_endpoints_replace args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_endpoints_replace args premises) := by
  sorry

theorem cmd_step_str_indexof_re_eval_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_re_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_re_eval args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_re_eval args premises) := by
  sorry

theorem cmd_step_str_replace_re_eval_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_re_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_re_eval args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_re_eval args premises) := by
  sorry

theorem cmd_step_str_replace_re_all_eval_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_re_all_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_re_all_eval args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_re_all_eval args premises) := by
  sorry

theorem cmd_step_seq_eval_op_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_eval_op args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.seq_eval_op args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_eval_op args premises) := by
  sorry

theorem cmd_step_sets_singleton_inj_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_singleton_inj args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_singleton_inj args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_singleton_inj args premises) := by
  sorry

theorem cmd_step_sets_ext_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_ext args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_ext args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_ext args premises) := by
  sorry

theorem cmd_step_sets_eval_op_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_eval_op args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_eval_op args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_eval_op args premises) := by
  sorry

theorem cmd_step_sets_insert_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_insert_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_insert_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_insert_elim args premises) := by
  sorry

theorem cmd_step_ubv_to_int_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ubv_to_int_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ubv_to_int_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ubv_to_int_elim args premises) := by
  sorry

theorem cmd_step_int_to_bv_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.int_to_bv_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.int_to_bv_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.int_to_bv_elim args premises) := by
  sorry

theorem cmd_step_instantiate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.instantiate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.instantiate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.instantiate args premises) := by
  sorry

theorem cmd_step_skolemize_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.skolemize args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.skolemize args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.skolemize args premises) := by
  sorry

theorem cmd_step_skolem_intro_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.skolem_intro args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.skolem_intro args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.skolem_intro args premises) := by
  sorry

theorem cmd_step_alpha_equiv_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.alpha_equiv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.alpha_equiv args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.alpha_equiv args premises) := by
  sorry

theorem cmd_step_beta_reduce_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.beta_reduce args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.beta_reduce args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.beta_reduce args premises) := by
  sorry

theorem cmd_step_quant_var_reordering_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_var_reordering args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.quant_var_reordering args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_var_reordering args premises) := by
  sorry

theorem cmd_step_exists_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.exists_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.exists_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.exists_elim args premises) := by
  sorry

theorem cmd_step_quant_unused_vars_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_unused_vars args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_unused_vars args premises) := by
  sorry

theorem cmd_step_quant_merge_prenex_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_merge_prenex args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.quant_merge_prenex args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_merge_prenex args premises) := by
  sorry

theorem cmd_step_quant_miniscope_and_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_miniscope_and args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.quant_miniscope_and args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_miniscope_and args premises) := by
  sorry

theorem cmd_step_quant_miniscope_or_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_miniscope_or args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.quant_miniscope_or args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_miniscope_or args premises) := by
  sorry

theorem cmd_step_quant_miniscope_ite_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_miniscope_ite args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.quant_miniscope_ite args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_miniscope_ite args premises) := by
  sorry

theorem cmd_step_quant_var_elim_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_var_elim_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.quant_var_elim_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_var_elim_eq args premises) := by
  sorry

theorem cmd_step_quant_dt_split_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_dt_split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.quant_dt_split args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_dt_split args premises) := by
  sorry

theorem cmd_step_dt_split_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_split args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_split args premises) := by
  sorry

theorem cmd_step_dt_inst_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_inst args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_inst args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_inst args premises) := by
  sorry

theorem cmd_step_dt_collapse_selector_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_collapse_selector args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_collapse_selector args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_collapse_selector args premises) := by
  sorry

theorem cmd_step_dt_collapse_tester_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_collapse_tester args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_collapse_tester args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_collapse_tester args premises) := by
  sorry

theorem cmd_step_dt_collapse_tester_singleton_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_collapse_tester_singleton args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_collapse_tester_singleton args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_collapse_tester_singleton args premises) := by
  sorry

theorem cmd_step_dt_cons_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_cons_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_cons_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_cons_eq args premises) := by
  sorry

theorem cmd_step_dt_cons_eq_clash_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_cons_eq_clash args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_cons_eq_clash args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_cons_eq_clash args premises) := by
  sorry

theorem cmd_step_dt_cycle_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_cycle args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_cycle args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_cycle args premises) := by
  sorry

theorem cmd_step_dt_collapse_updater_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_collapse_updater args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_collapse_updater args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_collapse_updater args premises) := by
  sorry

theorem cmd_step_dt_updater_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_updater_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.dt_updater_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_updater_elim args premises) := by
  sorry

theorem cmd_step_arith_div_total_zero_real_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_div_total_zero_real args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_div_total_zero_real args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_div_total_zero_real args premises) := by
  sorry

theorem cmd_step_arith_div_total_zero_int_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_div_total_zero_int args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_div_total_zero_int args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_div_total_zero_int args premises) := by
  sorry

theorem cmd_step_arith_int_div_total_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_div_total args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_div_total args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_div_total args premises) := by
  sorry

theorem cmd_step_arith_int_div_total_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_div_total_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_div_total_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_div_total_one args premises) := by
  sorry

theorem cmd_step_arith_int_div_total_zero_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_div_total_zero args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_div_total_zero args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_div_total_zero args premises) := by
  sorry

theorem cmd_step_arith_int_div_total_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_div_total_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_div_total_neg args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_div_total_neg args premises) := by
  sorry

theorem cmd_step_arith_int_mod_total_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_mod_total args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_mod_total args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_mod_total args premises) := by
  sorry

theorem cmd_step_arith_int_mod_total_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_mod_total_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_mod_total_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_mod_total_one args premises) := by
  sorry

theorem cmd_step_arith_int_mod_total_zero_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_mod_total_zero args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_mod_total_zero args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_mod_total_zero args premises) := by
  sorry

theorem cmd_step_arith_int_mod_total_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_mod_total_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_mod_total_neg args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_mod_total_neg args premises) := by
  sorry

theorem cmd_step_arith_elim_gt_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_elim_gt args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_elim_gt args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_elim_gt args premises) := by
  sorry

theorem cmd_step_arith_elim_lt_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_elim_lt args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_elim_lt args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_elim_lt args premises) := by
  sorry

theorem cmd_step_arith_elim_int_gt_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_elim_int_gt args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_elim_int_gt args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_elim_int_gt args premises) := by
  sorry

theorem cmd_step_arith_elim_int_lt_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_elim_int_lt args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_elim_int_lt args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_elim_int_lt args premises) := by
  sorry

theorem cmd_step_arith_elim_leq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_elim_leq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_elim_leq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_elim_leq args premises) := by
  sorry

theorem cmd_step_arith_leq_norm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_leq_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_leq_norm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_leq_norm args premises) := by
  sorry

theorem cmd_step_arith_geq_tighten_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_geq_tighten args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_geq_tighten args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_geq_tighten args premises) := by
  sorry

theorem cmd_step_arith_geq_norm1_int_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_geq_norm1_int args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_geq_norm1_int args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_geq_norm1_int args premises) := by
  sorry

theorem cmd_step_arith_geq_norm1_real_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_geq_norm1_real args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_geq_norm1_real args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_geq_norm1_real args premises) := by
  sorry

theorem cmd_step_arith_eq_elim_real_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_eq_elim_real args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_eq_elim_real args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_eq_elim_real args premises) := by
  sorry

theorem cmd_step_arith_eq_elim_int_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_eq_elim_int args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_eq_elim_int args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_eq_elim_int args premises) := by
  sorry

theorem cmd_step_arith_to_int_elim_to_real_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_to_int_elim_to_real args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_to_int_elim_to_real args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_to_int_elim_to_real args premises) := by
  sorry

theorem cmd_step_arith_mod_over_mod_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mod_over_mod_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_mod_over_mod_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mod_over_mod_1 args premises) := by
  sorry

theorem cmd_step_arith_mod_over_mod_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mod_over_mod args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_mod_over_mod args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mod_over_mod args premises) := by
  sorry

theorem cmd_step_arith_mod_over_mod_mult_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mod_over_mod_mult args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_mod_over_mod_mult args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mod_over_mod_mult args premises) := by
  sorry

theorem cmd_step_arith_int_eq_conflict_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_eq_conflict args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_eq_conflict args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_eq_conflict args premises) := by
  sorry

theorem cmd_step_arith_int_geq_tighten_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_geq_tighten args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_geq_tighten args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_geq_tighten args premises) := by
  sorry

theorem cmd_step_arith_divisible_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_divisible_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_divisible_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_divisible_elim args premises) := by
  sorry

theorem cmd_step_arith_abs_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_abs_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_abs_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_abs_eq args premises) := by
  sorry

theorem cmd_step_arith_abs_int_gt_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_abs_int_gt args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_abs_int_gt args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_abs_int_gt args premises) := by
  sorry

theorem cmd_step_arith_abs_real_gt_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_abs_real_gt args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_abs_real_gt args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_abs_real_gt args premises) := by
  sorry

theorem cmd_step_arith_geq_ite_lift_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_geq_ite_lift args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_geq_ite_lift args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_geq_ite_lift args premises) := by
  sorry

theorem cmd_step_arith_leq_ite_lift_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_leq_ite_lift args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_leq_ite_lift args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_leq_ite_lift args premises) := by
  sorry

theorem cmd_step_arith_min_lt1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_min_lt1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_min_lt1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_min_lt1 args premises) := by
  sorry

theorem cmd_step_arith_min_lt2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_min_lt2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_min_lt2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_min_lt2 args premises) := by
  sorry

theorem cmd_step_arith_max_geq1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_max_geq1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_max_geq1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_max_geq1 args premises) := by
  sorry

theorem cmd_step_arith_max_geq2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_max_geq2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_max_geq2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_max_geq2 args premises) := by
  sorry

theorem cmd_step_array_read_over_write_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_read_over_write args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.array_read_over_write args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_read_over_write args premises) := by
  sorry

theorem cmd_step_array_read_over_write2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_read_over_write2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.array_read_over_write2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_read_over_write2 args premises) := by
  sorry

theorem cmd_step_array_store_overwrite_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_store_overwrite args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.array_store_overwrite args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_store_overwrite args premises) := by
  sorry

theorem cmd_step_array_store_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_store_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.array_store_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_store_self args premises) := by
  sorry

theorem cmd_step_array_read_over_write_split_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_read_over_write_split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.array_read_over_write_split args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_read_over_write_split args premises) := by
  sorry

theorem cmd_step_array_store_swap_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_store_swap args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.array_store_swap args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_store_swap args premises) := by
  sorry

theorem cmd_step_bool_double_not_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_double_not_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_double_not_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_double_not_elim args premises) := by
  sorry

theorem cmd_step_bool_not_true_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_not_true args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_not_true args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_not_true args premises) := by
  sorry

theorem cmd_step_bool_not_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_not_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_not_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_not_false args premises) := by
  sorry

theorem cmd_step_bool_eq_true_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_eq_true args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_eq_true args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_eq_true args premises) := by
  sorry

theorem cmd_step_bool_eq_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_eq_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_eq_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_eq_false args premises) := by
  sorry

theorem cmd_step_bool_eq_nrefl_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_eq_nrefl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_eq_nrefl args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_eq_nrefl args premises) := by
  sorry

theorem cmd_step_bool_impl_false1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_impl_false1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_impl_false1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_impl_false1 args premises) := by
  sorry

theorem cmd_step_bool_impl_false2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_impl_false2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_impl_false2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_impl_false2 args premises) := by
  sorry

theorem cmd_step_bool_impl_true1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_impl_true1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_impl_true1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_impl_true1 args premises) := by
  sorry

theorem cmd_step_bool_impl_true2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_impl_true2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_impl_true2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_impl_true2 args premises) := by
  sorry

theorem cmd_step_bool_impl_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_impl_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_impl_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_impl_elim args premises) := by
  sorry

theorem cmd_step_bool_dual_impl_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_dual_impl_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_dual_impl_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_dual_impl_eq args premises) := by
  sorry

theorem cmd_step_bool_and_conf_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_and_conf args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_and_conf args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_and_conf args premises) := by
  sorry

theorem cmd_step_bool_and_conf2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_and_conf2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_and_conf2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_and_conf2 args premises) := by
  sorry

theorem cmd_step_bool_or_taut_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_or_taut args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_or_taut args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_or_taut args premises) := by
  sorry

theorem cmd_step_bool_or_taut2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_or_taut2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_or_taut2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_or_taut2 args premises) := by
  sorry

theorem cmd_step_bool_or_de_morgan_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_or_de_morgan args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_or_de_morgan args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_or_de_morgan args premises) := by
  sorry

theorem cmd_step_bool_implies_de_morgan_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_implies_de_morgan args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_implies_de_morgan args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_implies_de_morgan args premises) := by
  sorry

theorem cmd_step_bool_and_de_morgan_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_and_de_morgan args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_and_de_morgan args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_and_de_morgan args premises) := by
  sorry

theorem cmd_step_bool_or_and_distrib_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_or_and_distrib args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_or_and_distrib args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_or_and_distrib args premises) := by
  sorry

theorem cmd_step_bool_implies_or_distrib_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_implies_or_distrib args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_implies_or_distrib args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_implies_or_distrib args premises) := by
  sorry

theorem cmd_step_bool_xor_refl_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_xor_refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_xor_refl args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_xor_refl args premises) := by
  sorry

theorem cmd_step_bool_xor_nrefl_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_xor_nrefl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_xor_nrefl args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_xor_nrefl args premises) := by
  sorry

theorem cmd_step_bool_xor_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_xor_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_xor_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_xor_false args premises) := by
  sorry

theorem cmd_step_bool_xor_true_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_xor_true args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_xor_true args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_xor_true args premises) := by
  sorry

theorem cmd_step_bool_xor_comm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_xor_comm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_xor_comm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_xor_comm args premises) := by
  sorry

theorem cmd_step_bool_xor_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_xor_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_xor_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_xor_elim args premises) := by
  sorry

theorem cmd_step_bool_not_xor_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_not_xor_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_not_xor_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_not_xor_elim args premises) := by
  sorry

theorem cmd_step_bool_not_eq_elim1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_not_eq_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_not_eq_elim1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_not_eq_elim1 args premises) := by
  sorry

theorem cmd_step_bool_not_eq_elim2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_not_eq_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_not_eq_elim2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_not_eq_elim2 args premises) := by
  sorry

theorem cmd_step_ite_neg_branch_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_neg_branch args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_neg_branch args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_neg_branch args premises) := by
  sorry

theorem cmd_step_ite_then_true_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_then_true args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_then_true args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_then_true args premises) := by
  sorry

theorem cmd_step_ite_else_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_else_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_else_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_else_false args premises) := by
  sorry

theorem cmd_step_ite_then_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_then_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_then_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_then_false args premises) := by
  sorry

theorem cmd_step_ite_else_true_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_else_true args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_else_true args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_else_true args premises) := by
  sorry

theorem cmd_step_ite_then_lookahead_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_then_lookahead_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_then_lookahead_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_then_lookahead_self args premises) := by
  sorry

theorem cmd_step_ite_else_lookahead_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_else_lookahead_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_else_lookahead_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_else_lookahead_self args premises) := by
  sorry

theorem cmd_step_ite_then_lookahead_not_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_then_lookahead_not_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_then_lookahead_not_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_then_lookahead_not_self args premises) := by
  sorry

theorem cmd_step_ite_else_lookahead_not_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_else_lookahead_not_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_else_lookahead_not_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_else_lookahead_not_self args premises) := by
  sorry

theorem cmd_step_ite_expand_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_expand args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_expand args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_expand args premises) := by
  sorry

theorem cmd_step_bool_not_ite_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bool_not_ite_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bool_not_ite_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bool_not_ite_elim args premises) := by
  sorry

theorem cmd_step_ite_true_cond_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_true_cond args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_true_cond args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_true_cond args premises) := by
  sorry

theorem cmd_step_ite_false_cond_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_false_cond args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_false_cond args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_false_cond args premises) := by
  sorry

theorem cmd_step_ite_not_cond_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_not_cond args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_not_cond args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_not_cond args premises) := by
  sorry

theorem cmd_step_ite_eq_branch_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_eq_branch args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_eq_branch args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_eq_branch args premises) := by
  sorry

theorem cmd_step_ite_then_lookahead_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_then_lookahead args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_then_lookahead args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_then_lookahead args premises) := by
  sorry

theorem cmd_step_ite_else_lookahead_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_else_lookahead args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_else_lookahead args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_else_lookahead args premises) := by
  sorry

theorem cmd_step_ite_then_neg_lookahead_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_then_neg_lookahead args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_then_neg_lookahead args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_then_neg_lookahead args premises) := by
  sorry

theorem cmd_step_ite_else_neg_lookahead_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.ite_else_neg_lookahead args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.ite_else_neg_lookahead args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.ite_else_neg_lookahead args premises) := by
  sorry

theorem cmd_step_bv_concat_extract_merge_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_concat_extract_merge args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_concat_extract_merge args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_concat_extract_merge args premises) := by
  sorry

theorem cmd_step_bv_extract_extract_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_extract args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_extract args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_extract args premises) := by
  sorry

theorem cmd_step_bv_extract_whole_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_whole args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_whole args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_whole args premises) := by
  sorry

theorem cmd_step_bv_extract_concat_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_concat_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_concat_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_concat_1 args premises) := by
  sorry

theorem cmd_step_bv_extract_concat_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_concat_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_concat_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_concat_2 args premises) := by
  sorry

theorem cmd_step_bv_extract_concat_3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_concat_3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_concat_3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_concat_3 args premises) := by
  sorry

theorem cmd_step_bv_extract_concat_4_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_concat_4 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_concat_4 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_concat_4 args premises) := by
  sorry

theorem cmd_step_bv_eq_extract_elim1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_eq_extract_elim1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_eq_extract_elim1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_eq_extract_elim1 args premises) := by
  sorry

theorem cmd_step_bv_eq_extract_elim2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_eq_extract_elim2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_eq_extract_elim2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_eq_extract_elim2 args premises) := by
  sorry

theorem cmd_step_bv_eq_extract_elim3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_eq_extract_elim3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_eq_extract_elim3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_eq_extract_elim3 args premises) := by
  sorry

theorem cmd_step_bv_extract_not_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_not args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_not args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_not args premises) := by
  sorry

theorem cmd_step_bv_extract_sign_extend_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_sign_extend_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_sign_extend_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_sign_extend_1 args premises) := by
  sorry

theorem cmd_step_bv_extract_sign_extend_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_sign_extend_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_sign_extend_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_sign_extend_2 args premises) := by
  sorry

theorem cmd_step_bv_extract_sign_extend_3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_sign_extend_3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_sign_extend_3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_sign_extend_3 args premises) := by
  sorry

theorem cmd_step_bv_not_xor_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_not_xor args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_not_xor args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_not_xor args premises) := by
  sorry

theorem cmd_step_bv_and_simplify_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_and_simplify_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_and_simplify_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_and_simplify_1 args premises) := by
  sorry

theorem cmd_step_bv_and_simplify_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_and_simplify_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_and_simplify_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_and_simplify_2 args premises) := by
  sorry

theorem cmd_step_bv_or_simplify_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_or_simplify_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_or_simplify_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_or_simplify_1 args premises) := by
  sorry

theorem cmd_step_bv_or_simplify_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_or_simplify_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_or_simplify_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_or_simplify_2 args premises) := by
  sorry

theorem cmd_step_bv_xor_simplify_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_simplify_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xor_simplify_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_simplify_1 args premises) := by
  sorry

theorem cmd_step_bv_xor_simplify_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_simplify_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xor_simplify_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_simplify_2 args premises) := by
  sorry

theorem cmd_step_bv_xor_simplify_3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_simplify_3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xor_simplify_3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_simplify_3 args premises) := by
  sorry

theorem cmd_step_bv_ult_add_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ult_add_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ult_add_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ult_add_one args premises) := by
  sorry

theorem cmd_step_bv_mult_slt_mult_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_mult_slt_mult_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_mult_slt_mult_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_mult_slt_mult_1 args premises) := by
  sorry

theorem cmd_step_bv_mult_slt_mult_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_mult_slt_mult_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_mult_slt_mult_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_mult_slt_mult_2 args premises) := by
  sorry

theorem cmd_step_bv_commutative_xor_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_commutative_xor args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_commutative_xor args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_commutative_xor args premises) := by
  sorry

theorem cmd_step_bv_commutative_comp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_commutative_comp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_commutative_comp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_commutative_comp args premises) := by
  sorry

theorem cmd_step_bv_zero_extend_eliminate_0_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_extend_eliminate_0 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_zero_extend_eliminate_0 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_extend_eliminate_0 args premises) := by
  sorry

theorem cmd_step_bv_sign_extend_eliminate_0_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sign_extend_eliminate_0 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sign_extend_eliminate_0 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sign_extend_eliminate_0 args premises) := by
  sorry

theorem cmd_step_bv_not_neq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_not_neq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_not_neq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_not_neq args premises) := by
  sorry

theorem cmd_step_bv_ult_ones_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ult_ones args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ult_ones args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ult_ones args premises) := by
  sorry

theorem cmd_step_bv_concat_merge_const_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_concat_merge_const args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_concat_merge_const args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_concat_merge_const args premises) := by
  sorry

theorem cmd_step_bv_commutative_add_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_commutative_add args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_commutative_add args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_commutative_add args premises) := by
  sorry

theorem cmd_step_bv_sub_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sub_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sub_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sub_eliminate args premises) := by
  sorry

theorem cmd_step_bv_ite_width_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_width_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_width_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_width_one args premises) := by
  sorry

theorem cmd_step_bv_ite_width_one_not_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_width_one_not args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_width_one_not args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_width_one_not args premises) := by
  sorry

theorem cmd_step_bv_eq_xor_solve_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_eq_xor_solve args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_eq_xor_solve args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_eq_xor_solve args premises) := by
  sorry

theorem cmd_step_bv_eq_not_solve_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_eq_not_solve args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_eq_not_solve args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_eq_not_solve args premises) := by
  sorry

theorem cmd_step_bv_ugt_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ugt_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ugt_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ugt_eliminate args premises) := by
  sorry

theorem cmd_step_bv_uge_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_uge_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_uge_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_uge_eliminate args premises) := by
  sorry

theorem cmd_step_bv_sgt_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sgt_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sgt_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sgt_eliminate args premises) := by
  sorry

theorem cmd_step_bv_sge_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sge_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sge_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sge_eliminate args premises) := by
  sorry

theorem cmd_step_bv_sle_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sle_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sle_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sle_eliminate args premises) := by
  sorry

theorem cmd_step_bv_redor_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_redor_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_redor_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_redor_eliminate args premises) := by
  sorry

theorem cmd_step_bv_redand_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_redand_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_redand_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_redand_eliminate args premises) := by
  sorry

theorem cmd_step_bv_ule_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ule_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ule_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ule_eliminate args premises) := by
  sorry

theorem cmd_step_bv_comp_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_comp_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_comp_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_comp_eliminate args premises) := by
  sorry

theorem cmd_step_bv_rotate_left_eliminate_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_rotate_left_eliminate_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_rotate_left_eliminate_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_rotate_left_eliminate_1 args premises) := by
  sorry

theorem cmd_step_bv_rotate_left_eliminate_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_rotate_left_eliminate_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_rotate_left_eliminate_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_rotate_left_eliminate_2 args premises) := by
  sorry

theorem cmd_step_bv_rotate_right_eliminate_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_rotate_right_eliminate_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_rotate_right_eliminate_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_rotate_right_eliminate_1 args premises) := by
  sorry

theorem cmd_step_bv_rotate_right_eliminate_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_rotate_right_eliminate_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_rotate_right_eliminate_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_rotate_right_eliminate_2 args premises) := by
  sorry

theorem cmd_step_bv_nand_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_nand_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_nand_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_nand_eliminate args premises) := by
  sorry

theorem cmd_step_bv_nor_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_nor_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_nor_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_nor_eliminate args premises) := by
  sorry

theorem cmd_step_bv_xnor_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xnor_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xnor_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xnor_eliminate args premises) := by
  sorry

theorem cmd_step_bv_sdiv_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sdiv_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sdiv_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sdiv_eliminate args premises) := by
  sorry

theorem cmd_step_bv_zero_extend_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_extend_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_zero_extend_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_extend_eliminate args premises) := by
  sorry

theorem cmd_step_bv_uaddo_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_uaddo_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_uaddo_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_uaddo_eliminate args premises) := by
  sorry

theorem cmd_step_bv_saddo_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_saddo_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_saddo_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_saddo_eliminate args premises) := by
  sorry

theorem cmd_step_bv_sdivo_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sdivo_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sdivo_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sdivo_eliminate args premises) := by
  sorry

theorem cmd_step_bv_smod_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_smod_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_smod_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_smod_eliminate args premises) := by
  sorry

theorem cmd_step_bv_srem_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_srem_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_srem_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_srem_eliminate args premises) := by
  sorry

theorem cmd_step_bv_usubo_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_usubo_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_usubo_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_usubo_eliminate args premises) := by
  sorry

theorem cmd_step_bv_ssubo_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ssubo_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ssubo_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ssubo_eliminate args premises) := by
  sorry

theorem cmd_step_bv_nego_eliminate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_nego_eliminate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_nego_eliminate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_nego_eliminate args premises) := by
  sorry

theorem cmd_step_bv_ite_equal_children_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_equal_children args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_equal_children args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_equal_children args premises) := by
  sorry

theorem cmd_step_bv_ite_const_children_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_const_children_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_const_children_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_const_children_1 args premises) := by
  sorry

theorem cmd_step_bv_ite_const_children_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_const_children_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_const_children_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_const_children_2 args premises) := by
  sorry

theorem cmd_step_bv_ite_equal_cond_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_equal_cond_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_equal_cond_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_equal_cond_1 args premises) := by
  sorry

theorem cmd_step_bv_ite_equal_cond_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_equal_cond_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_equal_cond_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_equal_cond_2 args premises) := by
  sorry

theorem cmd_step_bv_ite_equal_cond_3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_equal_cond_3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_equal_cond_3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_equal_cond_3 args premises) := by
  sorry

theorem cmd_step_bv_ite_merge_then_if_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_merge_then_if args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_merge_then_if args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_merge_then_if args premises) := by
  sorry

theorem cmd_step_bv_ite_merge_else_if_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_merge_else_if args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_merge_else_if args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_merge_else_if args premises) := by
  sorry

theorem cmd_step_bv_ite_merge_then_else_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_merge_then_else args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_merge_then_else args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_merge_then_else args premises) := by
  sorry

theorem cmd_step_bv_ite_merge_else_else_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ite_merge_else_else args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ite_merge_else_else args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ite_merge_else_else args premises) := by
  sorry

theorem cmd_step_bv_shl_by_const_0_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_shl_by_const_0 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_shl_by_const_0 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_shl_by_const_0 args premises) := by
  sorry

theorem cmd_step_bv_shl_by_const_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_shl_by_const_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_shl_by_const_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_shl_by_const_1 args premises) := by
  sorry

theorem cmd_step_bv_shl_by_const_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_shl_by_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_shl_by_const_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_shl_by_const_2 args premises) := by
  sorry

theorem cmd_step_bv_lshr_by_const_0_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_lshr_by_const_0 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_lshr_by_const_0 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_lshr_by_const_0 args premises) := by
  sorry

theorem cmd_step_bv_lshr_by_const_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_lshr_by_const_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_lshr_by_const_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_lshr_by_const_1 args premises) := by
  sorry

theorem cmd_step_bv_lshr_by_const_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_lshr_by_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_lshr_by_const_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_lshr_by_const_2 args premises) := by
  sorry

theorem cmd_step_bv_ashr_by_const_0_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ashr_by_const_0 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ashr_by_const_0 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ashr_by_const_0 args premises) := by
  sorry

theorem cmd_step_bv_ashr_by_const_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ashr_by_const_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ashr_by_const_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ashr_by_const_1 args premises) := by
  sorry

theorem cmd_step_bv_ashr_by_const_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ashr_by_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ashr_by_const_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ashr_by_const_2 args premises) := by
  sorry

theorem cmd_step_bv_and_concat_pullup_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_and_concat_pullup args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_and_concat_pullup args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_and_concat_pullup args premises) := by
  sorry

theorem cmd_step_bv_or_concat_pullup_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_or_concat_pullup args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_or_concat_pullup args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_or_concat_pullup args premises) := by
  sorry

theorem cmd_step_bv_xor_concat_pullup_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_concat_pullup args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xor_concat_pullup args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_concat_pullup args premises) := by
  sorry

theorem cmd_step_bv_and_concat_pullup2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_and_concat_pullup2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_and_concat_pullup2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_and_concat_pullup2 args premises) := by
  sorry

theorem cmd_step_bv_or_concat_pullup2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_or_concat_pullup2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_or_concat_pullup2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_or_concat_pullup2 args premises) := by
  sorry

theorem cmd_step_bv_xor_concat_pullup2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_concat_pullup2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xor_concat_pullup2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_concat_pullup2 args premises) := by
  sorry

theorem cmd_step_bv_and_concat_pullup3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_and_concat_pullup3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_and_concat_pullup3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_and_concat_pullup3 args premises) := by
  sorry

theorem cmd_step_bv_or_concat_pullup3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_or_concat_pullup3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_or_concat_pullup3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_or_concat_pullup3 args premises) := by
  sorry

theorem cmd_step_bv_xor_concat_pullup3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_concat_pullup3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xor_concat_pullup3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_concat_pullup3 args premises) := by
  sorry

theorem cmd_step_bv_xor_duplicate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_duplicate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xor_duplicate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_duplicate args premises) := by
  sorry

theorem cmd_step_bv_xor_ones_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_ones args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xor_ones args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_ones args premises) := by
  sorry

theorem cmd_step_bv_xor_not_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_not args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_xor_not args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_not args premises) := by
  sorry

theorem cmd_step_bv_not_idemp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_not_idemp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_not_idemp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_not_idemp args premises) := by
  sorry

theorem cmd_step_bv_ult_zero_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ult_zero_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ult_zero_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ult_zero_1 args premises) := by
  sorry

theorem cmd_step_bv_ult_zero_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ult_zero_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ult_zero_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ult_zero_2 args premises) := by
  sorry

theorem cmd_step_bv_ult_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ult_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ult_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ult_self args premises) := by
  sorry

theorem cmd_step_bv_lt_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_lt_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_lt_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_lt_self args premises) := by
  sorry

theorem cmd_step_bv_ule_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ule_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ule_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ule_self args premises) := by
  sorry

theorem cmd_step_bv_ule_zero_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ule_zero args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ule_zero args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ule_zero args premises) := by
  sorry

theorem cmd_step_bv_zero_ule_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_ule args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_zero_ule args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_ule args premises) := by
  sorry

theorem cmd_step_bv_sle_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sle_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sle_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sle_self args premises) := by
  sorry

theorem cmd_step_bv_ule_max_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ule_max args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ule_max args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ule_max args premises) := by
  sorry

theorem cmd_step_bv_not_ult_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_not_ult args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_not_ult args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_not_ult args premises) := by
  sorry

theorem cmd_step_bv_mult_pow2_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_mult_pow2_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_mult_pow2_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_mult_pow2_1 args premises) := by
  sorry

theorem cmd_step_bv_mult_pow2_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_mult_pow2_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_mult_pow2_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_mult_pow2_2 args premises) := by
  sorry

theorem cmd_step_bv_mult_pow2_2b_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_mult_pow2_2b args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_mult_pow2_2b args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_mult_pow2_2b args premises) := by
  sorry

theorem cmd_step_bv_extract_mult_leading_bit_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_mult_leading_bit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises) := by
  sorry

theorem cmd_step_bv_udiv_pow2_not_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_udiv_pow2_not_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_udiv_pow2_not_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_udiv_pow2_not_one args premises) := by
  sorry

theorem cmd_step_bv_udiv_zero_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_udiv_zero args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_udiv_zero args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_udiv_zero args premises) := by
  sorry

theorem cmd_step_bv_udiv_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_udiv_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_udiv_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_udiv_one args premises) := by
  sorry

theorem cmd_step_bv_urem_pow2_not_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_urem_pow2_not_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_urem_pow2_not_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_urem_pow2_not_one args premises) := by
  sorry

theorem cmd_step_bv_urem_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_urem_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_urem_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_urem_one args premises) := by
  sorry

theorem cmd_step_bv_urem_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_urem_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_urem_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_urem_self args premises) := by
  sorry

theorem cmd_step_bv_shl_zero_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_shl_zero args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_shl_zero args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_shl_zero args premises) := by
  sorry

theorem cmd_step_bv_lshr_zero_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_lshr_zero args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_lshr_zero args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_lshr_zero args premises) := by
  sorry

theorem cmd_step_bv_ashr_zero_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ashr_zero args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ashr_zero args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ashr_zero args premises) := by
  sorry

theorem cmd_step_bv_ugt_urem_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ugt_urem args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ugt_urem args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ugt_urem args premises) := by
  sorry

theorem cmd_step_bv_ult_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ult_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_ult_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ult_one args premises) := by
  sorry

theorem cmd_step_bv_merge_sign_extend_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_merge_sign_extend_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_merge_sign_extend_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_merge_sign_extend_1 args premises) := by
  sorry

theorem cmd_step_bv_merge_sign_extend_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_merge_sign_extend_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_merge_sign_extend_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_merge_sign_extend_2 args premises) := by
  sorry

theorem cmd_step_bv_sign_extend_eq_const_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sign_extend_eq_const_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sign_extend_eq_const_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sign_extend_eq_const_1 args premises) := by
  sorry

theorem cmd_step_bv_sign_extend_eq_const_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sign_extend_eq_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sign_extend_eq_const_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sign_extend_eq_const_2 args premises) := by
  sorry

theorem cmd_step_bv_zero_extend_eq_const_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_extend_eq_const_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_zero_extend_eq_const_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_extend_eq_const_1 args premises) := by
  sorry

theorem cmd_step_bv_zero_extend_eq_const_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_extend_eq_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_zero_extend_eq_const_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_extend_eq_const_2 args premises) := by
  sorry

theorem cmd_step_bv_zero_extend_ult_const_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_extend_ult_const_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_zero_extend_ult_const_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_extend_ult_const_1 args premises) := by
  sorry

theorem cmd_step_bv_zero_extend_ult_const_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_zero_extend_ult_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_zero_extend_ult_const_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_zero_extend_ult_const_2 args premises) := by
  sorry

theorem cmd_step_bv_sign_extend_ult_const_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sign_extend_ult_const_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sign_extend_ult_const_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sign_extend_ult_const_1 args premises) := by
  sorry

theorem cmd_step_bv_sign_extend_ult_const_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sign_extend_ult_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sign_extend_ult_const_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sign_extend_ult_const_2 args premises) := by
  sorry

theorem cmd_step_bv_sign_extend_ult_const_3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sign_extend_ult_const_3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sign_extend_ult_const_3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sign_extend_ult_const_3 args premises) := by
  sorry

theorem cmd_step_bv_sign_extend_ult_const_4_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_sign_extend_ult_const_4 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.bv_sign_extend_ult_const_4 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_sign_extend_ult_const_4 args premises) := by
  sorry

theorem cmd_step_sets_eq_singleton_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_eq_singleton_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_eq_singleton_emp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_eq_singleton_emp args premises) := by
  sorry

theorem cmd_step_sets_member_singleton_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_member_singleton args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_member_singleton args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_member_singleton args premises) := by
  sorry

theorem cmd_step_sets_member_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_member_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_member_emp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_member_emp args premises) := by
  sorry

theorem cmd_step_sets_subset_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_subset_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_subset_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_subset_elim args premises) := by
  sorry

theorem cmd_step_sets_union_comm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_union_comm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_union_comm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_union_comm args premises) := by
  sorry

theorem cmd_step_sets_inter_comm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_inter_comm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_inter_comm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_inter_comm args premises) := by
  sorry

theorem cmd_step_sets_inter_emp1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_inter_emp1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_inter_emp1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_inter_emp1 args premises) := by
  sorry

theorem cmd_step_sets_inter_emp2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_inter_emp2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_inter_emp2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_inter_emp2 args premises) := by
  sorry

theorem cmd_step_sets_minus_emp1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_minus_emp1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_minus_emp1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_minus_emp1 args premises) := by
  sorry

theorem cmd_step_sets_minus_emp2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_minus_emp2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_minus_emp2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_minus_emp2 args premises) := by
  sorry

theorem cmd_step_sets_union_emp1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_union_emp1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_union_emp1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_union_emp1 args premises) := by
  sorry

theorem cmd_step_sets_union_emp2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_union_emp2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_union_emp2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_union_emp2 args premises) := by
  sorry

theorem cmd_step_sets_inter_member_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_inter_member args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_inter_member args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_inter_member args premises) := by
  sorry

theorem cmd_step_sets_minus_member_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_minus_member args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_minus_member args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_minus_member args premises) := by
  sorry

theorem cmd_step_sets_union_member_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_union_member args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_union_member args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_union_member args premises) := by
  sorry

theorem cmd_step_sets_choose_singleton_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_choose_singleton args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_choose_singleton args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_choose_singleton args premises) := by
  sorry

theorem cmd_step_sets_minus_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_minus_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_minus_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_minus_self args premises) := by
  sorry

theorem cmd_step_sets_is_empty_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_is_empty_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_is_empty_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_is_empty_elim args premises) := by
  sorry

theorem cmd_step_sets_is_singleton_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_is_singleton_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.sets_is_singleton_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_is_singleton_elim args premises) := by
  sorry

theorem cmd_step_str_eq_ctn_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_ctn_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_ctn_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_ctn_false args premises) := by
  sorry

theorem cmd_step_str_eq_ctn_full_false1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_ctn_full_false1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_ctn_full_false1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_ctn_full_false1 args premises) := by
  sorry

theorem cmd_step_str_eq_ctn_full_false2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_ctn_full_false2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_ctn_full_false2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_ctn_full_false2 args premises) := by
  sorry

theorem cmd_step_str_eq_len_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_len_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_len_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_len_false args premises) := by
  sorry

theorem cmd_step_str_substr_empty_str_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_empty_str args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_empty_str args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_empty_str args premises) := by
  sorry

theorem cmd_step_str_substr_empty_range_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_empty_range args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_empty_range args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_empty_range args premises) := by
  sorry

theorem cmd_step_str_substr_empty_start_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_empty_start args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_empty_start args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_empty_start args premises) := by
  sorry

theorem cmd_step_str_substr_empty_start_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_empty_start_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_empty_start_neg args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_empty_start_neg args premises) := by
  sorry

theorem cmd_step_str_substr_substr_start_geq_len_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_substr_start_geq_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_substr_start_geq_len args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_substr_start_geq_len args premises) := by
  sorry

theorem cmd_step_str_substr_eq_empty_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_eq_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_eq_empty args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_eq_empty args premises) := by
  sorry

theorem cmd_step_str_substr_z_eq_empty_leq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_z_eq_empty_leq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_z_eq_empty_leq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_z_eq_empty_leq args premises) := by
  sorry

theorem cmd_step_str_substr_eq_empty_leq_len_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_eq_empty_leq_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_eq_empty_leq_len args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_eq_empty_leq_len args premises) := by
  sorry

theorem cmd_step_str_len_replace_inv_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_replace_inv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_len_replace_inv args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_replace_inv args premises) := by
  sorry

theorem cmd_step_str_len_replace_all_inv_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_replace_all_inv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_len_replace_all_inv args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_replace_all_inv args premises) := by
  sorry

theorem cmd_step_str_len_update_inv_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_update_inv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_len_update_inv args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_update_inv args premises) := by
  sorry

theorem cmd_step_str_update_in_first_concat_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_update_in_first_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_update_in_first_concat args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_update_in_first_concat args premises) := by
  sorry

theorem cmd_step_str_len_substr_in_range_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_substr_in_range args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_len_substr_in_range args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_substr_in_range args premises) := by
  sorry

theorem cmd_step_str_concat_clash_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_clash args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_concat_clash args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_clash args premises) := by
  sorry

theorem cmd_step_str_concat_clash_rev_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_clash_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_concat_clash_rev args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_clash_rev args premises) := by
  sorry

theorem cmd_step_str_concat_clash2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_clash2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_concat_clash2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_clash2 args premises) := by
  sorry

theorem cmd_step_str_concat_clash2_rev_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_clash2_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_concat_clash2_rev args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_clash2_rev args premises) := by
  sorry

theorem cmd_step_str_concat_unify_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_unify args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_concat_unify args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_unify args premises) := by
  sorry

theorem cmd_step_str_concat_unify_rev_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_unify_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_concat_unify_rev args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_unify_rev args premises) := by
  sorry

theorem cmd_step_str_concat_unify_base_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_unify_base args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_concat_unify_base args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_unify_base args premises) := by
  sorry

theorem cmd_step_str_concat_unify_base_rev_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_concat_unify_base_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_concat_unify_base_rev args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_concat_unify_base_rev args premises) := by
  sorry

theorem cmd_step_str_prefixof_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_prefixof_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_prefixof_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_prefixof_elim args premises) := by
  sorry

theorem cmd_step_str_suffixof_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_suffixof_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_suffixof_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_suffixof_elim args premises) := by
  sorry

theorem cmd_step_str_prefixof_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_prefixof_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_prefixof_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_prefixof_eq args premises) := by
  sorry

theorem cmd_step_str_suffixof_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_suffixof_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_suffixof_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_suffixof_eq args premises) := by
  sorry

theorem cmd_step_str_prefixof_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_prefixof_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_prefixof_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_prefixof_one args premises) := by
  sorry

theorem cmd_step_str_suffixof_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_suffixof_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_suffixof_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_suffixof_one args premises) := by
  sorry

theorem cmd_step_str_substr_combine1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_combine1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_combine1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_combine1 args premises) := by
  sorry

theorem cmd_step_str_substr_combine2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_combine2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_combine2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_combine2 args premises) := by
  sorry

theorem cmd_step_str_substr_combine3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_combine3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_combine3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_combine3 args premises) := by
  sorry

theorem cmd_step_str_substr_combine4_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_combine4 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_combine4 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_combine4 args premises) := by
  sorry

theorem cmd_step_str_substr_concat1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_concat1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_concat1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_concat1 args premises) := by
  sorry

theorem cmd_step_str_substr_concat2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_concat2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_concat2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_concat2 args premises) := by
  sorry

theorem cmd_step_str_substr_replace_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_replace args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_replace args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_replace args premises) := by
  sorry

theorem cmd_step_str_substr_full_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_full args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_full args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_full args premises) := by
  sorry

theorem cmd_step_str_substr_full_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_full_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_full_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_full_eq args premises) := by
  sorry

theorem cmd_step_str_contains_refl_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_refl args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_refl args premises) := by
  sorry

theorem cmd_step_str_contains_concat_find_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_concat_find args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_concat_find args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_concat_find args premises) := by
  sorry

theorem cmd_step_str_contains_concat_find_contra_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_concat_find_contra args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_concat_find_contra args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_concat_find_contra args premises) := by
  sorry

theorem cmd_step_str_contains_split_char_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_split_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_split_char args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_split_char args premises) := by
  sorry

theorem cmd_step_str_contains_leq_len_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_leq_len_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_leq_len_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_leq_len_eq args premises) := by
  sorry

theorem cmd_step_str_contains_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_emp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_emp args premises) := by
  sorry

theorem cmd_step_str_contains_char_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_char args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_char args premises) := by
  sorry

theorem cmd_step_str_at_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_at_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_at_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_at_elim args premises) := by
  sorry

theorem cmd_step_str_replace_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_self args premises) := by
  sorry

theorem cmd_step_str_replace_id_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_id args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_id args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_id args premises) := by
  sorry

theorem cmd_step_str_replace_prefix_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_prefix args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_prefix args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_prefix args premises) := by
  sorry

theorem cmd_step_str_replace_no_contains_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_no_contains args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_no_contains args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_no_contains args premises) := by
  sorry

theorem cmd_step_str_replace_find_base_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_find_base args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_find_base args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_find_base args premises) := by
  sorry

theorem cmd_step_str_replace_find_first_concat_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_find_first_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_find_first_concat args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_find_first_concat args premises) := by
  sorry

theorem cmd_step_str_replace_empty_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_empty args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_empty args premises) := by
  sorry

theorem cmd_step_str_replace_one_pre_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_one_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_one_pre args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_one_pre args premises) := by
  sorry

theorem cmd_step_str_replace_find_pre_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_find_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_find_pre args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_find_pre args premises) := by
  sorry

theorem cmd_step_str_replace_all_no_contains_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_all_no_contains args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_all_no_contains args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_all_no_contains args premises) := by
  sorry

theorem cmd_step_str_replace_all_empty_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_all_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_all_empty args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_all_empty args premises) := by
  sorry

theorem cmd_step_str_replace_all_id_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_all_id args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_all_id args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_all_id args premises) := by
  sorry

theorem cmd_step_str_replace_all_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_all_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_all_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_all_self args premises) := by
  sorry

theorem cmd_step_str_replace_re_none_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_re_none args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_re_none args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_re_none args premises) := by
  sorry

theorem cmd_step_str_replace_re_all_none_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_re_all_none args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_re_all_none args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_re_all_none args premises) := by
  sorry

theorem cmd_step_str_len_concat_rec_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_concat_rec args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_len_concat_rec args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_concat_rec args premises) := by
  sorry

theorem cmd_step_str_len_eq_zero_concat_rec_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_eq_zero_concat_rec args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_len_eq_zero_concat_rec args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_eq_zero_concat_rec args premises) := by
  sorry

theorem cmd_step_str_len_eq_zero_base_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_len_eq_zero_base args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_len_eq_zero_base args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_len_eq_zero_base args premises) := by
  sorry

theorem cmd_step_str_indexof_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_self args premises) := by
  sorry

theorem cmd_step_str_indexof_no_contains_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_no_contains args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_no_contains args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_no_contains args premises) := by
  sorry

theorem cmd_step_str_indexof_oob_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_oob args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_oob args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_oob args premises) := by
  sorry

theorem cmd_step_str_indexof_oob2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_oob2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_oob2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_oob2 args premises) := by
  sorry

theorem cmd_step_str_indexof_contains_pre_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_contains_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_contains_pre args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_contains_pre args premises) := by
  sorry

theorem cmd_step_str_indexof_contains_concat_pre_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_contains_concat_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_contains_concat_pre args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_contains_concat_pre args premises) := by
  sorry

theorem cmd_step_str_indexof_find_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_find_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_find_emp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_find_emp args premises) := by
  sorry

theorem cmd_step_str_indexof_eq_irr_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_eq_irr args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_eq_irr args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_eq_irr args premises) := by
  sorry

theorem cmd_step_str_indexof_re_none_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_re_none args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_re_none args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_re_none args premises) := by
  sorry

theorem cmd_step_str_indexof_re_emp_re_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_re_emp_re args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_indexof_re_emp_re args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_re_emp_re args premises) := by
  sorry

theorem cmd_step_str_to_lower_concat_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_lower_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_to_lower_concat args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_lower_concat args premises) := by
  sorry

theorem cmd_step_str_to_upper_concat_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_upper_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_to_upper_concat args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_upper_concat args premises) := by
  sorry

theorem cmd_step_str_to_lower_upper_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_lower_upper args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_to_lower_upper args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_lower_upper args premises) := by
  sorry

theorem cmd_step_str_to_upper_lower_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_upper_lower args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_to_upper_lower args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_upper_lower args premises) := by
  sorry

theorem cmd_step_str_to_lower_len_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_lower_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_to_lower_len args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_lower_len args premises) := by
  sorry

theorem cmd_step_str_to_upper_len_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_upper_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_to_upper_len args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_upper_len args premises) := by
  sorry

theorem cmd_step_str_to_lower_from_int_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_lower_from_int args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_to_lower_from_int args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_lower_from_int args premises) := by
  sorry

theorem cmd_step_str_to_upper_from_int_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_upper_from_int args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_to_upper_from_int args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_upper_from_int args premises) := by
  sorry

theorem cmd_step_str_to_int_concat_neg_one_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_to_int_concat_neg_one args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_to_int_concat_neg_one args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_to_int_concat_neg_one args premises) := by
  sorry

theorem cmd_step_str_is_digit_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_is_digit_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_is_digit_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_is_digit_elim args premises) := by
  sorry

theorem cmd_step_str_leq_empty_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_leq_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_leq_empty args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_leq_empty args premises) := by
  sorry

theorem cmd_step_str_leq_empty_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_leq_empty_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_leq_empty_eq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_leq_empty_eq args premises) := by
  sorry

theorem cmd_step_str_leq_concat_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_leq_concat_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_leq_concat_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_leq_concat_false args premises) := by
  sorry

theorem cmd_step_str_leq_concat_true_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_leq_concat_true args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_leq_concat_true args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_leq_concat_true args premises) := by
  sorry

theorem cmd_step_str_leq_concat_base_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_leq_concat_base_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_leq_concat_base_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_leq_concat_base_1 args premises) := by
  sorry

theorem cmd_step_str_leq_concat_base_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_leq_concat_base_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_leq_concat_base_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_leq_concat_base_2 args premises) := by
  sorry

theorem cmd_step_str_lt_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_lt_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_lt_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_lt_elim args premises) := by
  sorry

theorem cmd_step_str_from_int_no_ctn_nondigit_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_from_int_no_ctn_nondigit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_from_int_no_ctn_nondigit args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_from_int_no_ctn_nondigit args premises) := by
  sorry

theorem cmd_step_str_substr_ctn_contra_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_ctn_contra args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_ctn_contra args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_ctn_contra args premises) := by
  sorry

theorem cmd_step_str_substr_ctn_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_ctn args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_ctn args premises) := by
  sorry

theorem cmd_step_str_replace_dual_ctn_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_dual_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_dual_ctn args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_dual_ctn args premises) := by
  sorry

theorem cmd_step_str_replace_dual_ctn_false_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_dual_ctn_false args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_dual_ctn_false args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_dual_ctn_false args premises) := by
  sorry

theorem cmd_step_str_replace_self_ctn_simp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_self_ctn_simp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_self_ctn_simp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_self_ctn_simp args premises) := by
  sorry

theorem cmd_step_str_replace_emp_ctn_src_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_replace_emp_ctn_src args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_replace_emp_ctn_src args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_replace_emp_ctn_src args premises) := by
  sorry

theorem cmd_step_str_substr_char_start_eq_len_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_char_start_eq_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_char_start_eq_len args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_char_start_eq_len args premises) := by
  sorry

theorem cmd_step_str_contains_repl_char_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_repl_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_repl_char args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_repl_char args premises) := by
  sorry

theorem cmd_step_str_contains_repl_self_tgt_char_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_repl_self_tgt_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_repl_self_tgt_char args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_repl_self_tgt_char args premises) := by
  sorry

theorem cmd_step_str_contains_repl_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_repl_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_repl_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_repl_self args premises) := by
  sorry

theorem cmd_step_str_contains_repl_tgt_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_contains_repl_tgt args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_contains_repl_tgt args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_contains_repl_tgt args premises) := by
  sorry

theorem cmd_step_str_repl_repl_len_id_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_len_id args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_len_id args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_len_id args premises) := by
  sorry

theorem cmd_step_str_repl_repl_src_tgt_no_ctn_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_src_tgt_no_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_src_tgt_no_ctn args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_src_tgt_no_ctn args premises) := by
  sorry

theorem cmd_step_str_repl_repl_tgt_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_tgt_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_tgt_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_tgt_self args premises) := by
  sorry

theorem cmd_step_str_repl_repl_tgt_no_ctn_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_tgt_no_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_tgt_no_ctn args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_tgt_no_ctn args premises) := by
  sorry

theorem cmd_step_str_repl_repl_src_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_src_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_src_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_src_self args premises) := by
  sorry

theorem cmd_step_str_repl_repl_src_inv_no_ctn1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_src_inv_no_ctn1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn1 args premises) := by
  sorry

theorem cmd_step_str_repl_repl_src_inv_no_ctn2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_src_inv_no_ctn2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn2 args premises) := by
  sorry

theorem cmd_step_str_repl_repl_src_inv_no_ctn3_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_src_inv_no_ctn3 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn3 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_src_inv_no_ctn3 args premises) := by
  sorry

theorem cmd_step_str_repl_repl_dual_self_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_dual_self args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_dual_self args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_dual_self args premises) := by
  sorry

theorem cmd_step_str_repl_repl_dual_ite1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_dual_ite1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_dual_ite1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_dual_ite1 args premises) := by
  sorry

theorem cmd_step_str_repl_repl_dual_ite2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_dual_ite2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_dual_ite2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_dual_ite2 args premises) := by
  sorry

theorem cmd_step_str_repl_repl_lookahead_id_simp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_repl_repl_lookahead_id_simp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_repl_repl_lookahead_id_simp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_repl_repl_lookahead_id_simp args premises) := by
  sorry

theorem cmd_step_re_all_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_all_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_all_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_all_elim args premises) := by
  sorry

theorem cmd_step_re_opt_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_opt_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_opt_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_opt_elim args premises) := by
  sorry

theorem cmd_step_re_diff_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_diff_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_diff_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_diff_elim args premises) := by
  sorry

theorem cmd_step_re_plus_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_plus_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_plus_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_plus_elim args premises) := by
  sorry

theorem cmd_step_re_repeat_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_repeat_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_repeat_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_repeat_elim args premises) := by
  sorry

theorem cmd_step_re_concat_star_swap_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_star_swap args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_concat_star_swap args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_star_swap args premises) := by
  sorry

theorem cmd_step_re_concat_star_repeat_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_star_repeat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_concat_star_repeat args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_star_repeat args premises) := by
  sorry

theorem cmd_step_re_concat_star_subsume1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_star_subsume1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_concat_star_subsume1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_star_subsume1 args premises) := by
  sorry

theorem cmd_step_re_concat_star_subsume2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_star_subsume2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_concat_star_subsume2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_star_subsume2 args premises) := by
  sorry

theorem cmd_step_re_concat_merge_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_merge args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_concat_merge args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_merge args premises) := by
  sorry

theorem cmd_step_re_union_all_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_union_all args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_union_all args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_union_all args premises) := by
  sorry

theorem cmd_step_re_union_const_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_union_const_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_union_const_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_union_const_elim args premises) := by
  sorry

theorem cmd_step_re_inter_all_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter_all args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_inter_all args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter_all args premises) := by
  sorry

theorem cmd_step_re_star_none_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_none args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_star_none args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_none args premises) := by
  sorry

theorem cmd_step_re_star_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_star_emp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_emp args premises) := by
  sorry

theorem cmd_step_re_star_star_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_star_star args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_star args premises) := by
  sorry

theorem cmd_step_re_range_refl_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_range_refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_range_refl args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_range_refl args premises) := by
  sorry

theorem cmd_step_re_range_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_range_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_range_emp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_range_emp args premises) := by
  sorry

theorem cmd_step_re_range_non_singleton_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_range_non_singleton_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_range_non_singleton_1 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_range_non_singleton_1 args premises) := by
  sorry

theorem cmd_step_re_range_non_singleton_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_range_non_singleton_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_range_non_singleton_2 args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_range_non_singleton_2 args premises) := by
  sorry

theorem cmd_step_re_star_union_char_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_union_char args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_star_union_char args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_union_char args premises) := by
  sorry

theorem cmd_step_re_star_union_drop_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_union_drop_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_star_union_drop_emp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_union_drop_emp args premises) := by
  sorry

theorem cmd_step_re_loop_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_loop_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_loop_neg args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_loop_neg args premises) := by
  sorry

theorem cmd_step_re_inter_cstring_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter_cstring args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_inter_cstring args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter_cstring args premises) := by
  sorry

theorem cmd_step_re_inter_cstring_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_inter_cstring_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_inter_cstring_neg args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_inter_cstring_neg args premises) := by
  sorry

theorem cmd_step_str_substr_len_include_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_len_include args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_len_include args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_len_include args premises) := by
  sorry

theorem cmd_step_str_substr_len_include_pre_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_len_include_pre args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_len_include_pre args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_len_include_pre args premises) := by
  sorry

theorem cmd_step_str_substr_len_norm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_substr_len_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_substr_len_norm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_substr_len_norm args premises) := by
  sorry

theorem cmd_step_seq_len_rev_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_len_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.seq_len_rev args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_len_rev args premises) := by
  sorry

theorem cmd_step_seq_rev_rev_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_rev_rev args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.seq_rev_rev args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_rev_rev args premises) := by
  sorry

theorem cmd_step_seq_rev_concat_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_rev_concat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.seq_rev_concat args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_rev_concat args premises) := by
  sorry

theorem cmd_step_str_eq_repl_self_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_self_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_repl_self_emp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_self_emp args premises) := by
  sorry

theorem cmd_step_str_eq_repl_no_change_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_no_change args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_repl_no_change args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_no_change args premises) := by
  sorry

theorem cmd_step_str_eq_repl_tgt_eq_len_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_tgt_eq_len args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_repl_tgt_eq_len args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_tgt_eq_len args premises) := by
  sorry

theorem cmd_step_str_eq_repl_len_one_emp_prefix_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_len_one_emp_prefix args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_repl_len_one_emp_prefix args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_len_one_emp_prefix args premises) := by
  sorry

theorem cmd_step_str_eq_repl_emp_tgt_nemp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_emp_tgt_nemp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_repl_emp_tgt_nemp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_emp_tgt_nemp args premises) := by
  sorry

theorem cmd_step_str_eq_repl_nemp_src_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_nemp_src_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_repl_nemp_src_emp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_nemp_src_emp args premises) := by
  sorry

theorem cmd_step_str_eq_repl_self_src_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_eq_repl_self_src args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_eq_repl_self_src args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_eq_repl_self_src args premises) := by
  sorry

theorem cmd_step_seq_len_unit_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_len_unit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.seq_len_unit args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_len_unit args premises) := by
  sorry

theorem cmd_step_seq_nth_unit_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_nth_unit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.seq_nth_unit args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_nth_unit args premises) := by
  sorry

theorem cmd_step_seq_rev_unit_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.seq_rev_unit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.seq_rev_unit args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.seq_rev_unit args premises) := by
  sorry

theorem cmd_step_re_in_empty_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_in_empty args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_in_empty args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_in_empty args premises) := by
  sorry

theorem cmd_step_re_in_sigma_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_in_sigma args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_in_sigma args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_in_sigma args premises) := by
  sorry

theorem cmd_step_re_in_sigma_star_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_in_sigma_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_in_sigma_star args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_in_sigma_star args premises) := by
  sorry

theorem cmd_step_re_in_cstring_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_in_cstring args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_in_cstring args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_in_cstring args premises) := by
  sorry

theorem cmd_step_re_in_comp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_in_comp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.re_in_comp args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_in_comp args premises) := by
  sorry

theorem cmd_step_str_in_re_union_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_union_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_union_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_union_elim args premises) := by
  sorry

theorem cmd_step_str_in_re_inter_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_inter_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_inter_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_inter_elim args premises) := by
  sorry

theorem cmd_step_str_in_re_range_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_range_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_range_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_range_elim args premises) := by
  sorry

theorem cmd_step_str_in_re_contains_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_contains args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_contains args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_contains args premises) := by
  sorry

theorem cmd_step_str_in_re_from_int_nemp_dig_range_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_from_int_nemp_dig_range args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_from_int_nemp_dig_range args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_from_int_nemp_dig_range args premises) := by
  sorry

theorem cmd_step_str_in_re_from_int_dig_range_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_from_int_dig_range args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.str_in_re_from_int_dig_range args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_from_int_dig_range args premises) := by
  sorry

theorem cmd_step_eq_refl_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.eq_refl args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_refl args premises) := by
  sorry

theorem cmd_step_eq_symm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_symm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.eq_symm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_symm args premises) := by
  sorry

theorem cmd_step_eq_cond_deq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_cond_deq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.eq_cond_deq args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_cond_deq args premises) := by
  sorry

theorem cmd_step_eq_ite_lift_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.eq_ite_lift args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.eq_ite_lift args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.eq_ite_lift args premises) := by
  sorry

theorem cmd_step_distinct_binary_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_binary_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.distinct_binary_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_binary_elim args premises) := by
  sorry

theorem cmd_step_uf_bv2nat_int2bv_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv args premises) := by
  sorry

theorem cmd_step_uf_bv2nat_int2bv_extend_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv_extend args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises) := by
  sorry

theorem cmd_step_uf_bv2nat_int2bv_extract_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv_extract args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract args premises) := by
  sorry

theorem cmd_step_uf_int2bv_bv2nat_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_int2bv_bv2nat args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.uf_int2bv_bv2nat args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_int2bv_bv2nat args premises) := by
  sorry

theorem cmd_step_uf_bv2nat_geq_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_geq_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.uf_bv2nat_geq_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_geq_elim args premises) := by
  sorry

theorem cmd_step_uf_int2bv_bvult_equiv_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_int2bv_bvult_equiv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.uf_int2bv_bvult_equiv args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_int2bv_bvult_equiv args premises) := by
  sorry

theorem cmd_step_uf_int2bv_bvule_equiv_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_int2bv_bvule_equiv args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.uf_int2bv_bvule_equiv args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_int2bv_bvule_equiv args premises) := by
  sorry

theorem cmd_step_uf_sbv_to_int_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_sbv_to_int_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.uf_sbv_to_int_elim args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_sbv_to_int_elim args premises) := by
  sorry

theorem cmd_step_evaluate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.evaluate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.evaluate args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.evaluate args premises) := by
  sorry

theorem cmd_step_distinct_values_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_values args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.distinct_values args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_values args premises) := by
  sorry

theorem cmd_step_aci_norm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.aci_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.aci_norm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.aci_norm args premises) := by
  sorry

theorem cmd_step_absorb_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.absorb args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.absorb args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.absorb args premises) := by
  sorry

theorem cmd_step_distinct_card_conflict_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.distinct_card_conflict args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.distinct_card_conflict args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.distinct_card_conflict args premises) := by
  sorry
