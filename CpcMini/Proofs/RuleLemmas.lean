import CpcMini.Proofs.Rules.Support
import CpcMini.Proofs.Rules.Scope
import CpcMini.Proofs.Rules.Contra
import CpcMini.Proofs.Rules.Refl
import CpcMini.Proofs.Rules.Symm
import CpcMini.Proofs.Rules.Trans

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
  intro hTrans1 hTy1 hPremisesTrans hPremisesTy hProg
  by_cases hX1 : x1 = Term.Stuck
  · exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven, hX1]))
  · cases args with
    | nil =>
        cases premises with
        | nil =>
            exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
        | cons n1 premises =>
            cases premises with
            | nil =>
                let x2 := __eo_state_proven_nth s n1
                have hTrans2 : RuleProofs.eo_has_smt_translation x2 :=
                  hPremisesTrans x2 (by simp [x2, premiseTermList])
                have hTy2 : __eo_typeof x2 = Term.Bool :=
                  hPremisesTy x2 (by simp [x2, premiseTermList])
                have hBool1 : RuleProofs.eo_has_bool_type x1 :=
                  RuleProofs.eo_typeof_bool_implies_has_bool_type x1 hTrans1 hTy1
                have hBool2 : RuleProofs.eo_has_bool_type x2 :=
                  RuleProofs.eo_typeof_bool_implies_has_bool_type x2 hTrans2 hTy2
                refine ⟨x2, ?_, ?_, ?_⟩
                · simp [x2, premiseTermList]
                · intro M hM hImp
                  simpa [x2, __eo_cmd_step_pop_proven, hX1] using
                    facts___eo_prog_scope_impl M hM x1 x2 hImp hTrans1 hTrans2 hTy1 hTy2
                      (by simpa [x2, __eo_cmd_step_pop_proven, hX1] using hProg)
                · simpa [x2, __eo_cmd_step_pop_proven, hX1] using
                    typed___eo_prog_scope_of_bool_args x1 x2 hBool1 hBool2
                      (by simpa [x2, __eo_cmd_step_pop_proven, hX1] using hProg)
            | cons _ _ =>
                exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
    | cons _ _ =>
        exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))

theorem cmd_step_contra_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.contra args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.contra args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.contra args premises) :=
by
  intro _hCmdTrans hPremisesBool hProg
  cases args with
  | nil =>
      cases premises with
      | nil =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons n1 premises =>
          cases premises with
          | nil =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
          | cons n2 premises =>
              cases premises with
              | nil =>
                  let X1 := __eo_state_proven_nth s n1
                  let X2 := __eo_state_proven_nth s n2
                  constructor
                  · intro hTrue
                    exact facts___eo_prog_contra_impl M hM X1 X2
                      (hTrue X1 (by simp [X1, premiseTermList]))
                      (hTrue X2 (by simp [X2, premiseTermList]))
                      (by simpa [X1, X2, premiseTermList, __eo_cmd_step_proven] using hProg)
                  · exact typed___eo_prog_contra_impl X1 X2
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      (hPremisesBool X2 (by simp [X2, premiseTermList]))
                      (by simpa [X1, X2, premiseTermList, __eo_cmd_step_proven] using hProg)
              | cons n3 premises =>
                  exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | cons a args =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))

theorem cmd_step_refl_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.refl args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.refl args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.refl args premises) :=
by
  intro hCmdTrans hPremisesBool hProg
  cases args with
  | nil =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk] using hCmdTrans
              refine ⟨?_, ?_⟩
              · intro _hTrue
                exact facts___eo_prog_refl_impl M hM a1 hATrans
                  (by simpa [__eo_cmd_step_proven] using hProg)
              · exact typed___eo_prog_refl_impl a1 hATrans
                  (by simpa [__eo_cmd_step_proven] using hProg)
          | cons n premises =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons a2 args =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))

theorem cmd_step_symm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.symm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.symm args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.symm args premises) :=
by
  intro _hCmdTrans hPremisesBool hProg
  cases args with
  | nil =>
      cases premises with
      | nil =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X := __eo_state_proven_nth s n1
              refine ⟨?_, ?_⟩
              · intro hTrue
                exact facts___eo_prog_symm_impl M hM X
                  (hTrue X (by simp [X, premiseTermList]))
                  (by simpa [X, premiseTermList, __eo_cmd_step_proven] using hProg)
              · exact typed___eo_prog_symm_impl X
                  (hPremisesBool X (by simp [X, premiseTermList]))
                  (by simpa [X, premiseTermList, __eo_cmd_step_proven] using hProg)
          | cons n2 premises =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | cons a args =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))

theorem cmd_step_trans_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.trans args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.trans args premises ≠ Term.Stuck ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.trans args premises) :=
by
  intro _hCmdTrans hPremises hProg
  cases args with
  | nil =>
      let premisesL := premiseTermList s premises
      have hProps :
          StepRuleProperties M premisesL
            (__eo_prog_trans (Proof.pf (premiseAndFormulaList premisesL))) := by
        refine ⟨?_, ?_⟩
        · intro hTrue
          exact facts___eo_prog_trans_impl M hM (premiseAndFormulaList premisesL)
            (premiseAndFormulaList_true_of_all_true M premisesL hTrue)
            (by
              simpa [premisesL, __eo_cmd_step_proven, mk_premise_list_and_eq_premiseAndFormulaList]
                using hProg)
        · exact typed___eo_prog_trans_impl (premiseAndFormulaList premisesL)
            (premiseAndFormulaList_has_bool_type premisesL (by simpa [premisesL] using hPremises))
            (by
              simpa [premisesL, __eo_cmd_step_proven, mk_premise_list_and_eq_premiseAndFormulaList]
                using hProg)
      simpa [premisesL, __eo_cmd_step_proven, mk_premise_list_and_eq_premiseAndFormulaList] using hProps
  | cons a args =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
