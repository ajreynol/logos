import Cpc.Proofs.RuleSupport.ConcatSplitSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

theorem cmd_step_concat_split_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_split args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_split args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_split args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_split args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons n2 premises =>
                  cases premises with
                  | nil =>
                      let X1 := __eo_state_proven_nth s n1
                      let X2 := __eo_state_proven_nth s n2
                      have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                        have hArgs : RuleProofs.eo_has_smt_translation a1 ∧
                            True := by
                          simpa [cmdTranslationOk, cArgListTranslationOk]
                            using hCmdTrans
                        exact hArgs.1
                      have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
                        hPremisesBool X1 (by simp [X1, premiseTermList])
                      have hX2Bool : RuleProofs.eo_has_bool_type X2 :=
                        hPremisesBool X2 (by simp [X2, premiseTermList])
                      have hProgConcat :
                          __eo_prog_concat_split a1 (Proof.pf X1)
                              (Proof.pf X2) ≠ Term.Stuck := by
                        change __eo_prog_concat_split a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)) ≠
                            Term.Stuck at hProg
                        simpa [X1, X2] using hProg
                      rcases
                          eo_prog_concat_split_premise_shapes_of_ne_stuck
                            a1 X1 X2 hProgConcat with
                        ⟨lhs, rhs, lhs1, rhs1, hX1Eq, hX2Eq⟩
                      have hState1Eq :
                          __eo_state_proven_nth s n1 = mkEq lhs rhs := by
                        simpa [X1] using hX1Eq
                      have hState2Eq :
                          __eo_state_proven_nth s n2 =
                            mkNot (mkEq (mkStrLen lhs1) (mkStrLen rhs1)) := by
                        simpa [X2] using hX2Eq
                      have hPremEqBool :
                          RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
                        simpa [X1, hState1Eq] using hX1Bool
                      have hLenNeBool :
                          RuleProofs.eo_has_bool_type
                            (mkNot (mkEq (mkStrLen lhs1) (mkStrLen rhs1))) := by
                        simpa [X2, hState2Eq] using hX2Bool
                      have hProgRule :
                          __eo_prog_concat_split a1
                              (Proof.pf (mkEq lhs rhs))
                              (Proof.pf
                                (mkNot
                                  (mkEq (mkStrLen lhs1) (mkStrLen rhs1)))) ≠
                            Term.Stuck := by
                        simpa [X1, X2, hState1Eq, hState2Eq]
                          using hProgConcat
                      have hResultTyRule :
                          __eo_typeof
                              (__eo_prog_concat_split a1
                                (Proof.pf (mkEq lhs rhs))
                                (Proof.pf
                                  (mkNot
                                    (mkEq (mkStrLen lhs1)
                                      (mkStrLen rhs1))))) =
                            Term.Bool := by
                        change __eo_typeof
                            (__eo_prog_concat_split a1
                              (Proof.pf (__eo_state_proven_nth s n1))
                              (Proof.pf (__eo_state_proven_nth s n2))) =
                          Term.Bool at hResultTy
                        simpa [hState1Eq, hState2Eq] using hResultTy
                      change StepRuleProperties M
                        [__eo_state_proven_nth s n1,
                          __eo_state_proven_nth s n2]
                        (__eo_prog_concat_split a1
                          (Proof.pf (__eo_state_proven_nth s n1))
                          (Proof.pf (__eo_state_proven_nth s n2)))
                      rw [hState1Eq, hState2Eq]
                      exact step_concat_split_core M hM a1 lhs rhs lhs1 rhs1
                        hA1Trans hPremEqBool hLenNeBool hProgRule
                        hResultTyRule
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)

