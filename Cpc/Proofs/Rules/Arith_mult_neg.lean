import Cpc.Proofs.RuleSupport.ArithMultSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem cmd_step_arith_mult_neg_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_mult_neg args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_mult_neg args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_mult_neg args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_mult_neg args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons m args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons F args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  have hArgOk :
                      arithMultArgTranslationOk
                        (CArgList.cons m (CArgList.cons F CArgList.nil)) := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  rcases ArithMultSupport.arithMultArgTranslationOk_two m F hArgOk with
                    ⟨r, a, b, hF, hmTrans0, hFTrans0, hRel, hMArith, haTy, hbTy⟩
                  subst F
                  have hmTrans : RuleProofs.eo_has_smt_translation m := by
                    simpa [eoHasSmtTranslation, RuleProofs.eo_has_smt_translation] using hmTrans0
                  have hFTrans :
                      RuleProofs.eo_has_smt_translation
                        (ArithMultSupport.relTerm r a b) := by
                    simpa [eoHasSmtTranslation, RuleProofs.eo_has_smt_translation,
                      ArithMultSupport.relTerm] using hFTrans0
                  change __eo_typeof
                    (__eo_prog_arith_mult_neg m (ArithMultSupport.relTerm r a b)) =
                      Term.Bool at hResultTy
                  have hResultTrue :
                      eo_interprets M
                        (__eo_prog_arith_mult_neg m
                          (ArithMultSupport.relTerm r a b)) true :=
                    ArithMultSupport.facts_arith_mult_neg M hM m r a b
                      hmTrans hFTrans hRel hMArith haTy hbTy hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    exact hResultTrue
                  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                      (RuleProofs.eo_has_bool_type_of_interprets_true M _
                        hResultTrue)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
