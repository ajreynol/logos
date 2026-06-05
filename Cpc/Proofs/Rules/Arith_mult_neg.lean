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
                  have hArgsTrans :
                      cArgListTranslationOk
                        (CArgList.cons m (CArgList.cons F CArgList.nil)) := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  rcases hArgsTrans with ⟨hmTrans0, hFTrans0, _⟩
                  have hmTrans : RuleProofs.eo_has_smt_translation m :=
                    hmTrans0.to_ruleProofs
                  have hFTrans : RuleProofs.eo_has_smt_translation F :=
                    hFTrans0.to_ruleProofs
                  change __eo_typeof
                    (__eo_prog_arith_mult_neg m F) = Term.Bool at hResultTy
                  have hResultTrue :
                      eo_interprets M (__eo_prog_arith_mult_neg m F) true :=
                    ArithMultSupport.facts_arith_mult_neg M hM m F
                      hmTrans hFTrans hResultTy
                  refine ⟨?_, ?_⟩
                  · intro _hTrue
                    exact hResultTrue
                  · exact eoHasSmtTranslation.of_has_bool_type
                      (RuleProofs.eo_has_bool_type_of_interprets_true M _
                        hResultTrue)
                      (by
                        change eoUOpIndicesClosed (__eo_prog_arith_mult_neg m F)
                        have hmClosed : eoUOpIndicesClosed m := hmTrans0.indices_closed
                        have hFClosed : eoUOpIndicesClosed F := hFTrans0.indices_closed
                        cases m <;> cases F <;>
                          simp [__eo_prog_arith_mult_neg, __mk_arith_mult_neg,
                            __arith_rel_inv, __eo_mk_apply, __eo_nil,
                            __eo_nil_mult, __arith_mk_one, __arith_mk_zero,
                            eoUOpIndicesClosed] at hmClosed hFClosed ⊢)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
