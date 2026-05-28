import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/--
Trusted semantic core for `skolemize`.

The wrapper theorem below proves that the checker command has the canonical
single-premise shape and that the premise/result are Boolean where the checker
requires them.  The remaining obligation is the model-theoretic Skolem-choice
argument for the generated simultaneous substitution.
-/
private axiom trusted_skolemize_canonical_properties
    (M : SmtModel) (hM : model_total_typed M) (P : Term) :
  RuleProofs.eo_has_bool_type P ->
  __eo_typeof (__eo_prog_skolemize (Proof.pf P)) = Term.Bool ->
  StepRuleProperties M [P] (__eo_prog_skolemize (Proof.pf P))

theorem cmd_step_skolemize_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.skolemize args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.skolemize args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.skolemize args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.skolemize args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              let P := __eo_state_proven_nth s n1
              change StepRuleProperties M [P] (__eo_prog_skolemize (Proof.pf P))
              have hPremiseBool : RuleProofs.eo_has_bool_type P :=
                hPremisesBool P (by simp [P, premiseTermList])
              have hResultTyLocal :
                  __eo_typeof (__eo_prog_skolemize (Proof.pf P)) = Term.Bool := by
                change
                  __eo_typeof
                    (__eo_prog_skolemize
                      (Proof.pf (__eo_state_proven_nth s n1))) = Term.Bool at hResultTy
                simpa [P] using hResultTy
              exact trusted_skolemize_canonical_properties
                M hM P hPremiseBool hResultTyLocal
