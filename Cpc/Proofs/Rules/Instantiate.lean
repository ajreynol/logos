import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def forallFormula (xs F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F

private theorem eo_typeof_stuck_ne_bool :
    __eo_typeof Term.Stuck ≠ Term.Bool := by
  native_decide

private theorem instantiate_shape_of_typeof_bool
    (ts premise : Term) :
  __eo_typeof (__eo_prog_instantiate ts (Proof.pf premise)) = Term.Bool ->
  ∃ xs F,
    premise = forallFormula xs F ∧
    __eo_prog_instantiate ts (Proof.pf premise) = __substitute_simul F xs ts := by
  intro hTy
  cases premise with
  | Apply f F =>
      cases f with
      | Apply q xs =>
          cases q with
          | UOp op =>
              cases op with
              | «forall» =>
                  by_cases hTs : ts = Term.Stuck
                  · subst ts
                    simp [__eo_prog_instantiate] at hTy
                    exact False.elim (eo_typeof_stuck_ne_bool hTy)
                  · refine ⟨xs, F, rfl, ?_⟩
                    cases ts <;> simp [__eo_prog_instantiate] at hTs ⊢
              | _ =>
                  cases ts <;> simp [__eo_prog_instantiate] at hTy <;>
                    exact False.elim (eo_typeof_stuck_ne_bool hTy)
          | _ =>
              cases ts <;> simp [__eo_prog_instantiate] at hTy <;>
                exact False.elim (eo_typeof_stuck_ne_bool hTy)
      | _ =>
          cases ts <;> simp [__eo_prog_instantiate] at hTy <;>
            exact False.elim (eo_typeof_stuck_ne_bool hTy)
  | _ =>
      cases ts <;> simp [__eo_prog_instantiate] at hTy <;>
        exact False.elim (eo_typeof_stuck_ne_bool hTy)

private theorem instantiate_substitute_simul_facts
    (M : SmtModel) (hM : model_total_typed M)
    (ts xs F : Term) :
  EoListAllHaveSmtTranslation ts ->
  RuleProofs.eo_has_bool_type (forallFormula xs F) ->
  __eo_typeof (__substitute_simul F xs ts) = Term.Bool ->
  eo_interprets M (forallFormula xs F) true ->
  eo_interprets M (__substitute_simul F xs ts) true :=
by
  sorry

private theorem instantiate_substitute_simul_has_smt_translation
    (ts xs F : Term) :
  EoListAllHaveSmtTranslation ts ->
  RuleProofs.eo_has_bool_type (forallFormula xs F) ->
  __eo_typeof (__substitute_simul F xs ts) = Term.Bool ->
  RuleProofs.eo_has_smt_translation (__substitute_simul F xs ts) :=
by
  sorry

theorem cmd_step_instantiate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.instantiate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.instantiate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.instantiate args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.instantiate args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
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
                  let X1 := __eo_state_proven_nth s n1
                  have hArgs : EoListAllHaveSmtTranslation a1 := by
                    have hMask :
                        cArgListTranslationOkMask [ArgTranslationKind.list]
                          (CArgList.cons a1 CArgList.nil) := by
                      simpa [cmdTranslationOk] using hCmdTrans
                    simpa [cArgListTranslationOkMask, argTranslationOkMasked] using hMask
                  have hX1Bool : RuleProofs.eo_has_bool_type X1 := by
                    exact hPremisesBool X1 (by simp [X1, premiseTermList])
                  have hInstTy :
                      __eo_typeof (__eo_prog_instantiate a1 (Proof.pf X1)) =
                        Term.Bool := by
                    change
                      __eo_typeof
                          (__eo_prog_instantiate a1
                            (Proof.pf (__eo_state_proven_nth s n1))) =
                        Term.Bool at hResultTy
                    simpa [X1] using hResultTy
                  rcases instantiate_shape_of_typeof_bool a1 X1 hInstTy with
                    ⟨xs, F, hX1, hInst⟩
                  have hForallBool :
                      RuleProofs.eo_has_bool_type (forallFormula xs F) := by
                    simpa [hX1] using hX1Bool
                  have hSubTy :
                      __eo_typeof (__substitute_simul F xs a1) = Term.Bool := by
                    rw [← hInst]
                    exact hInstTy
                  refine ⟨?_, ?_⟩
                  · intro hTrue
                    have hX1True : eo_interprets M X1 true :=
                      hTrue X1 (by simp [X1, premiseTermList])
                    change eo_interprets M
                      (__eo_prog_instantiate a1 (Proof.pf X1)) true
                    rw [hInst]
                    exact
                      instantiate_substitute_simul_facts M hM a1 xs F hArgs
                        hForallBool hSubTy (by simpa [hX1] using hX1True)
                  · change RuleProofs.eo_has_smt_translation
                      (__eo_prog_instantiate a1 (Proof.pf X1))
                    rw [hInst]
                    exact
                      instantiate_substitute_simul_has_smt_translation a1 xs F hArgs
                        hForallBool hSubTy
