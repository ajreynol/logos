import Cpc.Proofs.ArraySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem no_smt_translation_apply_set (T : Term) :
    ¬ RuleProofs.eo_has_smt_translation (Term.Apply Term.Set T) := by
  intro hTrans
  have hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply Term.Set T)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply Term.Set T)) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation (Term.Apply Term.Set T) hTrans
  have hNone : __eo_to_smt_type (__eo_typeof (Term.Apply Term.Set T)) = SmtType.None := by
    change __eo_to_smt_type (__eo_typeof_Seq (__eo_typeof T)) = SmtType.None
    unfold __eo_typeof_Seq
    split <;> rfl
  rw [hNone] at hTy
  exact hTrans hTy

private theorem eo_prog_sets_is_empty_elim_eq_stuck_of_not_set_arg
    (a1 a2 : Term)
    (hNoSetArg : ∀ T0, a2 ≠ Term.Apply Term.Set T0) :
    __eo_prog_sets_is_empty_elim a1 a2 = Term.Stuck := by
  cases a2
  case Apply f x =>
    by_cases hSet : f = Term.Set
    · subst f
      exact False.elim (hNoSetArg x rfl)
    · by_cases hA1 : a1 = Term.Stuck
      · subst a1
        simp [__eo_prog_sets_is_empty_elim]
      · simp [__eo_prog_sets_is_empty_elim]
  all_goals
    by_cases hA1 : a1 = Term.Stuck
    · subst a1
      simp [__eo_prog_sets_is_empty_elim]
    · simp [__eo_prog_sets_is_empty_elim]

theorem cmd_step_sets_is_empty_elim_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_is_empty_elim args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_is_empty_elim args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_is_empty_elim args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sets_is_empty_elim args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      have hFalse : False := by
        change Term.Stuck ≠ Term.Stuck at hProg
        exact hProg rfl
      exact False.elim hFalse
  | cons a1 args =>
      cases args with
      | nil =>
          have hFalse : False := by
            change Term.Stuck ≠ Term.Stuck at hProg
            exact hProg rfl
          exact False.elim hFalse
      | cons a2 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  by_cases hSetArg : ∃ T0, a2 = Term.Apply Term.Set T0
                  · rcases hSetArg with ⟨T0, rfl⟩
                    change __eo_prog_sets_is_empty_elim a1 (Term.Apply Term.Set T0) ≠ Term.Stuck at hProg
                    have hSetArgTrans :
                        RuleProofs.eo_has_smt_translation (Term.Apply Term.Set T0) := by
                      simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.2.1
                    have hFalse : False := by
                      exact no_smt_translation_apply_set T0 hSetArgTrans
                    exact False.elim hFalse
                  · have hNoSetArg : ∀ T0, a2 ≠ Term.Apply Term.Set T0 := by
                      intro T0 hEq
                      exact hSetArg ⟨T0, hEq⟩
                    have hFalse : False := by
                      change __eo_prog_sets_is_empty_elim a1 a2 ≠ Term.Stuck at hProg
                      exact hProg (eo_prog_sets_is_empty_elim_eq_stuck_of_not_set_arg a1 a2 hNoSetArg)
                    exact False.elim hFalse
              | cons _ _ =>
                  have hFalse : False := by
                    change Term.Stuck ≠ Term.Stuck at hProg
                    exact hProg rfl
                  exact False.elim hFalse
          | cons _ _ =>
              have hFalse : False := by
                change Term.Stuck ≠ Term.Stuck at hProg
                exact hProg rfl
              exact False.elim hFalse
