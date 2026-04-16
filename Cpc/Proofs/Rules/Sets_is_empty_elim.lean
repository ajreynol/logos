import Cpc.Proofs.ArraySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

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
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  cases a2 with
                  | Apply f T0 =>
                      cases f with
                      | Set =>
                          have hXTrans : RuleProofs.eo_has_smt_translation a1 := by
                            simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
                          have hXTyRaw :
                              __smtx_typeof (__eo_to_smt a1) =
                                __eo_to_smt_type (__eo_typeof a1) :=
                            TranslationProofs.eo_to_smt_typeof_matches_translation a1 hXTrans
                          have hOutEqTy :
                              __eo_typeof_eq
                                (__eo_typeof (Term.Apply Term.set_is_empty a1))
                                (__eo_typeof
                                  (Term.Apply (Term.Apply Term.eq a1)
                                    (Term.set_empty (Term.Apply Term.Set T0)))) =
                                Term.Bool := by
                            change
                              __eo_typeof_eq
                                (__eo_typeof (Term.Apply Term.set_is_empty a1))
                                (__eo_typeof
                                  (Term.Apply (Term.Apply Term.eq a1)
                                    (Term.set_empty (Term.Apply Term.Set T0)))) =
                                Term.Bool at hResultTy
                            exact hResultTy
                          have hRhsNotStuck :
                              __eo_typeof
                                (Term.Apply (Term.Apply Term.eq a1)
                                  (Term.set_empty (Term.Apply Term.Set T0))) ≠
                                Term.Stuck :=
                            (RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                              (__eo_typeof (Term.Apply Term.set_is_empty a1))
                              (__eo_typeof
                                (Term.Apply (Term.Apply Term.eq a1)
                                  (Term.set_empty (Term.Apply Term.Set T0))))
                              hOutEqTy).2
                          have hReqNotStuck :
                              __eo_requires
                                (__eo_eq (__eo_typeof a1) (Term.Apply Term.Set T0))
                                (Term.Boolean true) Term.Bool ≠ Term.Stuck := by
                            change
                              __eo_typeof
                                (Term.Apply (Term.Apply Term.eq a1)
                                  (Term.set_empty (Term.Apply Term.Set T0))) ≠
                                Term.Stuck
                            exact hRhsNotStuck
                          have hXTy :
                              __eo_typeof a1 = Term.Apply Term.Set T0 := by
                            exact
                              (RuleProofs.eq_of_requires_eq_true_not_stuck
                                (__eo_typeof a1) (Term.Apply Term.Set T0) Term.Bool hReqNotStuck).symm
                          have hSetTyNonNone :
                              __eo_to_smt_type (Term.Apply Term.Set T0) ≠ SmtType.None := by
                            rw [← hXTy, ← hXTyRaw]
                            exact hXTrans
                          have hT0TyNonNone : __eo_to_smt_type T0 ≠ SmtType.None := by
                            intro hNone
                            apply hSetTyNonNone
                            simp [TranslationProofs.eo_to_smt_type_set, __smtx_typeof_guard,
                              native_ite, native_Teq, hNone]
                          have hXSetTy :
                              __smtx_typeof (__eo_to_smt a1) = SmtType.Set (__eo_to_smt_type T0) := by
                            rw [hXTyRaw, hXTy, TranslationProofs.eo_to_smt_type_set]
                            simp [__smtx_typeof_guard, native_ite, native_Teq, hT0TyNonNone]
                          let lhs := Term.Apply Term.set_is_empty a1
                          let rhs :=
                            Term.Apply (Term.Apply Term.eq a1)
                              (Term.set_empty (Term.Apply Term.Set T0))
                          have hToSmtLhs :
                              __eo_to_smt lhs =
                                SmtTerm.eq (__eo_to_smt a1)
                                  (SmtTerm.set_empty (SmtType.Set (__eo_to_smt_type T0))) := by
                            simp [lhs, __eo_to_smt.eq_def, hXSetTy]
                          have hToSmtRhs :
                              __eo_to_smt rhs =
                                SmtTerm.eq (__eo_to_smt a1)
                                  (SmtTerm.set_empty (SmtType.Set (__eo_to_smt_type T0))) := by
                            simp [rhs, __eo_to_smt.eq_def, TranslationProofs.eo_to_smt_set_empty,
                              TranslationProofs.eo_to_smt_type_set, __smtx_typeof_guard,
                              native_ite, native_Teq, hT0TyNonNone]
                          have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.Bool := by
                            rw [hToSmtLhs]
                            simp [__smtx_typeof, hXSetTy]
                          have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.Bool := by
                            rw [hToSmtRhs]
                            simp [__smtx_typeof, hXSetTy]
                          have hBoolEq :
                              RuleProofs.eo_has_bool_type
                                (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
                            exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
                              (by rw [hLhsTy, hRhsTy]) (by simpa [lhs] using hLhsTy)
                          have hBool :
                              RuleProofs.eo_has_bool_type
                                (__eo_prog_sets_is_empty_elim a1 (Term.Apply Term.Set T0)) := by
                            simpa [lhs, rhs, __eo_prog_sets_is_empty_elim] using hBoolEq
                          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hBool⟩
                          intro _hTrue
                          have hFactsEq :
                              eo_interprets M (Term.Apply (Term.Apply Term.eq lhs) rhs) true := by
                            apply RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBoolEq
                            have hToSmtEq :
                                __eo_to_smt lhs = __eo_to_smt rhs := by
                              rw [hToSmtLhs, hToSmtRhs]
                            rw [hToSmtEq]
                            exact RuleProofs.smt_value_rel_refl
                              (__smtx_model_eval M (__eo_to_smt rhs))
                          simpa [lhs, rhs, __eo_prog_sets_is_empty_elim] using hFactsEq
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
