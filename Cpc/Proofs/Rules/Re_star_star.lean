import Cpc.Proofs.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem typed___eo_prog_re_star_star_impl
    (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.RegLan) :
  RuleProofs.eo_has_bool_type (__eo_prog_re_star_star a1) := by
  let lhs := Term.Apply Term.re_mult (Term.Apply Term.re_mult a1)
  let rhs := Term.Apply Term.re_mult a1
  have hA1SmtTy : __smtx_typeof (__eo_to_smt a1) = SmtType.RegLan := by
    have hTyRaw :
        __smtx_typeof (__eo_to_smt a1) = __eo_to_smt_type (__eo_typeof a1) :=
      TranslationProofs.eo_to_smt_typeof_matches_translation a1 hA1Trans
    rw [hA1Ty, TranslationProofs.eo_to_smt_type_reglan] at hTyRaw
    exact hTyRaw
  have hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.RegLan := by
    simp [lhs, __eo_to_smt.eq_def, __smtx_typeof, hA1SmtTy, native_ite, native_Teq]
  have hRhsTy : __smtx_typeof (__eo_to_smt rhs) = SmtType.RegLan := by
    simp [rhs, __eo_to_smt.eq_def, __smtx_typeof, hA1SmtTy, native_ite, native_Teq]
  have hBoolEq :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type lhs rhs
      (by rw [hLhsTy, hRhsTy]) (by simpa [lhs] using hLhsTy)
  simpa [lhs, rhs, __eo_prog_re_star_star] using hBoolEq

private theorem facts___eo_prog_re_star_star_impl
    (M : SmtModel) (a1 : Term)
    (hA1Trans : RuleProofs.eo_has_smt_translation a1)
    (hA1Ty : __eo_typeof a1 = Term.RegLan) :
  eo_interprets M (__eo_prog_re_star_star a1) true := by
  let lhs := Term.Apply Term.re_mult (Term.Apply Term.re_mult a1)
  let rhs := Term.Apply Term.re_mult a1
  have hBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq lhs) rhs) := by
    simpa [lhs, rhs, __eo_prog_re_star_star] using
      typed___eo_prog_re_star_star_impl a1 hA1Trans hA1Ty
  apply RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool
  cases hEval : __smtx_model_eval M (__eo_to_smt a1) with
  | RegLan r =>
      cases r <;>
        simp [RuleProofs.smt_value_rel, lhs, rhs, __eo_to_smt.eq_def, hEval,
          __smtx_model_eval, __smtx_model_eval_re_mult, native_re_mult,
          native_re_mk_star, native_veq]
  | _ =>
      simp [RuleProofs.smt_value_rel, lhs, rhs, __eo_to_smt.eq_def, hEval,
        __smtx_model_eval, __smtx_model_eval_re_mult, native_re_mult,
        native_re_mk_star, native_veq]

theorem cmd_step_re_star_star_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_star_star args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_star args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_star_star args premises ≠ Term.Stuck :=
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
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans.1
              have hA1Ty : __eo_typeof a1 = Term.RegLan := by
                cases hTy : __eo_typeof a1 <;>
                  simp [__eo_prog_re_star_star, hTy] at hResultTy
                exact hTy
              refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                (typed___eo_prog_re_star_star_impl a1 hA1Trans hA1Ty)⟩
              intro _hTrue
              exact facts___eo_prog_re_star_star_impl M a1 hA1Trans hA1Ty
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
