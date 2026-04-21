import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem typed___eo_prog_re_star_emp :
  RuleProofs.eo_has_bool_type __eo_prog_re_star_emp := by
  change RuleProofs.eo_has_bool_type
    (Term.Apply
      (Term.Apply Term.eq
        (Term.Apply Term.re_mult (Term.Apply Term.str_to_re (Term.String ""))))
      (Term.Apply Term.str_to_re (Term.String "")))
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply Term.re_mult (Term.Apply Term.str_to_re (Term.String "")))
    (Term.Apply Term.str_to_re (Term.String ""))
    (by
      simp [__eo_to_smt.eq_def, __smtx_typeof, native_ite, native_Teq])
    (by
      simp [__eo_to_smt.eq_def, __smtx_typeof, native_ite, native_Teq])

private theorem facts___eo_prog_re_star_emp (M : SmtModel) :
  eo_interprets M __eo_prog_re_star_emp true := by
  change eo_interprets M
    (Term.Apply
      (Term.Apply Term.eq
        (Term.Apply Term.re_mult (Term.Apply Term.str_to_re (Term.String ""))))
      (Term.Apply Term.str_to_re (Term.String ""))) true
  apply RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply Term.re_mult (Term.Apply Term.str_to_re (Term.String "")))
    (Term.Apply Term.str_to_re (Term.String ""))
  · exact typed___eo_prog_re_star_emp
  · have hEvalEq :
        __smtx_model_eval M (__eo_to_smt (Term.Apply Term.re_mult (Term.Apply Term.str_to_re (Term.String "")))) =
          __smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_to_re (Term.String ""))) := by
      simp [__eo_to_smt.eq_def, __smtx_model_eval, __smtx_model_eval_re_mult,
        __smtx_model_eval_str_to_re, native_re_mult, native_re_mk_star, native_str_to_re,
        native_re_of_list, native_pack_string, native_unpack_string, native_pack_seq,
        native_unpack_seq, __smtx_ssm_char_values_of_string, __smtx_ssm_string_of_char_values]
    rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.str_to_re (Term.String ""))))

theorem cmd_step_re_star_emp_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_star_emp args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_star_emp args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_star_emp args premises) :=
by
  intro _hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.re_star_emp args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
            typed___eo_prog_re_star_emp⟩
          intro _hTrue
          exact facts___eo_prog_re_star_emp M
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
