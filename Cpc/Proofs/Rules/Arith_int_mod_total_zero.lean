import Cpc.Proofs.Rules.Support

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_mod_total_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.mod_total x) y) =
      SmtTerm.mod_total (__eo_to_smt x) (__eo_to_smt y) := by
  rw [__eo_to_smt.eq_def]

private theorem typeof_arg_of_prog_arith_int_mod_total_zero_bool
    (t1 : Term)
    (h : __eo_typeof (__eo_prog_arith_int_mod_total_zero t1) = Term.Bool) :
    __eo_typeof t1 = Term.Int := by
  cases hT1 : __eo_typeof t1 <;>
    simp [__eo_prog_arith_int_mod_total_zero, hT1] at h

private theorem eval_numeral (M : SmtModel) (n : Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral n)) = SmtValue.Numeral n := by
  rw [__eo_to_smt.eq_def]
  simp [__smtx_model_eval]

private theorem typed___eo_prog_arith_int_mod_total_zero_impl
    (t1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  __eo_typeof (__eo_prog_arith_int_mod_total_zero t1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_arith_int_mod_total_zero t1) := by
  intro hT1Trans hResultTy
  have hT1Ty : __eo_typeof t1 = Term.Int :=
    typeof_arg_of_prog_arith_int_mod_total_zero_bool t1 hResultTy
  have hSmtT1 : __smtx_typeof (__eo_to_smt t1) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 Term.Int (__eo_to_smt t1) rfl hT1Trans hT1Ty
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply Term.mod_total t1) (Term.Numeral 0))) =
        SmtType.Int := by
    rw [eo_to_smt_mod_total_eq]
    simp [__smtx_typeof, hSmtT1]
  have hLhsTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply Term.mod_total t1) (Term.Numeral 0)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLhsTy]
    simp
  change RuleProofs.eo_has_bool_type
    (Term.Apply
      (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod_total t1) (Term.Numeral 0)))
      t1)
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply Term.mod_total t1) (Term.Numeral 0)) t1
    (by rw [hLhsTy, hSmtT1]) hLhsTrans

private theorem facts___eo_prog_arith_int_mod_total_zero_impl
    (M : SmtModel) (hM : model_total_typed M) (t1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  __eo_typeof (__eo_prog_arith_int_mod_total_zero t1) = Term.Bool ->
  eo_interprets M (__eo_prog_arith_int_mod_total_zero t1) true := by
  intro hT1Trans hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_arith_int_mod_total_zero t1) :=
    typed___eo_prog_arith_int_mod_total_zero_impl t1 hT1Trans hResultTy
  have hT1Ty : __eo_typeof t1 = Term.Int :=
    typeof_arg_of_prog_arith_int_mod_total_zero_bool t1 hResultTy
  have hSmtT1 : __smtx_typeof (__eo_to_smt t1) = SmtType.Int :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 Term.Int (__eo_to_smt t1) rfl hT1Trans hT1Ty
  have hEvalT1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) = SmtType.Int :=
    smt_model_eval_preserves_type M hM (__eo_to_smt t1) SmtType.Int hSmtT1
      type_inhabited_int
  rcases int_value_canonical hEvalT1Ty with ⟨n, hEvalT1⟩
  have hEval0 :
      __smtx_model_eval M (__eo_to_smt (Term.Numeral 0)) = SmtValue.Numeral 0 :=
    eval_numeral M 0
  have hEvalLhs :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply Term.mod_total t1) (Term.Numeral 0))) =
        SmtValue.Numeral n := by
    rw [eo_to_smt_mod_total_eq]
    simp [__smtx_model_eval, hEvalT1, hEval0, __smtx_model_eval_mod_total]
    simp [SmtEval.smt_lit_mod_total]
  change eo_interprets M
    (Term.Apply
      (Term.Apply Term.eq (Term.Apply (Term.Apply Term.mod_total t1) (Term.Numeral 0)))
      t1)
    true
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply Term.mod_total t1) (Term.Numeral 0)) t1
    hProgBool <| by
      rw [hEvalLhs, hEvalT1]
      exact RuleProofs.smt_value_rel_refl (SmtValue.Numeral n)

theorem cmd_step_arith_int_mod_total_zero_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_int_mod_total_zero args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_cmd_step_proven s CRule.arith_int_mod_total_zero args premises ≠ Term.Stuck ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_int_mod_total_zero args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_int_mod_total_zero args premises) :=
by
  intro hCmdTrans _hPremisesBool hProg hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              let T1 := a1
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons T1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hT1Trans : RuleProofs.eo_has_smt_translation T1 := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_arith_int_mod_total_zero T1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_arith_int_mod_total_zero T1) true
                exact facts___eo_prog_arith_int_mod_total_zero_impl M hM T1 hT1Trans hResultTy
              · change RuleProofs.eo_has_bool_type (__eo_prog_arith_int_mod_total_zero T1)
                exact typed___eo_prog_arith_int_mod_total_zero_impl T1 hT1Trans hResultTy
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
