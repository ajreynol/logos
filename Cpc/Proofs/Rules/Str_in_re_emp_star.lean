module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_typeof_re_mult_eq_reglan_of_ne_stuck (T : Term)
    (h : __eo_typeof_re_mult T ≠ Term.Stuck) :
    T = Term.RegLan := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_typeof_re_mult] at h ⊢
  | _ =>
      simp [__eo_typeof_re_mult] at h

private theorem eo_typeof_str_in_re_args_of_ne_stuck (A B : Term)
    (h : __eo_typeof_str_in_re A B ≠ Term.Stuck) :
    A = Term.Apply Term.Seq Term.Char ∧ B = Term.RegLan := by
  cases A with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_in_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp at h ⊢
                cases B with
                | UOp opb =>
                    cases opb <;> simp at h ⊢
                | _ => simp at h
            | _ => simp at h
      | _ => simp [__eo_typeof_str_in_re] at h
  | _ => simp [__eo_typeof_str_in_re] at h

private abbrev lhs (r : Term) : Term :=
  Term.Apply (Term.Apply Term.str_in_re (Term.String []))
    (Term.Apply Term.re_mult r)

private abbrev conclusion (r : Term) : Term :=
  Term.Apply (Term.Apply Term.eq (lhs r)) (Term.Boolean true)

private theorem prog_eq (r : Term) (hRNotStuck : r ≠ Term.Stuck) :
    __eo_prog_str_in_re_emp_star r = conclusion r := by
  cases r <;>
    simp [__eo_prog_str_in_re_emp_star, conclusion, lhs] at hRNotStuck ⊢

private theorem typed_prog
    (r : Term)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hRTy : __eo_typeof r = Term.RegLan) :
    RuleProofs.eo_has_bool_type (__eo_prog_str_in_re_emp_star r) := by
  have hRNotStuck : r ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hRSmtTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hTy :=
      TranslationProofs.eo_to_smt_typeof_matches_translation r hRTrans
    rw [hRTy, TranslationProofs.eo_to_smt_type_reglan] at hTy
    exact hTy
  have hStarTy :
      __smtx_typeof (SmtTerm.re_mult (__eo_to_smt r)) = SmtType.RegLan := by
    rw [typeof_re_mult_eq]
    simp [hRSmtTy, native_ite, native_Teq]
  have hEmptyTy :
      __smtx_typeof (SmtTerm.String []) = SmtType.Seq SmtType.Char := by
    simp [__smtx_typeof, native_string_valid, native_ite]
  have hLhsTy : __smtx_typeof (__eo_to_smt (lhs r)) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_in_re (SmtTerm.String [])
          (SmtTerm.re_mult (__eo_to_smt r))) = SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hEmptyTy, hStarTy, native_ite, native_Teq]
  have hTrueTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean true)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
    simp [__smtx_typeof]
  rw [prog_eq r hRNotStuck]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (lhs r) (Term.Boolean true)
    (by rw [hLhsTy, hTrueTy]) (by rw [hLhsTy]; simp)

private theorem native_str_in_re_emp_star (r : SmtRegLan) :
    Smtm.native_str_in_re [] (native_re_mult r) = true := by
  cases r <;>
    simp [Smtm.native_str_in_re, native_re_str_valid, native_re_mult,
      native_re_nullable]

private theorem facts_prog
    (M : SmtModel) (hM : model_total_typed M) (r : Term)
    (hRTrans : RuleProofs.eo_has_smt_translation r)
    (hRTy : __eo_typeof r = Term.RegLan) :
    eo_interprets M (__eo_prog_str_in_re_emp_star r) true := by
  have hRNotStuck : r ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation r hRTrans
  have hRSmtTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := by
    have hTy :=
      TranslationProofs.eo_to_smt_typeof_matches_translation r hRTrans
    rw [hRTy, TranslationProofs.eo_to_smt_type_reglan] at hTy
    exact hTy
  have hEvalRTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRSmtTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRSmtTy]
        simp)
  rcases reglan_value_canonical hEvalRTy with ⟨rv, hEvalR⟩
  have hLhsEval :
      __smtx_model_eval M (__eo_to_smt (lhs r)) = SmtValue.Boolean true := by
    change __smtx_model_eval M
        (SmtTerm.str_in_re (SmtTerm.String [])
          (SmtTerm.re_mult (__eo_to_smt r))) = SmtValue.Boolean true
    simp [__smtx_model_eval, hEvalR, __smtx_model_eval_str_in_re,
      __smtx_model_eval_re_mult, native_pack_string, native_pack_seq,
      native_unpack_seq, native_str_in_re_emp_star]
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by
    change __smtx_model_eval M (SmtTerm.Boolean true) = SmtValue.Boolean true
    simp [__smtx_model_eval]
  rw [prog_eq r hRNotStuck]
  exact RuleProofs.eo_interprets_eq_of_rel M (lhs r) (Term.Boolean true)
    (by simpa [prog_eq r hRNotStuck] using typed_prog r hRTrans hRTy) <| by
      rw [hLhsEval, hTrueEval]
      exact RuleProofs.smt_value_rel_refl (SmtValue.Boolean true)

public theorem cmd_step_str_in_re_emp_star_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_emp_star args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_emp_star args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_emp_star args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_in_re_emp_star args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons r args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hRTrans : RuleProofs.eo_has_smt_translation r := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hRNotStuck : r ≠ Term.Stuck := by
                intro hStuck
                subst r
                apply hProg
                rfl
              have hProgEq :
                  __eo_cmd_step_proven s CRule.str_in_re_emp_star
                      (CArgList.cons r CArgList.nil) CIndexList.nil =
                    conclusion r := by
                exact prog_eq r hRNotStuck
              rw [hProgEq] at hResultTy
              change __eo_typeof_eq (__eo_typeof (lhs r))
                  (__eo_typeof (Term.Boolean true)) = Term.Bool at hResultTy
              have hLhsNotStuck : __eo_typeof (lhs r) ≠ Term.Stuck :=
                (by
                  intro hStuck
                  rw [hStuck] at hResultTy
                  simp [__eo_typeof_eq] at hResultTy)
              have hStarTy :
                  __eo_typeof (Term.Apply Term.re_mult r) = Term.RegLan := by
                have hArgs := eo_typeof_str_in_re_args_of_ne_stuck
                  (__eo_typeof (Term.String []))
                  (__eo_typeof (Term.Apply Term.re_mult r)) hLhsNotStuck
                exact hArgs.2
              have hRTy : __eo_typeof r = Term.RegLan := by
                have hStarNotStuck :
                    __eo_typeof_re_mult (__eo_typeof r) ≠ Term.Stuck := by
                  change __eo_typeof (Term.Apply Term.re_mult r) ≠ Term.Stuck
                  rw [hStarTy]
                  decide
                exact eo_typeof_re_mult_eq_reglan_of_ne_stuck
                  (__eo_typeof r) hStarNotStuck
              refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
                (typed_prog r hRTrans hRTy)⟩
              intro _hTrue
              exact facts_prog M hM r hRTrans hRTy
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
