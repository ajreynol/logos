import Cpc.Proofs.RuleSupport.ReInclusionSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem str_re_consume_translation_facts
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) ∧
      RuleProofs.eo_has_smt_translation side ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side) := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  rcases eq_operands_have_smt_translation_of_eq_has_smt_translation strIn
      side (by simpa [strIn] using hEqTrans) with
    ⟨hStrInTrans, hSideTrans⟩
  rcases str_in_re_args_smt_types_of_has_translation s r hStrInTrans with
    ⟨hSTy, hRTy⟩
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      simpa [strIn] using hEqTrans
    exact Smtm.eq_term_typeof_of_non_none hNN
  exact ⟨hStrInTrans, hSideTrans, hSTy, hRTy, by
    simpa [strIn] using hEqBool⟩

theorem str_re_consume_input_eval
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    ∃ ss rv,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) =
        SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hRTy, _hEqBool⟩
  have hSEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        SmtType.Seq SmtType.Char := by
    simpa [hSTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s) (by
        unfold term_has_non_none_type
        rw [hSTy]
        simp)
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases seq_value_canonical hSEvalTy with ⟨ss, hSEval⟩
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  refine ⟨ss, rv, hSEval, hREval, ?_⟩
  change __smtx_model_eval M
      (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
    SmtValue.Boolean (native_str_in_re (native_unpack_string ss) rv)
  simp [__smtx_model_eval, __smtx_model_eval_str_in_re, hSEval, hREval]

theorem str_re_consume_str_flatten_eval_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hFlatNe : __str_flatten (__str_nary_intro s) ≠ Term.Stuck) :
    ∃ ss flatSs,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M
          (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
        SmtValue.Seq flatSs ∧
      __smtx_typeof
          (__eo_to_smt (__str_flatten (__str_nary_intro s))) =
        SmtType.Seq SmtType.Char ∧
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro s)) =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel (SmtValue.Seq flatSs)
        (SmtValue.Seq ss) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, _hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨ss, _rv, hSEval, _hREval, _hStrInEval⟩
  rcases str_flatten_nary_intro_eval_rel M hM s ss hSTy hSEval
      hFlatNe with
    ⟨flatSs, hFlatEval, hFlatTy, hFlatList, hFlatRel⟩
  exact ⟨ss, flatSs, hSEval, hFlatEval, hFlatTy, hFlatList, hFlatRel⟩

theorem str_re_consume_side_smt_type
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    __smtx_typeof (__eo_to_smt side) = SmtType.Bool := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, hSTy, hRTy, _hEqBool⟩
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation strIn
      side (by simpa [strIn] using hEqTrans) with
    ⟨hSameTy, _hStrInNN⟩
  have hStrInTy :
      __smtx_typeof (__eo_to_smt strIn) = SmtType.Bool := by
    change __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
      SmtType.Bool
    rw [typeof_str_in_re_eq]
    simp [hSTy, hRTy, native_ite, native_Teq]
  rw [← hSameTy, hStrInTy]

theorem str_re_consume_side_eval_bool
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side)) :
    ∃ b,
      __smtx_model_eval M (__eo_to_smt side) =
        SmtValue.Boolean b := by
  have hSideTy := str_re_consume_side_smt_type s r side hEqTrans
  have hSideEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt side)) =
        SmtType.Bool := by
    simpa [hSideTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt side) (by
        unfold term_has_non_none_type
        rw [hSideTy]
        simp)
  exact bool_value_canonical hSideEvalTy

theorem str_re_consume_model_rel_of_side_eq_str_in_re
    (M : SmtModel) (s r side : Term)
    (hSideEq :
      side =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  subst side
  exact RuleProofs.smt_value_rel_refl _

theorem str_re_consume_model_rel_of_consume_identity
    (M : SmtModel) (s r side : Term)
    (hSide : side = __str_re_consume s r)
    (hIdentity :
      __str_re_consume s r =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  apply str_re_consume_model_rel_of_side_eq_str_in_re M s r side
  rw [hSide, hIdentity]

theorem str_re_consume_model_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s r side : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r))
          side))
    (hSide : side = __str_re_consume s r)
    (hSideNe : side ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)))
      (__smtx_model_eval M (__eo_to_smt side)) := by
  rcases str_re_consume_translation_facts s r side hEqTrans with
    ⟨_hStrInTrans, _hSideTrans, _hSTy, _hRTy, _hEqBool⟩
  rcases str_re_consume_input_eval M hM s r side hEqTrans with
    ⟨_ss, _rv, _hSEval, _hREval, _hStrInEval⟩
  rcases str_re_consume_side_eval_bool M hM s r side hEqTrans with
    ⟨_sideBool, _hSideEval⟩
  by_cases hIdentity :
      __str_re_consume s r =
        Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  · exact str_re_consume_model_rel_of_consume_identity M s r side hSide
      hIdentity
  sorry

private theorem str_in_re_consume_valid_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s r b : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b))
    (hProgNe :
      __eo_prog_str_in_re_consume
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b) ≠
        Term.Stuck) :
    StepRuleProperties M []
      (__eo_prog_str_in_re_consume
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r)) b)) := by
  let strIn := Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) s) r
  let side := __str_re_consume s r
  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) b
  change __eo_requires side b body ≠ Term.Stuck at hProgNe
  have hSideEqB : side = b :=
    eo_requires_eq_of_ne_stuck side b body hProgNe
  have hReqResult : __eo_requires side b body = body :=
    eo_requires_result_eq_of_ne_stuck side b body hProgNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side b body hProgNe
  subst b
  change StepRuleProperties M [] (__eo_requires side side body)
  rw [hReqResult]
  have hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    simpa [strIn, side, body] using hArgTrans
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side) := by
    unfold RuleProofs.eo_has_bool_type
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt strIn) (__eo_to_smt side)) := by
      unfold term_has_non_none_type
      change __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) strIn) side)) ≠
        SmtType.None
      exact hEqTrans
    exact Smtm.eq_term_typeof_of_non_none hNN
  have hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt strIn))
        (__smtx_model_eval M (__eo_to_smt side)) :=
    RuleProofs.str_re_consume_model_rel M hM s r side hEqTrans rfl hSideNe
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _
    (by simpa [strIn, side] using hEqBool)⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M strIn side hEqBool hRel

end RuleProofs

theorem cmd_step_str_in_re_consume_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_in_re_consume args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_in_re_consume args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_in_re_consume args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_in_re_consume args premises ≠ Term.Stuck :=
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
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp b =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply inApp r =>
                                  cases inApp with
                                  | Apply inOp str =>
                                      cases inOp with
                                      | UOp inOpName =>
                                          cases inOpName with
                                          | str_in_re =>
                                              have hProps :=
                                                RuleProofs.str_in_re_consume_valid_properties
                                                  M hM str r b (by
                                                    simpa using hA1Trans) (by
                                                    change
                                                      __eo_prog_str_in_re_consume
                                                        (Term.Apply
                                                          (Term.Apply (Term.UOp UserOp.eq)
                                                            (Term.Apply
                                                              (Term.Apply
                                                                (Term.UOp UserOp.str_in_re) str) r)) b) ≠
                                                        Term.Stuck at hProg
                                                    exact hProg)
                                              change StepRuleProperties M []
                                                (__eo_prog_str_in_re_consume
                                                  (Term.Apply
                                                    (Term.Apply (Term.UOp UserOp.eq)
                                                      (Term.Apply
                                                        (Term.Apply
                                                          (Term.UOp UserOp.str_in_re) str) r)) b))
                                              simpa [premiseTermList] using hProps
                                          | _ =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                      | _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
