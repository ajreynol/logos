import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Closed.UOpIndices

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def qquant (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def quantUnusedVarsFormula (Q x F G : Term) : Term :=
  qeq (qquant Q x F) G

private theorem eq_of_requires_same_not_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hxy : x = y
  · exact hxy
  · exfalso
    apply hReq
    simp [__eo_requires, native_ite, native_teq, hxy]

private theorem requires_same_eq_body
    {x y B : Term} :
    x = y ->
    x ≠ Term.Stuck ->
    __eo_requires x y B = B := by
  intro hxy hx
  subst y
  simp [__eo_requires, native_ite, native_teq, hx, native_not,
    SmtEval.native_not]

private theorem quant_unused_vars_shape_of_not_stuck
    (a1 : Term) :
    __eo_prog_quant_unused_vars a1 ≠ Term.Stuck ->
    ∃ Q x F G,
      a1 = quantUnusedVarsFormula Q x F G ∧
      __eo_prog_quant_unused_vars a1 =
        quantUnusedVarsFormula Q x F G ∧
      __mk_quant Q (__mk_quant_unused_vars_rec x F) F = G := by
  intro hProg
  cases a1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply qHead F =>
                      cases qHead with
                      | Apply Q x =>
                          have hReq :
                              __eo_requires
                                  (__mk_quant Q
                                    (__mk_quant_unused_vars_rec x F) F)
                                  G
                                  (quantUnusedVarsFormula Q x F G) ≠
                                Term.Stuck := by
                            simpa [quantUnusedVarsFormula, qeq, qquant,
                              __eo_prog_quant_unused_vars] using hProg
                          have hMkEq :
                              __mk_quant Q
                                  (__mk_quant_unused_vars_rec x F) F =
                                G :=
                            eq_of_requires_same_not_stuck hReq
                          have hMkNe :
                              __mk_quant Q
                                  (__mk_quant_unused_vars_rec x F) F ≠
                                Term.Stuck := by
                            intro hStuck
                            have hG : G = Term.Stuck := by
                              rw [← hMkEq, hStuck]
                            subst G
                            simp [hStuck, __eo_requires, native_ite,
                              native_teq, native_not,
                              SmtEval.native_not] at hReq
                          refine ⟨Q, x, F, G, rfl, ?_, hMkEq⟩
                          change __eo_prog_quant_unused_vars
                              (quantUnusedVarsFormula Q x F G) =
                            quantUnusedVarsFormula Q x F G
                          simpa [quantUnusedVarsFormula, qeq, qquant,
                            __eo_prog_quant_unused_vars,
                            requires_same_eq_body hMkEq hMkNe]
                      | _ =>
                          simp [__eo_prog_quant_unused_vars] at hProg
                  | _ =>
                      simp [__eo_prog_quant_unused_vars] at hProg
              | _ =>
                  simp [__eo_prog_quant_unused_vars] at hProg
          | _ =>
              simp [__eo_prog_quant_unused_vars] at hProg
      | _ =>
          simp [__eo_prog_quant_unused_vars] at hProg
  | _ =>
      simp [__eo_prog_quant_unused_vars] at hProg

private theorem smtx_model_eval_quant_unused_vars_mk
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (quantUnusedVarsFormula Q x F
          (__mk_quant Q (__mk_quant_unused_vars_rec x F) F)))
    (hSafe :
      NativeEoToSmtUOpIndicesSafe
        (quantUnusedVarsFormula Q x F
          (__mk_quant Q (__mk_quant_unused_vars_rec x F) F))) :
    __smtx_model_eval M (__eo_to_smt (qquant Q x F)) =
      __smtx_model_eval M
        (__eo_to_smt
          (__mk_quant Q (__mk_quant_unused_vars_rec x F) F)) := by
  sorry

theorem cmd_step_quant_unused_vars_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_unused_vars args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_unused_vars args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_unused_vars args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠
        Term.Stuck :=
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
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using
                  hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_unused_vars a1 ≠ Term.Stuck := by
                change __eo_prog_quant_unused_vars a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_unused_vars_shape_of_not_stuck a1 hProgQuant with
                ⟨Q, x, F, G, ha1, hProgEq, hMkEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (quantUnusedVarsFormula Q x F G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (quantUnusedVarsFormula Q x F G) =
                    Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (quantUnusedVarsFormula Q x F G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (quantUnusedVarsFormula Q x F G)
                  hTransFormula hFormulaType
              have hSafeFormula :
                  NativeEoToSmtUOpIndicesSafe
                    (quantUnusedVarsFormula Q x F G) :=
                eo_to_smt_well_typed_implies_uop_indices_safe
                  (quantUnusedVarsFormula Q x F G)
                  (by
                    simpa [RuleProofs.eo_has_smt_translation]
                      using hTransFormula)
              have hMkFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (quantUnusedVarsFormula Q x F
                      (__mk_quant Q (__mk_quant_unused_vars_rec x F) F)) := by
                simpa [hMkEq] using hFormulaBool
              have hMkSafeFormula :
                  NativeEoToSmtUOpIndicesSafe
                    (quantUnusedVarsFormula Q x F
                      (__mk_quant Q (__mk_quant_unused_vars_rec x F) F)) := by
                simpa [hMkEq] using hSafeFormula
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_unused_vars a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                  (qquant Q x F) G
                · exact hFormulaBool
                · rw [← hMkEq]
                  have hEval :=
                    smtx_model_eval_quant_unused_vars_mk
                      M hM Q x F hMkFormulaBool hMkSafeFormula
                  rw [hEval]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M
                      (__eo_to_smt
                        (__mk_quant Q
                          (__mk_quant_unused_vars_rec x F) F)))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_unused_vars a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
