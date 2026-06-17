import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def qterm (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def quantUnusedFormula (Q x F G : Term) : Term :=
  qeq (qterm Q x F) G

private theorem eq_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hEq : native_teq x y = true
  · simpa [native_teq] using hEq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    unfold __eo_requires at hReq
    simp [hEqFalse, native_ite] at hReq

private theorem body_ne_stuck_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    B ≠ Term.Stuck := by
  intro hReq hB
  subst B
  unfold __eo_requires at hReq
  by_cases hEq : native_teq x y = true
  · by_cases hStuck : native_teq x Term.Stuck = true
    · simp [hEq, hStuck, native_ite] at hReq
    · have hStuckFalse : native_teq x Term.Stuck = false := by
        cases h : native_teq x Term.Stuck <;> simp [h] at hStuck ⊢
      simp [hEq, hStuckFalse, native_ite] at hReq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    simp [hEqFalse, native_ite] at hReq

private theorem eo_or_eq_true_cases_local (x y : Term) :
    __eo_or x y = Term.Boolean true ->
    x = Term.Boolean true ∨ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_or] at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [native_or] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [__eo_requires, hNumNe, native_ite, native_teq] at h

private axiom smtx_model_eval_quant_unused_formula
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt G)

private theorem quant_unused_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = quantUnusedFormula Q x F G ∧
      (Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists) ∧
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false ∧
      __eo_prog_quant_unused_vars x1 = quantUnusedFormula Q x F G := by
  intro hProg
  cases x1 with
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
                          let v0 := qterm Q x F
                          let unused := __get_unused_vars v0 G
                          let inner :=
                            __eo_requires
                              (__contains_atomic_term_list_free_rec G unused
                                Term.__eo_List_nil)
                              (Term.Boolean false) (qeq v0 G)
                          have hReq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner ≠ Term.Stuck := by
                            simpa [quantUnusedFormula, qeq, qterm, v0, unused,
                              inner, __eo_prog_quant_unused_vars] using hProg
                          have hGuard :
                              __eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                  (__eo_eq Q (Term.UOp UserOp.exists)) =
                                Term.Boolean true :=
                            eq_of_requires_ne_stuck hReq
                          have hInnerNe : inner ≠ Term.Stuck :=
                            body_ne_stuck_of_requires_ne_stuck hReq
                          have hNoFree :
                              __contains_atomic_term_list_free_rec G unused
                                  Term.__eo_List_nil =
                                Term.Boolean false :=
                            eq_of_requires_ne_stuck hInnerNe
                          rcases eo_or_eq_true_cases_local
                              (__eo_eq Q (Term.UOp UserOp.forall))
                              (__eo_eq Q (Term.UOp UserOp.exists)) hGuard with
                            hForall | hExists
                          · have hQ : Q = Term.UOp UserOp.forall :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.forall) hForall).symm
                            subst Q
                            have hNoFree' :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (qterm (Term.UOp UserOp.forall) x F) G)
                                    Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [v0, unused, qterm] using hNoFree
                            have hNoFreeRaw :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (((Term.UOp UserOp.forall).Apply x).Apply F)
                                      G) Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [qterm] using hNoFree'
                            refine ⟨Term.UOp UserOp.forall, x, F, G, rfl,
                              Or.inl rfl, ?_, ?_⟩
                            · exact hNoFree'
                            · change __eo_prog_quant_unused_vars
                                (quantUnusedFormula (Term.UOp UserOp.forall)
                                  x F G) =
                                quantUnusedFormula (Term.UOp UserOp.forall)
                                  x F G
                              simp [quantUnusedFormula, qeq, qterm,
                                __eo_prog_quant_unused_vars, hGuard,
                                hNoFreeRaw,
                                __eo_requires, native_ite, native_teq,
                                native_not, SmtEval.native_not]
                          · have hQ : Q = Term.UOp UserOp.exists :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.exists) hExists).symm
                            subst Q
                            have hNoFree' :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (qterm (Term.UOp UserOp.exists) x F) G)
                                    Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [v0, unused, qterm] using hNoFree
                            have hNoFreeRaw :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (((Term.UOp UserOp.exists).Apply x).Apply F)
                                      G) Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [qterm] using hNoFree'
                            refine ⟨Term.UOp UserOp.exists, x, F, G, rfl,
                              Or.inr rfl, ?_, ?_⟩
                            · exact hNoFree'
                            · change __eo_prog_quant_unused_vars
                                (quantUnusedFormula (Term.UOp UserOp.exists)
                                  x F G) =
                                quantUnusedFormula (Term.UOp UserOp.exists)
                                  x F G
                              simp [quantUnusedFormula, qeq, qterm,
                                __eo_prog_quant_unused_vars, hGuard,
                                hNoFreeRaw,
                                __eo_requires, native_ite, native_teq,
                                native_not, SmtEval.native_not]
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
  have hProg : __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠
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
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_unused_vars a1 ≠ Term.Stuck := by
                change __eo_prog_quant_unused_vars a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_unused_shape_of_not_stuck a1 hProgQuant with
                ⟨Q, x, F, G, ha1, hQ, hNoFree, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (quantUnusedFormula Q x F G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (quantUnusedFormula Q x F G) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (quantUnusedFormula Q x F G) hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_quant_unused_vars a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M (qterm Q x F) G
                · exact hFormulaBool
                · have hEvalEq :=
                    smtx_model_eval_quant_unused_formula M hM Q x F G hQ
                      hNoFree hFormulaBool
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M (__eo_to_smt G))
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
