import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def quant_unused_lhs (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def quant_unused_formula (Q x F G : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (quant_unused_lhs Q x F)) G

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  by_cases hxy : native_teq x y = true
  · by_cases hxOk : native_not (native_teq x Term.Stuck) = true
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite]
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite] at h
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

private theorem quant_unused_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = quant_unused_formula Q x F G ∧
      __mk_quant Q (__mk_quant_unused_vars_rec x F) F = G ∧
      __eo_prog_quant_unused_vars x1 = quant_unused_formula Q x F G := by
  intro hProg
  cases x1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhsArg with
                  | Apply qx F =>
                      cases qx with
                      | Apply Q x =>
                          let guard := __mk_quant Q (__mk_quant_unused_vars_rec x F) F
                          let formula := quant_unused_formula Q x F G
                          have hReq : __eo_requires guard G formula ≠ Term.Stuck := by
                            simpa [guard, formula, quant_unused_formula, quant_unused_lhs,
                              __eo_prog_quant_unused_vars] using hProg
                          have hGuard : guard = G :=
                            eo_requires_eq_of_ne_stuck guard G formula hReq
                          have hProgEq :
                              __eo_prog_quant_unused_vars (quant_unused_formula Q x F G) =
                                quant_unused_formula Q x F G := by
                            have hReqEq :
                                __eo_requires guard G formula = formula :=
                              eo_requires_eq_result_of_ne_stuck guard G formula hReq
                            simpa [guard, formula, quant_unused_formula, quant_unused_lhs,
                              __eo_prog_quant_unused_vars] using hReqEq
                          exact ⟨Q, x, F, G, rfl, hGuard, hProgEq⟩
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

private theorem quant_unused_has_translation_of_input
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    RuleProofs.eo_has_smt_translation (__eo_prog_quant_unused_vars x1) := by
  intro hTrans hProg
  rcases quant_unused_shape_of_not_stuck x1 hProg with
    ⟨Q, x, F, G, hx1, _hGuard, hProgEq⟩
  rw [hProgEq]
  simpa [hx1] using hTrans

private theorem typed___eo_prog_quant_unused_vars_impl
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_quant_unused_vars x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_quant_unused_vars x1) := by
  intro hTrans hProg hTy
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type
    (__eo_prog_quant_unused_vars x1)
    (quant_unused_has_translation_of_input x1 hTrans hProg)
    hTy

private theorem facts___eo_prog_quant_unused_vars_impl
    (M : SmtModel) (hM : model_total_typed M)
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_quant_unused_vars x1) = Term.Bool ->
    eo_interprets M (__eo_prog_quant_unused_vars x1) true := by
  intro hTrans hProg hTy
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
  have hProg : __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠ Term.Stuck :=
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
              have hTyQuant :
                  __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool at hResultTy
                simpa using hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_quant_unused_vars a1) true
                exact facts___eo_prog_quant_unused_vars_impl M hM a1 hTransA1
                  hProgQuant hTyQuant
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_quant_unused_vars_impl a1 hTransA1 hProgQuant hTyQuant)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
