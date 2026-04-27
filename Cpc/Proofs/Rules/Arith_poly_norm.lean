import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
TODO: the typing bridge is now local to this file, but the semantic bridge still
needs an arithmetic polynomial-normalization soundness lemma outside the main
TypePreservation development.  The command-level rule below intentionally
depends only on these small local bridges, so it does not pull in the full
TypePreservation proof.
-/
private theorem prog_arith_poly_norm_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_arith_poly_norm a1) = Term.Bool ->
  __eo_prog_arith_poly_norm a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_arith_poly_norm a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f b =>
      cases f with
      | Apply g a =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  let nA := __get_arith_poly_norm a
                  let nB := __get_arith_poly_norm b
                  have hReq :
                      __eo_requires nA nB
                        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ≠
                        Term.Stuck := by
                    simpa [__eo_prog_arith_poly_norm, nA, nB] using hProg
                  by_cases hEq : native_teq nA nB = true
                  · by_cases hSt : native_teq nA Term.Stuck = true
                    · exfalso
                      simpa [__eo_requires, hEq, hSt, native_ite, native_not,
                        SmtEval.native_not] using hReq
                    · have hNormEq : nA = nB := by
                        simpa [native_teq] using hEq
                      have hNormNotStuck : nA ≠ Term.Stuck := by
                        intro hNA
                        have hDec : native_teq nA Term.Stuck = true := by
                          simpa [hNA, native_teq] using rfl
                        exact hSt hDec
                      have hNormEq' :
                          __get_arith_poly_norm a = __get_arith_poly_norm b := by
                        simpa [nA, nB] using hNormEq
                      have hNormNotStuck' :
                          __get_arith_poly_norm a ≠ Term.Stuck := by
                        simpa [nA] using hNormNotStuck
                      have hNormNotStuckB' :
                          __get_arith_poly_norm b ≠ Term.Stuck := by
                        intro hNB
                        apply hNormNotStuck'
                        rw [hNormEq']
                        exact hNB
                      simpa [__eo_prog_arith_poly_norm, __eo_requires, hNormEq',
                        hNormNotStuck', hNormNotStuckB', native_ite, native_teq, native_not,
                        SmtEval.native_not]
                  · exfalso
                    simpa [__eo_requires, hEq, native_ite, native_not,
                      SmtEval.native_not] using hReq
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

private theorem eq_args_of_prog_arith_poly_norm_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_arith_poly_norm a1) = Term.Bool ->
  ∃ a b,
    a1 = Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b ∧
    __get_arith_poly_norm a = __get_arith_poly_norm b ∧
    __get_arith_poly_norm a ≠ Term.Stuck := by
  intro hTy
  have hProg : __eo_prog_arith_poly_norm a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  cases a1 with
  | Apply f b =>
      cases f with
      | Apply g a =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  let nA := __get_arith_poly_norm a
                  let nB := __get_arith_poly_norm b
                  have hReq :
                      __eo_requires nA nB
                        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ≠
                        Term.Stuck := by
                    simpa [__eo_prog_arith_poly_norm, nA, nB] using hProg
                  by_cases hEq : native_teq nA nB = true
                  · have hNormEq : nA = nB := by
                      simpa [native_teq] using hEq
                    by_cases hSt : native_teq nA Term.Stuck = true
                    · exfalso
                      simpa [__eo_requires, hEq, hSt, native_ite, native_not,
                        SmtEval.native_not] using hReq
                    · have hNormNotStuck : nA ≠ Term.Stuck := by
                        intro hNA
                        have hDec : native_teq nA Term.Stuck = true := by
                          simpa [hNA, native_teq] using rfl
                        exact hSt hDec
                      refine ⟨a, b, rfl, ?_, ?_⟩
                      · simpa [nA, nB] using hNormEq
                      · simpa [nA] using hNormNotStuck
                  · exfalso
                    simpa [__eo_requires, hEq, native_ite, native_not,
                      SmtEval.native_not] using hReq
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

theorem typed___eo_prog_arith_poly_norm_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_arith_poly_norm a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_arith_poly_norm a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_arith_poly_norm a1 = a1 :=
    prog_arith_poly_norm_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) =
          SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
      rw [__eo_to_smt.eq_def]
    rw [← hTranslate]
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

private theorem eq_operands_have_smt_translation_of_eq_has_smt_translation
    (x y : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  RuleProofs.eo_has_smt_translation x ∧
    RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation x y hTrans with
    ⟨hTy, hNonNone⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation] using hNonNone
  · simpa [RuleProofs.eo_has_smt_translation, hTy] using hNonNone

private theorem eq_operands_eval_same_smt_type_of_eq_has_smt_translation
    (M : SmtModel) (hM : model_total_typed M)
    (x y : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
    __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hTrans
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation x y hTrans with
    ⟨hTy, hNonNone⟩
  rcases eq_operands_have_smt_translation_of_eq_has_smt_translation x y hTrans with
    ⟨hXTrans, hYTrans⟩
  have hXPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt x) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
      (by simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation] using hXTrans)
  have hYPres :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
        __smtx_typeof (__eo_to_smt y) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt y)
      (by simpa [term_has_non_none_type, RuleProofs.eo_has_smt_translation] using hYTrans)
  calc
    __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt x) := hXPres
    _ = __smtx_typeof (__eo_to_smt y) := hTy
    _ = __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) := hYPres.symm

private theorem smt_value_rel_of_equal_arith_poly_norm
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  __get_arith_poly_norm a = __get_arith_poly_norm b ->
  __get_arith_poly_norm a ≠ Term.Stuck ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hEqTrans hNormEq _hNormNotStuck
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) :=
    eq_operands_eval_same_smt_type_of_eq_has_smt_translation M hM a b hEqTrans
  -- Remaining gap: show that equal arithmetic normal forms force equal numeric
  -- denotations for the original EO terms.
  sorry

theorem facts___eo_prog_arith_poly_norm_impl
    (M : SmtModel) (hM : model_total_typed M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_arith_poly_norm a1) = Term.Bool ->
  eo_interprets M (__eo_prog_arith_poly_norm a1) true := by
  intro hA1Trans hResultTy
  obtain ⟨a, b, rfl, hNormEq, hNormNotStuck⟩ :=
    eq_args_of_prog_arith_poly_norm_typeof_bool a1 hResultTy
  have hNormNotStuckB : __get_arith_poly_norm b ≠ Term.Stuck := by
    intro hNB
    apply hNormNotStuck
    rw [hNormEq]
    exact hNB
  have hProgEq :
      __eo_prog_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b := by
    simpa [__eo_prog_arith_poly_norm, __eo_requires, hNormEq, hNormNotStuck,
      hNormNotStuckB, native_ite, native_teq, native_not, SmtEval.native_not]
  have hEqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) = Term.Bool := by
    simpa [hProgEq] using hResultTy
  have hEqBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) hA1Trans hEqTy
  rw [hProgEq]
  exact RuleProofs.eo_interprets_eq_of_rel M a b hEqBool
    (smt_value_rel_of_equal_arith_poly_norm M hM a b hA1Trans hNormEq hNormNotStuck)

theorem cmd_step_arith_poly_norm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_poly_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_poly_norm args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_poly_norm args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.arith_poly_norm args premises ≠ Term.Stuck :=
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
              let A1 := a1
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons A1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation A1 := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_arith_poly_norm A1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_arith_poly_norm A1) true
                exact facts___eo_prog_arith_poly_norm_impl M hM A1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_arith_poly_norm A1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_arith_poly_norm A1)
                  (typed___eo_prog_arith_poly_norm_impl A1 hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
