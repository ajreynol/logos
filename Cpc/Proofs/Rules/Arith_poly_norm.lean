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

theorem facts___eo_prog_arith_poly_norm_impl
    (M : SmtModel) (hM : model_total_typed M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_arith_poly_norm a1) = Term.Bool ->
  eo_interprets M (__eo_prog_arith_poly_norm a1) true := by
  sorry

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
