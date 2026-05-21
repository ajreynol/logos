import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.TypePreservation.CoreArith
import Cpc.Proofs.TypePreservation.Helpers

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
      rfl
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

private theorem smt_value_rel_numeral_eq
    {n1 n2 : native_Int} :
  RuleProofs.smt_value_rel (SmtValue.Numeral n1) (SmtValue.Numeral n2) ->
  n1 = n2 := by
  intro hRel
  simpa [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq] using hRel

private theorem smt_value_rel_rational_eq
    {q1 q2 : native_Rat} :
  RuleProofs.smt_value_rel (SmtValue.Rational q1) (SmtValue.Rational q2) ->
  q1 = q2 := by
  intro hRel
  simpa [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq] using hRel

private theorem smt_value_rel_model_eval_to_real_of_int_rel
    {n1 n2 : native_Int} :
  RuleProofs.smt_value_rel (SmtValue.Numeral n1) (SmtValue.Numeral n2) ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_to_real (SmtValue.Numeral n1))
    (__smtx_model_eval_to_real (SmtValue.Numeral n2)) := by
  intro hRel
  have hEq : n1 = n2 := smt_value_rel_numeral_eq hRel
  simpa [__smtx_model_eval_to_real, hEq] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_to_real (SmtValue.Numeral n1))

private theorem smt_value_rel_model_eval_to_real_of_real_rel
    {q1 q2 : native_Rat} :
  RuleProofs.smt_value_rel (SmtValue.Rational q1) (SmtValue.Rational q2) ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_to_real (SmtValue.Rational q1))
    (__smtx_model_eval_to_real (SmtValue.Rational q2)) := by
  intro hRel
  have hEq : q1 = q2 := smt_value_rel_rational_eq hRel
  simpa [__smtx_model_eval_to_real, hEq] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_to_real (SmtValue.Rational q1))

private theorem smt_value_rel_model_eval_uneg_of_int_rel
    {n1 n2 : native_Int} :
  RuleProofs.smt_value_rel (SmtValue.Numeral n1) (SmtValue.Numeral n2) ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_uneg (SmtValue.Numeral n1))
    (__smtx_model_eval_uneg (SmtValue.Numeral n2)) := by
  intro hRel
  have hEq : n1 = n2 := smt_value_rel_numeral_eq hRel
  simpa [__smtx_model_eval_uneg, hEq] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_uneg (SmtValue.Numeral n1))

private theorem smt_value_rel_model_eval_uneg_of_real_rel
    {q1 q2 : native_Rat} :
  RuleProofs.smt_value_rel (SmtValue.Rational q1) (SmtValue.Rational q2) ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_uneg (SmtValue.Rational q1))
    (__smtx_model_eval_uneg (SmtValue.Rational q2)) := by
  intro hRel
  have hEq : q1 = q2 := smt_value_rel_rational_eq hRel
  simpa [__smtx_model_eval_uneg, hEq] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_uneg (SmtValue.Rational q1))

private theorem smt_value_rel_model_eval_plus_of_int_rel
    {n1 n1' n2 n2' : native_Int} :
  RuleProofs.smt_value_rel (SmtValue.Numeral n1) (SmtValue.Numeral n1') ->
  RuleProofs.smt_value_rel (SmtValue.Numeral n2) (SmtValue.Numeral n2') ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_plus (SmtValue.Numeral n1) (SmtValue.Numeral n2))
    (__smtx_model_eval_plus (SmtValue.Numeral n1') (SmtValue.Numeral n2')) := by
  intro hRel1 hRel2
  have hEq1 : n1 = n1' := smt_value_rel_numeral_eq hRel1
  have hEq2 : n2 = n2' := smt_value_rel_numeral_eq hRel2
  simpa [__smtx_model_eval_plus, hEq1, hEq2] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_plus (SmtValue.Numeral n1) (SmtValue.Numeral n2))

private theorem smt_value_rel_model_eval_plus_of_real_rel
    {q1 q1' q2 q2' : native_Rat} :
  RuleProofs.smt_value_rel (SmtValue.Rational q1) (SmtValue.Rational q1') ->
  RuleProofs.smt_value_rel (SmtValue.Rational q2) (SmtValue.Rational q2') ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_plus (SmtValue.Rational q1) (SmtValue.Rational q2))
    (__smtx_model_eval_plus (SmtValue.Rational q1') (SmtValue.Rational q2')) := by
  intro hRel1 hRel2
  have hEq1 : q1 = q1' := smt_value_rel_rational_eq hRel1
  have hEq2 : q2 = q2' := smt_value_rel_rational_eq hRel2
  simpa [__smtx_model_eval_plus, hEq1, hEq2] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_plus (SmtValue.Rational q1) (SmtValue.Rational q2))

private theorem smt_value_rel_model_eval_sub_of_int_rel
    {n1 n1' n2 n2' : native_Int} :
  RuleProofs.smt_value_rel (SmtValue.Numeral n1) (SmtValue.Numeral n1') ->
  RuleProofs.smt_value_rel (SmtValue.Numeral n2) (SmtValue.Numeral n2') ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval__ (SmtValue.Numeral n1) (SmtValue.Numeral n2))
    (__smtx_model_eval__ (SmtValue.Numeral n1') (SmtValue.Numeral n2')) := by
  intro hRel1 hRel2
  have hEq1 : n1 = n1' := smt_value_rel_numeral_eq hRel1
  have hEq2 : n2 = n2' := smt_value_rel_numeral_eq hRel2
  simpa [__smtx_model_eval__, hEq1, hEq2] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval__ (SmtValue.Numeral n1) (SmtValue.Numeral n2))

private theorem smt_value_rel_model_eval_sub_of_real_rel
    {q1 q1' q2 q2' : native_Rat} :
  RuleProofs.smt_value_rel (SmtValue.Rational q1) (SmtValue.Rational q1') ->
  RuleProofs.smt_value_rel (SmtValue.Rational q2) (SmtValue.Rational q2') ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval__ (SmtValue.Rational q1) (SmtValue.Rational q2))
    (__smtx_model_eval__ (SmtValue.Rational q1') (SmtValue.Rational q2')) := by
  intro hRel1 hRel2
  have hEq1 : q1 = q1' := smt_value_rel_rational_eq hRel1
  have hEq2 : q2 = q2' := smt_value_rel_rational_eq hRel2
  simpa [__smtx_model_eval__, hEq1, hEq2] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval__ (SmtValue.Rational q1) (SmtValue.Rational q2))

private theorem smt_value_rel_model_eval_mult_of_int_rel
    {n1 n1' n2 n2' : native_Int} :
  RuleProofs.smt_value_rel (SmtValue.Numeral n1) (SmtValue.Numeral n1') ->
  RuleProofs.smt_value_rel (SmtValue.Numeral n2) (SmtValue.Numeral n2') ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_mult (SmtValue.Numeral n1) (SmtValue.Numeral n2))
    (__smtx_model_eval_mult (SmtValue.Numeral n1') (SmtValue.Numeral n2')) := by
  intro hRel1 hRel2
  have hEq1 : n1 = n1' := smt_value_rel_numeral_eq hRel1
  have hEq2 : n2 = n2' := smt_value_rel_numeral_eq hRel2
  simpa [__smtx_model_eval_mult, hEq1, hEq2] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_mult (SmtValue.Numeral n1) (SmtValue.Numeral n2))

private theorem smt_value_rel_model_eval_mult_of_real_rel
    {q1 q1' q2 q2' : native_Rat} :
  RuleProofs.smt_value_rel (SmtValue.Rational q1) (SmtValue.Rational q1') ->
  RuleProofs.smt_value_rel (SmtValue.Rational q2) (SmtValue.Rational q2') ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_mult (SmtValue.Rational q1) (SmtValue.Rational q2))
    (__smtx_model_eval_mult (SmtValue.Rational q1') (SmtValue.Rational q2')) := by
  intro hRel1 hRel2
  have hEq1 : q1 = q1' := smt_value_rel_rational_eq hRel1
  have hEq2 : q2 = q2' := smt_value_rel_rational_eq hRel2
  simpa [__smtx_model_eval_mult, hEq1, hEq2] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_mult (SmtValue.Rational q1) (SmtValue.Rational q2))

private theorem smt_value_rel_model_eval_qdiv_total_of_int_rel
    {n1 n1' n2 n2' : native_Int} :
  RuleProofs.smt_value_rel (SmtValue.Numeral n1) (SmtValue.Numeral n1') ->
  RuleProofs.smt_value_rel (SmtValue.Numeral n2) (SmtValue.Numeral n2') ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_qdiv_total (SmtValue.Numeral n1) (SmtValue.Numeral n2))
    (__smtx_model_eval_qdiv_total (SmtValue.Numeral n1') (SmtValue.Numeral n2')) := by
  intro hRel1 hRel2
  have hEq1 : n1 = n1' := smt_value_rel_numeral_eq hRel1
  have hEq2 : n2 = n2' := smt_value_rel_numeral_eq hRel2
  simpa [__smtx_model_eval_qdiv_total, hEq1, hEq2] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_qdiv_total (SmtValue.Numeral n1) (SmtValue.Numeral n2))

private theorem smt_value_rel_model_eval_qdiv_total_of_real_rel
    {q1 q1' q2 q2' : native_Rat} :
  RuleProofs.smt_value_rel (SmtValue.Rational q1) (SmtValue.Rational q1') ->
  RuleProofs.smt_value_rel (SmtValue.Rational q2) (SmtValue.Rational q2') ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_qdiv_total (SmtValue.Rational q1) (SmtValue.Rational q2))
    (__smtx_model_eval_qdiv_total (SmtValue.Rational q1') (SmtValue.Rational q2')) := by
  intro hRel1 hRel2
  have hEq1 : q1 = q1' := smt_value_rel_rational_eq hRel1
  have hEq2 : q2 = q2' := smt_value_rel_rational_eq hRel2
  simpa [__smtx_model_eval_qdiv_total, hEq1, hEq2] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_qdiv_total (SmtValue.Rational q1) (SmtValue.Rational q2))

private theorem smt_value_rel_model_eval_to_int_of_real_rel
    {q1 q2 : native_Rat} :
  RuleProofs.smt_value_rel (SmtValue.Rational q1) (SmtValue.Rational q2) ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval_to_int (SmtValue.Rational q1))
    (__smtx_model_eval_to_int (SmtValue.Rational q2)) := by
  intro hRel
  have hEq : q1 = q2 := smt_value_rel_rational_eq hRel
  simpa [__smtx_model_eval_to_int, hEq] using
    RuleProofs.smt_value_rel_refl
      (__smtx_model_eval_to_int (SmtValue.Rational q1))

private theorem smtx_model_eval_to_int_to_real_of_numeral
    (n : native_Int) :
  __smtx_model_eval_to_int (__smtx_model_eval_to_real (SmtValue.Numeral n)) =
    SmtValue.Numeral n := by
  change SmtValue.Numeral (Rat.floor ((n : Rat) / 1)) = SmtValue.Numeral n
  congr
  have hDiv : ((n : Rat) / 1 : Rat) = (n : Rat) := by
    change ((n : Rat) * ((1 : Rat)⁻¹)) = (n : Rat)
    rw [Rat.inv_def]
    change (n : Rat) * Rat.divInt 1 1 = (n : Rat)
    rw [show Rat.divInt 1 1 = (1 : Rat) by rfl]
    exact Rat.mul_one _
  rw [hDiv]
  exact Rat.floor_intCast n

private theorem smt_value_rel_to_int_to_real_of_numeral
    (n : native_Int) :
  RuleProofs.smt_value_rel
    (__smtx_model_eval_to_int (__smtx_model_eval_to_real (SmtValue.Numeral n)))
    (SmtValue.Numeral n) := by
  rw [smtx_model_eval_to_int_to_real_of_numeral]
  exact RuleProofs.smt_value_rel_refl (SmtValue.Numeral n)

private theorem smtx_model_eval_to_real_idempotent
    (v : SmtValue) :
  __smtx_model_eval_to_real (__smtx_model_eval_to_real v) =
    __smtx_model_eval_to_real v := by
  cases v <;> simp [__smtx_model_eval_to_real]

private noncomputable def arith_atom_denote_real (M : SmtModel) (t : Term) : SmtValue :=
  __smtx_model_eval_to_real (__smtx_model_eval M (__eo_to_smt t))

private noncomputable def arith_mvar_denote_real (M : SmtModel) : Term -> SmtValue
  | Term.__eo_List_nil => SmtValue.Rational (native_mk_rational 1 1)
  | Term.Apply (Term.Apply Term.__eo_List_cons a) rest =>
      __smtx_model_eval_mult (arith_atom_denote_real M a)
        (arith_mvar_denote_real M rest)
  | _ => SmtValue.NotValue

private noncomputable def arith_mon_denote_real (M : SmtModel) : Term -> SmtValue
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c) =>
      __smtx_model_eval_mult (SmtValue.Rational c) (arith_mvar_denote_real M vars)
  | _ => SmtValue.NotValue

private noncomputable def arith_poly_denote_real (M : SmtModel) : Term -> SmtValue
  | Term.UOp UserOp._at__at_Polynomial => SmtValue.Rational (native_mk_rational 0 1)
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p =>
      __smtx_model_eval_plus (arith_mon_denote_real M m) (arith_poly_denote_real M p)
  | _ => SmtValue.NotValue

private inductive arith_mvar_wf : Term -> Prop where
  | nil : arith_mvar_wf Term.__eo_List_nil
  | cons (a rest : Term) :
      arith_mvar_wf rest ->
      arith_mvar_wf (Term.Apply (Term.Apply Term.__eo_List_cons a) rest)

private inductive arith_mon_wf : Term -> Prop where
  | mk (vars : Term) (c : native_Rat) :
      arith_mvar_wf vars ->
      arith_mon_wf (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c))

private inductive arith_poly_wf : Term -> Prop where
  | zero : arith_poly_wf (Term.UOp UserOp._at__at_Polynomial)
  | cons (m p : Term) :
      arith_mon_wf m ->
      arith_poly_wf p ->
      arith_poly_wf (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p)

private theorem native_mk_rational_zero :
    native_mk_rational 0 1 = (0 : Rat) := by
  native_decide

private theorem native_mk_rational_one :
    native_mk_rational 1 1 = (1 : Rat) := by
  native_decide

private theorem rat_mkRat_one_eq_intCast
    (n : native_Int) :
  mkRat n 1 = (n : Rat) := by
  unfold mkRat
  simp
  rw [Rat.normalize_eq]
  simp

private theorem rat_div_one_intCast
    (n : native_Int) :
  ((n : Rat) / (1 : Rat)) = (n : Rat) := by
  change ((n : Rat) / ((1 : Int) : Rat)) = (n : Rat)
  rw [← Rat.divInt_eq_div n 1]
  change Rat.divInt n ((1 : Nat) : Int) = (n : Rat)
  rw [Rat.divInt_ofNat]
  exact rat_mkRat_one_eq_intCast n

private theorem arith_atom_denote_real_rational_or_notValue
    (M : SmtModel) (t : Term) :
  (∃ q, arith_atom_denote_real M t = SmtValue.Rational q) ∨
    arith_atom_denote_real M t = SmtValue.NotValue := by
  unfold arith_atom_denote_real
  cases hEval : __smtx_model_eval M (__eo_to_smt t) <;>
    simp [__smtx_model_eval_to_real]

private theorem arith_atom_denote_real_rational_of_smt_arith_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
  ∃ q, arith_atom_denote_real M t = SmtValue.Rational q := by
  have hNonNone : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rcases hTy with hTy | hTy <;> simp [hTy]
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hNonNone
  rcases hTy with hTy | hTy
  · have hEvalInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
      simpa [hTy] using hEvalTy
    rcases int_value_canonical hEvalInt with ⟨n, hEval⟩
    refine ⟨native_to_real n, ?_⟩
    simp [arith_atom_denote_real, hEval, __smtx_model_eval_to_real]
  · have hEvalReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Real := by
      simpa [hTy] using hEvalTy
    rcases real_value_canonical hEvalReal with ⟨q, hEval⟩
    exact ⟨q, by simp [arith_atom_denote_real, hEval, __smtx_model_eval_to_real]⟩

private inductive arith_mvar_rational (M : SmtModel) : Term -> Prop where
  | nil : arith_mvar_rational M Term.__eo_List_nil
  | cons (a rest : Term) :
      (∃ q, arith_atom_denote_real M a = SmtValue.Rational q) ->
      arith_mvar_rational M rest ->
      arith_mvar_rational M (Term.Apply (Term.Apply Term.__eo_List_cons a) rest)

private inductive arith_mon_rational (M : SmtModel) : Term -> Prop where
  | mk (vars : Term) (c : native_Rat) :
      arith_mvar_rational M vars ->
      arith_mon_rational M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c))

private inductive arith_poly_rational (M : SmtModel) : Term -> Prop where
  | zero : arith_poly_rational M (Term.UOp UserOp._at__at_Polynomial)
  | cons (m p : Term) :
      arith_mon_rational M m ->
      arith_poly_rational M p ->
      arith_poly_rational M (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p)

private theorem arith_mvar_rational_ne_stuck
    {M : SmtModel} {vars : Term}
    (hvars : arith_mvar_rational M vars) :
  vars ≠ Term.Stuck := by
  intro hSt
  cases hvars <;> cases hSt

private theorem arith_mon_rational_ne_stuck
    {M : SmtModel} {m : Term}
    (hm : arith_mon_rational M m) :
  m ≠ Term.Stuck := by
  intro hSt
  cases hm <;> cases hSt

private theorem arith_poly_rational_ne_stuck
    {M : SmtModel} {p : Term}
    (hp : arith_poly_rational M p) :
  p ≠ Term.Stuck := by
  intro hSt
  cases hp <;> cases hSt

private theorem arith_mvar_wf_of_rational
    {M : SmtModel} {vars : Term}
    (hvars : arith_mvar_rational M vars) :
  arith_mvar_wf vars := by
  induction hvars with
  | nil =>
      exact arith_mvar_wf.nil
  | cons a rest _ hRest ih =>
      exact arith_mvar_wf.cons a rest ih

private theorem arith_mon_wf_of_rational
    {M : SmtModel} {m : Term}
    (hm : arith_mon_rational M m) :
  arith_mon_wf m := by
  cases hm with
  | mk vars c hvars =>
      exact arith_mon_wf.mk vars c (arith_mvar_wf_of_rational hvars)

private theorem arith_poly_wf_of_rational
    {M : SmtModel} {p : Term}
    (hp : arith_poly_rational M p) :
  arith_poly_wf p := by
  induction hp with
  | zero =>
      exact arith_poly_wf.zero
  | cons m p hm hp ih =>
      exact arith_poly_wf.cons m p (arith_mon_wf_of_rational hm) ih

private theorem arith_mvar_denote_real_rational_of_rational_support
    (M : SmtModel) {vars : Term}
    (hvars : arith_mvar_rational M vars) :
  ∃ q, arith_mvar_denote_real M vars = SmtValue.Rational q := by
  induction hvars with
  | nil =>
      exact ⟨native_mk_rational 1 1, rfl⟩
  | cons a rest hA hRest ih =>
      rcases hA with ⟨qa, hA⟩
      rcases ih with ⟨qr, hRest⟩
      refine ⟨native_qmult qa qr, ?_⟩
      simp [arith_mvar_denote_real, hA, hRest, __smtx_model_eval_mult, native_qmult]

private theorem arith_mon_denote_real_rational_of_rational_support
    (M : SmtModel) {m : Term}
    (hm : arith_mon_rational M m) :
  ∃ q, arith_mon_denote_real M m = SmtValue.Rational q := by
  cases hm with
  | mk vars c hvars =>
      rcases arith_mvar_denote_real_rational_of_rational_support M hvars with ⟨qv, hVars⟩
      refine ⟨native_qmult c qv, ?_⟩
      simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, native_qmult]

private theorem arith_poly_denote_real_rational_of_rational_support
    (M : SmtModel) {p : Term}
    (hp : arith_poly_rational M p) :
  ∃ q, arith_poly_denote_real M p = SmtValue.Rational q := by
  induction hp with
  | zero =>
      exact ⟨native_mk_rational 0 1, rfl⟩
  | cons m p hm hp ih =>
      rcases arith_mon_denote_real_rational_of_rational_support M hm with ⟨qm, hMon⟩
      rcases ih with ⟨qp, hPoly⟩
      refine ⟨native_qplus qm qp, ?_⟩
      simp [arith_poly_denote_real, hMon, hPoly, __smtx_model_eval_plus, native_qplus]

private def arith_const_mon (q : native_Rat) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) Term.__eo_List_nil) (Term.Rational q)

private theorem arith_atom_ne_stuck_of_rational_support
    {M : SmtModel} {a : Term}
    (hA : ∃ q, arith_atom_denote_real M a = SmtValue.Rational q) :
  a ≠ Term.Stuck := by
  intro hSt
  subst a
  rcases hA with ⟨q, hA⟩
  unfold arith_atom_denote_real at hA
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl] at hA
  simp [__smtx_model_eval, __smtx_model_eval_to_real] at hA

private theorem mvar_mul_mvar_nil_left
    (vars : Term) :
  __mvar_mul_mvar Term.__eo_List_nil vars = vars := by
  cases vars <;> simp [__mvar_mul_mvar]

private theorem mvar_mul_mvar_nil_right
    (vars : Term) :
  __mvar_mul_mvar vars Term.__eo_List_nil = vars := by
  cases vars <;> simp [__mvar_mul_mvar]

private theorem mvar_mul_mvar_cons_cons_true
    (a1 rest1 c1 rest2 : Term)
    (hA1 : a1 ≠ Term.Stuck)
    (hC1 : c1 ≠ Term.Stuck)
    (hCmp : native_tcmp c1 a1 = true) :
  __mvar_mul_mvar
      (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1)
      (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) =
    __eo_mk_apply (Term.Apply Term.__eo_List_cons a1)
      (__mvar_mul_mvar rest1
        (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2)) := by
  simp [__mvar_mul_mvar, __eo_cmp, hA1, hC1, __eo_ite, native_ite, native_teq, hCmp,
    __eo_mk_apply]

private theorem mvar_mul_mvar_cons_cons_false
    (a1 rest1 c1 rest2 : Term)
    (hA1 : a1 ≠ Term.Stuck)
    (hC1 : c1 ≠ Term.Stuck)
    (hCmp : native_tcmp c1 a1 = false) :
  __mvar_mul_mvar
      (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1)
      (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) =
    __eo_mk_apply (Term.Apply Term.__eo_List_cons c1)
      (__mvar_mul_mvar
        (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) rest2) := by
  simp [__mvar_mul_mvar, __eo_cmp, hA1, hC1, __eo_ite, native_ite, native_teq, hCmp,
    __eo_mk_apply]

private theorem mon_mul_mon_of_const_left
    (q c : native_Rat) (vars : Term)
    (hVars : vars ≠ Term.Stuck) :
  __mon_mul_mon (arith_const_mon q)
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c)) =
    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
      (Term.Rational (native_qmult q c)) := by
  cases vars <;>
    simp [arith_const_mon, __mon_mul_mon, __mvar_mul_mvar, __eo_mk_apply, __eo_mul] at hVars ⊢

private theorem poly_of_mon_mul_mon_const_left
    (q c : native_Rat) (vars : Term)
    (hVars : vars ≠ Term.Stuck) :
  __eo_mk_apply
      (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
        (__mon_mul_mon (arith_const_mon q)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c))))
      (Term.UOp UserOp._at__at_Polynomial) =
    Term.Apply
      (Term.Apply (Term.UOp UserOp._at__at_poly)
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
          (Term.Rational (native_qmult q c))))
      (Term.UOp UserOp._at__at_Polynomial) := by
  rw [mon_mul_mon_of_const_left q c vars hVars]
  simp [__eo_mk_apply]

private theorem arith_poly_rational_of_poly_neg
    (M : SmtModel) {p : Term}
    (hp : arith_poly_rational M p) :
  arith_poly_rational M (__poly_neg p) := by
  induction hp with
  | zero =>
      simpa [__poly_neg] using arith_poly_rational.zero (M := M)
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hTail : __poly_neg p ≠ Term.Stuck :=
            arith_poly_rational_ne_stuck ih
          simpa [__poly_neg, __eo_mk_apply, __eo_neg, hTail] using
            (arith_poly_rational.cons
              (M := M)
              (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                (Term.Rational (native_qneg c)))
              (__poly_neg p)
              (arith_mon_rational.mk (M := M) vars (native_qneg c) hvars)
              ih)

private theorem arith_poly_rational_of_poly_add
    (M : SmtModel) {P1 P2 : Term}
    (h1 : arith_poly_rational M P1)
    (h2 : arith_poly_rational M P2) :
  arith_poly_rational M (__poly_add P1 P2) := by
  cases h1 with
  | zero =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using arith_poly_rational.zero (M := M)
      | @cons m2 p2 hm2 hp2 =>
          simpa [__poly_add] using arith_poly_rational.cons (M := M) m2 p2 hm2 hp2
  | @cons m1 p1 hm1 hp1 =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using arith_poly_rational.cons (M := M) m1 p1 hm1 hp1
      | @cons m2 p2 hm2 hp2 =>
          cases hm1 with
          | mk vars1 c1 hvars1 =>
              cases hm2 with
              | mk vars2 c2 hvars2 =>
                  have hVars1 : vars1 ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars1
                  have hVars2 : vars2 ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars2
                  by_cases hEq : vars1 = vars2
                  · subst vars2
                    have hRec : arith_poly_rational M (__poly_add p1 p2) :=
                      arith_poly_rational_of_poly_add M hp1 hp2
                    by_cases hZero : native_qplus c1 c2 = native_mk_rational 0 1
                    · have hZero' : native_mk_rational 0 1 = native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero'] using hRec
                    · have hTail : __poly_add p1 p2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck hRec
                      have hZero' : native_mk_rational 0 1 ≠ native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero', __eo_mk_apply, hTail] using
                        (arith_poly_rational.cons
                          (M := M)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational (native_qplus c1 c2)))
                          (__poly_add p1 p2)
                          (arith_mon_rational.mk (M := M) vars1 (native_qplus c1 c2) hvars1)
                          hRec)
                  · have hEq' : vars2 ≠ vars1 := by
                        simpa [eq_comm] using hEq
                    by_cases hCmp : native_tcmp vars2 vars1
                    · have hRec : arith_poly_rational M
                            (__poly_add p1
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                    (Term.Rational c2)))
                                p2)) :=
                          arith_poly_rational_of_poly_add M hp1
                            (arith_poly_rational.cons
                              (M := M)
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                (Term.Rational c2))
                              p2
                              (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                              hp2)
                      have hTail :
                          __poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational c2)))
                              p2) ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail] using
                        (arith_poly_rational.cons
                          (M := M)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational c1))
                          (__poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational c2)))
                              p2))
                          (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                          hRec)
                    · have hRec : arith_poly_rational M
                            (__poly_add
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                    (Term.Rational c1)))
                                p1)
                              p2) :=
                          arith_poly_rational_of_poly_add M
                            (arith_poly_rational.cons
                              (M := M)
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                (Term.Rational c1))
                              p1
                              (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                              hp1)
                            hp2
                      have hTail :
                          __poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational c1)))
                              p1)
                            p2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail] using
                        (arith_poly_rational.cons
                          (M := M)
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                            (Term.Rational c2))
                          (__poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational c1)))
                              p1)
                            p2)
                          (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                          hRec)
termination_by sizeOf P1 + sizeOf P2
decreasing_by
  simp_wf
  · omega
  · have hSize :
        sizeOf p1 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational c1)))
              p1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf p2 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational c2)))
              p2) := by
        simp
        omega
    omega

private theorem arith_poly_rational_of_poly_mul_mon_const
    (M : SmtModel) (q : native_Rat) {p : Term}
    (hp : arith_poly_rational M p) :
  arith_poly_rational M (__poly_mul_mon (arith_const_mon q) p) := by
  induction hp with
  | zero =>
      simpa [arith_const_mon, __poly_mul_mon] using arith_poly_rational.zero (M := M)
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hVars : vars ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars
          have hHead :
              arith_poly_rational M
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at__at_poly)
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                      (Term.Rational (native_qmult q c))))
                  (Term.UOp UserOp._at__at_Polynomial)) := by
            exact arith_poly_rational.cons
              (M := M)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                (Term.Rational (native_qmult q c)))
              (Term.UOp UserOp._at__at_Polynomial)
              (arith_mon_rational.mk (M := M) vars (native_qmult q c) hvars)
              (arith_poly_rational.zero (M := M))
          change arith_poly_rational M
            (__poly_add
              (__eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
                  (__mon_mul_mon (arith_const_mon q)
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                      (Term.Rational c))))
                (Term.UOp UserOp._at__at_Polynomial))
              (__poly_mul_mon (arith_const_mon q) p))
          rw [poly_of_mon_mul_mon_const_left q c vars hVars]
          exact arith_poly_rational_of_poly_add M hHead ih

private theorem arith_mvar_rational_of_mvar_mul_mvar
    (M : SmtModel) {vars1 vars2 : Term}
    (hvars1 : arith_mvar_rational M vars1)
    (hvars2 : arith_mvar_rational M vars2) :
  arith_mvar_rational M (__mvar_mul_mvar vars1 vars2) := by
  cases hvars1 with
  | nil =>
      rw [mvar_mul_mvar_nil_left]
      exact hvars2
  | cons a1 rest1 hA1 hRest1 =>
      cases hvars2 with
      | nil =>
          rw [mvar_mul_mvar_nil_right]
          exact arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1
      | cons c1 rest2 hC1 hRest2 =>
          have hA1NotStuck : a1 ≠ Term.Stuck :=
            arith_atom_ne_stuck_of_rational_support hA1
          have hC1NotStuck : c1 ≠ Term.Stuck :=
            arith_atom_ne_stuck_of_rational_support hC1
          by_cases hCmp : native_tcmp c1 a1 = true
          · have hTail :
                __mvar_mul_mvar rest1
                  (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) ≠ Term.Stuck :=
              arith_mvar_rational_ne_stuck
                (arith_mvar_rational_of_mvar_mul_mvar M hRest1
                  (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2))
            rw [mvar_mul_mvar_cons_cons_true a1 rest1 c1 rest2 hA1NotStuck hC1NotStuck hCmp]
            simpa [__eo_mk_apply, hTail] using
              (arith_mvar_rational.cons (M := M) a1
                (__mvar_mul_mvar rest1
                  (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2))
                hA1
                (arith_mvar_rational_of_mvar_mul_mvar M hRest1
                  (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2)))
          · have hCmp' : native_tcmp c1 a1 = false := by
              cases hT : native_tcmp c1 a1 with
              | false =>
                  rfl
              | true =>
                  exfalso
                  exact hCmp hT
            have hTail :
                __mvar_mul_mvar
                  (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) rest2 ≠ Term.Stuck :=
              arith_mvar_rational_ne_stuck
                (arith_mvar_rational_of_mvar_mul_mvar M
                  (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1) hRest2)
            rw [mvar_mul_mvar_cons_cons_false a1 rest1 c1 rest2 hA1NotStuck hC1NotStuck hCmp']
            simpa [__eo_mk_apply, hTail] using
              (arith_mvar_rational.cons (M := M) c1
                (__mvar_mul_mvar
                  (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) rest2)
                hC1
                (arith_mvar_rational_of_mvar_mul_mvar M
                  (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1) hRest2))
termination_by sizeOf vars1 + sizeOf vars2
decreasing_by
  simp_wf
  · have hSize :
        sizeOf rest1 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf rest2 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) := by
        simp
        omega
    omega

private theorem arith_mon_rational_of_mon_mul_mon
    (M : SmtModel) {m1 m2 : Term}
    (hm1 : arith_mon_rational M m1)
    (hm2 : arith_mon_rational M m2) :
  arith_mon_rational M (__mon_mul_mon m1 m2) := by
  cases hm1 with
  | mk vars1 c1 hvars1 =>
      cases hm2 with
      | mk vars2 c2 hvars2 =>
          have hVars :
              __mvar_mul_mvar vars1 vars2 ≠ Term.Stuck :=
            arith_mvar_rational_ne_stuck
              (arith_mvar_rational_of_mvar_mul_mvar M hvars1 hvars2)
          rw [show __mon_mul_mon
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1) (Term.Rational c1))
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2) (Term.Rational c2)) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_mon) (__mvar_mul_mvar vars1 vars2))
                    (Term.Rational (native_qmult c1 c2)) by
                simp [__mon_mul_mon, __eo_mul, __eo_mk_apply, hVars]]
          exact arith_mon_rational.mk (M := M) (__mvar_mul_mvar vars1 vars2)
            (native_qmult c1 c2) (arith_mvar_rational_of_mvar_mul_mvar M hvars1 hvars2)

private theorem arith_poly_rational_of_poly_mul_mon
    (M : SmtModel) {m p : Term}
    (hm : arith_mon_rational M m)
    (hp : arith_poly_rational M p) :
  arith_poly_rational M (__poly_mul_mon m p) := by
  have hMNe : m ≠ Term.Stuck := arith_mon_rational_ne_stuck hm
  induction hp with
  | zero =>
      simpa [__poly_mul_mon, hMNe] using arith_poly_rational.zero (M := M)
  | @cons m2 p2 hm2 hp2 ih =>
      have hMul : arith_mon_rational M (__mon_mul_mon m m2) :=
        arith_mon_rational_of_mon_mul_mon M hm hm2
      have hMulNe : __mon_mul_mon m m2 ≠ Term.Stuck :=
        arith_mon_rational_ne_stuck hMul
      have hHead :
          arith_poly_rational M
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
              (Term.UOp UserOp._at__at_Polynomial)) := by
        simpa [__eo_mk_apply, hMulNe] using
          (arith_poly_rational.cons
            (M := M)
            (__mon_mul_mon m m2)
            (Term.UOp UserOp._at__at_Polynomial)
            hMul
            (arith_poly_rational.zero (M := M)))
      simpa [__poly_mul_mon, hMNe] using arith_poly_rational_of_poly_add M hHead ih

private theorem arith_poly_rational_of_poly_mul
    (M : SmtModel) {p1 p2 : Term}
    (hp1 : arith_poly_rational M p1)
    (hp2 : arith_poly_rational M p2) :
  arith_poly_rational M (__poly_mul p1 p2) := by
  have hP2Ne : p2 ≠ Term.Stuck := arith_poly_rational_ne_stuck hp2
  induction hp1 with
  | zero =>
      simpa [__poly_mul, hP2Ne] using arith_poly_rational.zero (M := M)
  | @cons m p1 hm hp1 ih =>
      simpa [__poly_mul, hP2Ne] using
        arith_poly_rational_of_poly_add M
          (arith_poly_rational_of_poly_mul_mon M hm hp2)
          ih

private theorem arith_mvar_denote_real_rational_or_notValue
    (M : SmtModel) (vars : Term) :
  (∃ q, arith_mvar_denote_real M vars = SmtValue.Rational q) ∨
    arith_mvar_denote_real M vars = SmtValue.NotValue := by
  cases vars with
  | __eo_List_nil =>
      exact Or.inl ⟨native_mk_rational 1 1, rfl⟩
  | Apply f rest =>
      cases f with
      | Apply g a =>
          cases g with
          | __eo_List_cons =>
              rcases arith_atom_denote_real_rational_or_notValue M a with hA | hA
              · rcases hA with ⟨qa, hA⟩
                rcases arith_mvar_denote_real_rational_or_notValue M rest with hRest | hRest
                · rcases hRest with ⟨qr, hRest⟩
                  refine Or.inl ?_
                  refine ⟨native_qmult qa qr, ?_⟩
                  simp [arith_mvar_denote_real, hA, hRest, __smtx_model_eval_mult, native_qmult]
                · exact Or.inr (by
                    simp [arith_mvar_denote_real, hA, hRest, __smtx_model_eval_mult])
              · exact Or.inr (by
                  simp [arith_mvar_denote_real, hA, __smtx_model_eval_mult])
          | _ =>
              exact Or.inr rfl
      | _ =>
          exact Or.inr rfl
  | _ =>
      exact Or.inr rfl
termination_by sizeOf vars
decreasing_by
  simp_wf
  all_goals omega

private theorem arith_mon_denote_real_rational_or_notValue
    (M : SmtModel) (m : Term) :
  (∃ q, arith_mon_denote_real M m = SmtValue.Rational q) ∨
    arith_mon_denote_real M m = SmtValue.NotValue := by
  cases m with
  | Apply f c =>
      cases f with
      | Apply g vars =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_mon =>
                  cases c with
                  | Rational q =>
                      rcases arith_mvar_denote_real_rational_or_notValue M vars with hVars | hVars
                      · rcases hVars with ⟨qv, hVars⟩
                        refine Or.inl ?_
                        refine ⟨native_qmult q qv, ?_⟩
                        simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, native_qmult]
                      · exact Or.inr (by
                          simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult])
                  | _ =>
                      exact Or.inr rfl
              | _ =>
                  exact Or.inr rfl
          | _ =>
              exact Or.inr rfl
      | _ =>
          exact Or.inr rfl
  | _ =>
      exact Or.inr rfl

private theorem arith_poly_denote_real_rational_or_notValue
    (M : SmtModel) (p : Term) :
  (∃ q, arith_poly_denote_real M p = SmtValue.Rational q) ∨
    arith_poly_denote_real M p = SmtValue.NotValue := by
  cases p with
  | UOp op =>
      cases op with
      | _at__at_Polynomial =>
          exact Or.inl ⟨native_mk_rational 0 1, rfl⟩
      | _ =>
          exact Or.inr rfl
  | Apply f tail =>
      cases f with
      | Apply g m =>
          cases g with
          | UOp op =>
              cases op with
              | _at__at_poly =>
                  rcases arith_mon_denote_real_rational_or_notValue M m with hMon | hMon
                  · rcases hMon with ⟨qm, hMon⟩
                    rcases arith_poly_denote_real_rational_or_notValue M tail with hPoly | hPoly
                    · rcases hPoly with ⟨qp, hPoly⟩
                      refine Or.inl ?_
                      refine ⟨native_qplus qm qp, ?_⟩
                      simp [arith_poly_denote_real, hMon, hPoly, __smtx_model_eval_plus, native_qplus]
                    · exact Or.inr (by
                        simp [arith_poly_denote_real, hMon, hPoly, __smtx_model_eval_plus])
                  · exact Or.inr (by
                      simp [arith_poly_denote_real, hMon, __smtx_model_eval_plus])
              | _ =>
                  exact Or.inr rfl
          | _ =>
              exact Or.inr rfl
      | _ =>
          exact Or.inr rfl
  | _ =>
      exact Or.inr rfl
termination_by sizeOf p
decreasing_by
  simp_wf
  all_goals omega

private theorem smtx_model_eval_plus_zero_left_of_rational_or_notValue
    {v : SmtValue}
    (hv : (∃ q, v = SmtValue.Rational q) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_plus (SmtValue.Rational (native_mk_rational 0 1)) v = v := by
  rcases hv with ⟨q, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, native_qplus, native_mk_rational_zero, Rat.zero_add]

private theorem smtx_model_eval_plus_zero_right_of_rational_or_notValue
    {v : SmtValue}
    (hv : (∃ q, v = SmtValue.Rational q) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_plus v (SmtValue.Rational (native_mk_rational 0 1)) = v := by
  rcases hv with ⟨q, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, native_qplus, native_mk_rational_zero, Rat.add_zero]

private theorem smtx_model_eval_mult_one_left_of_rational_or_notValue
    {v : SmtValue}
    (hv : (∃ q, v = SmtValue.Rational q) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_mult (SmtValue.Rational (native_mk_rational 1 1)) v = v := by
  rcases hv with ⟨q, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, native_qmult, native_mk_rational_one]

private theorem smtx_model_eval_mult_one_right_of_rational_or_notValue
    {v : SmtValue}
    (hv : (∃ q, v = SmtValue.Rational q) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_mult v (SmtValue.Rational (native_mk_rational 1 1)) = v := by
  rcases hv with ⟨q, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, native_qmult, native_mk_rational_one]

private theorem smtx_model_eval_plus_uneg_of_rational_or_notValue
    {v1 v2 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_plus (__smtx_model_eval_uneg v1) (__smtx_model_eval_uneg v2) =
    __smtx_model_eval_uneg (__smtx_model_eval_plus v1 v2) := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;> rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, __smtx_model_eval_uneg, native_qplus, native_qneg,
      Rat.neg_add]

private theorem smtx_model_eval_plus_comm_of_rational_or_notValue
    {v1 v2 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_plus v1 v2 = __smtx_model_eval_plus v2 v1 := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;> rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, native_qplus, Rat.add_comm]

private theorem smtx_model_eval_plus_assoc_of_rational_or_notValue
    {v1 v2 v3 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue)
    (h3 : (∃ q, v3 = SmtValue.Rational q) ∨ v3 = SmtValue.NotValue) :
  __smtx_model_eval_plus (__smtx_model_eval_plus v1 v2) v3 =
    __smtx_model_eval_plus v1 (__smtx_model_eval_plus v2 v3) := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;>
    rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    rcases h3 with ⟨q3, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_plus, native_qplus, Rat.add_assoc]

private theorem smtx_model_eval_mult_comm_of_rational_or_notValue
    {v1 v2 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_mult v1 v2 = __smtx_model_eval_mult v2 v1 := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;> rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, native_qmult, Rat.mul_comm]

private theorem smtx_model_eval_mult_assoc_of_rational_or_notValue
    {v1 v2 v3 : SmtValue}
    (h1 : (∃ q, v1 = SmtValue.Rational q) ∨ v1 = SmtValue.NotValue)
    (h2 : (∃ q, v2 = SmtValue.Rational q) ∨ v2 = SmtValue.NotValue)
    (h3 : (∃ q, v3 = SmtValue.Rational q) ∨ v3 = SmtValue.NotValue) :
  __smtx_model_eval_mult (__smtx_model_eval_mult v1 v2) v3 =
    __smtx_model_eval_mult v1 (__smtx_model_eval_mult v2 v3) := by
  rcases h1 with ⟨q1, rfl⟩ | rfl <;>
    rcases h2 with ⟨q2, rfl⟩ | rfl <;>
    rcases h3 with ⟨q3, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, native_qmult, Rat.mul_assoc]

private theorem smtx_model_eval_mult_neg_left_of_rational_or_notValue
    (q : native_Rat) {v : SmtValue}
    (hv : (∃ qv, v = SmtValue.Rational qv) ∨ v = SmtValue.NotValue) :
  __smtx_model_eval_mult (SmtValue.Rational (native_qneg q)) v =
    __smtx_model_eval_uneg (__smtx_model_eval_mult (SmtValue.Rational q) v) := by
  rcases hv with ⟨qv, rfl⟩ | rfl <;>
    simp [__smtx_model_eval_mult, __smtx_model_eval_uneg, native_qmult, native_qneg,
      Rat.neg_mul]

private theorem smtx_model_eval_mult_rational_left_distrib_plus_of_rational_or_notValue
    (q : native_Rat) (v1 v2 : SmtValue)
    (hv1 : (∃ q1, v1 = SmtValue.Rational q1) ∨ v1 = SmtValue.NotValue)
    (hv2 : (∃ q2, v2 = SmtValue.Rational q2) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_plus
      (__smtx_model_eval_mult (SmtValue.Rational q) v1)
      (__smtx_model_eval_mult (SmtValue.Rational q) v2) =
    __smtx_model_eval_mult
      (SmtValue.Rational q)
      (__smtx_model_eval_plus v1 v2) := by
  rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
  · rcases h1 with ⟨q1, rfl⟩
    rcases h2 with ⟨q2, rfl⟩
    simp [__smtx_model_eval_mult, __smtx_model_eval_plus, native_qmult, native_qplus,
      Rat.mul_add]
  · rcases h1 with ⟨q1, rfl⟩
    simp [h2, __smtx_model_eval_mult, __smtx_model_eval_plus]
  · rcases h2 with ⟨q2, rfl⟩
    simp [h1, __smtx_model_eval_mult, __smtx_model_eval_plus]
  · simp [h1, h2, __smtx_model_eval_mult, __smtx_model_eval_plus]

private theorem smtx_model_eval_mult_rational_right_distrib_plus_of_rational_or_notValue
    (q : native_Rat) (v1 v2 : SmtValue)
    (hv1 : (∃ q1, v1 = SmtValue.Rational q1) ∨ v1 = SmtValue.NotValue)
    (hv2 : (∃ q2, v2 = SmtValue.Rational q2) ∨ v2 = SmtValue.NotValue) :
  __smtx_model_eval_plus
      (__smtx_model_eval_mult v1 (SmtValue.Rational q))
      (__smtx_model_eval_mult v2 (SmtValue.Rational q)) =
    __smtx_model_eval_mult
      (__smtx_model_eval_plus v1 v2)
      (SmtValue.Rational q) := by
  rcases hv1 with h1 | h1 <;> rcases hv2 with h2 | h2
  · rcases h1 with ⟨q1, rfl⟩
    rcases h2 with ⟨q2, rfl⟩
    simp [__smtx_model_eval_mult, __smtx_model_eval_plus, native_qmult, native_qplus,
      Rat.add_mul]
  · rcases h1 with ⟨q1, rfl⟩
    simp [h2, __smtx_model_eval_mult, __smtx_model_eval_plus]
  · rcases h2 with ⟨q2, rfl⟩
    simp [h1, __smtx_model_eval_mult, __smtx_model_eval_plus]
  · simp [h1, h2, __smtx_model_eval_mult, __smtx_model_eval_plus]

private theorem arith_mon_denote_real_of_coeff_add
    (M : SmtModel) (vars : Term) (c1 c2 : native_Rat) :
  arith_mon_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
        (Term.Rational (native_qplus c1 c2))) =
    __smtx_model_eval_plus
      (arith_mon_denote_real M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c1)))
      (arith_mon_denote_real M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c2))) := by
  rcases arith_mvar_denote_real_rational_or_notValue M vars with hVars | hVars
  · rcases hVars with ⟨qv, hVars⟩
    simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, __smtx_model_eval_plus,
      native_qmult, native_qplus, Rat.add_mul]
  · simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, __smtx_model_eval_plus]

private theorem arith_mon_denote_real_of_coeff_mul
    (M : SmtModel) (vars : Term) (c1 c2 : native_Rat) :
  arith_mon_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
        (Term.Rational (native_qmult c1 c2))) =
    __smtx_model_eval_mult
      (SmtValue.Rational c1)
      (arith_mon_denote_real M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c2))) := by
  rcases arith_mvar_denote_real_rational_or_notValue M vars with hVars | hVars
  · rcases hVars with ⟨qv, hVars⟩
    simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, native_qmult, Rat.mul_assoc]
  · simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult]

private theorem arith_mvar_denote_real_of_mvar_mul_mvar_rational
    (M : SmtModel) {vars1 vars2 : Term}
    (hvars1 : arith_mvar_rational M vars1)
    (hvars2 : arith_mvar_rational M vars2) :
  arith_mvar_denote_real M (__mvar_mul_mvar vars1 vars2) =
    __smtx_model_eval_mult (arith_mvar_denote_real M vars1) (arith_mvar_denote_real M vars2) := by
  cases hvars1 with
  | nil =>
      rw [mvar_mul_mvar_nil_left]
      exact (smtx_model_eval_mult_one_left_of_rational_or_notValue
        (Or.inl (arith_mvar_denote_real_rational_of_rational_support M hvars2))).symm
  | cons a1 rest1 hA1 hRest1 =>
      cases hvars2 with
      | nil =>
          rw [mvar_mul_mvar_nil_right]
          exact (smtx_model_eval_mult_one_right_of_rational_or_notValue
            (Or.inl (arith_mvar_denote_real_rational_of_rational_support M
              (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1)))).symm
      | cons c1 rest2 hC1 hRest2 =>
          let vars1' := Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1
          let vars2' := Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2
          have hRest1Val : ∃ q, arith_mvar_denote_real M rest1 = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M hRest1
          have hVars1Val : ∃ q, arith_mvar_denote_real M vars1' = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M
              (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1)
          have hRest2Val : ∃ q, arith_mvar_denote_real M rest2 = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M hRest2
          have hVars2Val : ∃ q, arith_mvar_denote_real M vars2' = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M
              (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2)
          have hA1NotStuck : a1 ≠ Term.Stuck :=
            arith_atom_ne_stuck_of_rational_support hA1
          have hC1NotStuck : c1 ≠ Term.Stuck :=
            arith_atom_ne_stuck_of_rational_support hC1
          by_cases hCmp : native_tcmp c1 a1 = true
          · have hRec :
                arith_mvar_denote_real M (__mvar_mul_mvar rest1 vars2') =
                  __smtx_model_eval_mult (arith_mvar_denote_real M rest1)
                    (arith_mvar_denote_real M vars2') :=
              arith_mvar_denote_real_of_mvar_mul_mvar_rational M hRest1
                (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2)
            have hTail :
                __mvar_mul_mvar rest1 vars2' ≠ Term.Stuck :=
              arith_mvar_rational_ne_stuck
                (arith_mvar_rational_of_mvar_mul_mvar M hRest1
                  (arith_mvar_rational.cons (M := M) c1 rest2 hC1 hRest2))
            rw [mvar_mul_mvar_cons_cons_true a1 rest1 c1 rest2 hA1NotStuck hC1NotStuck hCmp]
            calc
              arith_mvar_denote_real M (__eo_mk_apply (Term.Apply Term.__eo_List_cons a1)
                  (__mvar_mul_mvar rest1 vars2')) =
                __smtx_model_eval_mult (arith_atom_denote_real M a1)
                  (__smtx_model_eval_mult (arith_mvar_denote_real M rest1)
                    (arith_mvar_denote_real M vars2')) := by
                  simp [__eo_mk_apply, hTail, arith_mvar_denote_real, hRec]
              _ =
                __smtx_model_eval_mult
                  (__smtx_model_eval_mult (arith_atom_denote_real M a1)
                    (arith_mvar_denote_real M rest1))
                  (arith_mvar_denote_real M vars2') := by
                  exact
                    (smtx_model_eval_mult_assoc_of_rational_or_notValue
                      (Or.inl hA1) (Or.inl hRest1Val) (Or.inl hVars2Val)).symm
              _ =
                __smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                  (arith_mvar_denote_real M vars2') := by
                  simp [vars1', arith_mvar_denote_real]
          · have hCmp' : native_tcmp c1 a1 = false := by
              cases hT : native_tcmp c1 a1 with
              | false =>
                  rfl
              | true =>
                  exfalso
                  exact hCmp hT
            have hRec :
                arith_mvar_denote_real M (__mvar_mul_mvar vars1' rest2) =
                  __smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                    (arith_mvar_denote_real M rest2) :=
              arith_mvar_denote_real_of_mvar_mul_mvar_rational M
                (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1) hRest2
            have hTail :
                __mvar_mul_mvar vars1' rest2 ≠ Term.Stuck :=
              arith_mvar_rational_ne_stuck
                (arith_mvar_rational_of_mvar_mul_mvar M
                  (arith_mvar_rational.cons (M := M) a1 rest1 hA1 hRest1) hRest2)
            rw [mvar_mul_mvar_cons_cons_false a1 rest1 c1 rest2 hA1NotStuck hC1NotStuck hCmp']
            calc
              arith_mvar_denote_real M (__eo_mk_apply (Term.Apply Term.__eo_List_cons c1)
                  (__mvar_mul_mvar vars1' rest2)) =
                __smtx_model_eval_mult (arith_atom_denote_real M c1)
                  (__smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                    (arith_mvar_denote_real M rest2)) := by
                  simp [__eo_mk_apply, hTail, arith_mvar_denote_real, hRec]
              _ =
                __smtx_model_eval_mult
                  (__smtx_model_eval_mult (arith_atom_denote_real M c1)
                    (arith_mvar_denote_real M vars1'))
                  (arith_mvar_denote_real M rest2) := by
                  exact
                    (smtx_model_eval_mult_assoc_of_rational_or_notValue
                      (Or.inl hC1) (Or.inl hVars1Val) (Or.inl hRest2Val)).symm
              _ =
                __smtx_model_eval_mult
                  (__smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                    (arith_atom_denote_real M c1))
                  (arith_mvar_denote_real M rest2) := by
                  rw [smtx_model_eval_mult_comm_of_rational_or_notValue
                    (Or.inl hC1) (Or.inl hVars1Val)]
              _ =
                __smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                  (__smtx_model_eval_mult (arith_atom_denote_real M c1)
                    (arith_mvar_denote_real M rest2)) := by
                  exact
                    smtx_model_eval_mult_assoc_of_rational_or_notValue
                      (Or.inl hVars1Val) (Or.inl hC1) (Or.inl hRest2Val)
              _ =
                __smtx_model_eval_mult (arith_mvar_denote_real M vars1')
                  (arith_mvar_denote_real M vars2') := by
                  simp [vars2', arith_mvar_denote_real]
termination_by sizeOf vars1 + sizeOf vars2
decreasing_by
  simp_wf
  · have hSize :
        sizeOf rest1 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons a1) rest1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf rest2 <
          sizeOf (Term.Apply (Term.Apply Term.__eo_List_cons c1) rest2) := by
        simp
        omega
    omega

private theorem arith_mon_denote_real_of_mon_mul_mon_rational
    (M : SmtModel) {m1 m2 : Term}
    (hm1 : arith_mon_rational M m1)
    (hm2 : arith_mon_rational M m2) :
  arith_mon_denote_real M (__mon_mul_mon m1 m2) =
    __smtx_model_eval_mult (arith_mon_denote_real M m1) (arith_mon_denote_real M m2) := by
  cases hm1 with
  | mk vars1 c1 hvars1 =>
      cases hm2 with
      | mk vars2 c2 hvars2 =>
          have hVars :
              __mvar_mul_mvar vars1 vars2 ≠ Term.Stuck :=
            arith_mvar_rational_ne_stuck
              (arith_mvar_rational_of_mvar_mul_mvar M hvars1 hvars2)
          have hVars1Val : ∃ q, arith_mvar_denote_real M vars1 = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M hvars1
          have hVars2Val : ∃ q, arith_mvar_denote_real M vars2 = SmtValue.Rational q :=
            arith_mvar_denote_real_rational_of_rational_support M hvars2
          rcases hVars1Val with ⟨q1, hVars1Val⟩
          rcases hVars2Val with ⟨q2, hVars2Val⟩
          rw [show __mon_mul_mon
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1) (Term.Rational c1))
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2) (Term.Rational c2)) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_mon) (__mvar_mul_mvar vars1 vars2))
                    (Term.Rational (native_qmult c1 c2)) by
                simp [__mon_mul_mon, __eo_mul, __eo_mk_apply, hVars]]
          rw [arith_mon_denote_real_of_coeff_mul M (__mvar_mul_mvar vars1 vars2) c1 c2]
          simp [arith_mon_denote_real]
          rw [arith_mvar_denote_real_of_mvar_mul_mvar_rational M hvars1 hvars2]
          rw [hVars1Val, hVars2Val]
          simp [arith_mon_denote_real, __smtx_model_eval_mult, native_qmult]
          calc
            c1 * (c2 * (q1 * q2)) = c1 * ((c2 * q1) * q2) := by rw [Rat.mul_assoc c2 q1 q2]
            _ = c1 * ((q1 * c2) * q2) := by rw [Rat.mul_comm c2 q1]
            _ = c1 * (q1 * (c2 * q2)) := by rw [← Rat.mul_assoc q1 c2 q2]
            _ = c1 * q1 * (c2 * q2) := by rw [Rat.mul_assoc c1 q1 (c2 * q2)]

private theorem arith_mon_denote_real_zero_coeff_of_rational
    (M : SmtModel) (vars : Term)
    (hVars : ∃ qv, arith_mvar_denote_real M vars = SmtValue.Rational qv) :
  arith_mon_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
        (Term.Rational (native_mk_rational 0 1))) =
    SmtValue.Rational (native_mk_rational 0 1) := by
  rcases hVars with ⟨qv, hVars⟩
  simp [arith_mon_denote_real, hVars, __smtx_model_eval_mult, native_qmult,
    native_mk_rational_zero, Rat.zero_mul]

private theorem arith_mon_denote_real_of_eo_neg
    (M : SmtModel) (vars c : Term) :
  arith_mon_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (__eo_neg c)) =
    __smtx_model_eval_uneg
      (arith_mon_denote_real M
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) c)) := by
  cases c with
  | Rational q =>
      rcases arith_mvar_denote_real_rational_or_notValue M vars with hVars | hVars
      · rcases hVars with ⟨qv, hVars⟩
        simpa [arith_mon_denote_real, __eo_neg, hVars] using
          smtx_model_eval_mult_neg_left_of_rational_or_notValue q (Or.inl ⟨qv, rfl⟩)
      · simpa [arith_mon_denote_real, __eo_neg, hVars] using
          smtx_model_eval_mult_neg_left_of_rational_or_notValue q (Or.inr rfl)
  | _ =>
      simp [arith_mon_denote_real, __eo_neg, __smtx_model_eval_uneg]

private theorem arith_mvar_wf_ne_stuck
    {vars : Term}
    (hvars : arith_mvar_wf vars) :
  vars ≠ Term.Stuck := by
  intro hSt
  cases hvars <;> cases hSt

private theorem arith_poly_wf_ne_stuck
    {p : Term}
    (hp : arith_poly_wf p) :
  p ≠ Term.Stuck := by
  intro hSt
  cases hp <;> cases hSt

private theorem arith_poly_wf_of_poly_neg
    {p : Term}
    (hp : arith_poly_wf p) :
  arith_poly_wf (__poly_neg p) := by
  induction hp with
  | zero =>
      simpa [__poly_neg] using arith_poly_wf.zero
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hTail : __poly_neg p ≠ Term.Stuck :=
            arith_poly_wf_ne_stuck ih
          simpa [__poly_neg, __eo_mk_apply, __eo_neg, hTail] using
            (arith_poly_wf.cons
              (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                (Term.Rational (native_qneg c)))
              (__poly_neg p)
              (arith_mon_wf.mk vars (native_qneg c) hvars)
              ih)

private theorem arith_poly_wf_of_poly_add
    {P1 P2 : Term}
    (h1 : arith_poly_wf P1)
    (h2 : arith_poly_wf P2) :
  arith_poly_wf (__poly_add P1 P2) := by
  cases h1 with
  | zero =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using arith_poly_wf.zero
      | @cons m2 p2 hm2 hp2 =>
          simpa [__poly_add] using arith_poly_wf.cons m2 p2 hm2 hp2
  | @cons m1 p1 hm1 hp1 =>
      cases h2 with
      | zero =>
          simpa [__poly_add] using arith_poly_wf.cons m1 p1 hm1 hp1
      | @cons m2 p2 hm2 hp2 =>
          cases hm1 with
          | mk vars1 c1 hvars1 =>
              cases hm2 with
              | mk vars2 c2 hvars2 =>
                  have hVars1 : vars1 ≠ Term.Stuck := arith_mvar_wf_ne_stuck hvars1
                  have hVars2 : vars2 ≠ Term.Stuck := arith_mvar_wf_ne_stuck hvars2
                  by_cases hEq : vars1 = vars2
                  · subst vars2
                    have hRec : arith_poly_wf (__poly_add p1 p2) :=
                        arith_poly_wf_of_poly_add hp1 hp2
                    by_cases hZero : native_qplus c1 c2 = native_mk_rational 0 1
                    · have hZero' : native_mk_rational 0 1 = native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero']
                        using hRec
                    · have hTail : __poly_add p1 p2 ≠ Term.Stuck :=
                          arith_poly_wf_ne_stuck hRec
                      have hZero' : native_mk_rational 0 1 ≠ native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      simpa [__poly_add, __eo_eq, __eo_ite, __eo_add, native_ite, native_teq,
                        hVars1, hZero', __eo_mk_apply, hTail] using
                        (arith_poly_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational (native_qplus c1 c2)))
                          (__poly_add p1 p2)
                          (arith_mon_wf.mk vars1 (native_qplus c1 c2) hvars1)
                          hRec)
                  · have hEq' : vars2 ≠ vars1 := by
                        simpa [eq_comm] using hEq
                    by_cases hCmp : native_tcmp vars2 vars1
                    · have hRec : arith_poly_wf
                            (__poly_add p1
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                    (Term.Rational c2)))
                                p2)) :=
                          arith_poly_wf_of_poly_add hp1
                            (arith_poly_wf.cons
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                (Term.Rational c2))
                              p2
                              (arith_mon_wf.mk vars2 c2 hvars2)
                              hp2)
                      have hTail :
                          __poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational c2)))
                              p2) ≠ Term.Stuck :=
                        arith_poly_wf_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail] using
                        (arith_poly_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                            (Term.Rational c1))
                          (__poly_add p1
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                                  (Term.Rational c2)))
                              p2))
                          (arith_mon_wf.mk vars1 c1 hvars1)
                          hRec)
                    · have hRec : arith_poly_wf
                            (__poly_add
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_poly)
                                  (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                    (Term.Rational c1)))
                                p1)
                              p2) :=
                          arith_poly_wf_of_poly_add
                            (arith_poly_wf.cons
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                (Term.Rational c1))
                              p1
                              (arith_mon_wf.mk vars1 c1 hvars1)
                              hp1)
                            hp2
                      have hTail :
                          __poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational c1)))
                              p1)
                            p2 ≠ Term.Stuck :=
                        arith_poly_wf_ne_stuck hRec
                      simpa [__poly_add, __eo_eq, __eo_ite, native_teq, hEq', hVars1, hVars2,
                        __eo_cmp, hCmp, __eo_mk_apply, hTail] using
                        (arith_poly_wf.cons
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                            (Term.Rational c2))
                          (__poly_add
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp._at__at_poly)
                                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational c1)))
                              p1)
                            p2)
                          (arith_mon_wf.mk vars2 c2 hvars2)
                          hRec)
termination_by sizeOf P1 + sizeOf P2
decreasing_by
  simp_wf
  · omega
  · have hSize :
        sizeOf p1 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational c1)))
              p1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf p2 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational c2)))
              p2) := by
        simp
        omega
    omega

private theorem arith_poly_denote_real_of_poly_neg_wf
    (M : SmtModel) {p : Term}
    (hp : arith_poly_wf p) :
  arith_poly_denote_real M (__poly_neg p) =
    __smtx_model_eval_uneg (arith_poly_denote_real M p) := by
  induction hp with
  | zero =>
      simp [__poly_neg, arith_poly_denote_real, __smtx_model_eval_uneg, native_qneg,
        native_mk_rational_zero]
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          have hTail : __poly_neg p ≠ Term.Stuck :=
            arith_poly_wf_ne_stuck (arith_poly_wf_of_poly_neg hp)
          have hMult :
              __smtx_model_eval_mult (SmtValue.Rational (native_qneg c))
                  (arith_mvar_denote_real M vars) =
                __smtx_model_eval_uneg
                  (__smtx_model_eval_mult (SmtValue.Rational c) (arith_mvar_denote_real M vars)) :=
            smtx_model_eval_mult_neg_left_of_rational_or_notValue c
              (arith_mvar_denote_real_rational_or_notValue M vars)
          simp [__poly_neg, __eo_mk_apply, __eo_neg, hTail, arith_poly_denote_real,
            arith_mon_denote_real, ih]
          rw [hMult]
          exact
            smtx_model_eval_plus_uneg_of_rational_or_notValue
              (arith_mon_denote_real_rational_or_notValue M
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c)))
              (arith_poly_denote_real_rational_or_notValue M p)

private theorem arith_poly_denote_real_of_poly_add_rational
    (M : SmtModel) {P1 P2 : Term}
    (h1 : arith_poly_rational M P1)
    (h2 : arith_poly_rational M P2) :
  arith_poly_denote_real M (__poly_add P1 P2) =
    __smtx_model_eval_plus (arith_poly_denote_real M P1) (arith_poly_denote_real M P2) := by
  cases h1 with
  | zero =>
      cases h2 with
      | zero =>
          simp [__poly_add, arith_poly_denote_real, __smtx_model_eval_plus, native_qplus,
            native_mk_rational_zero, Rat.zero_add]
      | @cons m2 p2 hm2 hp2 =>
          have hP2Val :
              ∃ q, arith_poly_denote_real M
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m2) p2) =
                  SmtValue.Rational q :=
            arith_poly_denote_real_rational_of_rational_support M
              (arith_poly_rational.cons (M := M) m2 p2 hm2 hp2)
          simpa [__poly_add, arith_poly_denote_real] using
            (smtx_model_eval_plus_zero_left_of_rational_or_notValue (Or.inl hP2Val)).symm
  | @cons m1 p1 hm1 hp1 =>
      cases h2 with
      | zero =>
          have hP1Val :
              ∃ q, arith_poly_denote_real M
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m1) p1) =
                  SmtValue.Rational q :=
            arith_poly_denote_real_rational_of_rational_support M
              (arith_poly_rational.cons (M := M) m1 p1 hm1 hp1)
          simpa [__poly_add, arith_poly_denote_real] using
            (smtx_model_eval_plus_zero_right_of_rational_or_notValue (Or.inl hP1Val)).symm
      | @cons m2 p2 hm2 hp2 =>
          cases hm1 with
          | mk vars1 c1 hvars1 =>
              cases hm2 with
              | mk vars2 c2 hvars2 =>
                  have hVars1 : vars1 ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars1
                  have hVars2 : vars2 ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars2
                  let mon1 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                      (Term.Rational c1)
                  let mon2 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                      (Term.Rational c2)
                  let poly1 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) mon1) p1
                  let poly2 : Term :=
                    Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) mon2) p2
                  have hMon1Val : ∃ q, arith_mon_denote_real M mon1 = SmtValue.Rational q := by
                    simpa [mon1] using
                      arith_mon_denote_real_rational_of_rational_support M
                        (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                  have hMon2Val : ∃ q, arith_mon_denote_real M mon2 = SmtValue.Rational q := by
                    simpa [mon2] using
                      arith_mon_denote_real_rational_of_rational_support M
                        (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                  have hP1Val : ∃ q, arith_poly_denote_real M p1 = SmtValue.Rational q :=
                    arith_poly_denote_real_rational_of_rational_support M hp1
                  have hP2Val : ∃ q, arith_poly_denote_real M p2 = SmtValue.Rational q :=
                    arith_poly_denote_real_rational_of_rational_support M hp2
                  rcases hMon1Val with ⟨qm1, hMon1Eq⟩
                  rcases hMon2Val with ⟨qm2, hMon2Eq⟩
                  rcases hP1Val with ⟨qp1, hP1Eq⟩
                  rcases hP2Val with ⟨qp2, hP2Eq⟩
                  have hPoly1Val : ∃ q, arith_poly_denote_real M poly1 = SmtValue.Rational q := by
                    refine ⟨native_qplus qm1 qp1, ?_⟩
                    simp [poly1, mon1, arith_poly_denote_real, hMon1Eq, hP1Eq,
                      __smtx_model_eval_plus, native_qplus]
                  have hPoly2Val : ∃ q, arith_poly_denote_real M poly2 = SmtValue.Rational q := by
                    refine ⟨native_qplus qm2 qp2, ?_⟩
                    simp [poly2, mon2, arith_poly_denote_real, hMon2Eq, hP2Eq,
                      __smtx_model_eval_plus, native_qplus]
                  have hP12Val :
                      ∃ q,
                        __smtx_model_eval_plus
                          (arith_poly_denote_real M p1)
                          (arith_poly_denote_real M p2) = SmtValue.Rational q := by
                    refine ⟨native_qplus qp1 qp2, ?_⟩
                    simp [hP1Eq, hP2Eq, __smtx_model_eval_plus, native_qplus]
                  have hM2P1Val :
                      ∃ q,
                        __smtx_model_eval_plus
                          (arith_mon_denote_real M mon2)
                          (arith_poly_denote_real M p1) = SmtValue.Rational q := by
                    refine ⟨native_qplus qm2 qp1, ?_⟩
                    simp [hMon2Eq, hP1Eq, __smtx_model_eval_plus, native_qplus]
                  by_cases hEq : vars1 = vars2
                  · subst vars2
                    have hRec :
                        arith_poly_denote_real M (__poly_add p1 p2) =
                          __smtx_model_eval_plus
                            (arith_poly_denote_real M p1)
                            (arith_poly_denote_real M p2) :=
                      arith_poly_denote_real_of_poly_add_rational M hp1 hp2
                    by_cases hZero : native_qplus c1 c2 = native_mk_rational 0 1
                    · have hZero' : native_mk_rational 0 1 = native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      have hVarsRat :
                          ∃ qv, arith_mvar_denote_real M vars1 = SmtValue.Rational qv :=
                        arith_mvar_denote_real_rational_of_rational_support M hvars1
                      have hMonSum :
                          __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (arith_mon_denote_real M mon2) =
                            SmtValue.Rational (native_mk_rational 0 1) := by
                        have hCoeffZero :
                            arith_mon_denote_real M
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational (native_qplus c1 c2))) =
                              SmtValue.Rational (native_mk_rational 0 1) := by
                          simpa [hZero', mon2] using
                            arith_mon_denote_real_zero_coeff_of_rational M vars1 hVarsRat
                        exact (arith_mon_denote_real_of_coeff_add M vars1 c1 c2).symm.trans
                          hCoeffZero
                      calc
                        arith_poly_denote_real M (__poly_add poly1 poly2) =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M p1)
                              (arith_poly_denote_real M p2) := by
                          simp [poly1, poly2, mon1, mon2, __poly_add, __eo_eq, __eo_ite,
                            __eo_add, native_ite, native_teq, hVars1, hZero',
                            arith_poly_denote_real, hRec]
                        _ =
                            __smtx_model_eval_plus
                              (SmtValue.Rational (native_mk_rational 0 1))
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M p2)) := by
                          symm
                          exact
                            smtx_model_eval_plus_zero_left_of_rational_or_notValue
                              (Or.inl hP12Val)
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_mon_denote_real M mon2))
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M p2)) := by
                          rw [← hMonSum]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon2)
                                (__smtx_model_eval_plus
                                  (arith_poly_denote_real M p1)
                                  (arith_poly_denote_real M p2))) := by
                          exact
                            smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl hP12Val)
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (__smtx_model_eval_plus
                                  (arith_mon_denote_real M mon2)
                                  (arith_poly_denote_real M p1))
                                (arith_poly_denote_real M p2)) := by
                          rw [smtx_model_eval_plus_assoc_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl ⟨qp1, hP1Eq⟩)
                            (Or.inl ⟨qp2, hP2Eq⟩)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (__smtx_model_eval_plus
                                  (arith_poly_denote_real M p1)
                                  (arith_mon_denote_real M mon2))
                                (arith_poly_denote_real M p2)) := by
                          rw [smtx_model_eval_plus_comm_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl ⟨qp1, hP1Eq⟩)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (__smtx_model_eval_plus
                                  (arith_mon_denote_real M mon2)
                                  (arith_poly_denote_real M p2))) := by
                          simpa using congrArg
                            (__smtx_model_eval_plus (arith_mon_denote_real M mon1))
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl ⟨qp2, hP2Eq⟩))
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M poly2)) := by
                          simp [poly2, mon2, arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_poly_denote_real M p1))
                              (arith_poly_denote_real M poly2) := by
                          exact
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl hPoly2Val)).symm
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (arith_poly_denote_real M poly2) := by
                          simp [poly1, mon1, arith_poly_denote_real]
                    · have hZero' : native_mk_rational 0 1 ≠ native_qplus c1 c2 := by
                        simpa [eq_comm] using hZero
                      have hTail :
                          __poly_add p1 p2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck (arith_poly_rational_of_poly_add M hp1 hp2)
                      calc
                        arith_poly_denote_real M (__poly_add poly1 poly2) =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                                  (Term.Rational (native_qplus c1 c2))))
                              (arith_poly_denote_real M (__poly_add p1 p2)) := by
                          simp [poly1, poly2, mon1, mon2, __poly_add, __eo_eq, __eo_ite,
                            __eo_add, native_ite, native_teq, hVars1, hZero', __eo_mk_apply,
                            hTail, arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_mon_denote_real M mon2))
                              (arith_poly_denote_real M (__poly_add p1 p2)) := by
                          rw [arith_mon_denote_real_of_coeff_add M vars1 c1 c2]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_mon_denote_real M mon2))
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M p2)) := by
                          rw [hRec]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon2)
                                (__smtx_model_eval_plus
                                  (arith_poly_denote_real M p1)
                                  (arith_poly_denote_real M p2))) := by
                          exact
                            smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl hP12Val)
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (__smtx_model_eval_plus
                                  (arith_mon_denote_real M mon2)
                                  (arith_poly_denote_real M p1))
                                (arith_poly_denote_real M p2)) := by
                          rw [smtx_model_eval_plus_assoc_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl ⟨qp1, hP1Eq⟩)
                            (Or.inl ⟨qp2, hP2Eq⟩)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (__smtx_model_eval_plus
                                  (arith_poly_denote_real M p1)
                                  (arith_mon_denote_real M mon2))
                                (arith_poly_denote_real M p2)) := by
                          rw [smtx_model_eval_plus_comm_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl ⟨qp1, hP1Eq⟩)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (__smtx_model_eval_plus
                                  (arith_mon_denote_real M mon2)
                                  (arith_poly_denote_real M p2))) := by
                          simpa using congrArg
                            (__smtx_model_eval_plus (arith_mon_denote_real M mon1))
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl ⟨qp2, hP2Eq⟩))
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M poly2)) := by
                          simp [poly2, mon2, arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_poly_denote_real M p1))
                              (arith_poly_denote_real M poly2) := by
                          exact
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl hPoly2Val)).symm
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (arith_poly_denote_real M poly2) := by
                          simp [poly1, mon1, arith_poly_denote_real]
                  · have hEq' : vars2 ≠ vars1 := by
                        simpa [eq_comm] using hEq
                    by_cases hCmp : native_tcmp vars2 vars1
                    · have hRec :
                            arith_poly_denote_real M (__poly_add p1 poly2) =
                              __smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M poly2) :=
                          arith_poly_denote_real_of_poly_add_rational M hp1
                            (arith_poly_rational.cons
                              (M := M)
                              mon2 p2
                              (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                              hp2)
                      have hTail : __poly_add p1 poly2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck
                          (arith_poly_rational_of_poly_add M hp1
                            (arith_poly_rational.cons
                              (M := M)
                              mon2 p2
                              (arith_mon_rational.mk (M := M) vars2 c2 hvars2)
                              hp2))
                      calc
                        arith_poly_denote_real M (__poly_add poly1 poly2) =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (arith_poly_denote_real M (__poly_add p1 poly2)) := by
                          simp [poly1, poly2, mon1, mon2, __poly_add, __eo_eq, __eo_ite,
                            native_ite, native_teq, hEq', hVars1, hVars2, __eo_cmp, hCmp,
                            __eo_mk_apply, hTail, arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon1)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M p1)
                                (arith_poly_denote_real M poly2)) := by
                          rw [hRec]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon1)
                                (arith_poly_denote_real M p1))
                              (arith_poly_denote_real M poly2) := by
                          exact
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm1, hMon1Eq⟩)
                              (Or.inl ⟨qp1, hP1Eq⟩)
                              (Or.inl hPoly2Val)).symm
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (arith_poly_denote_real M poly2) := by
                          simp [poly1, mon1, arith_poly_denote_real]
                    · have hRec :
                            arith_poly_denote_real M (__poly_add poly1 p2) =
                              __smtx_model_eval_plus
                                (arith_poly_denote_real M poly1)
                                (arith_poly_denote_real M p2) :=
                          arith_poly_denote_real_of_poly_add_rational M
                            (arith_poly_rational.cons
                              (M := M) mon1 p1
                              (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                              hp1)
                            hp2
                      have hCmp' : native_tcmp vars2 vars1 = false := by
                        cases hT : native_tcmp vars2 vars1 with
                        | false =>
                            rfl
                        | true =>
                            cases (hCmp hT)
                      have hTail : __poly_add poly1 p2 ≠ Term.Stuck :=
                        arith_poly_rational_ne_stuck
                          (arith_poly_rational_of_poly_add M
                            (arith_poly_rational.cons
                              (M := M) mon1 p1
                              (arith_mon_rational.mk (M := M) vars1 c1 hvars1)
                              hp1)
                            hp2)
                      calc
                        arith_poly_denote_real M (__poly_add poly1 poly2) =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon2)
                              (arith_poly_denote_real M (__poly_add poly1 p2)) := by
                          simp [poly1, poly2, mon1, mon2, __poly_add, __eo_eq, __eo_ite,
                            native_ite, native_teq, hEq', hVars1, hVars2, __eo_cmp, hCmp',
                            __eo_mk_apply, hTail, arith_poly_denote_real]
                        _ =
                            __smtx_model_eval_plus
                              (arith_mon_denote_real M mon2)
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M poly1)
                                (arith_poly_denote_real M p2)) := by
                          rw [hRec]
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon2)
                                (arith_poly_denote_real M poly1))
                              (arith_poly_denote_real M p2) := by
                          exact
                            (smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl hPoly1Val)
                              (Or.inl ⟨qp2, hP2Eq⟩)).symm
                        _ =
                            __smtx_model_eval_plus
                              (__smtx_model_eval_plus
                                (arith_poly_denote_real M poly1)
                                (arith_mon_denote_real M mon2))
                              (arith_poly_denote_real M p2) := by
                          rw [smtx_model_eval_plus_comm_of_rational_or_notValue
                            (Or.inl ⟨qm2, hMon2Eq⟩)
                            (Or.inl hPoly1Val)]
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (__smtx_model_eval_plus
                                (arith_mon_denote_real M mon2)
                                (arith_poly_denote_real M p2)) := by
                          exact
                            smtx_model_eval_plus_assoc_of_rational_or_notValue
                              (Or.inl hPoly1Val)
                              (Or.inl ⟨qm2, hMon2Eq⟩)
                              (Or.inl ⟨qp2, hP2Eq⟩)
                        _ =
                            __smtx_model_eval_plus
                              (arith_poly_denote_real M poly1)
                              (arith_poly_denote_real M poly2) := by
                          simp [poly2, mon2, arith_poly_denote_real]
termination_by sizeOf P1 + sizeOf P2
decreasing_by
  simp_wf
  · omega
  · have hSize :
        sizeOf p1 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars1)
                  (Term.Rational c1)))
              p1) := by
        simp
        omega
    omega
  · have hSize :
        sizeOf p2 <
          sizeOf
            (Term.Apply
              (Term.Apply (Term.UOp UserOp._at__at_poly)
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars2)
                  (Term.Rational c2)))
              p2) := by
        simp
        omega
    omega

private theorem arith_poly_denote_real_of_poly_mul_mon_rational
    (M : SmtModel) {m p : Term}
    (hm : arith_mon_rational M m)
    (hp : arith_poly_rational M p) :
  arith_poly_denote_real M (__poly_mul_mon m p) =
    __smtx_model_eval_mult (arith_mon_denote_real M m) (arith_poly_denote_real M p) := by
  have hMNe : m ≠ Term.Stuck := arith_mon_rational_ne_stuck hm
  rcases arith_mon_denote_real_rational_of_rational_support M hm with ⟨qm, hMonEq⟩
  induction hp with
  | zero =>
      rw [hMonEq]
      simp [__poly_mul_mon, hMNe, arith_poly_denote_real, __smtx_model_eval_mult, native_qmult,
        native_mk_rational_zero, Rat.mul_zero]
  | @cons m2 p2 hm2 hp2 ih =>
      have hMul : arith_mon_rational M (__mon_mul_mon m m2) :=
        arith_mon_rational_of_mon_mul_mon M hm hm2
      have hMulNe : __mon_mul_mon m m2 ≠ Term.Stuck :=
        arith_mon_rational_ne_stuck hMul
      have hHead :
          arith_poly_rational M
            (__eo_mk_apply
              (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
              (Term.UOp UserOp._at__at_Polynomial)) := by
        simpa [__eo_mk_apply, hMulNe] using
          (arith_poly_rational.cons
            (M := M)
            (__mon_mul_mon m m2)
            (Term.UOp UserOp._at__at_Polynomial)
            hMul
            (arith_poly_rational.zero (M := M)))
      have hMulTail : arith_poly_rational M (__poly_mul_mon m p2) :=
        arith_poly_rational_of_poly_mul_mon M hm hp2
      have hMon2Val : ∃ q, arith_mon_denote_real M m2 = SmtValue.Rational q :=
        arith_mon_denote_real_rational_of_rational_support M hm2
      have hPoly2Val : ∃ q, arith_poly_denote_real M p2 = SmtValue.Rational q :=
        arith_poly_denote_real_rational_of_rational_support M hp2
      have hHeadEq :
          arith_poly_denote_real M
              (__eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
                (Term.UOp UserOp._at__at_Polynomial)) =
            __smtx_model_eval_mult (arith_mon_denote_real M m) (arith_mon_denote_real M m2) := by
        rcases hMon2Val with ⟨qm2, hMon2Eq⟩
        simp [arith_poly_denote_real, __eo_mk_apply, hMulNe, __smtx_model_eval_plus,
          native_qplus, native_mk_rational_zero]
        rw [arith_mon_denote_real_of_mon_mul_mon_rational M hm hm2, hMonEq, hMon2Eq]
        simpa [__smtx_model_eval_plus, __smtx_model_eval_mult, native_qmult,
          native_mk_rational_zero] using
          congrArg SmtValue.Rational (Rat.add_zero (qm * qm2))
      have hStep :
          arith_poly_denote_real M
              (__poly_mul_mon m
                (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m2) p2)) =
            __smtx_model_eval_plus
              (arith_poly_denote_real M
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp._at__at_poly) (__mon_mul_mon m m2))
                  (Term.UOp UserOp._at__at_Polynomial)))
              (arith_poly_denote_real M (__poly_mul_mon m p2)) := by
        simpa [__poly_mul_mon, hMNe] using arith_poly_denote_real_of_poly_add_rational M hHead hMulTail
      rcases hMon2Val with ⟨qm2, hMon2Eq⟩
      rcases hPoly2Val with ⟨qp2, hPoly2Eq⟩
      rw [hStep, hHeadEq, ih, hMonEq]
      simpa [arith_poly_denote_real, hMon2Eq, hPoly2Eq] using
        (smtx_model_eval_mult_rational_left_distrib_plus_of_rational_or_notValue
          qm (arith_mon_denote_real M m2) (arith_poly_denote_real M p2)
          (Or.inl ⟨qm2, hMon2Eq⟩) (Or.inl ⟨qp2, hPoly2Eq⟩))

private theorem arith_poly_denote_real_of_poly_mul_rational
    (M : SmtModel) {p1 p2 : Term}
    (hp1 : arith_poly_rational M p1)
    (hp2 : arith_poly_rational M p2) :
  arith_poly_denote_real M (__poly_mul p1 p2) =
    __smtx_model_eval_mult (arith_poly_denote_real M p1) (arith_poly_denote_real M p2) := by
  have hP2Ne : p2 ≠ Term.Stuck := arith_poly_rational_ne_stuck hp2
  rcases arith_poly_denote_real_rational_of_rational_support M hp2 with ⟨qp2, hPoly2Eq⟩
  induction hp1 with
  | zero =>
      rw [hPoly2Eq]
      simp [__poly_mul, hP2Ne, arith_poly_denote_real, __smtx_model_eval_mult, native_qmult,
        native_mk_rational_zero, Rat.zero_mul]
  | @cons m p1 hm hp1 ih =>
      have hMulHead : arith_poly_rational M (__poly_mul_mon m p2) :=
        arith_poly_rational_of_poly_mul_mon M hm hp2
      have hMulTail : arith_poly_rational M (__poly_mul p1 p2) :=
        arith_poly_rational_of_poly_mul M hp1 hp2
      have hStep :
          arith_poly_denote_real M
              (__poly_mul (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) m) p1) p2) =
            __smtx_model_eval_plus
              (arith_poly_denote_real M (__poly_mul_mon m p2))
              (arith_poly_denote_real M (__poly_mul p1 p2)) := by
        simpa [__poly_mul, hP2Ne] using arith_poly_denote_real_of_poly_add_rational M hMulHead hMulTail
      have hMonVal : ∃ q, arith_mon_denote_real M m = SmtValue.Rational q :=
        arith_mon_denote_real_rational_of_rational_support M hm
      have hPoly1Val : ∃ q, arith_poly_denote_real M p1 = SmtValue.Rational q :=
        arith_poly_denote_real_rational_of_rational_support M hp1
      rcases hMonVal with ⟨qm, hMonEq⟩
      rcases hPoly1Val with ⟨qp1, hPoly1Eq⟩
      rw [hStep, arith_poly_denote_real_of_poly_mul_mon_rational M hm hp2, ih, hPoly2Eq]
      simpa [arith_poly_denote_real, hMonEq, hPoly1Eq] using
        (smtx_model_eval_mult_rational_right_distrib_plus_of_rational_or_notValue
          qp2 (arith_mon_denote_real M m) (arith_poly_denote_real M p1)
          (Or.inl ⟨qm, hMonEq⟩) (Or.inl ⟨qp1, hPoly1Eq⟩))

private theorem arith_poly_denote_real_of_poly_mul_mon_const_rational
    (M : SmtModel) (q : native_Rat) {p : Term}
    (hp : arith_poly_rational M p) :
  arith_poly_denote_real M (__poly_mul_mon (arith_const_mon q) p) =
    __smtx_model_eval_mult (SmtValue.Rational q) (arith_poly_denote_real M p) := by
  induction hp with
  | zero =>
      simp [arith_const_mon, __poly_mul_mon, arith_poly_denote_real, __smtx_model_eval_mult,
        native_qmult, native_qplus, native_mk_rational_zero, Rat.mul_zero]
  | @cons m p hm hp ih =>
      cases hm with
      | mk vars c hvars =>
          let mon : Term :=
            Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars) (Term.Rational c)
          have hVars : vars ≠ Term.Stuck := arith_mvar_rational_ne_stuck hvars
          have hHead :
              arith_poly_rational M
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp._at__at_poly)
                    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                      (Term.Rational (native_qmult q c))))
                  (Term.UOp UserOp._at__at_Polynomial)) := by
            exact arith_poly_rational.cons
              (M := M)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                (Term.Rational (native_qmult q c)))
              (Term.UOp UserOp._at__at_Polynomial)
              (arith_mon_rational.mk (M := M) vars (native_qmult q c) hvars)
              (arith_poly_rational.zero (M := M))
          have hMulTail :
              arith_poly_rational M (__poly_mul_mon (arith_const_mon q) p) :=
            arith_poly_rational_of_poly_mul_mon_const M q hp
          have hMonVal :
              ∃ qm, arith_mon_denote_real M mon = SmtValue.Rational qm := by
            simpa [mon] using
              arith_mon_denote_real_rational_of_rational_support M
                (arith_mon_rational.mk (M := M) vars c hvars)
          have hPolyVal :
              ∃ qp, arith_poly_denote_real M p = SmtValue.Rational qp :=
            arith_poly_denote_real_rational_of_rational_support M hp
          have hHeadEq :
              arith_poly_denote_real M
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_poly)
                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                        (Term.Rational (native_qmult q c))))
                    (Term.UOp UserOp._at__at_Polynomial)) =
                __smtx_model_eval_mult (SmtValue.Rational q) (arith_mon_denote_real M mon) := by
            rw [arith_poly_denote_real, arith_mon_denote_real_of_coeff_mul]
            rcases hMonVal with ⟨qm, hMonVal⟩
            simp [arith_poly_denote_real, mon, hMonVal, __smtx_model_eval_mult,
              __smtx_model_eval_plus, native_qmult, native_qplus, native_mk_rational_zero,
              Rat.add_zero]
          have hStep :
              arith_poly_denote_real M (__poly_mul_mon (arith_const_mon q) (Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_poly) mon) p)) =
                __smtx_model_eval_plus
                  (arith_poly_denote_real M
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_poly)
                        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                          (Term.Rational (native_qmult q c))))
                      (Term.UOp UserOp._at__at_Polynomial)))
                  (arith_poly_denote_real M (__poly_mul_mon (arith_const_mon q) p)) := by
            change arith_poly_denote_real M
              (__poly_add
                (__eo_mk_apply
                  (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
                    (__mon_mul_mon (arith_const_mon q) mon))
                  (Term.UOp UserOp._at__at_Polynomial))
                (__poly_mul_mon (arith_const_mon q) p)) =
              __smtx_model_eval_plus
                (arith_poly_denote_real M
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_poly)
                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                        (Term.Rational (native_qmult q c))))
                    (Term.UOp UserOp._at__at_Polynomial)))
                (arith_poly_denote_real M (__poly_mul_mon (arith_const_mon q) p))
            rw [show __eo_mk_apply
                (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
                  (__mon_mul_mon (arith_const_mon q) mon))
                (Term.UOp UserOp._at__at_Polynomial) =
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_poly)
                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
                        (Term.Rational (native_qmult q c))))
                    (Term.UOp UserOp._at__at_Polynomial) by
                  simpa [mon] using poly_of_mon_mul_mon_const_left q c vars hVars]
            exact arith_poly_denote_real_of_poly_add_rational M hHead hMulTail
          rw [hStep, hHeadEq, ih]
          rcases hMonVal with ⟨qm, hMonVal⟩
          rcases hPolyVal with ⟨qp, hPolyVal⟩
          simpa [arith_poly_denote_real, mon, hMonVal, hPolyVal] using
            (smtx_model_eval_mult_rational_left_distrib_plus_of_rational_or_notValue
              q (arith_mon_denote_real M mon) (arith_poly_denote_real M p)
              (Or.inl ⟨qm, hMonVal⟩) (Or.inl ⟨qp, hPolyVal⟩))

private theorem arith_poly_denote_real_of_rational
    (M : SmtModel) (q : native_Rat) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Rational q)) =
    SmtValue.Rational q := by
  by_cases hZero : q = native_mk_rational 0 1
  · subst hZero
    have hGet :
        __get_arith_poly_norm (Term.Rational (native_mk_rational 0 1)) =
          Term.UOp UserOp._at__at_Polynomial := by
      native_decide
    rw [hGet]
    rfl
  · have hZero' : ¬ native_mk_rational 0 1 = q := by
      simpa [eq_comm] using hZero
    have hDec : decide (native_mk_rational 0 1 = q) = false := by
      simp [hZero']
    have hGet :
        __get_arith_poly_norm (Term.Rational q) =
          __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_mon) Term.__eo_List_nil)
                (Term.Rational q)))
            (Term.UOp UserOp._at__at_Polynomial) := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hDec, SmtEval.native_and, SmtEval.native_not]
    rw [hGet]
    change SmtValue.Rational (q * native_mk_rational 1 1 + native_mk_rational 0 1) =
      SmtValue.Rational q
    congr
    have hOne : native_mk_rational 1 1 = (1 : Rat) := by
      native_decide
    have hZeroRat : native_mk_rational 0 1 = (0 : Rat) := by
      native_decide
    rw [hOne, hZeroRat]
    rw [Rat.mul_one, Rat.add_zero]

private theorem arith_poly_denote_real_of_numeral
    (M : SmtModel) (n : native_Int) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Numeral n)) =
    SmtValue.Rational (native_to_real n) := by
  by_cases hZero : native_to_real n = native_mk_rational 0 1
  · have hGet :
        __get_arith_poly_norm (Term.Numeral n) =
          Term.UOp UserOp._at__at_Polynomial := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hZero, SmtEval.native_and, SmtEval.native_not]
    rw [hGet, hZero]
    rfl
  · have hZero' : ¬ native_mk_rational 0 1 = native_to_real n := by
      simpa [eq_comm] using hZero
    have hDec : decide (native_mk_rational 0 1 = native_to_real n) = false := by
      simp [hZero']
    have hGet :
        __get_arith_poly_norm (Term.Numeral n) =
          __eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp._at__at_poly)
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp._at__at_mon) Term.__eo_List_nil)
                (Term.Rational (native_to_real n))))
            (Term.UOp UserOp._at__at_Polynomial) := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hDec, SmtEval.native_and, SmtEval.native_not]
    rw [hGet]
    change SmtValue.Rational (native_to_real n * native_mk_rational 1 1 + native_mk_rational 0 1) =
      SmtValue.Rational (native_to_real n)
    congr
    have hOne : native_mk_rational 1 1 = (1 : Rat) := by
      native_decide
    have hZeroRat : native_mk_rational 0 1 = (0 : Rat) := by
      native_decide
    rw [hOne, hZeroRat]
    rw [Rat.mul_one, Rat.add_zero]

private theorem arith_atom_denote_real_of_rational
    (M : SmtModel) (q : native_Rat) :
  arith_atom_denote_real M (Term.Rational q) = SmtValue.Rational q := by
  unfold arith_atom_denote_real
  rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl]
  simp [__smtx_model_eval, __smtx_model_eval_to_real]

private theorem arith_atom_denote_real_of_numeral
    (M : SmtModel) (n : native_Int) :
  arith_atom_denote_real M (Term.Numeral n) = SmtValue.Rational (native_to_real n) := by
  unfold arith_atom_denote_real
  rw [show __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n by rfl]
  simp [__smtx_model_eval, __smtx_model_eval_to_real]

private theorem arith_atom_denote_real_of_to_real
    (M : SmtModel) (t : Term) :
  arith_atom_denote_real M (Term.Apply (Term.UOp UserOp.to_real) t) =
    arith_atom_denote_real M t := by
  unfold arith_atom_denote_real
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) t) =
    SmtTerm.to_real (__eo_to_smt t) by rfl]
  rw [__smtx_model_eval.eq_19]
  exact smtx_model_eval_to_real_idempotent (__smtx_model_eval M (__eo_to_smt t))

private theorem native_to_real_neg
    (n : native_Int) :
  native_to_real (native_zneg n) = native_qneg (native_to_real n) := by
  change (-((n : Rat)) * ((1 : Rat)⁻¹)) = -((n : Rat) * ((1 : Rat)⁻¹))
  exact Rat.neg_mul _ _

private theorem native_to_real_add
    (n1 n2 : native_Int) :
  native_to_real (native_zplus n1 n2) =
    native_qplus (native_to_real n1) (native_to_real n2) := by
  rw [native_to_real, native_to_real, native_to_real, native_qplus, native_zplus,
    native_mk_rational, native_mk_rational, native_mk_rational]
  rw [← Rat.divInt_eq_div, ← Rat.divInt_eq_div, ← Rat.divInt_eq_div]
  simpa [Int.mul_one, Int.one_mul] using
    (Rat.divInt_add_divInt n1 n2 (d₁ := 1) (d₂ := 1) (by decide) (by decide)).symm

private theorem native_to_real_sub
    (n1 n2 : native_Int) :
  native_to_real (native_zplus n1 (native_zneg n2)) =
    native_qplus (native_to_real n1) (native_qneg (native_to_real n2)) := by
  rw [native_to_real_add, native_to_real_neg]

private theorem native_to_real_mul
    (n1 n2 : native_Int) :
  native_to_real (native_zmult n1 n2) =
    native_qmult (native_to_real n1) (native_to_real n2) := by
  rw [native_to_real, native_to_real, native_to_real, native_qmult, native_zmult,
    native_mk_rational, native_mk_rational, native_mk_rational]
  simpa [Rat.divInt_eq_div, Int.mul_one, Int.one_mul] using
    (Rat.divInt_mul_divInt n1 n2 (d₁ := 1) (d₂ := 1)).symm

private theorem native_to_real_qdiv_total
    (n1 n2 : native_Int) :
  native_qdiv_total (native_to_real n1) (native_to_real n2) =
    native_mk_rational n1 n2 := by
  rw [native_qdiv_total, native_to_real, native_to_real, native_mk_rational, native_mk_rational,
    native_mk_rational]
  rw [Rat.div_def]
  have hInv : ((↑n2 / ↑(1 : Int) : Rat)⁻¹) = ((↑(1 : Int) / ↑n2 : Rat)) := by
    simpa [Rat.divInt_eq_div] using (Rat.inv_divInt n2 1)
  rw [hInv]
  simpa [Rat.divInt_eq_div, Int.mul_one, Int.one_mul] using
    (Rat.divInt_mul_divInt n1 1 (d₁ := 1) (d₂ := n2))

private theorem arith_atom_denote_real_of_uneg
    (M : SmtModel) (t : Term) :
  arith_atom_denote_real M (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t) =
    __smtx_model_eval_uneg (arith_atom_denote_real M t) := by
  unfold arith_atom_denote_real
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t) =
    SmtTerm.uneg (__eo_to_smt t) by rfl]
  cases hEval : __smtx_model_eval M (__eo_to_smt t) <;>
    simp [__smtx_model_eval, __smtx_model_eval_to_real, __smtx_model_eval_uneg, hEval,
      native_to_real, native_mk_rational, native_zneg, native_qneg]
  case Numeral n =>
    change (-((n : Rat)) * ((1 : Rat)⁻¹)) = -((n : Rat) * ((1 : Rat)⁻¹))
    exact Rat.neg_mul _ _

private theorem arith_atom_denote_real_of_plus
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
        SmtType.Real) :
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) =
    __smtx_model_eval_plus (arith_atom_denote_real M t1) (arith_atom_denote_real M t2) := by
  have ht : term_has_non_none_type (SmtTerm.plus (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
          SmtType.None := by
      rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) =
        SmtTerm.plus (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
      exact hNone
    rcases hTy with hTy | hTy
    · cases hTy.symm.trans hNone'
    · cases hTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
      (typeof_plus_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simpa [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simpa [term_has_non_none_type, hArgs.2])
    rcases int_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨n1, hEval1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨n2, hEval2⟩
    unfold arith_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) =
      SmtTerm.plus (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    rw [__smtx_model_eval.eq_12, hEval1, hEval2]
    simp [__smtx_model_eval_to_real, __smtx_model_eval_plus, native_to_real_add]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simpa [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simpa [term_has_non_none_type, hArgs.2])
    rcases real_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨q1, hEval1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨q2, hEval2⟩
    unfold arith_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) =
      SmtTerm.plus (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    rw [__smtx_model_eval.eq_12, hEval1, hEval2]
    simp [__smtx_model_eval_to_real, __smtx_model_eval_plus]

private theorem arith_atom_denote_real_of_neg
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Real) :
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) =
    __smtx_model_eval_plus (arith_atom_denote_real M t1)
      (__smtx_model_eval_uneg (arith_atom_denote_real M t2)) := by
  have ht : term_has_non_none_type (SmtTerm.neg (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
          SmtType.None := by
      rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) =
        SmtTerm.neg (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
      exact hNone
    rcases hTy with hTy | hTy
    · cases hTy.symm.trans hNone'
    · cases hTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simpa [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simpa [term_has_non_none_type, hArgs.2])
    rcases int_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨n1, hEval1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨n2, hEval2⟩
    unfold arith_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) =
      SmtTerm.neg (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    rw [__smtx_model_eval.eq_13, hEval1, hEval2]
    simp [__smtx_model_eval_to_real, __smtx_model_eval_plus, __smtx_model_eval_uneg,
      __smtx_model_eval__, native_to_real_sub]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simpa [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simpa [term_has_non_none_type, hArgs.2])
    rcases real_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨q1, hEval1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨q2, hEval2⟩
    unfold arith_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) =
      SmtTerm.neg (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    rw [__smtx_model_eval.eq_13, hEval1, hEval2]
    simp [__smtx_model_eval_to_real, __smtx_model_eval_plus, __smtx_model_eval_uneg,
      __smtx_model_eval__]

private theorem arith_atom_denote_real_of_mult
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Real) :
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) =
    __smtx_model_eval_mult (arith_atom_denote_real M t1) (arith_atom_denote_real M t2) := by
  have ht : term_has_non_none_type (SmtTerm.mult (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
          SmtType.None := by
      rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) =
        SmtTerm.mult (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
      exact hNone
    rcases hTy with hTy | hTy
    · cases hTy.symm.trans hNone'
    · cases hTy.symm.trans hNone'
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simpa [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simpa [term_has_non_none_type, hArgs.2])
    rcases int_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨n1, hEval1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨n2, hEval2⟩
    unfold arith_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) =
      SmtTerm.mult (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    simp [__smtx_model_eval, hEval1, hEval2, __smtx_model_eval_to_real,
      __smtx_model_eval_mult, native_to_real_mul]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simpa [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simpa [term_has_non_none_type, hArgs.2])
    rcases real_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨q1, hEval1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨q2, hEval2⟩
    unfold arith_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) =
      SmtTerm.mult (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    simp [__smtx_model_eval, hEval1, hEval2, __smtx_model_eval_to_real,
      __smtx_model_eval_mult]

private theorem arith_atom_denote_real_of_qdiv_total
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
        SmtType.Real) :
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
    __smtx_model_eval_qdiv_total (arith_atom_denote_real M t1) (arith_atom_denote_real M t2) := by
  have ht : term_has_non_none_type ((__eo_to_smt t1).qdiv_total (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
          SmtType.None := by
      rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
        SmtTerm.qdiv_total (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
      exact hNone
    cases hTy.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simpa [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simpa [term_has_non_none_type, hArgs.2])
    rcases int_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨n1, hEval1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨n2, hEval2⟩
    unfold arith_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
      SmtTerm.qdiv_total (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    simp [__smtx_model_eval, hEval1, hEval2, __smtx_model_eval_to_real,
      __smtx_model_eval_qdiv_total, arith_atom_denote_real, native_to_real_qdiv_total]
  · have hEval1Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
          __smtx_typeof (__eo_to_smt t1) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
        (by simpa [term_has_non_none_type, hArgs.1])
    have hEval2Ty :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
          __smtx_typeof (__eo_to_smt t2) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
        (by simpa [term_has_non_none_type, hArgs.2])
    rcases real_value_canonical (by simpa [hArgs.1] using hEval1Ty) with ⟨q1, hEval1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hEval2Ty) with ⟨q2, hEval2⟩
    unfold arith_atom_denote_real
    rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
      SmtTerm.qdiv_total (__eo_to_smt t1) (__eo_to_smt t2) by rfl]
    simp [__smtx_model_eval, hEval1, hEval2, __smtx_model_eval_to_real,
      __smtx_model_eval_qdiv_total]

private def arith_atomic_poly (t : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp._at__at_poly)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_mon)
          (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil))
        (Term.Rational (native_mk_rational 1 1))))
    (Term.UOp UserOp._at__at_Polynomial)

private theorem arith_atomic_poly_injective
    {a b : Term} :
  arith_atomic_poly a = arith_atomic_poly b ->
  a = b := by
  intro h
  simpa [arith_atomic_poly] using h

private theorem arith_mvar_wf_singleton
    (t : Term) :
  arith_mvar_wf (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil) := by
  exact arith_mvar_wf.cons t Term.__eo_List_nil arith_mvar_wf.nil

private theorem arith_mvar_rational_singleton
    (M : SmtModel) (t : Term)
    (hRat : ∃ q, arith_atom_denote_real M t = SmtValue.Rational q) :
  arith_mvar_rational M (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil) := by
  exact arith_mvar_rational.cons t Term.__eo_List_nil hRat (arith_mvar_rational.nil (M := M))

private theorem arith_poly_wf_of_arith_atomic_poly
    (t : Term) :
  arith_poly_wf (arith_atomic_poly t) := by
  unfold arith_atomic_poly
  exact arith_poly_wf.cons
    (Term.Apply
      (Term.Apply (Term.UOp UserOp._at__at_mon)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil))
      (Term.Rational (native_mk_rational 1 1)))
    (Term.UOp UserOp._at__at_Polynomial)
    (arith_mon_wf.mk
      (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil)
      (native_mk_rational 1 1)
      (arith_mvar_wf_singleton t))
    arith_poly_wf.zero

private theorem arith_poly_rational_of_arith_atomic_poly
    (M : SmtModel) (t : Term)
    (hRat : ∃ q, arith_atom_denote_real M t = SmtValue.Rational q) :
  arith_poly_rational M (arith_atomic_poly t) := by
  unfold arith_atomic_poly
  exact arith_poly_rational.cons
    (M := M)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp._at__at_mon)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil))
      (Term.Rational (native_mk_rational 1 1)))
    (Term.UOp UserOp._at__at_Polynomial)
    (arith_mon_rational.mk
      (M := M)
      (Term.Apply (Term.Apply Term.__eo_List_cons t) Term.__eo_List_nil)
      (native_mk_rational 1 1)
      (arith_mvar_rational_singleton M t hRat))
    (arith_poly_rational.zero (M := M))

private theorem arith_poly_denote_real_of_arith_atomic_poly
    (M : SmtModel) (t : Term) :
  arith_poly_denote_real M (arith_atomic_poly t) = arith_atom_denote_real M t := by
  rcases arith_atom_denote_real_rational_or_notValue M t with hAtom | hAtom
  · rcases hAtom with ⟨q, hAtom⟩
    rw [arith_atomic_poly, arith_poly_denote_real, arith_mon_denote_real, arith_mvar_denote_real,
      hAtom]
    simp [arith_mvar_denote_real, arith_poly_denote_real, __smtx_model_eval_mult,
      __smtx_model_eval_plus, native_qmult, native_qplus, native_mk_rational_zero,
      native_mk_rational_one, Rat.mul_assoc, Rat.one_mul, Rat.mul_one, Rat.add_zero]
  · rw [arith_atomic_poly, arith_poly_denote_real, arith_mon_denote_real, arith_mvar_denote_real,
      hAtom]
    simp [__smtx_model_eval_mult, __smtx_model_eval_plus]

private theorem arith_poly_denote_real_eq_arith_atom_denote_real_of_norm_eq_atomic
    (M : SmtModel) (t : Term)
    (hNorm : __get_arith_poly_norm t = arith_atomic_poly t) :
  arith_poly_denote_real M (__get_arith_poly_norm t) = arith_atom_denote_real M t := by
  rw [hNorm]
  exact arith_poly_denote_real_of_arith_atomic_poly M t

private theorem eo_to_smt_uneg_eq
    (x : Term) :
  __eo_to_smt (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) =
    (__eo_to_smt x).uneg := by
  rfl

private theorem eo_to_smt_to_real_eq
    (x : Term) :
  __eo_to_smt (Term.Apply (Term.UOp UserOp.to_real) x) =
    (__eo_to_smt x).to_real := by
  rfl

private theorem eo_to_smt_plus_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) y) x) =
    (__eo_to_smt y).plus (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_neg_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x) =
    (__eo_to_smt y).neg (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_mult_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x) =
    (__eo_to_smt y).mult (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_qdiv_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) x) =
    (__eo_to_smt y).qdiv (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_qdiv_total_eq
    (y x : Term) :
  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) x) =
    (__eo_to_smt y).qdiv_total (__eo_to_smt x) := by
  rfl

private theorem get_arith_poly_norm_of_non_arith_smt_type
    (t : Term)
    (hNotInt : __smtx_typeof (__eo_to_smt t) ≠ SmtType.Int)
    (hNotReal : __smtx_typeof (__eo_to_smt t) ≠ SmtType.Real)
    (hNonNone : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
  __get_arith_poly_norm t = arith_atomic_poly t := by
  cases t with
  | Numeral n =>
      exfalso
      exact hNotInt (by
        rw [show __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n by rfl]
        rw [__smtx_typeof.eq_2])
  | Rational q =>
      exfalso
      exact hNotReal (by
        rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl]
        rw [__smtx_typeof.eq_3])
  | Stuck =>
      exfalso
      exact hNonNone (by
        rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl]
        exact TranslationProofs.smtx_typeof_none)
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;>
            try
              simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
                SmtEval.native_and, SmtEval.native_not]
          case __eoo_neg_2 =>
            exfalso
            have ht : term_has_non_none_type ((__eo_to_smt x).uneg) := by
              unfold term_has_non_none_type
              rw [← eo_to_smt_uneg_eq x]
              exact hNonNone
            rcases arith_unop_arg_of_non_none
                (op := SmtTerm.uneg) (t := __eo_to_smt x)
                (typeof_uneg_eq (__eo_to_smt x)) ht with hArg | hArg
            · exact hNotInt <| by
                rw [eo_to_smt_uneg_eq, typeof_uneg_eq]
                simp [__smtx_typeof_arith_overload_op_1, hArg]
            · exact hNotReal <| by
                rw [eo_to_smt_uneg_eq, typeof_uneg_eq]
                simp [__smtx_typeof_arith_overload_op_1, hArg]
          case to_real =>
            exfalso
            have ht : term_has_non_none_type ((__eo_to_smt x).to_real) := by
              unfold term_has_non_none_type
              rw [← eo_to_smt_to_real_eq x]
              exact hNonNone
            rcases to_real_arg_of_non_none (t := __eo_to_smt x) ht with hArg | hArg
            · exact hNotReal <| by
                rw [eo_to_smt_to_real_eq, typeof_to_real_eq]
                simp [native_ite, native_Teq, hArg]
            · exact hNotReal <| by
                rw [eo_to_smt_to_real_eq, typeof_to_real_eq]
                simp [native_ite, native_Teq, hArg]
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;>
                try
                  simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                    __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
                    SmtEval.native_and, SmtEval.native_not]
              case plus =>
                exfalso
                have ht : term_has_non_none_type
                    (SmtTerm.plus (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_plus_eq y x]
                  exact hNonNone
                rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
                    (typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                · exact hNotInt <| by
                    rw [eo_to_smt_plus_eq, typeof_plus_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_plus_eq, typeof_plus_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
              case neg =>
                exfalso
                have ht : term_has_non_none_type
                    (SmtTerm.neg (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_neg_eq y x]
                  exact hNonNone
                rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
                    (typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                · exact hNotInt <| by
                    rw [eo_to_smt_neg_eq, typeof_neg_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_neg_eq, typeof_neg_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
              case mult =>
                exfalso
                have ht : term_has_non_none_type
                    (SmtTerm.mult (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_mult_eq y x]
                  exact hNonNone
                rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
                    (typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                · exact hNotInt <| by
                    rw [eo_to_smt_mult_eq, typeof_mult_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_mult_eq, typeof_mult_eq]
                    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
              case qdiv =>
                exfalso
                have ht : term_has_non_none_type
                    (SmtTerm.qdiv (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_qdiv_eq y x]
                  exact hNonNone
                rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv)
                    (R := SmtType.Real)
                    (typeof_qdiv_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                · exact hNotReal <| by
                    rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
                    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
                    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
              case qdiv_total =>
                exfalso
                have ht : term_has_non_none_type
                    ((__eo_to_smt y).qdiv_total (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_qdiv_total_eq y x]
                  exact hNonNone
                rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total)
                    (R := SmtType.Real)
                    (typeof_qdiv_total_eq (__eo_to_smt y) (__eo_to_smt x)) ht with
                    hArgs | hArgs
                · exact hNotReal <| by
                    rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
                    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
                · exact hNotReal <| by
                    rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
                    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
          | _ =>
              simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
                SmtEval.native_and, SmtEval.native_not]
      | _ =>
          simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
            __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not]
  | _ =>
      simp [__get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
        __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
        SmtEval.native_and, SmtEval.native_not]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_of_non_arith_smt_type
    (M : SmtModel) (t : Term)
    (hNotInt : __smtx_typeof (__eo_to_smt t) ≠ SmtType.Int)
    (hNotReal : __smtx_typeof (__eo_to_smt t) ≠ SmtType.Real)
    (hNonNone : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
  arith_poly_denote_real M (__get_arith_poly_norm t) = arith_atom_denote_real M t := by
  exact arith_poly_denote_real_eq_arith_atom_denote_real_of_norm_eq_atomic M t
    (get_arith_poly_norm_of_non_arith_smt_type t hNotInt hNotReal hNonNone)

private theorem non_none_of_smt_arith_type
    {t : SmtTerm}
    (hTy : __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real) :
  term_has_non_none_type t := by
  unfold term_has_non_none_type
  intro hNone
  rcases hTy with hInt | hReal
  · cases hInt.symm.trans hNone
  · cases hReal.symm.trans hNone

private theorem arith_poly_rational_of_const_poly
    (M : SmtModel) (q : native_Rat) :
  arith_poly_rational M
    (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) (arith_const_mon q))
      (Term.UOp UserOp._at__at_Polynomial)) := by
  exact arith_poly_rational.cons
    (M := M)
    (arith_const_mon q)
    (Term.UOp UserOp._at__at_Polynomial)
    (arith_mon_rational.mk
      (M := M)
      Term.__eo_List_nil
      q
      (arith_mvar_rational.nil (M := M)))
    (arith_poly_rational.zero (M := M))

private theorem arith_poly_rational_of_get_arith_poly_norm_rational
    (M : SmtModel) (q : native_Rat) :
  arith_poly_rational M (__get_arith_poly_norm (Term.Rational q)) := by
  by_cases hZero : q = native_mk_rational 0 1
  · subst q
    have hGet :
        __get_arith_poly_norm (Term.Rational (native_mk_rational 0 1)) =
          Term.UOp UserOp._at__at_Polynomial := by
      native_decide
    rw [hGet]
    exact arith_poly_rational.zero (M := M)
  · have hZero' : ¬ native_mk_rational 0 1 = q := by
      simpa [eq_comm] using hZero
    have hDec : decide (native_mk_rational 0 1 = q) = false := by
      simp [hZero']
    have hGet :
        __get_arith_poly_norm (Term.Rational q) =
          Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly) (arith_const_mon q))
            (Term.UOp UserOp._at__at_Polynomial) := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hDec, SmtEval.native_and, SmtEval.native_not,
        arith_const_mon, __eo_mk_apply]
    rw [hGet]
    exact arith_poly_rational_of_const_poly M q

private theorem arith_poly_rational_of_get_arith_poly_norm_numeral
    (M : SmtModel) (n : native_Int) :
  arith_poly_rational M (__get_arith_poly_norm (Term.Numeral n)) := by
  by_cases hZero : native_to_real n = native_mk_rational 0 1
  · have hGet :
        __get_arith_poly_norm (Term.Numeral n) =
          Term.UOp UserOp._at__at_Polynomial := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hZero, SmtEval.native_and, SmtEval.native_not]
    rw [hGet]
    exact arith_poly_rational.zero (M := M)
  · have hZero' : ¬ native_mk_rational 0 1 = native_to_real n := by
      simpa [eq_comm] using hZero
    have hDec : decide (native_mk_rational 0 1 = native_to_real n) = false := by
      simp [hZero']
    have hGet :
        __get_arith_poly_norm (Term.Numeral n) =
          Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_poly) (arith_const_mon (native_to_real n)))
            (Term.UOp UserOp._at__at_Polynomial) := by
      simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_is_eq,
        __eo_ite, native_ite, native_teq, hDec, SmtEval.native_and, SmtEval.native_not,
        arith_const_mon, __eo_mk_apply]
    rw [hGet]
    exact arith_poly_rational_of_const_poly M (native_to_real n)

private theorem arith_poly_rational_of_get_arith_poly_norm_eq_atomic_of_smt_arith_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real)
    (hNorm : __get_arith_poly_norm t = arith_atomic_poly t) :
  arith_poly_rational M (__get_arith_poly_norm t) := by
  rw [hNorm]
  exact arith_poly_rational_of_arith_atomic_poly M t
    (arith_atom_denote_real_rational_of_smt_arith_type M hM t hTy)

private theorem arith_poly_denote_real_of_get_arith_poly_norm_rational
    (M : SmtModel) (q : native_Rat) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Rational q)) =
    arith_atom_denote_real M (Term.Rational q) := by
  rw [arith_poly_denote_real_of_rational, arith_atom_denote_real_of_rational]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_numeral
    (M : SmtModel) (n : native_Int) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Numeral n)) =
    arith_atom_denote_real M (Term.Numeral n) := by
  rw [arith_poly_denote_real_of_numeral, arith_atom_denote_real_of_numeral]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_to_real
    (M : SmtModel) (t : Term)
    (hRec : arith_poly_denote_real M (__get_arith_poly_norm t) = arith_atom_denote_real M t) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.to_real) t)) =
    arith_atom_denote_real M (Term.Apply (Term.UOp UserOp.to_real) t) := by
  simpa [__get_arith_poly_norm, arith_atom_denote_real_of_to_real] using hRec

private theorem arith_poly_wf_of_get_arith_poly_norm_of_non_arith_smt_type
    (t : Term)
    (hNotInt : __smtx_typeof (__eo_to_smt t) ≠ SmtType.Int)
    (hNotReal : __smtx_typeof (__eo_to_smt t) ≠ SmtType.Real)
    (hNonNone : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None) :
  arith_poly_wf (__get_arith_poly_norm t) := by
  rw [get_arith_poly_norm_of_non_arith_smt_type t hNotInt hNotReal hNonNone]
  exact arith_poly_wf_of_arith_atomic_poly t

private theorem arith_poly_wf_of_get_arith_poly_norm_to_real
    (t : Term)
    (hRec : arith_poly_wf (__get_arith_poly_norm t)) :
  arith_poly_wf (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.to_real) t)) := by
  simpa [__get_arith_poly_norm] using hRec

private theorem arith_poly_rational_of_get_arith_poly_norm_to_real
    (M : SmtModel) (t : Term)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t)) :
  arith_poly_rational M (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.to_real) t)) := by
  simpa [__get_arith_poly_norm] using hRec

private theorem arith_poly_wf_of_get_arith_poly_norm_uneg
    (t : Term)
    (hRec : arith_poly_wf (__get_arith_poly_norm t)) :
  arith_poly_wf (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t)) := by
  simpa [__get_arith_poly_norm] using arith_poly_wf_of_poly_neg hRec

private theorem arith_poly_rational_of_get_arith_poly_norm_uneg
    (M : SmtModel) (t : Term)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t)) :
  arith_poly_rational M (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t)) := by
  simpa [__get_arith_poly_norm] using arith_poly_rational_of_poly_neg M hRec

private theorem arith_poly_wf_of_get_arith_poly_norm_plus
    (t1 t2 : Term)
    (hRec1 : arith_poly_wf (__get_arith_poly_norm t1))
    (hRec2 : arith_poly_wf (__get_arith_poly_norm t2)) :
  arith_poly_wf
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) := by
  simpa [__get_arith_poly_norm] using arith_poly_wf_of_poly_add hRec1 hRec2

private theorem arith_poly_rational_of_get_arith_poly_norm_plus
    (M : SmtModel) (t1 t2 : Term)
    (hRec1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec2 : arith_poly_rational M (__get_arith_poly_norm t2)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) := by
  simpa [__get_arith_poly_norm] using arith_poly_rational_of_poly_add M hRec1 hRec2

private theorem arith_poly_wf_of_get_arith_poly_norm_neg
    (t1 t2 : Term)
    (hRec1 : arith_poly_wf (__get_arith_poly_norm t1))
    (hRec2 : arith_poly_wf (__get_arith_poly_norm t2)) :
  arith_poly_wf
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) := by
  simpa [__get_arith_poly_norm] using
    arith_poly_wf_of_poly_add hRec1 (arith_poly_wf_of_poly_neg hRec2)

private theorem arith_poly_rational_of_get_arith_poly_norm_neg
    (M : SmtModel) (t1 t2 : Term)
    (hRec1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec2 : arith_poly_rational M (__get_arith_poly_norm t2)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) := by
  simpa [__get_arith_poly_norm] using
    arith_poly_rational_of_poly_add M hRec1 (arith_poly_rational_of_poly_neg M hRec2)

private theorem arith_poly_rational_of_get_arith_poly_norm_mult
    (M : SmtModel) (t1 t2 : Term)
    (hRec1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec2 : arith_poly_rational M (__get_arith_poly_norm t2)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) := by
  simpa [__get_arith_poly_norm] using arith_poly_rational_of_poly_mul M hRec1 hRec2

private theorem arith_poly_denote_real_of_get_arith_poly_norm_uneg
    (M : SmtModel) (t : Term)
    (hWf : arith_poly_wf (__get_arith_poly_norm t))
    (hRec : arith_poly_denote_real M (__get_arith_poly_norm t) = arith_atom_denote_real M t) :
  arith_poly_denote_real M (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t)) =
    arith_atom_denote_real M (Term.Apply (Term.UOp UserOp.__eoo_neg_2) t) := by
  rw [__get_arith_poly_norm, arith_poly_denote_real_of_poly_neg_wf M hWf,
    arith_atom_denote_real_of_uneg]
  simpa [hRec]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_plus
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
        SmtType.Real)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRat2 : arith_poly_rational M (__get_arith_poly_norm t2))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_atom_denote_real M t1)
    (hRec2 : arith_poly_denote_real M (__get_arith_poly_norm t2) = arith_atom_denote_real M t2) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2)) =
    arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.plus) t1) t2) := by
  rw [__get_arith_poly_norm, arith_poly_denote_real_of_poly_add_rational M hRat1 hRat2, hRec1,
    hRec2]
  exact (arith_atom_denote_real_of_plus M hM t1 t2 hTy).symm

private theorem arith_poly_denote_real_of_get_arith_poly_norm_neg
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
        SmtType.Real)
    (hWf2 : arith_poly_wf (__get_arith_poly_norm t2))
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRat2 : arith_poly_rational M (__get_arith_poly_norm t2))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_atom_denote_real M t1)
    (hRec2 : arith_poly_denote_real M (__get_arith_poly_norm t2) = arith_atom_denote_real M t2) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2)) =
    arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.neg) t1) t2) := by
  have hNegRec :
      arith_poly_denote_real M (__poly_neg (__get_arith_poly_norm t2)) =
        __smtx_model_eval_uneg (arith_atom_denote_real M t2) := by
    rw [arith_poly_denote_real_of_poly_neg_wf M hWf2, hRec2]
  rw [__get_arith_poly_norm,
    arith_poly_denote_real_of_poly_add_rational M hRat1
      (arith_poly_rational_of_poly_neg M hRat2),
    hRec1, hNegRec]
  exact (arith_atom_denote_real_of_neg M hM t1 t2 hTy).symm

private theorem arith_poly_denote_real_of_get_arith_poly_norm_mult
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
        SmtType.Real)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRat2 : arith_poly_rational M (__get_arith_poly_norm t2))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_atom_denote_real M t1)
    (hRec2 : arith_poly_denote_real M (__get_arith_poly_norm t2) = arith_atom_denote_real M t2) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2)) =
    arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.mult) t1) t2) := by
  rw [__get_arith_poly_norm, arith_poly_denote_real_of_poly_mul_rational M hRat1 hRat2, hRec1,
    hRec2]
  exact (arith_atom_denote_real_of_mult M hM t1 t2 hTy).symm

private theorem get_arith_poly_norm_qdiv_of_rational
    (t1 : Term) (q : native_Rat)
    (hZero : q ≠ native_mk_rational 0 1) :
  __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q)) =
    __poly_mul_mon
      (arith_const_mon (native_qdiv_total (native_mk_rational 1 1) q))
      (__get_arith_poly_norm t1) := by
  have hZero' : native_mk_rational 0 1 ≠ q := by
    simpa [eq_comm] using hZero
  simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
    __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, native_qeq, __eo_qdiv,
    hZero', arith_const_mon, __eo_mk_apply]

private theorem get_arith_poly_norm_qdiv_total_of_rational
    (t1 : Term) (q : native_Rat)
    (hZero : q ≠ native_mk_rational 0 1) :
  __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Rational q)) =
    __poly_mul_mon
      (arith_const_mon (native_qdiv_total (native_mk_rational 1 1) q))
      (__get_arith_poly_norm t1) := by
  have hZero' : native_mk_rational 0 1 ≠ q := by
    simpa [eq_comm] using hZero
  simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
    __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, native_qeq, __eo_qdiv,
    hZero', arith_const_mon, __eo_mk_apply]

private theorem arith_poly_rational_of_get_arith_poly_norm_qdiv_of_rational
    (M : SmtModel) (t1 : Term) (q : native_Rat)
    (hZero : q ≠ native_mk_rational 0 1)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t1)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q))) := by
  rw [get_arith_poly_norm_qdiv_of_rational t1 q hZero]
  exact arith_poly_rational_of_poly_mul_mon_const M
    (native_qdiv_total (native_mk_rational 1 1) q) hRec

private theorem arith_poly_rational_of_get_arith_poly_norm_qdiv_total_of_rational
    (M : SmtModel) (t1 : Term) (q : native_Rat)
    (hZero : q ≠ native_mk_rational 0 1)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t1)) :
  arith_poly_rational M
    (__get_arith_poly_norm
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Rational q))) := by
  rw [get_arith_poly_norm_qdiv_total_of_rational t1 q hZero]
  exact arith_poly_rational_of_poly_mul_mon_const M
    (native_qdiv_total (native_mk_rational 1 1) q) hRec

private theorem get_arith_poly_norm_qdiv_of_numeral
    (t1 : Term) (n : native_Int)
    (hZero : native_to_real n ≠ native_mk_rational 0 1) :
  __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n)) =
    __poly_mul_mon
      (arith_const_mon (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)))
      (__get_arith_poly_norm t1) := by
  have hZero' : native_mk_rational 0 1 ≠ native_to_real n := by
    simpa [eq_comm] using hZero
  simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
    __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, native_qeq, __eo_qdiv,
    hZero', arith_const_mon, __eo_mk_apply]

private theorem get_arith_poly_norm_qdiv_total_of_numeral
    (t1 : Term) (n : native_Int)
    (hZero : native_to_real n ≠ native_mk_rational 0 1) :
  __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) =
    __poly_mul_mon
      (arith_const_mon (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)))
      (__get_arith_poly_norm t1) := by
  have hZero' : native_mk_rational 0 1 ≠ native_to_real n := by
    simpa [eq_comm] using hZero
  simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
    __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, native_qeq, __eo_qdiv,
    hZero', arith_const_mon, __eo_mk_apply]

private theorem arith_poly_rational_of_get_arith_poly_norm_qdiv_of_numeral
    (M : SmtModel) (t1 : Term) (n : native_Int)
    (hZero : native_to_real n ≠ native_mk_rational 0 1)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t1)) :
  arith_poly_rational M
    (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n))) := by
  rw [get_arith_poly_norm_qdiv_of_numeral t1 n hZero]
  exact arith_poly_rational_of_poly_mul_mon_const M
    (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)) hRec

private theorem arith_poly_rational_of_get_arith_poly_norm_qdiv_total_of_numeral
    (M : SmtModel) (t1 : Term) (n : native_Int)
    (hZero : native_to_real n ≠ native_mk_rational 0 1)
    (hRec : arith_poly_rational M (__get_arith_poly_norm t1)) :
  arith_poly_rational M
    (__get_arith_poly_norm
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n))) := by
  rw [get_arith_poly_norm_qdiv_total_of_numeral t1 n hZero]
  exact arith_poly_rational_of_poly_mul_mon_const M
    (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)) hRec

private theorem smt_typeof_qdiv_left_of_rational_right
    (t1 : Term) (q : native_Rat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Rational q))) = SmtType.Real) :
  __smtx_typeof (__eo_to_smt t1) = SmtType.Real := by
  have ht : term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt t1) (__eo_to_smt (Term.Rational q))) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
          (Term.Rational q))) = SmtType.None := by
      rw [eo_to_smt_qdiv_eq]
      exact hNone
    cases hTy.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt t1) (__eo_to_smt (Term.Rational q))) ht with hArgs | hArgs
  · have hQTy : __smtx_typeof (__eo_to_smt (Term.Rational q)) = SmtType.Real := by
      rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl]
      rw [__smtx_typeof.eq_3]
    cases hQTy.symm.trans hArgs.2
  · exact hArgs.1

private theorem arith_atom_denote_real_of_qdiv_rational
    (M : SmtModel) (hM : model_total_typed M) (t1 : Term) (q : native_Rat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Rational q))) = SmtType.Real)
    (hZero : q ≠ native_mk_rational 0 1) :
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q)) =
    __smtx_model_eval_qdiv_total (arith_atom_denote_real M t1) (SmtValue.Rational q) := by
  have hT1Real : __smtx_typeof (__eo_to_smt t1) = SmtType.Real :=
    smt_typeof_qdiv_left_of_rational_right t1 q hTy
  have hEval1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
        __smtx_typeof (__eo_to_smt t1) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
      (by simpa [term_has_non_none_type, hT1Real])
  rcases real_value_canonical (by simpa [hT1Real] using hEval1Ty) with ⟨q1, hEval1⟩
  have hZero' : native_mk_rational 0 1 ≠ q := by
    simpa [eq_comm] using hZero
  have hAtom1 : arith_atom_denote_real M t1 = SmtValue.Rational q1 := by
    simp [arith_atom_denote_real, hEval1, __smtx_model_eval_to_real]
  have hEvalQ : __smtx_model_eval M (__eo_to_smt (Term.Rational q)) = SmtValue.Rational q := by
    rw [show __eo_to_smt (Term.Rational q) = SmtTerm.Rational q by rfl]
    simp [__smtx_model_eval]
  rw [hAtom1]
  unfold arith_atom_denote_real
  rw [eo_to_smt_qdiv_eq, __smtx_model_eval.eq_128, hEvalQ, hEval1]
  simp [__smtx_model_eval_to_real, __smtx_model_eval_qdiv_total, __smtx_model_eval_ite,
    __smtx_model_eval_eq, native_veq, hZero, hZero']

private theorem smt_typeof_qdiv_left_of_numeral_right
    (t1 : Term) (n : native_Int)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Numeral n))) = SmtType.Real) :
  __smtx_typeof (__eo_to_smt t1) = SmtType.Int := by
  have ht : term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt t1) (__eo_to_smt (Term.Numeral n))) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
          (Term.Numeral n))) = SmtType.None := by
      rw [eo_to_smt_qdiv_eq]
      exact hNone
    cases hTy.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt t1) (__eo_to_smt (Term.Numeral n))) ht with hArgs | hArgs
  · exact hArgs.1
  · have hNTy : __smtx_typeof (__eo_to_smt (Term.Numeral n)) = SmtType.Int := by
      rw [show __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n by rfl]
      rw [__smtx_typeof.eq_2]
    cases hNTy.symm.trans hArgs.2

private theorem arith_atom_denote_real_of_qdiv_numeral
    (M : SmtModel) (hM : model_total_typed M) (t1 : Term) (n : native_Int)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Numeral n))) = SmtType.Real) :
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n)) =
    __smtx_model_eval_qdiv_total (arith_atom_denote_real M t1)
      (SmtValue.Rational (native_to_real n)) := by
  have hT1Int : __smtx_typeof (__eo_to_smt t1) = SmtType.Int :=
    smt_typeof_qdiv_left_of_numeral_right t1 n hTy
  have hEval1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
        __smtx_typeof (__eo_to_smt t1) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
      (by simpa [term_has_non_none_type, hT1Int])
  rcases int_value_canonical (by simpa [hT1Int] using hEval1Ty) with ⟨n1, hEval1⟩
  have hAtom1 : arith_atom_denote_real M t1 = SmtValue.Rational (native_to_real n1) := by
    simp [arith_atom_denote_real, hEval1, __smtx_model_eval_to_real]
  have hEvalN : __smtx_model_eval M (__eo_to_smt (Term.Numeral n)) = SmtValue.Numeral n := by
    rw [show __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n by rfl]
    simp [__smtx_model_eval]
  have hZeroTest :
      __smtx_model_eval_eq (SmtValue.Numeral n)
        (SmtValue.Rational (native_mk_rational 0 1)) =
        SmtValue.Boolean false := by
    simp [__smtx_model_eval_eq, native_veq]
  rw [hAtom1]
  unfold arith_atom_denote_real
  rw [eo_to_smt_qdiv_eq]
  simp [__smtx_model_eval, hEval1, hEvalN, hZeroTest, __smtx_model_eval_ite,
    __smtx_model_eval_to_real, __smtx_model_eval_qdiv_total, native_to_real_qdiv_total]

private theorem smtx_model_eval_mult_const_recip_eq_qdiv_total
    (q1 q : native_Rat) :
  __smtx_model_eval_mult
      (SmtValue.Rational (native_qdiv_total (native_mk_rational 1 1) q))
      (SmtValue.Rational q1) =
    __smtx_model_eval_qdiv_total (SmtValue.Rational q1) (SmtValue.Rational q) := by
  simp [__smtx_model_eval_mult, __smtx_model_eval_qdiv_total, native_qmult, native_qdiv_total,
    native_mk_rational_one, Rat.div_def, Rat.mul_comm]

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_of_rational
    (M : SmtModel) (hM : model_total_typed M) (t1 : Term) (q : native_Rat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Rational q))) = SmtType.Real)
    (hZero : q ≠ native_mk_rational 0 1)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_atom_denote_real M t1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q))) =
    arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Rational q)) := by
  rcases arith_poly_denote_real_rational_of_rational_support M hRat1 with ⟨q1, hPoly1⟩
  have hAtom1 : arith_atom_denote_real M t1 = SmtValue.Rational q1 := by
    rw [← hRec1]
    exact hPoly1
  rw [get_arith_poly_norm_qdiv_of_rational t1 q hZero,
    arith_poly_denote_real_of_poly_mul_mon_const_rational M
      (native_qdiv_total (native_mk_rational 1 1) q) hRat1,
    hRec1]
  rw [arith_atom_denote_real_of_qdiv_rational M hM t1 q hTy hZero, hAtom1]
  exact smtx_model_eval_mult_const_recip_eq_qdiv_total q1 q

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_of_numeral
    (M : SmtModel) (hM : model_total_typed M) (t1 : Term) (n : native_Int)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1)
        (Term.Numeral n))) = SmtType.Real)
    (hZero : native_to_real n ≠ native_mk_rational 0 1)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_atom_denote_real M t1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n))) =
    arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) (Term.Numeral n)) := by
  rcases arith_poly_denote_real_rational_of_rational_support M hRat1 with ⟨q1, hPoly1⟩
  have hAtom1 : arith_atom_denote_real M t1 = SmtValue.Rational q1 := by
    rw [← hRec1]
    exact hPoly1
  rw [get_arith_poly_norm_qdiv_of_numeral t1 n hZero,
    arith_poly_denote_real_of_poly_mul_mon_const_rational M
      (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)) hRat1,
    hRec1]
  rw [arith_atom_denote_real_of_qdiv_numeral M hM t1 n hTy, hAtom1]
  exact smtx_model_eval_mult_const_recip_eq_qdiv_total q1 (native_to_real n)

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_rational
    (M : SmtModel) (hM : model_total_typed M) (t1 : Term) (q : native_Rat)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1)
        (Term.Rational q))) = SmtType.Real)
    (hZero : q ≠ native_mk_rational 0 1)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_atom_denote_real M t1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Rational q))) =
    arith_atom_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Rational q)) := by
  rcases arith_poly_denote_real_rational_of_rational_support M hRat1 with ⟨q1, hPoly1⟩
  have hAtom1 : arith_atom_denote_real M t1 = SmtValue.Rational q1 := by
    rw [← hRec1]
    exact hPoly1
  rw [get_arith_poly_norm_qdiv_total_of_rational t1 q hZero,
    arith_poly_denote_real_of_poly_mul_mon_const_rational M
      (native_qdiv_total (native_mk_rational 1 1) q) hRat1,
    hRec1]
  rw [arith_atom_denote_real_of_qdiv_total M hM t1 (Term.Rational q) hTy, hAtom1,
    arith_atom_denote_real_of_rational]
  exact smtx_model_eval_mult_const_recip_eq_qdiv_total q1 q

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_numeral
    (M : SmtModel) (hM : model_total_typed M) (t1 : Term) (n : native_Int)
    (hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1)
        (Term.Numeral n))) = SmtType.Real)
    (hZero : native_to_real n ≠ native_mk_rational 0 1)
    (hRat1 : arith_poly_rational M (__get_arith_poly_norm t1))
    (hRec1 : arith_poly_denote_real M (__get_arith_poly_norm t1) = arith_atom_denote_real M t1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n))) =
    arith_atom_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) := by
  rcases arith_poly_denote_real_rational_of_rational_support M hRat1 with ⟨q1, hPoly1⟩
  have hAtom1 : arith_atom_denote_real M t1 = SmtValue.Rational q1 := by
    rw [← hRec1]
    exact hPoly1
  rw [get_arith_poly_norm_qdiv_total_of_numeral t1 n hZero,
    arith_poly_denote_real_of_poly_mul_mon_const_rational M
      (native_qdiv_total (native_mk_rational 1 1) (native_to_real n)) hRat1,
    hRec1]
  rw [arith_atom_denote_real_of_qdiv_total M hM t1 (Term.Numeral n) hTy, hAtom1,
    arith_atom_denote_real_of_numeral]
  exact smtx_model_eval_mult_const_recip_eq_qdiv_total q1 (native_to_real n)

private theorem smt_typeof_qdiv_of_smt_arith_type
    (t1 t2 : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
        SmtType.Real) :
  __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
    SmtType.Real := by
  have ht : term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt t1) (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
          SmtType.None := by
      rw [eo_to_smt_qdiv_eq]
      exact hNone
    rcases hTy with hInt | hReal
    · cases hInt.symm.trans hNone'
    · cases hReal.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
  · rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]

private theorem smt_typeof_qdiv_total_of_smt_arith_type
    (t1 t2 : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
        SmtType.Int ∨
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
        SmtType.Real) :
  __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
    SmtType.Real := by
  have ht : term_has_non_none_type ((__eo_to_smt t1).qdiv_total (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
          SmtType.None := by
      rw [eo_to_smt_qdiv_total_eq]
      exact hNone
    rcases hTy with hInt | hReal
    · cases hInt.symm.trans hNone'
    · cases hReal.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
  · rw [eo_to_smt_qdiv_total_eq, typeof_qdiv_total_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]

private theorem smt_typeof_qdiv_of_qdiv_total
    (t1 t2 : Term)
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
        SmtType.Real) :
  __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
    SmtType.Real := by
  have ht : term_has_non_none_type ((__eo_to_smt t1).qdiv_total (__eo_to_smt t2)) := by
    unfold term_has_non_none_type
    intro hNone
    have hNone' :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
          SmtType.None := by
      rw [eo_to_smt_qdiv_total_eq]
      exact hNone
    cases hTy.symm.trans hNone'
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt t1) (__eo_to_smt t2)) ht with hArgs | hArgs
  · rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
  · rw [eo_to_smt_qdiv_eq, typeof_qdiv_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]

private theorem arith_atom_denote_real_qdiv_eq_qdiv_total_of_int_args
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hTy1 : __smtx_typeof (__eo_to_smt t1) = SmtType.Int)
    (hTy2 : __smtx_typeof (__eo_to_smt t2) = SmtType.Int) :
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2) =
    arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) := by
  have hEval1Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t1)) =
        __smtx_typeof (__eo_to_smt t1) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t1)
      (by simpa [term_has_non_none_type, hTy1])
  have hEval2Ty :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t2)) =
        __smtx_typeof (__eo_to_smt t2) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t2)
      (by simpa [term_has_non_none_type, hTy2])
  rcases int_value_canonical (by simpa [hTy1] using hEval1Ty) with ⟨n1, hEval1⟩
  rcases int_value_canonical (by simpa [hTy2] using hEval2Ty) with ⟨n2, hEval2⟩
  have hZeroTest :
      __smtx_model_eval_eq (SmtValue.Numeral n2)
        (SmtValue.Rational (native_mk_rational 0 1)) =
        SmtValue.Boolean false := by
    simp [__smtx_model_eval_eq, native_veq]
  have hQdiv :
      arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2) =
        SmtValue.Rational (native_mk_rational n1 n2) := by
    unfold arith_atom_denote_real
    rw [eo_to_smt_qdiv_eq]
    simp [__smtx_model_eval, hEval1, hEval2, hZeroTest, __smtx_model_eval_ite,
      __smtx_model_eval_to_real, __smtx_model_eval_qdiv_total]
  have hQdivTotal :
      arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
        SmtValue.Rational (native_mk_rational n1 n2) := by
    unfold arith_atom_denote_real
    rw [eo_to_smt_qdiv_total_eq]
    simp [__smtx_model_eval, hEval1, hEval2, __smtx_model_eval_to_real,
      __smtx_model_eval_qdiv_total, native_to_real_qdiv_total]
  exact hQdiv.trans hQdivTotal.symm

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_eq_atomic_qdiv_of_int_args
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hNorm :
      __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
        arith_atomic_poly (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2))
    (hTy1 : __smtx_typeof (__eo_to_smt t1) = SmtType.Int)
    (hTy2 : __smtx_typeof (__eo_to_smt t2) = SmtType.Int) :
  arith_poly_denote_real M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) =
    arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) := by
  rw [hNorm, arith_poly_denote_real_of_arith_atomic_poly]
  exact arith_atom_denote_real_qdiv_eq_qdiv_total_of_int_args M hM t1 t2 hTy1 hTy2

private theorem arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_numeral_zero
    (M : SmtModel) (_hM : model_total_typed M) (t1 : Term) (n : native_Int)
    (_hTy : __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1)
        (Term.Numeral n))) = SmtType.Real)
    (hZero : native_to_real n = native_mk_rational 0 1) :
  arith_poly_denote_real M
      (__get_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n))) =
    arith_atom_denote_real M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) := by
  have hNorm :
      __get_arith_poly_norm
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) =
        arith_atomic_poly
          (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) (Term.Numeral n)) := by
    simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal, __eo_ite, native_ite,
      __eo_eq, native_teq, __eo_not, SmtEval.native_not, SmtEval.native_and, native_qeq, hZero,
      __eo_mk_apply, arith_atomic_poly]
  exact arith_poly_denote_real_eq_arith_atom_denote_real_of_norm_eq_atomic M _ hNorm

private theorem arith_poly_rational_of_get_arith_poly_norm_qdiv_total_eq_atomic_qdiv
    (M : SmtModel) (hM : model_total_typed M) (t1 t2 : Term)
    (hNorm :
      __get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2) =
        arith_atomic_poly (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2))
    (hTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) t1) t2)) =
        SmtType.Real) :
  arith_poly_rational M
      (__get_arith_poly_norm (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) t1) t2)) := by
  rw [hNorm]
  exact arith_poly_rational_of_arith_atomic_poly M _
    (arith_atom_denote_real_rational_of_smt_arith_type M hM _
      (Or.inr hTy))

private theorem arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type
    (M : SmtModel) (hM : model_total_typed M) :
    (t : Term) ->
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
      __smtx_typeof (__eo_to_smt t) = SmtType.Real) ->
    arith_poly_denote_real M (__get_arith_poly_norm t) = arith_atom_denote_real M t := by
  intro t hTy
  let finishAtomic :
      (t : Term) ->
      (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt t) = SmtType.Real) ->
      (__get_arith_poly_norm t = arith_atomic_poly t) ->
      arith_poly_rational M (__get_arith_poly_norm t) ∧
        arith_poly_wf (__get_arith_poly_norm t) ∧
        arith_poly_denote_real M (__get_arith_poly_norm t) = arith_atom_denote_real M t :=
    fun t hTy hNorm => by
      have hRat : arith_poly_rational M (__get_arith_poly_norm t) :=
        arith_poly_rational_of_get_arith_poly_norm_eq_atomic_of_smt_arith_type M hM t hTy hNorm
      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
      exact arith_poly_denote_real_eq_arith_atom_denote_real_of_norm_eq_atomic M t hNorm
  let rec go (t : Term)
      (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
      arith_poly_rational M (__get_arith_poly_norm t) ∧
        arith_poly_wf (__get_arith_poly_norm t) ∧
        arith_poly_denote_real M (__get_arith_poly_norm t) = arith_atom_denote_real M t := by
    cases hEq : t with
    | Rational q =>
        have hRat : arith_poly_rational M (__get_arith_poly_norm (Term.Rational q)) :=
          arith_poly_rational_of_get_arith_poly_norm_rational M q
        refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
        exact arith_poly_denote_real_of_get_arith_poly_norm_rational M q
    | Numeral n =>
        have hRat : arith_poly_rational M (__get_arith_poly_norm (Term.Numeral n)) :=
          arith_poly_rational_of_get_arith_poly_norm_numeral M n
        refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
        exact arith_poly_denote_real_of_get_arith_poly_norm_numeral M n
    | Stuck =>
        have hTy' :
            __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.Int ∨
              __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.Real := by
          simpa [hEq] using hTy
        exfalso
        rcases hTy' with hInt | hReal
        · rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
            TranslationProofs.smtx_typeof_none] at hInt
          cases hInt
        · rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl,
            TranslationProofs.smtx_typeof_none] at hReal
          cases hReal
    | Apply f x =>
        have hTy :
            __smtx_typeof (__eo_to_smt (Term.Apply f x)) = SmtType.Int ∨
              __smtx_typeof (__eo_to_smt (Term.Apply f x)) = SmtType.Real := by
          simpa [hEq] using hTy
        let tApplyF := Term.Apply f x
        cases f with
        | UOp op =>
            let tUnary := Term.Apply (Term.UOp op) x
            cases op with
            | __eoo_neg_2 =>
                have ht : term_has_non_none_type ((__eo_to_smt x).uneg) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_uneg_eq x]
                  exact non_none_of_smt_arith_type hTy
                have hXTy :
                    __smtx_typeof (__eo_to_smt x) = SmtType.Int ∨
                      __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
                  arith_unop_arg_of_non_none
                    (op := SmtTerm.uneg)
                    (t := __eo_to_smt x)
                    (typeof_uneg_eq (__eo_to_smt x)) ht
                rcases go x hXTy with ⟨hRatX, hWfX, hRecX⟩
                have hRat :
                    arith_poly_rational M
                      (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) :=
                  arith_poly_rational_of_get_arith_poly_norm_uneg M x hRatX
                refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                exact arith_poly_denote_real_of_get_arith_poly_norm_uneg M x hWfX hRecX
            | to_real =>
                have ht : term_has_non_none_type ((__eo_to_smt x).to_real) := by
                  unfold term_has_non_none_type
                  rw [← eo_to_smt_to_real_eq x]
                  exact non_none_of_smt_arith_type hTy
                have hXTy :
                    __smtx_typeof (__eo_to_smt x) = SmtType.Int ∨
                      __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
                  to_real_arg_of_non_none ht
                rcases go x hXTy with ⟨hRatX, _hWfX, hRecX⟩
                have hRat :
                    arith_poly_rational M
                      (__get_arith_poly_norm (Term.Apply (Term.UOp UserOp.to_real) x)) :=
                  arith_poly_rational_of_get_arith_poly_norm_to_real M x hRatX
                refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                exact arith_poly_denote_real_of_get_arith_poly_norm_to_real M x hRecX
            | _ =>
                have hNorm :
                    __get_arith_poly_norm tUnary =
                      arith_atomic_poly tUnary := by
                  simp [tUnary, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                    __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
                    SmtEval.native_and, SmtEval.native_not]
                exact finishAtomic tUnary hTy hNorm
        | Apply g y =>
            let tApplyG := Term.Apply (Term.Apply g y) x
            cases g with
            | UOp op =>
                let tBinary := Term.Apply (Term.Apply (Term.UOp op) y) x
                cases op with
                | plus =>
                    have ht : term_has_non_none_type
                        (SmtTerm.plus (__eo_to_smt y) (__eo_to_smt x)) := by
                      unfold term_has_non_none_type
                      rw [← eo_to_smt_plus_eq y x]
                      exact non_none_of_smt_arith_type hTy
                    rcases arith_binop_args_of_non_none
                        (op := SmtTerm.plus)
                        (typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                    · rcases go y (Or.inl hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inl hArgs.2) with ⟨hRatX, _hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_plus M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_plus
                        M hM y x hTy hRatY hRatX hRecY hRecX
                    · rcases go y (Or.inr hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inr hArgs.2) with ⟨hRatX, _hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_plus M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_plus
                        M hM y x hTy hRatY hRatX hRecY hRecX
                | neg =>
                    have ht : term_has_non_none_type
                        (SmtTerm.neg (__eo_to_smt y) (__eo_to_smt x)) := by
                      unfold term_has_non_none_type
                      rw [← eo_to_smt_neg_eq y x]
                      exact non_none_of_smt_arith_type hTy
                    rcases arith_binop_args_of_non_none
                        (op := SmtTerm.neg)
                        (typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                    · rcases go y (Or.inl hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inl hArgs.2) with ⟨hRatX, hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_neg M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_neg
                        M hM y x hTy hWfX hRatY hRatX hRecY hRecX
                    · rcases go y (Or.inr hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inr hArgs.2) with ⟨hRatX, hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_neg M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_neg
                        M hM y x hTy hWfX hRatY hRatX hRecY hRecX
                | mult =>
                    have ht : term_has_non_none_type
                        (SmtTerm.mult (__eo_to_smt y) (__eo_to_smt x)) := by
                      unfold term_has_non_none_type
                      rw [← eo_to_smt_mult_eq y x]
                      exact non_none_of_smt_arith_type hTy
                    rcases arith_binop_args_of_non_none
                        (op := SmtTerm.mult)
                        (typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x)) ht with hArgs | hArgs
                    · rcases go y (Or.inl hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inl hArgs.2) with ⟨hRatX, _hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_mult M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_mult
                        M hM y x hTy hRatY hRatX hRecY hRecX
                    · rcases go y (Or.inr hArgs.1) with ⟨hRatY, _hWfY, hRecY⟩
                      rcases go x (Or.inr hArgs.2) with ⟨hRatX, _hWfX, hRecX⟩
                      have hRat :
                          arith_poly_rational M
                            (__get_arith_poly_norm
                              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x)) :=
                        arith_poly_rational_of_get_arith_poly_norm_mult M y x hRatY hRatX
                      refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                      exact arith_poly_denote_real_of_get_arith_poly_norm_mult
                        M hM y x hTy hRatY hRatX hRecY hRecX
                | qdiv =>
                    let tQdiv := Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) x
                    have hQdivTy :
                        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) x)) =
                          SmtType.Real :=
                      smt_typeof_qdiv_of_smt_arith_type y x hTy
                    cases x with
                    | Rational q =>
                        by_cases hZero : q = native_mk_rational 0 1
                        · have hNorm :
                              __get_arith_poly_norm
                                (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Rational q)) =
                                arith_atomic_poly
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Rational q)) := by
                            simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal,
                              __eo_ite, native_ite, __eo_eq, native_teq, __eo_not,
                              SmtEval.native_not, SmtEval.native_and, native_qeq, hZero,
                              __eo_mk_apply, arith_atomic_poly]
                          exact finishAtomic
                            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Rational q))
                            hTy hNorm
                        · rcases go y (Or.inr (smt_typeof_qdiv_left_of_rational_right y q hQdivTy)) with
                            ⟨hRatY, _hWfY, hRecY⟩
                          have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Rational q))) :=
                            arith_poly_rational_of_get_arith_poly_norm_qdiv_of_rational M y q hZero hRatY
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_of_rational
                            M hM y q hQdivTy hZero hRatY hRecY
                    | Numeral n =>
                        by_cases hZero : native_to_real n = native_mk_rational 0 1
                        · have hNorm :
                              __get_arith_poly_norm
                                (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Numeral n)) =
                                arith_atomic_poly
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Numeral n)) := by
                            simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal,
                              __eo_ite, native_ite, __eo_eq, native_teq, __eo_not,
                              SmtEval.native_not, SmtEval.native_and, native_qeq, hZero,
                              __eo_mk_apply, arith_atomic_poly]
                          exact finishAtomic
                            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Numeral n))
                            hTy hNorm
                        · rcases go y (Or.inl (smt_typeof_qdiv_left_of_numeral_right y n hQdivTy)) with
                            ⟨hRatY, _hWfY, hRecY⟩
                          have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) (Term.Numeral n))) :=
                            arith_poly_rational_of_get_arith_poly_norm_qdiv_of_numeral M y n hZero hRatY
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_of_numeral
                            M hM y n hQdivTy hZero hRatY hRecY
                    | _ =>
                        have hNorm :
                            __get_arith_poly_norm tQdiv =
                              arith_atomic_poly tQdiv := by
                          simp [tQdiv, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                            __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
                            SmtEval.native_and, SmtEval.native_not]
                        exact finishAtomic tQdiv hTy hNorm
                | qdiv_total =>
                    let tQdivTotal := Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) x
                    have hQdivTotalTy :
                        __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) x)) =
                          SmtType.Real :=
                      smt_typeof_qdiv_total_of_smt_arith_type y x hTy
                    cases x with
                    | Rational q =>
                        by_cases hZero : q = native_mk_rational 0 1
                        · have hNorm :
                              __get_arith_poly_norm
                                (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Rational q)) =
                                arith_atomic_poly
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Rational q)) := by
                            simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal,
                              __eo_ite, native_ite, __eo_eq, native_teq, __eo_not,
                              SmtEval.native_not, SmtEval.native_and, native_qeq, hZero,
                              __eo_mk_apply, arith_atomic_poly]
                          exact finishAtomic
                            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Rational q))
                            hTy hNorm
                        · have hQdivTy :
                              __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y)
                                (Term.Rational q))) = SmtType.Real :=
                            smt_typeof_qdiv_of_qdiv_total y (Term.Rational q) hQdivTotalTy
                          rcases go y (Or.inr (smt_typeof_qdiv_left_of_rational_right y q hQdivTy)) with
                            ⟨hRatY, _hWfY, hRecY⟩
                          have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Rational q))) :=
                            arith_poly_rational_of_get_arith_poly_norm_qdiv_total_of_rational M y q hZero hRatY
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_rational
                            M hM y q hQdivTotalTy hZero hRatY hRecY
                    | Numeral n =>
                        by_cases hZero : native_to_real n = native_mk_rational 0 1
                        · have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Numeral n))) :=
                            arith_poly_rational_of_get_arith_poly_norm_eq_atomic_of_smt_arith_type
                              M hM
                              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Numeral n))
                              hTy
                              (by
                                simp [__get_arith_poly_norm, __eo_to_q, __eo_is_q, __eo_is_q_internal,
                                  __eo_ite, native_ite, __eo_eq, native_teq, __eo_not,
                                  SmtEval.native_not, SmtEval.native_and, native_qeq, hZero,
                                  __eo_mk_apply, arith_atomic_poly])
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_numeral_zero
                            M hM y n hQdivTotalTy hZero
                        · have hQdivTy :
                              __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y)
                                (Term.Numeral n))) = SmtType.Real :=
                            smt_typeof_qdiv_of_qdiv_total y (Term.Numeral n) hQdivTotalTy
                          rcases go y (Or.inl (smt_typeof_qdiv_left_of_numeral_right y n hQdivTy)) with
                            ⟨hRatY, _hWfY, hRecY⟩
                          have hRat :
                              arith_poly_rational M
                                (__get_arith_poly_norm
                                  (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) (Term.Numeral n))) :=
                            arith_poly_rational_of_get_arith_poly_norm_qdiv_total_of_numeral M y n hZero hRatY
                          refine ⟨hRat, arith_poly_wf_of_rational hRat, ?_⟩
                          exact arith_poly_denote_real_of_get_arith_poly_norm_qdiv_total_of_numeral
                            M hM y n hQdivTotalTy hZero hRatY hRecY
                    | _ =>
                        have hNorm :
                            __get_arith_poly_norm tQdivTotal =
                              arith_atomic_poly tQdivTotal := by
                          simp [tQdivTotal, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                            __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
                            SmtEval.native_and, SmtEval.native_not]
                        exact finishAtomic
                          tQdivTotal hTy hNorm
                | _ =>
                    have hNorm :
                        __get_arith_poly_norm tBinary = arith_atomic_poly tBinary := by
                      simp [tBinary, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                        __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
                        SmtEval.native_and, SmtEval.native_not]
                    exact finishAtomic tBinary hTy hNorm
            | _ =>
                have hNorm :
                    __get_arith_poly_norm tApplyG =
                      arith_atomic_poly tApplyG := by
                  simp [tApplyG, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                    __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
                    SmtEval.native_and, SmtEval.native_not]
                exact finishAtomic tApplyG hTy hNorm
        | _ =>
            have hNorm :
                __get_arith_poly_norm tApplyF = arith_atomic_poly tApplyF := by
              simp [tApplyF, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
                __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
                SmtEval.native_and, SmtEval.native_not]
            exact finishAtomic tApplyF hTy hNorm
    | _ =>
        have hTy' :
            __smtx_typeof (__eo_to_smt t) = SmtType.Int ∨
              __smtx_typeof (__eo_to_smt t) = SmtType.Real := by
          simpa [hEq] using hTy
        have hNorm : __get_arith_poly_norm t = arith_atomic_poly t := by
          simp [hEq, __get_arith_poly_norm, arith_atomic_poly, __eo_to_q, __eo_is_q,
            __eo_is_q_internal, __eo_is_eq, __eo_ite, native_ite, native_teq,
            SmtEval.native_and, SmtEval.native_not]
        simpa [hEq] using finishAtomic t hTy' hNorm
  exact (go t hTy).2.2

private theorem native_qlt_false_nonneg {q : native_Rat} :
    native_qlt q (native_mk_rational 0 1) = false ->
  0 ≤ q := by
  intro h
  unfold native_qlt at h
  rw [native_mk_rational_zero] at h
  exact Rat.not_lt.mp (of_decide_eq_false h)

private theorem arith_atom_denote_real_str_len_nonneg_of_rational
    (M : SmtModel) (s : Term) {q : native_Rat} :
  arith_atom_denote_real M (Term.Apply (Term.UOp UserOp.str_len) s) =
      SmtValue.Rational q ->
  0 ≤ q := by
  intro h
  unfold arith_atom_denote_real at h
  change
    __smtx_model_eval_to_real
        (__smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s))) =
      SmtValue.Rational q at h
  simp [__smtx_model_eval] at h
  cases hEval : __smtx_model_eval M (__eo_to_smt s) <;>
    simp [hEval, __smtx_model_eval_str_len, __smtx_model_eval_to_real] at h
  case Seq x =>
    rw [← h]
    dsimp [native_to_real, native_mk_rational, native_seq_len]
    rw [rat_div_one_intCast]
    exact_mod_cast Int.natCast_nonneg (native_unpack_seq x).length

private theorem str_arith_entail_simple_rec_mon_denote_nonneg
    (M : SmtModel) (tail : Term)
    (hTailNonneg :
      ∀ q : native_Rat,
        __str_arith_entail_simple_rec tail = Term.Boolean true ->
        arith_poly_denote_real M tail = SmtValue.Rational q ->
        0 ≤ q) :
    (vars : Term) -> (c qm : native_Rat) ->
      __str_arith_entail_simple_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_poly)
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
              (Term.Rational c))) tail) = Term.Boolean true ->
      arith_mon_denote_real M
          (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon) vars)
            (Term.Rational c)) = SmtValue.Rational qm ->
      0 ≤ qm ∧ __str_arith_entail_simple_rec tail = Term.Boolean true
  | vars, c, qm, hSimple, hDen => by
      cases vars with
      | __eo_List_nil =>
          have hParts :
              native_qlt c (native_mk_rational 0 1) = false ∧
                __str_arith_entail_simple_rec tail = Term.Boolean true := by
            cases hNeg : native_qlt c (native_mk_rational 0 1) <;>
              simp [__str_arith_entail_simple_rec, __eo_is_neg, __eo_ite, native_ite,
                native_teq, hNeg] at hSimple ⊢
            exact hSimple
          simp [arith_mon_denote_real, arith_mvar_denote_real, __smtx_model_eval_mult,
            native_qmult, native_mk_rational_one, Rat.mul_one] at hDen
          subst qm
          exact ⟨native_qlt_false_nonneg hParts.1, hParts.2⟩
      | Apply f rest =>
          cases f with
          | Apply g a =>
              cases g with
              | __eo_List_cons =>
                  cases a with
                  | Apply fArg s =>
                      cases fArg with
                      | UOp op =>
                          cases op <;> simp [__str_arith_entail_simple_rec] at hSimple
                          case str_len =>
                            cases hAtom :
                                arith_atom_denote_real M
                                  (Term.Apply (Term.UOp UserOp.str_len) s) <;>
                              cases hRest : arith_mvar_denote_real M rest <;>
                              simp [arith_mon_denote_real, arith_mvar_denote_real, hAtom,
                                hRest, __smtx_model_eval_mult, native_qmult] at hDen
                            case Rational.Rational qa qr =>
                              have hRestMon :
                                  arith_mon_denote_real M
                                      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_mon)
                                        rest) (Term.Rational c)) =
                                    SmtValue.Rational (native_qmult c qr) := by
                                simp [arith_mon_denote_real, hRest, __smtx_model_eval_mult,
                                  native_qmult]
                              have hRec :=
                                str_arith_entail_simple_rec_mon_denote_nonneg M tail
                                  hTailNonneg rest c (native_qmult c qr) hSimple hRestMon
                              have hAtomNonneg :
                                  0 ≤ qa :=
                                arith_atom_denote_real_str_len_nonneg_of_rational M s hAtom
                              have hProdRaw : 0 ≤ c * (qa * qr) := by
                                have hMul : 0 ≤ qa * (c * qr) :=
                                  Rat.mul_nonneg hAtomNonneg hRec.1
                                rw [show c * (qa * qr) = qa * (c * qr) by
                                  rw [← Rat.mul_assoc, Rat.mul_comm c qa, Rat.mul_assoc]]
                                exact hMul
                              have hProd : 0 ≤ qm := by
                                rw [← hDen]
                                exact hProdRaw
                              exact ⟨hProd, hRec.2⟩
                      | _ =>
                          simp [__str_arith_entail_simple_rec] at hSimple
                  | _ =>
                      simp [__str_arith_entail_simple_rec] at hSimple
              | _ =>
                  simp [__str_arith_entail_simple_rec] at hSimple
          | _ =>
              simp [__str_arith_entail_simple_rec] at hSimple
      | _ =>
          simp [__str_arith_entail_simple_rec] at hSimple
termination_by vars c qm => sizeOf vars

private theorem str_arith_entail_simple_rec_denote_nonneg
    (M : SmtModel) :
    (p : Term) -> (q : native_Rat) ->
      __str_arith_entail_simple_rec p = Term.Boolean true ->
      arith_poly_denote_real M p = SmtValue.Rational q ->
      0 ≤ q
  | p, q, hSimple, hDen => by
      cases p with
      | UOp op =>
          cases op with
          | _at__at_Polynomial =>
              simp [arith_poly_denote_real] at hDen
              subst q
              simp [native_mk_rational_zero]
          | _ =>
              simp [__str_arith_entail_simple_rec] at hSimple
      | Apply f tail =>
          cases f with
          | Apply g mon =>
              cases g with
              | UOp op =>
                  cases op with
                  | _at__at_poly =>
                      cases mon with
                      | Apply monF coeff =>
                          cases monF with
                          | Apply monHead vars =>
                              cases monHead with
                              | UOp monOp =>
                                  cases monOp with
                                  | _at__at_mon =>
                                      cases coeff with
                                      | Rational c =>
                                          cases hMon :
                                              arith_mon_denote_real M
                                                (Term.Apply
                                                  (Term.Apply
                                                    (Term.UOp UserOp._at__at_mon) vars)
                                                  (Term.Rational c)) <;>
                                            cases hTail : arith_poly_denote_real M tail <;>
                                            simp [arith_poly_denote_real, hMon, hTail,
                                              __smtx_model_eval_plus, native_qplus] at hDen
                                          case Rational.Rational qm qp =>
                                            have hMonTail :=
                                              str_arith_entail_simple_rec_mon_denote_nonneg
                                                M tail
                                                (str_arith_entail_simple_rec_denote_nonneg
                                                  M tail)
                                                vars c qm hSimple hMon
                                            have hTailNonneg :=
                                              str_arith_entail_simple_rec_denote_nonneg M
                                                tail qp hMonTail.2 hTail
                                            exact by
                                              rw [← hDen]
                                              exact Rat.add_nonneg hMonTail.1 hTailNonneg
                                      | _ =>
                                          simp [arith_poly_denote_real, arith_mon_denote_real,
                                            __smtx_model_eval_plus] at hDen
                                  | _ =>
                                      simp [arith_poly_denote_real, arith_mon_denote_real,
                                        __smtx_model_eval_plus] at hDen
                              | _ =>
                                  simp [arith_poly_denote_real, arith_mon_denote_real,
                                    __smtx_model_eval_plus] at hDen
                          | _ =>
                              simp [arith_poly_denote_real, arith_mon_denote_real,
                                __smtx_model_eval_plus] at hDen
                      | _ =>
                          simp [arith_poly_denote_real, arith_mon_denote_real,
                            __smtx_model_eval_plus] at hDen
                  | _ =>
                      simp [__str_arith_entail_simple_rec] at hSimple
              | _ =>
                  simp [__str_arith_entail_simple_rec] at hSimple
          | _ =>
              simp [__str_arith_entail_simple_rec] at hSimple
      | _ =>
          simp [__str_arith_entail_simple_rec] at hSimple
termination_by p q => sizeOf p

private theorem geq_left_int_type_of_has_bool_type
    (n : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) ->
  __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt (Term.Numeral 0))) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hTy
  have hNN : term_has_non_none_type
      (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt (Term.Numeral 0))) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt n) (__eo_to_smt (Term.Numeral 0))) hNN with
    hInt | hReal
  · exact hInt.1
  · have hZeroInt :
        __smtx_typeof (__eo_to_smt (Term.Numeral 0)) = SmtType.Int := by
      rw [show __eo_to_smt (Term.Numeral 0) = SmtTerm.Numeral 0 by rfl]
      rw [__smtx_typeof.eq_2]
    rw [hZeroInt] at hReal
    cases hReal.2

private theorem geq_zero_eval_true_of_int_denote_nonneg
    (M : SmtModel) (hM : model_total_typed M)
    (n : Term) (q : native_Rat) :
  __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
  arith_atom_denote_real M n = SmtValue.Rational q ->
  0 ≤ q ->
  __smtx_model_eval M
      (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))) =
    SmtValue.Boolean true := by
  intro hTy hDen hq
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
        __smtx_typeof (__eo_to_smt n) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
      (by simp [term_has_non_none_type, hTy])
  rcases int_value_canonical (by simpa [hTy] using hEvalTy) with ⟨z, hEval⟩
  have hDenEq : native_to_real z = q := by
    have h :
        SmtValue.Rational (native_to_real z) = SmtValue.Rational q := by
      simpa [arith_atom_denote_real, hEval, __smtx_model_eval_to_real] using hDen
    simpa using h
  have hzNonneg : (0 : Int) ≤ z := by
    have hq' : (0 : Rat) ≤ native_to_real z := by
      simpa [hDenEq] using hq
    dsimp [native_to_real, native_mk_rational] at hq'
    rw [rat_div_one_intCast z] at hq'
    exact_mod_cast hq'
  rw [show
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) =
        SmtTerm.geq (__eo_to_smt n) (SmtTerm.Numeral 0) by rfl]
  rw [__smtx_model_eval.eq_18, hEval]
  have hZle : native_zleq 0 z = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hzNonneg
  have hZeroEval :
      __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 := by
    rw [__smtx_model_eval.eq_2]
  rw [hZeroEval]
  simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hZle]

private theorem geq_eval_true_of_diff_denote_nonneg
    (M : SmtModel) (hM : model_total_typed M)
    (n m : Term) (q : native_Rat) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) ->
  arith_atom_denote_real M (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m) =
      SmtValue.Rational q ->
  0 ≤ q ->
  __smtx_model_eval M
      (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m)) =
    SmtValue.Boolean true := by
  intro hGeqBool hDiffDen hq
  have hGeqTy :
      __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hGeqBool
  have hGeqNN : term_has_non_none_type
      (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    rw [hGeqTy]
    simp
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt n) (__eo_to_smt m)) hGeqNN with
    hInt | hReal
  · have hEvalNTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
          __smtx_typeof (__eo_to_smt n) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
        (by simp [term_has_non_none_type, hInt.1])
    have hEvalMTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m)) =
          __smtx_typeof (__eo_to_smt m) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m)
        (by simp [term_has_non_none_type, hInt.2])
    rcases int_value_canonical (by simpa [hInt.1] using hEvalNTy) with ⟨zn, hEvalN⟩
    rcases int_value_canonical (by simpa [hInt.2] using hEvalMTy) with ⟨zm, hEvalM⟩
    have hDiffQ :
        native_to_real (native_zplus zn (native_zneg zm)) = q := by
      have h :
          SmtValue.Rational (native_to_real (native_zplus zn (native_zneg zm))) =
            SmtValue.Rational q := by
        have hDen := hDiffDen
        change
          __smtx_model_eval_to_real
              (__smtx_model_eval M (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m))) =
            SmtValue.Rational q at hDen
        rw [__smtx_model_eval.eq_13, hEvalN, hEvalM] at hDen
        simpa [__smtx_model_eval_to_real, __smtx_model_eval__, native_to_real_sub] using hDen
      simpa using h
    have hSubNonneg : (0 : Int) ≤ native_zplus zn (native_zneg zm) := by
      have hRat : (0 : Rat) ≤ native_to_real (native_zplus zn (native_zneg zm)) := by
        simpa [hDiffQ] using hq
      dsimp [native_to_real, native_mk_rational] at hRat
      rw [rat_div_one_intCast] at hRat
      exact_mod_cast hRat
    have hLe : zm ≤ zn := by
      have hSubNonneg' : (0 : Int) ≤ zn - zm := by
        change (0 : Int) ≤ zn + -zm
        simpa [native_zplus, native_zneg] using hSubNonneg
      exact Int.sub_nonneg.mp hSubNonneg'
    have hZle : native_zleq zm zn = true := by
      simpa [native_zleq, SmtEval.native_zleq] using hLe
    rw [show
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) =
          SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m) by rfl]
    rw [__smtx_model_eval.eq_18, hEvalN, hEvalM]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hZle]
  · have hEvalNTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt n)) =
          __smtx_typeof (__eo_to_smt n) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt n)
        (by simp [term_has_non_none_type, hReal.1])
    have hEvalMTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m)) =
          __smtx_typeof (__eo_to_smt m) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m)
        (by simp [term_has_non_none_type, hReal.2])
    rcases real_value_canonical (by simpa [hReal.1] using hEvalNTy) with ⟨qn, hEvalN⟩
    rcases real_value_canonical (by simpa [hReal.2] using hEvalMTy) with ⟨qm, hEvalM⟩
    have hDiffQ :
        native_qplus qn (native_qneg qm) = q := by
      have h :
          SmtValue.Rational (native_qplus qn (native_qneg qm)) =
            SmtValue.Rational q := by
        have hDen := hDiffDen
        change
          __smtx_model_eval_to_real
              (__smtx_model_eval M (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m))) =
            SmtValue.Rational q at hDen
        rw [__smtx_model_eval.eq_13, hEvalN, hEvalM] at hDen
        simpa [__smtx_model_eval_to_real, __smtx_model_eval__] using hDen
      simpa using h
    have hLe : qm ≤ qn := by
      have hSub : (0 : Rat) ≤ native_qplus qn (native_qneg qm) := by
        simpa [hDiffQ] using hq
      have hSub' : (0 : Rat) ≤ qn + -qm := by
        simpa [native_qplus, native_qneg] using hSub
      grind
    have hQle : native_qleq qm qn = true := by
      simpa [native_qleq] using hLe
    rw [show
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) =
          SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m) by rfl]
    rw [__smtx_model_eval.eq_18, hEvalN, hEvalM]
    simp [__smtx_model_eval_geq, __smtx_model_eval_leq, hQle]

theorem arith_string_pred_simple_geq_true
    (M : SmtModel) (hM : model_total_typed M) (n m : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) ->
  __str_arith_entail_simple_pred
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) = Term.Boolean true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) true := by
  intro hGeqBool hSimple
  let diff := Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m
  have hGeqTy :
      __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) =
        SmtType.Bool := by
    simpa [RuleProofs.eo_has_bool_type] using hGeqBool
  have hGeqNN : term_has_non_none_type
      (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    rw [hGeqTy]
    simp
  have hDiffTy :
      __smtx_typeof (__eo_to_smt diff) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt diff) = SmtType.Real := by
    rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
        (typeof_geq_eq (__eo_to_smt n) (__eo_to_smt m)) hGeqNN with
      hInt | hReal
    · left
      rw [show __eo_to_smt diff = SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m) by rfl]
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hInt.1, hInt.2]
    · right
      rw [show __eo_to_smt diff = SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m) by rfl]
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hReal.1, hReal.2]
  have hDenote :
      arith_poly_denote_real M (__get_arith_poly_norm diff) =
        arith_atom_denote_real M diff :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type
      M hM diff hDiffTy
  rcases arith_atom_denote_real_rational_of_smt_arith_type
      M hM diff hDiffTy with
    ⟨q, hAtomDenote⟩
  have hPolyDenote :
      arith_poly_denote_real M (__get_arith_poly_norm diff) =
        SmtValue.Rational q := by
    rw [hDenote, hAtomDenote]
  have hSimpleRec :
      __str_arith_entail_simple_rec (__get_arith_poly_norm diff) =
        Term.Boolean true := by
    simpa [diff, __str_arith_entail_simple_pred] using hSimple
  have hqNonneg : 0 ≤ q :=
    str_arith_entail_simple_rec_denote_nonneg
      M (__get_arith_poly_norm diff) q hSimpleRec hPolyDenote
  have hGeqEval :
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m)) =
        SmtValue.Boolean true :=
    geq_eval_true_of_diff_denote_nonneg M hM n m q hGeqBool hAtomDenote hqNonneg
  exact RuleProofs.eo_interprets_of_bool_eval M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) true hGeqBool hGeqEval

private theorem geq_has_bool_type_of_non_none (n m : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m)) ≠
      SmtType.None ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) := by
  intro hNN
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) = SmtType.Bool
  have hTerm : term_has_non_none_type (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    simpa using hNN
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
      (typeof_geq_eq (__eo_to_smt n) (__eo_to_smt m)) hTerm with
    hInt | hReal
  · rw [typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · rw [typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem int_eval_of_int_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  __smtx_typeof (__eo_to_smt t) = SmtType.Int ->
  ∃ z : native_Int, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral z := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact int_value_canonical (by simpa [hTy] using hEvalTy)

private theorem arith_atom_denote_real_eq_of_int_eval
    (M : SmtModel) (t : Term) (z : native_Int) :
  __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral z ->
  arith_atom_denote_real M t = SmtValue.Rational (native_to_real z) := by
  intro hEval
  simp [arith_atom_denote_real, hEval, __smtx_model_eval_to_real]

private theorem native_to_real_le_iff (a b : native_Int) :
    native_to_real a ≤ native_to_real b ↔ a ≤ b := by
  dsimp [native_to_real, native_mk_rational]
  rw [rat_div_one_intCast a, rat_div_one_intCast b]
  exact_mod_cast Iff.rfl

private theorem native_seq_indexof_rec_ge_neg_one
    (xs pat : List SmtValue) (i fuel : Nat) :
    (-1 : Int) ≤ native_seq_indexof_rec xs pat i fuel := by
  induction fuel generalizing xs i with
  | zero =>
      simp [native_seq_indexof_rec]
  | succ fuel ih =>
      unfold native_seq_indexof_rec
      split
      · exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.natCast_nonneg i)
      · cases xs with
        | nil => simp
        | cons _ xs => exact ih xs (i + 1)

private theorem native_seq_indexof_ge_neg_one
    (xs pat : List SmtValue) (i : native_Int) :
    (-1 : Int) ≤ native_seq_indexof xs pat i := by
  unfold native_seq_indexof
  split
  · simp
  · dsimp
    split
    · exact native_seq_indexof_rec_ge_neg_one _ _ _ _
    · simp

private theorem native_str_to_int_ge_neg_one
    (s : native_String) :
    (-1 : Int) ≤ native_str_to_int s := by
  unfold native_str_to_int
  cases hList : s.toList with
  | nil =>
      simp [hList]
  | cons c cs =>
      by_cases hMinus : c = '-'
      · subst c
        simp [hList]
      · by_cases hZero : c = '0'
        · subst c
          cases cs with
          | nil =>
              cases hNat : s.toNat? <;> simp [hList, hNat]
          | cons _ _ =>
              simp [hList]
        · cases hNat : s.toNat? with
          | none =>
              simp [hList, hMinus, hZero, hNat]
          | some _ =>
              simp [hList, hMinus, hZero, hNat]

private theorem int_le_of_simple_geq_true
    (M : SmtModel) (hM : model_total_typed M)
    (n m : Term) (zn zm : native_Int) :
  __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
  __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
  __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
  __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
  __str_arith_entail_simple_pred
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m) =
    Term.Boolean true ->
  zm ≤ zn := by
  intro hNInt hMInt hNEval hMEval hSimple
  let geqTerm := Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) m
  have hGeqBool : RuleProofs.eo_has_bool_type geqTerm := by
    unfold RuleProofs.eo_has_bool_type
    change __smtx_typeof (SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m)) =
      SmtType.Bool
    rw [typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hNInt, hMInt]
  have hTrue : eo_interprets M geqTerm true := by
    simpa [geqTerm] using
      arith_string_pred_simple_geq_true M hM n m hGeqBool hSimple
  have hEval :
      __smtx_model_eval M (__eo_to_smt geqTerm) = SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M geqTerm true).mp hTrue with
    | intro_true _ hEval => exact hEval
  rw [show __eo_to_smt geqTerm =
        SmtTerm.geq (__eo_to_smt n) (__eo_to_smt m) by rfl] at hEval
  rw [__smtx_model_eval.eq_18, hNEval, hMEval] at hEval
  simpa [__smtx_model_eval_geq, __smtx_model_eval_leq, native_zleq,
    SmtEval.native_zleq] using hEval

private theorem native_seq_indexof_rec_bound
    (xs pat : List SmtValue) :
    (i fuel : Nat) ->
    native_seq_indexof_rec xs pat i fuel = -1 ∨
      ∃ j : Nat, native_seq_indexof_rec xs pat i fuel = Int.ofNat (i + j) ∧
        j < fuel
  | i, 0 => by
      simp [native_seq_indexof_rec]
  | i, fuel + 1 => by
      unfold native_seq_indexof_rec
      split
      · right
        exact ⟨0, by simp, by omega⟩
      · cases xs with
        | nil =>
            simp
        | cons _ xs =>
            cases native_seq_indexof_rec_bound xs pat (i + 1) fuel with
            | inl h =>
                left
                exact h
            | inr h =>
                rcases h with ⟨j, hj, hjlt⟩
                right
                refine ⟨j + 1, ?_, by omega⟩
                simpa [hj, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem native_seq_indexof_le_len
    (xs pat : List SmtValue) (i : native_Int) :
    native_seq_indexof xs pat i ≤ Int.ofNat xs.length := by
  unfold native_seq_indexof
  split
  · exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.ofNat_nonneg _)
  · dsimp
    split
    · rename_i hStart h
      cases native_seq_indexof_rec_bound (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl hRec =>
          rw [hRec]
          exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.ofNat_nonneg _)
      | inr hRec =>
          rcases hRec with ⟨j, hRec, hjlt⟩
          rw [hRec]
          apply Int.ofNat_le.mpr
          have hjle : j ≤ xs.length - (Int.toNat i + pat.length) := by
            omega
          omega
    · exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.ofNat_nonneg _)

private theorem native_seq_indexof_le_len_sub_pat_of_pat_le_len
    (xs pat : List SmtValue) (i : native_Int) :
    pat.length ≤ xs.length ->
    native_seq_indexof xs pat i ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
  intro hPatLe
  unfold native_seq_indexof
  split
  · have hNonneg :
        (0 : Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
      exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
    exact Int.le_trans (by decide : (-1 : Int) ≤ 0) hNonneg
  · dsimp
    split
    · rename_i hStart h
      cases native_seq_indexof_rec_bound (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl hRec =>
          rw [hRec]
          have hNonneg :
              (0 : Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
            exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
          exact Int.le_trans (by decide : (-1 : Int) ≤ 0) hNonneg
      | inr hRec =>
          rcases hRec with ⟨j, hRec, hjlt⟩
          rw [hRec]
          have hjle : j ≤ xs.length - (Int.toNat i + pat.length) := by
            omega
          have hNat :
              Int.toNat i + j ≤ xs.length - pat.length := by
            omega
          calc
            Int.ofNat (Int.toNat i + j) ≤ Int.ofNat (xs.length - pat.length) :=
              Int.ofNat_le.mpr hNat
            _ = Int.ofNat xs.length - Int.ofNat pat.length :=
              Int.ofNat_sub hPatLe
    · have hNonneg :
          (0 : Int) ≤ Int.ofNat xs.length - Int.ofNat pat.length := by
        exact Int.sub_nonneg.mpr (Int.ofNat_le.mpr hPatLe)
      exact Int.le_trans (by decide : (-1 : Int) ≤ 0) hNonneg

private theorem int_eval_eq_of_term_eq
    (M : SmtModel) {n m : Term} {zn zm : native_Int} :
    n = m ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    zn = zm := by
  intro hEq hNEval hMEval
  subst m
  have h : SmtValue.Numeral zn = SmtValue.Numeral zm := by
    rw [← hNEval, ← hMEval]
  simpa using h

private theorem plus_int_args_of_int_type (n m : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m)) =
      SmtType.Int ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m)) =
        SmtType.Int := by
    simpa using hTy
  have hNN :
      term_has_non_none_type (SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
      (typeof_plus_eq (__eo_to_smt n) (__eo_to_smt m)) hNN with hInt | hReal
  · exact hInt
  · have hRet :
        __smtx_typeof
            (SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m)) =
          SmtType.Real := by
      rw [typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hReal.1, hReal.2]
    rw [show
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m) =
          SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m) by rfl] at hTy
    rw [hTy] at hRet
    cases hRet

private theorem mult_int_args_of_int_type (n m : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m)) =
      SmtType.Int ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m)) =
        SmtType.Int := by
    simpa using hTy
  have hNN :
      term_has_non_none_type (SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
      (typeof_mult_eq (__eo_to_smt n) (__eo_to_smt m)) hNN with hInt | hReal
  · exact hInt
  · have hRet :
        __smtx_typeof
            (SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m)) =
          SmtType.Real := by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hReal.1, hReal.2]
    rw [show
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m) =
          SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m) by rfl] at hTy
    rw [hTy] at hRet
    cases hRet

private theorem neg_int_args_of_int_type (n m : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m)) =
      SmtType.Int ->
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m)) =
        SmtType.Int := by
    simpa using hTy
  have hNN :
      term_has_non_none_type (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq (__eo_to_smt n) (__eo_to_smt m)) hNN with hInt | hReal
  · exact hInt
  · have hRet :
        __smtx_typeof
            (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m)) =
          SmtType.Real := by
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hReal.1, hReal.2]
    rw [show
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m) =
          SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m) by rfl] at hTy
    rw [hTy] at hRet
    cases hRet

private theorem plus_int_eval_decomp
    (M : SmtModel) (hM : model_total_typed M)
    (n m : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m)) =
      SmtValue.Numeral z ->
    ∃ zn zm,
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ∧
      __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ∧
      z = zn + zm := by
  intro hTy hEval
  rcases plus_int_args_of_int_type n m hTy with ⟨hNInt, hMInt⟩
  rcases int_eval_of_int_type M hM n hNInt with ⟨zn, hNEval⟩
  rcases int_eval_of_int_type M hM m hMInt with ⟨zm, hMEval⟩
  refine ⟨zn, zm, hNInt, hMInt, hNEval, hMEval, ?_⟩
  rw [show
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n) m) =
        SmtTerm.plus (__eo_to_smt n) (__eo_to_smt m) by rfl] at hEval
  rw [__smtx_model_eval.eq_12, hNEval, hMEval] at hEval
  simpa [__smtx_model_eval_plus, native_zplus] using hEval.symm

private theorem mult_int_eval_decomp
    (M : SmtModel) (hM : model_total_typed M)
    (n m : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m)) =
      SmtValue.Numeral z ->
    ∃ zn zm,
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ∧
      __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ∧
      z = zn * zm := by
  intro hTy hEval
  rcases mult_int_args_of_int_type n m hTy with ⟨hNInt, hMInt⟩
  rcases int_eval_of_int_type M hM n hNInt with ⟨zn, hNEval⟩
  rcases int_eval_of_int_type M hM m hMInt with ⟨zm, hMEval⟩
  refine ⟨zn, zm, hNInt, hMInt, hNEval, hMEval, ?_⟩
  rw [show
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n) m) =
        SmtTerm.mult (__eo_to_smt n) (__eo_to_smt m) by rfl] at hEval
  rw [__smtx_model_eval.eq_14, hNEval, hMEval] at hEval
  simpa [__smtx_model_eval_mult, native_zmult] using hEval.symm

private theorem neg_int_eval_decomp
    (M : SmtModel) (hM : model_total_typed M)
    (n m : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m)) =
      SmtValue.Numeral z ->
    ∃ zn zm,
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ∧
      __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ∧
      z = zn - zm := by
  intro hTy hEval
  rcases neg_int_args_of_int_type n m hTy with ⟨hNInt, hMInt⟩
  rcases int_eval_of_int_type M hM n hNInt with ⟨zn, hNEval⟩
  rcases int_eval_of_int_type M hM m hMInt with ⟨zm, hMEval⟩
  refine ⟨zn, zm, hNInt, hMInt, hNEval, hMEval, ?_⟩
  rw [show
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m) =
        SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m) by rfl] at hEval
  rw [__smtx_model_eval.eq_13, hNEval, hMEval] at hEval
  simpa [__smtx_model_eval__, native_zplus, native_zneg, Int.sub_eq_add_neg] using
    hEval.symm

private theorem seq_eval_of_seq_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    ∃ ss, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact seq_value_canonical (by simpa [hTy] using hEvalTy)

private theorem str_len_eval_decomp
    (M : SmtModel) (hM : model_total_typed M)
    (s : Term) (z : native_Int) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral z ->
    ∃ T ss,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      z = Int.ofNat (native_unpack_seq ss).length := by
  intro hTy hEval
  have hTy' :
      __smtx_typeof (SmtTerm.str_len (__eo_to_smt s)) = SmtType.Int := by
    simpa using hTy
  have hNN : term_has_non_none_type (SmtTerm.str_len (__eo_to_smt s)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq (__eo_to_smt s)) hNN with ⟨T, hSTy⟩
  rcases seq_eval_of_seq_type M hM s T hSTy with ⟨ss, hSEval⟩
  refine ⟨T, ss, hSTy, hSEval, ?_⟩
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s) =
        SmtTerm.str_len (__eo_to_smt s) by rfl] at hEval
  rw [__smtx_model_eval.eq_79, hSEval] at hEval
  simpa [__smtx_model_eval_str_len, native_seq_len] using hEval.symm

private theorem native_unpack_pack_seq
    (T : SmtType) (xs : List SmtValue) :
    native_unpack_seq (native_pack_seq T xs) = xs := by
  induction xs with
  | nil =>
      simp [native_pack_seq, native_unpack_seq]
  | cons x xs ih =>
      simp [native_pack_seq, native_unpack_seq, ih]

private theorem native_unpack_pack_string_len
    (s : native_String) :
    (native_unpack_seq (native_pack_string s)).length = s.length := by
  simp [native_pack_string, native_ssm_char_values_of_string,
    native_unpack_pack_seq, String.length_toList]

private theorem str_to_int_eval_decomp
    (M : SmtModel) (hM : model_total_typed M)
    (s : Term) (z : native_Int) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s)) =
      SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s)) =
      SmtValue.Numeral z ->
    ∃ ss,
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      z = native_str_to_int (native_unpack_string ss) := by
  intro hTy hEval
  have hTy' :
      __smtx_typeof (SmtTerm.str_to_int (__eo_to_smt s)) = SmtType.Int := by
    simpa using hTy
  have hNN : term_has_non_none_type (SmtTerm.str_to_int (__eo_to_smt s)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  have hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq (__eo_to_smt s)) hNN
  rcases seq_eval_of_seq_type M hM s SmtType.Char hSTy with ⟨ss, hSEval⟩
  refine ⟨ss, hSEval, ?_⟩
  rw [show __eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s) =
        SmtTerm.str_to_int (__eo_to_smt s) by rfl] at hEval
  rw [__smtx_model_eval.eq_95, hSEval] at hEval
  simpa [__smtx_model_eval_str_to_int] using hEval.symm

private theorem str_indexof_eval_decomp
    (M : SmtModel) (hM : model_total_typed M)
    (s t n : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n)) =
      SmtValue.Numeral z ->
    ∃ T ss tt zn,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq tt ∧
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ∧
      z = native_seq_indexof (native_unpack_seq ss) (native_unpack_seq tt) zn := by
  intro hTy hEval
  have hTy' :
      __smtx_typeof
          (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt n)) =
        SmtType.Int := by
    simpa using hTy
  have hNN :
      term_has_non_none_type
          (SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt n)) := by
    unfold term_has_non_none_type
    rw [hTy']
    simp
  rcases str_indexof_args_of_non_none hNN with ⟨T, hSTy, hTTy, hNTy⟩
  rcases seq_eval_of_seq_type M hM s T hSTy with ⟨ss, hSEval⟩
  rcases seq_eval_of_seq_type M hM t T hTTy with ⟨tt, hTEval⟩
  rcases int_eval_of_int_type M hM n hNTy with ⟨zn, hNEval⟩
  refine ⟨T, ss, tt, zn, hSTy, hTTy, hNTy, hSEval, hTEval, hNEval, ?_⟩
  rw [show
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n) =
        SmtTerm.str_indexof (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt n) by rfl] at hEval
  rw [__smtx_model_eval.eq_84, hSEval, hTEval, hNEval] at hEval
  simpa [__smtx_model_eval_str_indexof] using hEval.symm

private theorem str_substr_len_eval_decomp
    (M : SmtModel) (hM : model_total_typed M)
    (s n1 n2 : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))) =
      SmtValue.Numeral z ->
    ∃ T ss z1 z2,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt n1) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt n2) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt n1) = SmtValue.Numeral z1 ∧
      __smtx_model_eval M (__eo_to_smt n2) = SmtValue.Numeral z2 ∧
      z = Int.ofNat (native_seq_extract (native_unpack_seq ss) z1 z2).length := by
  intro hTy hEval
  let sub :=
    Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2
  rcases str_len_eval_decomp M hM sub z (by simpa [sub] using hTy)
      (by simpa [sub] using hEval) with ⟨T, subSeq, hSubTy, hSubEval, hzLen⟩
  have hSubTy' :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n1) (__eo_to_smt n2)) =
        SmtType.Seq T := by
    simpa [sub] using hSubTy
  have hSubNN :
      term_has_non_none_type
          (SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n1) (__eo_to_smt n2)) := by
    unfold term_has_non_none_type
    rw [hSubTy']
    simp
  rcases str_substr_args_of_non_none hSubNN with ⟨T', hSTy, hN1Ty, hN2Ty⟩
  rcases seq_eval_of_seq_type M hM s T' hSTy with ⟨ss, hSEval⟩
  rcases int_eval_of_int_type M hM n1 hN1Ty with ⟨z1, hN1Eval⟩
  rcases int_eval_of_int_type M hM n2 hN2Ty with ⟨z2, hN2Eval⟩
  have hSubEval' :
      native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_extract (native_unpack_seq ss) z1 z2) =
        subSeq := by
    rw [show __eo_to_smt sub =
          SmtTerm.str_substr (__eo_to_smt s) (__eo_to_smt n1) (__eo_to_smt n2) by rfl]
        at hSubEval
    rw [__smtx_model_eval.eq_81, hSEval, hN1Eval, hN2Eval] at hSubEval
    simpa [__smtx_model_eval_str_substr] using hSubEval
  have hLenEq :
      (native_unpack_seq subSeq).length =
        (native_seq_extract (native_unpack_seq ss) z1 z2).length := by
    rw [← hSubEval']
    simp [native_unpack_pack_seq]
  refine ⟨T', ss, z1, z2, hSTy, hN1Ty, hN2Ty, hSEval, hN1Eval, hN2Eval, ?_⟩
  rw [hzLen, hLenEq]

private theorem str_replace_len_eval_decomp
    (M : SmtModel) (hM : model_total_typed M)
    (s t r : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtValue.Numeral z ->
    ∃ T ss tt rr,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.Seq T ∧
      __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq tt ∧
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.Seq rr ∧
      z = Int.ofNat
        (native_seq_replace (native_unpack_seq ss) (native_unpack_seq tt)
          (native_unpack_seq rr)).length := by
  intro hTy hEval
  let rep :=
    Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r
  rcases str_len_eval_decomp M hM rep z (by simpa [rep] using hTy)
      (by simpa [rep] using hEval) with ⟨T, repSeq, hRepTy, hRepEval, hzLen⟩
  have hRepTy' :
      __smtx_typeof
          (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt r)) =
        SmtType.Seq T := by
    simpa [rep] using hRepTy
  have hRepNN :
      term_has_non_none_type
          (SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt r)) := by
    unfold term_has_non_none_type
    rw [hRepTy']
    simp
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace)
      (typeof_str_replace_eq (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt r))
      hRepNN with ⟨T', hSTy, hTTy, hRTy⟩
  rcases seq_eval_of_seq_type M hM s T' hSTy with ⟨ss, hSEval⟩
  rcases seq_eval_of_seq_type M hM t T' hTTy with ⟨tt, hTEval⟩
  rcases seq_eval_of_seq_type M hM r T' hRTy with ⟨rr, hREval⟩
  have hRepEval' :
      native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_replace (native_unpack_seq ss) (native_unpack_seq tt)
            (native_unpack_seq rr)) =
        repSeq := by
    rw [show __eo_to_smt rep =
          SmtTerm.str_replace (__eo_to_smt s) (__eo_to_smt t) (__eo_to_smt r) by rfl]
        at hRepEval
    rw [__smtx_model_eval.eq_83, hSEval, hTEval, hREval] at hRepEval
    simpa [__smtx_model_eval_str_replace] using hRepEval
  have hLenEq :
      (native_unpack_seq repSeq).length =
        (native_seq_replace (native_unpack_seq ss) (native_unpack_seq tt)
          (native_unpack_seq rr)).length := by
    rw [← hRepEval']
    simp [native_unpack_pack_seq]
  refine ⟨T', ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, ?_⟩
  rw [hzLen, hLenEq]

private theorem str_from_int_len_eval_decomp
    (M : SmtModel) (hM : model_total_typed M)
    (n : Term) (z : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n))) =
      SmtValue.Numeral z ->
    ∃ zn,
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ∧
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ∧
      z = Int.ofNat (native_str_from_int zn).length := by
  intro hTy hEval
  let fromInt := Term.Apply (Term.UOp UserOp.str_from_int) n
  rcases str_len_eval_decomp M hM fromInt z (by simpa [fromInt] using hTy)
      (by simpa [fromInt] using hEval) with ⟨T, seq, hFromTy, hFromEval, hzLen⟩
  have hFromTy' :
      __smtx_typeof (SmtTerm.str_from_int (__eo_to_smt n)) = SmtType.Seq T := by
    simpa [fromInt] using hFromTy
  have hFromNN : term_has_non_none_type (SmtTerm.str_from_int (__eo_to_smt n)) := by
    unfold term_has_non_none_type
    rw [hFromTy']
    simp
  have hNInt : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
      (typeof_str_from_int_eq (__eo_to_smt n)) hFromNN
  rcases int_eval_of_int_type M hM n hNInt with ⟨zn, hNEval⟩
  have hFromEval' :
      native_pack_string (native_str_from_int zn) = seq := by
    rw [show __eo_to_smt fromInt = SmtTerm.str_from_int (__eo_to_smt n) by rfl]
        at hFromEval
    rw [__smtx_model_eval.eq_96, hNEval] at hFromEval
    simpa [__smtx_model_eval_str_from_int] using hFromEval
  have hLenEq :
      (native_unpack_seq seq).length = (native_str_from_int zn).length := by
    rw [← hFromEval']
    exact native_unpack_pack_string_len (native_str_from_int zn)
  refine ⟨zn, hNInt, hNEval, ?_⟩
  rw [hzLen, hLenEq]

private theorem int_nonneg_of_simple_rec_true
    (M : SmtModel) (hM : model_total_typed M) (n : Term) (zn : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __str_arith_entail_simple_rec (__get_arith_poly_norm n) = Term.Boolean true ->
    0 ≤ zn := by
  intro hTy hEval hSimple
  have hDenote :
      arith_poly_denote_real M (__get_arith_poly_norm n) =
        arith_atom_denote_real M n :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type
      M hM n (Or.inl hTy)
  have hAtomDenote :
      arith_atom_denote_real M n = SmtValue.Rational (native_to_real zn) :=
    arith_atom_denote_real_eq_of_int_eval M n zn hEval
  have hPolyDenote :
      arith_poly_denote_real M (__get_arith_poly_norm n) =
        SmtValue.Rational (native_to_real zn) := by
    rw [hDenote, hAtomDenote]
  have hNonnegRat : (0 : Rat) ≤ native_to_real zn :=
    str_arith_entail_simple_rec_denote_nonneg
      M (__get_arith_poly_norm n) (native_to_real zn) hSimple hPolyDenote
  dsimp [native_to_real, native_mk_rational] at hNonnegRat
  rw [rat_div_one_intCast zn] at hNonnegRat
  exact_mod_cast hNonnegRat

private theorem int_pos_of_simple_gt_zero_true
    (M : SmtModel) (hM : model_total_typed M) (n : Term) (zn : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __str_arith_entail_simple_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) n) (Term.Numeral 0)) =
      Term.Boolean true ->
    0 < zn := by
  intro hNInt hNEval hSimple
  let oneTerm :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 0))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0))
  have hOneInt : __smtx_typeof (__eo_to_smt oneTerm) = SmtType.Int := by
    change
      __smtx_typeof
        (SmtTerm.plus (SmtTerm.Numeral 0)
          (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))) = SmtType.Int
    rw [typeof_plus_eq, typeof_plus_eq]
    simp [__smtx_typeof.eq_2, __smtx_typeof_arith_overload_op_2]
  have hOneEval :
      __smtx_model_eval M (__eo_to_smt oneTerm) = SmtValue.Numeral 1 := by
    change
      __smtx_model_eval M
          (SmtTerm.plus (SmtTerm.Numeral 0)
            (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))) =
        SmtValue.Numeral 1
    rw [__smtx_model_eval.eq_12, __smtx_model_eval.eq_12]
    simp [__smtx_model_eval.eq_2, __smtx_model_eval_plus, native_zplus]
  have hSimpleGeq :
      __str_arith_entail_simple_pred
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) oneTerm) =
        Term.Boolean true := by
    simpa [oneTerm, __str_arith_entail_simple_pred] using hSimple
  have hOneLe :
      (1 : Int) ≤ zn :=
    int_le_of_simple_geq_true M hM n oneTerm zn 1 hNInt hOneInt hNEval hOneEval
      hSimpleGeq
  exact Int.lt_of_lt_of_le (by decide : (0 : Int) < 1) hOneLe

private theorem numeral_int_type (z : native_Int) :
    __smtx_typeof (__eo_to_smt (Term.Numeral z)) = SmtType.Int := by
  change __smtx_typeof (SmtTerm.Numeral z) = SmtType.Int
  rw [__smtx_typeof.eq_2]

private theorem numeral_int_eval (M : SmtModel) (z : native_Int) :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral z)) = SmtValue.Numeral z := by
  change __smtx_model_eval M (SmtTerm.Numeral z) = SmtValue.Numeral z
  rw [__smtx_model_eval.eq_2]

private theorem numeral_eval_value_eq (M : SmtModel) {z w : native_Int} :
    __smtx_model_eval M (__eo_to_smt (Term.Numeral z)) = SmtValue.Numeral w ->
    w = z := by
  intro hEval
  have hVal : SmtValue.Numeral w = SmtValue.Numeral z := by
    rw [← hEval]
    exact numeral_int_eval M z
  simpa using hVal

private theorem plus_trailing_zero_int_type (n m : Term) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n)
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) m) (Term.Numeral 0)))) =
      SmtType.Int := by
  intro hNInt hMInt
  change
    __smtx_typeof
      (SmtTerm.plus (__eo_to_smt n)
        (SmtTerm.plus (__eo_to_smt m) (SmtTerm.Numeral 0))) = SmtType.Int
  rw [typeof_plus_eq, typeof_plus_eq]
  simp [__smtx_typeof.eq_2, __smtx_typeof_arith_overload_op_2, hNInt, hMInt]

private theorem plus_trailing_zero_int_eval
    (M : SmtModel) (n m : Term) (zn zm : native_Int) :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n)
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) m) (Term.Numeral 0)))) =
      SmtValue.Numeral (zn + zm) := by
  intro hNEval hMEval
  change
    __smtx_model_eval M
      (SmtTerm.plus (__eo_to_smt n)
        (SmtTerm.plus (__eo_to_smt m) (SmtTerm.Numeral 0))) =
      SmtValue.Numeral (zn + zm)
  rw [__smtx_model_eval.eq_12, __smtx_model_eval.eq_12, hNEval, hMEval,
    __smtx_model_eval.eq_2]
  simp [__smtx_model_eval_plus, native_zplus]

private theorem neg_int_type_of_args (n m : Term) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m)) =
      SmtType.Int := by
  intro hNInt hMInt
  change __smtx_typeof (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m)) = SmtType.Int
  rw [typeof_neg_eq]
  simp [__smtx_typeof_arith_overload_op_2, hNInt, hMInt]

private theorem neg_int_eval_of_args
    (M : SmtModel) (n m : Term) (zn zm : native_Int) :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.neg) n) m)) =
      SmtValue.Numeral (zn - zm) := by
  intro hNEval hMEval
  change __smtx_model_eval M (SmtTerm.neg (__eo_to_smt n) (__eo_to_smt m)) =
    SmtValue.Numeral (zn - zm)
  rw [__smtx_model_eval.eq_13, hNEval, hMEval]
  simp [__smtx_model_eval__, native_zplus, native_zneg, Int.sub_eq_add_neg]

private theorem str_len_int_type_of_seq_type (s : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtType.Int := by
  intro hSTy
  change __smtx_typeof (SmtTerm.str_len (__eo_to_smt s)) = SmtType.Int
  rw [typeof_str_len_eq]
  simp [__smtx_typeof_seq_op_1_ret, hSTy]

private theorem str_len_int_eval_of_seq_eval
    (M : SmtModel) (s : Term) (ss : SmtSeq) :
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
  intro hSEval
  change __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt s)) =
    SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length)
  rw [__smtx_model_eval.eq_79, hSEval]
  simp [__smtx_model_eval_str_len, native_seq_len]

private theorem eo_requires_true
    {x y z : Term} :
    __eo_requires x y z = Term.Boolean true ->
    x = y ∧ z = Term.Boolean true := by
  intro h
  by_cases hxy : x = y
  · subst y
    by_cases hx : x = Term.Stuck
    · subst x
      exfalso
      simpa [__eo_requires, native_teq, native_ite, native_not,
        SmtEval.native_not] using h
    · have hReq : __eo_requires x x z = z := by
        simp [__eo_requires, native_teq, hx, native_ite, native_not, SmtEval.native_not]
      rw [hReq] at h
      exact ⟨rfl, h⟩
  · have hReq : __eo_requires x y z = Term.Stuck := by
      simp [__eo_requires, native_teq, hxy, native_ite]
    rw [hReq] at h
    cases h

private theorem int_eval_lt_zero_of_eo_is_neg_true
    (M : SmtModel) (n : Term) (zn : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __eo_is_neg n = Term.Boolean true ->
    zn < 0 := by
  intro hNInt hNEval hNeg
  cases n <;> simp [__eo_is_neg] at hNeg
  case Numeral z =>
    have hZEval : z = zn := by
      have hVal :
          SmtValue.Numeral z = SmtValue.Numeral zn := by
        rw [← hNEval]
        exact (numeral_int_eval M z).symm
      simpa using hVal
    subst zn
    simpa [native_zlt, SmtEval.native_zlt] using hNeg
  case Rational q =>
    change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hNInt
    rw [__smtx_typeof.eq_3] at hNInt
    cases hNInt

private theorem int_eval_nonneg_of_eo_is_neg_false
    (M : SmtModel) (n : Term) (zn : native_Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __eo_is_neg n = Term.Boolean false ->
    0 <= zn := by
  intro hNInt hNEval hNeg
  cases n <;> simp [__eo_is_neg] at hNeg
  case Numeral z =>
    have hZEval : z = zn := by
      have hVal :
          SmtValue.Numeral z = SmtValue.Numeral zn := by
        rw [← hNEval]
        exact (numeral_int_eval M z).symm
      simpa using hVal
    subst zn
    have hNotLt : ¬ z < 0 := by
      simpa [native_zlt, SmtEval.native_zlt] using hNeg
    exact Int.le_of_not_gt hNotLt
  case Rational q =>
    change __smtx_typeof (SmtTerm.Rational q) = SmtType.Int at hNInt
    rw [__smtx_typeof.eq_3] at hNInt
    cases hNInt

private theorem eo_ite_true
    {c t e : Term} :
    __eo_ite c t e = Term.Boolean true ->
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h ⊢
  case Boolean b =>
    cases b <;> simp [__eo_ite, native_teq, native_ite] at h ⊢ <;> exact h

private theorem eo_and_true
    {x y : Term} :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [SmtEval.native_and] at h ⊢

private theorem eo_or_true
    {x y : Term} :
    __eo_or x y = Term.Boolean true ->
    x = Term.Boolean true ∨ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_or, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_or] at h
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [SmtEval.native_or] at h ⊢

private theorem eo_not_true_eq_false
    {x : Term} :
    __eo_not x = Term.Boolean true ->
    x = Term.Boolean false := by
  intro h
  cases x <;> simp [__eo_not, native_not, SmtEval.native_not] at h
  case Boolean b =>
    cases b <;> simp [native_not, SmtEval.native_not] at h ⊢

private theorem eo_not_false_eq_true
    {x : Term} :
    __eo_not x = Term.Boolean false ->
    x = Term.Boolean true := by
  intro h
  cases x <;> simp [__eo_not, native_not, SmtEval.native_not] at h
  case Boolean b =>
    cases b <;> simp [native_not, SmtEval.native_not] at h ⊢

private theorem eo_eq_true_eq
    {x y : Term} :
    __eo_eq x y = Term.Boolean true ->
    x = y := by
  intro h
  by_cases hxSt : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  by_cases hySt : y = Term.Stuck
  · subst y
    simp [__eo_eq] at h
  have hyx : y = x := by
    simpa [__eo_eq, hxSt, hySt, native_teq] using h
  exact hyx.symm

private theorem str_arith_entail_is_approx_bool_top
    {n m : Term} {b : Bool} :
    __str_arith_entail_is_approx n m (Term.Boolean b) = Term.Boolean true ->
    __eo_eq n m = Term.Boolean true ∨
      __eo_l_1___str_arith_entail_is_approx n m (Term.Boolean b) = Term.Boolean true := by
  intro h
  cases n <;> cases m <;>
    simp [__str_arith_entail_is_approx] at h
  all_goals
    rcases eo_ite_true h with hEq | hRest
    · exact Or.inl hEq.1
    · exact Or.inr hRest.2

private theorem int_eval_le_of_eo_eq_true
    (M : SmtModel) {n m : Term} {zn zm : native_Int} :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_eq n m = Term.Boolean true ->
    zm <= zn := by
  intro hNEval hMEval hEq
  have hEqTerms := eo_eq_true_eq hEq
  have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
  rw [hZEq]
  exact Int.le_refl zm

private theorem int_eval_ge_of_eo_eq_true
    (M : SmtModel) {n m : Term} {zn zm : native_Int} :
    __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_eq n m = Term.Boolean true ->
    zn <= zm := by
  intro hNEval hMEval hEq
  have hEqTerms := eo_eq_true_eq hEq
  have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
  rw [hZEq]
  exact Int.le_refl zm

private theorem l1_str_to_int_true
    (s m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_to_int) s) m (Term.Boolean true) =
      Term.Boolean true ->
    __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
        (Term.Boolean true) (Term.Boolean false) =
      Term.Boolean true := by
  intro h
  cases m <;> simp [__eo_l_1___str_arith_entail_is_approx] at h ⊢ <;> exact h

private theorem l1_str_to_int_false
    (s m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_to_int) s) m (Term.Boolean false) =
      Term.Boolean true ->
    __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
        (Term.Boolean false) (Term.Boolean false) =
      Term.Boolean true := by
  intro h
  cases m <;> simp [__eo_l_1___str_arith_entail_is_approx] at h ⊢ <;> exact h

private theorem l1_str_indexof_true
    (s t n0 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)
        m (Term.Boolean true) =
      Term.Boolean true ->
    __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int))) (Term.Boolean true)
        (__eo_ite (__eo_eq m (Term.Apply (Term.UOp UserOp.str_len) s))
          (Term.Boolean false)
          (__eo_ite
            (__eo_eq m
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply (Term.UOp UserOp.str_len) s))
                (Term.Apply (Term.UOp UserOp.str_len) t)))
            (__eo_and (Term.Boolean false)
              (__str_arith_entail_simple_pred
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.geq)
                    (Term.Apply (Term.UOp UserOp.str_len) s))
                  (Term.Apply (Term.UOp UserOp.str_len) t))))
            (Term.Boolean false))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __eo_not, native_not,
      SmtEval.native_not] at h ⊢ <;>
    exact h

private theorem l1_str_indexof_false
    (s t n0 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)
        m (Term.Boolean false) =
      Term.Boolean true ->
    __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int))) (Term.Boolean false)
        (__eo_ite (__eo_eq m (Term.Apply (Term.UOp UserOp.str_len) s))
          (Term.Boolean true)
          (__eo_ite
            (__eo_eq m
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.neg)
                  (Term.Apply (Term.UOp UserOp.str_len) s))
                (Term.Apply (Term.UOp UserOp.str_len) t)))
            (__eo_and (Term.Boolean true)
              (__str_arith_entail_simple_pred
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.geq)
                    (Term.Apply (Term.UOp UserOp.str_len) s))
                  (Term.Apply (Term.UOp UserOp.str_len) t))))
            (Term.Boolean false))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __eo_not, native_not,
      SmtEval.native_not] at h ⊢ <;>
    exact h

private theorem l1_str_from_int_len_true
    (n1 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.UOp UserOp.str_from_int) n1))
        m (Term.Boolean true) =
      Term.Boolean true ->
    __eo_ite
        (__eo_eq m
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
              (Term.Numeral 0))))
        (__eo_and (__eo_not (Term.Boolean true))
          (__str_arith_entail_simple_rec (__get_arith_poly_norm n1)))
        (__eo_ite (__eo_eq m n1)
          (__eo_and (__eo_not (Term.Boolean true))
            (__str_arith_entail_simple_pred
              (Term.Apply (Term.Apply (Term.UOp UserOp.gt) n1) (Term.Numeral 0))))
          (__eo_ite (__eo_eq m (Term.Numeral 1))
            (__eo_and (Term.Boolean true)
              (__str_arith_entail_simple_rec (__get_arith_poly_norm n1)))
            (Term.Boolean false))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_from_int_len_false
    (n1 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.UOp UserOp.str_from_int) n1))
        m (Term.Boolean false) =
      Term.Boolean true ->
    __eo_ite
        (__eo_eq m
          (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
              (Term.Numeral 0))))
        (__eo_and (__eo_not (Term.Boolean false))
          (__str_arith_entail_simple_rec (__get_arith_poly_norm n1)))
        (__eo_ite (__eo_eq m n1)
          (__eo_and (__eo_not (Term.Boolean false))
            (__str_arith_entail_simple_pred
              (Term.Apply (Term.Apply (Term.UOp UserOp.gt) n1) (Term.Numeral 0))))
          (__eo_ite (__eo_eq m (Term.Numeral 1))
            (__eo_and (Term.Boolean false)
              (__str_arith_entail_simple_rec (__get_arith_poly_norm n1)))
            (Term.Boolean false))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_substr_len_true
    (s n1 n2 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))
        m (Term.Boolean true) =
      Term.Boolean true ->
    (let lenS := Term.Apply (Term.UOp UserOp.str_len) s
     let sumN :=
       Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
         (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n2) (Term.Numeral 0))
     let n1Nonneg := __str_arith_entail_simple_rec (__get_arith_poly_norm n1)
     __eo_ite (__eo_eq m n2)
       (__eo_ite (Term.Boolean true)
         (__eo_and n1Nonneg
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenS) sumN)))
         (__str_arith_entail_simple_rec (__get_arith_poly_norm n2)))
       (__eo_ite (__eo_eq m lenS) (__eo_not (Term.Boolean true))
         (__eo_ite
           (__eo_eq m (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1))
           (__eo_ite (Term.Boolean true)
             (__eo_and n1Nonneg
               (__str_arith_entail_simple_pred
                 (Term.Apply (Term.Apply (Term.UOp UserOp.geq) sumN) lenS)))
             (__str_arith_entail_simple_pred
               (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenS) n1)))
           (Term.Boolean false)))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_substr_len_false
    (s n1 n2 m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))
        m (Term.Boolean false) =
      Term.Boolean true ->
    (let lenS := Term.Apply (Term.UOp UserOp.str_len) s
     let sumN :=
       Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
         (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n2) (Term.Numeral 0))
     let n1Nonneg := __str_arith_entail_simple_rec (__get_arith_poly_norm n1)
     __eo_ite (__eo_eq m n2)
       (__eo_ite (Term.Boolean false)
         (__eo_and n1Nonneg
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenS) sumN)))
         (__str_arith_entail_simple_rec (__get_arith_poly_norm n2)))
       (__eo_ite (__eo_eq m lenS) (__eo_not (Term.Boolean false))
         (__eo_ite
           (__eo_eq m (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1))
           (__eo_ite (Term.Boolean false)
             (__eo_and n1Nonneg
               (__str_arith_entail_simple_pred
                 (Term.Apply (Term.Apply (Term.UOp UserOp.geq) sumN) lenS)))
             (__str_arith_entail_simple_pred
               (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenS) n1)))
           (Term.Boolean false)))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_replace_len_true
    (s t r m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))
        m (Term.Boolean true) =
      Term.Boolean true ->
    (let lenT := Term.Apply (Term.UOp UserOp.str_len) t
     let lenS := Term.Apply (Term.UOp UserOp.str_len) s
     let lenR := Term.Apply (Term.UOp UserOp.str_len) r
     __eo_ite (__eo_eq m lenS)
       (__eo_ite (Term.Boolean true)
         (__eo_or
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenR) lenT))
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenR) lenS)))
         (__str_arith_entail_simple_pred
           (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenT) lenR)))
       (__eo_ite
         (__eo_eq m
           (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
             (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))))
         (__eo_not (Term.Boolean true))
         (__eo_ite
           (__eo_eq m (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT))
           (Term.Boolean true)
           (Term.Boolean false)))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem l1_str_replace_len_false
    (s t r m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))
        m (Term.Boolean false) =
      Term.Boolean true ->
    (let lenT := Term.Apply (Term.UOp UserOp.str_len) t
     let lenS := Term.Apply (Term.UOp UserOp.str_len) s
     let lenR := Term.Apply (Term.UOp UserOp.str_len) r
     __eo_ite (__eo_eq m lenS)
       (__eo_ite (Term.Boolean false)
         (__eo_or
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenR) lenT))
           (__str_arith_entail_simple_pred
             (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenR) lenS)))
         (__str_arith_entail_simple_pred
           (Term.Apply (Term.Apply (Term.UOp UserOp.geq) lenT) lenR)))
       (__eo_ite
         (__eo_eq m
           (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
             (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))))
         (__eo_not (Term.Boolean false))
         (__eo_ite
           (__eo_eq m (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT))
           (Term.Boolean false)
           (Term.Boolean false)))) =
      Term.Boolean true := by
  intro h
  cases m <;>
    simp [__eo_l_1___str_arith_entail_is_approx, __str_arith_entail_is_approx_len]
      at h ⊢ <;>
    exact h

private theorem native_seq_extract_len_nonneg
    (xs : List SmtValue) (i n : native_Int) :
    (0 : Int) ≤ Int.ofNat (native_seq_extract xs i n).length := by
  exact Int.ofNat_nonneg _

private theorem native_seq_extract_len_le_len
    (xs : List SmtValue) (i n : native_Int) :
    Int.ofNat (native_seq_extract xs i n).length <= Int.ofNat xs.length := by
  simp only [native_seq_extract]
  split
  · simp
  · have hTake :
        ((xs.drop (Int.toNat i)).take
            (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          (xs.drop (Int.toNat i)).length := by
      rw [List.length_take]
      exact Nat.min_le_right _ _
    have hDrop : (xs.drop (Int.toNat i)).length <= xs.length := by
      rw [List.length_drop]
      exact Nat.sub_le _ _
    exact Int.ofNat_le.mpr (Nat.le_trans hTake hDrop)

private theorem native_seq_extract_len_le_arg_of_nonneg
    (xs : List SmtValue) (i n : native_Int) :
    0 <= n -> Int.ofNat (native_seq_extract xs i n).length <= n := by
  intro hn
  simp only [native_seq_extract]
  split
  · simp [hn]
  · rename_i h
    have hProp : ¬ ((i < 0 ∨ n <= 0) ∨ Int.ofNat xs.length <= i) := by
      simpa [Bool.or_eq_true, decide_eq_true_eq] using h
    have hiNonneg : 0 <= i := by
      have hiNot : ¬ i < 0 := by
        intro hi
        exact hProp (Or.inl (Or.inl hi))
      exact Int.le_of_not_gt hiNot
    have hnPos : 0 < n := by
      have hnNot : ¬ n <= 0 := by
        intro hnle
        exact hProp (Or.inl (Or.inr hnle))
      exact Int.lt_of_not_ge hnNot
    have hiLt : i < Int.ofNat xs.length := by
      have hiNot : ¬ Int.ofNat xs.length <= i := by
        intro hle
        exact hProp (Or.inr hle)
      exact Int.lt_of_not_ge hiNot
    have hTake :
        ((xs.drop (Int.toNat i)).take
            (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          Int.toNat (min n (Int.ofNat xs.length - i)) := by
      exact List.length_take_le _ _
    have hDiffNonneg : 0 <= Int.ofNat xs.length - i := by omega
    have hMinNonneg : 0 <= min n (Int.ofNat xs.length - i) := by
      exact (Int.le_min).2 ⟨hn, hDiffNonneg⟩
    have hCast :
        Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) =
          min n (Int.ofNat xs.length - i) := by
      exact Int.toNat_of_nonneg hMinNonneg
    have hLenLe :
        Int.ofNat
            ((xs.drop (Int.toNat i)).take
              (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
          Int.ofNat (Int.toNat (min n (Int.ofNat xs.length - i))) := by
      exact Int.ofNat_le.mpr hTake
    have hMinLe : min n (Int.ofNat xs.length - i) <= n := Int.min_le_left _ _
    omega

private theorem native_seq_extract_len_ge_arg_of_in_range
    (xs : List SmtValue) (i n : native_Int) :
    0 <= i -> 0 <= n -> i + n <= Int.ofNat xs.length ->
    n <= Int.ofNat (native_seq_extract xs i n).length := by
  intro hi hn hle
  simp only [native_seq_extract]
  by_cases hnZero : n = 0
  · subst n
    simp
  · have hnPos : 0 < n := by grind
    have hiLt : i < Int.ofNat xs.length := by grind
    have hCondFalse :
        ¬ (decide (i < 0) || decide (n <= 0) ||
              decide (i >= Int.ofNat xs.length)) = true := by
      simp [Bool.or_eq_true, decide_eq_true_eq]
      grind
    split
    · rename_i h
      exact False.elim (hCondFalse h)
    · have hMin : min n (Int.ofNat xs.length - i) = n := by
        apply Int.min_eq_left
        grind
      have hTakeNat :
          Int.toNat (min n (Int.ofNat xs.length - i)) = Int.toNat n := by
        rw [hMin]
      have hiCast : Int.ofNat (Int.toNat i) = i := Int.toNat_of_nonneg hi
      have hnCast : Int.ofNat (Int.toNat n) = n := Int.toNat_of_nonneg hn
      have hDropLen :
          (xs.drop (Int.toNat i)).length = xs.length - Int.toNat i :=
        List.length_drop
      have hNLeDrop : Int.toNat n <= (xs.drop (Int.toNat i)).length := by
        rw [hDropLen]
        have hNat : Int.toNat n + Int.toNat i <= xs.length := by
          rw [← Int.ofNat_le]
          rw [Int.natCast_add]
          change
            Int.ofNat (Int.toNat n) + Int.ofNat (Int.toNat i) <=
              Int.ofNat xs.length
          rw [hnCast, hiCast]
          grind
        omega
      rw [hTakeNat, List.length_take, Nat.min_eq_left hNLeDrop]
      rw [hnCast]
      exact Int.le_refl _

private theorem native_seq_extract_len_ge_len_sub_start_of_covers_end
    (xs : List SmtValue) (i n : native_Int) :
    0 <= i -> Int.ofNat xs.length <= i + n ->
    Int.ofNat xs.length - i <= Int.ofNat (native_seq_extract xs i n).length := by
  intro hi hle
  simp only [native_seq_extract]
  by_cases hiEnd : Int.ofNat xs.length <= i
  · split
    · simp
      grind
    · simp
      grind
  · have hiLt : i < Int.ofNat xs.length := by exact Int.lt_of_not_ge hiEnd
    have hnPos : 0 < n := by grind
    have hCondFalse :
        ¬ (decide (i < 0) || decide (n <= 0) ||
              decide (i >= Int.ofNat xs.length)) = true := by
      simp [Bool.or_eq_true, decide_eq_true_eq]
      grind
    split
    · rename_i h
      exact False.elim (hCondFalse h)
    · have hMin :
          min n (Int.ofNat xs.length - i) = Int.ofNat xs.length - i := by
        apply Int.min_eq_right
        grind
      have hTakeNat :
          Int.toNat (min n (Int.ofNat xs.length - i)) =
            Int.toNat (Int.ofNat xs.length - i) := by
        rw [hMin]
      have hiCast : Int.ofNat (Int.toNat i) = i := Int.toNat_of_nonneg hi
      have hDiffNonneg : 0 <= Int.ofNat xs.length - i := by grind
      have hDiffCast :
          Int.ofNat (Int.toNat (Int.ofNat xs.length - i)) =
            Int.ofNat xs.length - i :=
        Int.toNat_of_nonneg hDiffNonneg
      have hDropLen :
          (xs.drop (Int.toNat i)).length = xs.length - Int.toNat i :=
        List.length_drop
      have hILeLenNat : Int.toNat i <= xs.length := by
        rw [← Int.ofNat_le]
        change Int.ofNat (Int.toNat i) <= Int.ofNat xs.length
        rw [hiCast]
        exact Int.le_of_lt hiLt
      have hSubCast :
          Int.ofNat (xs.length - Int.toNat i) =
            Int.ofNat xs.length - Int.ofNat (Int.toNat i) :=
        Int.ofNat_sub hILeLenNat
      have hDropLenCast :
          Int.ofNat (xs.drop (Int.toNat i)).length = Int.ofNat xs.length - i := by
        rw [hDropLen, hSubCast, hiCast]
      have hTakeEq :
          (xs.drop (Int.toNat i)).take
              (Int.toNat (Int.ofNat xs.length - i)) =
            xs.drop (Int.toNat i) := by
        apply List.take_of_length_le
        exact Int.ofNat_le.mp (by
          change
            Int.ofNat (xs.drop (Int.toNat i)).length <=
              Int.ofNat (Int.toNat (Int.ofNat xs.length - i))
          rw [hDropLenCast, hDiffCast]
          exact Int.le_refl _)
      rw [hTakeNat, hTakeEq]
      rw [hDropLen, hSubCast, hiCast]
      exact Int.le_refl _

private theorem native_seq_extract_len_le_len_sub_start_of_start_le_len
    (xs : List SmtValue) (i n : native_Int) :
    i <= Int.ofNat xs.length ->
    Int.ofNat (native_seq_extract xs i n).length <= Int.ofNat xs.length - i := by
  intro hiLe
  by_cases hiNeg : i < 0
  · simp [native_seq_extract, hiNeg]
    have hLenNonneg : (0 : Int) <= Int.ofNat xs.length := Int.ofNat_nonneg _
    omega
  · have hiNonneg : 0 <= i := Int.le_of_not_gt hiNeg
    simp only [native_seq_extract]
    split
    · simp
      omega
    · have hTake :
          ((xs.drop (Int.toNat i)).take
              (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
            (xs.drop (Int.toNat i)).length := by
        rw [List.length_take]
        exact Nat.min_le_right _ _
      have hiCast : Int.ofNat (Int.toNat i) = i := Int.toNat_of_nonneg hiNonneg
      have hILeLenNat : Int.toNat i <= xs.length := by
        rw [← Int.ofNat_le]
        change Int.ofNat (Int.toNat i) <= Int.ofNat xs.length
        rw [hiCast]
        exact hiLe
      have hSubCast :
          Int.ofNat (xs.length - Int.toNat i) =
            Int.ofNat xs.length - Int.ofNat (Int.toNat i) :=
        Int.ofNat_sub hILeLenNat
      have hDropLen :
          Int.ofNat (xs.drop (Int.toNat i)).length =
            Int.ofNat xs.length - i := by
        rw [List.length_drop, hSubCast, hiCast]
      have hLenLe :
          Int.ofNat
              ((xs.drop (Int.toNat i)).take
                (Int.toNat (min n (Int.ofNat xs.length - i)))).length <=
            Int.ofNat (xs.drop (Int.toNat i)).length :=
        Int.ofNat_le.mpr hTake
      rw [hDropLen] at hLenLe
      exact hLenLe

private theorem native_seq_indexof_zero_nonneg_pat_le_len
    (xs pat : List SmtValue) :
    0 <= native_seq_indexof xs pat 0 ->
    pat.length <= xs.length := by
  intro hIdx
  unfold native_seq_indexof at hIdx
  simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add] at hIdx
  split at hIdx
  · assumption
  · have hContr : ¬ ((0 : Int) <= -1) := by decide
    exact False.elim (hContr hIdx)

private theorem native_seq_indexof_zero_nonneg_toNat_add_pat_le_len
    (xs pat : List SmtValue) :
    0 <= native_seq_indexof xs pat 0 ->
    Int.toNat (native_seq_indexof xs pat 0) + pat.length <= xs.length := by
  intro hIdxNonneg
  have hPatLe : pat.length <= xs.length :=
    native_seq_indexof_zero_nonneg_pat_le_len xs pat hIdxNonneg
  have hIdxLe :=
    native_seq_indexof_le_len_sub_pat_of_pat_le_len xs pat 0 hPatLe
  rw [← Int.ofNat_le]
  have hAdd :=
    Int.add_le_of_le_sub_right hIdxLe
  have hMax :
      max (native_seq_indexof xs pat 0) 0 =
        native_seq_indexof xs pat 0 :=
    Int.max_eq_left hIdxNonneg
  simpa [Int.ofNat_toNat, hMax] using hAdd

private theorem native_seq_replace_len_le_len_add_repl
    (xs pat repl : List SmtValue) :
    Int.ofNat (native_seq_replace xs pat repl).length <=
      Int.ofNat xs.length + Int.ofNat repl.length := by
  cases pat with
  | nil =>
      simp [native_seq_replace, List.length_append]
      omega
  | cons p ps =>
      unfold native_seq_replace
      let idx := native_seq_indexof xs (p :: ps) 0
      by_cases hIdxNeg : idx < 0
      · simp [idx, hIdxNeg]
        omega
      · have hIdxNonneg : 0 <= idx := Int.le_of_not_gt hIdxNeg
        have hBound :
            Int.toNat idx + (p :: ps).length <= xs.length := by
          simpa [idx] using
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len xs (p :: ps)
              hIdxNonneg
        have hNLe : Int.toNat idx <= xs.length := by omega
        have hNLe' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) <= xs.length := by
          simpa [idx] using hNLe
        have hBound' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) + (ps.length + 1) <=
              xs.length := by
          simpa [idx] using hBound
        simp [idx, hIdxNeg, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hNLe']
        omega

private theorem native_seq_replace_len_ge_len_sub_pat
    (xs pat repl : List SmtValue) :
    Int.ofNat xs.length - Int.ofNat pat.length <=
      Int.ofNat (native_seq_replace xs pat repl).length := by
  cases pat with
  | nil =>
      simp [native_seq_replace, List.length_append]
      omega
  | cons p ps =>
      unfold native_seq_replace
      let idx := native_seq_indexof xs (p :: ps) 0
      by_cases hIdxNeg : idx < 0
      · simp [idx, hIdxNeg]
        omega
      · have hIdxNonneg : 0 <= idx := Int.le_of_not_gt hIdxNeg
        have hBound :
            Int.toNat idx + (p :: ps).length <= xs.length := by
          simpa [idx] using
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len xs (p :: ps)
              hIdxNonneg
        have hNLe : Int.toNat idx <= xs.length := by omega
        have hNLe' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) <= xs.length := by
          simpa [idx] using hNLe
        have hBound' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) + (ps.length + 1) <=
              xs.length := by
          simpa [idx] using hBound
        simp [idx, hIdxNeg, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hNLe']
        omega

private theorem native_seq_replace_len_le_len_of_repl_le_pat
    (xs pat repl : List SmtValue) :
    repl.length <= pat.length ->
    Int.ofNat (native_seq_replace xs pat repl).length <= Int.ofNat xs.length := by
  intro hReplLe
  cases pat with
  | nil =>
      have hReplZero : repl.length = 0 := Nat.eq_zero_of_le_zero hReplLe
      simp [native_seq_replace, List.length_append, hReplZero]
  | cons p ps =>
      unfold native_seq_replace
      let idx := native_seq_indexof xs (p :: ps) 0
      by_cases hIdxNeg : idx < 0
      · simp [idx, hIdxNeg]
      · have hIdxNonneg : 0 <= idx := Int.le_of_not_gt hIdxNeg
        have hBound :
            Int.toNat idx + (p :: ps).length <= xs.length := by
          simpa [idx] using
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len xs (p :: ps)
              hIdxNonneg
        have hNLe : Int.toNat idx <= xs.length := by omega
        have hNLe' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) <= xs.length := by
          simpa [idx] using hNLe
        have hBound' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) + (ps.length + 1) <=
              xs.length := by
          simpa [idx] using hBound
        let j := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        have hBoundJ : j + (ps.length + 1) <= xs.length := by
          simpa [j] using hBound'
        have hReplLe' : repl.length <= ps.length + 1 := by
          simpa using hReplLe
        have hSplit :
            j + (ps.length + 1) + (xs.length - (j + (ps.length + 1))) =
              xs.length :=
          Nat.add_sub_of_le hBoundJ
        apply Int.ofNat_le.mpr
        simp [idx, hIdxNeg, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hNLe']
        change
          j + (repl.length + (xs.length - (j + (ps.length + 1)))) <= xs.length
        calc
          j + (repl.length + (xs.length - (j + (ps.length + 1)))) <=
              j + ((ps.length + 1) + (xs.length - (j + (ps.length + 1)))) := by
            omega
          _ = xs.length := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hSplit

private theorem native_seq_replace_len_ge_len_of_pat_le_repl_or_len_le_repl
    (xs pat repl : List SmtValue) :
    pat.length <= repl.length ∨ xs.length <= repl.length ->
    Int.ofNat xs.length <= Int.ofNat (native_seq_replace xs pat repl).length := by
  intro hLe
  cases pat with
  | nil =>
      simp [native_seq_replace, List.length_append]
      omega
  | cons p ps =>
      unfold native_seq_replace
      let idx := native_seq_indexof xs (p :: ps) 0
      by_cases hIdxNeg : idx < 0
      · simp [idx, hIdxNeg]
      · have hIdxNonneg : 0 <= idx := Int.le_of_not_gt hIdxNeg
        have hBound :
            Int.toNat idx + (p :: ps).length <= xs.length := by
          simpa [idx] using
            native_seq_indexof_zero_nonneg_toNat_add_pat_le_len xs (p :: ps)
              hIdxNonneg
        have hPatLeRepl : (p :: ps).length <= repl.length := by
          rcases hLe with hPatLe | hLenLe
          · exact hPatLe
          · omega
        have hNLe : Int.toNat idx <= xs.length := by omega
        have hNLe' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) <= xs.length := by
          simpa [idx] using hNLe
        have hBound' :
            Int.toNat (native_seq_indexof xs (p :: ps) 0) + (ps.length + 1) <=
              xs.length := by
          simpa [idx] using hBound
        let j := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        have hBoundJ : j + (ps.length + 1) <= xs.length := by
          simpa [j] using hBound'
        have hPatLeRepl' : ps.length + 1 <= repl.length := by
          simpa using hPatLeRepl
        have hSplit :
            j + (ps.length + 1) + (xs.length - (j + (ps.length + 1))) =
              xs.length :=
          Nat.add_sub_of_le hBoundJ
        apply Int.ofNat_le.mpr
        simp [idx, hIdxNeg, List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hNLe']
        change
          xs.length <=
            j + (repl.length + (xs.length - (j + (ps.length + 1))))
        calc
          xs.length =
              j + ((ps.length + 1) + (xs.length - (j + (ps.length + 1)))) := by
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hSplit.symm
          _ <= j + (repl.length + (xs.length - (j + (ps.length + 1)))) := by
            omega

private theorem nat_toDigitsCore_len_le_fuel
    (base fuel n : Nat) (ds : List Char) :
    (Nat.toDigitsCore base fuel n ds).length <= fuel + ds.length := by
  induction fuel generalizing n ds with
  | zero =>
      simp [Nat.toDigitsCore]
  | succ fuel ih =>
      simp [Nat.toDigitsCore]
      split
      · simp
        omega
      · have h := ih (n / base) ((n % base).digitChar :: ds)
        simp at h
        omega

private theorem nat_toDigitsCore_len_le_value
    (base fuel n : Nat) (ds : List Char) :
    1 < base -> 0 < n ->
    (Nat.toDigitsCore base fuel n ds).length <= n + ds.length := by
  intro hbase hn
  induction fuel generalizing n ds with
  | zero =>
      simp [Nat.toDigitsCore]
  | succ fuel ih =>
      simp [Nat.toDigitsCore]
      split
      · simp
        omega
      · rename_i hnot
        have hnbase : base <= n := by
          have hlt : ¬ n < base := by
            intro hlt
            exact hnot (Or.inr hlt)
          exact Nat.le_of_not_gt hlt
        have hdivpos : 0 < n / base := Nat.div_pos hnbase (by omega)
        have h := ih (n / base) ((n % base).digitChar :: ds) hdivpos
        simp at h
        have hdivlt : n / base < n := Nat.div_lt_self hn hbase
        omega

private theorem nat_toDigitsCore_len_gt_acc
    (base fuel n : Nat) (ds : List Char) :
    ds.length < (Nat.toDigitsCore base (fuel + 1) n ds).length := by
  induction fuel generalizing n ds with
  | zero =>
      simp [Nat.toDigitsCore]
  | succ fuel ih =>
      simp [Nat.toDigitsCore]
      split
      · simp
      · have hcons : ds.length < ((n % base).digitChar :: ds).length := by simp
        have hrec :
            ((n % base).digitChar :: ds).length <
              (if base = 0 ∨ n / base < base then
                  (n / base % base).digitChar :: (n % base).digitChar :: ds
                else
                  Nat.toDigitsCore base fuel (n / base / base)
                    ((n / base % base).digitChar :: (n % base).digitChar :: ds)).length := by
          simpa [Nat.toDigitsCore] using
            ih (n / base) ((n % base).digitChar :: ds)
        exact Nat.lt_trans hcons hrec

private theorem nat_toString_len_le_succ
    (n : Nat) :
    (toString n).length <= n + 1 := by
  change (Nat.repr n).length <= n + 1
  simp [Nat.repr, Nat.toDigits]
  exact nat_toDigitsCore_len_le_fuel 10 (n + 1) n []

private theorem nat_toString_len_le_self_of_pos
    (n : Nat) :
    0 < n -> (toString n).length <= n := by
  intro hn
  change (Nat.repr n).length <= n
  simp [Nat.repr, Nat.toDigits]
  simpa using nat_toDigitsCore_len_le_value 10 (n + 1) n [] (by decide) hn

private theorem nat_toString_len_pos
    (n : Nat) :
    0 < (toString n).length := by
  change 0 < (Nat.repr n).length
  simp [Nat.repr, Nat.toDigits]
  simpa using nat_toDigitsCore_len_gt_acc 10 n n []

private theorem native_str_from_int_len_pos_of_nonneg
    (z : native_Int) :
    0 <= z ->
    (0 : Int) < Int.ofNat (native_str_from_int z).length := by
  intro hz
  cases z with
  | ofNat n =>
      have hlt : ¬ ((Int.ofNat n : Int) < 0) :=
        Int.not_lt.mpr (Int.ofNat_nonneg n)
      rw [native_str_from_int, if_neg hlt]
      change (0 : Int) < Int.ofNat (toString n).length
      exact Int.ofNat_lt.mpr (nat_toString_len_pos n)
  | negSucc n =>
      have hFalse : False := (Int.negSucc_not_nonneg n).mp hz
      exact False.elim hFalse

private theorem native_str_from_int_len_le_succ
    (z : native_Int) :
    0 <= z ->
    Int.ofNat (native_str_from_int z).length <= z + 1 := by
  intro hz
  cases z with
  | ofNat n =>
      have hlt : ¬ ((Int.ofNat n : Int) < 0) :=
        Int.not_lt.mpr (Int.ofNat_nonneg n)
      rw [native_str_from_int, if_neg hlt]
      change Int.ofNat (toString n).length <= Int.ofNat n + 1
      exact Int.ofNat_le.mpr (nat_toString_len_le_succ n)
  | negSucc n =>
      have hFalse : False := (Int.negSucc_not_nonneg n).mp hz
      exact False.elim hFalse

private theorem native_str_from_int_len_le_self_of_pos
    (z : native_Int) :
    0 < z ->
    Int.ofNat (native_str_from_int z).length <= z := by
  intro hz
  cases z with
  | ofNat n =>
      have hn : 0 < n := by
        exact Int.ofNat_lt.mp hz
      have hlt : ¬ ((Int.ofNat n : Int) < 0) :=
        Int.not_lt.mpr (Int.ofNat_nonneg n)
      rw [native_str_from_int, if_neg hlt]
      change Int.ofNat (toString n).length <= Int.ofNat n
      exact Int.ofNat_le.mpr (nat_toString_len_le_self_of_pos n hn)
    | negSucc n =>
        have hFalse : False := by
          have hneg : Int.negSucc n < 0 := Int.negSucc_lt_zero n
          exact (Int.lt_asymm hneg hz).elim
        exact False.elim hFalse

private theorem str_from_int_len_l1_true_order
    (M : SmtModel) (hM : model_total_typed M)
    (n1 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n1))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n1))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.UOp UserOp.str_from_int) n1))
        m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_from_int_len_true n1 m hL1Branch
  rcases str_from_int_len_eval_decomp M hM n1 zn hNInt hNEval with
    ⟨z1, hN1Int, hN1Eval, hZn⟩
  rcases eo_ite_true hIte with hSuccBranch | hRest
  · rcases hSuccBranch with ⟨_, hAnd⟩
    rcases eo_and_true hAnd with ⟨hFalse, _⟩
    simp [__eo_not, native_not, SmtEval.native_not] at hFalse
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hNBranch | hRest2
    · rcases hNBranch with ⟨_, hAnd⟩
      rcases eo_and_true hAnd with ⟨hFalse, _⟩
      simp [__eo_not, native_not, SmtEval.native_not] at hFalse
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hOneBranch | hFalseBranch
      · rcases hOneBranch with ⟨hOneEq, hAnd⟩
        rcases eo_and_true hAnd with ⟨_, hSimple⟩
        have hN1Nonneg : 0 <= z1 :=
          int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hSimple
        have hZMEq :
            zm = (1 : native_Int) :=
          int_eval_eq_of_term_eq M (eo_eq_true_eq hOneEq) hMEval
            (numeral_int_eval M 1)
        rw [hZn, hZMEq]
        have hPos := native_str_from_int_len_pos_of_nonneg z1 hN1Nonneg
        have hNatPos : 0 < (native_str_from_int z1).length :=
          Int.ofNat_lt.mp hPos
        exact Int.ofNat_le.mpr hNatPos
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_from_int_len_l1_false_order
    (M : SmtModel) (hM : model_total_typed M)
    (n1 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n1))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.UOp UserOp.str_from_int) n1))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.UOp UserOp.str_from_int) n1))
        m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_from_int_len_false n1 m hL1Branch
  rcases str_from_int_len_eval_decomp M hM n1 zn hNInt hNEval with
    ⟨z1, hN1Int, hN1Eval, hZn⟩
  let succN :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0))
  have hSuccEval :
      __smtx_model_eval M (__eo_to_smt succN) =
        SmtValue.Numeral (z1 + 1) := by
    simpa [succN] using
      plus_trailing_zero_int_eval M n1 (Term.Numeral 1) z1 1
        hN1Eval (numeral_int_eval M 1)
  rcases eo_ite_true hIte with hSuccBranch | hRest
  · rcases hSuccBranch with ⟨hSuccEq, hAnd⟩
    rcases eo_and_true hAnd with ⟨_, hSimple⟩
    have hN1Nonneg : 0 <= z1 :=
      int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hSimple
    have hZMEq :
        zm = z1 + 1 :=
      int_eval_eq_of_term_eq M (eo_eq_true_eq hSuccEq) hMEval hSuccEval
    rw [hZn, hZMEq]
    exact native_str_from_int_len_le_succ z1 hN1Nonneg
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hNBranch | hRest2
    · rcases hNBranch with ⟨hNEq, hAnd⟩
      rcases eo_and_true hAnd with ⟨_, hPred⟩
      have hN1Pos : 0 < z1 :=
        int_pos_of_simple_gt_zero_true M hM n1 z1 hN1Int hN1Eval hPred
      have hZMEq :
          zm = z1 :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hNEq) hMEval hN1Eval
      rw [hZn, hZMEq]
      exact native_str_from_int_len_le_self_of_pos z1 hN1Pos
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hOneBranch | hFalseBranch
      · rcases hOneBranch with ⟨_, hAnd⟩
        rcases eo_and_true hAnd with ⟨hFalse, _⟩
        cases hFalse
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_substr_len_l1_true_order
    (M : SmtModel) (hM : model_total_typed M)
    (s n1 n2 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1)
              n2))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1)
              n2))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))
        m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_substr_len_true s n1 n2 m hL1Branch
  dsimp only at hIte
  rcases str_substr_len_eval_decomp M hM s n1 n2 zn hNInt hNEval with
    ⟨T, ss, z1, z2, hSTy, hN1Int, hN2Int, hSEval, hN1Eval,
      hN2Eval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let sumN :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n2) (Term.Numeral 0))
  let negLenStart := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hSumInt : __smtx_typeof (__eo_to_smt sumN) = SmtType.Int := by
    simpa [sumN] using plus_trailing_zero_int_type n1 n2 hN1Int hN2Int
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hSumEval :
      __smtx_model_eval M (__eo_to_smt sumN) =
        SmtValue.Numeral (z1 + z2) := by
    simpa [sumN] using plus_trailing_zero_int_eval M n1 n2 z1 z2 hN1Eval hN2Eval
  have hNegEval :
      __smtx_model_eval M (__eo_to_smt negLenStart) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length - z1) := by
    simpa [negLenStart] using
      neg_int_eval_of_args M lenS n1
        (Int.ofNat (native_unpack_seq ss).length) z1 hLenSEval hN1Eval
  rcases eo_ite_true hIte with hN2Branch | hRest
  · rcases hN2Branch with ⟨hN2Eq, hUnderIte⟩
    rcases eo_ite_true hUnderIte with hThen | hElse
    · rcases hThen with ⟨_, hAnd⟩
      rcases eo_and_true hAnd with ⟨hN1Simple, hPred⟩
      have hN1Nonneg : 0 <= z1 :=
        int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hN1Simple
      have hLenSGeSum :
          z1 + z2 <= Int.ofNat (native_unpack_seq ss).length :=
        int_le_of_simple_geq_true M hM lenS sumN
          (Int.ofNat (native_unpack_seq ss).length) (z1 + z2)
          hLenSInt hSumInt hLenSEval hSumEval
          (by simpa [lenS, sumN] using hPred)
      have hZMEq :
          zm = z2 :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hN2Eq) hMEval hN2Eval
      rw [hZn, hZMEq]
      by_cases hN2Nonneg : 0 <= z2
      · exact native_seq_extract_len_ge_arg_of_in_range
          (native_unpack_seq ss) z1 z2 hN1Nonneg hN2Nonneg hLenSGeSum
      · have hLenNonneg :=
          native_seq_extract_len_nonneg (native_unpack_seq ss) z1 z2
        exact Int.le_trans (Int.le_of_lt (Int.lt_of_not_ge hN2Nonneg))
          hLenNonneg
    · rcases hElse with ⟨hContr, _⟩
      cases hContr
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hLenBranch | hRest2
    · rcases hLenBranch with ⟨_, hNot⟩
      simp [__eo_not, native_not, SmtEval.native_not] at hNot
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨hNegEq, hUnderIte⟩
        rcases eo_ite_true hUnderIte with hThen | hElse
        · rcases hThen with ⟨_, hAnd⟩
          rcases eo_and_true hAnd with ⟨hN1Simple, hPred⟩
          have hN1Nonneg : 0 <= z1 :=
            int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval
              hN1Simple
          have hLenSLeSum :
              Int.ofNat (native_unpack_seq ss).length <= z1 + z2 :=
            int_le_of_simple_geq_true M hM sumN lenS (z1 + z2)
              (Int.ofNat (native_unpack_seq ss).length)
              hSumInt hLenSInt hSumEval hLenSEval
              (by simpa [lenS, sumN] using hPred)
          have hZMEq :
              zm = Int.ofNat (native_unpack_seq ss).length - z1 :=
            int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
          rw [hZn, hZMEq]
          exact native_seq_extract_len_ge_len_sub_start_of_covers_end
            (native_unpack_seq ss) z1 z2 hN1Nonneg hLenSLeSum
        · rcases hElse with ⟨hContr, _⟩
          cases hContr
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_substr_len_l1_false_order
    (M : SmtModel) (hM : model_total_typed M)
    (s n1 n2 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1)
              n2))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1)
              n2))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2))
        m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_substr_len_false s n1 n2 m hL1Branch
  dsimp only at hIte
  rcases str_substr_len_eval_decomp M hM s n1 n2 zn hNInt hNEval with
    ⟨T, ss, z1, z2, hSTy, hN1Int, hN2Int, hSEval, hN1Eval,
      hN2Eval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let negLenStart := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hNegEval :
      __smtx_model_eval M (__eo_to_smt negLenStart) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length - z1) := by
    simpa [negLenStart] using
      neg_int_eval_of_args M lenS n1
        (Int.ofNat (native_unpack_seq ss).length) z1 hLenSEval hN1Eval
  rcases eo_ite_true hIte with hN2Branch | hRest
  · rcases hN2Branch with ⟨hN2Eq, hUnderIte⟩
    rcases eo_ite_true hUnderIte with hThen | hElse
    · rcases hThen with ⟨hContr, _⟩
      cases hContr
    · rcases hElse with ⟨_, hN2Simple⟩
      have hN2Nonneg : 0 <= z2 :=
        int_nonneg_of_simple_rec_true M hM n2 z2 hN2Int hN2Eval hN2Simple
      have hZMEq :
          zm = z2 :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hN2Eq) hMEval hN2Eval
      rw [hZn, hZMEq]
      exact native_seq_extract_len_le_arg_of_nonneg
        (native_unpack_seq ss) z1 z2 hN2Nonneg
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hLenBranch | hRest2
    · rcases hLenBranch with ⟨hLenEq, _⟩
      have hZMEq :
          zm = Int.ofNat (native_unpack_seq ss).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
      rw [hZn, hZMEq]
      exact native_seq_extract_len_le_len (native_unpack_seq ss) z1 z2
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨hNegEq, hUnderIte⟩
        rcases eo_ite_true hUnderIte with hThen | hElse
        · rcases hThen with ⟨hContr, _⟩
          cases hContr
        · rcases hElse with ⟨_, hPred⟩
          have hN1LeLenS :
              z1 <= Int.ofNat (native_unpack_seq ss).length :=
            int_le_of_simple_geq_true M hM lenS n1
              (Int.ofNat (native_unpack_seq ss).length) z1
              hLenSInt hN1Int hLenSEval hN1Eval
              (by simpa [lenS] using hPred)
          have hZMEq :
              zm = Int.ofNat (native_unpack_seq ss).length - z1 :=
            int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
          rw [hZn, hZMEq]
          exact native_seq_extract_len_le_len_sub_start_of_start_le_len
            (native_unpack_seq ss) z1 z2 hN1LeLenS
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_replace_len_l1_true_order
    (M : SmtModel) (hM : model_total_typed M)
    (s t r m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))
        m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_replace_len_true s t r m hL1Branch
  dsimp only at hIte
  rcases str_replace_len_eval_decomp M hM s t r zn hNInt hNEval with
    ⟨T, ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let lenT := Term.Apply (Term.UOp UserOp.str_len) t
  let lenR := Term.Apply (Term.UOp UserOp.str_len) r
  let sumLen :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))
  let negLen := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
    simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
  have hLenRInt : __smtx_typeof (__eo_to_smt lenR) = SmtType.Int := by
    simpa [lenR] using str_len_int_type_of_seq_type r T hRTy
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hLenTEval :
      __smtx_model_eval M (__eo_to_smt lenT) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
    simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
  have hLenREval :
      __smtx_model_eval M (__eo_to_smt lenR) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq rr).length) := by
    simpa [lenR] using str_len_int_eval_of_seq_eval M r rr hREval
  have hSumEval :
      __smtx_model_eval M (__eo_to_smt sumLen) =
        SmtValue.Numeral
          (Int.ofNat (native_unpack_seq ss).length +
            Int.ofNat (native_unpack_seq rr).length) := by
    simpa [sumLen] using
      plus_trailing_zero_int_eval M lenS lenR
        (Int.ofNat (native_unpack_seq ss).length)
        (Int.ofNat (native_unpack_seq rr).length) hLenSEval hLenREval
  have hNegEval :
      __smtx_model_eval M (__eo_to_smt negLen) =
        SmtValue.Numeral
          (Int.ofNat (native_unpack_seq ss).length -
            Int.ofNat (native_unpack_seq tt).length) := by
    simpa [negLen] using
      neg_int_eval_of_args M lenS lenT
        (Int.ofNat (native_unpack_seq ss).length)
        (Int.ofNat (native_unpack_seq tt).length) hLenSEval hLenTEval
  rcases eo_ite_true hIte with hLenBranch | hRest
  · rcases hLenBranch with ⟨hLenEq, hUnderIte⟩
    rcases eo_ite_true hUnderIte with hThen | hElse
    · rcases hThen with ⟨_, hOr⟩
      have hLe :
          (native_unpack_seq tt).length <= (native_unpack_seq rr).length ∨
            (native_unpack_seq ss).length <= (native_unpack_seq rr).length := by
        rcases eo_or_true hOr with hPred | hPred
        · have hLenTLeLenR :
              Int.ofNat (native_unpack_seq tt).length <=
                Int.ofNat (native_unpack_seq rr).length :=
            int_le_of_simple_geq_true M hM lenR lenT
              (Int.ofNat (native_unpack_seq rr).length)
              (Int.ofNat (native_unpack_seq tt).length)
              hLenRInt hLenTInt hLenREval hLenTEval
              (by simpa [lenR, lenT] using hPred)
          exact Or.inl (Int.ofNat_le.mp hLenTLeLenR)
        · have hLenSLeLenR :
              Int.ofNat (native_unpack_seq ss).length <=
                Int.ofNat (native_unpack_seq rr).length :=
            int_le_of_simple_geq_true M hM lenR lenS
              (Int.ofNat (native_unpack_seq rr).length)
              (Int.ofNat (native_unpack_seq ss).length)
              hLenRInt hLenSInt hLenREval hLenSEval
              (by simpa [lenR, lenS] using hPred)
          exact Or.inr (Int.ofNat_le.mp hLenSLeLenR)
      have hZMEq :
          zm = Int.ofNat (native_unpack_seq ss).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
      rw [hZn, hZMEq]
      exact native_seq_replace_len_ge_len_of_pat_le_repl_or_len_le_repl
        (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr) hLe
    · rcases hElse with ⟨hContr, _⟩
      cases hContr
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hSumBranch | hRest2
    · rcases hSumBranch with ⟨_, hNot⟩
      simp [__eo_not, native_not, SmtEval.native_not] at hNot
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨hNegEq, _⟩
        have hZMEq :
            zm =
              Int.ofNat (native_unpack_seq ss).length -
                Int.ofNat (native_unpack_seq tt).length :=
          int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
        rw [hZn, hZMEq]
        exact native_seq_replace_len_ge_len_sub_pat
          (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_replace_len_l1_false_order
    (M : SmtModel) (hM : model_total_typed M)
    (s t r m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.str_len)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r))
        m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_replace_len_false s t r m hL1Branch
  dsimp only at hIte
  rcases str_replace_len_eval_decomp M hM s t r zn hNInt hNEval with
    ⟨T, ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let lenT := Term.Apply (Term.UOp UserOp.str_len) t
  let lenR := Term.Apply (Term.UOp UserOp.str_len) r
  let sumLen :=
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
    simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
  have hLenRInt : __smtx_typeof (__eo_to_smt lenR) = SmtType.Int := by
    simpa [lenR] using str_len_int_type_of_seq_type r T hRTy
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hLenTEval :
      __smtx_model_eval M (__eo_to_smt lenT) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
    simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
  have hLenREval :
      __smtx_model_eval M (__eo_to_smt lenR) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq rr).length) := by
    simpa [lenR] using str_len_int_eval_of_seq_eval M r rr hREval
  have hSumEval :
      __smtx_model_eval M (__eo_to_smt sumLen) =
        SmtValue.Numeral
          (Int.ofNat (native_unpack_seq ss).length +
            Int.ofNat (native_unpack_seq rr).length) := by
    simpa [sumLen] using
      plus_trailing_zero_int_eval M lenS lenR
        (Int.ofNat (native_unpack_seq ss).length)
        (Int.ofNat (native_unpack_seq rr).length) hLenSEval hLenREval
  rcases eo_ite_true hIte with hLenBranch | hRest
  · rcases hLenBranch with ⟨hLenEq, hUnderIte⟩
    rcases eo_ite_true hUnderIte with hThen | hElse
    · rcases hThen with ⟨hContr, _⟩
      cases hContr
    · rcases hElse with ⟨_, hPred⟩
      have hLenRLeLenT :
          Int.ofNat (native_unpack_seq rr).length <=
            Int.ofNat (native_unpack_seq tt).length :=
        int_le_of_simple_geq_true M hM lenT lenR
          (Int.ofNat (native_unpack_seq tt).length)
          (Int.ofNat (native_unpack_seq rr).length)
          hLenTInt hLenRInt hLenTEval hLenREval
          (by simpa [lenT, lenR] using hPred)
      have hZMEq :
          zm = Int.ofNat (native_unpack_seq ss).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
      rw [hZn, hZMEq]
      exact native_seq_replace_len_le_len_of_repl_le_pat
        (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
        (Int.ofNat_le.mp hLenRLeLenT)
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hSumBranch | hRest2
    · rcases hSumBranch with ⟨hSumEq, _⟩
      have hZMEq :
          zm =
            Int.ofNat (native_unpack_seq ss).length +
              Int.ofNat (native_unpack_seq rr).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hSumEq) hMEval hSumEval
      rw [hZn, hZMEq]
      exact native_seq_replace_len_le_len_add_repl
        (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨_, hFalse⟩
        cases hFalse
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_to_int_l1_true_order
    (M : SmtModel) (hM : model_total_typed M)
    (s m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_int) s)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_to_int) s) m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte :
      __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Boolean false) =
        Term.Boolean true :=
    l1_str_to_int_true s m hL1Branch
  rcases eo_ite_true hIte with hMinusBranch | hFalseBranch
  · rcases hMinusBranch with ⟨hMinusEq, _⟩
    have hMEq :
        zm = (-1 : native_Int) :=
      int_eval_eq_of_term_eq M (eo_eq_true_eq hMinusEq) hMEval
        (numeral_int_eval M (-1))
    rcases str_to_int_eval_decomp M hM s zn hNInt hNEval with
      ⟨ss, _hSEval, hZn⟩
    rw [hMEq, hZn]
    exact native_str_to_int_ge_neg_one (native_unpack_string ss)
  · rcases hFalseBranch with ⟨_, hFalse⟩
    cases hFalse

private theorem str_to_int_l1_false_order
    (s m : Term) :
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_to_int) s) m (Term.Boolean false) =
      Term.Boolean true ->
    False := by
  intro hL1Branch
  have hIte :
      __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
          (Term.Boolean false) (Term.Boolean false) =
        Term.Boolean true :=
    l1_str_to_int_false s m hL1Branch
  rcases eo_ite_true hIte with hMinusBranch | hFalseBranch
  · rcases hMinusBranch with ⟨_, hFalse⟩
    cases hFalse
  · rcases hFalseBranch with ⟨_, hFalse⟩
    cases hFalse

private theorem str_indexof_l1_true_order
    (M : SmtModel) (hM : model_total_typed M)
    (s t n0 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)
        m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_indexof_true s t n0 m hL1Branch
  rcases eo_ite_true hIte with hMinusBranch | hRest
  · rcases hMinusBranch with ⟨hMinusEq, _⟩
    have hMEq :
        zm = (-1 : native_Int) :=
      int_eval_eq_of_term_eq M (eo_eq_true_eq hMinusEq) hMEval
        (numeral_int_eval M (-1))
    rcases str_indexof_eval_decomp M hM s t n0 zn hNInt hNEval with
      ⟨_T, ss, tt, z0, _hSTy, _hTTy, _hN0Ty, _hSEval, _hTEval,
        _hN0Eval, hZn⟩
    rw [hMEq, hZn]
    exact native_seq_indexof_ge_neg_one (native_unpack_seq ss)
      (native_unpack_seq tt) z0
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hLenBranch | hRest2
    · rcases hLenBranch with ⟨_, hFalse⟩
      cases hFalse
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨_, hAnd⟩
        rcases eo_and_true hAnd with ⟨hFalse, _⟩
        cases hFalse
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_indexof_l1_false_order
    (M : SmtModel) (hM : model_total_typed M)
    (s t n0 m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)) =
      SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0)
        m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hNEval hMEval hL1Branch
  have hIte := l1_str_indexof_false s t n0 m hL1Branch
  rcases str_indexof_eval_decomp M hM s t n0 zn hNInt hNEval with
    ⟨T, ss, tt, z0, hSTy, hTTy, _hN0Ty, hSEval, hTEval, _hN0Eval, hZn⟩
  let lenS := Term.Apply (Term.UOp UserOp.str_len) s
  let lenT := Term.Apply (Term.UOp UserOp.str_len) t
  have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
    simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
  have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
    simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
  have hLenSEval :
      __smtx_model_eval M (__eo_to_smt lenS) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
    simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
  have hLenTEval :
      __smtx_model_eval M (__eo_to_smt lenT) =
        SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
    simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
  rcases eo_ite_true hIte with hMinusBranch | hRest
  · rcases hMinusBranch with ⟨_, hFalse⟩
    cases hFalse
  · rcases hRest with ⟨_, hIte2⟩
    rcases eo_ite_true hIte2 with hLenBranch | hRest2
    · rcases hLenBranch with ⟨hLenEq, _⟩
      have hZMEq :
          zm = Int.ofNat (native_unpack_seq ss).length :=
        int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
      rw [hZn, hZMEq]
      exact native_seq_indexof_le_len (native_unpack_seq ss)
        (native_unpack_seq tt) z0
    · rcases hRest2 with ⟨_, hIte3⟩
      rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
      · rcases hNegBranch with ⟨hNegEq, hAnd⟩
        rcases eo_and_true hAnd with ⟨_, hPred⟩
        have hLenTLeLenS :
            Int.ofNat (native_unpack_seq tt).length <=
              Int.ofNat (native_unpack_seq ss).length :=
          int_le_of_simple_geq_true M hM lenS lenT
            (Int.ofNat (native_unpack_seq ss).length)
            (Int.ofNat (native_unpack_seq tt).length)
            hLenSInt hLenTInt hLenSEval hLenTEval
            (by simpa [lenS, lenT] using hPred)
        have hLenTLeLenSNat :
            (native_unpack_seq tt).length <= (native_unpack_seq ss).length :=
          Int.ofNat_le.mp hLenTLeLenS
        have hNegEval :
            __smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT)) =
              SmtValue.Numeral
                (Int.ofNat (native_unpack_seq ss).length -
                  Int.ofNat (native_unpack_seq tt).length) :=
          neg_int_eval_of_args M lenS lenT
            (Int.ofNat (native_unpack_seq ss).length)
            (Int.ofNat (native_unpack_seq tt).length)
            hLenSEval hLenTEval
        have hZMEq :
            zm =
              Int.ofNat (native_unpack_seq ss).length -
                Int.ofNat (native_unpack_seq tt).length :=
          int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval
            (by simpa [lenS, lenT] using hNegEval)
        rw [hZn, hZMEq]
        exact native_seq_indexof_le_len_sub_pat_of_pat_le_len
          (native_unpack_seq ss) (native_unpack_seq tt) z0 hLenTLeLenSNat
      · rcases hFalseBranch with ⟨_, hFalse⟩
        cases hFalse

private theorem str_len_l1_true_order
    (M : SmtModel) (hM : model_total_typed M)
    (s m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtType.Int ->
    __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len) s) m (Term.Boolean true) =
      Term.Boolean true ->
    zm ≤ zn := by
  intro hNInt hMInt hNEval hMEval hL1Branch
  have hMNe : m ≠ Term.Stuck := by
    intro hSt
    subst m
    exact (by native_decide :
      __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
  cases s with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try
            simp [__eo_l_1___str_arith_entail_is_approx,
              __str_arith_entail_is_approx_len, __eo_not, native_not,
              SmtEval.native_not, hMNe] at hL1Branch
          case str_from_int =>
            exact str_from_int_len_l1_true_order M hM x m zn zm
              hNInt hNEval hMEval
              (by
                simpa [__eo_l_1___str_arith_entail_is_approx,
                  __str_arith_entail_is_approx_len] using hL1Branch)
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;>
                simp [__eo_l_1___str_arith_entail_is_approx,
                  __str_arith_entail_is_approx_len, __eo_not, native_not,
                  SmtEval.native_not, hMNe] at hL1Branch
          | Apply h z =>
              cases h with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not,
                      SmtEval.native_not, hMNe] at hL1Branch
                  case str_substr =>
                    exact str_substr_len_l1_true_order M hM z y x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] using hL1Branch)
                  case str_replace =>
                    exact str_replace_len_l1_true_order M hM z y x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] using hL1Branch)
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len, __eo_not, native_not,
                    SmtEval.native_not, hMNe] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len, __eo_not, native_not,
                SmtEval.native_not, hMNe] at hL1Branch
      | _ =>
          simp [__eo_l_1___str_arith_entail_is_approx,
            __str_arith_entail_is_approx_len, __eo_not, native_not,
            SmtEval.native_not, hMNe] at hL1Branch
  | _ =>
      simp [__eo_l_1___str_arith_entail_is_approx,
        __str_arith_entail_is_approx_len, __eo_not, native_not,
        SmtEval.native_not, hMNe] at hL1Branch

private theorem str_len_l1_false_order
    (M : SmtModel) (hM : model_total_typed M)
    (s m : Term) (zn zm : native_Int) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtType.Int ->
    __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_len) s)) =
      SmtValue.Numeral zn ->
    __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
    __eo_l_1___str_arith_entail_is_approx
        (Term.Apply (Term.UOp UserOp.str_len) s) m (Term.Boolean false) =
      Term.Boolean true ->
    zn ≤ zm := by
  intro hNInt hMInt hNEval hMEval hL1Branch
  have hMNe : m ≠ Term.Stuck := by
    intro hSt
    subst m
    exact (by native_decide :
      __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
  cases s with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try
            simp [__eo_l_1___str_arith_entail_is_approx,
              __str_arith_entail_is_approx_len, __eo_not, native_not,
              SmtEval.native_not, hMNe] at hL1Branch
          case str_from_int =>
            exact str_from_int_len_l1_false_order M hM x m zn zm
              hNInt hNEval hMEval
              (by
                simpa [__eo_l_1___str_arith_entail_is_approx,
                  __str_arith_entail_is_approx_len] using hL1Branch)
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;>
                simp [__eo_l_1___str_arith_entail_is_approx,
                  __str_arith_entail_is_approx_len, __eo_not, native_not,
                  SmtEval.native_not, hMNe] at hL1Branch
          | Apply h z =>
              cases h with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not,
                      SmtEval.native_not, hMNe] at hL1Branch
                  case str_substr =>
                    exact str_substr_len_l1_false_order M hM z y x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] using hL1Branch)
                  case str_replace =>
                    exact str_replace_len_l1_false_order M hM z y x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] using hL1Branch)
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len, __eo_not, native_not,
                    SmtEval.native_not, hMNe] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len, __eo_not, native_not,
                SmtEval.native_not, hMNe] at hL1Branch
      | _ =>
          simp [__eo_l_1___str_arith_entail_is_approx,
            __str_arith_entail_is_approx_len, __eo_not, native_not,
            SmtEval.native_not, hMNe] at hL1Branch
  | _ =>
      simp [__eo_l_1___str_arith_entail_is_approx,
        __str_arith_entail_is_approx_len, __eo_not, native_not,
        SmtEval.native_not, hMNe] at hL1Branch

private theorem str_arith_entail_is_approx_int_eval_order_bool
    (M : SmtModel) (hM : model_total_typed M) :
    (n m : Term) -> (zn zm : native_Int) ->
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
      __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
      (__str_arith_entail_is_approx n m (Term.Boolean true) = Term.Boolean true ->
        zm ≤ zn) ∧
      (__str_arith_entail_is_approx n m (Term.Boolean false) = Term.Boolean true ->
        zn ≤ zm)
  | Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1) n2,
    Term.Apply (Term.Apply (Term.UOp UserOp.plus) n3) n4,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        have hApprox' :
            __eo_ite
                (__eo_eq
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1) n2)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n3) n4))
                (Term.Boolean true)
                (__eo_and (__str_arith_entail_is_approx n1 n3 (Term.Boolean true))
                  (__str_arith_entail_is_approx n2 n4 (Term.Boolean true))) =
              Term.Boolean true := by
          simpa [__str_arith_entail_is_approx, __eo_l_1___str_arith_entail_is_approx] using
            hApprox
        rcases eo_ite_true hApprox' with hEqBranch | hL1Branch
        · rcases hEqBranch with ⟨hEqCond, _⟩
          have hEqTerms := eo_eq_true_eq hEqCond
          have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
          rw [hZEq]
          exact Int.le_refl zm
        · rcases hL1Branch with ⟨_, hAnd⟩
          rcases eo_and_true hAnd with ⟨hA, hB⟩
          rcases plus_int_eval_decomp M hM n1 n2 zn hNInt hNEval with
            ⟨z1, z2, hN1Int, hN2Int, hN1Eval, hN2Eval, hZn⟩
          rcases plus_int_eval_decomp M hM n3 n4 zm hMInt hMEval with
            ⟨z3, z4, hN3Int, hN4Int, hN3Eval, hN4Eval, hZm⟩
          have h13 :
              z3 ≤ z1 :=
            (str_arith_entail_is_approx_int_eval_order_bool M hM n1 n3 z1 z3
              hN1Int hN3Int hN1Eval hN3Eval).1 hA
          have h24 :
              z4 ≤ z2 :=
            (str_arith_entail_is_approx_int_eval_order_bool M hM n2 n4 z2 z4
              hN2Int hN4Int hN2Eval hN4Eval).1 hB
          rw [hZn, hZm]
          calc
            z3 + z4 ≤ z1 + z4 := Int.add_le_add_right h13 z4
            _ ≤ z1 + z2 := Int.add_le_add_left h24 z1
      · intro hApprox
        have hApprox' :
            __eo_ite
                (__eo_eq
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1) n2)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n3) n4))
                (Term.Boolean true)
                (__eo_and (__str_arith_entail_is_approx n1 n3 (Term.Boolean false))
                  (__str_arith_entail_is_approx n2 n4 (Term.Boolean false))) =
              Term.Boolean true := by
          simpa [__str_arith_entail_is_approx, __eo_l_1___str_arith_entail_is_approx] using
            hApprox
        rcases eo_ite_true hApprox' with hEqBranch | hL1Branch
        · rcases hEqBranch with ⟨hEqCond, _⟩
          have hEqTerms := eo_eq_true_eq hEqCond
          have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
          rw [hZEq]
          exact Int.le_refl zm
        · rcases hL1Branch with ⟨_, hAnd⟩
          rcases eo_and_true hAnd with ⟨hA, hB⟩
          rcases plus_int_eval_decomp M hM n1 n2 zn hNInt hNEval with
            ⟨z1, z2, hN1Int, hN2Int, hN1Eval, hN2Eval, hZn⟩
          rcases plus_int_eval_decomp M hM n3 n4 zm hMInt hMEval with
            ⟨z3, z4, hN3Int, hN4Int, hN3Eval, hN4Eval, hZm⟩
          have h13 :
              z1 ≤ z3 :=
            (str_arith_entail_is_approx_int_eval_order_bool M hM n1 n3 z1 z3
              hN1Int hN3Int hN1Eval hN3Eval).2 hA
          have h24 :
              z2 ≤ z4 :=
            (str_arith_entail_is_approx_int_eval_order_bool M hM n2 n4 z2 z4
              hN2Int hN4Int hN2Eval hN4Eval).2 hB
          rw [hZn, hZm]
          calc
            z1 + z2 ≤ z3 + z2 := Int.add_le_add_right h13 z2
            _ ≤ z3 + z4 := Int.add_le_add_left h24 z3
  | Term.Apply (Term.Apply (Term.UOp UserOp.mult) n1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3) (Term.Numeral 1)),
    Term.Apply (Term.Apply (Term.UOp UserOp.mult) n1')
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5) (Term.Numeral 1)),
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · have hEqTerms := eo_eq_true_eq hEqBranch
          have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
          rw [hZEq]
          exact Int.le_refl zm
        · have hReq :
              __eo_requires (__eo_eq n1 n1') (Term.Boolean true)
                  (__eo_ite (__eo_is_neg n1)
                    (__str_arith_entail_is_approx n3 n5 (Term.Boolean false))
                    (__str_arith_entail_is_approx n3 n5 (Term.Boolean true))) =
                Term.Boolean true := by
            simpa [__eo_l_1___str_arith_entail_is_approx, __eo_not, native_not,
              SmtEval.native_not] using hL1Branch
          rcases eo_requires_true hReq with ⟨hCoeffEqCond, hBody⟩
          have hCoeffEqTerms := eo_eq_true_eq hCoeffEqCond
          rcases mult_int_eval_decomp M hM n1
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3) (Term.Numeral 1))
              zn hNInt hNEval with
            ⟨zc, zx1, hCInt, hX1Int, hCEval, hX1Eval, hZn⟩
          rcases mult_int_eval_decomp M hM n3 (Term.Numeral 1) zx1 hX1Int hX1Eval with
            ⟨zx, zOneX, hXInt, _hOneXInt, hXEval, hOneXEval, hZx1⟩
          have hOneX : zOneX = 1 := numeral_eval_value_eq M hOneXEval
          have hZx1' : zx1 = zx := by
            simpa [hOneX] using hZx1
          rcases mult_int_eval_decomp M hM n1'
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5) (Term.Numeral 1))
              zm hMInt hMEval with
            ⟨zc', zy1, hC'Int, hY1Int, hC'Eval, hY1Eval, hZm⟩
          rcases mult_int_eval_decomp M hM n5 (Term.Numeral 1) zy1 hY1Int hY1Eval with
            ⟨zy, zOneY, hYInt, _hOneYInt, hYEval, hOneYEval, hZy1⟩
          have hOneY : zOneY = 1 := numeral_eval_value_eq M hOneYEval
          have hZy1' : zy1 = zy := by
            simpa [hOneY] using hZy1
          have hCoeffEq :
              zc = zc' :=
            int_eval_eq_of_term_eq M hCoeffEqTerms hCEval hC'Eval
          rcases eo_ite_true hBody with hNegBranch | hNonnegBranch
          · rcases hNegBranch with ⟨hNegCond, hRecApprox⟩
            have hCNeg : zc < 0 :=
              int_eval_lt_zero_of_eo_is_neg_true M n1 zc hCInt hCEval hNegCond
            have hXY :
                zx ≤ zy :=
              (str_arith_entail_is_approx_int_eval_order_bool M hM n3 n5 zx zy
                hXInt hYInt hXEval hYEval).2 hRecApprox
            rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
            exact Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hCNeg) hXY
          · rcases hNonnegBranch with ⟨hNegCond, hRecApprox⟩
            have hCNonneg : 0 <= zc :=
              int_eval_nonneg_of_eo_is_neg_false M n1 zc hCInt hCEval hNegCond
            have hXY :
                zy ≤ zx :=
              (str_arith_entail_is_approx_int_eval_order_bool M hM n3 n5 zx zy
                hXInt hYInt hXEval hYEval).1 hRecApprox
            rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
            exact Int.mul_le_mul_of_nonneg_left hXY hCNonneg
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · have hEqTerms := eo_eq_true_eq hEqBranch
          have hZEq := int_eval_eq_of_term_eq M hEqTerms hNEval hMEval
          rw [hZEq]
          exact Int.le_refl zm
        · have hReq :
              __eo_requires (__eo_eq n1 n1') (Term.Boolean true)
                  (__eo_ite (__eo_is_neg n1)
                    (__str_arith_entail_is_approx n3 n5 (Term.Boolean true))
                    (__str_arith_entail_is_approx n3 n5 (Term.Boolean false))) =
                Term.Boolean true := by
            simpa [__eo_l_1___str_arith_entail_is_approx, __eo_not, native_not,
              SmtEval.native_not] using hL1Branch
          rcases eo_requires_true hReq with ⟨hCoeffEqCond, hBody⟩
          have hCoeffEqTerms := eo_eq_true_eq hCoeffEqCond
          rcases mult_int_eval_decomp M hM n1
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3) (Term.Numeral 1))
              zn hNInt hNEval with
            ⟨zc, zx1, hCInt, hX1Int, hCEval, hX1Eval, hZn⟩
          rcases mult_int_eval_decomp M hM n3 (Term.Numeral 1) zx1 hX1Int hX1Eval with
            ⟨zx, zOneX, hXInt, _hOneXInt, hXEval, hOneXEval, hZx1⟩
          have hOneX : zOneX = 1 := numeral_eval_value_eq M hOneXEval
          have hZx1' : zx1 = zx := by
            simpa [hOneX] using hZx1
          rcases mult_int_eval_decomp M hM n1'
              (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5) (Term.Numeral 1))
              zm hMInt hMEval with
            ⟨zc', zy1, hC'Int, hY1Int, hC'Eval, hY1Eval, hZm⟩
          rcases mult_int_eval_decomp M hM n5 (Term.Numeral 1) zy1 hY1Int hY1Eval with
            ⟨zy, zOneY, hYInt, _hOneYInt, hYEval, hOneYEval, hZy1⟩
          have hOneY : zOneY = 1 := numeral_eval_value_eq M hOneYEval
          have hZy1' : zy1 = zy := by
            simpa [hOneY] using hZy1
          have hCoeffEq :
              zc = zc' :=
            int_eval_eq_of_term_eq M hCoeffEqTerms hCEval hC'Eval
          rcases eo_ite_true hBody with hNegBranch | hNonnegBranch
          · rcases hNegBranch with ⟨hNegCond, hRecApprox⟩
            have hCNeg : zc < 0 :=
              int_eval_lt_zero_of_eo_is_neg_true M n1 zc hCInt hCEval hNegCond
            have hXY :
                zy ≤ zx :=
              (str_arith_entail_is_approx_int_eval_order_bool M hM n3 n5 zx zy
                hXInt hYInt hXEval hYEval).1 hRecApprox
            rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
            exact Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hCNeg) hXY
          · rcases hNonnegBranch with ⟨hNegCond, hRecApprox⟩
            have hCNonneg : 0 <= zc :=
              int_eval_nonneg_of_eo_is_neg_false M n1 zc hCInt hCEval hNegCond
            have hXY :
                zx ≤ zy :=
              (str_arith_entail_is_approx_int_eval_order_bool M hM n3 n5 zx zy
                hXInt hYInt hXEval hYEval).2 hRecApprox
            rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
            exact Int.mul_le_mul_of_nonneg_left hXY hCNonneg
  | Term.Apply (Term.UOp UserOp.str_to_int) s, m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte :
              __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
                  (Term.Boolean true) (Term.Boolean false) =
                Term.Boolean true :=
            l1_str_to_int_true s m hL1Branch
          rcases eo_ite_true hIte with hMinusBranch | hFalseBranch
          · rcases hMinusBranch with ⟨hMinusEq, _⟩
            have hMEq :
                zm = (-1 : native_Int) :=
              int_eval_eq_of_term_eq M (eo_eq_true_eq hMinusEq) hMEval
                (numeral_int_eval M (-1))
            rcases str_to_int_eval_decomp M hM s zn hNInt hNEval with
              ⟨ss, _hSEval, hZn⟩
            rw [hMEq, hZn]
            exact native_str_to_int_ge_neg_one (native_unpack_string ss)
          · rcases hFalseBranch with ⟨_, hFalse⟩
            cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte :
              __eo_ite (__eo_eq m (Term.Numeral (-1 : native_Int)))
                  (Term.Boolean false) (Term.Boolean false) =
                Term.Boolean true :=
            l1_str_to_int_false s m hL1Branch
          rcases eo_ite_true hIte with hMinusBranch | hFalseBranch
          · rcases hMinusBranch with ⟨_, hFalse⟩
            cases hFalse
          · rcases hFalseBranch with ⟨_, hFalse⟩
            cases hFalse
  | Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) s) t) n0, m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_indexof_true s t n0 m hL1Branch
          rcases eo_ite_true hIte with hMinusBranch | hRest
          · rcases hMinusBranch with ⟨hMinusEq, _⟩
            have hMEq :
                zm = (-1 : native_Int) :=
              int_eval_eq_of_term_eq M (eo_eq_true_eq hMinusEq) hMEval
                (numeral_int_eval M (-1))
            rcases str_indexof_eval_decomp M hM s t n0 zn hNInt hNEval with
              ⟨T, ss, tt, z0, _hSTy, _hTTy, _hN0Ty, _hSEval, _hTEval,
                _hN0Eval, hZn⟩
            rw [hMEq, hZn]
            exact native_seq_indexof_ge_neg_one (native_unpack_seq ss)
              (native_unpack_seq tt) z0
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hLenBranch | hRest2
            · rcases hLenBranch with ⟨_, hFalse⟩
              cases hFalse
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨_, hAnd⟩
                rcases eo_and_true hAnd with ⟨hFalse, _⟩
                cases hFalse
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_indexof_false s t n0 m hL1Branch
          rcases str_indexof_eval_decomp M hM s t n0 zn hNInt hNEval with
            ⟨T, ss, tt, z0, hSTy, hTTy, _hN0Ty, hSEval, hTEval, _hN0Eval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let lenT := Term.Apply (Term.UOp UserOp.str_len) t
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
            simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hLenTEval :
              __smtx_model_eval M (__eo_to_smt lenT) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
            simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
          rcases eo_ite_true hIte with hMinusBranch | hRest
          · rcases hMinusBranch with ⟨_, hFalse⟩
            cases hFalse
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hLenBranch | hRest2
            · rcases hLenBranch with ⟨hLenEq, _⟩
              have hZMEq :
                  zm = Int.ofNat (native_unpack_seq ss).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
              rw [hZn, hZMEq]
              exact native_seq_indexof_le_len (native_unpack_seq ss)
                (native_unpack_seq tt) z0
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨hNegEq, hAnd⟩
                rcases eo_and_true hAnd with ⟨_, hPred⟩
                have hLenTLeLenS :
                    Int.ofNat (native_unpack_seq tt).length <=
                      Int.ofNat (native_unpack_seq ss).length :=
                  int_le_of_simple_geq_true M hM lenS lenT
                    (Int.ofNat (native_unpack_seq ss).length)
                    (Int.ofNat (native_unpack_seq tt).length)
                    hLenSInt hLenTInt hLenSEval hLenTEval
                    (by simpa [lenS, lenT] using hPred)
                have hLenTLeLenSNat :
                    (native_unpack_seq tt).length <= (native_unpack_seq ss).length :=
                  Int.ofNat_le.mp hLenTLeLenS
                have hNegEval :
                    __smtx_model_eval M
                        (__eo_to_smt
                          (Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT)) =
                      SmtValue.Numeral
                        (Int.ofNat (native_unpack_seq ss).length -
                          Int.ofNat (native_unpack_seq tt).length) :=
                  neg_int_eval_of_args M lenS lenT
                    (Int.ofNat (native_unpack_seq ss).length)
                    (Int.ofNat (native_unpack_seq tt).length)
                    hLenSEval hLenTEval
                have hZMEq :
                    zm =
                      Int.ofNat (native_unpack_seq ss).length -
                        Int.ofNat (native_unpack_seq tt).length :=
                  int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval
                    (by simpa [lenS, lenT] using hNegEval)
                rw [hZn, hZMEq]
                exact native_seq_indexof_le_len_sub_pat_of_pat_le_len
                  (native_unpack_seq ss) (native_unpack_seq tt) z0 hLenTLeLenSNat
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
  | Term.Apply (Term.UOp UserOp.str_len)
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) s) n1) n2), m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_substr_len_true s n1 n2 m hL1Branch
          dsimp only at hIte
          rcases str_substr_len_eval_decomp M hM s n1 n2 zn hNInt hNEval with
            ⟨T, ss, z1, z2, hSTy, hN1Int, hN2Int, hSEval, hN1Eval,
              hN2Eval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let sumN :=
            Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) n2) (Term.Numeral 0))
          let negLenStart := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hSumInt : __smtx_typeof (__eo_to_smt sumN) = SmtType.Int := by
            simpa [sumN] using plus_trailing_zero_int_type n1 n2 hN1Int hN2Int
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hSumEval :
              __smtx_model_eval M (__eo_to_smt sumN) =
                SmtValue.Numeral (z1 + z2) := by
            simpa [sumN] using plus_trailing_zero_int_eval M n1 n2 z1 z2 hN1Eval hN2Eval
          have hNegEval :
              __smtx_model_eval M (__eo_to_smt negLenStart) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length - z1) := by
            simpa [negLenStart] using
              neg_int_eval_of_args M lenS n1
                (Int.ofNat (native_unpack_seq ss).length) z1 hLenSEval hN1Eval
          rcases eo_ite_true hIte with hN2Branch | hRest
          · rcases hN2Branch with ⟨hN2Eq, hUnderIte⟩
            rcases eo_ite_true hUnderIte with hThen | hElse
            · rcases hThen with ⟨_, hAnd⟩
              rcases eo_and_true hAnd with ⟨hN1Simple, hPred⟩
              have hN1Nonneg : 0 <= z1 :=
                int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hN1Simple
              have hLenSGeSum :
                  z1 + z2 <= Int.ofNat (native_unpack_seq ss).length :=
                int_le_of_simple_geq_true M hM lenS sumN
                  (Int.ofNat (native_unpack_seq ss).length) (z1 + z2)
                  hLenSInt hSumInt hLenSEval hSumEval
                  (by simpa [lenS, sumN] using hPred)
              have hZMEq :
                  zm = z2 :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hN2Eq) hMEval hN2Eval
              rw [hZn, hZMEq]
              by_cases hN2Nonneg : 0 <= z2
              · exact native_seq_extract_len_ge_arg_of_in_range
                  (native_unpack_seq ss) z1 z2 hN1Nonneg hN2Nonneg hLenSGeSum
              · have hLenNonneg :=
                  native_seq_extract_len_nonneg (native_unpack_seq ss) z1 z2
                exact Int.le_trans (Int.le_of_lt (Int.lt_of_not_ge hN2Nonneg))
                  hLenNonneg
            · rcases hElse with ⟨hContr, _⟩
              cases hContr
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hLenBranch | hRest2
            · rcases hLenBranch with ⟨_, hNot⟩
              simp [__eo_not, native_not, SmtEval.native_not] at hNot
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨hNegEq, hUnderIte⟩
                rcases eo_ite_true hUnderIte with hThen | hElse
                · rcases hThen with ⟨_, hAnd⟩
                  rcases eo_and_true hAnd with ⟨hN1Simple, hPred⟩
                  have hN1Nonneg : 0 <= z1 :=
                    int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval
                      hN1Simple
                  have hLenSLeSum :
                      Int.ofNat (native_unpack_seq ss).length <= z1 + z2 :=
                    int_le_of_simple_geq_true M hM sumN lenS (z1 + z2)
                      (Int.ofNat (native_unpack_seq ss).length)
                      hSumInt hLenSInt hSumEval hLenSEval
                      (by simpa [lenS, sumN] using hPred)
                  have hZMEq :
                      zm = Int.ofNat (native_unpack_seq ss).length - z1 :=
                    int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
                  rw [hZn, hZMEq]
                  exact native_seq_extract_len_ge_len_sub_start_of_covers_end
                    (native_unpack_seq ss) z1 z2 hN1Nonneg hLenSLeSum
                · rcases hElse with ⟨hContr, _⟩
                  cases hContr
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_substr_len_false s n1 n2 m hL1Branch
          dsimp only at hIte
          rcases str_substr_len_eval_decomp M hM s n1 n2 zn hNInt hNEval with
            ⟨T, ss, z1, z2, hSTy, hN1Int, hN2Int, hSEval, hN1Eval,
              hN2Eval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let negLenStart := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) n1
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hNegEval :
              __smtx_model_eval M (__eo_to_smt negLenStart) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length - z1) := by
            simpa [negLenStart] using
              neg_int_eval_of_args M lenS n1
                (Int.ofNat (native_unpack_seq ss).length) z1 hLenSEval hN1Eval
          rcases eo_ite_true hIte with hN2Branch | hRest
          · rcases hN2Branch with ⟨hN2Eq, hUnderIte⟩
            rcases eo_ite_true hUnderIte with hThen | hElse
            · rcases hThen with ⟨hContr, _⟩
              cases hContr
            · rcases hElse with ⟨_, hN2Simple⟩
              have hN2Nonneg : 0 <= z2 :=
                int_nonneg_of_simple_rec_true M hM n2 z2 hN2Int hN2Eval hN2Simple
              have hZMEq :
                  zm = z2 :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hN2Eq) hMEval hN2Eval
              rw [hZn, hZMEq]
              exact native_seq_extract_len_le_arg_of_nonneg
                (native_unpack_seq ss) z1 z2 hN2Nonneg
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hLenBranch | hRest2
            · rcases hLenBranch with ⟨hLenEq, _⟩
              have hZMEq :
                  zm = Int.ofNat (native_unpack_seq ss).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
              rw [hZn, hZMEq]
              exact native_seq_extract_len_le_len (native_unpack_seq ss) z1 z2
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨hNegEq, hUnderIte⟩
                rcases eo_ite_true hUnderIte with hThen | hElse
                · rcases hThen with ⟨hContr, _⟩
                  cases hContr
                · rcases hElse with ⟨_, hPred⟩
                  have hN1LeLenS :
                      z1 <= Int.ofNat (native_unpack_seq ss).length :=
                    int_le_of_simple_geq_true M hM lenS n1
                      (Int.ofNat (native_unpack_seq ss).length) z1
                      hLenSInt hN1Int hLenSEval hN1Eval
                      (by simpa [lenS] using hPred)
                  have hZMEq :
                      zm = Int.ofNat (native_unpack_seq ss).length - z1 :=
                    int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
                  rw [hZn, hZMEq]
                  exact native_seq_extract_len_le_len_sub_start_of_start_le_len
                    (native_unpack_seq ss) z1 z2 hN1LeLenS
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
  | Term.Apply (Term.UOp UserOp.str_len)
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) s) t) r), m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_replace_len_true s t r m hL1Branch
          dsimp only at hIte
          rcases str_replace_len_eval_decomp M hM s t r zn hNInt hNEval with
            ⟨T, ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let lenT := Term.Apply (Term.UOp UserOp.str_len) t
          let lenR := Term.Apply (Term.UOp UserOp.str_len) r
          let sumLen :=
            Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))
          let negLen := Term.Apply (Term.Apply (Term.UOp UserOp.neg) lenS) lenT
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
            simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
          have hLenRInt : __smtx_typeof (__eo_to_smt lenR) = SmtType.Int := by
            simpa [lenR] using str_len_int_type_of_seq_type r T hRTy
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hLenTEval :
              __smtx_model_eval M (__eo_to_smt lenT) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
            simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
          have hLenREval :
              __smtx_model_eval M (__eo_to_smt lenR) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq rr).length) := by
            simpa [lenR] using str_len_int_eval_of_seq_eval M r rr hREval
          have hSumEval :
              __smtx_model_eval M (__eo_to_smt sumLen) =
                SmtValue.Numeral
                  (Int.ofNat (native_unpack_seq ss).length +
                    Int.ofNat (native_unpack_seq rr).length) := by
            simpa [sumLen] using
              plus_trailing_zero_int_eval M lenS lenR
                (Int.ofNat (native_unpack_seq ss).length)
                (Int.ofNat (native_unpack_seq rr).length) hLenSEval hLenREval
          have hNegEval :
              __smtx_model_eval M (__eo_to_smt negLen) =
                SmtValue.Numeral
                  (Int.ofNat (native_unpack_seq ss).length -
                    Int.ofNat (native_unpack_seq tt).length) := by
            simpa [negLen] using
              neg_int_eval_of_args M lenS lenT
                (Int.ofNat (native_unpack_seq ss).length)
                (Int.ofNat (native_unpack_seq tt).length) hLenSEval hLenTEval
          rcases eo_ite_true hIte with hLenBranch | hRest
          · rcases hLenBranch with ⟨hLenEq, hUnderIte⟩
            rcases eo_ite_true hUnderIte with hThen | hElse
            · rcases hThen with ⟨_, hOr⟩
              have hLe :
                  (native_unpack_seq tt).length <= (native_unpack_seq rr).length ∨
                    (native_unpack_seq ss).length <= (native_unpack_seq rr).length := by
                rcases eo_or_true hOr with hPred | hPred
                · have hLenTLeLenR :
                      Int.ofNat (native_unpack_seq tt).length <=
                        Int.ofNat (native_unpack_seq rr).length :=
                    int_le_of_simple_geq_true M hM lenR lenT
                      (Int.ofNat (native_unpack_seq rr).length)
                      (Int.ofNat (native_unpack_seq tt).length)
                      hLenRInt hLenTInt hLenREval hLenTEval
                      (by simpa [lenR, lenT] using hPred)
                  exact Or.inl (Int.ofNat_le.mp hLenTLeLenR)
                · have hLenSLeLenR :
                      Int.ofNat (native_unpack_seq ss).length <=
                        Int.ofNat (native_unpack_seq rr).length :=
                    int_le_of_simple_geq_true M hM lenR lenS
                      (Int.ofNat (native_unpack_seq rr).length)
                      (Int.ofNat (native_unpack_seq ss).length)
                      hLenRInt hLenSInt hLenREval hLenSEval
                      (by simpa [lenR, lenS] using hPred)
                  exact Or.inr (Int.ofNat_le.mp hLenSLeLenR)
              have hZMEq :
                  zm = Int.ofNat (native_unpack_seq ss).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
              rw [hZn, hZMEq]
              exact native_seq_replace_len_ge_len_of_pat_le_repl_or_len_le_repl
                (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr) hLe
            · rcases hElse with ⟨hContr, _⟩
              cases hContr
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hSumBranch | hRest2
            · rcases hSumBranch with ⟨_, hNot⟩
              simp [__eo_not, native_not, SmtEval.native_not] at hNot
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨hNegEq, _⟩
                have hZMEq :
                    zm =
                      Int.ofNat (native_unpack_seq ss).length -
                        Int.ofNat (native_unpack_seq tt).length :=
                  int_eval_eq_of_term_eq M (eo_eq_true_eq hNegEq) hMEval hNegEval
                rw [hZn, hZMEq]
                exact native_seq_replace_len_ge_len_sub_pat
                  (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_replace_len_false s t r m hL1Branch
          dsimp only at hIte
          rcases str_replace_len_eval_decomp M hM s t r zn hNInt hNEval with
            ⟨T, ss, tt, rr, hSTy, hTTy, hRTy, hSEval, hTEval, hREval, hZn⟩
          let lenS := Term.Apply (Term.UOp UserOp.str_len) s
          let lenT := Term.Apply (Term.UOp UserOp.str_len) t
          let lenR := Term.Apply (Term.UOp UserOp.str_len) r
          let sumLen :=
            Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenS)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) lenR) (Term.Numeral 0))
          have hLenSInt : __smtx_typeof (__eo_to_smt lenS) = SmtType.Int := by
            simpa [lenS] using str_len_int_type_of_seq_type s T hSTy
          have hLenTInt : __smtx_typeof (__eo_to_smt lenT) = SmtType.Int := by
            simpa [lenT] using str_len_int_type_of_seq_type t T hTTy
          have hLenRInt : __smtx_typeof (__eo_to_smt lenR) = SmtType.Int := by
            simpa [lenR] using str_len_int_type_of_seq_type r T hRTy
          have hLenSEval :
              __smtx_model_eval M (__eo_to_smt lenS) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq ss).length) := by
            simpa [lenS] using str_len_int_eval_of_seq_eval M s ss hSEval
          have hLenTEval :
              __smtx_model_eval M (__eo_to_smt lenT) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq tt).length) := by
            simpa [lenT] using str_len_int_eval_of_seq_eval M t tt hTEval
          have hLenREval :
              __smtx_model_eval M (__eo_to_smt lenR) =
                SmtValue.Numeral (Int.ofNat (native_unpack_seq rr).length) := by
            simpa [lenR] using str_len_int_eval_of_seq_eval M r rr hREval
          have hSumEval :
              __smtx_model_eval M (__eo_to_smt sumLen) =
                SmtValue.Numeral
                  (Int.ofNat (native_unpack_seq ss).length +
                    Int.ofNat (native_unpack_seq rr).length) := by
            simpa [sumLen] using
              plus_trailing_zero_int_eval M lenS lenR
                (Int.ofNat (native_unpack_seq ss).length)
                (Int.ofNat (native_unpack_seq rr).length) hLenSEval hLenREval
          rcases eo_ite_true hIte with hLenBranch | hRest
          · rcases hLenBranch with ⟨hLenEq, hUnderIte⟩
            rcases eo_ite_true hUnderIte with hThen | hElse
            · rcases hThen with ⟨hContr, _⟩
              cases hContr
            · rcases hElse with ⟨_, hPred⟩
              have hLenRLeLenT :
                  Int.ofNat (native_unpack_seq rr).length <=
                    Int.ofNat (native_unpack_seq tt).length :=
                int_le_of_simple_geq_true M hM lenT lenR
                  (Int.ofNat (native_unpack_seq tt).length)
                  (Int.ofNat (native_unpack_seq rr).length)
                  hLenTInt hLenRInt hLenTEval hLenREval
                  (by simpa [lenT, lenR] using hPred)
              have hZMEq :
                  zm = Int.ofNat (native_unpack_seq ss).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hLenEq) hMEval hLenSEval
              rw [hZn, hZMEq]
              exact native_seq_replace_len_le_len_of_repl_le_pat
                (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
                (Int.ofNat_le.mp hLenRLeLenT)
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hSumBranch | hRest2
            · rcases hSumBranch with ⟨hSumEq, _⟩
              have hZMEq :
                  zm =
                    Int.ofNat (native_unpack_seq ss).length +
                      Int.ofNat (native_unpack_seq rr).length :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hSumEq) hMEval hSumEval
              rw [hZn, hZMEq]
              exact native_seq_replace_len_le_len_add_repl
                (native_unpack_seq ss) (native_unpack_seq tt) (native_unpack_seq rr)
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hNegBranch | hFalseBranch
              · rcases hNegBranch with ⟨_, hFalse⟩
                cases hFalse
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
  | Term.Apply (Term.UOp UserOp.str_len)
      (Term.Apply (Term.UOp UserOp.str_from_int) n1), m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_from_int_len_true n1 m hL1Branch
          rcases str_from_int_len_eval_decomp M hM n1 zn hNInt hNEval with
            ⟨z1, hN1Int, hN1Eval, hZn⟩
          rcases eo_ite_true hIte with hSuccBranch | hRest
          · rcases hSuccBranch with ⟨_, hAnd⟩
            rcases eo_and_true hAnd with ⟨hFalse, _⟩
            simp [__eo_not, native_not, SmtEval.native_not] at hFalse
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hNBranch | hRest2
            · rcases hNBranch with ⟨_, hAnd⟩
              rcases eo_and_true hAnd with ⟨hFalse, _⟩
              simp [__eo_not, native_not, SmtEval.native_not] at hFalse
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hOneBranch | hFalseBranch
              · rcases hOneBranch with ⟨hOneEq, hAnd⟩
                rcases eo_and_true hAnd with ⟨_, hSimple⟩
                have hN1Nonneg : 0 <= z1 :=
                  int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hSimple
                have hZMEq :
                    zm = (1 : native_Int) :=
                  int_eval_eq_of_term_eq M (eo_eq_true_eq hOneEq) hMEval
                    (numeral_int_eval M 1)
                rw [hZn, hZMEq]
                have hPos := native_str_from_int_len_pos_of_nonneg z1 hN1Nonneg
                have hNatPos : 0 < (native_str_from_int z1).length :=
                  Int.ofNat_lt.mp hPos
                exact Int.ofNat_le.mpr hNatPos
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hIte := l1_str_from_int_len_false n1 m hL1Branch
          rcases str_from_int_len_eval_decomp M hM n1 zn hNInt hNEval with
            ⟨z1, hN1Int, hN1Eval, hZn⟩
          let succN :=
            Term.Apply (Term.Apply (Term.UOp UserOp.plus) n1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
                (Term.Numeral 0))
          have hSuccEval :
              __smtx_model_eval M (__eo_to_smt succN) =
                SmtValue.Numeral (z1 + 1) := by
            simpa [succN] using
              plus_trailing_zero_int_eval M n1 (Term.Numeral 1) z1 1
                hN1Eval (numeral_int_eval M 1)
          rcases eo_ite_true hIte with hSuccBranch | hRest
          · rcases hSuccBranch with ⟨hSuccEq, hAnd⟩
            rcases eo_and_true hAnd with ⟨_, hSimple⟩
            have hN1Nonneg : 0 <= z1 :=
              int_nonneg_of_simple_rec_true M hM n1 z1 hN1Int hN1Eval hSimple
            have hZMEq :
                zm = z1 + 1 :=
              int_eval_eq_of_term_eq M (eo_eq_true_eq hSuccEq) hMEval hSuccEval
            rw [hZn, hZMEq]
            exact native_str_from_int_len_le_succ z1 hN1Nonneg
          · rcases hRest with ⟨_, hIte2⟩
            rcases eo_ite_true hIte2 with hNBranch | hRest2
            · rcases hNBranch with ⟨hNEq, hAnd⟩
              rcases eo_and_true hAnd with ⟨_, hPred⟩
              have hN1Pos : 0 < z1 :=
                int_pos_of_simple_gt_zero_true M hM n1 z1 hN1Int hN1Eval hPred
              have hZMEq :
                  zm = z1 :=
                int_eval_eq_of_term_eq M (eo_eq_true_eq hNEq) hMEval hN1Eval
              rw [hZn, hZMEq]
              exact native_str_from_int_len_le_self_of_pos z1 hN1Pos
            · rcases hRest2 with ⟨_, hIte3⟩
              rcases eo_ite_true hIte3 with hOneBranch | hFalseBranch
              · rcases hOneBranch with ⟨_, hAnd⟩
                rcases eo_and_true hAnd with ⟨hFalse, _⟩
                cases hFalse
              · rcases hFalseBranch with ⟨_, hFalse⟩
                cases hFalse
  | Term.Apply (Term.UOp UserOp.str_len) s, m,
    zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hMNe : m ≠ Term.Stuck := by
            intro hSt
            subst m
            exact (by native_decide :
              __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
          cases s with
          | Apply f x =>
              cases f with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not,
                      SmtEval.native_not, hMNe] at hL1Branch
                  case str_from_int =>
                    exact str_from_int_len_l1_true_order M hM x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] using hL1Branch)
              | Apply g y =>
                  cases g with
                  | UOp op =>
                      cases op <;>
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not,
                          SmtEval.native_not, hMNe] at hL1Branch
                  | Apply h z =>
                      cases h with
                      | UOp op =>
                          cases op <;> try
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not, native_not,
                              SmtEval.native_not, hMNe] at hL1Branch
                          case str_substr =>
                            exact str_substr_len_l1_true_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len] using hL1Branch)
                          case str_replace =>
                            exact str_replace_len_l1_true_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len] using hL1Branch)
                      | _ =>
                          simp [__eo_l_1___str_arith_entail_is_approx,
                            __str_arith_entail_is_approx_len, __eo_not, native_not,
                            SmtEval.native_not, hMNe] at hL1Branch
                  | _ =>
                      simp [__eo_l_1___str_arith_entail_is_approx,
                        __str_arith_entail_is_approx_len, __eo_not, native_not,
                        SmtEval.native_not, hMNe] at hL1Branch
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len, __eo_not, native_not,
                    SmtEval.native_not, hMNe] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len, __eo_not, native_not,
                SmtEval.native_not, hMNe] at hL1Branch
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hMNe : m ≠ Term.Stuck := by
            intro hSt
            subst m
            exact (by native_decide :
              __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
          cases s with
          | Apply f x =>
              cases f with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not,
                      SmtEval.native_not, hMNe] at hL1Branch
                  case str_from_int =>
                    exact str_from_int_len_l1_false_order M hM x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] using hL1Branch)
              | Apply g y =>
                  cases g with
                  | UOp op =>
                      cases op <;>
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not,
                          SmtEval.native_not, hMNe] at hL1Branch
                  | Apply h z =>
                      cases h with
                      | UOp op =>
                          cases op <;> try
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not, native_not,
                              SmtEval.native_not, hMNe] at hL1Branch
                          case str_substr =>
                            exact str_substr_len_l1_false_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len] using hL1Branch)
                          case str_replace =>
                            exact str_replace_len_l1_false_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len] using hL1Branch)
                      | _ =>
                          simp [__eo_l_1___str_arith_entail_is_approx,
                            __str_arith_entail_is_approx_len, __eo_not, native_not,
                            SmtEval.native_not, hMNe] at hL1Branch
                  | _ =>
                      simp [__eo_l_1___str_arith_entail_is_approx,
                        __str_arith_entail_is_approx_len, __eo_not, native_not,
                        SmtEval.native_not, hMNe] at hL1Branch
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len, __eo_not, native_not,
                    SmtEval.native_not, hMNe] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len, __eo_not, native_not,
                SmtEval.native_not, hMNe] at hL1Branch
  | n, m, zn, zm, hNInt, hMInt, hNEval, hMEval => by
      constructor
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_le_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hMNe : m ≠ Term.Stuck := by
            intro hSt
            subst m
            exact (by native_decide :
              __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
          cases n with
          | Apply f x =>
              cases f with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not,
                      SmtEval.native_not, hMNe] at hL1Branch
                  case str_len =>
                    exact str_len_l1_true_order M hM x m zn zm
                      hNInt hMInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] using hL1Branch)
                  case str_to_int =>
                    exact str_to_int_l1_true_order M hM x m zn zm
                      hNInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx] using
                          hL1Branch)
              | Apply g y =>
                  cases g with
                  | UOp op =>
                      cases op <;> try
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not,
                          SmtEval.native_not, hMNe] at hL1Branch
                      case mult =>
                        cases x with
                        | Apply xf xArg =>
                            cases xf with
                            | Apply xg n3 =>
                                cases xg with
                                | UOp xop =>
                                    cases xop <;> try
                                      simp [__eo_l_1___str_arith_entail_is_approx,
                                        __str_arith_entail_is_approx_len, __eo_not,
                                        native_not, SmtEval.native_not, hMNe]
                                        at hL1Branch
                                    case mult =>
                                      cases xArg with
                                      | Numeral k =>
                                          by_cases hk : k = (1 : native_Int)
                                          · subst k
                                            cases m with
                                            | Apply mf mArg =>
                                                cases mf with
                                                | Apply mg n1' =>
                                                    cases mg with
                                                    | UOp mop =>
                                                        cases mop <;> try
                                                          simp [__eo_l_1___str_arith_entail_is_approx,
                                                            __str_arith_entail_is_approx_len, __eo_not,
                                                            native_not, SmtEval.native_not] at hL1Branch
                                                        next =>
                                                          cases mArg with
                                                          | Apply mf2 mArg2 =>
                                                              cases mf2 with
                                                              | Apply mg2 n5 =>
                                                                  cases mg2 with
                                                                  | UOp mop2 =>
                                                                      cases mop2 <;> try
                                                                        simp [__eo_l_1___str_arith_entail_is_approx,
                                                                          __str_arith_entail_is_approx_len, __eo_not,
                                                                          native_not, SmtEval.native_not] at hL1Branch
                                                                      next =>
                                                                        cases mArg2 with
                                                                        | Numeral k2 =>
                                                                            by_cases hk2 : k2 = (1 : native_Int)
                                                                            · subst k2
                                                                              have hReq :
                                                                                  __eo_requires (__eo_eq y n1')
                                                                                      (Term.Boolean true)
                                                                                      (__eo_ite (__eo_is_neg y)
                                                                                        (__str_arith_entail_is_approx n3 n5
                                                                                          (Term.Boolean false))
                                                                                        (__str_arith_entail_is_approx n3 n5
                                                                                          (Term.Boolean true))) =
                                                                                    Term.Boolean true := by
                                                                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                                                                  __eo_not, native_not, SmtEval.native_not]
                                                                                  using hL1Branch
                                                                              rcases eo_requires_true hReq with ⟨hCoeffEqCond, hBody⟩
                                                                              have hCoeffEqTerms := eo_eq_true_eq hCoeffEqCond
                                                                              rcases mult_int_eval_decomp M hM y
                                                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3)
                                                                                    (Term.Numeral 1))
                                                                                  zn hNInt hNEval with
                                                                                ⟨zc, zx1, hCInt, hX1Int, hCEval, hX1Eval, hZn⟩
                                                                              rcases mult_int_eval_decomp M hM n3 (Term.Numeral 1)
                                                                                  zx1 hX1Int hX1Eval with
                                                                                ⟨zx, zOneX, hXInt, _hOneXInt, hXEval,
                                                                                  hOneXEval, hZx1⟩
                                                                              have hOneX : zOneX = 1 := numeral_eval_value_eq M hOneXEval
                                                                              have hZx1' : zx1 = zx := by
                                                                                simpa [hOneX] using hZx1
                                                                              rcases mult_int_eval_decomp M hM n1'
                                                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5)
                                                                                    (Term.Numeral 1))
                                                                                  zm hMInt hMEval with
                                                                                ⟨zc', zy1, hC'Int, hY1Int, hC'Eval, hY1Eval, hZm⟩
                                                                              rcases mult_int_eval_decomp M hM n5 (Term.Numeral 1)
                                                                                  zy1 hY1Int hY1Eval with
                                                                                ⟨zy, zOneY, hYInt, _hOneYInt, hYEval,
                                                                                  hOneYEval, hZy1⟩
                                                                              have hOneY : zOneY = 1 := numeral_eval_value_eq M hOneYEval
                                                                              have hZy1' : zy1 = zy := by
                                                                                simpa [hOneY] using hZy1
                                                                              have hCoeffEq :
                                                                                  zc = zc' :=
                                                                                int_eval_eq_of_term_eq M hCoeffEqTerms hCEval
                                                                                  hC'Eval
                                                                              rcases eo_ite_true hBody with hNegBranch | hNonnegBranch
                                                                              · rcases hNegBranch with ⟨hNegCond, hRecApprox⟩
                                                                                have hCNeg : zc < 0 :=
                                                                                  int_eval_lt_zero_of_eo_is_neg_true M y zc
                                                                                    hCInt hCEval hNegCond
                                                                                have hXY :
                                                                                    zx ≤ zy :=
                                                                                  (str_arith_entail_is_approx_int_eval_order_bool
                                                                                    M hM n3 n5 zx zy hXInt hYInt hXEval
                                                                                    hYEval).2 hRecApprox
                                                                                rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
                                                                                exact Int.mul_le_mul_of_nonpos_left
                                                                                  (Int.le_of_lt hCNeg) hXY
                                                                              · rcases hNonnegBranch with ⟨hNegCond, hRecApprox⟩
                                                                                have hCNonneg : 0 <= zc :=
                                                                                  int_eval_nonneg_of_eo_is_neg_false M y zc
                                                                                    hCInt hCEval hNegCond
                                                                                have hXY :
                                                                                    zy ≤ zx :=
                                                                                  (str_arith_entail_is_approx_int_eval_order_bool
                                                                                    M hM n3 n5 zx zy hXInt hYInt hXEval
                                                                                    hYEval).1 hRecApprox
                                                                                rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
                                                                                exact Int.mul_le_mul_of_nonneg_left hXY
                                                                                  hCNonneg
                                                                            · simp [__eo_l_1___str_arith_entail_is_approx,
                                                                                __str_arith_entail_is_approx_len, __eo_not,
                                                                                native_not, SmtEval.native_not, hk2]
                                                                                at hL1Branch
                                                                        | _ =>
                                                                            simp [__eo_l_1___str_arith_entail_is_approx,
                                                                              __str_arith_entail_is_approx_len, __eo_not,
                                                                              native_not, SmtEval.native_not] at hL1Branch
                                                                  | _ =>
                                                                      simp [__eo_l_1___str_arith_entail_is_approx,
                                                                        __str_arith_entail_is_approx_len, __eo_not,
                                                                        native_not, SmtEval.native_not] at hL1Branch
                                                              | _ =>
                                                                  simp [__eo_l_1___str_arith_entail_is_approx,
                                                                    __str_arith_entail_is_approx_len, __eo_not,
                                                                    native_not, SmtEval.native_not] at hL1Branch
                                                          | _ =>
                                                              simp [__eo_l_1___str_arith_entail_is_approx,
                                                                __str_arith_entail_is_approx_len, __eo_not,
                                                                native_not, SmtEval.native_not] at hL1Branch
                                                    | _ =>
                                                        simp [__eo_l_1___str_arith_entail_is_approx,
                                                          __str_arith_entail_is_approx_len, __eo_not,
                                                          native_not, SmtEval.native_not] at hL1Branch
                                                | _ =>
                                                    simp [__eo_l_1___str_arith_entail_is_approx,
                                                      __str_arith_entail_is_approx_len, __eo_not,
                                                      native_not, SmtEval.native_not] at hL1Branch
                                            | _ =>
                                                simp [__eo_l_1___str_arith_entail_is_approx,
                                                  __str_arith_entail_is_approx_len, __eo_not,
                                                  native_not, SmtEval.native_not] at hL1Branch
                                          · simp [__eo_l_1___str_arith_entail_is_approx,
                                              __str_arith_entail_is_approx_len, __eo_not,
                                              native_not, SmtEval.native_not, hk, hMNe] at hL1Branch
                                      | _ =>
                                          simp [__eo_l_1___str_arith_entail_is_approx,
                                            __str_arith_entail_is_approx_len, __eo_not,
                                            native_not, SmtEval.native_not, hMNe] at hL1Branch
                                | _ =>
                                    simp [__eo_l_1___str_arith_entail_is_approx,
                                      __str_arith_entail_is_approx_len, __eo_not,
                                      native_not, SmtEval.native_not, hMNe] at hL1Branch
                            | _ =>
                                simp [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len, __eo_not,
                                  native_not, SmtEval.native_not, hMNe] at hL1Branch
                        | _ =>
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not,
                              native_not, SmtEval.native_not, hMNe] at hL1Branch
                      case plus =>
                        cases m with
                        | Apply mf mx =>
                            cases mf with
                            | Apply mg my =>
                                cases mg with
                                | UOp mop =>
                                    cases mop <;> try
                                      simp [__eo_l_1___str_arith_entail_is_approx,
                                        __str_arith_entail_is_approx_len, __eo_not,
                                        native_not, SmtEval.native_not] at hL1Branch
                                    case plus =>
                                      have hAnd :
                                          __eo_and
                                              (__str_arith_entail_is_approx y my
                                                (Term.Boolean true))
                                              (__str_arith_entail_is_approx x mx
                                                (Term.Boolean true)) =
                                            Term.Boolean true := by
                                        simpa [__eo_l_1___str_arith_entail_is_approx]
                                          using hL1Branch
                                      rcases eo_and_true hAnd with ⟨hA, hB⟩
                                      rcases plus_int_eval_decomp M hM y x zn hNInt hNEval with
                                        ⟨z1, z2, hN1Int, hN2Int, hN1Eval, hN2Eval, hZn⟩
                                      rcases plus_int_eval_decomp M hM my mx zm hMInt hMEval with
                                        ⟨z3, z4, hN3Int, hN4Int, hN3Eval, hN4Eval, hZm⟩
                                      have h13 :
                                          z3 ≤ z1 :=
                                        (str_arith_entail_is_approx_int_eval_order_bool
                                          M hM y my z1 z3 hN1Int hN3Int hN1Eval
                                          hN3Eval).1 hA
                                      have h24 :
                                          z4 ≤ z2 :=
                                        (str_arith_entail_is_approx_int_eval_order_bool
                                          M hM x mx z2 z4 hN2Int hN4Int hN2Eval
                                          hN4Eval).1 hB
                                      rw [hZn, hZm]
                                      calc
                                        z3 + z4 ≤ z1 + z4 :=
                                          Int.add_le_add_right h13 z4
                                        _ ≤ z1 + z2 := Int.add_le_add_left h24 z1
                                | _ =>
                                    simp [__eo_l_1___str_arith_entail_is_approx,
                                      __str_arith_entail_is_approx_len, __eo_not,
                                      native_not, SmtEval.native_not] at hL1Branch
                            | _ =>
                                simp [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len, __eo_not,
                                  native_not, SmtEval.native_not] at hL1Branch
                        | _ =>
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not, native_not,
                              SmtEval.native_not] at hL1Branch
                  | Apply h z =>
                      cases h with
                      | UOp op =>
                          cases op <;> try
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not, native_not,
                              SmtEval.native_not, hMNe] at hL1Branch
                          case str_indexof =>
                            exact str_indexof_l1_true_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                  __eo_not, native_not, SmtEval.native_not] using
                                  hL1Branch)
                      | _ =>
                          simp [__eo_l_1___str_arith_entail_is_approx,
                            __str_arith_entail_is_approx_len, __eo_not, native_not,
                            SmtEval.native_not, hMNe] at hL1Branch
                  | _ =>
                      simp [__eo_l_1___str_arith_entail_is_approx,
                        __str_arith_entail_is_approx_len, __eo_not, native_not,
                        SmtEval.native_not, hMNe] at hL1Branch
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len, __eo_not, native_not,
                    SmtEval.native_not, hMNe] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len, __eo_not, native_not,
                SmtEval.native_not, hMNe] at hL1Branch
      · intro hApprox
        rcases str_arith_entail_is_approx_bool_top hApprox with hEqBranch | hL1Branch
        · exact int_eval_ge_of_eo_eq_true M hNEval hMEval hEqBranch
        · have hMNe : m ≠ Term.Stuck := by
            intro hSt
            subst m
            exact (by native_decide :
              __smtx_typeof (__eo_to_smt Term.Stuck) ≠ SmtType.Int) hMInt
          cases n with
          | Apply f x =>
              cases f with
              | UOp op =>
                  cases op <;> try
                    simp [__eo_l_1___str_arith_entail_is_approx,
                      __str_arith_entail_is_approx_len, __eo_not, native_not,
                      SmtEval.native_not, hMNe] at hL1Branch
                  case str_len =>
                    exact str_len_l1_false_order M hM x m zn zm
                      hNInt hMInt hNEval hMEval
                      (by
                        simpa [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len] using hL1Branch)
                  case str_to_int =>
                    exact False.elim
                      (str_to_int_l1_false_order x m
                        (by
                          simpa [__eo_l_1___str_arith_entail_is_approx] using
                            hL1Branch))
              | Apply g y =>
                  cases g with
                  | UOp op =>
                      cases op <;> try
                        simp [__eo_l_1___str_arith_entail_is_approx,
                          __str_arith_entail_is_approx_len, __eo_not, native_not,
                          SmtEval.native_not, hMNe] at hL1Branch
                      case mult =>
                        cases x with
                        | Apply xf xArg =>
                            cases xf with
                            | Apply xg n3 =>
                                cases xg with
                                | UOp xop =>
                                    cases xop <;> try
                                      simp [__eo_l_1___str_arith_entail_is_approx,
                                        __str_arith_entail_is_approx_len, __eo_not,
                                        native_not, SmtEval.native_not, hMNe]
                                        at hL1Branch
                                    case mult =>
                                      cases xArg with
                                      | Numeral k =>
                                          by_cases hk : k = (1 : native_Int)
                                          · subst k
                                            cases m with
                                            | Apply mf mArg =>
                                                cases mf with
                                                | Apply mg n1' =>
                                                    cases mg with
                                                    | UOp mop =>
                                                        cases mop <;> try
                                                          simp [__eo_l_1___str_arith_entail_is_approx,
                                                            __str_arith_entail_is_approx_len, __eo_not,
                                                            native_not, SmtEval.native_not] at hL1Branch
                                                        next =>
                                                          cases mArg with
                                                          | Apply mf2 mArg2 =>
                                                              cases mf2 with
                                                              | Apply mg2 n5 =>
                                                                  cases mg2 with
                                                                  | UOp mop2 =>
                                                                      cases mop2 <;> try
                                                                        simp [__eo_l_1___str_arith_entail_is_approx,
                                                                          __str_arith_entail_is_approx_len, __eo_not,
                                                                          native_not, SmtEval.native_not] at hL1Branch
                                                                      next =>
                                                                        cases mArg2 with
                                                                        | Numeral k2 =>
                                                                            by_cases hk2 : k2 = (1 : native_Int)
                                                                            · subst k2
                                                                              have hReq :
                                                                                  __eo_requires (__eo_eq y n1')
                                                                                      (Term.Boolean true)
                                                                                      (__eo_ite (__eo_is_neg y)
                                                                                        (__str_arith_entail_is_approx n3 n5
                                                                                          (Term.Boolean true))
                                                                                        (__str_arith_entail_is_approx n3 n5
                                                                                          (Term.Boolean false))) =
                                                                                    Term.Boolean true := by
                                                                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                                                                  __eo_not, native_not, SmtEval.native_not]
                                                                                  using hL1Branch
                                                                              rcases eo_requires_true hReq with ⟨hCoeffEqCond, hBody⟩
                                                                              have hCoeffEqTerms := eo_eq_true_eq hCoeffEqCond
                                                                              rcases mult_int_eval_decomp M hM y
                                                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n3)
                                                                                    (Term.Numeral 1))
                                                                                  zn hNInt hNEval with
                                                                                ⟨zc, zx1, hCInt, hX1Int, hCEval, hX1Eval, hZn⟩
                                                                              rcases mult_int_eval_decomp M hM n3 (Term.Numeral 1)
                                                                                  zx1 hX1Int hX1Eval with
                                                                                ⟨zx, zOneX, hXInt, _hOneXInt, hXEval,
                                                                                  hOneXEval, hZx1⟩
                                                                              have hOneX : zOneX = 1 := numeral_eval_value_eq M hOneXEval
                                                                              have hZx1' : zx1 = zx := by
                                                                                simpa [hOneX] using hZx1
                                                                              rcases mult_int_eval_decomp M hM n1'
                                                                                  (Term.Apply (Term.Apply (Term.UOp UserOp.mult) n5)
                                                                                    (Term.Numeral 1))
                                                                                  zm hMInt hMEval with
                                                                                ⟨zc', zy1, hC'Int, hY1Int, hC'Eval, hY1Eval, hZm⟩
                                                                              rcases mult_int_eval_decomp M hM n5 (Term.Numeral 1)
                                                                                  zy1 hY1Int hY1Eval with
                                                                                ⟨zy, zOneY, hYInt, _hOneYInt, hYEval,
                                                                                  hOneYEval, hZy1⟩
                                                                              have hOneY : zOneY = 1 := numeral_eval_value_eq M hOneYEval
                                                                              have hZy1' : zy1 = zy := by
                                                                                simpa [hOneY] using hZy1
                                                                              have hCoeffEq :
                                                                                  zc = zc' :=
                                                                                int_eval_eq_of_term_eq M hCoeffEqTerms hCEval
                                                                                  hC'Eval
                                                                              rcases eo_ite_true hBody with hNegBranch | hNonnegBranch
                                                                              · rcases hNegBranch with ⟨hNegCond, hRecApprox⟩
                                                                                have hCNeg : zc < 0 :=
                                                                                  int_eval_lt_zero_of_eo_is_neg_true M y zc
                                                                                    hCInt hCEval hNegCond
                                                                                have hXY :
                                                                                    zy ≤ zx :=
                                                                                  (str_arith_entail_is_approx_int_eval_order_bool
                                                                                    M hM n3 n5 zx zy hXInt hYInt hXEval
                                                                                    hYEval).1 hRecApprox
                                                                                rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
                                                                                exact Int.mul_le_mul_of_nonpos_left
                                                                                  (Int.le_of_lt hCNeg) hXY
                                                                              · rcases hNonnegBranch with ⟨hNegCond, hRecApprox⟩
                                                                                have hCNonneg : 0 <= zc :=
                                                                                  int_eval_nonneg_of_eo_is_neg_false M y zc
                                                                                    hCInt hCEval hNegCond
                                                                                have hXY :
                                                                                    zx ≤ zy :=
                                                                                  (str_arith_entail_is_approx_int_eval_order_bool
                                                                                    M hM n3 n5 zx zy hXInt hYInt hXEval
                                                                                    hYEval).2 hRecApprox
                                                                                rw [hZn, hZm, hZx1', hZy1', ← hCoeffEq]
                                                                                exact Int.mul_le_mul_of_nonneg_left hXY
                                                                                  hCNonneg
                                                                            · simp [__eo_l_1___str_arith_entail_is_approx,
                                                                                __str_arith_entail_is_approx_len, __eo_not,
                                                                                native_not, SmtEval.native_not, hk2]
                                                                                at hL1Branch
                                                                        | _ =>
                                                                            simp [__eo_l_1___str_arith_entail_is_approx,
                                                                              __str_arith_entail_is_approx_len, __eo_not,
                                                                              native_not, SmtEval.native_not] at hL1Branch
                                                                  | _ =>
                                                                      simp [__eo_l_1___str_arith_entail_is_approx,
                                                                        __str_arith_entail_is_approx_len, __eo_not,
                                                                        native_not, SmtEval.native_not] at hL1Branch
                                                              | _ =>
                                                                  simp [__eo_l_1___str_arith_entail_is_approx,
                                                                    __str_arith_entail_is_approx_len, __eo_not,
                                                                    native_not, SmtEval.native_not] at hL1Branch
                                                          | _ =>
                                                              simp [__eo_l_1___str_arith_entail_is_approx,
                                                                __str_arith_entail_is_approx_len, __eo_not,
                                                                native_not, SmtEval.native_not] at hL1Branch
                                                    | _ =>
                                                        simp [__eo_l_1___str_arith_entail_is_approx,
                                                          __str_arith_entail_is_approx_len, __eo_not,
                                                          native_not, SmtEval.native_not] at hL1Branch
                                                | _ =>
                                                    simp [__eo_l_1___str_arith_entail_is_approx,
                                                      __str_arith_entail_is_approx_len, __eo_not,
                                                      native_not, SmtEval.native_not] at hL1Branch
                                            | _ =>
                                                simp [__eo_l_1___str_arith_entail_is_approx,
                                                  __str_arith_entail_is_approx_len, __eo_not,
                                                  native_not, SmtEval.native_not] at hL1Branch
                                          · simp [__eo_l_1___str_arith_entail_is_approx,
                                              __str_arith_entail_is_approx_len, __eo_not,
                                              native_not, SmtEval.native_not, hk, hMNe] at hL1Branch
                                      | _ =>
                                          simp [__eo_l_1___str_arith_entail_is_approx,
                                            __str_arith_entail_is_approx_len, __eo_not,
                                            native_not, SmtEval.native_not, hMNe] at hL1Branch
                                | _ =>
                                    simp [__eo_l_1___str_arith_entail_is_approx,
                                      __str_arith_entail_is_approx_len, __eo_not,
                                      native_not, SmtEval.native_not, hMNe] at hL1Branch
                            | _ =>
                                simp [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len, __eo_not,
                                  native_not, SmtEval.native_not, hMNe] at hL1Branch
                        | _ =>
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not,
                              native_not, SmtEval.native_not, hMNe] at hL1Branch
                      case plus =>
                        cases m with
                        | Apply mf mx =>
                            cases mf with
                            | Apply mg my =>
                                cases mg with
                                | UOp mop =>
                                    cases mop <;> try
                                      simp [__eo_l_1___str_arith_entail_is_approx,
                                        __str_arith_entail_is_approx_len, __eo_not,
                                        native_not, SmtEval.native_not] at hL1Branch
                                    case plus =>
                                      have hAnd :
                                          __eo_and
                                              (__str_arith_entail_is_approx y my
                                                (Term.Boolean false))
                                              (__str_arith_entail_is_approx x mx
                                                (Term.Boolean false)) =
                                            Term.Boolean true := by
                                        simpa [__eo_l_1___str_arith_entail_is_approx]
                                          using hL1Branch
                                      rcases eo_and_true hAnd with ⟨hA, hB⟩
                                      rcases plus_int_eval_decomp M hM y x zn hNInt hNEval with
                                        ⟨z1, z2, hN1Int, hN2Int, hN1Eval, hN2Eval, hZn⟩
                                      rcases plus_int_eval_decomp M hM my mx zm hMInt hMEval with
                                        ⟨z3, z4, hN3Int, hN4Int, hN3Eval, hN4Eval, hZm⟩
                                      have h13 :
                                          z1 ≤ z3 :=
                                        (str_arith_entail_is_approx_int_eval_order_bool
                                          M hM y my z1 z3 hN1Int hN3Int hN1Eval
                                          hN3Eval).2 hA
                                      have h24 :
                                          z2 ≤ z4 :=
                                        (str_arith_entail_is_approx_int_eval_order_bool
                                          M hM x mx z2 z4 hN2Int hN4Int hN2Eval
                                          hN4Eval).2 hB
                                      rw [hZn, hZm]
                                      calc
                                        z1 + z2 ≤ z3 + z2 :=
                                          Int.add_le_add_right h13 z2
                                        _ ≤ z3 + z4 := Int.add_le_add_left h24 z3
                                | _ =>
                                    simp [__eo_l_1___str_arith_entail_is_approx,
                                      __str_arith_entail_is_approx_len, __eo_not,
                                      native_not, SmtEval.native_not] at hL1Branch
                            | _ =>
                                simp [__eo_l_1___str_arith_entail_is_approx,
                                  __str_arith_entail_is_approx_len, __eo_not,
                                  native_not, SmtEval.native_not] at hL1Branch
                        | _ =>
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not, native_not,
                              SmtEval.native_not] at hL1Branch
                  | Apply h z =>
                      cases h with
                      | UOp op =>
                          cases op <;> try
                            simp [__eo_l_1___str_arith_entail_is_approx,
                              __str_arith_entail_is_approx_len, __eo_not, native_not,
                              SmtEval.native_not, hMNe] at hL1Branch
                          case str_indexof =>
                            exact str_indexof_l1_false_order M hM z y x m zn zm
                              hNInt hNEval hMEval
                              (by
                                simpa [__eo_l_1___str_arith_entail_is_approx,
                                  __eo_not, native_not, SmtEval.native_not] using
                                  hL1Branch)
                      | _ =>
                          simp [__eo_l_1___str_arith_entail_is_approx,
                            __str_arith_entail_is_approx_len, __eo_not, native_not,
                            SmtEval.native_not, hMNe] at hL1Branch
                  | _ =>
                      simp [__eo_l_1___str_arith_entail_is_approx,
                        __str_arith_entail_is_approx_len, __eo_not, native_not,
                        SmtEval.native_not, hMNe] at hL1Branch
              | _ =>
                  simp [__eo_l_1___str_arith_entail_is_approx,
                    __str_arith_entail_is_approx_len, __eo_not, native_not,
                    SmtEval.native_not, hMNe] at hL1Branch
          | _ =>
              simp [__eo_l_1___str_arith_entail_is_approx,
                __str_arith_entail_is_approx_len, __eo_not, native_not,
                SmtEval.native_not, hMNe] at hL1Branch

private theorem str_arith_entail_is_approx_int_eval_order
    (M : SmtModel) (hM : model_total_typed M) :
    (n m isUnder : Term) -> (zn zm : native_Int) ->
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
      __smtx_model_eval M (__eo_to_smt n) = SmtValue.Numeral zn ->
      __smtx_model_eval M (__eo_to_smt m) = SmtValue.Numeral zm ->
      __str_arith_entail_is_approx n m isUnder = Term.Boolean true ->
      (isUnder = Term.Boolean true -> zm ≤ zn) ∧
        (isUnder = Term.Boolean false -> zn ≤ zm)
  | n, m, isUnder, zn, zm, hNInt, hMInt, hNEval, hMEval, hApprox => by
      constructor
      · intro hUnder
        subst isUnder
        exact (str_arith_entail_is_approx_int_eval_order_bool M hM n m zn zm
          hNInt hMInt hNEval hMEval).1 hApprox
      · intro hUnder
        subst isUnder
        exact (str_arith_entail_is_approx_int_eval_order_bool M hM n m zn zm
          hNInt hMInt hNEval hMEval).2 hApprox

private theorem str_arith_entail_is_approx_int_denote_order
    (M : SmtModel) (hM : model_total_typed M) :
    (n m isUnder : Term) -> (qn qm : native_Rat) ->
      __smtx_typeof (__eo_to_smt n) = SmtType.Int ->
      __smtx_typeof (__eo_to_smt m) = SmtType.Int ->
      __str_arith_entail_is_approx n m isUnder = Term.Boolean true ->
      arith_atom_denote_real M n = SmtValue.Rational qn ->
      arith_atom_denote_real M m = SmtValue.Rational qm ->
      (isUnder = Term.Boolean true -> qm ≤ qn) ∧
        (isUnder = Term.Boolean false -> qn ≤ qm)
  | n, m, isUnder, qn, qm, hNInt, hMInt, hApprox, hNDen, hMDen => by
      rcases int_eval_of_int_type M hM n hNInt with ⟨zn, hNEval⟩
      rcases int_eval_of_int_type M hM m hMInt with ⟨zm, hMEval⟩
      have hQn : qn = native_to_real zn := by
        have h :
            SmtValue.Rational (native_to_real zn) = SmtValue.Rational qn := by
          simpa [arith_atom_denote_real, hNEval, __smtx_model_eval_to_real] using hNDen
        simpa using h.symm
      have hQm : qm = native_to_real zm := by
        have h :
            SmtValue.Rational (native_to_real zm) = SmtValue.Rational qm := by
          simpa [arith_atom_denote_real, hMEval, __smtx_model_eval_to_real] using hMDen
        simpa using h.symm
      have hOrder :=
        str_arith_entail_is_approx_int_eval_order M hM n m isUnder zn zm
          hNInt hMInt hNEval hMEval hApprox
      constructor
      · intro hUnder
        rw [hQm, hQn]
        exact (native_to_real_le_iff zm zn).2 (hOrder.1 hUnder)
      · intro hOver
        rw [hQn, hQm]
        exact (native_to_real_le_iff zn zm).2 (hOrder.2 hOver)

private theorem arith_string_pred_safe_approx_left_true
    (M : SmtModel) (hM : model_total_typed M) (n m : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) ->
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) ->
  __str_arith_entail_is_approx n m (Term.Boolean true) = Term.Boolean true ->
  __str_arith_entail_simple_pred
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) =
    Term.Boolean true ->
  eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) true := by
  intro hNBool hMBool hApprox hSimple
  have hNInt : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    geq_left_int_type_of_has_bool_type n hNBool
  have hMInt : __smtx_typeof (__eo_to_smt m) = SmtType.Int :=
    geq_left_int_type_of_has_bool_type m hMBool
  rcases arith_atom_denote_real_rational_of_smt_arith_type
      M hM n (Or.inl hNInt) with
    ⟨qn, hNDen⟩
  rcases arith_atom_denote_real_rational_of_smt_arith_type
      M hM m (Or.inl hMInt) with
    ⟨qm, hMDen⟩
  have hMTrue :
      eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) true :=
    arith_string_pred_simple_geq_true M hM m (Term.Numeral 0) hMBool hSimple
  have hMEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0))) =
        SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) true).mp
        hMTrue with
    | intro_true _ hEval => exact hEval
  have hqmNonneg : 0 ≤ qm := by
    have hEvalMTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt m)) =
          __smtx_typeof (__eo_to_smt m) := by
      exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt m)
        (by simp [term_has_non_none_type, hMInt])
    rcases int_value_canonical (by simpa [hMInt] using hEvalMTy) with ⟨zm, hEvalM⟩
    have hDenEq : native_to_real zm = qm := by
      have h :
          SmtValue.Rational (native_to_real zm) = SmtValue.Rational qm := by
        simpa [arith_atom_denote_real, hEvalM, __smtx_model_eval_to_real] using hMDen
      simpa using h
    have hZle : native_zleq 0 zm = true := by
      have hZeroEval :
          __smtx_model_eval M (SmtTerm.Numeral 0) = SmtValue.Numeral 0 := by
        rw [__smtx_model_eval.eq_2]
      rw [show
          __eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) =
            SmtTerm.geq (__eo_to_smt m) (SmtTerm.Numeral 0) by rfl] at hMEval
      rw [__smtx_model_eval.eq_18, hEvalM, hZeroEval] at hMEval
      simpa [__smtx_model_eval_geq, __smtx_model_eval_leq] using hMEval
    have hzmNonneg : (0 : Int) ≤ zm := by
      simpa [native_zleq, SmtEval.native_zleq] using hZle
    have hqm' : (0 : Rat) ≤ native_to_real zm := by
      dsimp [native_to_real, native_mk_rational]
      rw [rat_div_one_intCast zm]
      exact_mod_cast hzmNonneg
    simpa [hDenEq] using hqm'
  have hOrder :=
    (str_arith_entail_is_approx_int_denote_order M hM n m (Term.Boolean true) qn qm
      hNInt hMInt hApprox hNDen hMDen).1 rfl
  have hqnNonneg : 0 ≤ qn := by
    calc
      (0 : Rat) ≤ qm := hqmNonneg
      _ ≤ qn := hOrder
  have hNEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0))) =
        SmtValue.Boolean true :=
    geq_zero_eval_true_of_int_denote_nonneg M hM n qn hNInt hNDen hqnNonneg
  exact RuleProofs.eo_interprets_of_bool_eval M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)) true hNBool hNEval

theorem arith_string_pred_entail_formula_true
    (M : SmtModel) (hM : model_total_typed M) (n : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
        (Term.Boolean true)) ->
  __str_arith_entail_simple_rec (__get_arith_poly_norm n) = Term.Boolean true ->
  eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
        (Term.Boolean true)) true := by
  intro hEqBool hSimple
  let geqTerm := Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)
  have hGeqBool : RuleProofs.eo_has_bool_type geqTerm := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        geqTerm (Term.Boolean true) (by simpa [geqTerm] using hEqBool) with
      ⟨hTy, _hNonNone⟩
    unfold RuleProofs.eo_has_bool_type
    rw [hTy]
    rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
    rw [__smtx_typeof.eq_1]
  have hNInt : __smtx_typeof (__eo_to_smt n) = SmtType.Int :=
    geq_left_int_type_of_has_bool_type n hGeqBool
  have hDenote :
      arith_poly_denote_real M (__get_arith_poly_norm n) =
        arith_atom_denote_real M n :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type
      M hM n (Or.inl hNInt)
  rcases arith_atom_denote_real_rational_of_smt_arith_type
      M hM n (Or.inl hNInt) with
    ⟨q, hAtomDenote⟩
  have hPolyDenote :
      arith_poly_denote_real M (__get_arith_poly_norm n) =
        SmtValue.Rational q := by
    rw [hDenote, hAtomDenote]
  have hqNonneg : 0 ≤ q :=
    str_arith_entail_simple_rec_denote_nonneg
      M (__get_arith_poly_norm n) q hSimple hPolyDenote
  have hGeqEval :
      __smtx_model_eval M (__eo_to_smt geqTerm) = SmtValue.Boolean true := by
    simpa [geqTerm] using
      geq_zero_eval_true_of_int_denote_nonneg M hM n q hNInt hAtomDenote hqNonneg
  apply RuleProofs.eo_interprets_eq_of_rel M geqTerm (Term.Boolean true)
    (by simpa [geqTerm] using hEqBool)
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [hGeqEval]
  rw [show __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true by rfl]
  rw [__smtx_model_eval.eq_1]
  simp [__smtx_model_eval_eq, native_veq]

theorem arith_string_pred_safe_approx_formula_true
    (M : SmtModel) (hM : model_total_typed M) (n m : Term) :
  RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0))) ->
  __str_arith_entail_is_approx n m (Term.Boolean true) = Term.Boolean true ->
  __str_arith_entail_simple_pred
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)) =
    Term.Boolean true ->
  eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0))) true := by
  intro hFormulaBool hApprox hSimple
  let geqN := Term.Apply (Term.Apply (Term.UOp UserOp.geq) n) (Term.Numeral 0)
  let geqM := Term.Apply (Term.Apply (Term.UOp UserOp.geq) m) (Term.Numeral 0)
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type geqN geqM
      (by simpa [geqN, geqM] using hFormulaBool) with
    ⟨hSameTy, hGeqNNN⟩
  have hGeqMNN : __smtx_typeof (__eo_to_smt geqM) ≠ SmtType.None := by
    rw [← hSameTy]
    exact hGeqNNN
  have hGeqNBool : RuleProofs.eo_has_bool_type geqN := by
    exact geq_has_bool_type_of_non_none n (Term.Numeral 0)
      (by simpa [geqN] using hGeqNNN)
  have hGeqMBool : RuleProofs.eo_has_bool_type geqM := by
    exact geq_has_bool_type_of_non_none m (Term.Numeral 0)
      (by simpa [geqM] using hGeqMNN)
  have hNTrue : eo_interprets M geqN true := by
    simpa [geqN, geqM] using
      arith_string_pred_safe_approx_left_true M hM n m hGeqNBool hGeqMBool
        hApprox hSimple
  have hMTrue : eo_interprets M geqM true := by
    simpa [geqM] using
      arith_string_pred_simple_geq_true M hM m (Term.Numeral 0) hGeqMBool hSimple
  have hEvalN :
      __smtx_model_eval M (__eo_to_smt geqN) = SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M geqN true).mp hNTrue with
    | intro_true _ hEval => exact hEval
  have hEvalM :
      __smtx_model_eval M (__eo_to_smt geqM) = SmtValue.Boolean true := by
    cases (RuleProofs.eo_interprets_iff_smt_interprets M geqM true).mp hMTrue with
    | intro_true _ hEval => exact hEval
  apply RuleProofs.eo_interprets_eq_of_rel M geqN geqM
    (by simpa [geqN, geqM] using hFormulaBool)
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [hEvalN, hEvalM]
  simp [__smtx_model_eval_eq, native_veq]

private theorem smt_value_rel_of_eq_arith_atom_denote_real_of_smt_arith_type
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∨
    __smtx_typeof (__eo_to_smt a) = SmtType.Real) ->
  arith_atom_denote_real M a = arith_atom_denote_real M b ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hEqTrans hArithTy hAtomEq
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation a b hEqTrans with ⟨hTy, hNonNoneA⟩
  have hNonNoneB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
    rw [← hTy]
    exact hNonNoneA
  have hEvalATy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) =
        __smtx_typeof (__eo_to_smt a) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt a)
      (by simpa [term_has_non_none_type] using hNonNoneA)
  have hEvalBTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt b) := by
    exact Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt b)
      (by simpa [term_has_non_none_type] using hNonNoneB)
  rcases hArithTy with hAInt | hAReal
  · have hBInt : __smtx_typeof (__eo_to_smt b) = SmtType.Int := by
      exact hTy.symm.trans hAInt
    have hEvalAInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) = SmtType.Int := by
      simpa [hAInt] using hEvalATy
    have hEvalBInt :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) = SmtType.Int := by
      simpa [hBInt] using hEvalBTy
    rcases int_value_canonical hEvalAInt with ⟨nA, hEvalA⟩
    rcases int_value_canonical hEvalBInt with ⟨nB, hEvalB⟩
    have hToRealEq :
        __smtx_model_eval_to_real (SmtValue.Numeral nA) =
          __smtx_model_eval_to_real (SmtValue.Numeral nB) := by
      simpa [arith_atom_denote_real, hEvalA, hEvalB] using hAtomEq
    have hValEq : SmtValue.Numeral nA = SmtValue.Numeral nB := by
      simpa [smtx_model_eval_to_int_to_real_of_numeral] using
        congrArg __smtx_model_eval_to_int hToRealEq
    cases hValEq
    simpa [hEvalA, hEvalB] using RuleProofs.smt_value_rel_refl (SmtValue.Numeral nA)
  · have hBReal : __smtx_typeof (__eo_to_smt b) = SmtType.Real := by
      exact hTy.symm.trans hAReal
    have hEvalAReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt a)) = SmtType.Real := by
      simpa [hAReal] using hEvalATy
    have hEvalBReal :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt b)) = SmtType.Real := by
      simpa [hBReal] using hEvalBTy
    rcases real_value_canonical hEvalAReal with ⟨qA, hEvalA⟩
    rcases real_value_canonical hEvalBReal with ⟨qB, hEvalB⟩
    have hToRealEq :
        __smtx_model_eval_to_real (SmtValue.Rational qA) =
          __smtx_model_eval_to_real (SmtValue.Rational qB) := by
      simpa [arith_atom_denote_real, hEvalA, hEvalB] using hAtomEq
    have hValEq : SmtValue.Rational qA = SmtValue.Rational qB := by
      simpa [__smtx_model_eval_to_real] using hToRealEq
    cases hValEq
    simpa [hEvalA, hEvalB] using RuleProofs.smt_value_rel_refl (SmtValue.Rational qA)

private theorem smt_value_rel_of_equal_arith_poly_norm_of_smt_arith_type
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  (__smtx_typeof (__eo_to_smt a) = SmtType.Int ∨
    __smtx_typeof (__eo_to_smt a) = SmtType.Real) ->
  __get_arith_poly_norm a = __get_arith_poly_norm b ->
  __get_arith_poly_norm a ≠ Term.Stuck ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hEqTrans hArithTy hNormEq _hNormNotStuck
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation a b hEqTrans with ⟨hTy, _hNonNoneA⟩
  have hBArithTy :
      __smtx_typeof (__eo_to_smt b) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt b) = SmtType.Real := by
    rcases hArithTy with hAInt | hAReal
    · exact Or.inl (hTy.symm.trans hAInt)
    · exact Or.inr (hTy.symm.trans hAReal)
  have hDenoteA :
      arith_poly_denote_real M (__get_arith_poly_norm a) = arith_atom_denote_real M a :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type M hM a hArithTy
  have hDenoteB :
      arith_poly_denote_real M (__get_arith_poly_norm b) = arith_atom_denote_real M b :=
    arith_poly_denote_real_of_get_arith_poly_norm_of_smt_arith_type M hM b hBArithTy
  have hAtomEq : arith_atom_denote_real M a = arith_atom_denote_real M b := by
    calc
      arith_atom_denote_real M a =
          arith_poly_denote_real M (__get_arith_poly_norm a) := hDenoteA.symm
      _ = arith_poly_denote_real M (__get_arith_poly_norm b) := by rw [hNormEq]
      _ = arith_atom_denote_real M b := hDenoteB
  exact smt_value_rel_of_eq_arith_atom_denote_real_of_smt_arith_type
    M hM a b hEqTrans hArithTy hAtomEq

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
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation a b hEqTrans with
    ⟨hTy, hNonNone⟩
  by_cases hInt : __smtx_typeof (__eo_to_smt a) = SmtType.Int
  · exact smt_value_rel_of_equal_arith_poly_norm_of_smt_arith_type
      M hM a b hEqTrans (Or.inl hInt) hNormEq _hNormNotStuck
  · by_cases hReal : __smtx_typeof (__eo_to_smt a) = SmtType.Real
    · exact smt_value_rel_of_equal_arith_poly_norm_of_smt_arith_type
        M hM a b hEqTrans (Or.inr hReal) hNormEq _hNormNotStuck
    · have hNotIntB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.Int := by
        intro hIntB
        exact hInt (hTy.trans hIntB)
      have hNotRealB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.Real := by
        intro hRealB
        exact hReal (hTy.trans hRealB)
      have hNormA :
          __get_arith_poly_norm a = arith_atomic_poly a :=
        get_arith_poly_norm_of_non_arith_smt_type a hInt hReal hNonNone
      have hNormB :
          __get_arith_poly_norm b = arith_atomic_poly b := by
        have hNonNoneB : __smtx_typeof (__eo_to_smt b) ≠ SmtType.None := by
          rw [← hTy]
          exact hNonNone
        exact get_arith_poly_norm_of_non_arith_smt_type b hNotIntB hNotRealB hNonNoneB
      have hEqTerms : a = b := by
        apply arith_atomic_poly_injective
        rw [← hNormA, ← hNormB]
        exact hNormEq
      subst a
      exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt b))

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
