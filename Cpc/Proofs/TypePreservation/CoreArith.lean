import Cpc.Proofs.TypePreservation.Datatypes

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

/-- Rewrites the typing equation for `ite`. -/
theorem typeof_ite_eq
    (c t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.ite c t1 t2) =
      __smtx_typeof_ite (__smtx_typeof c) (__smtx_typeof t1) (__smtx_typeof t2) := by
  simpa using (__smtx_typeof.eq_def (SmtTerm.ite c t1 t2))

/-- Rewrites the typing equation for `select`. -/
theorem typeof_select_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.select t1 t2) =
      __smtx_typeof_select (__smtx_typeof t1) (__smtx_typeof t2) := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.select t1 t2))

/-- Rewrites the typing equation for `store`. -/
theorem typeof_store_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (theory3 SmtTheoryOp.store t1 t2 t3) =
      __smtx_typeof_store (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3) := by
  simpa [theory3, theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory3 SmtTheoryOp.store t1 t2 t3))

/-- Rewrites the typing equation for `eq`. -/
theorem typeof_eq_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.eq t1 t2) =
      __smtx_typeof_eq (__smtx_typeof t1) (__smtx_typeof t2) := by
  simpa using (__smtx_typeof.eq_def (SmtTerm.eq t1 t2))

theorem typeof_not_eq (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.not t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None := by
  simpa [theory1, theory0] using (__smtx_typeof.eq_def (theory1 SmtTheoryOp.not t))

theorem typeof_or_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.or t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.or t1 t2))

theorem typeof_and_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.and t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.and t1 t2))

theorem typeof_imp_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.imp t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.imp t1 t2))

theorem typeof_xor_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.xor t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.xor t1 t2))

theorem typeof_plus_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.plus t1 t2) =
      __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.plus t1 t2))

theorem typeof_neg_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.neg t1 t2) =
      __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.neg t1 t2))

theorem typeof_mult_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.mult t1 t2) =
      __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2) := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.mult t1 t2))

theorem typeof_lt_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.lt t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.lt t1 t2))

theorem typeof_leq_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.leq t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.leq t1 t2))

theorem typeof_gt_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.gt t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.gt t1 t2))

theorem typeof_geq_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.geq t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.geq t1 t2))

theorem typeof_to_real_eq (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.to_real t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Int) SmtType.Real
        (native_ite (native_Teq (__smtx_typeof t) SmtType.Real) SmtType.Real SmtType.None) := by
  simpa [theory1, theory0] using (__smtx_typeof.eq_def (theory1 SmtTheoryOp.to_real t))

theorem typeof_to_int_eq (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.to_int t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Real) SmtType.Int SmtType.None := by
  simpa [theory1, theory0] using (__smtx_typeof.eq_def (theory1 SmtTheoryOp.to_int t))

theorem typeof_is_int_eq (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.is_int t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Real) SmtType.Bool SmtType.None := by
  simpa [theory1, theory0] using (__smtx_typeof.eq_def (theory1 SmtTheoryOp.is_int t))

theorem typeof_abs_eq (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.abs t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Int) SmtType.Int SmtType.None := by
  simpa [theory1, theory0] using (__smtx_typeof.eq_def (theory1 SmtTheoryOp.abs t))

theorem typeof_uneg_eq (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.uneg t) =
      __smtx_typeof_arith_overload_op_1 (__smtx_typeof t) := by
  simpa [theory1, theory0] using (__smtx_typeof.eq_def (theory1 SmtTheoryOp.uneg t))

theorem typeof_div_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.div t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.div t1 t2))

theorem typeof_mod_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.mod t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.mod t1 t2))

theorem typeof_multmult_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.multmult t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.multmult t1 t2))

theorem typeof_divisible_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.divisible t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Bool SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.divisible t1 t2))

theorem typeof_int_pow2_eq (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.int_pow2 t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Int) SmtType.Int SmtType.None := by
  simpa [theory1, theory0] using (__smtx_typeof.eq_def (theory1 SmtTheoryOp.int_pow2 t))

theorem typeof_int_log2_eq (t : SmtTerm) :
    __smtx_typeof (theory1 SmtTheoryOp.int_log2 t) =
      native_ite (native_Teq (__smtx_typeof t) SmtType.Int) SmtType.Int SmtType.None := by
  simpa [theory1, theory0] using (__smtx_typeof.eq_def (theory1 SmtTheoryOp.int_log2 t))

theorem typeof_div_total_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.div_total t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.div_total t1 t2))

theorem typeof_mod_total_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.mod_total t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.mod_total t1 t2))

theorem typeof_multmult_total_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.multmult_total t1 t2) =
      native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
        (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) SmtType.Int SmtType.None)
        SmtType.None := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.multmult_total t1 t2))

theorem typeof_qdiv_total_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.qdiv_total t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Real := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.qdiv_total t1 t2))

theorem typeof_qdiv_eq (t1 t2 : SmtTerm) :
    __smtx_typeof (theory2 SmtTheoryOp.qdiv t1 t2) =
      __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Real := by
  simpa [theory2, theory1, theory0] using
    (__smtx_typeof.eq_def (theory2 SmtTheoryOp.qdiv t1 t2))

/-- Derives `ite_args` from `non_none`. -/
theorem ite_args_of_non_none
    {c t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.ite c t1 t2)) :
    ∃ T : SmtType,
      __smtx_typeof c = SmtType.Bool ∧
        __smtx_typeof t1 = T ∧
        __smtx_typeof t2 = T ∧
        T ≠ SmtType.None := by
  unfold term_has_non_none_type at ht
  rw [typeof_ite_eq] at ht
  let T1 := __smtx_typeof t1
  let T2 := __smtx_typeof t2
  have hBool : __smtx_typeof c = SmtType.Bool := by
    cases hc : __smtx_typeof c <;>
      simp [__smtx_typeof_ite, native_ite, hc, T1, T2] at ht
    simp
  by_cases hEq : native_Teq T1 T2 = true
  · have hT : T1 = T2 := by
      simpa [native_Teq] using hEq
    have hNN : T1 ≠ SmtType.None := by
      simpa [__smtx_typeof_ite, native_ite, hBool, T1, T2, hEq] using ht
    exact ⟨T1, hBool, rfl, by simpa [T1, T2] using hT.symm, hNN⟩
  · exfalso
    apply ht
    simp [__smtx_typeof_ite, native_ite, hBool, T1, T2, hEq]

/-- Shows that evaluating `ite` terms produces values of the expected type. -/
theorem typeof_value_model_eval_ite
    (M : SmtModel)
    (c t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.ite c t1 t2))
    (hpresc : __smtx_typeof_value (__smtx_model_eval M c) = __smtx_typeof c)
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.ite c t1 t2)) =
      __smtx_typeof (SmtTerm.ite c t1 t2) := by
  rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
  rw [show __smtx_typeof
      (SmtTerm.ite c t1 t2) = T by
    rw [typeof_ite_eq]
    simp [__smtx_typeof_ite, native_ite, native_Teq, hc, h1, h2]]
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_ite (__smtx_model_eval M c) (__smtx_model_eval M t1)
        (__smtx_model_eval M t2)) = T
  rcases bool_value_canonical (by simpa [hc] using hpresc) with ⟨b, hb⟩
  rw [hb]
  cases b
  · simpa [__smtx_model_eval_ite, __smtx_typeof_value, h1, h2] using hpres2
  · simpa [__smtx_model_eval_ite, __smtx_typeof_value, h1, h2] using hpres1

/-- Derives `select_args` from `non_none`. -/
theorem select_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.select t1 t2)) :
    ∃ A B : SmtType,
      __smtx_typeof t1 = SmtType.Map A B ∧
        __smtx_typeof t2 = A := by
  unfold term_has_non_none_type at ht
  rw [typeof_select_eq] at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      by_cases hEq : native_Teq A (__smtx_typeof t2)
      · have h2' : A = __smtx_typeof t2 := by
          simpa [native_Teq] using hEq
        exact ⟨A, B, rfl, h2'.symm⟩
      · exfalso
        exact ht (by simp [__smtx_typeof_select, native_ite, h1, hEq])
  | _ =>
      exfalso
      exact ht (by simp [__smtx_typeof_select, h1])

/-- Derives `store_args` from `non_none`. -/
theorem store_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type
      (theory3 SmtTheoryOp.store t1 t2 t3)) :
    ∃ A B : SmtType,
      __smtx_typeof t1 = SmtType.Map A B ∧
        __smtx_typeof t2 = A ∧
        __smtx_typeof t3 = B := by
  unfold term_has_non_none_type at ht
  rw [typeof_store_eq] at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      by_cases hEq1 : native_Teq A (__smtx_typeof t2)
      · by_cases hEq2 : native_Teq B (__smtx_typeof t3)
        · have h2' : A = __smtx_typeof t2 := by
            simpa [native_Teq] using hEq1
          have h3' : B = __smtx_typeof t3 := by
            simpa [native_Teq] using hEq2
          exact ⟨A, B, rfl, h2'.symm, h3'.symm⟩
        · exfalso
          exact ht (by
            simp [__smtx_typeof_store, native_ite, h1, hEq1, hEq2])
      · exfalso
        exact ht (by
          simp [__smtx_typeof_store, native_ite, h1, hEq1])
  | _ =>
      exfalso
      exact ht (by simp [__smtx_typeof_store, h1])

/-- Shows that evaluating `select` terms produces values of the expected type. -/
theorem typeof_value_model_eval_select
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.select t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.select t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.select t1 t2) := by
  rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
  rw [show __smtx_typeof (theory2 SmtTheoryOp.select t1 t2) = B by
    rw [typeof_select_eq]
    simp [__smtx_typeof_select, native_ite, native_Teq, h1, h2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.select) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_select (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = B
  rcases map_value_canonical (A := A) (B := B) (by simpa [h1] using hpres1) with ⟨m, hm⟩
  rw [hm]
  simpa [__smtx_model_eval_select, __smtx_map_select] using
    map_lookup_typed (m := m) (A := A) (B := B) (i := __smtx_model_eval M t2)
      (by simpa [hm, h1] using hpres1)
      (by simpa [h2] using hpres2)

/-- Shows that evaluating `store` terms produces values of the expected type. -/
theorem typeof_value_model_eval_store
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht : term_has_non_none_type
      (theory3 SmtTheoryOp.store t1 t2 t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (theory3 SmtTheoryOp.store t1 t2 t3)) =
      __smtx_typeof (theory3 SmtTheoryOp.store t1 t2 t3) := by
  rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
  rw [show __smtx_typeof
      (theory3 SmtTheoryOp.store t1 t2 t3) =
        SmtType.Map A B by
    rw [typeof_store_eq]
    simp [__smtx_typeof_store, native_ite, native_Teq, h1, h2, h3]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.store) t1) t2) t3)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_store (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Map A B
  rcases map_value_canonical (A := A) (B := B) (by simpa [h1] using hpres1) with ⟨m, hm⟩
  rw [hm]
  have hMap : __smtx_typeof_map_value m = SmtType.Map A B := by
    simpa [hm, h1, __smtx_typeof_value] using hpres1
  have hi : __smtx_typeof_value (__smtx_model_eval M t2) = A := by
    simpa [h2] using hpres2
  have he : __smtx_typeof_value (__smtx_model_eval M t3) = B := by
    simpa [h3] using hpres3
  simp [__smtx_model_eval_store, __smtx_map_store, __smtx_typeof_value,
    __smtx_typeof_map_value, hMap, hi, he, native_ite, native_Teq]

/-- Derives `eq_term_typeof` from `non_none`. -/
theorem eq_term_typeof_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    __smtx_typeof (SmtTerm.eq t1 t2) = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  rw [typeof_eq_eq] at ht
  rw [typeof_eq_eq]
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, h1, h2] at ht ⊢
  all_goals
    first | exact ht

/-- Shows that evaluating `not` terms produces values of the expected type. -/
theorem typeof_value_model_eval_not
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (theory1 SmtTheoryOp.not t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (theory1 SmtTheoryOp.not t)) =
      __smtx_typeof (theory1 SmtTheoryOp.not t) := by
  have hArg : __smtx_typeof t = SmtType.Bool := by
    unfold term_has_non_none_type at ht
    rw [typeof_not_eq] at ht
    cases h : __smtx_typeof t <;>
      simp [native_ite, native_Teq, h] at ht
    simp
  rw [show __smtx_typeof (theory1 SmtTheoryOp.not t) = SmtType.Bool by
    rw [typeof_not_eq]
    simp [native_ite, native_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.not) t)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value (__smtx_model_eval_not (__smtx_model_eval M t)) = SmtType.Bool
  rcases bool_value_canonical (by simpa [hArg] using hpres) with ⟨b, hb⟩
  rw [hb]
  simp [__smtx_model_eval_not, __smtx_typeof_value]

/-- Shows that evaluating `or` terms produces values of the expected type. -/
theorem typeof_value_model_eval_or
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.or t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.or t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.or t1 t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := theory2 SmtTheoryOp.or) (typeof_or_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.or t1 t2) = SmtType.Bool by
    rw [typeof_or_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.or) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_or (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_or, __smtx_typeof_value]

/-- Shows that evaluating `and` terms produces values of the expected type. -/
theorem typeof_value_model_eval_and
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.and t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.and t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.and t1 t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := theory2 SmtTheoryOp.and) (typeof_and_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.and t1 t2) = SmtType.Bool by
    rw [typeof_and_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_and (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_and, __smtx_typeof_value]

/-- Shows that evaluating `imp` terms produces values of the expected type. -/
theorem typeof_value_model_eval_imp
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.imp t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.imp t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.imp t1 t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := theory2 SmtTheoryOp.imp) (typeof_imp_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.imp t1 t2) = SmtType.Bool by
    rw [typeof_imp_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_imp (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not, __smtx_typeof_value]

/-- Shows that evaluating `eq` terms produces values of the expected type. -/
theorem typeof_value_model_eval_eq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.eq t1 t2)) =
      __smtx_typeof (SmtTerm.eq t1 t2) := by
  rw [eq_term_typeof_of_non_none ht]
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_eq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
  simpa using typeof_value_model_eval_eq_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

/-- Shows that evaluating `xor` terms produces values of the expected type. -/
theorem typeof_value_model_eval_xor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.xor t1 t2)) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.xor t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.xor t1 t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := theory2 SmtTheoryOp.xor) (typeof_xor_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.xor t1 t2) = SmtType.Bool by
    rw [typeof_xor_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.xor) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_xor (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
  simpa using typeof_value_model_eval_xor_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

/-- Shows that evaluating `plus` terms produces values of the expected type. -/
theorem typeof_value_model_eval_plus
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.plus t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.plus t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.plus t1 t2) := by
  rcases arith_binop_args_of_non_none (op := theory2 SmtTheoryOp.plus) (typeof_plus_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.plus t1 t2) = SmtType.Int by
      rw [typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.plus) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_plus (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.plus t1 t2) = SmtType.Real by
      rw [typeof_plus_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.plus) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_plus (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `neg` terms produces values of the expected type. -/
theorem typeof_value_model_eval_neg
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.neg t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.neg t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.neg t1 t2) := by
  rcases arith_binop_args_of_non_none (op := theory2 SmtTheoryOp.neg) (typeof_neg_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.neg t1 t2) = SmtType.Int by
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.neg) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval__ (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.neg t1 t2) = SmtType.Real by
      rw [typeof_neg_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.neg) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval__ (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `mult` terms produces values of the expected type. -/
theorem typeof_value_model_eval_mult
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.mult t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.mult t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.mult t1 t2) := by
  rcases arith_binop_args_of_non_none (op := theory2 SmtTheoryOp.mult) (typeof_mult_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.mult t1 t2) = SmtType.Int by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mult) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_mult (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.mult t1 t2) = SmtType.Real by
      rw [typeof_mult_eq]
      simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mult) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_mult (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `lt` terms produces values of the expected type. -/
theorem typeof_value_model_eval_lt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.lt t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.lt t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.lt t1 t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := theory2 SmtTheoryOp.lt) (typeof_lt_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.lt t1 t2) = SmtType.Bool by
      rw [typeof_lt_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.lt) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_lt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.lt t1 t2) = SmtType.Bool by
      rw [typeof_lt_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.lt) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_lt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `leq` terms produces values of the expected type. -/
theorem typeof_value_model_eval_leq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.leq t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.leq t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.leq t1 t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := theory2 SmtTheoryOp.leq) (typeof_leq_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.leq t1 t2) = SmtType.Bool by
      rw [typeof_leq_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.leq) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_leq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.leq t1 t2) = SmtType.Bool by
      rw [typeof_leq_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.leq) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_leq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `gt` terms produces values of the expected type. -/
theorem typeof_value_model_eval_gt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.gt t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.gt t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.gt t1 t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := theory2 SmtTheoryOp.gt) (typeof_gt_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.gt t1 t2) = SmtType.Bool by
      rw [typeof_gt_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.gt) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_gt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.gt t1 t2) = SmtType.Bool by
      rw [typeof_gt_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.gt) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_gt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `geq` terms produces values of the expected type. -/
theorem typeof_value_model_eval_geq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.geq t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (theory2 SmtTheoryOp.geq t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.geq t1 t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := theory2 SmtTheoryOp.geq) (typeof_geq_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.geq t1 t2) = SmtType.Bool by
      rw [typeof_geq_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.geq) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_geq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.geq t1 t2) = SmtType.Bool by
      rw [typeof_geq_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.geq) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_geq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `to_real` terms produces values of the expected type. -/
theorem typeof_value_model_eval_to_real
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (theory1 SmtTheoryOp.to_real t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (theory1 SmtTheoryOp.to_real t)) =
      __smtx_typeof (theory1 SmtTheoryOp.to_real t) := by
  rcases to_real_arg_of_non_none ht with hArg | hArg
  · rw [show __smtx_typeof (theory1 SmtTheoryOp.to_real t) = SmtType.Real by
      rw [typeof_to_real_eq]
      simp [native_ite, native_Teq, hArg]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.to_real) t)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value (__smtx_model_eval_to_real (__smtx_model_eval M t)) = SmtType.Real
    rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
    rw [hn]
    rfl
  · rw [show __smtx_typeof (theory1 SmtTheoryOp.to_real t) = SmtType.Real by
      rw [typeof_to_real_eq]
      simp [native_ite, native_Teq, hArg]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.to_real) t)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value (__smtx_model_eval_to_real (__smtx_model_eval M t)) = SmtType.Real
    rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
    rw [hq]
    rfl

/-- Shows that evaluating `to_int` terms produces values of the expected type. -/
theorem typeof_value_model_eval_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (theory1 SmtTheoryOp.to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (theory1 SmtTheoryOp.to_int t)) =
      __smtx_typeof (theory1 SmtTheoryOp.to_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := theory1 SmtTheoryOp.to_int) (typeof_to_int_eq t) ht
  rw [show __smtx_typeof (theory1 SmtTheoryOp.to_int t) = SmtType.Int by
    rw [typeof_to_int_eq]
    simp [native_ite, native_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.to_int) t)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value (__smtx_model_eval_to_int (__smtx_model_eval M t)) = SmtType.Int
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  rfl

/-- Shows that evaluating `is_int` terms produces values of the expected type. -/
theorem typeof_value_model_eval_is_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (theory1 SmtTheoryOp.is_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (theory1 SmtTheoryOp.is_int t)) =
      __smtx_typeof (theory1 SmtTheoryOp.is_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := theory1 SmtTheoryOp.is_int) (typeof_is_int_eq t) ht
  rw [show __smtx_typeof (theory1 SmtTheoryOp.is_int t) = SmtType.Bool by
    rw [typeof_is_int_eq]
    simp [native_ite, native_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.is_int) t)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value (__smtx_model_eval_is_int (__smtx_model_eval M t)) = SmtType.Bool
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  simpa [__smtx_model_eval_is_int, __smtx_model_eval_to_int, __smtx_model_eval_to_real] using
    typeof_value_model_eval_eq_value
      (SmtValue.Rational (native_to_real (native_to_int q))) (SmtValue.Rational q)

/-- Shows that evaluating `abs` terms produces values of the expected type. -/
theorem typeof_value_model_eval_abs
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (theory1 SmtTheoryOp.abs t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (theory1 SmtTheoryOp.abs t)) =
      __smtx_typeof (theory1 SmtTheoryOp.abs t) := by
  have hArg : __smtx_typeof t = SmtType.Int := int_arg_of_non_none ht
  rw [show __smtx_typeof (theory1 SmtTheoryOp.abs t) = SmtType.Int by
    rw [typeof_abs_eq]
    simp [native_ite, native_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.abs) t)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value (__smtx_model_eval_abs (__smtx_model_eval M t)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  cases hlt : native_zlt n 0 <;>
    simp [__smtx_model_eval_abs, __smtx_model_eval_lt, __smtx_model_eval_ite,
      __smtx_model_eval__, __smtx_typeof_value, hlt]

/-- Shows that evaluating `uneg` terms produces values of the expected type. -/
theorem typeof_value_model_eval_uneg
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (theory1 SmtTheoryOp.uneg t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (theory1 SmtTheoryOp.uneg t)) =
      __smtx_typeof (theory1 SmtTheoryOp.uneg t) := by
  rcases arith_unop_arg_of_non_none (op := theory1 SmtTheoryOp.uneg) (typeof_uneg_eq t) ht with hArg | hArg
  · rw [show __smtx_typeof (theory1 SmtTheoryOp.uneg t) = SmtType.Int by
      rw [typeof_uneg_eq]
      simp [__smtx_typeof_arith_overload_op_1, hArg]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.uneg) t)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value (__smtx_model_eval_uneg (__smtx_model_eval M t)) = SmtType.Int
    rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
    rw [hn]
    rfl
  · rw [show __smtx_typeof (theory1 SmtTheoryOp.uneg t) = SmtType.Real by
      rw [typeof_uneg_eq]
      simp [__smtx_typeof_arith_overload_op_1, hArg]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.uneg) t)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value (__smtx_model_eval_uneg (__smtx_model_eval M t)) = SmtType.Real
    rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
    rw [hq]
    rfl

/-- Derives `int_ret_arg` from `non_none`. -/
theorem int_ret_arg_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Int) R SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, native_ite, native_Teq, h] at ht
  simp

/-- Derives `int_binop_args` from `non_none`. -/
theorem int_binop_args_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) R SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    __smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, native_ite, native_Teq, h1, h2] at ht
  simp

/-- Shows that evaluating `apply_lookup_fun` terms produces values of the expected type. -/
theorem typeof_value_model_eval_apply_lookup_fun
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (A B : SmtType)
    (hA : A ≠ SmtType.None)
    (hB : type_inhabited B)
    (i : SmtValue)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value
        (__smtx_model_eval_apply (__smtx_model_lookup M s (SmtType.FunType A B)) i) = B := by
  have hLookup :
      __smtx_typeof_value (__smtx_model_lookup M s (SmtType.FunType A B)) =
        SmtType.FunType A B :=
    model_total_typed_lookup hM s (SmtType.FunType A B) (type_inhabited_fun hB)
  exact typeof_value_model_eval_apply_dt hA (Or.inl hLookup) hi

/-- Shows that evaluating `div_total` terms produces values of the expected type. -/
theorem typeof_value_model_eval_div_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.div_total t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (theory2 SmtTheoryOp.div_total t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.div_total t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.div_total) (typeof_div_total_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.div_total t1 t2) = SmtType.Int by
    rw [typeof_div_total_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.div_total) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_div_total (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  rfl

/-- Shows that evaluating `mod_total` terms produces values of the expected type. -/
theorem typeof_value_model_eval_mod_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.mod_total t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (theory2 SmtTheoryOp.mod_total t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.mod_total t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.mod_total) (typeof_mod_total_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.mod_total t1 t2) = SmtType.Int by
    rw [typeof_mod_total_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mod_total) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_mod_total (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  rfl

/-- Shows that evaluating `multmult_total` terms produces values of the expected type. -/
theorem typeof_value_model_eval_multmult_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.multmult_total t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (theory2 SmtTheoryOp.multmult_total t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.multmult_total t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.multmult_total) (typeof_multmult_total_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.multmult_total t1 t2) =
      SmtType.Int by
    rw [typeof_multmult_total_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.multmult_total) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_multmult_total (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  rfl

/-- Shows that evaluating `divisible` terms produces values of the expected type. -/
theorem typeof_value_model_eval_divisible
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.divisible t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (theory2 SmtTheoryOp.divisible t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.divisible t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.divisible) (typeof_divisible_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.divisible t1 t2) = SmtType.Bool by
    rw [typeof_divisible_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.divisible) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_divisible (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  simpa [__smtx_model_eval_divisible, __smtx_model_eval_mod_total] using
    typeof_value_model_eval_eq_value
      (SmtValue.Numeral (native_mod_total n2 n1))
      (SmtValue.Numeral 0)

/-- Shows that evaluating `int_pow2` terms produces values of the expected type. -/
theorem typeof_value_model_eval_int_pow2
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (theory1 SmtTheoryOp.int_pow2 t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (theory1 SmtTheoryOp.int_pow2 t)) =
      __smtx_typeof (theory1 SmtTheoryOp.int_pow2 t) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_ret_arg_of_non_none (op := theory1 SmtTheoryOp.int_pow2) (typeof_int_pow2_eq t) ht
  rw [show __smtx_typeof (theory1 SmtTheoryOp.int_pow2 t) = SmtType.Int by
    rw [typeof_int_pow2_eq]
    simp [native_ite, native_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.int_pow2) t)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value (__smtx_model_eval_int_pow2 (__smtx_model_eval M t)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  rfl

/-- Shows that evaluating `int_log2` terms produces values of the expected type. -/
theorem typeof_value_model_eval_int_log2
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (theory1 SmtTheoryOp.int_log2 t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (theory1 SmtTheoryOp.int_log2 t)) =
      __smtx_typeof (theory1 SmtTheoryOp.int_log2 t) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_ret_arg_of_non_none (op := theory1 SmtTheoryOp.int_log2) (typeof_int_log2_eq t) ht
  rw [show __smtx_typeof (theory1 SmtTheoryOp.int_log2 t) = SmtType.Int by
    rw [typeof_int_log2_eq]
    simp [native_ite, native_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.int_log2) t)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value (__smtx_model_eval_int_log2 (__smtx_model_eval M t)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  rfl

/-- Shows that evaluating `div` terms produces values of the expected type. -/
theorem typeof_value_model_eval_div
    (M : SmtModel)
    (hM : model_total_typed M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.div t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (theory2 SmtTheoryOp.div t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.div t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.div) (typeof_div_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.div t1 t2) = SmtType.Int by
    rw [typeof_div_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.div) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_ite
        (__smtx_model_eval_eq (__smtx_model_eval M t2) (SmtValue.Numeral 0))
        (__smtx_model_eval_apply
          (__smtx_model_lookup M native_div_by_zero_id (SmtType.FunType SmtType.Int SmtType.Int))
          (__smtx_model_eval M t1))
        (__smtx_model_eval_div_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))) =
    SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  by_cases hZero : n2 = 0
  · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_div_total,
      native_veq, hZero] using
      typeof_value_model_eval_apply_lookup_fun M hM
        native_div_by_zero_id SmtType.Int SmtType.Int (by simp) type_inhabited_int
        (SmtValue.Numeral n1) rfl
  · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_div_total,
      __smtx_typeof_value, native_veq, hZero]

/-- Shows that evaluating `mod` terms produces values of the expected type. -/
theorem typeof_value_model_eval_mod
    (M : SmtModel)
    (hM : model_total_typed M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.mod t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (theory2 SmtTheoryOp.mod t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.mod t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.mod) (typeof_mod_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.mod t1 t2) = SmtType.Int by
    rw [typeof_mod_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.mod) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_ite
        (__smtx_model_eval_eq (__smtx_model_eval M t2) (SmtValue.Numeral 0))
        (__smtx_model_eval_apply
          (__smtx_model_lookup M native_mod_by_zero_id (SmtType.FunType SmtType.Int SmtType.Int))
          (__smtx_model_eval M t1))
        (__smtx_model_eval_mod_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))) =
    SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  by_cases hZero : n2 = 0
  · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_mod_total,
      native_veq, hZero] using
      typeof_value_model_eval_apply_lookup_fun M hM
        native_mod_by_zero_id SmtType.Int SmtType.Int (by simp) type_inhabited_int
        (SmtValue.Numeral n1) rfl
  · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_mod_total,
      __smtx_typeof_value, native_veq, hZero]

/-- Shows that evaluating `multmult` terms produces values of the expected type. -/
theorem typeof_value_model_eval_multmult
    (M : SmtModel)
    (hM : model_total_typed M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.multmult t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (theory2 SmtTheoryOp.multmult t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.multmult t1 t2) := by
  have hArgs := int_binop_args_of_non_none (op := theory2 SmtTheoryOp.multmult) (typeof_multmult_eq t1 t2) ht
  rw [show __smtx_typeof (theory2 SmtTheoryOp.multmult t1 t2) = SmtType.Int by
    rw [typeof_multmult_eq]
    simp [native_ite, native_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.multmult) t1) t2)) = _
  rw [__smtx_model_eval.eq_def]
  change __smtx_typeof_value
      (__smtx_model_eval_ite
        (__smtx_model_eval_geq (__smtx_model_eval M t2) (SmtValue.Numeral 0))
        (__smtx_model_eval_multmult_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))
        (__smtx_model_eval_ite
          (__smtx_model_eval_eq (__smtx_model_eval M t1) (SmtValue.Numeral 0))
          (__smtx_model_eval_apply
            (__smtx_model_lookup M native_div_by_zero_id (SmtType.FunType SmtType.Int SmtType.Int))
            (SmtValue.Numeral 1))
          (__smtx_model_eval_div_total (SmtValue.Numeral 1)
            (__smtx_model_eval_multmult_total (__smtx_model_eval M t1)
              (__smtx_model_eval__ (SmtValue.Numeral 0) (__smtx_model_eval M t2)))))) =
    SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  by_cases hNonneg : native_zleq 0 n2 = true
  · simp [__smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_ite,
      __smtx_model_eval_multmult_total, __smtx_typeof_value, hNonneg]
  · by_cases hZero : n1 = 0
    · simpa [__smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_ite,
        __smtx_model_eval_eq, __smtx_model_eval_div_total, __smtx_model_eval_multmult_total,
        __smtx_model_eval__, native_veq, hNonneg, hZero] using
        typeof_value_model_eval_apply_lookup_fun M hM
          native_div_by_zero_id SmtType.Int SmtType.Int (by simp) type_inhabited_int
          (SmtValue.Numeral 1) rfl
    · simp [__smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_ite,
        __smtx_model_eval_eq, __smtx_model_eval_div_total, __smtx_model_eval_multmult_total,
        __smtx_model_eval__, __smtx_typeof_value, native_veq, hNonneg, hZero]

/-- Shows that evaluating `qdiv_total` terms produces values of the expected type. -/
theorem typeof_value_model_eval_qdiv_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.qdiv_total t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (theory2 SmtTheoryOp.qdiv_total t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.qdiv_total t1 t2) := by
  rcases arith_binop_ret_args_of_non_none (op := theory2 SmtTheoryOp.qdiv_total) (typeof_qdiv_total_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.qdiv_total t1 t2) = SmtType.Real by
      rw [typeof_qdiv_total_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.qdiv_total) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_qdiv_total (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.qdiv_total t1 t2) = SmtType.Real by
      rw [typeof_qdiv_total_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.qdiv_total) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_qdiv_total (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

/-- Shows that evaluating `qdiv` terms produces values of the expected type. -/
theorem typeof_value_model_eval_qdiv
    (M : SmtModel)
    (hM : model_total_typed M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (theory2 SmtTheoryOp.qdiv t1 t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (theory2 SmtTheoryOp.qdiv t1 t2)) =
      __smtx_typeof (theory2 SmtTheoryOp.qdiv t1 t2) := by
  rcases arith_binop_ret_args_of_non_none (op := theory2 SmtTheoryOp.qdiv) (typeof_qdiv_eq t1 t2) ht with hArgs | hArgs
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.qdiv t1 t2) = SmtType.Real by
      rw [typeof_qdiv_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.qdiv) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_ite
          (__smtx_model_eval_eq (__smtx_model_eval M t2)
            (SmtValue.Rational (native_mk_rational 0 1)))
          (__smtx_model_eval_apply
            (__smtx_model_lookup M native_qdiv_by_zero_id
              (SmtType.FunType SmtType.Real SmtType.Real))
            (__smtx_model_eval M t1))
          (__smtx_model_eval_qdiv_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))) =
      SmtType.Real
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_qdiv_total,
      __smtx_typeof_value, native_veq]
  · rw [show __smtx_typeof (theory2 SmtTheoryOp.qdiv t1 t2) = SmtType.Real by
      rw [typeof_qdiv_eq]
      simp [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval M
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.qdiv) t1) t2)) = _
    rw [__smtx_model_eval.eq_def]
    change __smtx_typeof_value
        (__smtx_model_eval_ite
          (__smtx_model_eval_eq (__smtx_model_eval M t2)
            (SmtValue.Rational (native_mk_rational 0 1)))
          (__smtx_model_eval_apply
            (__smtx_model_lookup M native_qdiv_by_zero_id
              (SmtType.FunType SmtType.Real SmtType.Real))
            (__smtx_model_eval M t1))
          (__smtx_model_eval_qdiv_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    by_cases hZero : q2 = native_mk_rational 0 1
    · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_qdiv_total,
        native_veq, hZero] using
        typeof_value_model_eval_apply_lookup_fun M hM
          native_qdiv_by_zero_id SmtType.Real SmtType.Real (by simp) type_inhabited_real
          (SmtValue.Rational q1) rfl
    · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_qdiv_total,
        __smtx_typeof_value, native_veq, hZero]

end Smtm
