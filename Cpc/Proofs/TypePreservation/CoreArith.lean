import Cpc.Proofs.TypePreservation.Helpers

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

theorem ite_args_of_non_none
    {c t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2)) :
    ∃ T : SmtType,
      __smtx_typeof c = SmtType.Bool ∧
        __smtx_typeof t1 = T ∧
        __smtx_typeof t2 = T ∧
        T ≠ SmtType.None := by
  unfold term_has_non_none_type at ht
  let T1 := __smtx_typeof t1
  let T2 := __smtx_typeof t2
  have hBool : __smtx_typeof c = SmtType.Bool := by
    cases hc : __smtx_typeof c <;>
      simp [__smtx_typeof, __smtx_typeof_ite, smt_lit_ite, hc] at ht
    simp
  by_cases hEq : smt_lit_Teq T1 T2 = true
  · have hT : T1 = T2 := by
      simpa [smt_lit_Teq] using hEq
    have hNN : T1 ≠ SmtType.None := by
      simpa [__smtx_typeof, __smtx_typeof_ite, smt_lit_ite, hBool, T1, T2, hEq] using ht
    exact ⟨T1, hBool, rfl, by simpa [T1, T2] using hT.symm, hNN⟩
  · exfalso
    apply ht
    simp [__smtx_typeof, __smtx_typeof_ite, smt_lit_ite, hBool, T1, T2, hEq]

theorem typeof_value_model_eval_ite
    (M : SmtModel)
    (c t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2))
    (hpresc : __smtx_typeof_value (__smtx_model_eval M c) = __smtx_typeof c)
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2) := by
  rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2) = T by
    simp [__smtx_typeof, __smtx_typeof_ite, smt_lit_ite, smt_lit_Teq, hc, h1, h2]]
  change __smtx_typeof_value
      (__smtx_model_eval_ite (__smtx_model_eval M c) (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = T
  rcases bool_value_canonical (by simpa [hc] using hpresc) with ⟨b, hb⟩
  rw [hb]
  cases b
  · simpa [__smtx_model_eval_ite, h1, h2] using hpres2
  · simpa [__smtx_model_eval_ite, h1, h2] using hpres1

theorem select_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2)) :
    ∃ A B : SmtType,
      __smtx_typeof t1 = SmtType.Map A B ∧
        __smtx_typeof t2 = A := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      by_cases hEq : smt_lit_Teq A (__smtx_typeof t2)
      · have h2' : A = __smtx_typeof t2 := by
          simpa [smt_lit_Teq] using hEq
        exact ⟨A, B, rfl, h2'.symm⟩
      · exfalso
        exact ht (by simp [__smtx_typeof, __smtx_typeof_select, smt_lit_ite, h1, hEq])
  | _ =>
      exfalso
      exact ht (by simp [__smtx_typeof, __smtx_typeof_select, h1])

theorem store_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3)) :
    ∃ A B : SmtType,
      __smtx_typeof t1 = SmtType.Map A B ∧
        __smtx_typeof t2 = A ∧
        __smtx_typeof t3 = B := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      by_cases hEq1 : smt_lit_Teq A (__smtx_typeof t2)
      · by_cases hEq2 : smt_lit_Teq B (__smtx_typeof t3)
        · have h2' : A = __smtx_typeof t2 := by
            simpa [smt_lit_Teq] using hEq1
          have h3' : B = __smtx_typeof t3 := by
            simpa [smt_lit_Teq] using hEq2
          exact ⟨A, B, rfl, h2'.symm, h3'.symm⟩
        · exfalso
          exact ht (by
            simp [__smtx_typeof, __smtx_typeof_store, smt_lit_ite, h1, hEq1, hEq2])
      · exfalso
        exact ht (by
          simp [__smtx_typeof, __smtx_typeof_store, smt_lit_ite, h1, hEq1])
  | _ =>
      exfalso
      exact ht (by simp [__smtx_typeof, __smtx_typeof_store, h1])

theorem typeof_value_model_eval_select
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2) := by
  rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2) = B by
    simp [__smtx_typeof, __smtx_typeof_select, smt_lit_ite, smt_lit_Teq, h1, h2]]
  change
    __smtx_typeof_value
      (__smtx_model_eval_select (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = B
  rcases map_value_canonical (A := A) (B := B) (by simpa [h1] using hpres1) with ⟨m, hm⟩
  rw [hm]
  simpa [__smtx_model_eval_select, __smtx_map_select] using
    map_lookup_typed (m := m) (A := A) (B := B) (i := __smtx_model_eval M t2)
      (by simpa [hm, h1] using hpres1)
      (by simpa [h2] using hpres2)

theorem typeof_value_model_eval_store
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht : term_has_non_none_type
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3) := by
  rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3) =
        SmtType.Map A B by
    simp [__smtx_typeof, __smtx_typeof_store, smt_lit_ite, smt_lit_Teq, h1, h2, h3]]
  change
    __smtx_typeof_value
      (__smtx_model_eval_store (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Map A B
  rcases map_value_canonical (A := A) (B := B) (by simpa [h1] using hpres1) with ⟨m, hm⟩
  rw [hm]
  simpa [__smtx_model_eval_store, __smtx_map_store] using
    map_store_typed (m := m) (A := A) (B := B)
      (i := __smtx_model_eval M t2) (e := __smtx_model_eval M t3)
      (by simpa [hm, h1] using hpres1)
      (by simpa [h2] using hpres2)
      (by simpa [h3] using hpres3)

theorem eq_term_typeof_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2) = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, h1, h2] at ht ⊢
  all_goals
    first | exact ht

theorem typeof_value_model_eval_not
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.not t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.not t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.not t) := by
  have hArg : __smtx_typeof t = SmtType.Bool := by
    unfold term_has_non_none_type at ht
    cases h : __smtx_typeof t <;>
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
    simp
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.not t) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_not (__smtx_model_eval M t)) = SmtType.Bool
  rcases bool_value_canonical (by simpa [hArg] using hpres) with ⟨b, hb⟩
  rw [hb]
  rfl

theorem typeof_value_model_eval_or
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_or (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  rfl

theorem typeof_value_model_eval_and
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_and (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  rfl

theorem typeof_value_model_eval_imp
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_imp (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  rfl

theorem typeof_value_model_eval_eq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2) := by
  rw [eq_term_typeof_of_non_none ht]
  simpa using typeof_value_model_eval_eq_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem typeof_value_model_eval_xor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.xor) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  simpa using typeof_value_model_eval_xor_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem typeof_value_model_eval_distinct
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2) := by
  rw [eq_term_typeof_of_non_none ht]
  simpa using typeof_value_model_eval_distinct_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem typeof_value_model_eval_plus
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.plus) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2) = SmtType.Int by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_plus (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_plus (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_neg
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2) = SmtType.Int by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval__ (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval__ (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_mult
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2) = SmtType.Int by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_mult (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_mult (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_lt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_lt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_lt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_leq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_leq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_leq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_gt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_gt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_gt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_geq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_geq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_geq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_to_real
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_real t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.to_real t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.to_real t) := by
  rcases to_real_arg_of_non_none ht with hArg | hArg
  · rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.to_real t) = SmtType.Real by
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
    change __smtx_typeof_value (__smtx_model_eval_to_real (__smtx_model_eval M t)) = SmtType.Real
    rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
    rw [hn]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.to_real t) = SmtType.Real by
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
    change __smtx_typeof_value (__smtx_model_eval_to_real (__smtx_model_eval M t)) = SmtType.Real
    rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
    rw [hq]
    rfl

theorem typeof_value_model_eval_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.to_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.to_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.to_int t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_to_int (__smtx_model_eval M t)) = SmtType.Int
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  rfl

theorem typeof_value_model_eval_is_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.is_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.is_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.is_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.is_int t) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_is_int (__smtx_model_eval M t)) = SmtType.Bool
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  simpa [__smtx_model_eval_is_int, __smtx_model_eval_to_int, __smtx_model_eval_to_real] using
    typeof_value_model_eval_eq_value
      (SmtValue.Rational (smt_lit_to_real (smt_lit_to_int q))) (SmtValue.Rational q)

theorem typeof_value_model_eval_abs
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.abs t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.abs t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.abs t) := by
  have hArg : __smtx_typeof t = SmtType.Int := int_arg_of_non_none ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.abs t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_abs (__smtx_model_eval M t)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  cases hlt : smt_lit_zlt n 0 <;>
    simp [__smtx_model_eval_abs, __smtx_model_eval_lt, __smtx_model_eval_ite,
      __smtx_model_eval__, __smtx_typeof_value, hlt]

theorem int_ret_arg_of_non_none
    {op t : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t) SmtType.Int) R SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h] at ht
  simp

theorem int_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) SmtType.Int)
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) SmtType.Int) R SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    __smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  simp

theorem typeof_value_model_eval_apply_lookup_map
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (A B : SmtType)
    (hA : A ≠ SmtType.None)
    (hB : type_inhabited B)
    (i : SmtValue)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value
        (__smtx_model_eval_apply (__smtx_model_lookup M s (SmtType.Map A B)) i) = B := by
  have hiNN : i ≠ SmtValue.NotValue := by
    intro h
    cases h
    simp [__smtx_typeof_value] at hi
    exact hA hi.symm
  have hMapApply :
      ∀ {m : SmtMap} {j : SmtValue},
        j ≠ SmtValue.NotValue ->
        __smtx_model_eval_apply (SmtValue.Map m) j =
          __smtx_map_select (SmtValue.Map m) j := by
    intro m j hj
    cases j with
    | NotValue => exact (hj rfl).elim
    | Boolean b
    | Numeral b
    | Rational b
    | Binary _ b
    | RegLan b
    | Map b
    | Set b
    | Seq b
    | Char b
    | DtCons _ _ b
    | Apply _ b =>
        simp [__smtx_model_eval_apply, __smtx_map_select]
  have hLookup :
      __smtx_typeof_value (__smtx_model_lookup M s (SmtType.Map A B)) = SmtType.Map A B :=
    model_total_typed_lookup hM s (SmtType.Map A B) (type_inhabited_map hB)
  rcases map_value_canonical (A := A) (B := B) hLookup with ⟨m, hm⟩
  rw [hm]
  rw [hMapApply hiNN]
  simpa [__smtx_map_select] using
    map_lookup_typed (m := m) (A := A) (B := B) (i := i)
      (by simpa [hm] using hLookup) hi

theorem typeof_value_model_eval_div_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total t1) t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.div_total) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total t1) t2) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_div_total (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  rfl

theorem typeof_value_model_eval_mod_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total t1) t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod_total) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total t1) t2) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_mod_total (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  rfl

theorem typeof_value_model_eval_multmult_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total t1) t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.multmult_total) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total t1) t2) =
      SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_multmult_total (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  rfl

theorem typeof_value_model_eval_divisible
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible t1) t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.divisible) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_divisible (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  simpa [__smtx_model_eval_divisible, __smtx_model_eval_mod_total] using
    typeof_value_model_eval_eq_value
      (SmtValue.Numeral (smt_lit_mod_total n2 n1))
      (SmtValue.Numeral 0)

theorem typeof_value_model_eval_int_pow2
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.int_pow2 t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.int_pow2 t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.int_pow2 t) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_pow2) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.int_pow2 t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_int_pow2 (__smtx_model_eval M t)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  rfl

theorem typeof_value_model_eval_int_log2
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.int_log2 t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.int_log2 t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.int_log2 t) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_log2) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.int_log2 t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_int_log2 (__smtx_model_eval M t)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  rfl

theorem typeof_value_model_eval_div
    (M : SmtModel)
    (hM : model_total_typed M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div t1) t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.div) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div t1) t2) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value
      (__smtx_model_eval_ite
        (__smtx_model_eval_eq (__smtx_model_eval M t2) (SmtValue.Numeral 0))
        (__smtx_model_eval_apply
          (__smtx_model_lookup M smt_lit_div_by_zero_id (SmtType.Map SmtType.Int SmtType.Int))
          (__smtx_model_eval M t1))
        (__smtx_model_eval_div_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))) =
      SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  by_cases hZero : n2 = 0
  · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_div_total,
      smt_lit_veq, hZero] using
      typeof_value_model_eval_apply_lookup_map M hM
        smt_lit_div_by_zero_id SmtType.Int SmtType.Int (by simp) type_inhabited_int
        (SmtValue.Numeral n1) rfl
  · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_div_total,
      __smtx_typeof_value, smt_lit_veq, hZero]

theorem typeof_value_model_eval_mod
    (M : SmtModel)
    (hM : model_total_typed M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod t1) t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod t1) t2) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value
      (__smtx_model_eval_ite
        (__smtx_model_eval_eq (__smtx_model_eval M t2) (SmtValue.Numeral 0))
        (__smtx_model_eval_apply
          (__smtx_model_lookup M smt_lit_mod_by_zero_id (SmtType.Map SmtType.Int SmtType.Int))
          (__smtx_model_eval M t1))
        (__smtx_model_eval_mod_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))) =
      SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  by_cases hZero : n2 = 0
  · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_mod_total,
      smt_lit_veq, hZero] using
      typeof_value_model_eval_apply_lookup_map M hM
        smt_lit_mod_by_zero_id SmtType.Int SmtType.Int (by simp) type_inhabited_int
        (SmtValue.Numeral n1) rfl
  · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_mod_total,
      __smtx_typeof_value, smt_lit_veq, hZero]

theorem typeof_value_model_eval_multmult
    (M : SmtModel)
    (hM : model_total_typed M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult t1) t2) := by
  have hArgs := int_binop_args_of_non_none (op := SmtTerm.multmult) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult t1) t2) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value
      (__smtx_model_eval_ite
        (__smtx_model_eval_geq (__smtx_model_eval M t2) (SmtValue.Numeral 0))
        (__smtx_model_eval_multmult_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))
        (__smtx_model_eval_ite
          (__smtx_model_eval_eq (__smtx_model_eval M t1) (SmtValue.Numeral 0))
          (__smtx_model_eval_apply
            (__smtx_model_lookup M smt_lit_div_by_zero_id (SmtType.Map SmtType.Int SmtType.Int))
            (SmtValue.Numeral 1))
          (__smtx_model_eval_div_total (SmtValue.Numeral 1)
            (__smtx_model_eval_multmult_total (__smtx_model_eval M t1)
              (__smtx_model_eval__ (SmtValue.Numeral 0) (__smtx_model_eval M t2))))))
      = SmtType.Int
  rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
  rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
  rw [hn1, hn2]
  by_cases hNonneg : smt_lit_zleq 0 n2 = true
  · simp [__smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_ite,
      __smtx_model_eval_multmult_total, __smtx_typeof_value, hNonneg]
  · by_cases hZero : n1 = 0
    · simpa [__smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_ite,
        __smtx_model_eval_eq, __smtx_model_eval_div_total, __smtx_model_eval_multmult_total,
        __smtx_model_eval__, smt_lit_veq, hNonneg, hZero] using
        typeof_value_model_eval_apply_lookup_map M hM
          smt_lit_div_by_zero_id SmtType.Int SmtType.Int (by simp) type_inhabited_int
          (SmtValue.Numeral 1) rfl
    · simp [__smtx_model_eval_geq, __smtx_model_eval_leq, __smtx_model_eval_ite,
        __smtx_model_eval_eq, __smtx_model_eval_div_total, __smtx_model_eval_multmult_total,
        __smtx_model_eval__, __smtx_typeof_value, smt_lit_veq, hNonneg, hZero]

theorem typeof_value_model_eval_qdiv_total
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total t1) t2) := by
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_qdiv_total (__smtx_model_eval M t1)
        (__smtx_model_eval M t2)) = SmtType.Real
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_qdiv_total (__smtx_model_eval M t1)
        (__smtx_model_eval M t2)) = SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_qdiv
    (M : SmtModel)
    (hM : model_total_typed M)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv t1) t2) := by
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value
        (__smtx_model_eval_ite
          (__smtx_model_eval_eq (__smtx_model_eval M t2)
            (SmtValue.Rational (smt_lit_mk_rational 0 1)))
          (__smtx_model_eval_apply
            (__smtx_model_lookup M smt_lit_qdiv_by_zero_id (SmtType.Map SmtType.Real SmtType.Real))
            (__smtx_model_eval M t1))
          (__smtx_model_eval_qdiv_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))) =
        SmtType.Real
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_qdiv_total,
      __smtx_typeof_value, smt_lit_veq]
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value
        (__smtx_model_eval_ite
          (__smtx_model_eval_eq (__smtx_model_eval M t2)
            (SmtValue.Rational (smt_lit_mk_rational 0 1)))
          (__smtx_model_eval_apply
            (__smtx_model_lookup M smt_lit_qdiv_by_zero_id (SmtType.Map SmtType.Real SmtType.Real))
            (__smtx_model_eval M t1))
          (__smtx_model_eval_qdiv_total (__smtx_model_eval M t1) (__smtx_model_eval M t2))) =
        SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    by_cases hZero : q2 = smt_lit_mk_rational 0 1
    · simpa [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_qdiv_total,
        smt_lit_veq, hZero] using
        typeof_value_model_eval_apply_lookup_map M hM
          smt_lit_qdiv_by_zero_id SmtType.Real SmtType.Real (by simp) type_inhabited_real
          (SmtValue.Rational q1) rfl
    · simp [__smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_qdiv_total,
        __smtx_typeof_value, smt_lit_veq, hZero]

end Smtm
