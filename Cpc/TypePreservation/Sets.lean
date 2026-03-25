import Cpc.TypePreservation.Helpers

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

theorem set_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_sets_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    ∃ A : SmtType,
      __smtx_typeof t1 = SmtType.Map A SmtType.Bool ∧
        __smtx_typeof t2 = SmtType.Map A SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      cases h2 : __smtx_typeof t2 with
      | Map C D =>
          cases B <;> cases D <;>
            simp [hTy, __smtx_typeof_sets_op_2, h1, h2] at ht
          have hEq : A = C := by
            simpa [hTy, __smtx_typeof_sets_op_2, smt_lit_ite, smt_lit_Teq, h1, h2] using ht
          subst hEq
          exact ⟨A, rfl, rfl⟩
      | _ =>
          simp [hTy, __smtx_typeof_sets_op_2, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_sets_op_2, h1, h2] at ht

theorem set_binop_ret_args_of_non_none
    {op t1 t2 : SmtTerm} {T : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_sets_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) T)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    ∃ A : SmtType,
      __smtx_typeof t1 = SmtType.Map A SmtType.Bool ∧
        __smtx_typeof t2 = SmtType.Map A SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      cases h2 : __smtx_typeof t2 with
      | Map C D =>
          cases B <;> cases D <;>
            simp [hTy, __smtx_typeof_sets_op_2_ret, h1, h2] at ht
          have hEqAnd : A = C ∧ T ≠ SmtType.None := by
            simpa [hTy, __smtx_typeof_sets_op_2_ret, smt_lit_ite, smt_lit_Teq, h1, h2] using ht
          have hEq : A = C := hEqAnd.1
          subst hEq
          exact ⟨A, rfl, rfl⟩
      | _ =>
          simp [hTy, __smtx_typeof_sets_op_2_ret, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_sets_op_2_ret, h1, h2] at ht

theorem set_member_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member t1) t2)) :
    ∃ A : SmtType,
      __smtx_typeof t1 = A ∧
        __smtx_typeof t2 = SmtType.Map A SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h2 : __smtx_typeof t2 with
  | Map A B =>
      cases B with
      | Bool =>
          by_cases hEq : __smtx_typeof t1 = A
          · refine ⟨A, hEq, ?_⟩
            rfl
          · simp [__smtx_typeof, __smtx_typeof_set_member, smt_lit_ite, smt_lit_Teq, h2, hEq] at ht
      | _ =>
          simp [__smtx_typeof, __smtx_typeof_set_member, h2] at ht
  | _ =>
      simp [__smtx_typeof, __smtx_typeof_set_member, h2] at ht

theorem mss_op_internal_typed
    (isInter : smt_lit_Bool) :
    ∀ {m1 m2 acc : SmtMap} {A : SmtType},
      __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool ->
        __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool ->
        __smtx_typeof_map_value acc = SmtType.Map A SmtType.Bool ->
        __smtx_typeof_map_value (__smtx_mss_op_internal isInter m1 m2 acc) =
          SmtType.Map A SmtType.Bool
  | SmtMap.default T efalse, m2, acc, A, hm1, hm2, hacc => by
      simpa [__smtx_mss_op_internal] using hacc
  | SmtMap.cons e etrue m1, m2, acc, A, hm1, hm2, hacc => by
      by_cases hEq :
          smt_lit_Teq (SmtType.Map (__smtx_typeof_value e) (__smtx_typeof_value etrue))
            (__smtx_typeof_map_value m1)
      · have hm1' : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool := by
          simpa [__smtx_typeof_map_value, smt_lit_ite, hEq] using hm1
        have hEq' :
            SmtType.Map (__smtx_typeof_value e) (__smtx_typeof_value etrue) =
              __smtx_typeof_map_value m1 := by
          simpa [smt_lit_Teq] using hEq
        have hHead :
            SmtType.Map (__smtx_typeof_value e) (__smtx_typeof_value etrue) =
              SmtType.Map A SmtType.Bool := hEq'.trans hm1'
        have he : __smtx_typeof_value e = A := by
          simpa [__smtx_index_typeof_map] using congrArg __smtx_index_typeof_map hHead
        have hAccCons :
            __smtx_typeof_map_value (SmtMap.cons e (SmtValue.Boolean true) acc) =
              SmtType.Map A SmtType.Bool := by
          simpa [__smtx_typeof_value] using
            map_store_typed (m := acc) (A := A) (B := SmtType.Bool)
              hacc he rfl
        let acc' :=
          smt_lit_ite
            (smt_lit_iff
              (smt_lit_veq (__smtx_msm_lookup m2 e) (SmtValue.Boolean true))
              isInter)
            (SmtMap.cons e (SmtValue.Boolean true) acc) acc
        have hacc' : __smtx_typeof_map_value acc' = SmtType.Map A SmtType.Bool := by
          dsimp [acc']
          by_cases hKeep :
              smt_lit_iff
                (smt_lit_veq (__smtx_msm_lookup m2 e) (SmtValue.Boolean true))
                isInter
          · simpa [smt_lit_ite, hKeep] using hAccCons
          · simpa [smt_lit_ite, hKeep] using hacc
        simpa [__smtx_mss_op_internal, hEq, acc'] using
          mss_op_internal_typed isInter (m1 := m1) (m2 := m2) (acc := acc')
            (A := A) hm1' hm2 hacc'
      · simp [__smtx_typeof_map_value, smt_lit_ite, hEq] at hm1

theorem typeof_value_model_eval_set_union
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union t1) t2) := by
  rcases set_binop_args_of_non_none (op := SmtTerm.set_union) rfl ht with ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union t1) t2) =
      SmtType.Map A SmtType.Bool by
    simp [__smtx_typeof, __smtx_typeof_sets_op_2, smt_lit_ite, smt_lit_Teq, h1, h2]]
  change __smtx_typeof_value (__smtx_model_eval_set_union (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Map A SmtType.Bool
  rcases map_value_canonical (A := A) (B := SmtType.Bool)
      (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
  rcases map_value_canonical (A := A) (B := SmtType.Bool)
      (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
  have hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool := by
    simpa [hm1, h1, __smtx_typeof_value] using hpres1
  have hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool := by
    simpa [hm2, h2, __smtx_typeof_value] using hpres2
  have hIdx1 : __smtx_index_typeof_map (__smtx_typeof_map_value m1) = A := by
    simpa [__smtx_index_typeof_map] using congrArg __smtx_index_typeof_map hm1Ty
  have hDefault :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  rw [hm1, hm2]
  simpa [__smtx_model_eval_set_union, __smtx_set_union, __smtx_typeof_value, hIdx1] using
    mss_op_internal_typed false
      (m1 := m1) (m2 := SmtMap.default A (SmtValue.Boolean false)) (acc := m2)
      (A := A)
      hm1Ty
      hDefault
      hm2Ty

theorem typeof_value_model_eval_set_inter
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter t1) t2) := by
  rcases set_binop_args_of_non_none (op := SmtTerm.set_inter) rfl ht with ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter t1) t2) =
      SmtType.Map A SmtType.Bool by
    simp [__smtx_typeof, __smtx_typeof_sets_op_2, smt_lit_ite, smt_lit_Teq, h1, h2]]
  change __smtx_typeof_value (__smtx_model_eval_set_inter (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Map A SmtType.Bool
  rcases map_value_canonical (A := A) (B := SmtType.Bool)
      (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
  rcases map_value_canonical (A := A) (B := SmtType.Bool)
      (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
  have hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool := by
    simpa [hm1, h1, __smtx_typeof_value] using hpres1
  have hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool := by
    simpa [hm2, h2, __smtx_typeof_value] using hpres2
  have hIdx1 : __smtx_index_typeof_map (__smtx_typeof_map_value m1) = A := by
    simpa [__smtx_index_typeof_map] using congrArg __smtx_index_typeof_map hm1Ty
  have hDefault :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  rw [hm1, hm2]
  simpa [__smtx_model_eval_set_inter, __smtx_set_inter, __smtx_typeof_value, hIdx1] using
    mss_op_internal_typed true
      (m1 := m1) (m2 := m2) (acc := SmtMap.default A (SmtValue.Boolean false))
      (A := A)
      hm1Ty
      hm2Ty
      hDefault

theorem typeof_value_model_eval_set_minus
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus t1) t2) := by
  rcases set_binop_args_of_non_none (op := SmtTerm.set_minus) rfl ht with ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus t1) t2) =
      SmtType.Map A SmtType.Bool by
    simp [__smtx_typeof, __smtx_typeof_sets_op_2, smt_lit_ite, smt_lit_Teq, h1, h2]]
  change __smtx_typeof_value (__smtx_model_eval_set_minus (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Map A SmtType.Bool
  rcases map_value_canonical (A := A) (B := SmtType.Bool)
      (by simpa [h1] using hpres1) with ⟨m1, hm1⟩
  rcases map_value_canonical (A := A) (B := SmtType.Bool)
      (by simpa [h2] using hpres2) with ⟨m2, hm2⟩
  have hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A SmtType.Bool := by
    simpa [hm1, h1, __smtx_typeof_value] using hpres1
  have hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A SmtType.Bool := by
    simpa [hm2, h2, __smtx_typeof_value] using hpres2
  have hIdx1 : __smtx_index_typeof_map (__smtx_typeof_map_value m1) = A := by
    simpa [__smtx_index_typeof_map] using congrArg __smtx_index_typeof_map hm1Ty
  have hDefault :
      __smtx_typeof_map_value (SmtMap.default A (SmtValue.Boolean false)) =
        SmtType.Map A SmtType.Bool := by
    simp [__smtx_typeof_map_value, __smtx_typeof_value]
  rw [hm1, hm2]
  simpa [__smtx_model_eval_set_minus, __smtx_set_minus, __smtx_typeof_value, hIdx1] using
    mss_op_internal_typed false
      (m1 := m1) (m2 := m2) (acc := SmtMap.default A (SmtValue.Boolean false))
      (A := A)
      hm1Ty
      hm2Ty
      hDefault

theorem typeof_value_model_eval_set_member
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member t1) t2) := by
  rcases set_member_args_of_non_none ht with ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, __smtx_typeof_set_member, smt_lit_ite, smt_lit_Teq, h1, h2]]
  change __smtx_typeof_value (__smtx_model_eval_set_member (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases map_value_canonical (A := A) (B := SmtType.Bool)
      (by simpa [h2] using hpres2) with ⟨m, hm⟩
  have hmTy : __smtx_typeof_map_value m = SmtType.Map A SmtType.Bool := by
    simpa [hm, h2, __smtx_typeof_value] using hpres2
  rw [hm]
  simpa [__smtx_model_eval_set_member, __smtx_map_select] using
    map_lookup_typed (m := m) (A := A) (B := SmtType.Bool) (i := __smtx_model_eval M t1)
      hmTy
      (by simpa [h1] using hpres1)

theorem typeof_value_model_eval_set_subset
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset t1) t2) := by
  rcases set_binop_ret_args_of_non_none (op := SmtTerm.set_subset) (T := SmtType.Bool) rfl ht with
    ⟨A, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, __smtx_typeof_sets_op_2_ret, smt_lit_ite, smt_lit_Teq, h1, h2]]
  simpa [__smtx_model_eval_set_subset] using
    typeof_value_model_eval_eq_value
      (__smtx_model_eval_set_inter (__smtx_model_eval M t1) (__smtx_model_eval M t2))
      (__smtx_model_eval M t1)

end Smtm
