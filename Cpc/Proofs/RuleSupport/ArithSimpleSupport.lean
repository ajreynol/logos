import Cpc.Proofs.RuleSupport.ArithPolyNormRelSupport
import Cpc.Proofs.RuleSupport.CnfSupport
import Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace ArithSimpleSupport

private theorem eo_typeof_lt_eq_bool_of_ne_stuck {A B : Term}
    (h : __eo_typeof_lt A B ≠ Term.Stuck) :
    __eo_typeof_lt A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
      native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢
  case UOp.UOp opA opB =>
    cases opA <;> cases opB <;>
      simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢

private theorem eo_typeof_lt_bool_cases {A B : Term}
    (h : __eo_typeof_lt A B = Term.Bool) :
    (A = Term.UOp UserOp.Int ∧ B = Term.UOp UserOp.Int) ∨
      (A = Term.UOp UserOp.Real ∧ B = Term.UOp UserOp.Real) := by
  cases A <;> cases B <;>
    simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
      native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢
  case UOp.UOp opA opB =>
    cases opA <;> cases opB <;>
      simp [__eo_typeof_lt, __eo_requires, __eo_eq, __is_arith_type,
        native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢

private theorem smt_arith_arg_types_of_eo_rel_bool
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool) :
    (__smtx_typeof (__eo_to_smt t) = SmtType.Int ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.Int) ∨
    (__smtx_typeof (__eo_to_smt t) = SmtType.Real ∧
      __smtx_typeof (__eo_to_smt s) = SmtType.Real) := by
  rcases eo_typeof_lt_bool_cases hTy with hInt | hReal
  · left
    constructor
    · have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t (Term.UOp UserOp.Int) (__eo_to_smt t) rfl hTTrans hInt.1
      simpa [__eo_to_smt_type] using this
    · have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s (Term.UOp UserOp.Int) (__eo_to_smt s) rfl hSTrans hInt.2
      simpa [__eo_to_smt_type] using this
  · right
    constructor
    · have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        t (Term.UOp UserOp.Real) (__eo_to_smt t) rfl hTTrans hReal.1
      simpa [__eo_to_smt_type] using this
    · have := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        s (Term.UOp UserOp.Real) (__eo_to_smt s) rfl hSTrans hReal.2
      simpa [__eo_to_smt_type] using this

private theorem leq_has_bool_type
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_leq_eq, typeof_leq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_leq_eq, typeof_leq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem lt_has_bool_type
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_lt_eq, typeof_lt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem gt_has_bool_type
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_gt_eq, typeof_gt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_gt_eq, typeof_gt_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem geq_has_bool_type
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hTy with hInt | hReal
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_geq_eq, typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hInt.1, hInt.2]
  · unfold RuleProofs.eo_has_bool_type
    rw [eo_to_smt_geq_eq, typeof_geq_eq]
    simp [__smtx_typeof_arith_overload_op_2_ret, hReal.1, hReal.2]

private theorem eo_typeof_not_eq_bool_of_ne_stuck {A : Term}
    (h : __eo_typeof_not A ≠ Term.Stuck) :
    __eo_typeof_not A = Term.Bool := by
  cases A <;> simp [__eo_typeof_not] at h ⊢

private theorem int_decide_lt_eq_not_decide_ge (a b : native_Int) :
    decide (a < b) = native_not (decide (b ≤ a)) := by
  by_cases h : b ≤ a
  · have hNot : ¬ a < b := Int.not_lt_of_ge h
    simp [native_not, h, hNot]
  · have hLt : a < b := Int.lt_of_not_ge h
    simp [native_not, h, hLt]

private theorem rat_decide_lt_eq_not_decide_ge (a b : native_Rat) :
    decide (a < b) = native_not (decide (b ≤ a)) := by
  by_cases h : b ≤ a
  · have hNot : ¬ a < b := Rat.not_lt.mpr h
    simp [native_not, h, hNot]
  · have hLt : a < b := Rat.not_le.mp h
    simp [native_not, h, hLt]

private theorem eval_lt_not_geq_rel
    (M : SmtModel) (hM : model_total_typed M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hLtTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) = Term.Bool) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)))) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hLtTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hLtTy with hInt | hReal
  · have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
      simpa [hInt.1] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hInt.1])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Int := by
      simpa [hInt.2] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hInt.2])
    rcases int_value_canonical hEvalTValTy with ⟨nt, hEvalT⟩
    rcases int_value_canonical hEvalSValTy with ⟨ns, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_lt_eq]
    rw [show __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
        SmtTerm.not (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s)) by rfl]
    rw [__smtx_model_eval.eq_15, __smtx_model_eval.eq_6, __smtx_model_eval.eq_18]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_lt, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_not, native_zlt, native_zleq,
      int_decide_lt_eq_not_decide_ge]
    exact RuleProofs.smtx_model_eval_eq_refl
      (SmtValue.Boolean (native_not (decide (ns ≤ nt))))
  · have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Real := by
      simpa [hReal.1] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hReal.1])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Real := by
      simpa [hReal.2] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hReal.2])
    rcases real_value_canonical hEvalTValTy with ⟨qt, hEvalT⟩
    rcases real_value_canonical hEvalSValTy with ⟨qs, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_lt_eq]
    rw [show __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
        SmtTerm.not (SmtTerm.geq (__eo_to_smt t) (__eo_to_smt s)) by rfl]
    rw [__smtx_model_eval.eq_15, __smtx_model_eval.eq_6, __smtx_model_eval.eq_18]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_lt, __smtx_model_eval_geq, __smtx_model_eval_leq,
      __smtx_model_eval_not, native_qlt, native_qleq,
      rat_decide_lt_eq_not_decide_ge]
    exact RuleProofs.smtx_model_eval_eq_refl
      (SmtValue.Boolean (native_not (decide (qs ≤ qt))))

private theorem eval_gt_not_geq_swap_rel
    (M : SmtModel) (hM : model_total_typed M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hGtTy : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) = Term.Bool) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s)))
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)))) := by
  change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool at hGtTy
  rcases smt_arith_arg_types_of_eo_rel_bool t s hTTrans hSTrans hGtTy with hInt | hReal
  · have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Int := by
      simpa [hInt.1] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hInt.1])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Int := by
      simpa [hInt.2] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hInt.2])
    rcases int_value_canonical hEvalTValTy with ⟨nt, hEvalT⟩
    rcases int_value_canonical hEvalSValTy with ⟨ns, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_gt_eq]
    rw [show __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
        SmtTerm.not (SmtTerm.geq (__eo_to_smt s) (__eo_to_smt t)) by rfl]
    rw [__smtx_model_eval.eq_17, __smtx_model_eval.eq_6, __smtx_model_eval.eq_18]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, __smtx_model_eval_geq,
      __smtx_model_eval_leq, __smtx_model_eval_not, native_zlt, native_zleq,
      int_decide_lt_eq_not_decide_ge]
    exact RuleProofs.smtx_model_eval_eq_refl
      (SmtValue.Boolean (native_not (decide (nt ≤ ns))))
  · have hEvalTValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = SmtType.Real := by
      simpa [hReal.1] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
          (by simp [term_has_non_none_type, hReal.1])
    have hEvalSValTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = SmtType.Real := by
      simpa [hReal.2] using
        Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
          (by simp [term_has_non_none_type, hReal.2])
    rcases real_value_canonical hEvalTValTy with ⟨qt, hEvalT⟩
    rcases real_value_canonical hEvalSValTy with ⟨qs, hEvalS⟩
    unfold RuleProofs.smt_value_rel
    rw [eo_to_smt_gt_eq]
    rw [show __eo_to_smt
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
        SmtTerm.not (SmtTerm.geq (__eo_to_smt s) (__eo_to_smt t)) by rfl]
    rw [__smtx_model_eval.eq_17, __smtx_model_eval.eq_6, __smtx_model_eval.eq_18]
    rw [hEvalT, hEvalS]
    simp [__smtx_model_eval_gt, __smtx_model_eval_lt, __smtx_model_eval_geq,
      __smtx_model_eval_leq, __smtx_model_eval_not, native_qlt, native_qleq,
      rat_decide_lt_eq_not_decide_ge]
    exact RuleProofs.smtx_model_eval_eq_refl
      (SmtValue.Boolean (native_not (decide (qt ≤ qs))))

private theorem prog_arith_elim_leq_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_elim_leq t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_elim_leq, htSt, hsSt]

private theorem prog_arith_elim_lt_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_elim_lt t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_elim_lt, htSt, hsSt]

private theorem prog_arith_elim_gt_eq_of_nonstuck
    (t s : Term)
    (ht : t ≠ Term.Stuck)
    (hs : s ≠ Term.Stuck) :
    __eo_prog_arith_elim_gt t s =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) := by
  by_cases htSt : t = Term.Stuck
  · exact False.elim (ht htSt)
  by_cases hsSt : s = Term.Stuck
  · exact False.elim (hs hsSt)
  simp [__eo_prog_arith_elim_gt, htSt, hsSt]

theorem typed_arith_elim_leq
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_leq t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_elim_leq t s) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_leq_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
      Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof s) (__eo_typeof t) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hRightNotStuck
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)
    (leq_has_bool_type t s hTTrans hSTrans hLeftTy)
    (geq_has_bool_type s t hSTrans hTTrans hRightTy)

theorem facts_arith_elim_leq
    (M : SmtModel) (_hM : model_total_typed M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_leq t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_elim_leq t s) true := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_leq_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_elim_leq t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s))
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) := by
    simpa [hProgEq] using hBool
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.leq) t) s)
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)
    hBool' <| by
      unfold RuleProofs.smt_value_rel
      rw [eo_to_smt_leq_eq, eo_to_smt_geq_eq]
      rw [__smtx_model_eval.eq_16, __smtx_model_eval.eq_18]
      simp [__smtx_model_eval_geq]
      exact RuleProofs.smtx_model_eval_eq_refl
        (__smtx_model_eval_leq (__smtx_model_eval M (__eo_to_smt t))
          (__smtx_model_eval M (__eo_to_smt s)))

theorem typed_arith_elim_lt
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_lt t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_elim_lt t s) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_lt_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
      (__eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))) =
      Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightNotTy :
      __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
        Term.Bool := by
    change __eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)) =
      Term.Bool
    exact eo_typeof_not_eq_bool_of_ne_stuck hRightNotStuck
  have hGeqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s) =
        Term.Bool := by
    exact CnfSupport.typeof_not_eq_bool hRightNotTy
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
    (lt_has_bool_type t s hTTrans hSTrans hLeftTy)
    (RuleProofs.eo_has_bool_type_not_of_bool_arg
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s)
      (geq_has_bool_type t s hTTrans hSTrans hGeqTy))

theorem facts_arith_elim_lt
    (M : SmtModel) (hM : model_total_typed M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_lt t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_elim_lt t s) true := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_lt_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_elim_lt t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))) := by
    simpa [hProgEq] using hBool
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s))
      (__eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))) =
      Term.Bool at hResultTy'
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck
      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').1
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) t) s))
    hBool'
    (eval_lt_not_geq_rel M hM t s hTTrans hSTrans hLeftTy)

theorem typed_arith_elim_gt
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_gt t s) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_arith_elim_gt t s) := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_gt_eq_of_nonstuck t s ht hs
  rw [hProgEq] at hResultTy ⊢
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
      (__eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))) =
      Term.Bool at hResultTy
  have hLeftNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  have hRightNotStuck :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).2
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck hLeftNotStuck
  have hRightNotTy :
      __eo_typeof
        (Term.Apply (Term.UOp UserOp.not)
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
        Term.Bool := by
    change __eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)) =
      Term.Bool
    exact eo_typeof_not_eq_bool_of_ne_stuck hRightNotStuck
  have hGeqTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t) =
        Term.Bool := by
    exact CnfSupport.typeof_not_eq_bool hRightNotTy
  exact CnfSupport.eo_has_bool_type_eq_of_bool_args
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))
    (gt_has_bool_type t s hTTrans hSTrans hLeftTy)
    (RuleProofs.eo_has_bool_type_not_of_bool_arg
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t)
      (geq_has_bool_type s t hSTrans hTTrans hGeqTy))

theorem facts_arith_elim_gt
    (M : SmtModel) (hM : model_total_typed M)
    (t s : Term)
    (hTTrans : RuleProofs.eo_has_smt_translation t)
    (hSTrans : RuleProofs.eo_has_smt_translation s)
    (hResultTy : __eo_typeof (__eo_prog_arith_elim_gt t s) = Term.Bool) :
    eo_interprets M (__eo_prog_arith_elim_gt t s) true := by
  have ht : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTTrans
  have hs : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hSTrans
  have hProgEq := prog_arith_elim_gt_eq_of_nonstuck t s ht hs
  have hBool := typed_arith_elim_gt t s hTTrans hSTrans hResultTy
  rw [hProgEq]
  have hBool' :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))) := by
    simpa [hProgEq] using hBool
  have hResultTy' :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
          (Term.Apply (Term.UOp UserOp.not)
            (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))) =
        Term.Bool := by
    simpa [hProgEq] using hResultTy
  change __eo_typeof_eq
      (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s))
      (__eo_typeof_not
        (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))) =
      Term.Bool at hResultTy'
  have hLeftTy :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s) =
        Term.Bool := by
    change __eo_typeof_lt (__eo_typeof t) (__eo_typeof s) = Term.Bool
    exact eo_typeof_lt_eq_bool_of_ne_stuck
      (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy').1
  exact RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.gt) t) s)
    (Term.Apply (Term.UOp UserOp.not)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) s) t))
    hBool'
    (eval_gt_not_geq_swap_rel M hM t s hTTrans hSTrans hLeftTy)

end ArithSimpleSupport
