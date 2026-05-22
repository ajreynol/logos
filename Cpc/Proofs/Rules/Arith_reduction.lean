import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem smt_eval_to_real_idem (v : SmtValue) :
    __smtx_model_eval_to_real (__smtx_model_eval_to_real v) =
      __smtx_model_eval_to_real v := by
  cases v <;> rfl

private theorem smt_qdiv_eval_reduction_self
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.qdiv x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       let yr := __smtx_model_eval_to_real yv
       let xr := __smtx_model_eval_to_real xv
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yr (SmtValue.Rational (native_mk_rational 0 1)))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_qdiv_by_zero_id
             (SmtType.FunType SmtType.Real SmtType.Real))
           xr)
         (__smtx_model_eval_qdiv_total xr yr)) := by
  rw [__smtx_model_eval.eq_128]

private theorem smt_qdiv_eval_reduction_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.qdiv x y))
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       let yr := __smtx_model_eval_to_real yv
       let xr := __smtx_model_eval_to_real xv
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yr (SmtValue.Rational (native_mk_rational 0 1)))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_qdiv_by_zero_id
             (SmtType.FunType SmtType.Real SmtType.Real))
           xr)
         (__smtx_model_eval_qdiv_total xr yr)) := by
  rw [smt_qdiv_eval_reduction_self]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_qdiv_eval_reduction_normalized_term_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.qdiv x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq
            (SmtTerm.to_real y)
            (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv
            (SmtTerm.to_real x)
            (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv_total (SmtTerm.to_real x) (SmtTerm.to_real y)))) := by
  rw [smt_qdiv_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_134, __smtx_model_eval.eq_19,
    __smtx_model_eval.eq_3, __smtx_model_eval.eq_128,
    __smtx_model_eval.eq_129]
  rw [__smtx_model_eval.eq_19, __smtx_model_eval.eq_3]
  rw [__smtx_model_eval.eq_19]
  rw [smt_eval_to_real_idem (__smtx_model_eval M x)]
  simp [__smtx_model_eval_to_real, __smtx_model_eval_ite, __smtx_model_eval_eq,
    native_veq]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_div_eval_reduction_self
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.div x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_div_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_div_total xv yv)) := by
  rw [__smtx_model_eval.eq_24]

private theorem smt_div_eval_reduction_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.div x y))
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_div_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_div_total xv yv)) := by
  rw [smt_div_eval_reduction_self]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_div_eval_reduction_term_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.div x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Numeral 0))
          (SmtTerm.div x (SmtTerm.Numeral 0))
          (SmtTerm.div_total x y))) := by
  rw [smt_div_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_134, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_24, __smtx_model_eval.eq_30]
  cases hy : __smtx_model_eval M y <;>
    simp [__smtx_model_eval_ite, __smtx_model_eval_eq,
      __smtx_model_eval_div_total, native_veq] <;>
    try exact RuleProofs.smt_value_rel_refl _
  case Numeral n =>
    by_cases hZero : n = 0 <;>
      simp [__smtx_model_eval.eq_2, hZero] <;>
      exact RuleProofs.smt_value_rel_refl _

private theorem smt_mod_eval_reduction_self
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.mod x y) =
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_mod_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_mod_total xv yv)) := by
  rw [__smtx_model_eval.eq_25]

private theorem smt_mod_eval_reduction_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.mod x y))
      (let yv := __smtx_model_eval M y
       let xv := __smtx_model_eval M x
       __smtx_model_eval_ite
         (__smtx_model_eval_eq yv (SmtValue.Numeral 0))
         (__smtx_model_eval_apply M
           (native_model_lookup M native_mod_by_zero_id
             (SmtType.FunType SmtType.Int SmtType.Int))
           xv)
         (__smtx_model_eval_mod_total xv yv)) := by
  rw [smt_mod_eval_reduction_self]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_mod_eval_reduction_term_rel
    (M : SmtModel) (x y : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.mod x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Numeral 0))
          (SmtTerm.mod x (SmtTerm.Numeral 0))
          (SmtTerm.mod_total x y))) := by
  rw [smt_mod_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_134, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_25, __smtx_model_eval.eq_31]
  cases hy : __smtx_model_eval M y <;>
    simp [__smtx_model_eval_ite, __smtx_model_eval_eq,
      __smtx_model_eval_mod_total, native_veq] <;>
    try exact RuleProofs.smt_value_rel_refl _
  case Numeral n =>
    by_cases hZero : n = 0 <;>
      simp [__smtx_model_eval.eq_2, hZero] <;>
      exact RuleProofs.smt_value_rel_refl _

private theorem smt_abs_eval_reduction_self
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.abs x) =
      (let xv := __smtx_model_eval M x
       let zero := SmtValue.Numeral 0
       __smtx_model_eval_ite
         (__smtx_model_eval_lt xv zero)
         (__smtx_model_eval__ zero xv)
         xv) := by
  rw [__smtx_model_eval.eq_22]
  rfl

private theorem smt_abs_eval_reduction_rel
    (M : SmtModel) (x : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.abs x))
      (let xv := __smtx_model_eval M x
       let zero := SmtValue.Numeral 0
       __smtx_model_eval_ite
         (__smtx_model_eval_lt xv zero)
         (__smtx_model_eval__ zero xv)
         xv) := by
  rw [smt_abs_eval_reduction_self]
  exact RuleProofs.smt_value_rel_refl _

private theorem smt_abs_eval_reduction_term_rel
    (M : SmtModel) (x : SmtTerm) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.abs x))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.lt x (SmtTerm.Numeral 0))
          (SmtTerm.uneg x)
          x)) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [smt_abs_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_15, __smtx_model_eval.eq_2, __smtx_model_eval.eq_23]
  cases hx : __smtx_model_eval M x <;>
    simp [__smtx_model_eval_lt, __smtx_model_eval_ite, __smtx_model_eval__,
      __smtx_model_eval_uneg, __smtx_model_eval_eq, native_veq,
      native_zplus, native_zneg, native_zlt]
  case Numeral n =>
    by_cases hlt : n < 0 <;>
      simp [hlt]

private theorem rat_div_one (q : Rat) : q / (1 : Rat) = q := by
  rw [Rat.div_def]
  have hInvOne : (1 : Rat)⁻¹ = 1 := by
    native_decide
  rw [hInvOne, Rat.mul_one]

private theorem native_to_real_qdiv_total
    (n1 n2 : native_Int) :
    native_qdiv_total (native_to_real n1) (native_to_real n2) =
      native_mk_rational n1 n2 := by
  rw [native_qdiv_total, native_to_real, native_to_real, native_mk_rational,
    native_mk_rational, native_mk_rational]
  rw [Rat.div_def]
  have hInv :
      ((↑n2 / ↑(1 : Int) : Rat)⁻¹) = ((↑(1 : Int) / ↑n2 : Rat)) := by
    simpa [Rat.divInt_eq_div] using (Rat.inv_divInt n2 1)
  rw [hInv]
  simpa [Rat.divInt_eq_div, Int.mul_one, Int.one_mul] using
    (Rat.divInt_mul_divInt n1 1 (d₁ := 1) (d₂ := n2))

private theorem native_to_real_eq_zero_iff (n : native_Int) :
    native_to_real n = native_mk_rational 0 1 ↔ n = 0 := by
  unfold native_to_real native_mk_rational
  simp [rat_div_one]

private theorem native_qmult_qdiv_total_cancel
    (q1 q2 : native_Rat) (h : q2 ≠ 0) :
    native_qmult q2
      (native_qmult (native_qdiv_total q1 q2) (native_mk_rational 1 1)) =
      q1 := by
  unfold native_qmult native_qdiv_total native_mk_rational
  simp [rat_div_one]
  rw [Rat.div_def]
  rw [Rat.mul_comm q1 q2⁻¹]
  rw [← Rat.mul_assoc]
  rw [Rat.mul_inv_cancel q2 h]
  rw [Rat.one_mul]

private theorem native_to_real_qmult_mk_rational_cancel
    (n1 n2 : native_Int) (h : n2 ≠ 0) :
    native_qmult (native_to_real n2)
      (native_qmult (native_mk_rational n1 n2) (native_mk_rational 1 1)) =
      native_to_real n1 := by
  unfold native_qmult native_to_real native_mk_rational
  simp [rat_div_one]
  rw [Rat.div_def]
  rw [Rat.mul_comm (n1 : Rat) (n2 : Rat)⁻¹]
  rw [← Rat.mul_assoc]
  have hRat : (n2 : Rat) ≠ 0 := by
    exact_mod_cast h
  rw [Rat.mul_inv_cancel (n2 : Rat) hRat]
  rw [Rat.one_mul]

private theorem smt_qdiv_eval_reduction_int_term_rel
    (M : SmtModel) (x y : SmtTerm) (n1 n2 : native_Int)
    (hx : __smtx_model_eval M x = SmtValue.Numeral n1)
    (hy : __smtx_model_eval M y = SmtValue.Numeral n2) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.qdiv x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Numeral 0))
          (SmtTerm.qdiv (SmtTerm.to_real x)
            (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv_total x y))) := by
  rw [smt_qdiv_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_134, __smtx_model_eval.eq_2,
    __smtx_model_eval.eq_128, __smtx_model_eval.eq_129,
    __smtx_model_eval.eq_19, __smtx_model_eval.eq_3]
  by_cases hZero : n2 = 0
  · simp [hx, hy, hZero, __smtx_model_eval_to_real, __smtx_model_eval_eq,
      __smtx_model_eval_ite, native_veq, native_to_real_eq_zero_iff]
    exact RuleProofs.smt_value_rel_refl _
  · simp [hx, hy, hZero, __smtx_model_eval_to_real, __smtx_model_eval_eq,
      __smtx_model_eval_ite, __smtx_model_eval_qdiv_total, native_veq,
      native_to_real_eq_zero_iff, native_to_real_qdiv_total]
    exact RuleProofs.smt_value_rel_refl _

private theorem smt_qdiv_eval_reduction_real_term_rel
    (M : SmtModel) (x y : SmtTerm) (q1 q2 : native_Rat)
    (hx : __smtx_model_eval M x = SmtValue.Rational q1)
    (hy : __smtx_model_eval M y = SmtValue.Rational q2) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.qdiv x y))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq y (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv x (SmtTerm.Rational (native_mk_rational 0 1)))
          (SmtTerm.qdiv_total x y))) := by
  rw [smt_qdiv_eval_reduction_self, __smtx_model_eval.eq_133,
    __smtx_model_eval.eq_134, __smtx_model_eval.eq_3,
    __smtx_model_eval.eq_128, __smtx_model_eval.eq_129]
  by_cases hZero : q2 = native_mk_rational 0 1
  · simp [hx, hy, hZero, __smtx_model_eval_to_real, __smtx_model_eval_eq,
      __smtx_model_eval_ite, __smtx_model_eval_qdiv_total,
      __smtx_model_eval.eq_3, native_veq]
    exact RuleProofs.smt_value_rel_refl _
  · simp [hx, hy, hZero, __smtx_model_eval_to_real, __smtx_model_eval_eq,
      __smtx_model_eval_ite, __smtx_model_eval_qdiv_total,
      __smtx_model_eval.eq_3, native_veq]
    exact RuleProofs.smt_value_rel_refl _

private theorem rat_floor_remainder_nonneg (q : Rat) :
    (0 : Rat) ≤ q - (q.floor : Rat) := by
  rw [Rat.sub_eq_add_neg]
  have hFloor := Rat.floor_le q
  have hShift :
      (q.floor : Rat) + (-(q.floor : Rat)) ≤
        q + (-(q.floor : Rat)) :=
    (Rat.add_le_add_right (a := (q.floor : Rat)) (b := q)
      (c := -(q.floor : Rat))).mpr hFloor
  rwa [Rat.add_neg_cancel] at hShift

private theorem rat_floor_remainder_lt_one (q : Rat) :
    q - (q.floor : Rat) < 1 := by
  rw [Rat.sub_eq_add_neg]
  have hFloor := Rat.lt_floor_add_one q
  have hShift :
      q + (-(q.floor : Rat)) <
        ((q.floor + 1 : Int) : Rat) + (-(q.floor : Rat)) :=
    (Rat.add_lt_add_right (a := q) (b := ((q.floor + 1 : Int) : Rat))
      (c := -(q.floor : Rat))).mpr hFloor
  rw [Rat.intCast_add, Rat.intCast_one] at hShift
  rw [Rat.add_assoc] at hShift
  rw [Rat.add_comm (1 : Rat) (-(q.floor : Rat))] at hShift
  rwa [← Rat.add_assoc, Rat.add_neg_cancel, Rat.zero_add] at hShift

private theorem native_floor_remainder_nonneg (q : Rat) :
    native_qleq (native_mk_rational 0 1)
      (native_qplus q (native_qneg (native_to_real (native_to_int q)))) =
      true := by
  unfold native_qleq native_qplus native_qneg native_to_real native_to_int
    native_mk_rational
  rw [decide_eq_true_eq]
  simp [rat_div_one]
  rw [← Rat.sub_eq_add_neg]
  exact rat_floor_remainder_nonneg q

private theorem native_floor_remainder_lt_one (q : Rat) :
    native_qlt
      (native_qplus q (native_qneg (native_to_real (native_to_int q))))
      (native_mk_rational 1 1) =
      true := by
  unfold native_qlt native_qplus native_qneg native_to_real native_to_int
    native_mk_rational
  rw [decide_eq_true_eq]
  simp [rat_div_one]
  rw [← Rat.sub_eq_add_neg]
  exact rat_floor_remainder_lt_one q

private theorem typed_arith_reduction_is_int
    (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.is_int) u)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.is_int) u)) := by
  have hIsIntNN :
      term_has_non_none_type (SmtTerm.is_int (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int) (Tout := SmtType.Bool)
      (typeof_is_int_eq (__eo_to_smt u)) hIsIntNN
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
      (SmtTerm.and
        (SmtTerm.eq
          (SmtTerm.is_int (__eo_to_smt u))
          (SmtTerm.eq (__eo_to_smt u)
            (SmtTerm.to_real
              (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.leq (SmtTerm.Rational (native_mk_rational 0 1))
              (SmtTerm.neg (__eo_to_smt u)
                (SmtTerm.to_real
                  (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
            (SmtTerm.and
              (SmtTerm.lt
                (SmtTerm.neg (__eo_to_smt u)
                  (SmtTerm.to_real
                    (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u)))))
                (SmtTerm.Rational (native_mk_rational 1 1)))
              (SmtTerm.Boolean true)))
          (SmtTerm.Boolean true))) =
      SmtType.Bool
  rw [typeof_and_eq, typeof_eq_eq, typeof_is_int_eq, typeof_eq_eq,
    typeof_to_real_eq, __smtx_typeof.eq_11, typeof_to_int_eq,
    typeof_and_eq, typeof_and_eq, typeof_leq_eq, typeof_neg_eq,
    typeof_to_real_eq, __smtx_typeof.eq_11, typeof_to_int_eq,
    typeof_and_eq, typeof_lt_eq, typeof_neg_eq, typeof_to_real_eq,
    __smtx_typeof.eq_11, typeof_to_int_eq]
  simp [__smtx_typeof.eq_1, __smtx_typeof.eq_3, __smtx_typeof_eq,
    __smtx_typeof_arith_overload_op_2,
    __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
    native_ite, native_Teq, hUSmtTy]

private theorem typed_arith_reduction_to_int
    (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.to_int) u)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.to_int) u)) := by
  have hToIntNN :
      term_has_non_none_type (SmtTerm.to_int (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int) (Tout := SmtType.Int)
      (typeof_to_int_eq (__eo_to_smt u)) hToIntNN
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
      (SmtTerm.and
        (SmtTerm.eq
          (SmtTerm.to_int (__eo_to_smt u))
          (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))
        (SmtTerm.and
          (SmtTerm.and
            (SmtTerm.leq (SmtTerm.Rational (native_mk_rational 0 1))
              (SmtTerm.neg (__eo_to_smt u)
                (SmtTerm.to_real
                  (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
            (SmtTerm.and
              (SmtTerm.lt
                (SmtTerm.neg (__eo_to_smt u)
                  (SmtTerm.to_real
                    (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u)))))
                (SmtTerm.Rational (native_mk_rational 1 1)))
              (SmtTerm.Boolean true)))
          (SmtTerm.Boolean true))) =
      SmtType.Bool
  rw [typeof_and_eq, typeof_eq_eq, __smtx_typeof.eq_11, typeof_and_eq,
    typeof_and_eq, typeof_leq_eq, typeof_neg_eq, typeof_to_real_eq,
    __smtx_typeof.eq_11, typeof_to_int_eq, typeof_and_eq, typeof_lt_eq,
    typeof_neg_eq, typeof_to_real_eq, __smtx_typeof.eq_11,
    typeof_to_int_eq]
  simp [__smtx_typeof.eq_1, __smtx_typeof.eq_3, __smtx_typeof_eq,
    __smtx_typeof_arith_overload_op_2,
    __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
    native_ite, native_Teq, hUSmtTy]

private theorem typed_arith_reduction_qdiv
    (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)) := by
  have hQdivNN :
      term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv)
      (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt u) (__eo_to_smt v)) hQdivNN with
    hArgs | hArgs
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hVEoSmtTy
    unfold RuleProofs.eo_has_bool_type
    simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      native_teq, native_ite, hUEoTy, hVEoTy, __arith_mk_zero]
    change
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v))
            (SmtTerm.ite
              (SmtTerm.eq (__eo_to_smt v) (SmtTerm.Numeral 0))
              (SmtTerm.qdiv (SmtTerm.to_real (__eo_to_smt u))
                (SmtTerm.Rational (native_mk_rational 0 1)))
              (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))) =
        SmtType.Bool
    rw [typeof_eq_eq, typeof_qdiv_eq, typeof_ite_eq, typeof_eq_eq,
      typeof_qdiv_eq, typeof_to_real_eq, __smtx_typeof.eq_3,
      typeof_qdiv_total_eq, __smtx_typeof.eq_2]
    simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
      __smtx_typeof_arith_overload_op_2_ret, native_ite, native_Teq,
      hArgs.1, hArgs.2]
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hVEoSmtTy
    have hUTrans : RuleProofs.eo_has_smt_translation u := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.1]
      simp
    have hUNe : u ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
    unfold RuleProofs.eo_has_bool_type
    simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      native_teq, native_ite, hUEoTy, hVEoTy, __arith_mk_zero]
    change
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v))
            (SmtTerm.ite
              (SmtTerm.eq (__eo_to_smt v)
                (SmtTerm.Rational (native_mk_rational 0 1)))
              (SmtTerm.qdiv (__eo_to_smt u)
                (SmtTerm.Rational (native_mk_rational 0 1)))
              (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))) =
        SmtType.Bool
    rw [typeof_eq_eq, typeof_qdiv_eq, typeof_ite_eq, typeof_eq_eq,
      __smtx_typeof.eq_3, typeof_qdiv_eq, typeof_qdiv_total_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof.eq_3,
      native_ite, native_Teq,
      hArgs.1, hArgs.2]

private theorem typed_arith_reduction_qdiv_total
    (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v)) :
    RuleProofs.eo_has_bool_type
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v)) := by
  have hQdivNN :
      term_has_non_none_type
        (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total)
      (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt u) (__eo_to_smt v)) hQdivNN with
    hArgs | hArgs
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hVEoSmtTy
    have hVToRealTy :
        __eo_typeof (Term.Apply (Term.UOp UserOp.to_real) v) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_to_real (__eo_typeof v) = Term.UOp UserOp.Real
      rw [hVEoTy]
      rfl
    unfold RuleProofs.eo_has_bool_type
    simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      native_teq, native_ite, hUEoTy, hVEoTy, __eo_nil, __eo_nil_mult,
      __arith_mk_one, hVToRealTy]
    change
      __smtx_typeof
          (SmtTerm.and
            (SmtTerm.eq
              (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))
              (SmtTerm._at_purify
                (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
            (SmtTerm.and
              (SmtTerm.imp
                (SmtTerm.not
                  (SmtTerm.eq (SmtTerm.to_real (__eo_to_smt v))
                    (SmtTerm.Rational (native_mk_rational 0 1))))
                (SmtTerm.eq
                  (SmtTerm.mult (SmtTerm.to_real (__eo_to_smt v))
                    (SmtTerm.mult
                      (SmtTerm._at_purify
                        (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))
                      (SmtTerm.Rational (native_mk_rational 1 1))))
                  (SmtTerm.to_real (__eo_to_smt u))))
              (SmtTerm.Boolean true))) =
        SmtType.Bool
    rw [typeof_and_eq, typeof_eq_eq, typeof_qdiv_total_eq,
      __smtx_typeof.eq_11, typeof_and_eq, typeof_imp_eq, typeof_not_eq,
      typeof_eq_eq, typeof_to_real_eq, __smtx_typeof.eq_3,
      typeof_eq_eq, typeof_mult_eq, typeof_to_real_eq, typeof_mult_eq,
      __smtx_typeof.eq_11, typeof_qdiv_total_eq, __smtx_typeof.eq_3,
      typeof_to_real_eq, __smtx_typeof.eq_1]
    simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq, hArgs.1, hArgs.2]
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hVEoSmtTy
    have hUTrans : RuleProofs.eo_has_smt_translation u := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.1]
      simp
    have hVTrans : RuleProofs.eo_has_smt_translation v := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.2]
      simp
    have hUNe : u ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
    have hVNe : v ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation v hVTrans
    unfold RuleProofs.eo_has_bool_type
    simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
      native_teq, native_ite, hUEoTy, hVEoTy, __eo_nil, __eo_nil_mult,
      __arith_mk_one]
    change
      __smtx_typeof
          (SmtTerm.and
            (SmtTerm.eq
              (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))
              (SmtTerm._at_purify
                (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
            (SmtTerm.and
              (SmtTerm.imp
                (SmtTerm.not
                  (SmtTerm.eq (__eo_to_smt v)
                    (SmtTerm.Rational (native_mk_rational 0 1))))
                (SmtTerm.eq
                  (SmtTerm.mult (__eo_to_smt v)
                    (SmtTerm.mult
                      (SmtTerm._at_purify
                        (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))
                      (SmtTerm.Rational (native_mk_rational 1 1))))
                  (__eo_to_smt u)))
              (SmtTerm.Boolean true))) =
        SmtType.Bool
    rw [typeof_and_eq, typeof_eq_eq, typeof_qdiv_total_eq,
      __smtx_typeof.eq_11, typeof_and_eq, typeof_imp_eq, typeof_not_eq,
      typeof_eq_eq, __smtx_typeof.eq_3, typeof_eq_eq, typeof_mult_eq,
      typeof_mult_eq, __smtx_typeof.eq_11, typeof_qdiv_total_eq,
      __smtx_typeof.eq_3, __smtx_typeof.eq_1]
    simp [__smtx_typeof_eq, __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_guard,
      native_ite, native_Teq, hArgs.1, hArgs.2]

private theorem typed_arith_reduction_div
    (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
            (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) a))
          (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))) := by
  have hDivNN :
      term_has_non_none_type (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_binop_args_of_non_none (op := SmtTerm.div) (R := SmtType.Int)
      (typeof_div_eq (__eo_to_smt a) (__eo_to_smt b)) hDivNN
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b))
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt b) (SmtTerm.Numeral 0))
            (SmtTerm.div (__eo_to_smt a) (SmtTerm.Numeral 0))
            (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b)))) =
      SmtType.Bool
  rw [typeof_eq_eq, typeof_div_eq, typeof_ite_eq, typeof_eq_eq,
    typeof_div_eq, typeof_div_total_eq]
  rw [__smtx_typeof.eq_2]
  simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
    native_ite, native_Teq, hArgs.1, hArgs.2]

private theorem typed_arith_reduction_mod
    (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
            (Term.Apply (Term.UOp UserOp._at_mod_by_zero) a))
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))) := by
  have hModNN :
      term_has_non_none_type (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  have hArgs :
      __smtx_typeof (__eo_to_smt a) = SmtType.Int ∧
        __smtx_typeof (__eo_to_smt b) = SmtType.Int :=
    int_binop_args_of_non_none (op := SmtTerm.mod) (R := SmtType.Int)
      (typeof_mod_eq (__eo_to_smt a) (__eo_to_smt b)) hModNN
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b))
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt b) (SmtTerm.Numeral 0))
            (SmtTerm.mod (__eo_to_smt a) (SmtTerm.Numeral 0))
            (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b)))) =
      SmtType.Bool
  rw [typeof_eq_eq, typeof_mod_eq, typeof_ite_eq, typeof_eq_eq,
    typeof_mod_eq, typeof_mod_total_eq]
  rw [__smtx_typeof.eq_2]
  simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
    native_ite, native_Teq, hArgs.1, hArgs.2]

private theorem typed_arith_reduction_abs
    (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.abs) u)) :
    RuleProofs.eo_has_bool_type
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.abs) u))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt) u)
                (__arith_mk_zero (__eo_typeof u))))
            (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
          u)) := by
  have hAbsNN :
      term_has_non_none_type (SmtTerm.abs (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Int :=
    int_arg_of_non_none hAbsNN
  have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
    TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hUSmtTy (by simp)
  have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
  have hZero :
      __eo_to_smt (__arith_mk_zero (__eo_typeof u)) = SmtTerm.Numeral 0 := by
    rw [hUEoTy]
    rfl
  unfold RuleProofs.eo_has_bool_type
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.abs (__eo_to_smt u))
          (SmtTerm.ite
            (SmtTerm.lt (__eo_to_smt u)
              (__eo_to_smt (__arith_mk_zero (__eo_typeof u))))
            (SmtTerm.uneg (__eo_to_smt u))
            (__eo_to_smt u))) =
      SmtType.Bool
  rw [hZero]
  rw [typeof_eq_eq, typeof_abs_eq, typeof_ite_eq, typeof_lt_eq, typeof_uneg_eq]
  rw [__smtx_typeof.eq_2]
  simp [__smtx_typeof_eq, __smtx_typeof_ite, __smtx_typeof_guard,
    __smtx_typeof_arith_overload_op_1, __smtx_typeof_arith_overload_op_2_ret,
    native_ite, native_Teq, hUSmtTy]

private theorem facts_arith_reduction_is_int
    (M : SmtModel) (hM : model_total_typed M) (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.is_int) u)) :
    eo_interprets M
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.is_int) u))
      true := by
  have hBool := typed_arith_reduction_is_int u hTrans
  have hIsIntNN :
      term_has_non_none_type (SmtTerm.is_int (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int) (Tout := SmtType.Bool)
      (typeof_is_int_eq (__eo_to_smt u)) hIsIntNN
  have hEvalUTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
        SmtType.Real :=
    smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Real hUSmtTy
      (by simp) type_inhabited_real
  rcases real_value_canonical hEvalUTy with ⟨q, hEvalU⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M _ ?_ ?_
  · simpa [RuleProofs.eo_has_bool_type] using hBool
  · change
      __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.eq
            (SmtTerm.is_int (__eo_to_smt u))
            (SmtTerm.eq (__eo_to_smt u)
              (SmtTerm.to_real
                (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
          (SmtTerm.and
            (SmtTerm.and
              (SmtTerm.leq (SmtTerm.Rational (native_mk_rational 0 1))
                (SmtTerm.neg (__eo_to_smt u)
                  (SmtTerm.to_real
                    (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
              (SmtTerm.and
                (SmtTerm.lt
                  (SmtTerm.neg (__eo_to_smt u)
                    (SmtTerm.to_real
                      (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u)))))
                  (SmtTerm.Rational (native_mk_rational 1 1)))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean true))) =
        SmtValue.Boolean true
    simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
      __smtx_model_eval.eq_8, __smtx_model_eval.eq_11,
      __smtx_model_eval.eq_13, __smtx_model_eval.eq_15,
      __smtx_model_eval.eq_16, __smtx_model_eval.eq_19,
      __smtx_model_eval.eq_20, __smtx_model_eval.eq_21,
      __smtx_model_eval.eq_134, hEvalU, __smtx_model_eval__at_purify,
      __smtx_model_eval_to_int, __smtx_model_eval_to_real,
      __smtx_model_eval_is_int, __smtx_model_eval_eq,
      __smtx_model_eval__, __smtx_model_eval_leq, __smtx_model_eval_lt,
      __smtx_model_eval_and, native_veq, native_floor_remainder_nonneg,
      native_floor_remainder_lt_one, native_and, eq_comm]

private theorem facts_arith_reduction_to_int
    (M : SmtModel) (hM : model_total_typed M) (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.to_int) u)) :
    eo_interprets M
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.to_int) u))
      true := by
  have hBool := typed_arith_reduction_to_int u hTrans
  have hToIntNN :
      term_has_non_none_type (SmtTerm.to_int (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int) (Tout := SmtType.Int)
      (typeof_to_int_eq (__eo_to_smt u)) hToIntNN
  have hEvalUTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
        SmtType.Real :=
    smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Real hUSmtTy
      (by simp) type_inhabited_real
  rcases real_value_canonical hEvalUTy with ⟨q, hEvalU⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M _ ?_ ?_
  · simpa [RuleProofs.eo_has_bool_type] using hBool
  · change
      __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.eq
            (SmtTerm.to_int (__eo_to_smt u))
            (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))
          (SmtTerm.and
            (SmtTerm.and
              (SmtTerm.leq (SmtTerm.Rational (native_mk_rational 0 1))
                (SmtTerm.neg (__eo_to_smt u)
                  (SmtTerm.to_real
                    (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u))))))
              (SmtTerm.and
                (SmtTerm.lt
                  (SmtTerm.neg (__eo_to_smt u)
                    (SmtTerm.to_real
                      (SmtTerm._at_purify (SmtTerm.to_int (__eo_to_smt u)))))
                  (SmtTerm.Rational (native_mk_rational 1 1)))
                (SmtTerm.Boolean true)))
            (SmtTerm.Boolean true))) =
        SmtValue.Boolean true
    simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
      __smtx_model_eval.eq_8, __smtx_model_eval.eq_11,
      __smtx_model_eval.eq_13, __smtx_model_eval.eq_15,
      __smtx_model_eval.eq_16, __smtx_model_eval.eq_19,
      __smtx_model_eval.eq_20, __smtx_model_eval.eq_134,
      hEvalU, __smtx_model_eval__at_purify,
      __smtx_model_eval_to_int, __smtx_model_eval_to_real,
      __smtx_model_eval_eq, __smtx_model_eval__,
      __smtx_model_eval_leq, __smtx_model_eval_lt, __smtx_model_eval_and,
      native_veq, native_floor_remainder_nonneg,
      native_floor_remainder_lt_one, native_and]

private theorem facts_arith_reduction_qdiv
    (M : SmtModel) (hM : model_total_typed M) (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v))
      true := by
  have hBool := typed_arith_reduction_qdiv u v hTrans
  have hQdivNN :
      term_has_non_none_type (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv)
      (R := SmtType.Real)
      (typeof_qdiv_eq (__eo_to_smt u) (__eo_to_smt v)) hQdivNN with
    hArgs | hArgs
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hVEoSmtTy
    have hEvalUTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
          SmtType.Int :=
      smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Int
        hArgs.1 (by simp) type_inhabited_int
    have hEvalVTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt v)) =
          SmtType.Int :=
      smt_model_eval_preserves_type M hM (__eo_to_smt v) SmtType.Int
        hArgs.2 (by simp) type_inhabited_int
    rcases int_value_canonical hEvalUTy with ⟨n1, hEvalU⟩
    rcases int_value_canonical hEvalVTy with ⟨n2, hEvalV⟩
    have hPred :
        __arith_reduction_pred
            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v) =
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v))
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.ite)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) v)
                    (Term.Numeral 0)))
                (Term.Apply (Term.UOp UserOp._at_div_by_zero)
                  (Term.Apply (Term.UOp UserOp.to_real) u)))
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))) := by
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
        native_teq, native_ite, hUEoTy, hVEoTy, __arith_mk_zero]
    rw [hPred]
    apply RuleProofs.eo_interprets_eq_of_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) v)
              (Term.Numeral 0)))
          (Term.Apply (Term.UOp UserOp._at_div_by_zero)
            (Term.Apply (Term.UOp UserOp.to_real) u)))
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))
    · simpa [hPred] using hBool
    · change RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v)))
        (__smtx_model_eval M
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt v) (SmtTerm.Numeral 0))
            (SmtTerm.qdiv (SmtTerm.to_real (__eo_to_smt u))
              (SmtTerm.Rational (native_mk_rational 0 1)))
            (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
      exact smt_qdiv_eval_reduction_int_term_rel M
        (__eo_to_smt u) (__eo_to_smt v) n1 n2 hEvalU hEvalV
  · have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hVEoSmtTy
    have hEvalUTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
          SmtType.Real :=
      smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Real
        hArgs.1 (by simp) type_inhabited_real
    have hEvalVTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt v)) =
          SmtType.Real :=
      smt_model_eval_preserves_type M hM (__eo_to_smt v) SmtType.Real
        hArgs.2 (by simp) type_inhabited_real
    rcases real_value_canonical hEvalUTy with ⟨q1, hEvalU⟩
    rcases real_value_canonical hEvalVTy with ⟨q2, hEvalV⟩
    have hUTrans : RuleProofs.eo_has_smt_translation u := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.1]
      simp
    have hUNe : u ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
    have hPred :
        __arith_reduction_pred
            (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v) =
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v))
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.ite)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.eq) v)
                    (Term.Rational (native_mk_rational 0 1))))
                (Term.Apply (Term.UOp UserOp._at_div_by_zero) u))
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))) := by
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
        native_teq, native_ite, hUEoTy, hVEoTy, __arith_mk_zero]
    rw [hPred]
    apply RuleProofs.eo_interprets_eq_of_rel M
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) v)
              (Term.Rational (native_mk_rational 0 1))))
          (Term.Apply (Term.UOp UserOp._at_div_by_zero) u))
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))
    · simpa [hPred] using hBool
    · change RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.qdiv (__eo_to_smt u) (__eo_to_smt v)))
        (__smtx_model_eval M
          (SmtTerm.ite
            (SmtTerm.eq (__eo_to_smt v)
              (SmtTerm.Rational (native_mk_rational 0 1)))
            (SmtTerm.qdiv (__eo_to_smt u)
              (SmtTerm.Rational (native_mk_rational 0 1)))
            (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
      exact smt_qdiv_eval_reduction_real_term_rel M
        (__eo_to_smt u) (__eo_to_smt v) q1 q2 hEvalU hEvalV

private theorem facts_arith_reduction_qdiv_total
    (M : SmtModel) (hM : model_total_typed M) (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v)) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))
      true := by
  have hBool := typed_arith_reduction_qdiv_total u v hTrans
  have hQdivNN :
      term_has_non_none_type
        (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total)
      (R := SmtType.Real)
      (typeof_qdiv_total_eq (__eo_to_smt u) (__eo_to_smt v)) hQdivNN with
    hArgs | hArgs
  · have hEvalUTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
          SmtType.Int := by
      exact smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Int
        hArgs.1 (by simp) type_inhabited_int
    have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Int :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Int :=
      TranslationProofs.eo_to_smt_type_eq_int hVEoSmtTy
    have hVToRealTy :
        __eo_typeof (Term.Apply (Term.UOp UserOp.to_real) v) =
          Term.UOp UserOp.Real := by
      change __eo_typeof_to_real (__eo_typeof v) = Term.UOp UserOp.Real
      rw [hVEoTy]
      rfl
    have hEvalVTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt v)) =
          SmtType.Int :=
      smt_model_eval_preserves_type M hM (__eo_to_smt v) SmtType.Int
        hArgs.2 (by simp) type_inhabited_int
    rcases int_value_canonical hEvalUTy with ⟨n1, hEvalU⟩
    rcases int_value_canonical hEvalVTy with ⟨n2, hEvalV⟩
    rw [RuleProofs.eo_interprets_iff_smt_interprets]
    refine smt_interprets.intro_true M _ ?_ ?_
    · simpa [RuleProofs.eo_has_bool_type] using hBool
    · change
        __smtx_model_eval M (__eo_to_smt
            (__arith_reduction_pred
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))) =
          SmtValue.Boolean true
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
        native_teq, native_ite, hUEoTy, hVEoTy, __eo_nil, __eo_nil_mult,
        __arith_mk_one, hVToRealTy]
      change
        __smtx_model_eval M
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))
                (SmtTerm._at_purify
                  (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
              (SmtTerm.and
                (SmtTerm.imp
                  (SmtTerm.not
                    (SmtTerm.eq (SmtTerm.to_real (__eo_to_smt v))
                      (SmtTerm.Rational (native_mk_rational 0 1))))
                  (SmtTerm.eq
                    (SmtTerm.mult (SmtTerm.to_real (__eo_to_smt v))
                      (SmtTerm.mult
                        (SmtTerm._at_purify
                          (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))
                        (SmtTerm.Rational (native_mk_rational 1 1))))
                    (SmtTerm.to_real (__eo_to_smt u))))
                (SmtTerm.Boolean true))) =
          SmtValue.Boolean true
      by_cases hZero : n2 = 0
      · simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
          __smtx_model_eval.eq_6, __smtx_model_eval.eq_8,
          __smtx_model_eval.eq_9, __smtx_model_eval.eq_11,
          __smtx_model_eval.eq_14, __smtx_model_eval.eq_19,
          __smtx_model_eval.eq_129, __smtx_model_eval.eq_134,
          hEvalU, hEvalV, hZero, __smtx_model_eval__at_purify,
          __smtx_model_eval_to_real, __smtx_model_eval_qdiv_total,
          __smtx_model_eval_mult, __smtx_model_eval_eq,
          __smtx_model_eval_not, __smtx_model_eval_or,
          __smtx_model_eval_imp, __smtx_model_eval_and, native_veq,
          native_not, native_or, native_and, native_to_real_eq_zero_iff]
      · have hCancel :
          native_qmult (native_to_real n2)
            (native_qmult (native_mk_rational n1 n2)
              (native_mk_rational 1 1)) =
            native_to_real n1 :=
          native_to_real_qmult_mk_rational_cancel n1 n2 hZero
        simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
          __smtx_model_eval.eq_6, __smtx_model_eval.eq_8,
          __smtx_model_eval.eq_9, __smtx_model_eval.eq_11,
          __smtx_model_eval.eq_14, __smtx_model_eval.eq_19,
          __smtx_model_eval.eq_129, __smtx_model_eval.eq_134,
          hEvalU, hEvalV, hZero, hCancel, __smtx_model_eval__at_purify,
          __smtx_model_eval_to_real, __smtx_model_eval_qdiv_total,
          __smtx_model_eval_mult, __smtx_model_eval_eq,
          __smtx_model_eval_not, __smtx_model_eval_or,
          __smtx_model_eval_imp, __smtx_model_eval_and, native_veq,
          native_not, native_or, native_and, native_to_real_eq_zero_iff]
  · have hEvalUTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt u)) =
          SmtType.Real := by
      exact smt_model_eval_preserves_type M hM (__eo_to_smt u) SmtType.Real
        hArgs.1 (by simp) type_inhabited_real
    have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hArgs.1 (by simp)
    have hVEoSmtTy : __eo_to_smt_type (__eo_typeof v) = SmtType.Real :=
      TranslationProofs.eo_to_smt_type_typeof_of_smt_type v hArgs.2 (by simp)
    have hUEoTy : __eo_typeof u = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hUEoSmtTy
    have hVEoTy : __eo_typeof v = Term.UOp UserOp.Real :=
      TranslationProofs.eo_to_smt_type_eq_real hVEoSmtTy
    have hUTrans : RuleProofs.eo_has_smt_translation u := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.1]
      simp
    have hVTrans : RuleProofs.eo_has_smt_translation v := by
      unfold RuleProofs.eo_has_smt_translation
      rw [hArgs.2]
      simp
    have hUNe : u ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
    have hVNe : v ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation v hVTrans
    have hEvalVTy :
        __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt v)) =
          SmtType.Real :=
      smt_model_eval_preserves_type M hM (__eo_to_smt v) SmtType.Real
        hArgs.2 (by simp) type_inhabited_real
    rcases real_value_canonical hEvalUTy with ⟨q1, hEvalU⟩
    rcases real_value_canonical hEvalVTy with ⟨q2, hEvalV⟩
    rw [RuleProofs.eo_interprets_iff_smt_interprets]
    refine smt_interprets.intro_true M _ ?_ ?_
    · simpa [RuleProofs.eo_has_bool_type] using hBool
    · change
        __smtx_model_eval M (__eo_to_smt
            (__arith_reduction_pred
              (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))) =
          SmtValue.Boolean true
      simp [__arith_reduction_pred, __eo_mk_apply, __eo_eq, __eo_ite,
        native_teq, native_ite, hUEoTy, hVEoTy, __eo_nil, __eo_nil_mult,
        __arith_mk_one]
      change
        __smtx_model_eval M
            (SmtTerm.and
              (SmtTerm.eq
                (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))
                (SmtTerm._at_purify
                  (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v))))
              (SmtTerm.and
                (SmtTerm.imp
                  (SmtTerm.not
                    (SmtTerm.eq (__eo_to_smt v)
                      (SmtTerm.Rational (native_mk_rational 0 1))))
                  (SmtTerm.eq
                    (SmtTerm.mult (__eo_to_smt v)
                      (SmtTerm.mult
                        (SmtTerm._at_purify
                          (SmtTerm.qdiv_total (__eo_to_smt u) (__eo_to_smt v)))
                        (SmtTerm.Rational (native_mk_rational 1 1))))
                    (__eo_to_smt u)))
                (SmtTerm.Boolean true))) =
          SmtValue.Boolean true
      by_cases hZero : q2 = native_mk_rational 0 1
      · simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
          __smtx_model_eval.eq_6, __smtx_model_eval.eq_8,
          __smtx_model_eval.eq_9, __smtx_model_eval.eq_11,
          __smtx_model_eval.eq_14, __smtx_model_eval.eq_129,
          __smtx_model_eval.eq_134, hEvalU, hEvalV, hZero,
          __smtx_model_eval__at_purify, __smtx_model_eval_qdiv_total,
          __smtx_model_eval_mult, __smtx_model_eval_eq,
          __smtx_model_eval_not, __smtx_model_eval_or,
          __smtx_model_eval_imp, __smtx_model_eval_and, native_veq,
          native_not, native_or, native_and]
      · have hNZ : q2 ≠ 0 := by
          intro hQ2
          apply hZero
          rw [hQ2]
          unfold native_mk_rational
          simp [rat_div_one]
        have hCancel :
            native_qmult q2
              (native_qmult (native_qdiv_total q1 q2)
                (native_mk_rational 1 1)) =
              q1 :=
          native_qmult_qdiv_total_cancel q1 q2 hNZ
        simp [__smtx_model_eval.eq_1, __smtx_model_eval.eq_3,
          __smtx_model_eval.eq_6, __smtx_model_eval.eq_8,
          __smtx_model_eval.eq_9, __smtx_model_eval.eq_11,
          __smtx_model_eval.eq_14, __smtx_model_eval.eq_129,
          __smtx_model_eval.eq_134, hEvalU, hEvalV, hZero, hCancel,
          __smtx_model_eval__at_purify, __smtx_model_eval_qdiv_total,
          __smtx_model_eval_mult, __smtx_model_eval_eq,
          __smtx_model_eval_not, __smtx_model_eval_or,
          __smtx_model_eval_imp, __smtx_model_eval_and, native_veq,
          native_not, native_or, native_and]

private theorem facts_arith_reduction_div
    (M : SmtModel) (a b : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
              (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) a))
            (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
            (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) a))
          (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)))
      true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
        (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) a))
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b))
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.div (__eo_to_smt a) (__eo_to_smt b)))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt b) (SmtTerm.Numeral 0))
          (SmtTerm.div (__eo_to_smt a) (SmtTerm.Numeral 0))
          (SmtTerm.div_total (__eo_to_smt a) (__eo_to_smt b))))
    exact smt_div_eval_reduction_term_rel M (__eo_to_smt a) (__eo_to_smt b)

private theorem facts_arith_reduction_mod
    (M : SmtModel) (a b : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
              (Term.Apply (Term.UOp UserOp._at_mod_by_zero) a))
            (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
            (Term.Apply (Term.UOp UserOp._at_mod_by_zero) a))
          (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)))
      true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
        (Term.Apply (Term.UOp UserOp._at_mod_by_zero) a))
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b))
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.mod (__eo_to_smt a) (__eo_to_smt b)))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt b) (SmtTerm.Numeral 0))
          (SmtTerm.mod (__eo_to_smt a) (SmtTerm.Numeral 0))
          (SmtTerm.mod_total (__eo_to_smt a) (__eo_to_smt b))))
    exact smt_mod_eval_reduction_term_rel M (__eo_to_smt a) (__eo_to_smt b)

private theorem facts_arith_reduction_abs
    (M : SmtModel) (u : Term)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.abs) u))
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.lt) u)
                  (__arith_mk_zero (__eo_typeof u))))
              (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
            u))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp UserOp.abs) u))
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt) u)
                (__arith_mk_zero (__eo_typeof u))))
            (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
          u))
      true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
    (Term.Apply (Term.UOp UserOp.abs) u)
    (Term.Apply
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.ite)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.lt) u)
            (__arith_mk_zero (__eo_typeof u))))
        (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
      u)
  · exact hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (SmtTerm.abs (__eo_to_smt u)))
      (__smtx_model_eval M
        (SmtTerm.ite
          (SmtTerm.lt (__eo_to_smt u) (__eo_to_smt (__arith_mk_zero (__eo_typeof u))))
          (SmtTerm.uneg (__eo_to_smt u))
          (__eo_to_smt u)))
    have hZero :
        __eo_to_smt (__arith_mk_zero (__eo_typeof u)) = SmtTerm.Numeral 0 := by
      rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp UserOp.abs) u)
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.ite)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.lt) u)
                (__arith_mk_zero (__eo_typeof u))))
            (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
          u)
        hBool with ⟨_hSame, hAbsNonNone⟩
      have hAbsNN :
          term_has_non_none_type (SmtTerm.abs (__eo_to_smt u)) := by
        unfold term_has_non_none_type
        simpa using hAbsNonNone
      have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Int :=
        int_arg_of_non_none hAbsNN
      have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
        TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hUSmtTy (by simp)
      have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
        TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
      rw [hUEoTy]
      rfl
    rw [hZero]
    exact smt_abs_eval_reduction_term_rel M (__eo_to_smt u)

private theorem facts_arith_reduction_qdiv_of_trans
    (M : SmtModel) (hM : model_total_typed M) (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v)) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) u) v))
      true := by
  exact facts_arith_reduction_qdiv M hM u v hTrans

private theorem facts_arith_reduction_qdiv_total_of_trans
    (M : SmtModel) (hM : model_total_typed M) (u v : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v)) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) u) v))
      true := by
  exact facts_arith_reduction_qdiv_total M hM u v hTrans

private theorem facts_arith_reduction_div_of_trans
    (M : SmtModel) (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b)) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
      true := by
  change eo_interprets M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) a) b))
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
          (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) a))
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) a) b)))
    true
  exact facts_arith_reduction_div M a b
    (typed_arith_reduction_div a b hTrans)

private theorem facts_arith_reduction_mod_of_trans
    (M : SmtModel) (a b : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b)) :
    eo_interprets M
      (__arith_reduction_pred
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
      true := by
  change eo_interprets M
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) a) b))
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.ite)
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) b) (Term.Numeral 0)))
          (Term.Apply (Term.UOp UserOp._at_mod_by_zero) a))
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) a) b)))
    true
  exact facts_arith_reduction_mod M a b
    (typed_arith_reduction_mod a b hTrans)

private theorem facts_arith_reduction_abs_of_trans
    (M : SmtModel) (u : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.abs) u)) :
    eo_interprets M
      (__arith_reduction_pred (Term.Apply (Term.UOp UserOp.abs) u))
      true := by
  have hAbsNN :
      term_has_non_none_type (SmtTerm.abs (__eo_to_smt u)) := by
    unfold RuleProofs.eo_has_smt_translation at hTrans
    unfold term_has_non_none_type
    simpa using hTrans
  have hUSmtTy : __smtx_typeof (__eo_to_smt u) = SmtType.Int :=
    int_arg_of_non_none hAbsNN
  have hUEoSmtTy : __eo_to_smt_type (__eo_typeof u) = SmtType.Int :=
    TranslationProofs.eo_to_smt_type_typeof_of_smt_type u hUSmtTy (by simp)
  have hUEoTy : __eo_typeof u = Term.UOp UserOp.Int :=
    TranslationProofs.eo_to_smt_type_eq_int hUEoSmtTy
  have hUTrans : RuleProofs.eo_has_smt_translation u := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hUSmtTy]
    simp
  have hUNe : u ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation u hUTrans
  have hPred :
      __arith_reduction_pred (Term.Apply (Term.UOp UserOp.abs) u) =
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.abs) u))
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.ite)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.lt) u)
                  (__arith_mk_zero (__eo_typeof u))))
              (Term.Apply (Term.UOp UserOp.__eoo_neg_2) u))
            u)) := by
    simp [__arith_reduction_pred, __eo_mk_apply, hUEoTy, __arith_mk_zero]
  rw [hPred]
  exact facts_arith_reduction_abs M u
    (typed_arith_reduction_abs u hTrans)

theorem cmd_step_arith_reduction_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.arith_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.arith_reduction args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.arith_reduction args premises) :=
by
  sorry
