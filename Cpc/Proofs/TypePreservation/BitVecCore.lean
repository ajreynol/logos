import Cpc.Proofs.TypePreservation.BitVecPrep

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

theorem typeof_value_model_eval_concat
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2) := by
  rcases bv_concat_args_of_non_none ht with ⟨w1, w2, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2) =
      SmtType.BitVec (smt_lit_zplus w1 w2) by
    simp [__smtx_typeof, __smtx_typeof_concat, h1, h2]]
  change __smtx_typeof_value
      (__smtx_model_eval_concat (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus w1 w2)
  rcases bitvec_value_canonical (by simpa [h1] using hpres1) with ⟨n1, hv1⟩
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hv2⟩
  rw [hv1, hv2]
  have hWidth1 : smt_lit_zleq 0 w1 = true := by
    exact bitvec_width_nonneg (by simpa [h1, hv1] using hpres1)
  have hWidth2 : smt_lit_zleq 0 w2 = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv2] using hpres2)
  have hw1 : 0 <= w1 := by
    simpa [SmtEval.smt_lit_zleq] using hWidth1
  have hw2 : 0 <= w2 := by
    simpa [SmtEval.smt_lit_zleq] using hWidth2
  have hWidth : smt_lit_zleq 0 (smt_lit_zplus w1 w2) = true := by
    have hAdd : 0 <= w1 + w2 := Int.add_nonneg hw1 hw2
    simpa [SmtEval.smt_lit_zleq, SmtEval.smt_lit_zplus] using hAdd
  simpa [__smtx_model_eval_concat] using
    typeof_value_binary_of_nonneg (smt_lit_zplus w1 w2)
      (smt_lit_mod_total (smt_lit_binary_concat w1 n1 w2 n2)
        (smt_lit_int_pow2 (smt_lit_zplus w1 w2))) hWidth

theorem typeof_value_model_eval_extract
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht : term_has_non_none_type
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3))
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3) := by
  rcases extract_args_of_non_none ht with ⟨i, j, w, h1, h2, h3, hj0, hji, hiw⟩
  have hWidthEq :
      smt_lit_zplus (smt_lit_zplus i (smt_lit_zneg j)) 1 =
        smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j) := by
    simp [SmtEval.smt_lit_zplus, SmtEval.smt_lit_zneg, Int.add_assoc, Int.add_comm, Int.add_left_comm]
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3) =
        SmtType.BitVec (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j)) by
    rw [typeof_extract_eq, h1, h2, h3]
    simp [__smtx_typeof_extract, smt_lit_ite, hj0, hji, hiw, hWidthEq]]
  change __smtx_typeof_value
      (__smtx_model_eval_extract (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) =
    SmtType.BitVec (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j))
  rw [h1, h2]
  change __smtx_typeof_value
      (__smtx_model_eval_extract (SmtValue.Numeral i) (SmtValue.Numeral j)
        (__smtx_model_eval M t3)) =
    SmtType.BitVec (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j))
  rcases bitvec_value_canonical (by simpa [h3] using hpres3) with ⟨n, hv⟩
  rw [hv]
  have hji' : j <= i := by
    simpa [SmtEval.smt_lit_zleq] using hji
  have hWidthInt : 0 <= (i + 1) + -j := by
    have hsub : 0 <= i - j := (Int.sub_nonneg).2 hji'
    have hWidth' : 0 <= (i - j) + 1 := Int.add_nonneg hsub (by decide)
    simpa [Int.sub_eq_add_neg, Int.add_assoc, Int.add_comm, Int.add_left_comm] using hWidth'
  have hWidth : smt_lit_zleq 0 (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j)) = true := by
    have hWidthInt' : 0 <= smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j) := by
      simpa [SmtEval.smt_lit_zplus, SmtEval.smt_lit_zneg] using hWidthInt
    simpa [SmtEval.smt_lit_zleq] using hWidthInt'
  simpa [__smtx_model_eval_extract] using
    typeof_value_binary_of_nonneg (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j))
      (smt_lit_mod_total (smt_lit_binary_extract w n i j)
        (smt_lit_int_pow2 (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j)))) hWidth

theorem typeof_value_model_eval_bv_unop
    (M : SmtModel)
    (op : SmtTerm)
    (eval : SmtValue -> SmtValue)
    (t : SmtTerm)
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        __smtx_typeof_bv_op_1 (__smtx_typeof t))
    (hEvalTerm :
      __smtx_model_eval M (SmtTerm.Apply op t) = eval (__smtx_model_eval M t))
    (ht : term_has_non_none_type (SmtTerm.Apply op t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t)
    (hEvalTy :
      ∀ w n, smt_lit_zleq 0 w = true ->
        __smtx_typeof_value (eval (SmtValue.Binary w n)) = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply op t)) =
      __smtx_typeof (SmtTerm.Apply op t) := by
  rcases bv_unop_arg_of_non_none hTy ht with ⟨w, hArg⟩
  rw [hEvalTerm]
  rw [show __smtx_typeof (SmtTerm.Apply op t) = SmtType.BitVec w by
    simp [hTy, __smtx_typeof_bv_op_1, hArg]]
  rcases bitvec_value_canonical (by simpa [hArg] using hpres) with ⟨n, hv⟩
  rw [hv]
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [hArg, hv] using hpres)
  simpa using hEvalTy w n hWidth

theorem typeof_value_model_eval_bv_unop_ret
    (M : SmtModel)
    (op : SmtTerm)
    (eval : SmtValue -> SmtValue)
    (ret : SmtType)
    (t : SmtTerm)
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        __smtx_typeof_bv_op_1_ret (__smtx_typeof t) ret)
    (hEvalTerm :
      __smtx_model_eval M (SmtTerm.Apply op t) = eval (__smtx_model_eval M t))
    (ht : term_has_non_none_type (SmtTerm.Apply op t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t)
    (hEvalTy :
      ∀ w n, smt_lit_zleq 0 w = true ->
        __smtx_typeof_value (eval (SmtValue.Binary w n)) = ret) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply op t)) =
      __smtx_typeof (SmtTerm.Apply op t) := by
  rcases bv_unop_ret_arg_of_non_none hTy ht with ⟨w, hArg⟩
  rw [hEvalTerm]
  rw [show __smtx_typeof (SmtTerm.Apply op t) = ret by
    simp [hTy, __smtx_typeof_bv_op_1_ret, hArg]]
  rcases bitvec_value_canonical (by simpa [hArg] using hpres) with ⟨n, hv⟩
  rw [hv]
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [hArg, hv] using hpres)
  simpa using hEvalTy w n hWidth

theorem typeof_value_model_eval_bv_binop
    (M : SmtModel)
    (op : SmtTerm)
    (eval : SmtValue -> SmtValue -> SmtValue)
    (t1 t2 : SmtTerm)
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (hEvalTerm :
      __smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        eval (__smtx_model_eval M t1) (__smtx_model_eval M t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hEvalTy :
      ∀ w n1 n2, smt_lit_zleq 0 w = true ->
        __smtx_typeof_value (eval (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
          SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) := by
  rcases bv_binop_args_of_non_none hTy ht with ⟨w, h1, h2⟩
  rw [hEvalTerm]
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) = SmtType.BitVec w by
    simp [hTy, __smtx_typeof_bv_op_2, smt_lit_ite, SmtEval.smt_lit_zeq, h1, h2]]
  rcases bitvec_value_canonical (by simpa [h1] using hpres1) with ⟨n1, hv1⟩
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hv2⟩
  rw [hv1, hv2]
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h1, hv1] using hpres1)
  simpa using hEvalTy w n1 n2 hWidth

theorem typeof_value_model_eval_bv_binop_ret
    (M : SmtModel)
    (op : SmtTerm)
    (eval : SmtValue -> SmtValue -> SmtValue)
    (ret : SmtType)
    (t1 t2 : SmtTerm)
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (hEvalTerm :
      __smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        eval (__smtx_model_eval M t1) (__smtx_model_eval M t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hEvalTy :
      ∀ w n1 n2, smt_lit_zleq 0 w = true ->
        __smtx_typeof_value (eval (SmtValue.Binary w n1) (SmtValue.Binary w n2)) = ret) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) := by
  rcases bv_binop_ret_args_of_non_none hTy ht with ⟨w, h1, h2⟩
  rw [hEvalTerm]
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) = ret by
    simp [hTy, __smtx_typeof_bv_op_2_ret, smt_lit_ite, SmtEval.smt_lit_zeq, h1, h2]]
  rcases bitvec_value_canonical (by simpa [h1] using hpres1) with ⟨n1, hv1⟩
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hv2⟩
  rw [hv1, hv2]
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h1, hv1] using hpres1)
  simpa using hEvalTy w n1 n2 hWidth

theorem typeof_value_model_eval_bvcomp_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvcomp (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec 1 := by
  unfold __smtx_model_eval_bvcomp
  have hEq :
      __smtx_typeof_value (__smtx_model_eval_eq (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
        SmtType.Bool := by
    exact typeof_value_model_eval_eq_value _ _
  rcases bool_value_canonical hEq with ⟨b, hb⟩
  rw [hb]
  cases b <;> simp [__smtx_model_eval_ite, __smtx_typeof_value, smt_lit_ite, SmtEval.smt_lit_zleq]

theorem typeof_value_model_eval_bvugt_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvugt (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  simp [__smtx_model_eval_bvugt, __smtx_typeof_value]

theorem typeof_value_model_eval_bvuge_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvuge (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  unfold __smtx_model_eval_bvuge
  have h1 :
      __smtx_typeof_value (__smtx_model_eval_bvugt (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
        SmtType.Bool := by
    exact typeof_value_model_eval_bvugt_value w n1 n2 hWidth
  have h2 :
      __smtx_typeof_value (__smtx_model_eval_eq (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
        SmtType.Bool := by
    exact typeof_value_model_eval_eq_value _ _
  rcases bool_value_canonical h1 with ⟨b1, hb1⟩
  rcases bool_value_canonical h2 with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_or, __smtx_typeof_value]

theorem typeof_value_model_eval_ite_of_bool
    {c t e : SmtValue}
    {T : SmtType}
    (hc : __smtx_typeof_value c = SmtType.Bool)
    (ht : __smtx_typeof_value t = T)
    (he : __smtx_typeof_value e = T) :
    __smtx_typeof_value (__smtx_model_eval_ite c t e) = T := by
  rcases bool_value_canonical hc with ⟨b, hb⟩
  rw [hb]
  cases b
  · simpa [__smtx_model_eval_ite] using he
  · simpa [__smtx_model_eval_ite] using ht

theorem typeof_value_model_eval_not_of_bool
    {v : SmtValue}
    (hv : __smtx_typeof_value v = SmtType.Bool) :
    __smtx_typeof_value (__smtx_model_eval_not v) = SmtType.Bool := by
  rcases bool_value_canonical hv with ⟨b, hb⟩
  rw [hb]
  simp [__smtx_model_eval_not, __smtx_typeof_value]

theorem typeof_value_model_eval_and_of_bool
    {v1 v2 : SmtValue}
    (h1 : __smtx_typeof_value v1 = SmtType.Bool)
    (h2 : __smtx_typeof_value v2 = SmtType.Bool) :
    __smtx_typeof_value (__smtx_model_eval_and v1 v2) = SmtType.Bool := by
  rcases bool_value_canonical h1 with ⟨b1, hb1⟩
  rcases bool_value_canonical h2 with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_and, __smtx_typeof_value]

theorem typeof_value_model_eval_or_of_bool
    {v1 v2 : SmtValue}
    (h1 : __smtx_typeof_value v1 = SmtType.Bool)
    (h2 : __smtx_typeof_value v2 = SmtType.Bool) :
    __smtx_typeof_value (__smtx_model_eval_or v1 v2) = SmtType.Bool := by
  rcases bool_value_canonical h1 with ⟨b1, hb1⟩
  rcases bool_value_canonical h2 with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_or, __smtx_typeof_value]

theorem typeof_value_model_eval_bvnot_value
    (w n : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvnot (SmtValue.Binary w n)) = SmtType.BitVec w := by
  simpa [__smtx_model_eval_bvnot] using
    typeof_value_binary_of_nonneg w
      (smt_lit_mod_total (smt_lit_binary_not w n) (smt_lit_int_pow2 w)) hWidth

theorem typeof_value_model_eval_bvneg_value
    (w n : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvneg (SmtValue.Binary w n)) = SmtType.BitVec w := by
  simpa [__smtx_model_eval_bvneg] using
    typeof_value_binary_of_nonneg w
      (smt_lit_mod_total (smt_lit_zneg n) (smt_lit_int_pow2 w)) hWidth

theorem typeof_value_model_eval_bvadd_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvadd (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
  simpa [__smtx_model_eval_bvadd] using
    typeof_value_binary_of_nonneg w
      (smt_lit_mod_total (smt_lit_zplus n1 n2) (smt_lit_int_pow2 w)) hWidth

theorem typeof_value_model_eval_bvudiv_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvudiv (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
  simpa [__smtx_model_eval_bvudiv] using
    typeof_value_binary_of_nonneg w
      (smt_lit_mod_total
        (smt_lit_ite (smt_lit_zeq n2 0) (smt_lit_binary_max w) (smt_lit_div_total n1 n2))
        (smt_lit_int_pow2 w)) hWidth

theorem typeof_value_model_eval_bvurem_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvurem (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
  simpa [__smtx_model_eval_bvurem] using
    typeof_value_binary_of_nonneg w
      (smt_lit_mod_total
        (smt_lit_ite (smt_lit_zeq n2 0) n1 (smt_lit_mod_total n1 n2))
        (smt_lit_int_pow2 w)) hWidth

theorem typeof_value_model_eval_bvlshr_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvlshr (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
  simpa [__smtx_model_eval_bvlshr] using
    typeof_value_binary_of_nonneg w
      (smt_lit_mod_total (smt_lit_div_total n1 (smt_lit_int_pow2 n2)) (smt_lit_int_pow2 w)) hWidth

theorem typeof_value_model_eval_bvnego_value
    (w n : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvnego (SmtValue.Binary w n)) = SmtType.Bool := by
  simp [__smtx_model_eval_bvnego, __smtx_typeof_value]

theorem typeof_value_model_eval_bvsaddo_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvsaddo (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  simp [__smtx_model_eval_bvsaddo, __smtx_typeof_value]

theorem typeof_value_model_eval_bvnot_of_bitvec
    {v : SmtValue}
    {w : smt_lit_Int}
    (hv : __smtx_typeof_value v = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvnot v) = SmtType.BitVec w := by
  rcases bitvec_value_canonical hv with ⟨n, rfl⟩
  exact typeof_value_model_eval_bvnot_value w n (bitvec_width_nonneg hv)

theorem typeof_value_model_eval_bvneg_of_bitvec
    {v : SmtValue}
    {w : smt_lit_Int}
    (hv : __smtx_typeof_value v = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvneg v) = SmtType.BitVec w := by
  rcases bitvec_value_canonical hv with ⟨n, rfl⟩
  exact typeof_value_model_eval_bvneg_value w n (bitvec_width_nonneg hv)

theorem typeof_value_model_eval_bvadd_of_bitvec
    {v1 v2 : SmtValue}
    {w : smt_lit_Int}
    (h1 : __smtx_typeof_value v1 = SmtType.BitVec w)
    (h2 : __smtx_typeof_value v2 = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvadd v1 v2) = SmtType.BitVec w := by
  rcases bitvec_value_canonical h1 with ⟨n1, hv1⟩
  rcases bitvec_value_canonical h2 with ⟨n2, hv2⟩
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [hv1] using h1)
  rw [hv1, hv2]
  exact typeof_value_model_eval_bvadd_value w n1 n2 hWidth

theorem typeof_value_model_eval_bvudiv_of_bitvec
    {v1 v2 : SmtValue}
    {w : smt_lit_Int}
    (h1 : __smtx_typeof_value v1 = SmtType.BitVec w)
    (h2 : __smtx_typeof_value v2 = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvudiv v1 v2) = SmtType.BitVec w := by
  rcases bitvec_value_canonical h1 with ⟨n1, hv1⟩
  rcases bitvec_value_canonical h2 with ⟨n2, hv2⟩
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [hv1] using h1)
  rw [hv1, hv2]
  exact typeof_value_model_eval_bvudiv_value w n1 n2 hWidth

theorem typeof_value_model_eval_bvurem_of_bitvec
    {v1 v2 : SmtValue}
    {w : smt_lit_Int}
    (h1 : __smtx_typeof_value v1 = SmtType.BitVec w)
    (h2 : __smtx_typeof_value v2 = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvurem v1 v2) = SmtType.BitVec w := by
  rcases bitvec_value_canonical h1 with ⟨n1, hv1⟩
  rcases bitvec_value_canonical h2 with ⟨n2, hv2⟩
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [hv1] using h1)
  rw [hv1, hv2]
  exact typeof_value_model_eval_bvurem_value w n1 n2 hWidth

theorem typeof_value_model_eval_bvlshr_of_bitvec
    {v1 v2 : SmtValue}
    {w : smt_lit_Int}
    (h1 : __smtx_typeof_value v1 = SmtType.BitVec w)
    (h2 : __smtx_typeof_value v2 = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvlshr v1 v2) = SmtType.BitVec w := by
  rcases bitvec_value_canonical h1 with ⟨n1, hv1⟩
  rcases bitvec_value_canonical h2 with ⟨n2, hv2⟩
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [hv1] using h1)
  rw [hv1, hv2]
  exact typeof_value_model_eval_bvlshr_value w n1 n2 hWidth

theorem typeof_value_model_eval_bvnego_of_bitvec
    {v : SmtValue}
    {w : smt_lit_Int}
    (hv : __smtx_typeof_value v = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvnego v) = SmtType.Bool := by
  rcases bitvec_value_canonical hv with ⟨n, hv'⟩
  rw [hv']
  exact typeof_value_model_eval_bvnego_value w n

theorem typeof_value_model_eval_bvsaddo_of_bitvec
    {v1 v2 : SmtValue}
    {w : smt_lit_Int}
    (h1 : __smtx_typeof_value v1 = SmtType.BitVec w)
    (h2 : __smtx_typeof_value v2 = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvsaddo v1 v2) = SmtType.Bool := by
  rcases bitvec_value_canonical h1 with ⟨n1, hv1⟩
  rcases bitvec_value_canonical h2 with ⟨n2, hv2⟩
  rw [hv1, hv2]
  exact typeof_value_model_eval_bvsaddo_value w n1 n2

end Smtm
