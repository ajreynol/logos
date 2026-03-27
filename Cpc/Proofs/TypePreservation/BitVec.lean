import Cpc.Proofs.TypePreservation.BitVecCmp

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

theorem typeof_value_model_eval_ubv_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.ubv_to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.ubv_to_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.ubv_to_int t) := by
  exact typeof_value_model_eval_bv_unop_ret M SmtTerm.ubv_to_int __smtx_model_eval_ubv_to_int
    SmtType.Int t rfl rfl ht hpres (fun w n hWidth => by
      simp [__smtx_model_eval_ubv_to_int, __smtx_typeof_value])

theorem typeof_value_model_eval_sbv_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.sbv_to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.sbv_to_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.sbv_to_int t) := by
  exact typeof_value_model_eval_bv_unop_ret M SmtTerm.sbv_to_int __smtx_model_eval_sbv_to_int
    SmtType.Int t rfl rfl ht hpres (fun w n hWidth => by
      simp [__smtx_model_eval_sbv_to_int, __smtx_typeof_value])

theorem typeof_value_model_eval_bvshl
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvshl __smtx_model_eval_bvshl t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvshl] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_zmult n1 (smt_lit_int_pow2 n2)) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvlshr
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvlshr __smtx_model_eval_bvlshr t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvlshr] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_div_total n1 (smt_lit_int_pow2 n2)) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvsge_of_bitvec
    {v1 v2 : SmtValue}
    {w : smt_lit_Int}
    (h1 : __smtx_typeof_value v1 = SmtType.BitVec w)
    (h2 : __smtx_typeof_value v2 = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval_bvsge v1 v2) = SmtType.Bool := by
  rcases bitvec_value_canonical h1 with ⟨n1, hv1⟩
  rcases bitvec_value_canonical h2 with ⟨n2, hv2⟩
  rw [hv1, hv2]
  exact typeof_value_model_eval_bvsge_value w n1 n2

theorem typeof_value_model_eval_bvsdiv_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvsdiv (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
  let v0 := __smtx_model_eval_bvneg (SmtValue.Binary w n2)
  let v1 := __smtx_model_eval_bvneg (SmtValue.Binary w n1)
  let v3 := SmtValue.Binary 1 1
  let v4 :=
    __smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value (SmtValue.Binary w n1)))
      (SmtValue.Numeral 1)
  let v5 := __smtx_model_eval_eq (__smtx_model_eval_extract v4 v4 (SmtValue.Binary w n2)) v3
  let v6 := __smtx_model_eval_eq (__smtx_model_eval_extract v4 v4 (SmtValue.Binary w n1)) v3
  let v7 := __smtx_model_eval_not v6
  let v8 := __smtx_model_eval_not v5
  have hBin1 : __smtx_typeof_value (SmtValue.Binary w n1) = SmtType.BitVec w := by
    exact typeof_value_binary_of_nonneg w n1 hWidth
  have hBin2 : __smtx_typeof_value (SmtValue.Binary w n2) = SmtType.BitVec w := by
    exact typeof_value_binary_of_nonneg w n2 hWidth
  have hv0 : __smtx_typeof_value v0 = SmtType.BitVec w := by
    simpa [v0] using typeof_value_model_eval_bvneg_value w n2 hWidth
  have hv1 : __smtx_typeof_value v1 = SmtType.BitVec w := by
    simpa [v1] using typeof_value_model_eval_bvneg_value w n1 hWidth
  have h5 : __smtx_typeof_value v5 = SmtType.Bool := by
    unfold v5
    exact typeof_value_model_eval_eq_value _ _
  have h6 : __smtx_typeof_value v6 = SmtType.Bool := by
    unfold v6
    exact typeof_value_model_eval_eq_value _ _
  have h7 : __smtx_typeof_value v7 = SmtType.Bool := by
    simpa [v7] using typeof_value_model_eval_not_of_bool h6
  have h8 : __smtx_typeof_value v8 = SmtType.Bool := by
    simpa [v8] using typeof_value_model_eval_not_of_bool h5
  have h78 : __smtx_typeof_value (__smtx_model_eval_and v7 v8) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h7 h8
  have h68 : __smtx_typeof_value (__smtx_model_eval_and v6 v8) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h6 h8
  have h75 : __smtx_typeof_value (__smtx_model_eval_and v7 v5) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h7 h5
  have hu0 : __smtx_typeof_value (__smtx_model_eval_bvudiv (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
    exact typeof_value_model_eval_bvudiv_value w n1 n2 hWidth
  have hu1 : __smtx_typeof_value (__smtx_model_eval_bvudiv v1 (SmtValue.Binary w n2)) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvudiv_of_bitvec hv1 hBin2
  have hu2 : __smtx_typeof_value (__smtx_model_eval_bvudiv (SmtValue.Binary w n1) v0) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvudiv_of_bitvec hBin1 hv0
  have hu3 : __smtx_typeof_value (__smtx_model_eval_bvudiv v1 v0) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvudiv_of_bitvec hv1 hv0
  have hn1 : __smtx_typeof_value (__smtx_model_eval_bvneg (__smtx_model_eval_bvudiv v1 (SmtValue.Binary w n2))) =
      SmtType.BitVec w := by
    exact typeof_value_model_eval_bvneg_of_bitvec hu1
  have hn2 : __smtx_typeof_value (__smtx_model_eval_bvneg (__smtx_model_eval_bvudiv (SmtValue.Binary w n1) v0)) =
      SmtType.BitVec w := by
    exact typeof_value_model_eval_bvneg_of_bitvec hu2
  unfold __smtx_model_eval_bvsdiv
  simpa [v0, v1, v3, v4, v5, v6, v7, v8] using
    (typeof_value_model_eval_ite_of_bool h78 hu0
      (typeof_value_model_eval_ite_of_bool h68 hn1
        (typeof_value_model_eval_ite_of_bool h75 hn2 hu3)))

theorem typeof_value_model_eval_bvsdiv
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdiv t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdiv t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdiv t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvsdiv __smtx_model_eval_bvsdiv t1 t2
    rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvsdiv_value

theorem typeof_value_model_eval_bvsrem_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvsrem (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
  let v0 := __smtx_model_eval_bvneg (SmtValue.Binary w n2)
  let v1 := __smtx_model_eval_bvneg (SmtValue.Binary w n1)
  let v3 := SmtValue.Binary 1 1
  let v4 :=
    __smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value (SmtValue.Binary w n1)))
      (SmtValue.Numeral 1)
  let v5 := __smtx_model_eval_eq (__smtx_model_eval_extract v4 v4 (SmtValue.Binary w n2)) v3
  let v6 := __smtx_model_eval_eq (__smtx_model_eval_extract v4 v4 (SmtValue.Binary w n1)) v3
  let v7 := __smtx_model_eval_not v6
  let v8 := __smtx_model_eval_not v5
  have hBin1 : __smtx_typeof_value (SmtValue.Binary w n1) = SmtType.BitVec w := by
    exact typeof_value_binary_of_nonneg w n1 hWidth
  have hBin2 : __smtx_typeof_value (SmtValue.Binary w n2) = SmtType.BitVec w := by
    exact typeof_value_binary_of_nonneg w n2 hWidth
  have hv0 : __smtx_typeof_value v0 = SmtType.BitVec w := by
    simpa [v0] using typeof_value_model_eval_bvneg_value w n2 hWidth
  have hv1 : __smtx_typeof_value v1 = SmtType.BitVec w := by
    simpa [v1] using typeof_value_model_eval_bvneg_value w n1 hWidth
  have h5 : __smtx_typeof_value v5 = SmtType.Bool := by
    unfold v5
    exact typeof_value_model_eval_eq_value _ _
  have h6 : __smtx_typeof_value v6 = SmtType.Bool := by
    unfold v6
    exact typeof_value_model_eval_eq_value _ _
  have h7 : __smtx_typeof_value v7 = SmtType.Bool := by
    simpa [v7] using typeof_value_model_eval_not_of_bool h6
  have h8 : __smtx_typeof_value v8 = SmtType.Bool := by
    simpa [v8] using typeof_value_model_eval_not_of_bool h5
  have h78 : __smtx_typeof_value (__smtx_model_eval_and v7 v8) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h7 h8
  have h68 : __smtx_typeof_value (__smtx_model_eval_and v6 v8) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h6 h8
  have h75 : __smtx_typeof_value (__smtx_model_eval_and v7 v5) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h7 h5
  have hu0 : __smtx_typeof_value (__smtx_model_eval_bvurem (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
    exact typeof_value_model_eval_bvurem_value w n1 n2 hWidth
  have hu1 : __smtx_typeof_value (__smtx_model_eval_bvurem v1 (SmtValue.Binary w n2)) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvurem_of_bitvec hv1 hBin2
  have hu2 : __smtx_typeof_value (__smtx_model_eval_bvurem (SmtValue.Binary w n1) v0) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvurem_of_bitvec hBin1 hv0
  have hu3 : __smtx_typeof_value (__smtx_model_eval_bvurem v1 v0) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvurem_of_bitvec hv1 hv0
  have hn1 : __smtx_typeof_value (__smtx_model_eval_bvneg (__smtx_model_eval_bvurem v1 (SmtValue.Binary w n2))) =
      SmtType.BitVec w := by
    exact typeof_value_model_eval_bvneg_of_bitvec hu1
  have hn2 : __smtx_typeof_value (__smtx_model_eval_bvneg (__smtx_model_eval_bvurem (SmtValue.Binary w n1) v0)) =
      SmtType.BitVec w := by
    exact typeof_value_model_eval_bvneg_of_bitvec hu2
  unfold __smtx_model_eval_bvsrem
  simpa [v0, v1, v3, v4, v5, v6, v7, v8] using
    (typeof_value_model_eval_ite_of_bool h78 hu0
      (typeof_value_model_eval_ite_of_bool h68 hn1
        (typeof_value_model_eval_ite_of_bool h75 hn2 hu3)))

theorem typeof_value_model_eval_bvsrem
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsrem t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsrem t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsrem t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvsrem __smtx_model_eval_bvsrem t1 t2
    rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvsrem_value

theorem typeof_value_model_eval_bvsmod_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvsmod (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
  let v1 := SmtValue.Binary 1 1
  let v2 := __smtx_bv_sizeof_value (SmtValue.Binary w n1)
  let v3 := __smtx_model_eval__ (SmtValue.Numeral v2) (SmtValue.Numeral 1)
  let v4 := __smtx_model_eval_eq (__smtx_model_eval_extract v3 v3 (SmtValue.Binary w n2)) v1
  let v5 := __smtx_model_eval_eq (__smtx_model_eval_extract v3 v3 (SmtValue.Binary w n1)) v1
  let v6 :=
    __smtx_model_eval_bvurem
      (__smtx_model_eval_ite v5 (SmtValue.Binary w n1) (__smtx_model_eval_bvneg (SmtValue.Binary w n1)))
      (__smtx_model_eval_ite v4 (SmtValue.Binary w n2) (__smtx_model_eval_bvneg (SmtValue.Binary w n2)))
  let v7 := __smtx_model_eval_bvneg v6
  let v8 := __smtx_model_eval_not v5
  let v9 := __smtx_model_eval_not v4
  have hBin1 : __smtx_typeof_value (SmtValue.Binary w n1) = SmtType.BitVec w := by
    exact typeof_value_binary_of_nonneg w n1 hWidth
  have hBin2 : __smtx_typeof_value (SmtValue.Binary w n2) = SmtType.BitVec w := by
    exact typeof_value_binary_of_nonneg w n2 hWidth
  have hNeg1 : __smtx_typeof_value (__smtx_model_eval_bvneg (SmtValue.Binary w n1)) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvneg_value w n1 hWidth
  have hNeg2 : __smtx_typeof_value (__smtx_model_eval_bvneg (SmtValue.Binary w n2)) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvneg_value w n2 hWidth
  have h4 : __smtx_typeof_value v4 = SmtType.Bool := by
    unfold v4
    exact typeof_value_model_eval_eq_value _ _
  have h5 : __smtx_typeof_value v5 = SmtType.Bool := by
    unfold v5
    exact typeof_value_model_eval_eq_value _ _
  have hAbs1 :
      __smtx_typeof_value
          (__smtx_model_eval_ite v5 (SmtValue.Binary w n1) (__smtx_model_eval_bvneg (SmtValue.Binary w n1))) =
        SmtType.BitVec w := by
    exact typeof_value_model_eval_ite_of_bool h5 hBin1 hNeg1
  have hAbs2 :
      __smtx_typeof_value
          (__smtx_model_eval_ite v4 (SmtValue.Binary w n2) (__smtx_model_eval_bvneg (SmtValue.Binary w n2))) =
        SmtType.BitVec w := by
    exact typeof_value_model_eval_ite_of_bool h4 hBin2 hNeg2
  have h6 : __smtx_typeof_value v6 = SmtType.BitVec w := by
    unfold v6
    exact typeof_value_model_eval_bvurem_of_bitvec hAbs1 hAbs2
  have h7 : __smtx_typeof_value v7 = SmtType.BitVec w := by
    unfold v7
    exact typeof_value_model_eval_bvneg_of_bitvec h6
  have h8 : __smtx_typeof_value v8 = SmtType.Bool := by
    simpa [v8] using typeof_value_model_eval_not_of_bool h5
  have h9 : __smtx_typeof_value v9 = SmtType.Bool := by
    simpa [v9] using typeof_value_model_eval_not_of_bool h4
  have hEq0 : __smtx_typeof_value (__smtx_model_eval_eq v6 (SmtValue.Binary v2 0)) = SmtType.Bool := by
    exact typeof_value_model_eval_eq_value _ _
  have h89 : __smtx_typeof_value (__smtx_model_eval_and v8 v9) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h8 h9
  have h59 : __smtx_typeof_value (__smtx_model_eval_and v5 v9) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h5 h9
  have h84 : __smtx_typeof_value (__smtx_model_eval_and v8 v4) = SmtType.Bool := by
    exact typeof_value_model_eval_and_of_bool h8 h4
  have hAdd1 : __smtx_typeof_value (__smtx_model_eval_bvadd v7 (SmtValue.Binary w n2)) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvadd_of_bitvec h7 hBin2
  have hAdd2 : __smtx_typeof_value (__smtx_model_eval_bvadd v6 (SmtValue.Binary w n2)) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvadd_of_bitvec h6 hBin2
  unfold __smtx_model_eval_bvsmod
  simpa [v1, v2, v3, v4, v5, v6, v7, v8, v9] using
    (typeof_value_model_eval_ite_of_bool hEq0 h6
      (typeof_value_model_eval_ite_of_bool h89 h6
        (typeof_value_model_eval_ite_of_bool h59 hAdd1
          (typeof_value_model_eval_ite_of_bool h84 hAdd2 h7))))

theorem typeof_value_model_eval_bvsmod
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmod t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmod t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmod t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvsmod __smtx_model_eval_bvsmod t1 t2
    rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvsmod_value

theorem typeof_value_model_eval_bvashr_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvashr (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
  let v1 :=
    __smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value (SmtValue.Binary w n1)))
      (SmtValue.Numeral 1)
  have hBin2 : __smtx_typeof_value (SmtValue.Binary w n2) = SmtType.BitVec w := by
    exact typeof_value_binary_of_nonneg w n2 hWidth
  have hCond :
      __smtx_typeof_value
          (__smtx_model_eval_eq (__smtx_model_eval_extract v1 v1 (SmtValue.Binary w n1)) (SmtValue.Binary 1 0)) =
        SmtType.Bool := by
    exact typeof_value_model_eval_eq_value _ _
  have hL : __smtx_typeof_value (__smtx_model_eval_bvlshr (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec w := by
    exact typeof_value_model_eval_bvlshr_value w n1 n2 hWidth
  have hNot : __smtx_typeof_value (__smtx_model_eval_bvnot (SmtValue.Binary w n1)) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvnot_value w n1 hWidth
  have hR0 :
      __smtx_typeof_value
          (__smtx_model_eval_bvlshr (__smtx_model_eval_bvnot (SmtValue.Binary w n1)) (SmtValue.Binary w n2)) =
        SmtType.BitVec w := by
    exact typeof_value_model_eval_bvlshr_of_bitvec hNot hBin2
  have hR :
      __smtx_typeof_value
          (__smtx_model_eval_bvnot
            (__smtx_model_eval_bvlshr (__smtx_model_eval_bvnot (SmtValue.Binary w n1)) (SmtValue.Binary w n2))) =
        SmtType.BitVec w := by
    exact typeof_value_model_eval_bvnot_of_bitvec hR0
  unfold __smtx_model_eval_bvashr
  simpa [v1] using typeof_value_model_eval_ite_of_bool hCond hL hR

theorem typeof_value_model_eval_bvashr
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvashr t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvashr t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvashr t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvashr __smtx_model_eval_bvashr t1 t2
    rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvashr_value

theorem typeof_value_model_eval_bvssubo_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvssubo (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  have hBin1 : __smtx_typeof_value (SmtValue.Binary w n1) = SmtType.BitVec w := by
    exact typeof_value_binary_of_nonneg w n1 hWidth
  have hCond : __smtx_typeof_value (__smtx_model_eval_bvnego (SmtValue.Binary w n2)) = SmtType.Bool := by
    exact typeof_value_model_eval_bvnego_value w n2
  have hThen :
      __smtx_typeof_value
          (__smtx_model_eval_bvsge (SmtValue.Binary w n1)
            (SmtValue.Binary (__smtx_bv_sizeof_value (SmtValue.Binary w n1)) 0)) =
        SmtType.Bool := by
    simpa [__smtx_bv_sizeof_value] using typeof_value_model_eval_bvsge_value w n1 0
  have hNeg2 : __smtx_typeof_value (__smtx_model_eval_bvneg (SmtValue.Binary w n2)) = SmtType.BitVec w := by
    exact typeof_value_model_eval_bvneg_value w n2 hWidth
  have hElse :
      __smtx_typeof_value
          (__smtx_model_eval_bvsaddo (SmtValue.Binary w n1) (__smtx_model_eval_bvneg (SmtValue.Binary w n2))) =
        SmtType.Bool := by
    exact typeof_value_model_eval_bvsaddo_of_bitvec hBin1 hNeg2
  unfold __smtx_model_eval_bvssubo
  exact typeof_value_model_eval_ite_of_bool hCond hThen hElse

theorem typeof_value_model_eval_bvssubo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvssubo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvssubo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvssubo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvssubo __smtx_model_eval_bvssubo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvssubo_value

theorem typeof_value_model_eval_bvsdivo_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvsdivo (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  have hCond : __smtx_typeof_value (__smtx_model_eval_bvnego (SmtValue.Binary w n1)) = SmtType.Bool := by
    exact typeof_value_model_eval_bvnego_value w n1
  have hEq :
      __smtx_typeof_value
          (__smtx_model_eval_eq (SmtValue.Binary w n2)
            (__smtx_model_eval_bvnot
              (SmtValue.Binary (__smtx_bv_sizeof_value (SmtValue.Binary w n1)) 0))) =
        SmtType.Bool := by
    simpa [__smtx_bv_sizeof_value] using
      (typeof_value_model_eval_eq_value
        (SmtValue.Binary w n2)
        (__smtx_model_eval_bvnot (SmtValue.Binary w 0)))
  unfold __smtx_model_eval_bvsdivo
  exact typeof_value_model_eval_and_of_bool hCond hEq

theorem typeof_value_model_eval_bvsdivo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdivo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdivo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsdivo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsdivo __smtx_model_eval_bvsdivo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvsdivo_value

theorem model_eval_repeat_rec_binary :
    ∀ n : smt_lit_Nat, ∀ w x : smt_lit_Int,
      ∃ m : smt_lit_Int,
        __smtx_model_eval_repeat_rec n (SmtValue.Binary w x) =
          SmtValue.Binary (smt_lit_zmult (smt_lit_nat_to_int n) w) m
  | smt_lit_nat_zero, w, x => by
      refine ⟨0, ?_⟩
      simp [__smtx_model_eval_repeat_rec, SmtEval.smt_lit_zmult, SmtEval.smt_lit_nat_to_int]
  | smt_lit_nat_succ n, w, x => by
      rcases model_eval_repeat_rec_binary n w x with ⟨m, hm⟩
      refine ⟨smt_lit_mod_total
        (smt_lit_binary_concat w x (smt_lit_zmult (smt_lit_nat_to_int n) w) m)
        (smt_lit_int_pow2 (smt_lit_zmult (smt_lit_nat_to_int (smt_lit_nat_succ n)) w)), ?_⟩
      rw [__smtx_model_eval_repeat_rec, hm, __smtx_model_eval_concat]
      have hWidthEq : w + ↑n * w = (↑n + 1) * w := by
        calc
          w + ↑n * w = 1 * w + ↑n * w := by simp
          _ = (1 + ↑n) * w := by rw [Int.add_mul]
          _ = (↑n + 1) * w := by simp [Int.add_comm]
      have hWidthEq' :
          smt_lit_zplus w (smt_lit_zmult (smt_lit_nat_to_int n) w) =
            smt_lit_zmult (smt_lit_nat_to_int (smt_lit_nat_succ n)) w := by
        simpa [SmtEval.smt_lit_zplus, SmtEval.smt_lit_zmult, SmtEval.smt_lit_nat_to_int] using hWidthEq
      exact congrArg
        (fun z =>
          SmtValue.Binary z
            (smt_lit_mod_total
              (smt_lit_binary_concat w x (smt_lit_zmult (smt_lit_nat_to_int n) w) m)
              (smt_lit_int_pow2 z)))
        hWidthEq'

theorem typeof_value_model_eval_repeat
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.__smt_repeat t1) t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.__smt_repeat t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.__smt_repeat t1) t2) := by
  rcases repeat_args_of_non_none ht with ⟨i, w, h1, h2, hi1⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.__smt_repeat t1) t2) =
      SmtType.BitVec (smt_lit_zmult i w) by
    simp [__smtx_typeof, __smtx_typeof_repeat, smt_lit_ite, h1, h2, hi1]]
  change __smtx_typeof_value
      (__smtx_model_eval_repeat (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zmult i w)
  rw [h1]
  change __smtx_typeof_value
      (__smtx_model_eval_repeat (SmtValue.Numeral i) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zmult i w)
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv, __smtx_model_eval_repeat]
  have hi : 0 <= i := by
    have hi' : 1 <= i := by
      simpa [SmtEval.smt_lit_zleq] using hi1
    calc
      (0 : Int) <= 1 := by decide
      _ <= i := hi'
  have hw0 : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  have hw : 0 <= w := by
    simpa [SmtEval.smt_lit_zleq] using hw0
  have hMult : smt_lit_zleq 0 (smt_lit_zmult i w) = true := by
    have hMultInt : 0 <= i * w := Int.mul_nonneg hi hw
    simpa [SmtEval.smt_lit_zleq, SmtEval.smt_lit_zmult] using hMultInt
  rcases model_eval_repeat_rec_binary (smt_lit_int_to_nat i) w n with ⟨m, hm⟩
  rw [hm]
  have hNat :
      smt_lit_zmult (smt_lit_nat_to_int (smt_lit_int_to_nat i)) w =
        smt_lit_zmult i w := by
    simp [SmtEval.smt_lit_zmult, SmtEval.smt_lit_nat_to_int, SmtEval.smt_lit_int_to_nat,
      Int.toNat_of_nonneg hi]
  rw [hNat]
  exact typeof_value_binary_of_nonneg (smt_lit_zmult i w) m hMult

theorem model_eval_rotate_left_step_binary
    (w x : smt_lit_Int) :
    ∃ y : smt_lit_Int,
      __smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral (smt_lit_zplus (smt_lit_zplus w (smt_lit_zneg 1)) (smt_lit_zneg 1)))
            (SmtValue.Numeral 0)
            (SmtValue.Binary w x))
          (__smtx_model_eval_extract
            (SmtValue.Numeral (smt_lit_zplus w (smt_lit_zneg 1)))
            (SmtValue.Numeral (smt_lit_zplus w (smt_lit_zneg 1)))
            (SmtValue.Binary w x)) =
        SmtValue.Binary w y := by
  let hi := smt_lit_zplus w (smt_lit_zneg 1)
  let w1 := smt_lit_zplus (smt_lit_zplus (smt_lit_zplus hi (smt_lit_zneg 1)) 1) (smt_lit_zneg 0)
  let w2 := smt_lit_zplus (smt_lit_zplus hi 1) (smt_lit_zneg hi)
  refine ⟨smt_lit_mod_total
      (smt_lit_binary_concat w1
        (smt_lit_mod_total
          (smt_lit_binary_extract w x (smt_lit_zplus hi (smt_lit_zneg 1)) 0)
          (smt_lit_int_pow2 w1))
        w2
        (smt_lit_mod_total (smt_lit_binary_extract w x hi hi) (smt_lit_int_pow2 w2)))
      (smt_lit_int_pow2 w), ?_⟩
  simp [__smtx_model_eval_concat, __smtx_model_eval_extract, w1, w2, hi,
    SmtEval.smt_lit_zplus, SmtEval.smt_lit_zneg]
  have hWidthEq : w + -1 + -1 + 1 + (w + -1 + 1 + -(w + -1)) = w := by
    rw [Int.neg_add]
    calc
      w + -1 + -1 + 1 + (w + -1 + 1 + (-w + 1)) = w + (w + -w) := by
        simp [Int.add_assoc, Int.add_left_comm, Int.add_comm]
      _ = w := by
        simpa [Int.add_assoc] using (Int.add_neg_cancel_right w w)
  constructor
  · exact hWidthEq
  · simp [hWidthEq]

theorem model_eval_rotate_left_rec_binary :
    ∀ n : smt_lit_Nat, ∀ w x : smt_lit_Int,
      ∃ m : smt_lit_Int,
        __smtx_model_eval_rotate_left_rec n (SmtValue.Binary w x) =
          SmtValue.Binary w m
  | smt_lit_nat_zero, w, x => by
      refine ⟨x, ?_⟩
      simp [__smtx_model_eval_rotate_left_rec]
  | smt_lit_nat_succ n, w, x => by
      rcases model_eval_rotate_left_step_binary w x with ⟨y, hy⟩
      rw [__smtx_model_eval_rotate_left_rec, hy]
      exact model_eval_rotate_left_rec_binary n w y

theorem typeof_value_model_eval_rotate_left
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left t1) t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left t1) t2) := by
  rcases rotate_left_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left t1) t2) =
      SmtType.BitVec w by
    simp [__smtx_typeof, __smtx_typeof_rotate_left, smt_lit_ite, h1, h2, hi0]]
  change __smtx_typeof_value
      (__smtx_model_eval_rotate_left (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec w
  rw [h1]
  change __smtx_typeof_value
      (__smtx_model_eval_rotate_left (SmtValue.Numeral i) (__smtx_model_eval M t2)) =
    SmtType.BitVec w
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv, __smtx_model_eval_rotate_left]
  rcases model_eval_rotate_left_rec_binary (smt_lit_int_to_nat i) w n with ⟨m, hm⟩
  rw [hm]
  have hw0 : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  exact typeof_value_binary_of_nonneg w m hw0

theorem model_eval_rotate_right_step_binary
    (w x : smt_lit_Int) :
    ∃ y : smt_lit_Int,
      __smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral 0)
            (SmtValue.Numeral 0)
            (SmtValue.Binary w x))
          (__smtx_model_eval_extract
            (SmtValue.Numeral (smt_lit_zplus w (smt_lit_zneg 1)))
            (SmtValue.Numeral 1)
            (SmtValue.Binary w x)) =
        SmtValue.Binary w y := by
  let hi := smt_lit_zplus w (smt_lit_zneg 1)
  let w1 := smt_lit_zplus (smt_lit_zplus 0 1) (smt_lit_zneg 0)
  let w2 := smt_lit_zplus (smt_lit_zplus hi 1) (smt_lit_zneg 1)
  refine ⟨smt_lit_mod_total
      (smt_lit_binary_concat w1
        (smt_lit_mod_total (smt_lit_binary_extract w x 0 0) (smt_lit_int_pow2 w1))
        w2
        (smt_lit_mod_total (smt_lit_binary_extract w x hi 1) (smt_lit_int_pow2 w2)))
      (smt_lit_int_pow2 w), ?_⟩
  simp [__smtx_model_eval_concat, __smtx_model_eval_extract, w1, w2, hi,
    SmtEval.smt_lit_zplus, SmtEval.smt_lit_zneg]
  have hWidthEq : 1 + (w + -1 + 1 + -1) = w := by
    simp [Int.add_left_comm, Int.add_comm]
  constructor
  · exact hWidthEq
  · simp [hWidthEq]

theorem model_eval_rotate_right_rec_binary :
    ∀ n : smt_lit_Nat, ∀ w x : smt_lit_Int,
      ∃ m : smt_lit_Int,
        __smtx_model_eval_rotate_right_rec n (SmtValue.Binary w x) =
          SmtValue.Binary w m
  | smt_lit_nat_zero, w, x => by
      refine ⟨x, ?_⟩
      simp [__smtx_model_eval_rotate_right_rec]
  | smt_lit_nat_succ n, w, x => by
      rcases model_eval_rotate_right_step_binary w x with ⟨y, hy⟩
      rw [__smtx_model_eval_rotate_right_rec, hy]
      exact model_eval_rotate_right_rec_binary n w y

theorem typeof_value_model_eval_rotate_right
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right t1) t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right t1) t2) := by
  rcases rotate_right_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right t1) t2) =
      SmtType.BitVec w by
    simp [__smtx_typeof, __smtx_typeof_rotate_right, smt_lit_ite, h1, h2, hi0]]
  change __smtx_typeof_value
      (__smtx_model_eval_rotate_right (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec w
  rw [h1]
  change __smtx_typeof_value
      (__smtx_model_eval_rotate_right (SmtValue.Numeral i) (__smtx_model_eval M t2)) =
    SmtType.BitVec w
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv, __smtx_model_eval_rotate_right]
  rcases model_eval_rotate_right_rec_binary (smt_lit_int_to_nat i) w n with ⟨m, hm⟩
  rw [hm]
  have hw0 : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  exact typeof_value_binary_of_nonneg w m hw0

theorem typeof_value_model_eval_bvuaddo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvuaddo __smtx_model_eval_bvuaddo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun _ _ _ _ => by
      simp [__smtx_model_eval_bvuaddo, __smtx_typeof_value])

theorem typeof_value_model_eval_bvnego
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.bvnego t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.bvnego t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.bvnego t) := by
  exact typeof_value_model_eval_bv_unop_ret M SmtTerm.bvnego __smtx_model_eval_bvnego
    SmtType.Bool t rfl rfl ht hpres (fun _ _ _ => by
      simp [__smtx_model_eval_bvnego, __smtx_typeof_value])

theorem typeof_value_model_eval_bvsaddo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsaddo __smtx_model_eval_bvsaddo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun _ _ _ _ => by
      simp [__smtx_model_eval_bvsaddo, __smtx_typeof_value])

theorem typeof_value_model_eval_bvumulo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvumulo __smtx_model_eval_bvumulo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun _ _ _ _ => by
      simp [__smtx_model_eval_bvumulo, __smtx_typeof_value])

theorem typeof_value_model_eval_bvsmulo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsmulo __smtx_model_eval_bvsmulo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun _ _ _ _ => by
      simp [__smtx_model_eval_bvsmulo, __smtx_typeof_value])

theorem typeof_value_model_eval_bvusubo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvusubo __smtx_model_eval_bvusubo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvusubo, __smtx_model_eval_bvult] using
        typeof_value_model_eval_bvugt_value w n2 n1 hWidth)

theorem typeof_value_model_eval_zero_extend
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2) := by
  rcases zero_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2) =
      SmtType.BitVec (smt_lit_zplus i w) by
    simp [__smtx_typeof, __smtx_typeof_zero_extend, smt_lit_ite, h1, h2, hi0]]
  change __smtx_typeof_value
      (__smtx_model_eval_zero_extend (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus i w)
  rw [h1]
  change __smtx_typeof_value
      (__smtx_model_eval_zero_extend (SmtValue.Numeral i) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus i w)
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv]
  have hi : 0 <= i := by
    simpa [SmtEval.smt_lit_zleq] using hi0
  have hw0 : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  have hw : 0 <= w := by
    simpa [SmtEval.smt_lit_zleq] using hw0
  have hWidth : smt_lit_zleq 0 (smt_lit_zplus i w) = true := by
    have hAdd : 0 <= i + w := Int.add_nonneg hi hw
    simpa [SmtEval.smt_lit_zleq, SmtEval.smt_lit_zplus] using hAdd
  simpa [__smtx_model_eval_zero_extend] using
    typeof_value_binary_of_nonneg (smt_lit_zplus i w) n hWidth

theorem typeof_value_model_eval_sign_extend
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2) := by
  rcases sign_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2) =
      SmtType.BitVec (smt_lit_zplus i w) by
    simp [__smtx_typeof, __smtx_typeof_sign_extend, smt_lit_ite, h1, h2, hi0]]
  change __smtx_typeof_value
      (__smtx_model_eval_sign_extend (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus i w)
  rw [h1]
  change __smtx_typeof_value
      (__smtx_model_eval_sign_extend (SmtValue.Numeral i) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus i w)
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv]
  have hi : 0 <= i := by
    simpa [SmtEval.smt_lit_zleq] using hi0
  have hw0 : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  have hw : 0 <= w := by
    simpa [SmtEval.smt_lit_zleq] using hw0
  have hWidth : smt_lit_zleq 0 (smt_lit_zplus i w) = true := by
    have hAdd : 0 <= i + w := Int.add_nonneg hi hw
    simpa [SmtEval.smt_lit_zleq, SmtEval.smt_lit_zplus] using hAdd
  simpa [__smtx_model_eval_sign_extend] using
    typeof_value_binary_of_nonneg (smt_lit_zplus i w)
      (smt_lit_mod_total (smt_lit_binary_uts w n) (smt_lit_int_pow2 (smt_lit_zplus i w))) hWidth

theorem typeof_value_model_eval_int_to_bv
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2) := by
  rcases int_to_bv_args_of_non_none ht with ⟨i, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2) =
      SmtType.BitVec i by
    simp [__smtx_typeof, __smtx_typeof_int_to_bv, smt_lit_ite, h1, h2, hi0]]
  change __smtx_typeof_value
      (__smtx_model_eval_int_to_bv (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec i
  rw [h1]
  change __smtx_typeof_value
      (__smtx_model_eval_int_to_bv (SmtValue.Numeral i) (__smtx_model_eval M t2)) =
    SmtType.BitVec i
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n, hn⟩
  rw [hn]
  simpa [__smtx_model_eval_int_to_bv] using
    typeof_value_binary_of_nonneg i (smt_lit_mod_total n (smt_lit_int_pow2 i)) hi0

end Smtm
