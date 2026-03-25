import Cpc.TypePreservation.BitVecCmp

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
