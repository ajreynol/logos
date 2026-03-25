import Cpc.TypePreservation.BitVecCore

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

theorem typeof_value_model_eval_bvnot
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.bvnot t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.bvnot t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.bvnot t) := by
  exact typeof_value_model_eval_bv_unop M SmtTerm.bvnot __smtx_model_eval_bvnot t
    rfl rfl ht hpres (fun w n hWidth => by
      simpa [__smtx_model_eval_bvnot] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_binary_not w n) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvand
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvand __smtx_model_eval_bvand t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvand] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_binary_and w n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvor __smtx_model_eval_bvor t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvor] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_binary_or w n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvnand
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvnand __smtx_model_eval_bvnand t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvnand, __smtx_model_eval_bvnot, __smtx_model_eval_bvand] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_binary_not w
              (smt_lit_mod_total (smt_lit_binary_and w n1 n2) (smt_lit_int_pow2 w)))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvnor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvnor __smtx_model_eval_bvnor t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvnor, __smtx_model_eval_bvnot, __smtx_model_eval_bvor] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_binary_not w
              (smt_lit_mod_total (smt_lit_binary_or w n1 n2) (smt_lit_int_pow2 w)))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvxor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvxor __smtx_model_eval_bvxor t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvxor] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_binary_xor w n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvxnor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvxnor __smtx_model_eval_bvxnor t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvxnor, __smtx_model_eval_bvnot, __smtx_model_eval_bvxor] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_binary_not w
              (smt_lit_mod_total (smt_lit_binary_xor w n1 n2) (smt_lit_int_pow2 w)))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvcomp
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvcomp __smtx_model_eval_bvcomp
    (SmtType.BitVec 1) t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvcomp_value w n1 n2)

theorem typeof_value_model_eval_bvneg
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.bvneg t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.bvneg t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.bvneg t) := by
  exact typeof_value_model_eval_bv_unop M SmtTerm.bvneg __smtx_model_eval_bvneg t
    rfl rfl ht hpres (fun w n hWidth => by
      simpa [__smtx_model_eval_bvneg] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_zneg n) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvadd
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvadd __smtx_model_eval_bvadd t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvadd] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_zplus n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvmul
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvmul __smtx_model_eval_bvmul t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvmul] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_zmult n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvudiv
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvudiv __smtx_model_eval_bvudiv t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvudiv] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_ite (smt_lit_zeq n2 0) (smt_lit_binary_max w) (smt_lit_div_total n1 n2))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvurem
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvurem __smtx_model_eval_bvurem t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvurem] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_ite (smt_lit_zeq n2 0) n1 (smt_lit_mod_total n1 n2))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvsub
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvsub __smtx_model_eval_bvsub t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvsub, __smtx_model_eval_bvadd, __smtx_model_eval_bvneg] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_zplus n1
              (smt_lit_mod_total (smt_lit_zneg n2) (smt_lit_int_pow2 w)))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvult
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvult __smtx_model_eval_bvult
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvult, __smtx_model_eval_bvugt, __smtx_typeof_value] using
        typeof_value_model_eval_bvugt_value w n2 n1 hWidth)

theorem typeof_value_model_eval_bvule
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvule __smtx_model_eval_bvule
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvule, __smtx_model_eval_bvuge] using
        typeof_value_model_eval_bvuge_value w n2 n1 hWidth)

theorem typeof_value_model_eval_bvugt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvugt __smtx_model_eval_bvugt
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvugt_value

theorem typeof_value_model_eval_bvuge
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvuge __smtx_model_eval_bvuge
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvuge_value

theorem typeof_value_model_eval_bvsgt_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvsgt (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  simp [__smtx_model_eval_bvsgt, __smtx_model_eval__, __smtx_model_eval_extract,
    __smtx_model_eval_eq, __smtx_model_eval_not, __smtx_model_eval_and,
    __smtx_model_eval_or, __smtx_model_eval_bvugt, __smtx_typeof_value,
    SmtEval.smt_lit_zplus, SmtEval.smt_lit_zneg]

theorem typeof_value_model_eval_bvsge_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvsge (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  unfold __smtx_model_eval_bvsge
  rcases bool_value_canonical (typeof_value_model_eval_bvsgt_value w n1 n2) with ⟨b1, hb1⟩
  rcases bool_value_canonical (typeof_value_model_eval_eq_value
      (SmtValue.Binary w n1) (SmtValue.Binary w n2)) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_or, __smtx_typeof_value]

theorem typeof_value_model_eval_bvslt_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvslt (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  simpa [__smtx_model_eval_bvslt] using typeof_value_model_eval_bvsgt_value w n2 n1

theorem typeof_value_model_eval_bvsle_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvsle (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  simpa [__smtx_model_eval_bvsle] using typeof_value_model_eval_bvsge_value w n2 n1

theorem typeof_value_model_eval_bvslt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvslt __smtx_model_eval_bvslt
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvslt_value w n1 n2)

theorem typeof_value_model_eval_bvsle
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsle __smtx_model_eval_bvsle
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvsle_value w n1 n2)

theorem typeof_value_model_eval_bvsgt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsgt __smtx_model_eval_bvsgt
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvsgt_value w n1 n2)

theorem typeof_value_model_eval_bvsge
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsge __smtx_model_eval_bvsge
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvsge_value w n1 n2)


end Smtm
