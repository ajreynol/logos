import Cpc.Proofs.Canonical.Maps
import Cpc.Proofs.Canonical.Seq

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Value-level SMT equality always returns a canonical Boolean value. -/
theorem model_eval_eq_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_eq v1 v2) :=
  value_canonical_of_bool_type (typeof_value_model_eval_eq_value v1 v2)

/-- Value-level Boolean negation always returns a canonical value. -/
theorem model_eval_not_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_not v) := by
  cases v <;>
    simp [__smtx_model_eval_not, __smtx_value_canonical,
      __smtx_value_canonical_bool]

/-- Value-level Boolean disjunction always returns a canonical value. -/
theorem model_eval_or_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_or v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_or, __smtx_value_canonical,
      __smtx_value_canonical_bool]

/-- Value-level Boolean conjunction always returns a canonical value. -/
theorem model_eval_and_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_and v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_and, __smtx_value_canonical,
      __smtx_value_canonical_bool]

/-- Value-level implication always returns a canonical value. -/
theorem model_eval_imp_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_imp v1 v2) := by
  simpa [__smtx_model_eval_imp] using
    model_eval_or_canonical (__smtx_model_eval_not v1) v2

/-- Value-level xor always returns a canonical value. -/
theorem model_eval_xor_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_xor v1 v2) := by
  simpa [__smtx_model_eval_xor] using
    model_eval_not_canonical (__smtx_model_eval_eq v1 v2)

/-- Value-level arithmetic addition always returns a canonical value. -/
theorem model_eval_plus_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_plus v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_plus, __smtx_value_canonical,
      __smtx_value_canonical_bool]

/-- Value-level arithmetic subtraction always returns a canonical value. -/
theorem model_eval_sub_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval__ v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval__, __smtx_value_canonical,
      __smtx_value_canonical_bool]

/-- Value-level arithmetic multiplication always returns a canonical value. -/
theorem model_eval_mult_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_mult v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_mult, __smtx_value_canonical,
      __smtx_value_canonical_bool]

/-- Value-level less-than always returns a canonical value. -/
theorem model_eval_lt_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_lt v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_lt, __smtx_value_canonical,
      __smtx_value_canonical_bool]

/-- Value-level less-or-equal always returns a canonical value. -/
theorem model_eval_leq_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_leq v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_leq, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_gt_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_gt v1 v2) := by
  simpa [__smtx_model_eval_gt] using model_eval_lt_canonical v2 v1

theorem model_eval_geq_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_geq v1 v2) := by
  simpa [__smtx_model_eval_geq] using model_eval_leq_canonical v2 v1

theorem model_eval_to_real_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_to_real v) := by
  cases v <;>
    simp [__smtx_model_eval_to_real, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_to_int_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_to_int v) := by
  cases v <;>
    simp [__smtx_model_eval_to_int, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_is_int_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_is_int v) := by
  simpa [__smtx_model_eval_is_int] using
    model_eval_eq_canonical (__smtx_model_eval_to_real (__smtx_model_eval_to_int v)) v

theorem model_eval_abs_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_abs v) := by
  cases v <;>
    simp [__smtx_model_eval_abs, __smtx_model_eval_ite, __smtx_model_eval_lt,
      __smtx_model_eval__, __smtx_value_canonical, __smtx_value_canonical_bool]
  · cases native_zlt ‹native_Int› 0 <;>
      simp [__smtx_value_canonical_bool]

theorem model_eval_uneg_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_uneg v) := by
  cases v <;>
    simp [__smtx_model_eval_uneg, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_divisible_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_divisible v1 v2) := by
  simpa [__smtx_model_eval_divisible] using
    model_eval_eq_canonical (__smtx_model_eval_mod_total v2 v1) (SmtValue.Numeral 0)

theorem model_eval_int_pow2_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_int_pow2 v) := by
  cases v <;>
    simp [__smtx_model_eval_int_pow2, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_int_log2_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_int_log2 v) := by
  cases v <;>
    simp [__smtx_model_eval_int_log2, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_div_total_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_div_total v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_div_total, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_mod_total_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_mod_total v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_mod_total, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_multmult_total_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_multmult_total v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_multmult_total, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_qdiv_total_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_qdiv_total v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_qdiv_total, __smtx_value_canonical,
      __smtx_value_canonical_bool]

theorem model_eval_apply_canonical
    {f x : SmtValue}
    (hf : __smtx_value_canonical f)
    (hx : __smtx_value_canonical x) :
    __smtx_value_canonical (__smtx_model_eval_apply f x) := by
  cases f <;> cases x <;>
    simp [__smtx_model_eval_apply, __smtx_map_select,
      __smtx_value_canonical, __smtx_value_canonical_bool,
      SmtEval.native_and] at hf hx ⊢
  all_goals
    first
    | assumption
    | exact ⟨hf, hx⟩
    | simpa [__smtx_value_canonical] using
        map_lookup_value_canonical (i := ?_) hf

/-- Value-level SMT `ite` preserves canonicality of the selected branch. -/
theorem model_eval_ite_canonical
    {c t e : SmtValue}
    (ht : __smtx_value_canonical t)
    (he : __smtx_value_canonical e) :
    __smtx_value_canonical (__smtx_model_eval_ite c t e) := by
  cases c <;>
    try
      simpa [__smtx_model_eval_ite] using value_canonical_notValue
  · cases ‹native_Bool› <;>
      simp [__smtx_model_eval_ite, ht, he]

theorem value_canonical_binary_mod
    (w n : native_Int) :
    __smtx_value_canonical
      (SmtValue.Binary w (native_mod_total n (native_int_pow2 w))) := by
  cases hw : native_zleq 0 w <;>
    simp [__smtx_value_canonical, __smtx_value_canonical_bool, native_ite,
      hw, native_mod_total_canonical]

theorem model_eval_concat_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_concat v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_concat, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_extract_canonical
    (v1 v2 v3 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_extract v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval_extract, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_repeat_rec_canonical :
    ∀ n v, __smtx_value_canonical (__smtx_model_eval_repeat_rec n v)
  | native_nat_zero, v => by
      simp [__smtx_model_eval_repeat_rec, __smtx_value_canonical,
        __smtx_value_canonical_bool, native_ite, native_zleq, native_zeq,
        native_mod_total, native_int_pow2, native_zexp_total]
  | native_nat_succ n, v => by
      simpa [__smtx_model_eval_repeat_rec] using
        model_eval_concat_canonical v (__smtx_model_eval_repeat_rec n v)

theorem model_eval_repeat_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_repeat v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_repeat, value_canonical_notValue,
      model_eval_repeat_rec_canonical]

theorem model_eval_bvnot_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvnot v) := by
  cases v <;>
    simp [__smtx_model_eval_bvnot, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvand_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvand v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvand, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvor_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvor v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvor, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvxor_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvxor v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvxor, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvnand_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvnand v1 v2) := by
  simpa [__smtx_model_eval_bvnand] using
    model_eval_bvnot_canonical (__smtx_model_eval_bvand v1 v2)

theorem model_eval_bvnor_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvnor v1 v2) := by
  simpa [__smtx_model_eval_bvnor] using
    model_eval_bvnot_canonical (__smtx_model_eval_bvor v1 v2)

theorem model_eval_bvxnor_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvxnor v1 v2) := by
  simpa [__smtx_model_eval_bvxnor] using
    model_eval_bvnot_canonical (__smtx_model_eval_bvxor v1 v2)

theorem model_eval_bvcomp_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvcomp v1 v2) := by
  simpa [__smtx_model_eval_bvcomp] using
    model_eval_ite_canonical
      (t := SmtValue.Binary 1 1)
      (e := SmtValue.Binary 1 0)
      (by simp [__smtx_value_canonical, __smtx_value_canonical_bool, native_ite,
        native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total])
      (by simp [__smtx_value_canonical, __smtx_value_canonical_bool, native_ite,
        native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total])

theorem model_eval_bvneg_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvneg v) := by
  cases v <;>
    simp [__smtx_model_eval_bvneg, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvadd_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvadd v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvadd, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvmul_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvmul v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvmul, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvudiv_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvudiv v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvudiv, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvurem_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvurem v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvurem, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvsub_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsub v1 v2) := by
  simpa [__smtx_model_eval_bvsub] using
    model_eval_bvadd_canonical v1 (__smtx_model_eval_bvneg v2)

theorem model_eval_bvugt_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvugt v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvugt, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvult_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvult v1 v2) := by
  simpa [__smtx_model_eval_bvult] using model_eval_bvugt_canonical v2 v1

theorem model_eval_bvuge_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvuge v1 v2) := by
  simpa [__smtx_model_eval_bvuge] using
    model_eval_or_canonical (__smtx_model_eval_bvugt v1 v2) (__smtx_model_eval_eq v1 v2)

theorem model_eval_bvule_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvule v1 v2) := by
  simpa [__smtx_model_eval_bvule] using model_eval_bvuge_canonical v2 v1

theorem model_eval_bvshl_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvshl v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvshl, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_bvlshr_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvlshr v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvlshr, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_sign_extend_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_sign_extend v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_sign_extend, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_int_to_bv_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_int_to_bv v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_int_to_bv, value_canonical_notValue, value_canonical_binary_mod]

theorem model_eval_ubv_to_int_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_ubv_to_int v) := by
  cases v <;>
    simp [__smtx_model_eval_ubv_to_int, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_sbv_to_int_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_sbv_to_int v) := by
  cases v <;>
    simp [__smtx_model_eval_sbv_to_int, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_bvuaddo_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvuaddo v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvuaddo, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvnego_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvnego v) := by
  cases v <;>
    simp [__smtx_model_eval_bvnego, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvsaddo_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsaddo v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvsaddo, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvumulo_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvumulo v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvumulo, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvsmulo_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsmulo v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_bvsmulo, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_bvusubo_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvusubo v1 v2) := by
  simpa [__smtx_model_eval_bvusubo] using model_eval_bvult_canonical v1 v2

theorem model_eval_bvsgt_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsgt v1 v2) := by
  simpa [__smtx_model_eval_bvsgt] using
    model_eval_or_canonical
      (__smtx_model_eval_and
        (__smtx_model_eval_not
          (__smtx_model_eval_eq
            (__smtx_model_eval_extract
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v1))
                (SmtValue.Numeral 1))
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v1))
                (SmtValue.Numeral 1))
              v1)
            (SmtValue.Binary 1 1)))
        (__smtx_model_eval_eq
          (__smtx_model_eval_extract
            (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v2))
              (SmtValue.Numeral 1))
            (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v2))
              (SmtValue.Numeral 1))
            v2)
          (SmtValue.Binary 1 1)))
      (__smtx_model_eval_and
        (__smtx_model_eval_eq
          (__smtx_model_eval_eq
            (__smtx_model_eval_extract
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v1))
                (SmtValue.Numeral 1))
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v1))
                (SmtValue.Numeral 1))
              v1)
            (SmtValue.Binary 1 1))
          (__smtx_model_eval_eq
            (__smtx_model_eval_extract
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v2))
                (SmtValue.Numeral 1))
              (__smtx_model_eval__ (SmtValue.Numeral (__smtx_bv_sizeof_value v2))
                (SmtValue.Numeral 1))
              v2)
            (SmtValue.Binary 1 1)))
        (__smtx_model_eval_bvugt v1 v2))

theorem model_eval_bvslt_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvslt v1 v2) := by
  simpa [__smtx_model_eval_bvslt] using model_eval_bvsgt_canonical v2 v1

theorem model_eval_bvsge_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsge v1 v2) := by
  simpa [__smtx_model_eval_bvsge] using
    model_eval_or_canonical (__smtx_model_eval_bvsgt v1 v2) (__smtx_model_eval_eq v1 v2)

theorem model_eval_bvsle_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsle v1 v2) := by
  simpa [__smtx_model_eval_bvsle] using model_eval_bvsge_canonical v2 v1

theorem model_eval_bvsdiv_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsdiv v1 v2) := by
  unfold __smtx_model_eval_bvsdiv
  repeat first
    | apply model_eval_ite_canonical
    | exact model_eval_bvudiv_canonical _ _
    | exact model_eval_bvneg_canonical _

theorem model_eval_bvsrem_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsrem v1 v2) := by
  unfold __smtx_model_eval_bvsrem
  repeat first
    | apply model_eval_ite_canonical
    | exact model_eval_bvurem_canonical _ _
    | exact model_eval_bvneg_canonical _

theorem model_eval_bvsmod_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsmod v1 v2) := by
  unfold __smtx_model_eval_bvsmod
  repeat first
    | apply model_eval_ite_canonical
    | exact model_eval_bvurem_canonical _ _
    | exact model_eval_bvneg_canonical _
    | exact model_eval_bvadd_canonical _ _

theorem model_eval_bvashr_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvashr v1 v2) := by
  unfold __smtx_model_eval_bvashr
  exact model_eval_ite_canonical
    (model_eval_bvlshr_canonical v1 v2)
    (model_eval_bvnot_canonical (__smtx_model_eval_bvlshr (__smtx_model_eval_bvnot v1) v2))

theorem model_eval_bvssubo_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvssubo v1 v2) := by
  unfold __smtx_model_eval_bvssubo
  exact model_eval_ite_canonical
    (model_eval_bvsge_canonical v1 (SmtValue.Binary (__smtx_bv_sizeof_value v1) 0))
    (model_eval_bvsaddo_canonical v1 (__smtx_model_eval_bvneg v2))

theorem model_eval_bvsdivo_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_bvsdivo v1 v2) := by
  simpa [__smtx_model_eval_bvsdivo] using
    model_eval_and_canonical
      (__smtx_model_eval_bvnego v1)
      (__smtx_model_eval_eq v2
        (__smtx_model_eval_bvnot (SmtValue.Binary (__smtx_bv_sizeof_value v1) 0)))

theorem model_eval_rotate_left_rec_canonical :
    ∀ n v,
      __smtx_value_canonical v ->
        __smtx_value_canonical (__smtx_model_eval_rotate_left_rec n v)
  | native_nat_zero, v, hv => by
      cases v with
      | Binary w x =>
          simpa [__smtx_model_eval_rotate_left_rec] using hv
      | _ =>
          simp [__smtx_model_eval_rotate_left_rec, value_canonical_notValue]
  | native_nat_succ n, v, hv => by
      cases v with
      | Binary w x =>
          simpa [__smtx_model_eval_rotate_left_rec] using
            model_eval_rotate_left_rec_canonical n
              (__smtx_model_eval_concat
                (__smtx_model_eval_extract
                  (SmtValue.Numeral (native_zplus (native_zplus w (native_zneg 1)) (native_zneg 1)))
                  (SmtValue.Numeral 0) (SmtValue.Binary w x))
                (__smtx_model_eval_extract
                  (SmtValue.Numeral (native_zplus w (native_zneg 1)))
                  (SmtValue.Numeral (native_zplus w (native_zneg 1))) (SmtValue.Binary w x)))
              (model_eval_concat_canonical _ _)
      | _ =>
          simp [__smtx_model_eval_rotate_left_rec, value_canonical_notValue]

theorem model_eval_rotate_right_rec_canonical :
    ∀ n v,
      __smtx_value_canonical v ->
        __smtx_value_canonical (__smtx_model_eval_rotate_right_rec n v)
  | native_nat_zero, v, hv => by
      cases v with
      | Binary w x =>
          simpa [__smtx_model_eval_rotate_right_rec] using hv
      | _ =>
          simp [__smtx_model_eval_rotate_right_rec, value_canonical_notValue]
  | native_nat_succ n, v, hv => by
      cases v with
      | Binary w x =>
          simpa [__smtx_model_eval_rotate_right_rec] using
            model_eval_rotate_right_rec_canonical n
              (__smtx_model_eval_concat
                (__smtx_model_eval_extract (SmtValue.Numeral 0)
                  (SmtValue.Numeral 0) (SmtValue.Binary w x))
                (__smtx_model_eval_extract
                  (SmtValue.Numeral (native_zplus w (native_zneg 1)))
                  (SmtValue.Numeral 1) (SmtValue.Binary w x)))
              (model_eval_concat_canonical _ _)
      | _ =>
          simp [__smtx_model_eval_rotate_right_rec, value_canonical_notValue]

theorem model_eval_rotate_left_canonical
    (v1 v2 : SmtValue)
    (hv2 : __smtx_value_canonical v2) :
    __smtx_value_canonical (__smtx_model_eval_rotate_left v1 v2) := by
  cases v1 with
  | Numeral n =>
      simpa [__smtx_model_eval_rotate_left] using
        model_eval_rotate_left_rec_canonical (native_int_to_nat n) v2 hv2
  | _ =>
      simp [__smtx_model_eval_rotate_left, value_canonical_notValue]

theorem model_eval_rotate_right_canonical
    (v1 v2 : SmtValue)
    (hv2 : __smtx_value_canonical v2) :
    __smtx_value_canonical (__smtx_model_eval_rotate_right v1 v2) := by
  cases v1 with
  | Numeral n =>
      simpa [__smtx_model_eval_rotate_right] using
        model_eval_rotate_right_rec_canonical (native_int_to_nat n) v2 hv2
  | _ =>
      simp [__smtx_model_eval_rotate_right, value_canonical_notValue]

/-- Literal strings evaluate to canonical sequence values. -/
theorem model_eval_string_value_canonical
    (s : native_String) :
    __smtx_value_canonical (SmtValue.Seq (native_pack_string s)) :=
  value_canonical_string s

theorem model_eval_seq_empty_value_canonical
    (T : SmtType) :
    __smtx_value_canonical (SmtValue.Seq (SmtSeq.empty T)) :=
  value_canonical_seq_empty T

theorem model_eval_seq_unit_value_canonical
    {v : SmtValue}
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical
      (SmtValue.Seq (SmtSeq.cons v (SmtSeq.empty (__smtx_typeof_value v)))) := by
  exact value_canonical_seq_cons hv (seq_canonical_empty (__smtx_typeof_value v))

theorem model_eval_str_concat_canonical
    {v1 v2 : SmtValue}
    (hv1 : __smtx_value_canonical v1)
    (hv2 : __smtx_value_canonical v2) :
    __smtx_value_canonical (__smtx_model_eval_str_concat v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_str_concat] using value_canonical_notValue
  case Seq.Seq s1 s2 =>
    have hs1 : __smtx_seq_canonical s1 = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv1
    have hs2 : __smtx_seq_canonical s2 = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv2
    simpa [__smtx_model_eval_str_concat, __smtx_value_canonical,
      __smtx_value_canonical_bool, native_seq_concat] using
      seq_canonical_pack_unpack_concat (__smtx_elem_typeof_seq_value s1)
        hs1 hs2

theorem model_eval_str_rev_canonical
    {v : SmtValue}
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (__smtx_model_eval_str_rev v) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_rev] using value_canonical_notValue
  · have hs : __smtx_seq_canonical ‹SmtSeq› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    simpa [__smtx_model_eval_str_rev, __smtx_value_canonical,
      __smtx_value_canonical_bool, native_seq_rev] using
      seq_canonical_pack_unpack_reverse (__smtx_elem_typeof_seq_value ‹SmtSeq›) hs

set_option maxHeartbeats 200000

theorem model_eval_str_substr_canonical
    {v i n : SmtValue}
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (__smtx_model_eval_str_substr v i n) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_substr] using value_canonical_notValue
  case Seq s =>
    cases i <;>
      try
        simpa [__smtx_model_eval_str_substr] using value_canonical_notValue
    case Numeral start =>
      cases n <;>
        try
          simpa [__smtx_model_eval_str_substr] using value_canonical_notValue
      case Numeral len =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
        simpa [__smtx_model_eval_str_substr, __smtx_value_canonical,
          __smtx_value_canonical_bool] using
          seq_canonical_pack_unpack_extract (__smtx_elem_typeof_seq_value s)
            hs start len

theorem model_eval_str_replace_canonical
    {v pat repl : SmtValue}
    (hv : __smtx_value_canonical v)
    (hpat : __smtx_value_canonical pat)
    (hrepl : __smtx_value_canonical repl) :
    __smtx_value_canonical (__smtx_model_eval_str_replace v pat repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_replace] using value_canonical_notValue
  case Seq s =>
    cases pat <;>
      try
        simpa [__smtx_model_eval_str_replace] using value_canonical_notValue
    case Seq p =>
      cases repl <;>
        try
          simpa [__smtx_model_eval_str_replace] using value_canonical_notValue
      case Seq r =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
        have hpatSeq : __smtx_seq_canonical p = true := by
          simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hpat
        have hreplSeq : __smtx_seq_canonical r = true := by
          simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hrepl
        simpa [__smtx_model_eval_str_replace, __smtx_value_canonical,
          __smtx_value_canonical_bool] using
          seq_canonical_pack_unpack_replace (__smtx_elem_typeof_seq_value s)
            hs hpatSeq hreplSeq

theorem model_eval_str_at_canonical
    {v i : SmtValue}
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (__smtx_model_eval_str_at v i) := by
  simpa [__smtx_model_eval_str_at] using
    model_eval_str_substr_canonical (v := v) (i := i) (n := SmtValue.Numeral 1) hv

theorem model_eval_str_update_canonical
    {v i repl : SmtValue}
    (hv : __smtx_value_canonical v)
    (hrepl : __smtx_value_canonical repl) :
    __smtx_value_canonical (__smtx_model_eval_str_update v i repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_update] using value_canonical_notValue
  case Seq s =>
    cases i <;>
      try
        simpa [__smtx_model_eval_str_update] using value_canonical_notValue
    case Numeral n =>
      cases repl <;>
        try
          simpa [__smtx_model_eval_str_update] using value_canonical_notValue
      case Seq r =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
        have hreplSeq : __smtx_seq_canonical r = true := by
          simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hrepl
        simpa [__smtx_model_eval_str_update, __smtx_value_canonical,
          __smtx_value_canonical_bool] using
          seq_canonical_pack_unpack_update (__smtx_elem_typeof_seq_value s)
            hs hreplSeq n

theorem model_eval_str_to_lower_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_to_lower v) := by
  cases v <;>
    simp [__smtx_model_eval_str_to_lower, __smtx_value_canonical,
      __smtx_value_canonical_bool, seq_canonical_pack_string]

theorem model_eval_str_to_upper_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_to_upper v) := by
  cases v <;>
    simp [__smtx_model_eval_str_to_upper, __smtx_value_canonical,
      __smtx_value_canonical_bool, seq_canonical_pack_string]

theorem model_eval_str_from_code_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_from_code v) := by
  cases v <;>
    simp [__smtx_model_eval_str_from_code, __smtx_value_canonical,
      __smtx_value_canonical_bool, seq_canonical_pack_string]

theorem model_eval_str_from_int_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_from_int v) := by
  cases v <;>
    simp [__smtx_model_eval_str_from_int, __smtx_value_canonical,
      __smtx_value_canonical_bool, seq_canonical_pack_string]

theorem model_eval_str_replace_all_canonical
    {v pat repl : SmtValue}
    (hv : __smtx_value_canonical v)
    (hpat : __smtx_value_canonical pat)
    (hrepl : __smtx_value_canonical repl) :
    __smtx_value_canonical (__smtx_model_eval_str_replace_all v pat repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_replace_all] using value_canonical_notValue
  case Seq s =>
    cases pat <;>
      try
        simpa [__smtx_model_eval_str_replace_all] using value_canonical_notValue
    case Seq p =>
      cases repl <;>
        try
          simpa [__smtx_model_eval_str_replace_all] using value_canonical_notValue
      case Seq r =>
        have hs : __smtx_seq_canonical s = true := by
          simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
        have hpatSeq : __smtx_seq_canonical p = true := by
          simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hpat
        have hreplSeq : __smtx_seq_canonical r = true := by
          simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hrepl
        simpa [__smtx_model_eval_str_replace_all, __smtx_value_canonical,
          __smtx_value_canonical_bool] using
          seq_canonical_pack_unpack_replace_all (__smtx_elem_typeof_seq_value s)
            hs hpatSeq hreplSeq

theorem model_eval_str_replace_re_canonical
    (v re repl : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_replace_re v re repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_replace_re] using value_canonical_notValue
  case Seq s =>
    cases re <;>
      try
        simpa [__smtx_model_eval_str_replace_re] using value_canonical_notValue
    case RegLan r =>
      cases repl <;>
        simp [__smtx_model_eval_str_replace_re, __smtx_value_canonical,
          __smtx_value_canonical_bool, seq_canonical_pack_string]

theorem model_eval_str_replace_re_all_canonical
    (v re repl : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_replace_re_all v re repl) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_str_replace_re_all] using value_canonical_notValue
  case Seq s =>
    cases re <;>
      try
        simpa [__smtx_model_eval_str_replace_re_all] using value_canonical_notValue
    case RegLan r =>
      cases repl <;>
        simp [__smtx_model_eval_str_replace_re_all, __smtx_value_canonical,
          __smtx_value_canonical_bool, seq_canonical_pack_string]

theorem model_eval_str_len_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_len v) := by
  cases v <;>
    simp [__smtx_model_eval_str_len, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_str_contains_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_contains v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_str_contains, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_str_indexof_canonical
    (v1 v2 v3 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_indexof v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval_str_indexof, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_str_indexof_re_canonical
    (v1 v2 v3 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_indexof_re v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    simp [__smtx_model_eval_str_indexof_re, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_str_to_code_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_to_code v) := by
  cases v <;>
    simp [__smtx_model_eval_str_to_code, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_str_to_int_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_to_int v) := by
  cases v <;>
    simp [__smtx_model_eval_str_to_int, value_canonical_notValue, value_canonical_numeral]

theorem model_eval_str_to_re_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_to_re v) := by
  cases v <;>
    simp [__smtx_model_eval_str_to_re, value_canonical_notValue, value_canonical_reglan]

theorem model_eval_re_mult_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_mult v) := by
  cases v <;>
    simp [__smtx_model_eval_re_mult, value_canonical_notValue, value_canonical_reglan]

theorem model_eval_re_concat_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_concat v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_re_concat, value_canonical_notValue, value_canonical_reglan]

theorem model_eval_re_inter_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_inter v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_re_inter, value_canonical_notValue, value_canonical_reglan]

theorem model_eval_re_union_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_union v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_re_union, value_canonical_notValue, value_canonical_reglan]

theorem model_eval_re_diff_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_diff v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_re_diff, value_canonical_notValue, value_canonical_reglan]

theorem model_eval_re_plus_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_plus v) := by
  simpa [__smtx_model_eval_re_plus] using
    model_eval_re_concat_canonical v (__smtx_model_eval_re_mult v)

theorem model_eval_re_opt_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_opt v) := by
  simpa [__smtx_model_eval_re_opt] using
    model_eval_re_union_canonical v
      (SmtValue.RegLan (native_str_to_re (native_unpack_string (SmtSeq.empty SmtType.Char))))

theorem model_eval_re_comp_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_comp v) := by
  cases v <;>
    simp [__smtx_model_eval_re_comp, value_canonical_notValue, value_canonical_reglan]

theorem model_eval_re_range_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_range v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_re_range, value_canonical_notValue, value_canonical_reglan]

theorem model_eval_re_exp_rec_canonical :
    ∀ n v, __smtx_value_canonical (__smtx_model_eval_re_exp_rec n v)
  | native_nat_zero, v => by
      simp [__smtx_model_eval_re_exp_rec, value_canonical_reglan]
  | native_nat_succ n, v => by
      simpa [__smtx_model_eval_re_exp_rec] using
        model_eval_re_concat_canonical (__smtx_model_eval_re_exp_rec n v) v

theorem model_eval_re_exp_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_exp v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_re_exp, value_canonical_notValue,
      model_eval_re_exp_rec_canonical]

theorem model_eval_re_loop_rec_canonical :
    ∀ n v1 v2 v3, __smtx_value_canonical (__smtx_model_eval_re_loop_rec n v1 v2 v3)
  | native_nat_zero, v1, v2, v3 => by
      cases v2 <;>
        simp [__smtx_model_eval_re_loop_rec, value_canonical_notValue,
          model_eval_re_exp_canonical]
  | native_nat_succ n, v1, v2, v3 => by
      cases v2 with
      | Numeral z =>
          simpa [__smtx_model_eval_re_loop_rec] using
            model_eval_re_union_canonical
              (__smtx_model_eval_re_loop_rec n v1
                (SmtValue.Numeral (native_zplus z (native_zneg 1))) v3)
              (__smtx_model_eval_re_exp (SmtValue.Numeral z) v3)
      | _ =>
          simp [__smtx_model_eval_re_loop_rec, value_canonical_notValue]

theorem model_eval_re_loop_canonical
    (v1 v2 v3 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_re_loop v1 v2 v3) := by
  cases v1 <;> cases v2 <;> cases v3 <;>
    try
      simpa [__smtx_model_eval_re_loop] using value_canonical_notValue
  case Numeral.Numeral.RegLan n1 n2 r =>
    simpa [__smtx_model_eval_re_loop] using
      model_eval_ite_canonical
        (t := SmtValue.RegLan native_re_none)
        (e := __smtx_model_eval_re_loop_rec (native_int_to_nat (native_zplus n2 (native_zneg n1)))
          (SmtValue.Numeral n1) (SmtValue.Numeral n2) (SmtValue.RegLan r))
        (value_canonical_reglan native_re_none)
        (model_eval_re_loop_rec_canonical _ _ _ _)

theorem model_eval_str_in_re_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_in_re v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_str_in_re, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_str_lt_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_lt v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_str_lt, value_canonical_notValue, value_canonical_boolean]

theorem model_eval_str_leq_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_leq v1 v2) := by
  simpa [__smtx_model_eval_str_leq] using
    model_eval_or_canonical (__smtx_model_eval_eq v1 v2) (__smtx_model_eval_str_lt v1 v2)

theorem model_eval_str_prefixof_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_prefixof v1 v2) := by
  simpa [__smtx_model_eval_str_prefixof] using
    model_eval_eq_canonical v1
      (__smtx_model_eval_str_substr v2 (SmtValue.Numeral 0) (__smtx_model_eval_str_len v1))

theorem model_eval_str_suffixof_canonical
    (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_suffixof v1 v2) := by
  simpa [__smtx_model_eval_str_suffixof] using
    model_eval_eq_canonical v1
      (__smtx_model_eval_str_substr v2
        (__smtx_model_eval__ (__smtx_model_eval_str_len v2) (__smtx_model_eval_str_len v1))
        (__smtx_model_eval_str_len v1))

theorem model_eval_str_is_digit_canonical
    (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_str_is_digit v) := by
  simpa [__smtx_model_eval_str_is_digit] using
    model_eval_and_canonical
      (__smtx_model_eval_leq (SmtValue.Numeral 48) (__smtx_model_eval_str_to_code v))
      (__smtx_model_eval_leq (__smtx_model_eval_str_to_code v) (SmtValue.Numeral 57))

theorem model_eval_set_empty_value_canonical
    (T : SmtType) :
    __smtx_value_canonical (SmtValue.Set (SmtMap.default T (SmtValue.Boolean false))) := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool,
    __smtx_map_canonical, __smtx_map_default_canonical, __smtx_typeof_value,
    __smtx_type_default, native_ite, native_veq, SmtEval.native_and]

theorem set_empty_map_canonical
    (T : SmtType) :
    __smtx_map_canonical (SmtMap.default T (SmtValue.Boolean false)) = true := by
  simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using
    model_eval_set_empty_value_canonical T

theorem model_eval_set_singleton_value_canonical
    {v : SmtValue}
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (__smtx_model_eval_set_singleton v) := by
  have hvBool : __smtx_value_canonical_bool v = true := by
    simpa [__smtx_value_canonical] using hv
  simp [__smtx_model_eval_set_singleton, __smtx_value_canonical,
    __smtx_value_canonical_bool, __smtx_map_canonical,
    __smtx_map_entries_ordered_after, __smtx_map_default_canonical,
    __smtx_typeof_value, __smtx_type_default, __smtx_msm_get_default,
    native_ite, native_veq, hvBool, SmtEval.native_and, SmtEval.native_not]

theorem mss_op_internal_canonical
    (isInter : native_Bool) :
    ∀ {m1 m2 acc : SmtMap},
      __smtx_map_canonical m1 = true ->
        __smtx_map_canonical acc = true ->
          __smtx_map_canonical (__smtx_mss_op_internal isInter m1 m2 acc) = true
  | SmtMap.default T efalse, m2, acc, _hm1, hacc => by
      simpa [__smtx_mss_op_internal] using hacc
  | SmtMap.cons e etrue m1, m2, acc, hm1, hacc => by
      have he : __smtx_value_canonical e := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.1.1
      have hmTail : __smtx_map_canonical m1 = true := by
        have hParts := hm1
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.2
      have htrue : __smtx_value_canonical (SmtValue.Boolean true) :=
        value_canonical_boolean true
      cases hCond :
          native_iff (native_veq (__smtx_msm_lookup m2 e) (SmtValue.Boolean true)) isInter
      · simpa [__smtx_mss_op_internal, hCond] using
          mss_op_internal_canonical isInter hmTail hacc
      · have hacc' :
            __smtx_map_canonical
              (__smtx_msm_update_aux (__smtx_msm_get_default acc) acc e
                (SmtValue.Boolean true)) = true :=
          map_update_aux_canonical hacc he htrue
        simpa [__smtx_mss_op_internal, hCond] using
          mss_op_internal_canonical isInter hmTail hacc'

theorem model_eval_set_inter_canonical
    {v1 v2 : SmtValue}
    (hv1 : __smtx_value_canonical v1)
    (_hv2 : __smtx_value_canonical v2) :
    __smtx_value_canonical (__smtx_model_eval_set_inter v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_set_inter, __smtx_set_inter] using
        value_canonical_notValue
  case Set.Set m1 m2 =>
    have hm1 : __smtx_map_canonical m1 = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv1
    exact value_canonical_set_of_map_canonical
      (mss_op_internal_canonical true hm1
        (set_empty_map_canonical (__smtx_index_typeof_map (__smtx_typeof_map_value m1))))

theorem model_eval_set_minus_canonical
    {v1 v2 : SmtValue}
    (hv1 : __smtx_value_canonical v1)
    (_hv2 : __smtx_value_canonical v2) :
    __smtx_value_canonical (__smtx_model_eval_set_minus v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_set_minus, __smtx_set_minus] using
        value_canonical_notValue
  case Set.Set m1 m2 =>
    have hm1 : __smtx_map_canonical m1 = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv1
    exact value_canonical_set_of_map_canonical
      (mss_op_internal_canonical false hm1
        (set_empty_map_canonical (__smtx_index_typeof_map (__smtx_typeof_map_value m1))))

theorem model_eval_set_union_canonical
    {v1 v2 : SmtValue}
    (hv1 : __smtx_value_canonical v1)
    (hv2 : __smtx_value_canonical v2) :
    __smtx_value_canonical (__smtx_model_eval_set_union v1 v2) := by
  cases v1 <;> cases v2 <;>
    try
      simpa [__smtx_model_eval_set_union, __smtx_set_union] using
        value_canonical_notValue
  case Set.Set m1 m2 =>
    have hm1 : __smtx_map_canonical m1 = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv1
    have hm2 : __smtx_map_canonical m2 = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv2
    exact value_canonical_set_of_map_canonical
      (mss_op_internal_canonical false hm1 hm2)

theorem model_eval_seq_nth_wrong_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : SmtSeq)
    (n : native_Int)
    (T : SmtType) :
    __smtx_value_canonical (__smtx_seq_nth_wrong M s n T) := by
  cases T with
  | Seq A =>
      let mapTy := SmtType.Map (SmtType.Seq A) (SmtType.Map SmtType.Int A)
      by_cases hTy : __smtx_type_wf mapTy = true
      · have hLookup : __smtx_value_canonical
            (__smtx_model_lookup M native_oob_seq_nth_id mapTy) :=
          model_total_typed_lookup_canonical hM native_oob_seq_nth_id mapTy hTy
        have hFirst : __smtx_value_canonical
            (__smtx_model_eval_select
              (__smtx_model_lookup M native_oob_seq_nth_id mapTy)
              (SmtValue.Seq s)) :=
          model_eval_select_canonical hLookup
        have hSecond : __smtx_value_canonical
            (__smtx_model_eval_select
              (__smtx_model_eval_select
                (__smtx_model_lookup M native_oob_seq_nth_id mapTy)
                (SmtValue.Seq s))
              (SmtValue.Numeral n)) :=
          model_eval_select_canonical hFirst
        simpa [__smtx_seq_nth_wrong, mapTy, __smtx_model_eval_select] using
          hSecond
      · have hLookup :
            __smtx_model_lookup M native_oob_seq_nth_id mapTy = SmtValue.NotValue :=
          model_total_typed_lookup_not_wf hM native_oob_seq_nth_id mapTy (by
            cases hWF : __smtx_type_wf mapTy <;> simp [hWF] at hTy ⊢)
        simpa [__smtx_seq_nth_wrong, mapTy, hLookup, __smtx_map_select] using
          value_canonical_notValue
  | _ =>
      simpa [__smtx_seq_nth_wrong] using value_canonical_notValue

theorem seq_nth_aux_canonical :
    ∀ {s : SmtSeq} {n : native_Int} {d : SmtValue},
      __smtx_seq_canonical s = true ->
        __smtx_value_canonical d ->
          __smtx_value_canonical (__smtx_ssm_seq_nth s n d)
  | SmtSeq.empty T, n, d, _hs, hd => by
      simpa [__smtx_ssm_seq_nth] using hd
  | SmtSeq.cons v vs, n, d, hs, hd => by
      have hv : __smtx_value_canonical v := by
        have hParts := hs
        simp [__smtx_seq_canonical, SmtEval.native_and] at hParts
        exact hParts.1
      have hvs : __smtx_seq_canonical vs = true := by
        have hParts := hs
        simp [__smtx_seq_canonical, SmtEval.native_and] at hParts
        exact hParts.2
      by_cases hn : n = 0
      · subst n
        simpa [__smtx_ssm_seq_nth] using hv
      · have hRec :
            __smtx_value_canonical
              (__smtx_ssm_seq_nth vs (native_zplus n (native_zneg 1)) d) :=
          seq_nth_aux_canonical hvs hd
        simpa [__smtx_ssm_seq_nth, hn] using hRec

theorem model_eval_seq_nth_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    {v i : SmtValue}
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (__smtx_seq_nth M v i) := by
  cases v <;> cases i <;>
    try
      simpa [__smtx_seq_nth] using value_canonical_notValue
  case Seq.Numeral s n =>
    have hs : __smtx_seq_canonical s = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    exact seq_nth_aux_canonical hs
      (model_eval_seq_nth_wrong_canonical M hM s n (__smtx_typeof_seq_value s))

theorem vsm_apply_arg_nth_canonical :
    ∀ {v : SmtValue} {n npos : native_Nat},
      __smtx_value_canonical v ->
        __smtx_value_canonical (__vsm_apply_arg_nth v n npos)
  | SmtValue.Apply f a, n, npos, hv => by
      cases npos with
      | zero =>
          simpa [__vsm_apply_arg_nth] using value_canonical_notValue
      | succ npos =>
          have hf : __smtx_value_canonical f := by
            have hParts := hv
            simp [__smtx_value_canonical, __smtx_value_canonical_bool,
              SmtEval.native_and] at hParts
            exact hParts.1
          have ha : __smtx_value_canonical a := by
            have hParts := hv
            simp [__smtx_value_canonical, __smtx_value_canonical_bool,
              SmtEval.native_and] at hParts
            exact hParts.2
          cases hEq : native_nateq n npos
          · simpa [__vsm_apply_arg_nth, hEq] using
              vsm_apply_arg_nth_canonical hf
          · simpa [__vsm_apply_arg_nth, hEq] using ha
  | SmtValue.NotValue, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.Boolean b, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.Numeral k, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.Rational q, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.Binary w k, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.Map m, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.Fun m, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.Set m, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.Seq s, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.Char c, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.UValue u k, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.RegLan r, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue
  | SmtValue.DtCons s d i, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using value_canonical_notValue

theorem model_eval_dt_sel_wrong_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (d : SmtDatatype)
    (n m : native_Nat)
    (v : SmtValue) :
    __smtx_value_canonical
      (__smtx_map_select
        (__smtx_map_select
          (__smtx_map_select
            (__smtx_model_lookup M native_wrong_apply_sel_id
              (SmtType.Map SmtType.Int
                (SmtType.Map SmtType.Int
                  (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)))))
            (SmtValue.Numeral (native_nat_to_int n)))
          (SmtValue.Numeral (native_nat_to_int m))) v) := by
  let mapTy :=
    SmtType.Map SmtType.Int
      (SmtType.Map SmtType.Int
        (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)))
  by_cases hTy : __smtx_type_wf mapTy = true
  · have hLookup : __smtx_value_canonical
        (__smtx_model_lookup M native_wrong_apply_sel_id mapTy) :=
      model_total_typed_lookup_canonical hM native_wrong_apply_sel_id mapTy hTy
    have h1 : __smtx_value_canonical
        (__smtx_model_eval_select
          (__smtx_model_lookup M native_wrong_apply_sel_id mapTy)
          (SmtValue.Numeral (native_nat_to_int n))) :=
      model_eval_select_canonical hLookup
    have h2 : __smtx_value_canonical
        (__smtx_model_eval_select
          (__smtx_model_eval_select
            (__smtx_model_lookup M native_wrong_apply_sel_id mapTy)
            (SmtValue.Numeral (native_nat_to_int n)))
          (SmtValue.Numeral (native_nat_to_int m))) :=
      model_eval_select_canonical h1
    have h3 : __smtx_value_canonical
        (__smtx_model_eval_select
          (__smtx_model_eval_select
            (__smtx_model_eval_select
              (__smtx_model_lookup M native_wrong_apply_sel_id mapTy)
              (SmtValue.Numeral (native_nat_to_int n)))
            (SmtValue.Numeral (native_nat_to_int m))) v) :=
      model_eval_select_canonical h2
    simpa [mapTy, __smtx_model_eval_select] using h3
  · have hLookup :
        __smtx_model_lookup M native_wrong_apply_sel_id mapTy = SmtValue.NotValue :=
      model_total_typed_lookup_not_wf hM native_wrong_apply_sel_id mapTy (by
        cases hWF : __smtx_type_wf mapTy <;> simp [hWF] at hTy ⊢)
    simpa [mapTy, hLookup, __smtx_map_select] using value_canonical_notValue

theorem model_eval_dt_sel_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (d : SmtDatatype)
    (n m : native_Nat)
    {v : SmtValue}
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (__smtx_model_eval_dt_sel M s d n m v) := by
  unfold __smtx_model_eval_dt_sel
  cases hEq : native_veq (__vsm_apply_head v) (SmtValue.DtCons s d n)
  · simpa [native_ite, hEq] using
      model_eval_dt_sel_wrong_canonical M hM s d n m v
  · simpa [native_ite, hEq] using
      vsm_apply_arg_nth_canonical (v := v) (n := m)
        (npos := __smtx_dt_num_sels d n) hv

/--
Store canonicality reduces to the map-update canonicality theorem. This isolates
the remaining sorted-map preservation obligation from the value-level evaluator.
-/
theorem model_eval_store_canonical_of_map_update
    {m : SmtMap}
    {i e : SmtValue}
    (hUpdate :
      __smtx_map_canonical
        (__smtx_msm_update_aux (__smtx_msm_get_default m) m i e) = true) :
    __smtx_value_canonical
      (__smtx_model_eval_store (SmtValue.Map m) i e) := by
  simpa [__smtx_model_eval_store, __smtx_map_store,
    __smtx_value_canonical, __smtx_value_canonical_bool] using hUpdate

/-- Set-store canonicality has the same map-update obligation as array-store. -/
theorem model_eval_store_canonical_of_set_update
    {m : SmtMap}
    {i e : SmtValue}
    (hUpdate :
      __smtx_map_canonical
        (__smtx_msm_update_aux (__smtx_msm_get_default m) m i e) = true) :
    __smtx_value_canonical
      (__smtx_model_eval_store (SmtValue.Set m) i e) := by
  simpa [__smtx_model_eval_store, __smtx_map_store,
    __smtx_value_canonical, __smtx_value_canonical_bool] using hUpdate

/-- Map-store preserves canonicality, assuming the strict-order laws of `native_vcmp`. -/
theorem model_eval_store_canonical_of_map
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true)
    {m : SmtMap}
    {i e : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hi : __smtx_value_canonical i)
    (he : __smtx_value_canonical e) :
    __smtx_value_canonical
      (__smtx_model_eval_store (SmtValue.Map m) i e) := by
  exact model_eval_store_canonical_of_map_update
    (map_update_aux_canonical_of_order_laws hFlip hTrans hm hi he)

/-- Set-store preserves canonicality, assuming the strict-order laws of `native_vcmp`. -/
theorem model_eval_store_canonical_of_set
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true)
    {m : SmtMap}
    {i e : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hi : __smtx_value_canonical i)
    (he : __smtx_value_canonical e) :
    __smtx_value_canonical
      (__smtx_model_eval_store (SmtValue.Set m) i e) := by
  exact model_eval_store_canonical_of_set_update
    (map_update_aux_canonical_of_order_laws hFlip hTrans hm hi he)

/-- Value-level store preserves canonicality modulo the strict-order laws of `native_vcmp`. -/
theorem model_eval_store_canonical_of_order_laws
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true)
    {v i e : SmtValue}
    (hv : __smtx_value_canonical v)
    (hi : __smtx_value_canonical i)
    (he : __smtx_value_canonical e) :
    __smtx_value_canonical (__smtx_model_eval_store v i e) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_store, __smtx_map_store] using
        value_canonical_notValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    exact model_eval_store_canonical_of_map hFlip hTrans hm hi he
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    exact model_eval_store_canonical_of_set hFlip hTrans hm hi he

/--
Value-level store preserves canonicality, using the temporary `native_vcmp`
order-law assumptions.
-/
theorem model_eval_store_canonical
    {v i e : SmtValue}
    (hv : __smtx_value_canonical v)
    (hi : __smtx_value_canonical i)
    (he : __smtx_value_canonical e) :
    __smtx_value_canonical (__smtx_model_eval_store v i e) :=
  model_eval_store_canonical_of_order_laws
    (fun hNe hCmp => native_vcmp_flip hNe hCmp)
    (fun hAB hBC => native_vcmp_trans hAB hBC)
    hv hi he

end Smtm
