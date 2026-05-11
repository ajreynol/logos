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

theorem model_eval_set_empty_value_canonical
    (T : SmtType) :
    __smtx_value_canonical (SmtValue.Set (SmtMap.default T (SmtValue.Boolean false))) := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool,
    __smtx_map_canonical, __smtx_map_default_canonical, __smtx_typeof_value,
    __smtx_finite_type_default, native_ite, native_veq, SmtEval.native_and]

theorem model_eval_set_singleton_value_canonical
    {v : SmtValue}
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (__smtx_model_eval_set_singleton v) := by
  have hvBool : __smtx_value_canonical_bool v = true := by
    simpa [__smtx_value_canonical] using hv
  simp [__smtx_model_eval_set_singleton, __smtx_value_canonical,
    __smtx_value_canonical_bool, __smtx_map_canonical,
    __smtx_map_entries_ordered_after, __smtx_map_default_canonical,
    __smtx_typeof_value, __smtx_finite_type_default, __smtx_msm_get_default,
    native_ite, native_veq, hvBool, SmtEval.native_and, SmtEval.native_not]

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

end Smtm
