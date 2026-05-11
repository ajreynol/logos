import Cpc.Proofs.Canonical.Maps

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
