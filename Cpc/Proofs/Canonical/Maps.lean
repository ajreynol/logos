import Cpc.Proofs.Canonical.Basic

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- The default payload of a canonical map is canonical. -/
theorem map_default_value_canonical :
    ∀ {m : SmtMap},
      __smtx_map_canonical m = true ->
        __smtx_value_canonical (__smtx_msm_get_default m)
  | SmtMap.default T e, h => by
      have hParts := h
      simp [__smtx_map_canonical, SmtEval.native_and] at hParts
      exact hParts.2
  | SmtMap.cons i e m, h => by
      have hm : __smtx_map_canonical m = true := by
        have hParts := h
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.2
      simpa [__smtx_msm_get_default] using map_default_value_canonical hm

/-- Entries in a canonical map have canonical values. -/
theorem map_lookup_value_canonical :
    ∀ {m : SmtMap} {i : SmtValue},
      __smtx_map_canonical m = true ->
        __smtx_value_canonical (__smtx_msm_lookup m i)
  | SmtMap.default T e, i, h => by
      simpa [__smtx_msm_lookup] using
        map_default_value_canonical (m := SmtMap.default T e) h
  | SmtMap.cons k v m, i, h => by
      have hv : __smtx_value_canonical v := by
        have hParts := h
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.1.2
      have hm : __smtx_map_canonical m = true := by
        have hParts := h
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.2
      cases hki : native_veq k i
      · simpa [__smtx_msm_lookup, native_ite, hki] using
          map_lookup_value_canonical (m := m) (i := i) hm
      · simpa [__smtx_msm_lookup, native_ite, hki] using hv

/-- Canonical maps give canonical `Map` values. -/
theorem value_canonical_map_of_map_canonical
    {m : SmtMap}
    (h : __smtx_map_canonical m = true) :
    __smtx_value_canonical (SmtValue.Map m) := by
  simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using h

/-- Canonical maps give canonical `Set` values. -/
theorem value_canonical_set_of_map_canonical
    {m : SmtMap}
    (h : __smtx_map_canonical m = true) :
    __smtx_value_canonical (SmtValue.Set m) := by
  simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using h

/--
The non-recursive insertion helper preserves map canonicality when it is used at
a position that is already known to be ordered with respect to the tail map.
-/
theorem map_update_aux_no_default_canonical
    {m : SmtMap}
    {i e : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hi : __smtx_value_canonical i)
    (he : __smtx_value_canonical e)
    (hOrd : __smtx_map_entries_ordered_after i m = true) :
    __smtx_map_canonical
      (__smtx_msm_update_aux_no_default (__smtx_msm_get_default m) m i e) = true := by
  by_cases hEq : native_veq (__smtx_msm_get_default m) e = true
  · simpa [__smtx_msm_update_aux_no_default, native_ite, hEq] using hm
  · have hEqFalse : native_veq (__smtx_msm_get_default m) e = false := by
      cases hEqBool : native_veq (__smtx_msm_get_default m) e <;>
        simp [hEqBool] at hEq ⊢
    have hSymm : native_veq e (__smtx_msm_get_default m) = false :=
      native_veq_false_symm hEqFalse
    have hiBool : __smtx_value_canonical_bool i = true := by
      simpa [__smtx_value_canonical] using hi
    have heBool : __smtx_value_canonical_bool e = true := by
      simpa [__smtx_value_canonical] using he
    simp [__smtx_msm_update_aux_no_default, __smtx_map_canonical, native_ite,
      hEqFalse, hiBool, heBool, hm, hOrd, hSymm, SmtEval.native_and,
      SmtEval.native_not]

/-- Selecting from a canonical map value returns a canonical value. -/
theorem model_eval_select_canonical_of_map
    {m : SmtMap}
    {i : SmtValue}
    (hm : __smtx_map_canonical m = true) :
    __smtx_value_canonical
      (__smtx_model_eval_select (SmtValue.Map m) i) := by
  simpa [__smtx_model_eval_select, __smtx_map_select] using
    map_lookup_value_canonical (m := m) (i := i) hm

/-- Selecting from a canonical set value returns a canonical value. -/
theorem model_eval_select_canonical_of_set
    {m : SmtMap}
    {i : SmtValue}
    (hm : __smtx_map_canonical m = true) :
    __smtx_value_canonical
      (__smtx_model_eval_select (SmtValue.Set m) i) := by
  simpa [__smtx_model_eval_select, __smtx_map_select] using
    map_lookup_value_canonical (m := m) (i := i) hm

/-- Value-level select preserves canonicality of its map/set argument. -/
theorem model_eval_select_canonical
    {v i : SmtValue}
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (__smtx_model_eval_select v i) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_select, __smtx_map_select] using
        value_canonical_notValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    exact model_eval_select_canonical_of_map (m := ‹SmtMap›) (i := i) hm
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    exact model_eval_select_canonical_of_set (m := ‹SmtMap›) (i := i) hm

end Smtm
