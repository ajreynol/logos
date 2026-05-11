import Cpc.Proofs.Canonical.Order

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

/-- The non-recursive update helper preserves the map default. -/
theorem map_update_aux_no_default_get_default
    (ed : SmtValue) (m : SmtMap) (i e : SmtValue) :
    __smtx_msm_get_default (__smtx_msm_update_aux_no_default ed m i e) =
      __smtx_msm_get_default m := by
  cases hEq : native_veq ed e <;>
    simp [__smtx_msm_update_aux_no_default, native_ite, hEq, __smtx_msm_get_default]

/-- The recursive update helper preserves the map default. -/
theorem map_update_aux_get_default
    (ed : SmtValue) :
    ∀ (m : SmtMap) (i e : SmtValue),
      __smtx_msm_get_default (__smtx_msm_update_aux ed m i e) =
        __smtx_msm_get_default m
  | SmtMap.default T d, i, e => by
      simpa [__smtx_msm_update_aux] using
        map_update_aux_no_default_get_default ed (SmtMap.default T d) i e
  | SmtMap.cons k v m, i, e => by
      cases hEq : native_veq k i
      · cases hCmp : native_vcmp k i
        · simp [__smtx_msm_update_aux, native_ite, hEq, hCmp,
            __smtx_msm_get_default, map_update_aux_get_default ed m i e]
        · simpa [__smtx_msm_update_aux, native_ite, hEq, hCmp] using
            map_update_aux_no_default_get_default ed (SmtMap.cons k v m) i e
      · simpa [__smtx_msm_update_aux, native_ite, hEq] using
          map_update_aux_no_default_get_default ed m i e

/--
If every entry of `m` is below `lo`, and `lo < hi`, then every entry of `m`
is below `hi`.
-/
theorem map_entries_ordered_after_trans
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true) :
    ∀ {m : SmtMap} {lo hi : SmtValue},
      __smtx_map_canonical m = true ->
        __smtx_map_entries_ordered_after lo m = true ->
          native_vcmp lo hi = true ->
            __smtx_map_entries_ordered_after hi m = true
  | SmtMap.default T e, lo, hi, _hm, _hOrd, _hLoHi => by
      simp [__smtx_map_entries_ordered_after]
  | SmtMap.cons k v m, lo, hi, _hm, hOrd, hLoHi => by
      exact hTrans hOrd hLoHi

/--
The one-step insertion helper preserves an external upper bound, provided the
new key is also below that bound.
-/
theorem map_update_aux_no_default_entries_ordered_after
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    {ed : SmtValue}
    {m : SmtMap}
    {upper i e : SmtValue}
    (hOrd : __smtx_map_entries_ordered_after upper m = true)
    (hNe : native_veq upper i = false)
    (hCmp : native_vcmp upper i = false) :
    __smtx_map_entries_ordered_after upper
      (__smtx_msm_update_aux_no_default ed m i e) = true := by
  cases hEd : native_veq ed e
  · have hIUpper : native_vcmp i upper = true := hFlip hNe hCmp
    simp [__smtx_msm_update_aux_no_default, native_ite, hEd,
      __smtx_map_entries_ordered_after, hIUpper]
  · simpa [__smtx_msm_update_aux_no_default, native_ite, hEd] using hOrd

/--
Updating a canonical map at an index below `upper` keeps the updated map below
`upper`, assuming the intended strict-order laws of `native_vcmp`.
-/
theorem map_update_aux_entries_ordered_after
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true) :
    ∀ (ed : SmtValue) {m : SmtMap} {upper i e : SmtValue},
      __smtx_map_canonical m = true ->
        __smtx_map_entries_ordered_after upper m = true ->
          native_veq upper i = false ->
            native_vcmp upper i = false ->
              __smtx_map_entries_ordered_after upper
                (__smtx_msm_update_aux ed m i e) = true
  | ed, SmtMap.default T d, upper, i, e, _hm, _hOrd, hNe, hCmp => by
      simpa [__smtx_msm_update_aux] using
        map_update_aux_no_default_entries_ordered_after hFlip
          (ed := ed) (m := SmtMap.default T d) (upper := upper)
          (i := i) (e := e) (by simp [__smtx_map_entries_ordered_after])
          hNe hCmp
  | ed, SmtMap.cons k v m, upper, i, e, hmCons, hOrdUpper, hNe, hCmp => by
      cases hEq : native_veq k i
      · cases hLt : native_vcmp k i
        · simpa [__smtx_msm_update_aux, native_ite, hEq, hLt,
            __smtx_map_entries_ordered_after] using hOrdUpper
        · simpa [__smtx_msm_update_aux, native_ite, hEq, hLt] using
            map_update_aux_no_default_entries_ordered_after hFlip
              (ed := ed) (m := SmtMap.cons k v m) (upper := upper)
              (i := i) (e := e) hOrdUpper hNe hCmp
      · have hki : k = i := eq_of_native_veq_true hEq
        subst i
        have hIUpper : native_vcmp k upper = true := hFlip hNe hCmp
        have hm : __smtx_map_canonical m = true := by
          have hParts := hmCons
          simp [__smtx_map_canonical, SmtEval.native_and] at hParts
          rcases hParts with ⟨hMain, _hNeDefault⟩
          rcases hMain with ⟨hEntries, _hOrdered⟩
          exact hEntries.2
        have hOrdTailK : __smtx_map_entries_ordered_after k m = true := by
          have hParts := hmCons
          simp [__smtx_map_canonical, SmtEval.native_and] at hParts
          rcases hParts with ⟨hMain, _hNeDefault⟩
          exact hMain.2
        have hOrdTailUpper : __smtx_map_entries_ordered_after upper m = true :=
          map_entries_ordered_after_trans hTrans hm hOrdTailK hIUpper
        simpa [__smtx_msm_update_aux, native_ite, hEq] using
          map_update_aux_no_default_entries_ordered_after hFlip
            (ed := ed) (m := m) (upper := upper) (i := k) (e := e)
            hOrdTailUpper hNe hCmp

/--
Canonicality of the recursive map update, parameterized by the strict-order laws
that `native_vcmp` is intended to satisfy.
-/
theorem map_update_aux_canonical_of_order_laws
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true) :
    ∀ {m : SmtMap} {i e : SmtValue},
      __smtx_map_canonical m = true ->
        __smtx_value_canonical i ->
          __smtx_value_canonical e ->
            __smtx_map_canonical
              (__smtx_msm_update_aux (__smtx_msm_get_default m) m i e) = true
  | SmtMap.default T d, i, e, hm, hi, he => by
      exact map_update_aux_no_default_canonical hm hi he (by simp [__smtx_map_entries_ordered_after])
  | SmtMap.cons k v m, i, e, hmCons, hi, he => by
      have hk : __smtx_value_canonical k := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.1.1
      have hv : __smtx_value_canonical v := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.1.2
      have hm : __smtx_map_canonical m = true := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        rcases hMain with ⟨hEntries, _hOrdered⟩
        exact hEntries.2
      have hOrdTailK : __smtx_map_entries_ordered_after k m = true := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        rcases hParts with ⟨hMain, _hNeDefault⟩
        exact hMain.2
      have hNeDefault : native_veq v (__smtx_msm_get_default m) = false := by
        have hParts := hmCons
        simp [__smtx_map_canonical, SmtEval.native_and, SmtEval.native_not] at hParts
        rcases hParts with ⟨_hMain, hNe⟩
        exact hNe
      cases hEq : native_veq k i
      · cases hLt : native_vcmp k i
        · have hTailCanon :
            __smtx_map_canonical
              (__smtx_msm_update_aux (__smtx_msm_get_default m) m i e) = true :=
              map_update_aux_canonical_of_order_laws hFlip hTrans hm hi he
          have hOrdUpdated :
              __smtx_map_entries_ordered_after k
                (__smtx_msm_update_aux (__smtx_msm_get_default m) m i e) = true :=
            map_update_aux_entries_ordered_after hFlip hTrans
              (__smtx_msm_get_default m) hm hOrdTailK hEq hLt
          have hDefault :
              __smtx_msm_get_default
                (__smtx_msm_update_aux (__smtx_msm_get_default m) m i e) =
                  __smtx_msm_get_default m :=
            map_update_aux_get_default (__smtx_msm_get_default m) m i e
          have hkBool : __smtx_value_canonical_bool k = true := by
            simpa [__smtx_value_canonical] using hk
          have hvBool : __smtx_value_canonical_bool v = true := by
            simpa [__smtx_value_canonical] using hv
          simp [__smtx_msm_update_aux, __smtx_msm_get_default, native_ite, hEq,
            hLt, __smtx_map_canonical, hkBool, hvBool, hTailCanon,
            hOrdUpdated, hDefault, hNeDefault,
            SmtEval.native_and, SmtEval.native_not]
        · simpa [__smtx_msm_update_aux, native_ite, hEq, hLt] using
            map_update_aux_no_default_canonical hmCons hi he
              (by simpa [__smtx_map_entries_ordered_after] using hLt)
      · have hki : k = i := eq_of_native_veq_true hEq
        subst i
        simpa [__smtx_msm_update_aux, native_ite, hEq, __smtx_msm_get_default] using
          map_update_aux_no_default_canonical hm hi he hOrdTailK

/--
Canonicality of the recursive map update, using the temporary `native_vcmp`
order-law assumptions.
-/
theorem map_update_aux_canonical
    {m : SmtMap}
    {i e : SmtValue}
    (hm : __smtx_map_canonical m = true)
    (hi : __smtx_value_canonical i)
    (he : __smtx_value_canonical e) :
    __smtx_map_canonical
      (__smtx_msm_update_aux (__smtx_msm_get_default m) m i e) = true :=
  map_update_aux_canonical_of_order_laws
    (fun hNe hCmp => native_vcmp_flip hNe hCmp)
    (fun hAB hBC => native_vcmp_trans hAB hBC)
    hm hi he

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
