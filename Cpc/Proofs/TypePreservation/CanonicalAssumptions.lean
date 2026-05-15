import Cpc.SmtModel

open SmtEval
open Smtm

namespace Smtm

private theorem cpc_map_lookup_typed_for_assumption :
    ∀ {m : SmtMap} {A B : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_typeof_value i = A ->
        __smtx_typeof_value (__smtx_msm_lookup m i) = B
  | SmtMap.default T e, A, B, i, hMap, _hi => by
      cases hMap
      simp [__smtx_msm_lookup]
  | SmtMap.cons j e m, A, B, i, hMap, hi => by
      by_cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · have hm : __smtx_typeof_map_value m = SmtType.Map A B := by
          simpa [__smtx_typeof_map_value, native_ite, hEq] using hMap
        have hEq' :
            SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e) =
              __smtx_typeof_map_value m := by
          simpa [native_Teq] using hEq
        have hHead :
            SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e) =
              SmtType.Map A B := hEq'.trans hm
        have he : __smtx_typeof_value e = B := by
          cases hHead
          rfl
        have hRec : __smtx_typeof_value (__smtx_msm_lookup m i) = B :=
          cpc_map_lookup_typed_for_assumption hm hi
        by_cases hVeq : native_veq j i
        · simpa [__smtx_msm_lookup, native_ite, hVeq] using he
        · simpa [__smtx_msm_lookup, native_ite, hVeq] using hRec
      · simp [__smtx_typeof_map_value, native_ite, hEq] at hMap

private theorem cpc_model_eval_eq_false_of_native_veq_false_non_reglan
    {v1 v2 : SmtValue} {B : SmtType}
    (hTy1 : __smtx_typeof_value v1 = B)
    (hTy2 : __smtx_typeof_value v2 = B)
    (hB : B ≠ SmtType.RegLan)
    (hNe : native_veq v1 v2 = false) :
    __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_eq, native_veq, __smtx_typeof_value] at hTy1 hTy2 hB hNe ⊢
  all_goals try assumption
  exact False.elim (hB hTy1.symm)

/--
The remaining datatype-default canonicity assumption.

This isolates the open proof obligation needed to build canonical inhabitants
for well-formed datatype types.
-/
theorem cpc_datatype_type_default_typed_canonical_assumption
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  sorry

/--
Native lookup witness property for `map_diff` on canonical typed maps.

This is the remaining canonical finite-map extensionality/fresh-index argument:
if two canonical maps of the same type are structurally unequal, then some
typed canonical index has structurally different lookup values.  The finite
domain case uses canonical default normalization; the infinite domain case
needs a fresh typed canonical index outside both finite spines.
-/
theorem cpc_map_diff_typed_canonical_lookup_witness_assumption
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (_hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (_hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (_hm1Can : __smtx_map_canonical m1 = true)
    (_hm2Can : __smtx_map_canonical m2 = true)
    (_hDefaultTy : __smtx_typeof_value (__smtx_type_default A) = A)
    (_hDefaultCan : __smtx_value_canonical (__smtx_type_default A))
    (_hNe : __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
      SmtValue.Boolean false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical_bool i = true ∧
          native_veq (__smtx_msm_lookup m1 i)
            (__smtx_msm_lookup m2 i) = false := by
  sorry

/--
Semantic witness property for `map_diff` on canonical typed maps.

The executable definition of `native_eval_map_diff_msm` chooses an index whose
lookups are syntactically different when such an index exists.  Away from
`RegLan`, syntactic and model equality coincide for values of the element type.
-/
theorem cpc_map_diff_selects_model_eval_eq_false_assumption
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hm1Can : __smtx_map_canonical m1 = true)
    (hm2Can : __smtx_map_canonical m2 = true)
    (hDefaultTy : __smtx_typeof_value (__smtx_type_default A) = A)
    (hDefaultCan : __smtx_value_canonical (__smtx_type_default A))
    (hBNeRegLan : B ≠ SmtType.RegLan)
    (hNe : __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
      SmtValue.Boolean false) :
    __smtx_model_eval_eq
        (__smtx_msm_lookup m1 (native_eval_map_diff_msm m1 m2))
        (__smtx_msm_lookup m2 (native_eval_map_diff_msm m1 m2)) =
      SmtValue.Boolean false := by
  classical
  change
    __smtx_model_eval_eq
        (__smtx_msm_lookup m1 (native_eval_map_diff_msm m1 m2))
        (__smtx_msm_lookup m2 (native_eval_map_diff_msm m1 m2)) =
      SmtValue.Boolean false
  rw [hm1Ty, hm2Ty]
  simp [native_ite, native_Teq, SmtEval.native_and]
  by_cases hDiff :
      ∃ i : SmtValue,
        __smtx_typeof_value i = A ∧
          __smtx_value_canonical_bool i = true ∧
            native_veq (__smtx_msm_lookup m1 i)
              (__smtx_msm_lookup m2 i) = false
  · have hSpec := Classical.choose_spec hDiff
    have hLookup1Ty :
        __smtx_typeof_value
            (__smtx_msm_lookup m1 (Classical.choose hDiff)) = B :=
      cpc_map_lookup_typed_for_assumption hm1Ty hSpec.1
    have hLookup2Ty :
        __smtx_typeof_value
            (__smtx_msm_lookup m2 (Classical.choose hDiff)) = B :=
      cpc_map_lookup_typed_for_assumption hm2Ty hSpec.1
    have hFalse :
        __smtx_model_eval_eq
            (__smtx_msm_lookup m1 (Classical.choose hDiff))
            (__smtx_msm_lookup m2 (Classical.choose hDiff)) =
          SmtValue.Boolean false :=
      cpc_model_eval_eq_false_of_native_veq_false_non_reglan
        hLookup1Ty hLookup2Ty hBNeRegLan hSpec.2.2
    simpa [hDiff] using hFalse
  · exact False.elim (hDiff
      (cpc_map_diff_typed_canonical_lookup_witness_assumption
        m1 m2 A B hm1Ty hm2Ty hm1Can hm2Can hDefaultTy hDefaultCan hNe))

end Smtm
