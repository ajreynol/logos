import Cpc.SmtModel

open SmtEval
open Smtm

namespace Smtm

/--
Datatype-default canonicity for the generated model.

The theorem keeps the historical `_assumption` name used by the downstream
proof skeleton, but `native_inhabited_type` now uniformly carries exactly this
canonical default witness.
-/
theorem cpc_datatype_type_default_typed_canonical_assumption
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  classical
  simpa [native_inhabited_type, __smtx_value_canonical, native_and] using _hInh

private def smt_map_keys : SmtMap -> List SmtValue
  | SmtMap.cons i _ m => i :: smt_map_keys m
  | SmtMap.default _ _ => []

/--
Fresh value assumption for well-formed infinite SMT types.

This is the real infinitude/cardinality statement needed by array extensionality:
given a finite avoid list, an inhabited recursively well-formed type classified
as infinite has a typed canonical value syntactically distinct from every value
in the avoid list.
-/
theorem cpc_fresh_typed_canonical_value_for_infinite_type_assumption
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A native_reflist_nil = true)
    (_hInfinite : __smtx_is_finite_type A = false)
    (avoid : List SmtValue) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical_bool i = true ∧
          ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false := by
  sorry

private theorem msm_lookup_eq_default_of_fresh_keys :
    ∀ (m : SmtMap) (i : SmtValue),
      (∀ j : SmtValue, j ∈ smt_map_keys m -> native_veq j i = false) ->
        __smtx_msm_lookup m i = __smtx_msm_get_default m
  | SmtMap.default T e, i, _hFresh => by
      simp [__smtx_msm_lookup, __smtx_msm_get_default]
  | SmtMap.cons j e m, i, hFresh => by
      have hj : native_veq j i = false := hFresh j (by simp [smt_map_keys])
      have hmFresh :
          ∀ k : SmtValue, k ∈ smt_map_keys m -> native_veq k i = false := by
        intro k hk
        exact hFresh k (by simp [smt_map_keys, hk])
      have hmLookup :
          __smtx_msm_lookup m i = __smtx_msm_get_default m :=
        msm_lookup_eq_default_of_fresh_keys m i hmFresh
      simpa [smt_map_keys, __smtx_msm_lookup, __smtx_msm_get_default,
        native_ite, hj] using hmLookup

/--
Fresh-index theorem for infinite map domains.

When the executable map-difference proof needs to compare the two default
payloads of canonical maps over an infinite domain, it needs a typed canonical
index outside both finite spines.
-/
theorem cpc_fresh_default_lookup_for_infinite_map_domain_assumption
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (_hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (_hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (_hm1Can : __smtx_map_canonical m1 = true)
    (_hm2Can : __smtx_map_canonical m2 = true)
    (hAInh : native_inhabited_type A = true)
    (hARec : __smtx_type_wf_rec A native_reflist_nil = true)
    (_hInfinite : __smtx_is_finite_type A = false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical_bool i = true ∧
          __smtx_msm_lookup m1 i = __smtx_msm_get_default m1 ∧
            __smtx_msm_lookup m2 i = __smtx_msm_get_default m2 := by
  rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
      A hAInh hARec _hInfinite (smt_map_keys m1 ++ smt_map_keys m2) with
    ⟨i, hiTy, hiCan, hiFresh⟩
  refine ⟨i, hiTy, hiCan, ?_, ?_⟩
  · exact msm_lookup_eq_default_of_fresh_keys m1 i (by
      intro j hj
      exact hiFresh j (by simp [hj]))
  · exact msm_lookup_eq_default_of_fresh_keys m2 i (by
      intro j hj
      exact hiFresh j (by simp [hj]))

end Smtm
