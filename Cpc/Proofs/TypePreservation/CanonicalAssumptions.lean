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

/--
Fresh-index assumption for infinite map domains.

When the executable map-difference proof needs to compare the two default
payloads of canonical maps over an infinite domain, it needs a typed canonical
index outside both finite spines.  This isolates that remaining infinitude
argument; the surrounding `map_diff` witness proof lives in array rule support,
where canonical map extensionality is available without creating an import
cycle.
-/
theorem cpc_fresh_default_lookup_for_infinite_map_domain_assumption
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (_hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (_hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (_hm1Can : __smtx_map_canonical m1 = true)
    (_hm2Can : __smtx_map_canonical m2 = true)
    (_hInfinite : __smtx_is_finite_type A = false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical_bool i = true ∧
          __smtx_msm_lookup m1 i = __smtx_msm_get_default m1 ∧
            __smtx_msm_lookup m2 i = __smtx_msm_get_default m2 := by
  sorry

end Smtm
