import Cpc.SmtModel

open SmtEval
open Smtm

namespace Smtm

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
Semantic witness property for `map_diff` on canonical typed maps.

The executable definition of `native_eval_map_diff_msm` chooses an index whose
lookups are syntactically different when such an index exists.  Proving that
canonical map disequality always supplies such a typed canonical index requires
the remaining canonical finite-map extensionality/fresh-index argument; we keep
that open obligation isolated here, as with datatype defaults above.
-/
theorem cpc_map_diff_selects_model_eval_eq_false_assumption
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (_hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (_hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (_hm1Can : __smtx_map_canonical m1 = true)
    (_hm2Can : __smtx_map_canonical m2 = true)
    (_hNe : __smtx_model_eval_eq (SmtValue.Map m1) (SmtValue.Map m2) =
      SmtValue.Boolean false) :
    __smtx_model_eval_eq
        (__smtx_msm_lookup m1 (native_eval_map_diff_msm m1 m2))
        (__smtx_msm_lookup m2 (native_eval_map_diff_msm m1 m2)) =
      SmtValue.Boolean false := by
  sorry

end Smtm
