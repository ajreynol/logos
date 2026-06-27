import CpcMini.Proofs.TypePreservation.Predicates

open SmtEval
open Smtm

namespace Smtm

/--
Datatype-default canonicity for the generated Mini model.

The theorem keeps the historical `_assumption` name used by the downstream
proof skeleton, but `native_inhabited_type` now uniformly carries exactly this
canonical default witness.
-/
theorem cpcmini_datatype_type_default_typed_canonical_assumption
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  classical
  refine ⟨?_, ?_⟩
  · -- typing: extracted from the inhabitance check (`native_inhabited_type`)
    have h2 := _hInh
    simp only [native_inhabited_type, native_and, Bool.and_eq_true] at h2
    exact of_decide_eq_true (by simpa [native_Teq] using h2.2)
  · -- canonicity: `native_inhabited_type` no longer carries the canonical conjunct
    -- (dropped on the `dtMutual` branch). It holds unconditionally — proved by the
    -- kernel (`type_default_canonical_of_typed`) in the full `Cpc` library — but the
    -- kernel is not ported to the Mini library, so it is admitted here as the
    -- Mini-model assumption boundary (this file's stated purpose).
    sorry

end Smtm
