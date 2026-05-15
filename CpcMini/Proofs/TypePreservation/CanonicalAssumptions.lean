import CpcMini.SmtModel

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
  simpa [native_inhabited_type, __smtx_value_canonical, native_and] using _hInh

end Smtm
