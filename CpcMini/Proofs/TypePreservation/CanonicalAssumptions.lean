import CpcMini.SmtModel

open SmtEval
open Smtm

namespace Smtm

/--
The remaining datatype-default canonicity assumption.

This isolates the open proof obligation needed to build canonical inhabitants
for well-formed datatype types.
-/
axiom cpcmini_datatype_type_default_typed_canonical_assumption
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d))

end Smtm
