import Cpc.Proofs.TypePreservation.CanonicalAssumptions

/-!
Tuple-specific default witness used when translation peels one field from a
generated `@Tuple` datatype.

This isolates the tuple-tail residual assumption from the cardinality and
array-extensionality support.
-/

open SmtEval
open Smtm

namespace Smtm

theorem cpc_tuple_tail_default_typed_canonical_assumption
    (T : SmtType)
    (c : SmtDatatypeCons)
    (_hWf :
      __smtx_type_wf
          (SmtType.Datatype "@Tuple"
            (SmtDatatype.sum (SmtDatatypeCons.cons T c) SmtDatatype.null)) =
        true) :
    __smtx_typeof_value
        (__smtx_datatype_cons_default "@Tuple"
          (SmtDatatype.sum c SmtDatatype.null)
          (SmtValue.DtCons "@Tuple" (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero)
          c) =
      SmtType.Datatype "@Tuple" (SmtDatatype.sum c SmtDatatype.null) ∧
      __smtx_value_canonical_bool
          (__smtx_datatype_cons_default "@Tuple"
            (SmtDatatype.sum c SmtDatatype.null)
            (SmtValue.DtCons "@Tuple" (SmtDatatype.sum c SmtDatatype.null)
              native_nat_zero)
            c) =
        true := by
  sorry

end Smtm
