module

public import Cpc.Proofs.Translation.Full
import all Cpc.Proofs.Translation.Full

public section

open Eo
open Smtm

/-!
# EO type translation preservation

This file exposes the public wrapper around the full translation
preservation theorem. The internal recursion over EO syntax lives in
`Cpc.Proofs.Translation.EoTypeofCore`; here we only connect that result to
the full SMT typing theorem.
-/

namespace TranslationProofs

/--
Recovers the EO translated type from an SMT typing equality.

The auxiliary non-`None` premise rules out the deliberately partial default
case in `__eo_to_smt_type`.
-/
theorem eo_to_smt_type_typeof_of_smt_type
    (t : Term) {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof t) = T := by
  exact eo_to_smt_type_typeof_of_smt_type_from_full t h hT

end TranslationProofs
