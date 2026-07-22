module

public import CpcMini.Proofs.Translation.Datatypes
import all CpcMini.Spec
import all CpcMini.Logos

public section

open Eo
open SmtEval
open Smtm

namespace RuleProofs

/--
Transfers EO typing information to a defined, non-`None` SMT translation.

The former proof expands datatype bodies with the deleted lift/substitution
operations. Reconstructing it for declaration-based datatypes requires
commutation lemmas for declaration lookup and `__smtx_dt_resolve`; keep that
remaining obligation isolated while the declaration translation compiles.
-/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  sorry

end RuleProofs
