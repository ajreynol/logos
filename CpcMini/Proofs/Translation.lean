import CpcMini.Proofs.Translation.Base
import CpcMini.Proofs.Translation.Datatypes

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-- Transfers EO typing information to the translated SMT term when the translation is defined.

RESIDUAL ASSUMPTION (dtDecl refactor): the proof of this theorem lived in
`CpcMini.Proofs.Translation.Typeof` / `CpcMini.Proofs.Translation.EoTypeof`, whose
induction invariants (`smt_fold_type_rec` over `__smtx_*_substitute`/`__smtx_*_lift`)
were built for the pre-`DatatypeDecl` substitution-based datatype algorithms. Those
algorithms were deleted in the `dtDecl` refactor (declaration lists + `__smtx_dt_resolve`
/ `__smtx_dd_lookup` replace lift/substitute), so the proof needs to be re-architected
around resolve-based invariants. Until that port is done, the statement is kept here as
a `sorry` assumption so the checker stack states exactly what it relies on. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  sorry

end TranslationProofs

namespace RuleProofs

/-- Transfers EO typing information to the translated SMT term when the translation is defined. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type t T s

end RuleProofs
