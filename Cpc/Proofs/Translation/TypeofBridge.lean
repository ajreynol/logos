import Cpc.Spec
import Cpc.Logos

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false

/-!
Bridge exporting the eo→smt typeof-correspondence facts consumed by the rule/checker
stack (`Cpc.Proofs.Common` and downstream), decoupled from the full translation proof
development.

RESIDUAL ASSUMPTION (dtDecl refactor): the proof of
`eo_to_smt_well_typed_and_typeof_implies_smt_type` lives in
`Cpc.Proofs.Translation.Full` (via `EoTypeofCore`/`Apply`/`Inversions`/`SmtFreeRefs`),
whose induction invariants (`imgTy` substitution images, `hasFree*`/`noDt*`/`noStray*`
scoping predicates, lift/substitute no-op lemmas) were built for the pre-`DatatypeDecl`
substitution-based datatype algorithms. Those algorithms were deleted in the `dtDecl`
refactor (declaration lists + `__smtx_dt_resolve` / `__smtx_dd_lookup` replace
lift/substitute), so that stack needs to be re-architected around resolve-based
invariants. Until that port is done, the statement is kept here as a `sorry`
assumption so the checker stack states exactly what it relies on.
-/

namespace TranslationProofs

/-- Transfers EO typing information to the translated SMT term when the translation is defined. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  sorry

/-- Transfers EO Boolean typing to the translated SMT term under a defined translation. -/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = Term.Bool ->
    __smtx_typeof s = SmtType.Bool := by
  intro hs hNonNone hTy
  exact eo_to_smt_well_typed_and_typeof_implies_smt_type
    t Term.Bool s hs hNonNone hTy

end TranslationProofs

namespace RuleProofs

/-- Transfers EO typing information to the translated SMT term when the translation is defined. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = T ->
  __smtx_typeof s = __eo_to_smt_type T := by
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    t T s

/-- Shows that `eo_to_smt_non_none_and_typeof_bool` implies `smt_bool`. -/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = Term.Bool ->
  __smtx_typeof s = SmtType.Bool := by
  exact TranslationProofs.eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t s

end RuleProofs
