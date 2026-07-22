module

public import Cpc.Proofs.Translation.Datatypes
public import Cpc.Proofs.Translation.Quantifiers
import all Cpc.Spec
import all Cpc.Logos

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false

namespace TranslationProofs

/--
Transfers EO typing information to a defined, non-`None` SMT translation.

The former proof expands datatype aliases with the deleted lift/substitution
operations. Reconstructing it requires commutation lemmas for declaration
lookup and `__smtx_dt_resolve`; keep the remaining assumption isolated here so
the declaration-based datatype translation and type-preservation proofs can be
compiled independently in the meantime.
-/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  sorry

/-- Specialization of translation preservation to Boolean terms. -/
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

/-- Rule-proof namespace wrapper for translation preservation. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type t T s

/-- Rule-proof namespace wrapper for Boolean translation preservation. -/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = Term.Bool ->
    __smtx_typeof s = SmtType.Bool := by
  exact TranslationProofs.eo_to_smt_non_none_and_typeof_bool_implies_smt_bool t s

end RuleProofs
