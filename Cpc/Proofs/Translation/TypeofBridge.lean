module

public import Cpc.Proofs.Translation.EoTypeof
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

This is the equality-oriented form of the full translation theorem: recover
the translated EO type from the non-`None` SMT type, then rewrite the supplied
EO typing equality.
-/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  intro hs hNonNone hTy
  subst s
  have hRecovered :
      __eo_to_smt_type (__eo_typeof t) = __smtx_typeof (__eo_to_smt t) :=
    eo_to_smt_type_typeof_of_smt_type t rfl hNonNone
  exact hRecovered.symm.trans (congrArg __eo_to_smt_type hTy)

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
