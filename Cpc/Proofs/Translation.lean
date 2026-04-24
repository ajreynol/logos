import Cpc.Spec
import Cpc.Proofs.Translation.Base

open Eo
open SmtEval
open Smtm

/-!
Lightweight public surface for the translation facts used by the rule proofs.

To reconnect the final translation proofs:
1. Uncomment `import Cpc.Proofs.Translation.Full`.
2. Comment out or delete the stub declarations below.

The full module exposes the same theorem names in the same namespaces, so the
rest of the proof development does not need to change.
-/

-- import Cpc.Proofs.Translation.Full

namespace TranslationProofs

@[simp] theorem smtx_typeof_none :
    __smtx_typeof SmtTerm.None = SmtType.None := by
  simp [__smtx_typeof.eq_def]

axiom eo_to_smt_typeof_matches_translation
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t)

axiom eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T

axiom eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = Term.Bool ->
    __smtx_typeof s = SmtType.Bool

end TranslationProofs

namespace RuleProofs

theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    t T s

theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = Term.Bool ->
    __smtx_typeof s = SmtType.Bool := by
  exact TranslationProofs.eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t s

end RuleProofs
