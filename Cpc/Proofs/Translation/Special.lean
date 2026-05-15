import Cpc.Proofs.Translation.EoTypeofCore
import Cpc.Proofs.TypePreservationFull

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_array_deq_diff`. -/
theorem eo_to_smt_typeof_matches_translation_array_deq_diff
    (x1 x2 : Term)
    (ih1 :
      __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x1) = __eo_to_smt_type (__eo_typeof x1))
    (ih2 :
      __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x2) = __eo_to_smt_type (__eo_typeof x2)) :
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) := by
  intro hNonNone
  exfalso
  apply hNonNone
  change
    __smtx_typeof
        (native_ite
          (native_Teq (__eo_to_smt_type (Term._at_array_deq_diff x1 x2)) SmtType.None)
          SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
      SmtType.None
  simp [__eo_to_smt_type, native_ite, native_Teq]

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_sets_deq_diff`. -/
theorem eo_to_smt_typeof_matches_translation_sets_deq_diff
    (x1 x2 : Term)
    (ih1 :
      __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x1) = __eo_to_smt_type (__eo_typeof x1))
    (ih2 :
      __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x2) = __eo_to_smt_type (__eo_typeof x2)) :
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) := by
  intro hNonNone
  exfalso
  apply hNonNone
  change
    __smtx_typeof
        (native_ite
          (native_Teq (__eo_to_smt_type (Term._at_sets_deq_diff x1 x2)) SmtType.None)
          SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
      SmtType.None
  simp [__eo_to_smt_type, native_ite, native_Teq]

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_purify`. -/
theorem eo_to_smt_typeof_matches_translation_purify
    (x : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term._at_purify x)) =
      __eo_to_smt_type (__eo_typeof (Term._at_purify x)) := by
  change __smtx_typeof (SmtTerm._at_purify (__eo_to_smt x)) =
    __eo_to_smt_type (__eo_typeof (Term._at_purify x))
  simp [__smtx_typeof]
  rw [hx]
  exact (eo_to_smt_type_typeof_purify x).symm

end TranslationProofs
