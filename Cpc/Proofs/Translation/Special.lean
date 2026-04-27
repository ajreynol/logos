import Cpc.Proofs.Translation.EoTypeof
import Cpc.Proofs.TypePreservationFull

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_purify`. -/
theorem eo_to_smt_typeof_matches_translation_purify
    (x : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term._at_purify x)) =
      __eo_to_smt_type (__eo_typeof (Term._at_purify x)) := by
  rw [__eo_to_smt.eq_def, hx]
  exact (eo_to_smt_type_typeof_purify x).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_array_deq_diff`. -/
theorem eo_to_smt_typeof_matches_translation_array_deq_diff
    (x1 x2 : Term) :
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) := by
  intro hNonNone
  have hTranslate :
      __eo_to_smt (Term._at_array_deq_diff x1 x2) =
        let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))
        let _v2 := SmtTerm.Var "_at_x" _v0
        SmtTerm.choice_nth "_at_x" _v0
          (SmtTerm.not
            (SmtTerm.eq
              (SmtTerm.select (__eo_to_smt x1) _v2)
              (SmtTerm.select (__eo_to_smt x2) _v2))) 0 := by
    rw [__eo_to_smt.eq_def]
  have hApplyNN :
      term_has_non_none_type
        (let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))
         let _v2 := SmtTerm.Var "_at_x" _v0
         SmtTerm.choice_nth "_at_x" _v0
           (SmtTerm.not
             (SmtTerm.eq
               (SmtTerm.select (__eo_to_smt x1) _v2)
               (SmtTerm.select (__eo_to_smt x2) _v2))) 0) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rw [hTranslate]
  simpa using
    choice_term_typeof_of_non_none
      (s := "_at_x")
      (T := __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
      (body :=
        SmtTerm.not
          (SmtTerm.eq
            (SmtTerm.select
              (__eo_to_smt x1)
              (SmtTerm.Var "_at_x"
                (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))))
            (SmtTerm.select
              (__eo_to_smt x2)
              (SmtTerm.Var "_at_x"
                (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))))))
      hApplyNN

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_sets_deq_diff`. -/
theorem eo_to_smt_typeof_matches_translation_sets_deq_diff
    (x1 x2 : Term) :
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) := by
  intro hNonNone
  have hTranslate :
      __eo_to_smt (Term._at_sets_deq_diff x1 x2) =
        let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))
        let _v2 := SmtTerm.Var "_at_x" _v0
        SmtTerm.choice_nth "_at_x" _v0
          (SmtTerm.not
            (SmtTerm.eq
              (SmtTerm.set_member _v2 (__eo_to_smt x1))
              (SmtTerm.set_member _v2 (__eo_to_smt x2)))) 0 := by
    rw [__eo_to_smt.eq_def]
  have hApplyNN :
      term_has_non_none_type
        (let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))
         let _v2 := SmtTerm.Var "_at_x" _v0
         SmtTerm.choice_nth "_at_x" _v0
           (SmtTerm.not
             (SmtTerm.eq
               (SmtTerm.set_member _v2 (__eo_to_smt x1))
               (SmtTerm.set_member _v2 (__eo_to_smt x2)))) 0) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rw [hTranslate]
  simpa using
    choice_term_typeof_of_non_none
      (s := "_at_x")
      (T := __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))
      (body :=
        SmtTerm.not
          (SmtTerm.eq
            (SmtTerm.set_member
              (SmtTerm.Var "_at_x"
                (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))))
              (__eo_to_smt x1))
            (SmtTerm.set_member
              (SmtTerm.Var "_at_x"
                (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))))
              (__eo_to_smt x2))))
      hApplyNN

end TranslationProofs
