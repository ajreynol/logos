import Cpc.Proofs.Translation.EoTypeof
import Cpc.Proofs.TypePreservation

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_purify`. -/
theorem eo_to_smt_typeof_matches_translation_purify
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term._at_purify x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_purify x)) =
      __eo_to_smt_type (__eo_typeof (Term._at_purify x)) := by
  sorry

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
        SmtTerm.Apply (SmtTerm.choice "_at_x" _v0)
          (SmtTerm.Apply SmtTerm.not
            (SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.eq
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt x1)) _v2))
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt x2)) _v2))) := by
    rw [__eo_to_smt.eq_def]
  have hApplyNN :
      term_has_non_none_type
        (let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))
         let _v2 := SmtTerm.Var "_at_x" _v0
         SmtTerm.Apply (SmtTerm.choice "_at_x" _v0)
           (SmtTerm.Apply SmtTerm.not
             (SmtTerm.Apply
               (SmtTerm.Apply SmtTerm.eq
                 (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt x1)) _v2))
               (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt x2)) _v2)))) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rw [hTranslate]
  simpa using
    choice_term_typeof_of_non_none
      (s := "_at_x")
      (T := __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
      (body :=
        SmtTerm.Apply SmtTerm.not
          (SmtTerm.Apply
            (SmtTerm.Apply SmtTerm.eq
              (SmtTerm.Apply
                (SmtTerm.Apply SmtTerm.select (__eo_to_smt x1))
                (SmtTerm.Var "_at_x"
                  (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))))))
            (SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.select (__eo_to_smt x2))
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
        let _v2 := SmtTerm.Apply SmtTerm.set_member (SmtTerm.Var "_at_x" _v0)
        SmtTerm.Apply (SmtTerm.choice "_at_x" _v0)
          (SmtTerm.Apply SmtTerm.not
            (SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply _v2 (__eo_to_smt x1)))
              (SmtTerm.Apply _v2 (__eo_to_smt x2)))) := by
    rw [__eo_to_smt.eq_def]
  have hApplyNN :
      term_has_non_none_type
        (let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))
         let _v2 := SmtTerm.Apply SmtTerm.set_member (SmtTerm.Var "_at_x" _v0)
         SmtTerm.Apply (SmtTerm.choice "_at_x" _v0)
           (SmtTerm.Apply SmtTerm.not
             (SmtTerm.Apply
               (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply _v2 (__eo_to_smt x1)))
               (SmtTerm.Apply _v2 (__eo_to_smt x2))))) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rw [hTranslate]
  simpa using
    choice_term_typeof_of_non_none
      (s := "_at_x")
      (T := __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))
      (body :=
        SmtTerm.Apply SmtTerm.not
          (SmtTerm.Apply
            (SmtTerm.Apply SmtTerm.eq
              (SmtTerm.Apply
                (SmtTerm.Apply SmtTerm.set_member
                  (SmtTerm.Var "_at_x"
                    (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))))
                (__eo_to_smt x1)))
            (SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.set_member
                (SmtTerm.Var "_at_x"
                  (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))))
              (__eo_to_smt x2))))
      hApplyNN

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_quantifiers_skolemize`. -/
theorem eo_to_smt_typeof_matches_translation_quantifiers_skolemize
    (x1 x2 : Term) :
    __smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_quantifiers_skolemize x1 x2)) := by
  sorry

end TranslationProofs
