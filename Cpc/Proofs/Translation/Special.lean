import Cpc.Proofs.Translation.EoTypeof

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

theorem eo_to_smt_typeof_matches_translation_purify
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term._at_purify x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_purify x)) =
      __eo_to_smt_type (__eo_typeof (Term._at_purify x)) := by
  sorry

theorem eo_to_smt_typeof_matches_translation_array_deq_diff
    (x1 x2 : Term) :
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) := by
  sorry

theorem eo_to_smt_typeof_matches_translation_sets_deq_diff
    (x1 x2 : Term) :
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) := by
  sorry

theorem eo_to_smt_typeof_matches_translation_quantifiers_skolemize
    (x1 x2 : Term) :
    __smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_quantifiers_skolemize x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_quantifiers_skolemize x1 x2)) := by
  sorry

end TranslationProofs
