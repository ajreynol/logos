module

public import Cpc.Proofs.Translation.EoTypeofCore
import all Cpc.Proofs.Translation.EoTypeofCore

public section

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
    (ih1Valid :
      __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None ->
      eo_type_valid (__eo_typeof x1))
    (ih2 :
      __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x2) = __eo_to_smt_type (__eo_typeof x2)) :
    (ih2Valid :
      __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None ->
      eo_type_valid (__eo_typeof x2)) ->
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) := by
  intro ih2Valid
  intro hNonNone
  change
    __smtx_typeof
        (__eo_to_smt_array_deq_diff
          (__eo_to_smt x1) (__smtx_typeof (__eo_to_smt x1))
          (__eo_to_smt x2) (__smtx_typeof (__eo_to_smt x2))) ≠
      SmtType.None at hNonNone
  change
    __smtx_typeof
        (__eo_to_smt_array_deq_diff
          (__eo_to_smt x1) (__smtx_typeof (__eo_to_smt x1))
          (__eo_to_smt x2) (__smtx_typeof (__eo_to_smt x2))) =
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))
  cases hx1Smt : __smtx_typeof (__eo_to_smt x1) <;>
    cases hx2Smt : __smtx_typeof (__eo_to_smt x2) <;>
    simp [__eo_to_smt_array_deq_diff, hx1Smt, hx2Smt, smtx_typeof_none] at hNonNone ⊢
  case Map.Map A B A' B' =>
    have hMapNN :
        term_has_non_none_type (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) :=
      hNonNone
    rcases map_diff_args_of_non_none hMapNN with
      ⟨C, D, hx1Ty, hx2Ty, hDiffTy⟩ |
      ⟨C, hx1Ty, _hx2Ty, _hDiffTy⟩
    · have hx1Eo :
          __eo_to_smt_type (__eo_typeof x1) = SmtType.Map C D :=
        eo_to_smt_type_typeof_of_smt_type_from_ih x1 ih1 hx1Ty (by simp)
      have hx2Eo :
          __eo_to_smt_type (__eo_typeof x2) = SmtType.Map C D :=
        eo_to_smt_type_typeof_of_smt_type_from_ih x2 ih2 hx2Ty (by simp)
      rcases eo_to_smt_type_eq_map hx1Eo with
        ⟨U1, V1, hx1EoTy, hU1, hV1⟩
      rcases eo_to_smt_type_eq_map hx2Eo with
        ⟨U2, V2, hx2EoTy, hU2, hV2⟩
      have hx1Valid := ih1Valid (by simp [hx1Ty])
      have hValidParts :
          eo_type_valid_rec [] U1 ∧ eo_type_valid_rec [] V1 := by
        simpa [hx1EoTy, eo_type_valid, eo_type_valid_rec] using hx1Valid
      have hUeq : U1 = U2 :=
        eo_to_smt_type_eq_of_valid_rec hValidParts.1 (hU1.trans hU2.symm)
      have hVeq : V1 = V2 :=
        eo_to_smt_type_eq_of_valid_rec hValidParts.2 (hV1.trans hV2.symm)
      subst U2
      subst V2
      rw [hDiffTy]
      symm
      change
        __eo_to_smt_type
            (__eo_typeof__at_array_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
          C
      rw [hx1EoTy, hx2EoTy]
      have hUNS : U1 ≠ Term.Stuck :=
        eo_type_valid_rec_not_stuck hValidParts.1
      have hVNS : V1 ≠ Term.Stuck :=
        eo_type_valid_rec_not_stuck hValidParts.2
      change __eo_to_smt_type
          (__eo_requires (__eo_and (__eo_eq U1 U1) (__eo_eq V1 V1))
            (Term.Boolean true) U1) = C
      rw [eo_requires_eo_and_eq_self_of_non_stuck U1 V1 U1 hUNS hVNS]
      exact hU1
    · rw [hx1Smt] at hx1Ty
      cases hx1Ty

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_sets_deq_diff`. -/
theorem eo_to_smt_typeof_matches_translation_sets_deq_diff
    (x1 x2 : Term)
    (ih1 :
      __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x1) = __eo_to_smt_type (__eo_typeof x1))
    (ih1Valid :
      __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None ->
      eo_type_valid (__eo_typeof x1))
    (ih2 :
      __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x2) = __eo_to_smt_type (__eo_typeof x2)) :
    (ih2Valid :
      __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None ->
      eo_type_valid (__eo_typeof x2)) ->
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) =
      __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) := by
  intro ih2Valid
  intro hNonNone
  change
    __smtx_typeof
        (__eo_to_smt_sets_deq_diff
          (__eo_to_smt x1) (__smtx_typeof (__eo_to_smt x1))
          (__eo_to_smt x2) (__smtx_typeof (__eo_to_smt x2))) =
      __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))
  change
    __smtx_typeof
        (__eo_to_smt_sets_deq_diff
          (__eo_to_smt x1) (__smtx_typeof (__eo_to_smt x1))
          (__eo_to_smt x2) (__smtx_typeof (__eo_to_smt x2))) ≠
      SmtType.None
    at hNonNone
  cases hx1Smt : __smtx_typeof (__eo_to_smt x1) <;>
    cases hx2Smt : __smtx_typeof (__eo_to_smt x2) <;>
    simp [__eo_to_smt_sets_deq_diff, hx1Smt, hx2Smt, smtx_typeof_none] at hNonNone ⊢
  case Set.Set A A' =>
    have hMapNN :
        term_has_non_none_type (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) :=
      hNonNone
    rcases map_diff_args_of_non_none hMapNN with
      ⟨C, D, hx1Ty, _hx2Ty, _hDiffTy⟩ |
      ⟨C, hx1Ty, hx2Ty, hDiffTy⟩
    · rw [hx1Smt] at hx1Ty
      cases hx1Ty
    · have hx1Eo :
          __eo_to_smt_type (__eo_typeof x1) = SmtType.Set C :=
        eo_to_smt_type_typeof_of_smt_type_from_ih x1 ih1 hx1Ty (by simp)
      have hx2Eo :
          __eo_to_smt_type (__eo_typeof x2) = SmtType.Set C :=
        eo_to_smt_type_typeof_of_smt_type_from_ih x2 ih2 hx2Ty (by simp)
      rcases eo_to_smt_type_eq_set hx1Eo with
        ⟨U1, hx1EoTy, hU1⟩
      rcases eo_to_smt_type_eq_set hx2Eo with
        ⟨U2, hx2EoTy, hU2⟩
      have hx1Valid := ih1Valid (by simp [hx1Ty])
      have hU1Valid : eo_type_valid_rec [] U1 := by
        simpa [hx1EoTy, eo_type_valid, eo_type_valid_rec] using hx1Valid
      have hUeq : U1 = U2 :=
        eo_to_smt_type_eq_of_valid_rec hU1Valid (hU1.trans hU2.symm)
      subst U2
      rw [hDiffTy]
      symm
      change
        __eo_to_smt_type
            (__eo_typeof__at_sets_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
          C
      rw [hx1EoTy, hx2EoTy]
      have hUNS : U1 ≠ Term.Stuck :=
        eo_type_valid_rec_not_stuck hU1Valid
      change __eo_to_smt_type
          (__eo_requires (__eo_eq U1 U1) (Term.Boolean true) U1) = C
      rw [eo_requires_eo_eq_self_of_non_stuck U1 U1 hUNS]
      exact hU1

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
