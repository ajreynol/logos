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
  change
    __smtx_typeof
        (native_ite
          (native_Teq
            (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
            SmtType.None)
          SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) ≠
      SmtType.None at hNonNone
  change
    __smtx_typeof
        (native_ite
          (native_Teq
            (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
            SmtType.None)
          SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))
  cases hGuard :
      native_Teq
        (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
        SmtType.None <;>
    simp [native_ite, hGuard] at hNonNone ⊢
  · have hMapNN :
        term_has_non_none_type (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) :=
      hNonNone
    rcases map_diff_args_of_non_none hMapNN with
      ⟨A, B, hx1Ty, hx2Ty, hDiffTy⟩ |
      ⟨A, hx1Ty, hx2Ty, hDiffTy⟩
    · have hx1Eo :
          __eo_to_smt_type (__eo_typeof x1) = SmtType.Map A B :=
        eo_to_smt_type_typeof_of_smt_type_from_ih x1 ih1 hx1Ty (by simp)
      have hx2Eo :
          __eo_to_smt_type (__eo_typeof x2) = SmtType.Map A B :=
        eo_to_smt_type_typeof_of_smt_type_from_ih x2 ih2 hx2Ty (by simp)
      rcases eo_to_smt_type_eq_map hx1Eo with
        ⟨U1, V1, hx1EoTy, hU1, hV1⟩
      rcases eo_to_smt_type_eq_map hx2Eo with
        ⟨U2, V2, hx2EoTy, hU2, hV2⟩
      rw [hDiffTy]
      symm
      change
        __eo_to_smt_type
            (__eo_typeof__at_array_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
          A
      rw [hx1EoTy, hx2EoTy]
      cases hReq :
          native_teq
            (__eo_and (__eo_eq U1 U2) (__eo_eq V1 V2))
            (Term.Boolean true)
      · have hNone :
            __eo_to_smt_type
                (__eo_typeof (Term._at_array_deq_diff x1 x2)) =
              SmtType.None := by
          change
            __eo_to_smt_type
                (__eo_typeof__at_array_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
              SmtType.None
          rw [hx1EoTy, hx2EoTy]
          simp [__eo_typeof__at_array_deq_diff, __eo_requires, __eo_to_smt_type,
            native_ite, hReq]
        rw [hNone] at hGuard
        simp [native_Teq] at hGuard
      · have hNotStuck :
            native_not
                (native_teq
                  (__eo_and (__eo_eq U1 U2) (__eo_eq V1 V2))
                  Term.Stuck) = true := by
          cases hCond : __eo_and (__eo_eq U1 U2) (__eo_eq V1 V2) <;>
            simp [native_teq, native_not, hCond] at hReq ⊢
        simp [__eo_typeof__at_array_deq_diff, __eo_requires, native_ite,
          hReq, hNotStuck, hU1]
    · have hx1Eo :
          __eo_to_smt_type (__eo_typeof x1) = SmtType.Set A :=
        eo_to_smt_type_typeof_of_smt_type_from_ih x1 ih1 hx1Ty (by simp)
      rcases eo_to_smt_type_eq_set hx1Eo with
        ⟨U, hx1EoTy, _hU⟩
      have hNone :
          __eo_to_smt_type
              (__eo_typeof (Term._at_array_deq_diff x1 x2)) =
            SmtType.None := by
        change
          __eo_to_smt_type
              (__eo_typeof__at_array_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
            SmtType.None
        rw [hx1EoTy]
        simp [__eo_typeof__at_array_deq_diff, __eo_to_smt_type]
      rw [hNone] at hGuard
      simp [native_Teq] at hGuard

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
