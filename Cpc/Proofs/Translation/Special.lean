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
  have hTypeNN :
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) ≠
        SmtType.None := by
    intro hNone
    apply hNonNone
    change
      __smtx_typeof
          (native_ite
            (native_Teq
              (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
              SmtType.None)
            SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
        SmtType.None
    simp [native_ite, native_Teq, hNone]
  have hTranslate :
      __eo_to_smt (Term._at_array_deq_diff x1 x2) =
        SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2) := by
    change
      native_ite
          (native_Teq
            (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
            SmtType.None)
          SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) =
        SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)
    cases hEq :
        native_Teq
          (__eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)))
          SmtType.None with
    | false => rfl
    | true =>
        have hNone :
            __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) =
              SmtType.None := by
          simpa [native_Teq] using hEq
        exact False.elim (hTypeNN hNone)
  have hMapNN : term_has_non_none_type
      (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases map_diff_args_of_non_none hMapNN with hMap | hFun | hSet
  · rcases hMap with ⟨A, B, h1, h2, hSmt⟩
    have h1NN : __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None := by
      rw [h1]
      simp
    have h2NN : __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None := by
      rw [h2]
      simp
    have h1Trans :
        __eo_to_smt_type (__eo_typeof x1) = SmtType.Map A B :=
      (ih1 h1NN).symm.trans h1
    have h2Trans :
        __eo_to_smt_type (__eo_typeof x2) = SmtType.Map A B :=
      (ih2 h2NN).symm.trans h2
    rcases eo_to_smt_type_eq_map h1Trans with ⟨U1, V1, hx1, hU1, hV1⟩
    rcases eo_to_smt_type_eq_map h2Trans with ⟨U2, V2, hx2, hU2, hV2⟩
    have hComps := smt_map_components_wf_rec_of_non_none_type
      (__eo_to_smt x1) A B h1
    have hAWF : smtx_type_field_wf_rec A native_reflist_nil :=
      smtx_type_field_wf_rec_of_type_wf_rec hComps.1
    have hBWF : smtx_type_field_wf_rec B native_reflist_nil :=
      smtx_type_field_wf_rec_of_type_wf_rec hComps.2
    have hU : U2 = U1 :=
      eo_to_smt_type_injective_of_field_wf_rec hU2 hU1 hAWF
    have hV : V2 = V1 :=
      eo_to_smt_type_injective_of_field_wf_rec hV2 hV1 hBWF
    have hANN : A ≠ SmtType.None := by
      cases A <;> simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hAWF ⊢
    have hBNN : B ≠ SmtType.None := by
      cases B <;> simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hBWF ⊢
    have hUNS : U1 ≠ Term.Stuck :=
      eo_term_ne_stuck_of_smt_type_non_none U1 (by rw [hU1]; exact hANN)
    have hVNS : V1 ≠ Term.Stuck :=
      eo_term_ne_stuck_of_smt_type_non_none V1 (by rw [hV1]; exact hBNN)
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) = A := by
      change
        __eo_to_smt_type
            (__eo_typeof__at_array_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
          A
      rw [hx1, hx2, hU, hV]
      simpa [__eo_typeof__at_array_deq_diff, hU1] using
        congrArg __eo_to_smt_type
          (eo_requires_eo_and_eq_self_of_non_stuck U1 V1 U1 hUNS hVNS)
    rw [hTranslate, hSmt]
    exact hEo.symm
  · rcases hFun with ⟨A, B, h1, _h2, _hSmt⟩
    have h1NN : __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None := by
      rw [h1]
      simp
    have h1Trans :
        __eo_to_smt_type (__eo_typeof x1) = SmtType.FunType A B :=
      (ih1 h1NN).symm.trans h1
    rcases eo_to_smt_type_eq_fun h1Trans with ⟨U, V, hx1, _hU, _hV⟩
    exfalso
    apply hTypeNN
    change
      __eo_to_smt_type
          (__eo_typeof__at_array_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
        SmtType.None
    rw [hx1]
    simp [__eo_typeof__at_array_deq_diff, __eo_to_smt_type]
  · rcases hSet with ⟨A, h1, _h2, _hSmt⟩
    have h1NN : __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None := by
      rw [h1]
      simp
    have h1Trans :
        __eo_to_smt_type (__eo_typeof x1) = SmtType.Set A :=
      (ih1 h1NN).symm.trans h1
    rcases eo_to_smt_type_eq_set h1Trans with ⟨U, hx1, _hU⟩
    exfalso
    apply hTypeNN
    change
      __eo_to_smt_type
          (__eo_typeof__at_array_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
        SmtType.None
    rw [hx1]
    simp [__eo_typeof__at_array_deq_diff, __eo_to_smt_type]

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
  have hTypeNN :
      __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) ≠
        SmtType.None := by
    intro hNone
    apply hNonNone
    change
      __smtx_typeof
          (native_ite
            (native_Teq
              (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))
              SmtType.None)
            SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2))) =
        SmtType.None
    simp [native_ite, native_Teq, hNone]
  have hTranslate :
      __eo_to_smt (Term._at_sets_deq_diff x1 x2) =
        SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2) := by
    change
      native_ite
          (native_Teq
            (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))
            SmtType.None)
          SmtTerm.None (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) =
        SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)
    cases hEq :
        native_Teq
          (__eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)))
          SmtType.None with
    | false => rfl
    | true =>
        have hNone :
            __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) =
              SmtType.None := by
          simpa [native_Teq] using hEq
        exact False.elim (hTypeNN hNone)
  have hMapNN : term_has_non_none_type
      (SmtTerm.map_diff (__eo_to_smt x1) (__eo_to_smt x2)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases map_diff_args_of_non_none hMapNN with hMap | hFun | hSet
  · rcases hMap with ⟨A, B, h1, _h2, _hSmt⟩
    have h1NN : __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None := by
      rw [h1]
      simp
    have h1Trans :
        __eo_to_smt_type (__eo_typeof x1) = SmtType.Map A B :=
      (ih1 h1NN).symm.trans h1
    rcases eo_to_smt_type_eq_map h1Trans with ⟨U, V, hx1, _hU, _hV⟩
    exfalso
    apply hTypeNN
    change
      __eo_to_smt_type
          (__eo_typeof__at_sets_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
        SmtType.None
    rw [hx1]
    simp [__eo_typeof__at_sets_deq_diff, __eo_to_smt_type]
  · rcases hFun with ⟨A, B, h1, _h2, _hSmt⟩
    have h1NN : __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None := by
      rw [h1]
      simp
    have h1Trans :
        __eo_to_smt_type (__eo_typeof x1) = SmtType.FunType A B :=
      (ih1 h1NN).symm.trans h1
    rcases eo_to_smt_type_eq_fun h1Trans with ⟨U, V, hx1, _hU, _hV⟩
    exfalso
    apply hTypeNN
    change
      __eo_to_smt_type
          (__eo_typeof__at_sets_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
        SmtType.None
    rw [hx1]
    simp [__eo_typeof__at_sets_deq_diff, __eo_to_smt_type]
  · rcases hSet with ⟨A, h1, h2, hSmt⟩
    have h1NN : __smtx_typeof (__eo_to_smt x1) ≠ SmtType.None := by
      rw [h1]
      simp
    have h2NN : __smtx_typeof (__eo_to_smt x2) ≠ SmtType.None := by
      rw [h2]
      simp
    have h1Trans :
        __eo_to_smt_type (__eo_typeof x1) = SmtType.Set A :=
      (ih1 h1NN).symm.trans h1
    have h2Trans :
        __eo_to_smt_type (__eo_typeof x2) = SmtType.Set A :=
      (ih2 h2NN).symm.trans h2
    rcases eo_to_smt_type_eq_set h1Trans with ⟨U1, hx1, hU1⟩
    rcases eo_to_smt_type_eq_set h2Trans with ⟨U2, hx2, hU2⟩
    have hAWF : smtx_type_field_wf_rec A native_reflist_nil :=
      smtx_type_field_wf_rec_of_type_wf_rec
        (smt_set_component_wf_rec_of_non_none_type (__eo_to_smt x1) A h1)
    have hU : U2 = U1 :=
      eo_to_smt_type_injective_of_field_wf_rec hU2 hU1 hAWF
    have hANN : A ≠ SmtType.None := by
      cases A <;> simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hAWF ⊢
    have hUNS : U1 ≠ Term.Stuck :=
      eo_term_ne_stuck_of_smt_type_non_none U1 (by rw [hU1]; exact hANN)
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) = A := by
      change
        __eo_to_smt_type
            (__eo_typeof__at_sets_deq_diff (__eo_typeof x1) (__eo_typeof x2)) =
          A
      rw [hx1, hx2, hU]
      simpa [__eo_typeof__at_sets_deq_diff, hU1] using
        congrArg __eo_to_smt_type
          (eo_requires_eo_eq_self_of_non_stuck U1 U1 hUNS)
    rw [hTranslate, hSmt]
    exact hEo.symm

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
