import CpcMicro.Proofs.Translation.Datatypes
import CpcMicro.Proofs.TypePreservation.CoreArith
import CpcMicro.Proofs.TypePreservation.Datatypes

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Derives `smtx_typeof_apply_generic` from `head_not_special`. -/
private theorem smtx_typeof_apply_generic_of_head_not_special
    (f x : SmtTerm)
    (hEq : ∀ u, f ≠ SmtTerm.Apply SmtTerm.eq u)
    (hIte2 : ∀ c u, f ≠ SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) u)
    (hExists : ∀ s T, f ≠ SmtTerm.exists s T)
    (hForall : ∀ s T, f ≠ SmtTerm.forall s T)
    (hChoice : ∀ s T, f ≠ SmtTerm.choice s T) :
    generic_apply_type f x := by
  unfold generic_apply_type
  cases f <;> try rfl
  case «exists» s T =>
      exact False.elim (hExists s T rfl)
  case «forall» s T =>
      exact False.elim (hForall s T rfl)
  case choice s T =>
      exact False.elim (hChoice s T rfl)
  case Apply f y =>
      cases f <;> try rfl
      case eq =>
          exact False.elim (hEq y rfl)
      case Apply g c =>
          cases g <;> try rfl
          case ite =>
              exact False.elim (hIte2 c y rfl)

/-- Shows that generic EO application translation satisfies `generic_apply_type`. -/
theorem eo_to_smt_apply_generic_type
    (f x : Term) :
    generic_apply_type (__eo_to_smt f) (__eo_to_smt x) := by
  apply smtx_typeof_apply_generic_of_head_not_special
  · intro u
    exact eo_to_smt_ne_eq_partial f u
  · intro c u
    exact eo_to_smt_ne_ite_partial2 f c u
  · intro s T
    exact eo_to_smt_ne_exists f s T
  · intro s T
    exact eo_to_smt_ne_forall f s T
  · intro s T
    exact eo_to_smt_ne_choice f s T

/-- Derives `smtx_typeof_translation_not` from `non_none`. -/
theorem smtx_typeof_translation_not_of_non_none
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
    cases h : __smtx_typeof (__eo_to_smt x) <;>
      simp [__smtx_typeof, native_ite, native_Teq, h] at hNonNone
    simp
  simp [__smtx_typeof, native_ite, native_Teq, hArg]

/-- Derives `smtx_typeof_translation_or` from `non_none`. -/
theorem smtx_typeof_translation_or_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl hApplyNN
  simp [__smtx_typeof, native_ite, native_Teq, hArgs.1, hArgs.2]

/-- Derives `smtx_typeof_translation_and` from `non_none`. -/
theorem smtx_typeof_translation_and_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl hApplyNN
  simp [__smtx_typeof, native_ite, native_Teq, hArgs.1, hArgs.2]

/-- Derives `smtx_typeof_translation_imp` from `non_none`. -/
theorem smtx_typeof_translation_imp_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl hApplyNN
  simp [__smtx_typeof, native_ite, native_Teq, hArgs.1, hArgs.2]

/-- Derives `smtx_typeof_translation_eq` from `non_none`. -/
theorem smtx_typeof_translation_eq_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.eq x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.eq x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  simpa using
    eq_term_typeof_of_non_none (t1 := __eo_to_smt x) (t2 := __eo_to_smt y) hApplyNN

/-- Establishes an equality relating `smtx_typeof` and `non_none`. -/
theorem smtx_typeof_eq_non_none
    {T U : SmtType}
    (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    T = U ∧ T ≠ SmtType.None := by
  by_cases hNone : T = SmtType.None
  · subst hNone
    exfalso
    exact h (by simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq])
  · by_cases hEq : T = U
    · exact ⟨hEq, hNone⟩
    · exfalso
      exact h (by
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq, hNone, hEq])

/-- Transfers generic application typing from EO terms to their SMT translations. -/
theorem eo_to_smt_typeof_matches_translation_apply_generic
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hGeneric :
      generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply f x) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hTypeof :
      __eo_typeof (Term.Apply f x) = __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f)) (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTranslate] using hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, _hB⟩
  have hFNN : __smtx_typeof (__eo_to_smt f) ≠ SmtType.None := by
    cases hF with
    | inl hMap =>
        rw [hMap]
        simp
    | inr hFun =>
        rw [hFun]
        simp
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hX]
    exact hA
  have hXEo : __eo_to_smt_type (__eo_typeof x) = A := by
    simpa [ihX hXNN] using hX
  cases hF with
  | inl hMap =>
      have hFEo : __eo_to_smt_type (__eo_typeof f) = SmtType.Map A B := by
        simpa [ihF hFNN] using hMap
      exact False.elim ((eo_to_smt_type_ne_map (T := __eo_typeof f) (A := A) (B := B)) hFEo)
  | inr hFun =>
      have hFEo : __eo_to_smt_type (__eo_typeof f) = SmtType.FunType A B := by
        simpa [ihF hFNN] using hFun
      rcases eo_to_smt_type_eq_fun_iff.mp hFEo with
        ⟨T1, T2, hFunTy, hT1, hT2, hT1NN, _hT2NN⟩
      have hArgTy : __eo_typeof x = T1 := by
        apply eo_to_smt_type_eq_of_non_none
        · rw [hXEo, ← hT1]
        · rwa [hXEo, ← hT1]
      have hT1NotStuck : T1 ≠ Term.Stuck := by
        intro hStuck
        apply hT1NN
        simp [hStuck, __eo_to_smt_type]
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply f x)) = B := by
        rw [hTranslate, hGeneric, hFun, hX]
        simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
      have hTypeApply :
          __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType T1) T2) T1 = T2 := by
        rw [__eo_typeof_apply.eq_def]
        by_cases hStuck : T1 = Term.Stuck
        · exact False.elim (hT1NotStuck hStuck)
        · simp [hStuck, __eo_requires.eq_def, native_teq, native_ite, native_not]
      rw [hSmt, hTypeof, hFunTy, hArgTy, hTypeApply, hT2]

/-- Handles the application case of `eo_to_smt_typeof_matches_translation`. -/
theorem eo_to_smt_typeof_matches_translation_apply
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hTranslate :
      __eo_to_smt (Term.Apply f x) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hTypeof :
      __eo_typeof (Term.Apply f x) = __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  exact eo_to_smt_typeof_matches_translation_apply_generic f x ihF ihX
    (eo_to_smt_apply_generic_type f x) hTranslate hTypeof hNonNone

end TranslationProofs
