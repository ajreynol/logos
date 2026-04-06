import CpcMicro.Proofs.Translation.Datatypes
import CpcMicro.Proofs.TypePreservation.CoreArith
import CpcMicro.Proofs.TypePreservation.Datatypes

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

theorem smtx_typeof_translation_not_of_non_none
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
    cases h : __smtx_typeof (__eo_to_smt x) <;>
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at hNonNone
    simp
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]

theorem smtx_typeof_translation_or_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl hApplyNN
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]

theorem smtx_typeof_translation_and_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl hApplyNN
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]

theorem smtx_typeof_translation_imp_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl hApplyNN
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]

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

theorem smtx_typeof_eq_non_none
    {T U : SmtType}
    (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    T = U ∧ T ≠ SmtType.None := by
  by_cases hNone : T = SmtType.None
  · subst hNone
    exfalso
    exact h (by simp [__smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq])
  · by_cases hEq : T = U
    · exact ⟨hEq, hNone⟩
    · exfalso
      exact h (by
        simp [__smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hNone, hEq])

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
    rw [hF]
    simp
  have hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hX]
    exact hA
  have hFEo : __eo_to_smt_type (__eo_typeof f) = SmtType.Map A B := by
    simpa [ihF hFNN] using hF
  have hXEo : __eo_to_smt_type (__eo_typeof x) = A := by
    simpa [ihX hXNN] using hX
  rcases eo_to_smt_type_eq_map_iff.mp hFEo with
    ⟨T1, T2, hFun, hT1, hT2, hT1NN, _hT2NN⟩
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
    rw [hTranslate, hGeneric]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hF, hX, hA]
  have hTypeApply :
      __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType T1) T2) T1 = T2 := by
    rw [__eo_typeof_apply.eq_def]
    by_cases hStuck : T1 = Term.Stuck
    · exact False.elim (hT1NotStuck hStuck)
    · simp [hStuck, __eo_requires.eq_def, eo_lit_teq, eo_lit_ite, eo_lit_not]
      intro hFalse
      cases hFalse
  rw [hSmt, hTypeof, hFun, hArgTy, hTypeApply, hT2]

end TranslationProofs
