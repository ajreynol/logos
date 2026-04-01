import CpcMini.Proofs.Translation.Datatypes
import CpcMini.Proofs.Translation.Apply

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-!
This file is the staging area for the `CpcMini` EO-to-SMT translation typing
port.

Unlike `Cpc`, the current mini `__eo_to_smt_type` only translates first-order EO
types, so the full wrapper theorem from `Cpc/Proofs/Translation.lean` is too
strong for constructor heads whose SMT translation has a function-like datatype
type. The port here therefore focuses on the fragment that already lines up
cleanly in `CpcMini`:

1. Direct translation helpers for literals and symbols.
2. Datatype head translation helpers.
3. Fully translated boolean/equality applications.
-/

inductive supported_bool_translation_term : Term -> Prop where
  | boolean (b : eo_lit_Bool) :
      supported_bool_translation_term (Term.Boolean b)
  | «not» (x : Term) :
      supported_bool_translation_term (Term.Apply Term.not x)
  | «or» (x y : Term) :
      supported_bool_translation_term (Term.Apply (Term.Apply Term.or x) y)
  | «and» (x y : Term) :
      supported_bool_translation_term (Term.Apply (Term.Apply Term.and x) y)
  | «imp» (x y : Term) :
      supported_bool_translation_term (Term.Apply (Term.Apply Term.imp x) y)
  | eq (x y : Term) :
      supported_bool_translation_term (Term.Apply (Term.Apply Term.eq x) y)

theorem eo_to_smt_supported_bool_term_has_bool_smt_type
    {t : Term} :
    supported_bool_translation_term t ->
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
  intro hs hNonNone
  cases hs with
  | boolean b =>
      simp [__eo_to_smt.eq_def, __smtx_typeof]
  | not x =>
      simpa using smtx_typeof_translation_not_of_non_none x hNonNone
  | or x y =>
      simpa using smtx_typeof_translation_or_of_non_none x y hNonNone
  | and x y =>
      simpa using smtx_typeof_translation_and_of_non_none x y hNonNone
  | imp x y =>
      simpa using smtx_typeof_translation_imp_of_non_none x y hNonNone
  | eq x y =>
      simpa using smtx_typeof_translation_eq_of_non_none x y hNonNone

/--
Compatibility wrapper in the shape used by the mini proofs. The EO typing
assumption is redundant for this supported fragment, but we keep it in the
statement to match the eventual full theorem shape.
-/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool_of_supported
    {t : Term} (s : SmtTerm) :
    supported_bool_translation_term t ->
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = Term.Bool ->
    __smtx_typeof s = SmtType.Bool := by
  intro hs hsmt hNonNone _hTy
  subst s
  exact eo_to_smt_supported_bool_term_has_bool_smt_type hs hNonNone

private theorem eo_requires_eq_bool
    {T X U : Term} :
    __eo_requires T X U = Term.Bool ->
      T = X ∧ T ≠ Term.Stuck ∧ U = Term.Bool := by
  intro h
  by_cases hEq : T = X
  · by_cases hStuck : T = Term.Stuck
    · subst X
      subst T
      have : False := by
        simpa [__eo_requires, eo_lit_teq, eo_lit_ite, SmtEval.smt_lit_not] using h
      exact False.elim this
    · have hU : U = Term.Bool := by
        subst X
        simpa [__eo_requires, eo_lit_teq, eo_lit_not, eo_lit_ite, hStuck] using h
      exact ⟨hEq, hStuck, hU⟩
  · simp [__eo_requires, eo_lit_ite, eo_lit_teq, eo_lit_not, hEq] at h

private theorem eo_requires_fun_ends_in_bool
    {T X U : Term} :
    eo_fun_ends_in_bool (__eo_requires T X U) ->
      T = X ∧ T ≠ Term.Stuck ∧ eo_fun_ends_in_bool U := by
  intro h
  by_cases hEq : T = X
  · by_cases hStuck : T = Term.Stuck
    · subst X
      subst T
      have : False := by
        simpa [__eo_requires, eo_lit_teq, eo_lit_ite, SmtEval.smt_lit_not,
          eo_fun_ends_in_bool] using h
      exact False.elim this
    · have hU : eo_fun_ends_in_bool U := by
        subst X
        simpa [__eo_requires, eo_lit_teq, eo_lit_not, eo_lit_ite, hStuck,
          eo_fun_ends_in_bool] using h
      exact ⟨hEq, hStuck, hU⟩
  · simp [__eo_requires, eo_lit_ite, eo_lit_teq, eo_lit_not, hEq,
      eo_fun_ends_in_bool] at h

private theorem eo_typeof_apply_eq_bool
    {F X : Term} :
    __eo_typeof_apply F X = Term.Bool ->
      F = Term.Apply (Term.Apply Term.FunType X) Term.Bool := by
  intro h
  by_cases hX : X = Term.Stuck
  · subst X
    simp [__eo_typeof_apply] at h
  · cases F with
    | Apply F1 U =>
        cases F1 with
        | Apply F11 T =>
            cases F11 with
            | FunType =>
                obtain ⟨hEq, _hStuck, hU⟩ :=
                  eo_requires_eq_bool (T := T) (X := X) (U := U)
                    (by simpa [__eo_typeof_apply, hX] using h)
                subst hEq
                subst hU
                rfl
            | _ =>
                simp [__eo_typeof_apply, hX] at h
        | _ =>
            simp [__eo_typeof_apply, hX] at h
    | _ =>
        simp [__eo_typeof_apply, hX] at h

private theorem eo_fun_ends_in_bool_of_typeof_apply
    {F X : Term} :
    eo_fun_ends_in_bool (__eo_typeof_apply F X) ->
      eo_fun_ends_in_bool F := by
  intro h
  by_cases hX : X = Term.Stuck
  · subst X
    simp [__eo_typeof_apply, eo_fun_ends_in_bool] at h
  · cases F with
    | Apply F1 U =>
        cases F1 with
        | Apply F11 T =>
            cases F11 with
            | FunType =>
                obtain ⟨hEq, _hStuck, hU⟩ :=
                  eo_requires_fun_ends_in_bool (T := T) (X := X) (U := U)
                    (by simpa [__eo_typeof_apply, hX] using h)
                subst hEq
                simpa [eo_fun_ends_in_bool] using Or.inr hU
            | _ =>
                simp [__eo_typeof_apply, hX, eo_fun_ends_in_bool] at h
        | _ =>
            simp [__eo_typeof_apply, hX, eo_fun_ends_in_bool] at h
    | _ =>
        simp [__eo_typeof_apply, hX, eo_fun_ends_in_bool] at h


end TranslationProofs
