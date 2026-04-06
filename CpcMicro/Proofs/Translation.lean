import CpcMicro.Proofs.Translation.Datatypes
import CpcMicro.Proofs.Translation.Apply

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
2. Datatype helper translations that remain in the reduced micro fragment.
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

theorem smt_lit_ite_ne_map
    {c : smt_lit_Bool} {T U A B : SmtType}
    (hT : T ≠ SmtType.Map A B)
    (hU : U ≠ SmtType.Map A B) :
    smt_lit_ite c T U ≠ SmtType.Map A B := by
  cases c
  · simpa [smt_lit_ite] using hU
  · simpa [smt_lit_ite] using hT

theorem eo_to_smt_type_ne_map
    (T : Term) (A B : SmtType) :
    __eo_to_smt_type T ≠ SmtType.Map A B := by
  cases T with
  | Apply f x =>
      cases f with
      | BitVec =>
          cases x <;> simp [__eo_to_smt_type]
      | Seq =>
          by_cases h : __eo_to_smt_type x = SmtType.None
          · simp [__eo_to_smt_type, h]
          · simp [__eo_to_smt_type, h]
      | _ =>
          simp [__eo_to_smt_type]
  | _ =>
      simp [__eo_to_smt_type]

theorem smtx_typeof_guard_ne_map
    {T U A B : SmtType}
    (hU : U ≠ SmtType.Map A B) :
    __smtx_typeof_guard T U ≠ SmtType.Map A B := by
  unfold __smtx_typeof_guard
  exact smt_lit_ite_ne_map (by simp) hU

theorem smtx_typeof_guard_inhabited_ne_map
    {T U A B : SmtType}
    (hU : U ≠ SmtType.Map A B) :
    __smtx_typeof_guard_inhabited T U ≠ SmtType.Map A B := by
  unfold __smtx_typeof_guard_inhabited
  exact smt_lit_ite_ne_map hU (by simp)

theorem smtx_typeof_apply_eq_none_of_head_not_map
    {F X : SmtType}
    (hF : ∀ T U, F ≠ SmtType.Map T U) :
    __smtx_typeof_apply F X = SmtType.None := by
  cases F with
  | Map T U =>
      exact False.elim (hF T U rfl)
  | _ =>
      simp [__smtx_typeof_apply]

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

end TranslationProofs
