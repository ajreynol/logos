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

The mini type translation now includes EO function types via SMT maps, but the
proof port here is still intentionally centered on the boolean/equality fragment
already used by the checker. In other words, the proof file is narrower than the
translation semantics on purpose. The current staging area therefore focuses on:

1. Direct translation helpers for literals and symbols.
2. Datatype head translation helpers.
3. Fully translated boolean/equality applications.
-/

/-- Inductive predicate describing the boolean and equality EO terms handled by the mini translation proof. -/
inductive supported_bool_translation_term : Term -> Prop where
  | boolean (b : native_Bool) :
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

/-- Shows that supported boolean mini translations always have SMT Boolean type when defined. -/
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

end TranslationProofs
