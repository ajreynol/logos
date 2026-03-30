import Cpc.Proofs.Translation.Datatypes
import Cpc.Proofs.Translation.Quantifiers

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-!
This file is the staging area for the full EO-to-SMT translation typing proof.
The intended proof structure mirrors the helper decomposition in `Cpc.Spec`:

1. Base type translation and direct constructor cases.
2. Datatype and tuple-specific translation helpers.
3. Quantifier, lambda, and substitution-specific translation helpers.
4. The main theorem, proved by following the recursion pattern of `__eo_to_smt`.
-/

/-- Direct form of the translation typing theorem. -/
theorem eo_to_smt_typeof_matches_translation
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) := by
  cases t <;> intro hNonNone
  case __eo_pf t =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case Int =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case Real =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case BitVec =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case Char =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case Seq =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case __eo_List =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case __eo_List_nil =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case __eo_List_cons =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case Bool =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case Boolean b =>
    simp [__eo_to_smt.eq_def]
  case «Type» =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case Stuck =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case FunType =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case DatatypeType s d =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case DatatypeTypeRef s =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case USort i =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case _at__at_Pair =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case _at__at_pair =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case _at__at_result_null =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case _at__at_result_invalid =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case re_allchar =>
    simp [__eo_to_smt.eq_def]
  case re_none =>
    simp [__eo_to_smt.eq_def]
  case re_all =>
    simp [__eo_to_smt.eq_def]
  case RegLan =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case UnitTuple =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case Tuple =>
    simp [__eo_to_smt.eq_def] at hNonNone
  case tuple_unit =>
    simpa [__eo_to_smt.eq_def] using smtx_typeof_tuple_unit_translation
  case Set =>
    simp [__eo_to_smt.eq_def] at hNonNone
  all_goals sorry

/--
Compatibility wrapper matching the more explicit theorem shape we used in the
`CpcMini` development.
-/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = T ->
    __smtx_typeof s = __eo_to_smt_type T := by
  intro hs hNonNone hTy
  subst s
  simpa [hTy] using eo_to_smt_typeof_matches_translation t hNonNone

theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = Term.Bool ->
    __smtx_typeof s = SmtType.Bool := by
  intro hs hNonNone hTy
  exact eo_to_smt_well_typed_and_typeof_implies_smt_type
    t Term.Bool s hs hNonNone hTy

end TranslationProofs
