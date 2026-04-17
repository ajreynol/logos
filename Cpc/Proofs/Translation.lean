import Cpc.Proofs.Translation.Datatypes
import Cpc.Proofs.Translation.Apply

open Eo
open SmtEval
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
  let rec go (t : Term) :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t) := by
    cases t <;> intro hNonNone
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
    case Numeral n =>
      symm
      simpa [__eo_to_smt.eq_def] using eo_to_smt_type_typeof_numeral n
    case Rational r =>
      symm
      simpa [__eo_to_smt.eq_def] using eo_to_smt_type_typeof_rational r
    case String s =>
      symm
      simpa [__eo_to_smt.eq_def] using eo_to_smt_type_typeof_string s
    case Binary w n =>
      have hTy : __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None := by
        simpa [__eo_to_smt.eq_def] using hNonNone
      have hWidth : native_zleq 0 w = true :=
        (smtx_binary_well_formed_of_non_none w n hTy).1
      rw [show __smtx_typeof (__eo_to_smt (Term.Binary w n)) =
        SmtType.BitVec (native_int_to_nat w) by
        simpa [__eo_to_smt.eq_def] using smtx_typeof_binary_of_non_none w n hTy]
      symm
      simpa using eo_to_smt_type_typeof_binary w n hWidth
    case Var name T =>
      cases name
      case String s =>
          have hTy : __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) ≠ SmtType.None := by
            simpa [__eo_to_smt.eq_def] using hNonNone
          rw [show __smtx_typeof (__eo_to_smt (Term.Var (Term.String s) T)) = __eo_to_smt_type T by
            simpa [__eo_to_smt.eq_def] using
              smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hTy]
          symm
          simpa using eo_to_smt_type_typeof_var s T
      all_goals
        exact False.elim (hNonNone (by simp [__eo_to_smt.eq_def]))
    case DtCons s d i =>
      symm
      simpa [eo_to_smt_term_dt_cons] using eo_to_smt_type_typeof_dt_cons s d i
    case DtSel s d i j =>
      have hNone : __smtx_typeof (__eo_to_smt (Term.DtSel s d i j)) = SmtType.None := by
        rw [__eo_to_smt.eq_def]
      exact (hNonNone hNone).elim
    case UConst i T =>
      have hTy :
          __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) ≠
            SmtType.None := by
        simpa [__eo_to_smt.eq_def] using hNonNone
      rw [show __smtx_typeof (__eo_to_smt (Term.UConst i T)) = __eo_to_smt_type T by
        simpa [__eo_to_smt.eq_def] using
          smtx_typeof_uconst_of_non_none (native_uconst_id i) (__eo_to_smt_type T) hTy]
      symm
      simpa using eo_to_smt_type_typeof_uconst i T
    case Apply f x =>
      simpa using eo_to_smt_typeof_matches_translation_apply f x (go f) (go x) hNonNone
    case _at_purify x =>
      have hTranslatePurify : __eo_to_smt (Term._at_purify x) = __eo_to_smt x := by
        rw [__eo_to_smt.eq_def]
      have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        intro hNone
        apply hNonNone
        rwa [hTranslatePurify]
      have hX := go x hXNonNone
      rw [hTranslatePurify, hX]
      exact (eo_to_smt_type_typeof_purify x).symm
    case _at_array_deq_diff x1 x2 =>
      simpa using eo_to_smt_typeof_matches_translation_array_deq_diff x1 x2 hNonNone
    case seq_empty x =>
      symm
      simpa [__eo_to_smt.eq_def] using eo_to_smt_type_typeof_seq_empty x
        (by simpa [__eo_to_smt.eq_def] using hNonNone)
    case set_empty x =>
      symm
      simpa [__eo_to_smt.eq_def] using eo_to_smt_type_typeof_set_empty x
        (by simpa [__eo_to_smt.eq_def] using hNonNone)
    case _at_sets_deq_diff x1 x2 =>
      simpa using eo_to_smt_typeof_matches_translation_sets_deq_diff x1 x2 hNonNone
    case _at_quantifiers_skolemize x1 x2 =>
      simpa using eo_to_smt_typeof_matches_translation_quantifiers_skolemize x1 x2 hNonNone
    all_goals
      first
        | exact False.elim (hNonNone (by simp [__eo_to_smt.eq_def]))
        | native_decide
  exact go t

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

/-- Transfers EO Boolean typing to the translated SMT term under a defined translation. -/
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
