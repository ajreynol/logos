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
This file is the staging area for the reduced `CpcMicro` EO-to-SMT translation
typing port.

Unlike full `Cpc`, the micro development here still focuses on the fragment
already used by the checker. The type translation now includes EO function
types via SMT maps, but the proof file below is still centered on the direct
boolean/equality fragment that already lines up cleanly:

1. Direct translation helpers for literals and symbols.
2. Shape lemmas for key translated type forms.
3. Fully translated boolean/equality applications.
-/

theorem smtx_typeof_eq_bool_iff
    (T U : SmtType) :
    __smtx_typeof_eq T U = SmtType.Bool ↔ T = U ∧ T ≠ SmtType.None := by
  unfold __smtx_typeof_eq __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · subst hT
    simp [smt_lit_ite, smt_lit_Teq]
  · by_cases hEq : T = U
    · subst hEq
      simp [smt_lit_ite, smt_lit_Teq, hT]
    · simp [smt_lit_ite, smt_lit_Teq, hEq, hT]

private theorem eo_to_smt_type_fun_ne_bool
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Bool := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

private theorem eo_to_smt_type_fun_ne_usort
    (T U : Term) (i : eo_lit_Nat) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.USort i := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

private theorem eo_to_smt_type_fun_ne_int
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Int := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

private theorem eo_to_smt_type_fun_ne_real
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Real := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

private theorem eo_to_smt_type_fun_ne_char
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Char := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

private theorem eo_to_smt_type_fun_ne_bitvec
    (T U : Term) (w : smt_lit_Int) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.BitVec w := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

private theorem eo_to_smt_type_fun_ne_seq
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Seq V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

private theorem eo_to_smt_type_fun_ne_reglan
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.RegLan := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

private theorem eo_to_smt_type_fun_ne_set
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Set V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

theorem eo_to_smt_type_eq_bool
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Bool) :
    T = Term.Bool := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Bool =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Seq =>
      by_cases hx : __eo_to_smt_type x = SmtType.None
      · simp [hx] at h
      · simp [hx] at h
    case Apply g y =>
      cases g <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_bool y x h).elim

theorem eo_to_smt_type_eq_usort
    {T : Term} {i : eo_lit_Nat}
    (h : __eo_to_smt_type T = SmtType.USort i) :
    T = Term.USort i := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case USort j =>
    cases h
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Seq =>
      by_cases hx : __eo_to_smt_type x = SmtType.None
      · simp [hx] at h
      · simp [hx] at h
    case Apply g y =>
      cases g <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_usort y x i h).elim

theorem eo_to_smt_type_eq_int
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Int) :
    T = Term.Int := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Int =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Seq =>
      by_cases hx : __eo_to_smt_type x = SmtType.None
      · simp [hx] at h
      · simp [hx] at h
    case Apply g y =>
      cases g <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_int y x h).elim

theorem eo_to_smt_type_eq_real
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Real) :
    T = Term.Real := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Real =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Seq =>
      by_cases hx : __eo_to_smt_type x = SmtType.None
      · simp [hx] at h
      · simp [hx] at h
    case Apply g y =>
      cases g <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_real y x h).elim

theorem eo_to_smt_type_eq_char
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Char) :
    T = Term.Char := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Char =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Seq =>
      by_cases hx : __eo_to_smt_type x = SmtType.None
      · simp [hx] at h
      · simp [hx] at h
    case Apply g y =>
      cases g <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_char y x h).elim

theorem eo_to_smt_type_eq_bitvec
    {T : Term} {w : smt_lit_Int}
    (h : __eo_to_smt_type T = SmtType.BitVec w) :
    T = Term.Apply Term.BitVec (Term.Numeral w) := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
      case Numeral n =>
        cases h
        rfl
    case Seq =>
      by_cases hx : __eo_to_smt_type x = SmtType.None
      · simp [hx] at h
      · simp [hx] at h
    case Apply g y =>
      cases g <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_bitvec y x w h).elim

theorem eo_to_smt_type_eq_seq
    {T : Term} {U : SmtType}
    (h : __eo_to_smt_type T = SmtType.Seq U) :
    ∃ V, T = Term.Apply Term.Seq V ∧
      __eo_to_smt_type V = U ∧
      __eo_to_smt_type V ≠ SmtType.None := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case Seq =>
      by_cases hx : __eo_to_smt_type x = SmtType.None
      · simp [hx] at h
      · exact ⟨x, rfl, by simpa [hx] using h, hx⟩
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Apply g y =>
      cases g <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_seq y x U h).elim

theorem eo_to_smt_type_eq_seq_char
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Seq SmtType.Char) :
    T = Term.Apply Term.Seq Term.Char := by
  rcases eo_to_smt_type_eq_seq h with ⟨V, rfl, hV, _⟩
  rw [eo_to_smt_type_eq_char hV]

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

theorem smtx_typeof_guard_eq_map_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.Map A B ↔
      T ≠ SmtType.None ∧ U = SmtType.Map A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, smt_lit_ite, smt_lit_Teq]
  · simp [hT, smt_lit_ite, smt_lit_Teq]

theorem eo_to_smt_type_eq_map_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.Map A B ↔
      ∃ T1 T2,
        T = Term.Apply (Term.Apply Term.FunType T1) T2 ∧
        __eo_to_smt_type T1 = A ∧
        __eo_to_smt_type T2 = B ∧
        __eo_to_smt_type T1 ≠ SmtType.None ∧
        __eo_to_smt_type T2 ≠ SmtType.None := by
  constructor
  · intro h
    cases T with
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | FunType =>
                have hOuter :
                    __smtx_typeof_guard (__eo_to_smt_type y)
                      (__smtx_typeof_guard (__eo_to_smt_type x)
                        (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x))) =
                      SmtType.Map A B := by
                  simpa using h
                rcases smtx_typeof_guard_eq_map_iff.mp hOuter with ⟨hyNN, hInner⟩
                rcases smtx_typeof_guard_eq_map_iff.mp hInner with ⟨hxNN, hMap⟩
                injection hMap with hA hB
                exact ⟨y, x, rfl, hA, hB, hyNN, hxNN⟩
            | _ =>
                simp [__eo_to_smt_type] at h
        | BitVec =>
            cases x <;> simp [__eo_to_smt_type] at h
        | Seq =>
            by_cases hx : __eo_to_smt_type x = SmtType.None
            · simp [__eo_to_smt_type, hx] at h
            · simp [__eo_to_smt_type, hx] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨T1, T2, rfl, hT1, hT2, hT1NN, hT2NN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hT1]
    have hBNN : B ≠ SmtType.None := by
      rwa [← hT2]
    simp [eo_to_smt_type_fun, hT1, hT2, hANN, hBNN,
      __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]

theorem eo_to_smt_type_ne_reglan
    (T : Term) :
    __eo_to_smt_type T ≠ SmtType.RegLan := by
  cases T <;> try simp [__eo_to_smt_type]
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type]
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type]
    case Seq =>
      by_cases hx : __eo_to_smt_type x = SmtType.None
      · simp [hx]
      · simp [hx]
    case Apply g y =>
      cases g <;> try simp [__eo_to_smt_type]
      case FunType =>
        exact eo_to_smt_type_fun_ne_reglan y x

theorem eo_to_smt_type_ne_set
    (T : Term) (V : SmtType) :
    __eo_to_smt_type T ≠ SmtType.Set V := by
  cases T <;> try simp [__eo_to_smt_type]
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type]
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type]
    case Seq =>
      by_cases hx : __eo_to_smt_type x = SmtType.None
      · simp [hx]
      · simp [hx]
    case Apply g y =>
      cases g <;> try simp [__eo_to_smt_type]
      case FunType =>
        exact eo_to_smt_type_fun_ne_set y x V

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
