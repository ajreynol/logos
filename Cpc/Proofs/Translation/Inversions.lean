import Cpc.Proofs.Translation.Base

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

theorem eo_to_smt_type_tuple_ne_bool
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Bool := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
            · simp [hs]
        | sum c' d'' =>
            simp

theorem eo_to_smt_type_tuple_ne_int
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Int := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
            · simp [hs]
        | sum c' d'' =>
            simp

theorem eo_to_smt_type_tuple_ne_real
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Real := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
            · simp [hs]
        | sum c' d'' =>
            simp

theorem eo_to_smt_type_tuple_ne_reglan
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.RegLan := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
            · simp [hs]
        | sum c' d'' =>
            simp

theorem eo_to_smt_type_tuple_ne_bitvec
    (U V : SmtType) (w : smt_lit_Int) :
    __eo_to_smt_type_tuple U V ≠ SmtType.BitVec w := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
            · simp [hs]
        | sum c' d'' =>
            simp

theorem eo_to_smt_type_tuple_ne_char
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Char := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
            · simp [hs]
        | sum c' d'' =>
            simp

theorem eo_to_smt_type_tuple_ne_seq
    (U V W : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Seq W := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
            · simp [hs]
        | sum c' d'' =>
            simp

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
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_bool (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim

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
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_int (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim

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
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_real (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim

theorem eo_to_smt_type_eq_reglan
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.RegLan) :
    T = Term.RegLan := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case RegLan =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_reglan (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim

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
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_char (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim

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
        simpa [h] using rfl
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_bitvec (__eo_to_smt_type y) (__eo_to_smt_type x) w h).elim

theorem eo_to_smt_type_eq_seq
    {T : Term} {U : SmtType}
    (h : __eo_to_smt_type T = SmtType.Seq U) :
    ∃ V, T = Term.Apply Term.Seq V ∧ __eo_to_smt_type V = U := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case Seq =>
      exact ⟨x, rfl, by simpa [__eo_to_smt_type] using h⟩
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_seq (__eo_to_smt_type y) (__eo_to_smt_type x) U h).elim

theorem eo_to_smt_type_eq_seq_char
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Seq SmtType.Char) :
    T = Term.Apply Term.Seq Term.Char := by
  rcases eo_to_smt_type_eq_seq h with ⟨V, rfl, hV⟩
  rw [eo_to_smt_type_eq_char hV]

end TranslationProofs
