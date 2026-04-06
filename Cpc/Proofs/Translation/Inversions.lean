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

private theorem eo_to_smt_type_fun_ne_bool
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Bool := by
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

private theorem eo_to_smt_type_fun_ne_reglan
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.RegLan := by
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

private theorem eo_to_smt_type_seq_inner
    (T : Term) {U : SmtType}
    (h : __eo_to_smt_type (Term.Apply Term.Seq T) = SmtType.Seq U) :
    __eo_to_smt_type T = U := by
  cases hT : __eo_to_smt_type T <;>
    simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT] at h
  all_goals exact h

theorem eo_to_smt_type_eq_bool
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Bool) :
    T = Term.Bool := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Bool =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case Seq =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case Set =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_bool y x h).elim
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_bool (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
      case Array =>
        cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
          simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hy, hx] at h

theorem eo_to_smt_type_eq_int
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Int) :
    T = Term.Int := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Int =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case Seq =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case Set =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_int y x h).elim
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_int (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
      case Array =>
        cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
          simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hy, hx] at h

theorem eo_to_smt_type_eq_real
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Real) :
    T = Term.Real := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Real =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case Seq =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case Set =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_real y x h).elim
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_real (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
      case Array =>
        cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
          simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hy, hx] at h

theorem eo_to_smt_type_eq_reglan
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.RegLan) :
    T = Term.RegLan := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case RegLan =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case Seq =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case Set =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_reglan y x h).elim
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_reglan (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
      case Array =>
        cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
          simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hy, hx] at h

theorem eo_to_smt_type_eq_char
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Char) :
    T = Term.Char := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Char =>
    rfl
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case Seq =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case Set =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_char y x h).elim
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_char (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
      case Array =>
        cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
          simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hy, hx] at h

theorem eo_to_smt_type_eq_bitvec
    {T : Term} {w : smt_lit_Int}
    (h : __eo_to_smt_type T = SmtType.BitVec w) :
    T = Term.Apply Term.BitVec (Term.Numeral w) := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case Seq =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case Set =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
      case Numeral n =>
        cases h
        rfl
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_bitvec y x w h).elim
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_bitvec (__eo_to_smt_type y) (__eo_to_smt_type x) w h).elim
      case Array =>
        cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
          simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hy, hx] at h

theorem eo_to_smt_type_eq_seq
    {T : Term} {U : SmtType}
    (h : __eo_to_smt_type T = SmtType.Seq U) :
    ∃ V, T = Term.Apply Term.Seq V ∧ __eo_to_smt_type V = U := by
  cases T <;> try simp [__eo_to_smt_type] at h
  case Apply f x =>
    cases f <;> try simp [__eo_to_smt_type] at h
    case Seq =>
      exact ⟨x, rfl, eo_to_smt_type_seq_inner x h⟩
    case Set =>
      cases hx : __eo_to_smt_type x <;>
        simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx] at h
    case BitVec =>
      cases x <;> simp [__eo_to_smt_type] at h
    case Apply f y =>
      cases f <;> try simp [__eo_to_smt_type] at h
      case FunType =>
        exact (eo_to_smt_type_fun_ne_seq y x U h).elim
      case Tuple =>
        exact (eo_to_smt_type_tuple_ne_seq (__eo_to_smt_type y) (__eo_to_smt_type x) U h).elim
      case Array =>
        cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
          simp [__smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hy, hx] at h

theorem eo_to_smt_type_eq_seq_char
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Seq SmtType.Char) :
    T = Term.Apply Term.Seq Term.Char := by
  rcases eo_to_smt_type_eq_seq h with ⟨V, rfl, hV⟩
  rw [eo_to_smt_type_eq_char hV]

end TranslationProofs
