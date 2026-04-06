import CpcMicro.Proofs.TypePreservation.Common

open Smtm

namespace Smtm

inductive supported_preservation_term : SmtTerm -> Prop
  | boolean (b : smt_lit_Bool) : supported_preservation_term (SmtTerm.Boolean b)
  | numeral (n : smt_lit_Int) : supported_preservation_term (SmtTerm.Numeral n)
  | rational (q : smt_lit_Rat) : supported_preservation_term (SmtTerm.Rational q)
  | string (s : smt_lit_String) : supported_preservation_term (SmtTerm.String s)
  | binary (w n : smt_lit_Int) : supported_preservation_term (SmtTerm.Binary w n)
  | var (s : smt_lit_String) (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.Var s T)
  | uconst (s : smt_lit_String) (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.UConst s T)
  | ite {c t1 t2 : SmtTerm}
      (htc : term_has_non_none_type c)
      (hsc : supported_preservation_term c)
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2)
  | exists (s : smt_lit_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.exists s T) body)
  | forall (s : smt_lit_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.forall s T) body)
  | choice (s : smt_lit_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.choice s T) body)
  | not {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.not t)
  | or {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2)
  | and {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2)
  | imp {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2)
  | eq (t1 t2 : SmtTerm) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)
  | apply {f x : SmtTerm}
      (hTy : generic_apply_type f x)
      (hEval : generic_apply_eval f x)
      (htf : term_has_non_none_type f)
      (hsf : supported_preservation_term f)
      (htx : term_has_non_none_type x)
      (hsx : supported_preservation_term x) :
      supported_preservation_term (SmtTerm.Apply f x)

inductive supported_preservation_apply_case : SmtTerm -> SmtTerm -> Prop where
  | not_case (t : SmtTerm) :
      supported_preservation_apply_case SmtTerm.not t
  | or_case (t1 t2 : SmtTerm) :
      supported_preservation_apply_case (SmtTerm.Apply SmtTerm.or t1) t2
  | and_case (t1 t2 : SmtTerm) :
      supported_preservation_apply_case (SmtTerm.Apply SmtTerm.and t1) t2
  | imp_case (t1 t2 : SmtTerm) :
      supported_preservation_apply_case (SmtTerm.Apply SmtTerm.imp t1) t2
  | eq_case (t1 t2 : SmtTerm) :
      supported_preservation_apply_case (SmtTerm.Apply SmtTerm.eq t1) t2
  | ite_case (c t1 t2 : SmtTerm) :
      supported_preservation_apply_case (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2
  | exists_case (s : smt_lit_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_apply_case (SmtTerm.exists s T) body
  | forall_case (s : smt_lit_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_apply_case (SmtTerm.forall s T) body
  | choice_case (s : smt_lit_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_apply_case (SmtTerm.choice s T) body
  | generic {f x : SmtTerm}
      (hTy : generic_apply_type f x)
      (hEval : generic_apply_eval f x) :
      supported_preservation_apply_case f x

theorem supported_preservation_apply_cases
    (f x : SmtTerm) :
    supported_preservation_apply_case f x := by
  cases f <;> try exact supported_preservation_apply_case.generic rfl (by intro M; rfl)
  case not =>
    exact supported_preservation_apply_case.not_case x
  case «exists» s T =>
    exact supported_preservation_apply_case.exists_case s T x
  case «forall» s T =>
    exact supported_preservation_apply_case.forall_case s T x
  case choice s T =>
    exact supported_preservation_apply_case.choice_case s T x
  case Apply f y =>
    cases f <;> try exact supported_preservation_apply_case.generic rfl (by intro M; rfl)
    case or =>
      exact supported_preservation_apply_case.or_case y x
    case and =>
      exact supported_preservation_apply_case.and_case y x
    case imp =>
      exact supported_preservation_apply_case.imp_case y x
    case eq =>
      exact supported_preservation_apply_case.eq_case y x
    case Apply g c =>
      cases g <;> try exact supported_preservation_apply_case.generic rfl (by intro M; rfl)
      case ite =>
        exact supported_preservation_apply_case.ite_case c y x

end Smtm
