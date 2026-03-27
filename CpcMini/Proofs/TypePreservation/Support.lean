import CpcMini.Proofs.TypePreservation.Common

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
  | dt_cons (s : smt_lit_String) (d : SmtDatatype) (i : smt_lit_Nat) :
      supported_preservation_term (SmtTerm.DtCons s d i)
  | dt_sel {s : smt_lit_String} {d : SmtDatatype} {i j : smt_lit_Nat} {x : SmtTerm}
      (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
      (hT : type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)))
      (htx : term_has_non_none_type x)
      (hsx : supported_preservation_term x) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)
  | dt_tester (s : smt_lit_String) (d : SmtDatatype) (i : smt_lit_Nat) (x : SmtTerm) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.DtTester s d i) x)
  | apply {f x : SmtTerm}
      (hTy : generic_apply_type f x)
      (hEval : generic_apply_eval f x)
      (htf : term_has_non_none_type f)
      (hsf : supported_preservation_term f)
      (htx : term_has_non_none_type x)
      (hsx : supported_preservation_term x) :
      supported_preservation_term (SmtTerm.Apply f x)

end Smtm
