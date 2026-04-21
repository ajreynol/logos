import Cpc.Proofs.TypePreservation.Common

open SmtEval
open Smtm

namespace Smtm

/-- Inductive predicate describing the SMT terms covered by the type-preservation proof. -/
inductive supported_preservation_term : SmtTerm -> Prop
  | boolean (b : native_Bool) : supported_preservation_term (SmtTerm.Boolean b)
  | numeral (n : native_Int) : supported_preservation_term (SmtTerm.Numeral n)
  | rational (q : native_Rat) : supported_preservation_term (SmtTerm.Rational q)
  | string (s : native_String) : supported_preservation_term (SmtTerm.String s)
  | binary (w n : native_Int) : supported_preservation_term (SmtTerm.Binary w n)
  | var (s : native_String) (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.Var s T)
  | uconst (s : native_String) (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.UConst s T)
  | re_allchar : supported_preservation_term (SmtTerm.TheoryOp SmtTheoryOp.re_allchar)
  | re_none : supported_preservation_term (SmtTerm.TheoryOp SmtTheoryOp.re_none)
  | re_all : supported_preservation_term (SmtTerm.TheoryOp SmtTheoryOp.re_all)
  | seq_empty (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.seq_empty T)
  | set_empty (T : SmtType)
      (hT : type_inhabited T) :
      supported_preservation_term (SmtTerm.set_empty T)
  | seq_unit {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.seq_unit t)
  | set_singleton {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.set_singleton t)
  | seq_nth {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (hT :
        type_inhabited (__smtx_typeof (theory2 SmtTheoryOp.seq_nth t1 t2))) :
      supported_preservation_term (theory2 SmtTheoryOp.seq_nth t1 t2)
  | set_union {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.set_union t1 t2)
  | set_inter {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.set_inter t1 t2)
  | set_minus {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.set_minus t1 t2)
  | set_member {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.set_member t1 t2)
  | set_subset {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.set_subset t1 t2)
  | select {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.select t1 t2)
  | store {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.store t1 t2 t3)
  | ite {c t1 t2 : SmtTerm}
      (htc : term_has_non_none_type c)
      (hsc : supported_preservation_term c)
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term
        (SmtTerm.ite c t1 t2)
  | exists (s : native_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_term (SmtTerm.exists s T body)
  | forall (s : native_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_term (SmtTerm.forall s T body)
  | choice (s : native_String) (T : SmtType) (body : SmtTerm) :
      supported_preservation_term (SmtTerm.choice_nth s T body 0)
  | not {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.not t)
  | or {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.or t1 t2)
  | and {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.and t1 t2)
  | imp {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.imp t1 t2)
  | eq (t1 t2 : SmtTerm) :
      supported_preservation_term (SmtTerm.eq t1 t2)
  | xor (t1 t2 : SmtTerm) :
      supported_preservation_term (theory2 SmtTheoryOp.xor t1 t2)
  | plus {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.plus t1 t2)
  | arith_neg {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.neg t1 t2)
  | mult {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.mult t1 t2)
  | lt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.lt t1 t2)
  | leq {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.leq t1 t2)
  | gt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.gt t1 t2)
  | geq {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.geq t1 t2)
  | to_real {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.to_real t)
  | to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.to_int t)
  | is_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.is_int t)
  | abs {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.abs t)
  | uneg {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.uneg t)
  | div {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.div t1 t2)
  | mod {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.mod t1 t2)
  | multmult {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.multmult t1 t2)
  | divisible {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.divisible t1 t2)
  | int_pow2 {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.int_pow2 t)
  | int_log2 {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.int_log2 t)
  | div_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.div_total t1 t2)
  | mod_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.mod_total t1 t2)
  | multmult_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.multmult_total t1 t2)
  | qdiv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.qdiv t1 t2)
  | qdiv_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.qdiv_total t1 t2)
  | str_len {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_len t)
  | str_to_lower {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_to_lower t)
  | str_to_upper {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_to_upper t)
  | str_concat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.str_concat t1 t2)
  | str_substr {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.str_substr t1 t2 t3)
  | str_contains {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.str_contains t1 t2)
  | str_indexof {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.str_indexof t1 t2 t3)
  | str_at {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.str_at t1 t2)
  | str_replace {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.str_replace t1 t2 t3)
  | str_rev {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_rev t)
  | str_update {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.str_update t1 t2 t3)
  | str_replace_all {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.str_replace_all t1 t2 t3)
  | str_replace_re {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.str_replace_re t1 t2 t3)
  | str_replace_re_all {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.str_replace_re_all t1 t2 t3)
  | str_indexof_re {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.str_indexof_re t1 t2 t3)
  | str_to_code {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_to_code t)
  | str_to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_to_int t)
  | str_from_code {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_from_code t)
  | str_from_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_from_int t)
  | str_to_re {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_to_re t)
  | re_mult {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.re_mult t)
  | re_plus {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.re_plus t)
  | re_exp (n : native_Int) {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory2 SmtTheoryOp.re_exp (SmtTerm.Numeral n) t)
  | re_opt {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.re_opt t)
  | re_comp {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.re_comp t)
  | re_range {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.re_range t1 t2)
  | re_concat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.re_concat t1 t2)
  | re_inter {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.re_inter t1 t2)
  | re_union {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.re_union t1 t2)
  | re_diff {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.re_diff t1 t2)
  | re_loop (n1 n2 : native_Int) {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term
        (theory3 SmtTheoryOp.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t)
  | str_in_re {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.str_in_re t1 t2)
  | str_lt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.str_lt t1 t2)
  | str_leq {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.str_leq t1 t2)
  | str_prefixof {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.str_prefixof t1 t2)
  | str_suffixof {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.str_suffixof t1 t2)
  | str_is_digit {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.str_is_digit t)
  | bv_concat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.concat t1 t2)
  | extract {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (theory3 SmtTheoryOp.extract t1 t2 t3)
  | bvnot {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.bvnot t)
  | bvand {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvand t1 t2)
  | bvor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvor t1 t2)
  | bvnand {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvnand t1 t2)
  | bvnor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvnor t1 t2)
  | bvxor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvxor t1 t2)
  | bvxnor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvxnor t1 t2)
  | bvcomp {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvcomp t1 t2)
  | bvneg {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.bvneg t)
  | bvadd {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvadd t1 t2)
  | bvmul {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvmul t1 t2)
  | bvudiv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvudiv t1 t2)
  | bvurem {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvurem t1 t2)
  | bvsub {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsub t1 t2)
  | bvult {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvult t1 t2)
  | bvule {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvule t1 t2)
  | bvugt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvugt t1 t2)
  | bvuge {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvuge t1 t2)
  | bvslt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvslt t1 t2)
  | bvsle {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsle t1 t2)
  | bvsgt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsgt t1 t2)
  | bvsge {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsge t1 t2)
  | bvshl {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvshl t1 t2)
  | bvlshr {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvlshr t1 t2)
  | repeat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.repeat t1 t2)
  | bvsdiv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsdiv t1 t2)
  | bvsrem {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsrem t1 t2)
  | bvsmod {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsmod t1 t2)
  | bvashr {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvashr t1 t2)
  | rotate_left {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.rotate_left t1 t2)
  | rotate_right {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.rotate_right t1 t2)
  | bvuaddo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvuaddo t1 t2)
  | bvnego {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.bvnego t)
  | bvsaddo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsaddo t1 t2)
  | bvumulo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvumulo t1 t2)
  | bvsmulo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsmulo t1 t2)
  | bvusubo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvusubo t1 t2)
  | bvssubo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvssubo t1 t2)
  | bvsdivo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.bvsdivo t1 t2)
  | zero_extend {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.zero_extend t1 t2)
  | sign_extend {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.sign_extend t1 t2)
  | int_to_bv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (theory2 SmtTheoryOp.int_to_bv t1 t2)
  | ubv_to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.ubv_to_int t)
  | sbv_to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (theory1 SmtTheoryOp.sbv_to_int t)
  | dt_cons (s : native_String) (d : SmtDatatype) (i : native_Nat) :
      supported_preservation_term (SmtTerm.DtCons s d i)
  | dt_sel {s : native_String} {d : SmtDatatype} {i j : native_Nat} {x : SmtTerm}
      (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
      (hT : type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)))
      (htx : term_has_non_none_type x)
      (hsx : supported_preservation_term x) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)
  | dt_tester (s : native_String) (d : SmtDatatype) (i : native_Nat) (x : SmtTerm) :
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
