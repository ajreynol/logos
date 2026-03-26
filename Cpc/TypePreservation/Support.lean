import Cpc.TypePreservation.Common

open Smtm

namespace Smtm

inductive supported_preservation_term : SmtTerm -> Prop
  | boolean (b : smt_lit_Bool) : supported_preservation_term (SmtTerm.Boolean b)
  | numeral (n : smt_lit_Int) : supported_preservation_term (SmtTerm.Numeral n)
  | rational (q : smt_lit_Rat) : supported_preservation_term (SmtTerm.Rational q)
  | string (s : smt_lit_String) : supported_preservation_term (SmtTerm.String s)
  | binary (w n : smt_lit_Int) : supported_preservation_term (SmtTerm.Binary w n)
  | var (s : smt_lit_String) (T : SmtType) : supported_preservation_term (SmtTerm.Var s T)
  | uconst (s : smt_lit_String) (T : SmtType) : supported_preservation_term (SmtTerm.UConst s T)
  | re_allchar : supported_preservation_term SmtTerm.re_allchar
  | re_none : supported_preservation_term SmtTerm.re_none
  | re_all : supported_preservation_term SmtTerm.re_all
  | seq_empty (T : SmtType) : supported_preservation_term (SmtTerm.seq_empty T)
  | set_empty (T : SmtType) : supported_preservation_term (SmtTerm.set_empty T)
  | seq_unit {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.seq_unit t)
  | set_singleton {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.set_singleton t)
  | seq_nth {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.seq_nth t1) t2)
  | set_union {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union t1) t2)
  | set_inter {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter t1) t2)
  | set_minus {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus t1) t2)
  | set_member {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member t1) t2)
  | set_subset {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset t1) t2)
  | select {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2)
  | store {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3)
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
  | xor (t1 t2 : SmtTerm) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2)
  | distinct (t1 t2 : SmtTerm) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2)
  | plus {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2)
  | arith_neg {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2)
  | mult {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2)
  | lt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2)
  | leq {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2)
  | gt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2)
  | geq {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2)
  | to_real {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.to_real t)
  | to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.to_int t)
  | is_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.is_int t)
  | abs {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.abs t)
  | div {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div t1) t2)
  | mod {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod t1) t2)
  | multmult {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult t1) t2)
  | divisible {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible t1) t2)
  | int_pow2 {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.int_pow2 t)
  | int_log2 {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.int_log2 t)
  | div_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total t1) t2)
  | mod_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total t1) t2)
  | multmult_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total t1) t2)
  | qdiv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv t1) t2)
  | qdiv_total {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total t1) t2)
  | str_len {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_len t)
  | str_to_lower {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_to_lower t)
  | str_to_upper {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_to_upper t)
  | str_concat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat t1) t2)
  | str_substr {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr t1) t2) t3)
  | str_contains {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains t1) t2)
  | str_indexof {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3)
  | str_at {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at t1) t2)
  | str_replace {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace t1) t2) t3)
  | str_rev {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_rev t)
  | str_update {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update t1) t2) t3)
  | str_replace_all {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all t1) t2) t3)
  | str_replace_re {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re t1) t2) t3)
  | str_replace_re_all {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all t1) t2) t3)
  | str_indexof_re {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re t1) t2) t3)
  | str_to_code {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_to_code t)
  | str_to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_to_int t)
  | str_from_code {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_from_code t)
  | str_from_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_from_int t)
  | str_to_re {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_to_re t)
  | re_mult {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.re_mult t)
  | re_plus {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.re_plus t)
  | re_exp (n : smt_lit_Int) {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_exp (SmtTerm.Numeral n)) t)
  | re_opt {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.re_opt t)
  | re_comp {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.re_comp t)
  | re_range {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range t1) t2)
  | re_concat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat t1) t2)
  | re_inter {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter t1) t2)
  | re_union {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union t1) t2)
  | re_diff {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff t1) t2)
  | re_loop (n1 n2 : smt_lit_Int) {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term
        (SmtTerm.Apply
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_loop (SmtTerm.Numeral n1))
            (SmtTerm.Numeral n2))
          t)
  | str_in_re {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re t1) t2)
  | str_lt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt t1) t2)
  | str_leq {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq t1) t2)
  | str_prefixof {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof t1) t2)
  | str_suffixof {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof t1) t2)
  | str_is_digit {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.str_is_digit t)
  | bv_concat {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2)
  | extract {t1 t2 t3 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2)
      (ht3 : term_has_non_none_type t3)
      (hs3 : supported_preservation_term t3) :
      supported_preservation_term
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3)
  | bvnot {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.bvnot t)
  | bvand {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand t1) t2)
  | bvor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor t1) t2)
  | bvnand {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand t1) t2)
  | bvnor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor t1) t2)
  | bvxor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor t1) t2)
  | bvxnor {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor t1) t2)
  | bvcomp {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp t1) t2)
  | bvneg {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.bvneg t)
  | bvadd {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd t1) t2)
  | bvmul {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul t1) t2)
  | bvudiv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv t1) t2)
  | bvurem {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem t1) t2)
  | bvsub {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub t1) t2)
  | bvult {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult t1) t2)
  | bvule {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule t1) t2)
  | bvugt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt t1) t2)
  | bvuge {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge t1) t2)
  | bvslt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt t1) t2)
  | bvsle {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle t1) t2)
  | bvsgt {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt t1) t2)
  | bvsge {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge t1) t2)
  | bvshl {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl t1) t2)
  | bvlshr {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr t1) t2)
  | bvuaddo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo t1) t2)
  | bvnego {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.bvnego t)
  | bvsaddo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo t1) t2)
  | bvumulo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo t1) t2)
  | bvsmulo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo t1) t2)
  | bvusubo {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo t1) t2)
  | zero_extend {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2)
  | sign_extend {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2)
  | int_to_bv {t1 t2 : SmtTerm}
      (ht1 : term_has_non_none_type t1)
      (hs1 : supported_preservation_term t1)
      (ht2 : term_has_non_none_type t2)
      (hs2 : supported_preservation_term t2) :
      supported_preservation_term (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2)
  | ubv_to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.ubv_to_int t)
  | sbv_to_int {t : SmtTerm}
      (ht : term_has_non_none_type t)
      (hs : supported_preservation_term t) :
      supported_preservation_term (SmtTerm.Apply SmtTerm.sbv_to_int t)

end Smtm
