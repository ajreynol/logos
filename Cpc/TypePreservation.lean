import Cpc.SmtModel

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

def term_has_non_none_type (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None

def model_total_typed (M : SmtModel) : Prop :=
  ∀ s T, __smtx_typeof_value (__smtx_model_lookup M s T) = T

def model_typed_at (M : SmtModel) (s : smt_lit_String) (T : SmtType) : Prop :=
  __smtx_typeof_value (__smtx_model_lookup M s T) = T

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

theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_lookup M s T) = T :=
  hM s T

theorem model_typed_at_push
    {M : SmtModel}
    {s : smt_lit_String}
    {T : SmtType}
    {v : SmtValue}
    (hv : __smtx_typeof_value v = T) :
    model_typed_at (__smtx_model_push M s T v) s T := by
  unfold model_typed_at __smtx_model_lookup __smtx_model_push
  simp [__smtx_model_key, hv]

theorem model_total_typed_push
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType)
    (v : SmtValue)
    (hv : __smtx_typeof_value v = T) :
    model_total_typed (__smtx_model_push M s T v) := by
  intro s' T'
  unfold __smtx_model_lookup __smtx_model_push
  by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
  · cases h
    simp [hv]
  · simp [h]
    exact hM s' T'

theorem typeof_value_model_eval_boolean
    (M : SmtModel)
    (b : smt_lit_Bool) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Boolean b)) =
      __smtx_typeof (SmtTerm.Boolean b) := rfl

theorem typeof_value_model_eval_numeral
    (M : SmtModel)
    (n : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Numeral n)) =
      __smtx_typeof (SmtTerm.Numeral n) := rfl

theorem typeof_value_model_eval_rational
    (M : SmtModel)
    (q : smt_lit_Rat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Rational q)) =
      __smtx_typeof (SmtTerm.Rational q) := rfl

theorem typeof_value_model_eval_binary
    (M : SmtModel)
    (w n : smt_lit_Int)
    (ht : term_has_non_none_type (SmtTerm.Binary w n)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Binary w n)) =
      __smtx_typeof (SmtTerm.Binary w n) := by
  unfold term_has_non_none_type at ht
  let g :=
    smt_lit_and (smt_lit_zleq 0 w)
      (smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)))
  have hg : g = true := by
    by_cases h : g = true
    · exact h
    · exfalso
      apply ht
      change smt_lit_ite g (SmtType.BitVec w) SmtType.None = SmtType.None
      simp [smt_lit_ite, h]
  have hWidth : smt_lit_zleq 0 w = true := by
    cases h1 : smt_lit_zleq 0 w
    · simp [g, SmtEval.smt_lit_and, h1] at hg
    · rfl
  have hMod :
      smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)) = true := by
    cases h2 : smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w))
    · simp [g, SmtEval.smt_lit_and, hWidth, h2] at hg
    · rfl
  change smt_lit_ite (smt_lit_zleq 0 w) (SmtType.BitVec w) SmtType.None =
    __smtx_typeof (SmtTerm.Binary w n)
  rw [show smt_lit_ite (smt_lit_zleq 0 w) (SmtType.BitVec w) SmtType.None = SmtType.BitVec w by
    simp [smt_lit_ite, hWidth]]
  rw [show __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec w by
    simp [__smtx_typeof, smt_lit_ite, SmtEval.smt_lit_and, hWidth, hMod]]

theorem typeof_value_model_eval_var
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Var s T)) =
      __smtx_typeof (SmtTerm.Var s T) := by
  change __smtx_typeof_value (__smtx_model_lookup M s T) = T
  exact hM s T

theorem typeof_value_model_eval_uconst
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.UConst s T)) =
      __smtx_typeof (SmtTerm.UConst s T) := by
  change __smtx_typeof_value (__smtx_model_lookup M s T) = T
  exact hM s T

theorem typeof_value_model_eval_re_allchar
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_allchar) =
      __smtx_typeof SmtTerm.re_allchar := rfl

theorem typeof_value_model_eval_re_none
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_none) =
      __smtx_typeof SmtTerm.re_none := rfl

theorem typeof_value_model_eval_re_all
    (M : SmtModel) :
    __smtx_typeof_value (__smtx_model_eval M SmtTerm.re_all) =
      __smtx_typeof SmtTerm.re_all := rfl

theorem typeof_value_model_eval_seq_empty
    (M : SmtModel)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.seq_empty T)) =
      __smtx_typeof (SmtTerm.seq_empty T) := rfl

theorem typeof_value_model_eval_set_empty
    (M : SmtModel)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.set_empty T)) =
      __smtx_typeof (SmtTerm.set_empty T) := rfl

theorem typeof_value_model_eval_seq_unit
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.seq_unit t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.seq_unit t) := by
  unfold term_has_non_none_type at ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.seq_unit t) = SmtType.Seq (__smtx_typeof t) by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, ht]]
  rw [show __smtx_model_eval M (SmtTerm.Apply SmtTerm.seq_unit t) =
      SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval M t)
          (SmtSeq.empty (__smtx_typeof_value (__smtx_model_eval M t)))) by
    rfl]
  simp [__smtx_typeof_value, __smtx_typeof_seq_value, smt_lit_ite, smt_lit_Teq, hpres]

theorem typeof_value_model_eval_set_singleton
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.set_singleton t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.set_singleton t) := by
  unfold term_has_non_none_type at ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.set_singleton t) =
      SmtType.Map (__smtx_typeof t) SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, ht]]
  rw [show __smtx_model_eval M (SmtTerm.Apply SmtTerm.set_singleton t) =
      SmtValue.Map
        (SmtMap.cons (__smtx_model_eval M t) (SmtValue.Boolean true)
          (SmtMap.default (__smtx_typeof_value (__smtx_model_eval M t)) (SmtValue.Boolean false))) by
    rfl]
  simp [__smtx_typeof_value, __smtx_typeof_map_value, smt_lit_ite, smt_lit_Teq, hpres]

theorem exists_body_bool_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.exists s T) body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  rfl

theorem exists_term_typeof_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.exists s T) body)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.exists s T) body) = SmtType.Bool := by
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, exists_body_bool_of_non_none ht]

theorem typeof_value_model_eval_exists
    (M : SmtModel)
    (s : smt_lit_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.exists s T) body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.exists s T) body)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.exists s T) body) := by
  classical
  rw [exists_term_typeof_of_non_none ht]
  change
    __smtx_typeof_value
      (if h :
          ∃ v : SmtValue,
            __smtx_typeof_value v = T ∧
              __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
        SmtValue.Boolean true
      else
        SmtValue.Boolean false) = SmtType.Bool
  by_cases h :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · simp [h, __smtx_typeof_value]
  · simp [h, __smtx_typeof_value]

theorem forall_body_bool_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.forall s T) body)) :
    __smtx_typeof body = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  rfl

theorem forall_term_typeof_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.forall s T) body)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.forall s T) body) = SmtType.Bool := by
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, forall_body_bool_of_non_none ht]

theorem typeof_value_model_eval_forall
    (M : SmtModel)
    (s : smt_lit_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.forall s T) body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.forall s T) body)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.forall s T) body) := by
  classical
  rw [forall_term_typeof_of_non_none ht]
  change
    __smtx_typeof_value
      (if h :
          ∀ v : SmtValue,
            __smtx_typeof_value v = T ->
              __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
        SmtValue.Boolean true
      else
        SmtValue.Boolean false) = SmtType.Bool
  by_cases h :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · have hIf :
        (if h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
          SmtValue.Boolean true
        else
          SmtValue.Boolean false) = SmtValue.Boolean true := by
        by_cases h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
        · simpa using h'
        · contradiction
    rw [hIf]
    rfl
  · have hIf :
        (if h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
          SmtValue.Boolean true
        else
          SmtValue.Boolean false) = SmtValue.Boolean false := by
        by_cases h' :
            ∀ v : SmtValue,
              __smtx_typeof_value v = T ->
                __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
        · contradiction
        · simp [h']
    rw [hIf]
    rfl

theorem choice_term_has_witness
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.choice s T) body)) :
    ∃ v : SmtValue, __smtx_typeof_value v = T := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  exact ht.1

theorem choice_term_typeof_of_non_none
    {s : smt_lit_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.choice s T) body)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.choice s T) body) = T := by
  have hTy := choice_term_has_witness ht
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof body <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h, hTy] at ht ⊢

theorem typeof_value_model_eval_choice
    (M : SmtModel)
    (s : smt_lit_String)
    (T : SmtType)
    (body : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.choice s T) body)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.choice s T) body)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.choice s T) body) := by
  classical
  have hTy : ∃ v : SmtValue, __smtx_typeof_value v = T :=
    choice_term_has_witness ht
  rw [choice_term_typeof_of_non_none ht]
  change
    __smtx_typeof_value
      (if hSat :
          ∃ v : SmtValue,
            __smtx_typeof_value v = T ∧
              __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true then
        Classical.choose hSat
      else
        if hTy' : ∃ v : SmtValue, __smtx_typeof_value v = T then
          Classical.choose hTy'
        else
          SmtValue.NotValue) = T
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_model_eval (__smtx_model_push M s T v) body = SmtValue.Boolean true
  · simpa [hSat] using (Classical.choose_spec hSat).1
  · simpa [hSat, hTy] using Classical.choose_spec hTy

theorem typeof_map_value_shape :
    ∀ m : SmtMap,
      (∃ T U, __smtx_typeof_map_value m = SmtType.Map T U) ∨
        __smtx_typeof_map_value m = SmtType.None
  | SmtMap.default T e => Or.inl ⟨T, __smtx_typeof_value e, rfl⟩
  | SmtMap.cons i e m => by
      by_cases hEq :
          smt_lit_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · simpa [__smtx_typeof_map_value, smt_lit_ite, hEq] using typeof_map_value_shape m
      · exact Or.inr (by simp [__smtx_typeof_map_value, smt_lit_ite, hEq])

theorem typeof_seq_value_shape :
    ∀ ss : SmtSeq,
      (∃ T, __smtx_typeof_seq_value ss = SmtType.Seq T) ∨
        __smtx_typeof_seq_value ss = SmtType.None
  | SmtSeq.empty T => Or.inl ⟨T, rfl⟩
  | SmtSeq.cons v vs => by
      by_cases hEq : smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · simpa [__smtx_typeof_seq_value, smt_lit_ite, hEq] using typeof_seq_value_shape vs
      · exact Or.inr (by simp [__smtx_typeof_seq_value, smt_lit_ite, hEq])

def dt_cons_chain_result : SmtType -> Prop
  | SmtType.None => True
  | SmtType.Datatype _ _ => True
  | SmtType.DtConsType _ U => dt_cons_chain_result U
  | _ => False

theorem typeof_dt_cons_value_rec_chain_result
    (s : smt_lit_String)
    (d0 : SmtDatatype) :
    ∀ d n,
      dt_cons_chain_result (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d n)
  | SmtDatatype.null, n => by
      simp [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, smt_lit_nat_zero => by
      simp [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, smt_lit_nat_zero => by
      simpa [dt_cons_chain_result, __smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_chain_result s d0 (SmtDatatype.sum c d) smt_lit_nat_zero
  | SmtDatatype.sum c d, smt_lit_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_chain_result s d0 d n

theorem typeof_value_dt_cons_type_chain_result :
    ∀ v : SmtValue, ∀ T U : SmtType,
      __smtx_typeof_value v = SmtType.DtConsType T U -> dt_cons_chain_result U
  | SmtValue.NotValue, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Boolean _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Numeral _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Rational _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.Binary w _, T, U, h => by
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | SmtValue.Map m, T, U, h => by
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Seq ss, T, U, h => by
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Char _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.RegLan _, T, U, h => by
      simp [__smtx_typeof_value] at h
  | SmtValue.DtCons s d i, T, U, h => by
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simpa [dt_cons_chain_result] using hShape
  | SmtValue.Apply f v, T, U, h => by
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType A B =>
        cases hNone : smt_lit_Teq A SmtType.None <;>
        cases hEq : smt_lit_Teq A (__smtx_typeof_value v) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        have hShape := typeof_value_dt_cons_type_chain_result f A B hf
        simpa [h, dt_cons_chain_result] using hShape

theorem no_value_of_dt_cons_type_bool
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T SmtType.Bool := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T SmtType.Bool hv
  simp [dt_cons_chain_result] at hShape

theorem no_value_of_dt_cons_type_int
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T SmtType.Int := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T SmtType.Int hv
  simp [dt_cons_chain_result] at hShape

theorem no_value_of_dt_cons_type_real
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T SmtType.Real := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T SmtType.Real hv
  simp [dt_cons_chain_result] at hShape

theorem no_value_of_dt_cons_type_type_ref
    (T : SmtType)
    (s : smt_lit_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T (SmtType.TypeRef s) := by
  intro h
  rcases h with ⟨v, hv⟩
  have hShape := typeof_value_dt_cons_type_chain_result v T (SmtType.TypeRef s) hv
  simp [dt_cons_chain_result] at hShape

theorem typeof_value_ne_type_ref
    (s : smt_lit_String) :
    ∀ v : SmtValue, __smtx_typeof_value v ≠ SmtType.TypeRef s
  | SmtValue.NotValue => by
      simp [__smtx_typeof_value]
  | SmtValue.Boolean _ => by
      simp [__smtx_typeof_value]
  | SmtValue.Numeral _ => by
      simp [__smtx_typeof_value]
  | SmtValue.Rational _ => by
      simp [__smtx_typeof_value]
  | SmtValue.Binary w _ => by
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth]
  | SmtValue.Map m => by
      intro h
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Seq ss => by
      intro h
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | SmtValue.Char _ => by
      simp [__smtx_typeof_value]
  | SmtValue.RegLan _ => by
      simp [__smtx_typeof_value]
  | SmtValue.DtCons s' d i => by
      intro h
      have hShape := typeof_dt_cons_value_rec_chain_result s' d (__smtx_dt_substitute s' d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | SmtValue.Apply f v => by
      intro h
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value v) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_type_ref T s ⟨f, by simpa [h] using hf⟩

theorem no_value_of_type_ref
    (s : smt_lit_String) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef s := by
  intro h
  rcases h with ⟨v, hv⟩
  exact typeof_value_ne_type_ref s v hv

theorem bool_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Bool) :
    ∃ b : smt_lit_Bool, v = SmtValue.Boolean b := by
  cases v with
  | Boolean b =>
      exact ⟨b, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      exfalso
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_bool T ⟨f, by simpa [h] using hf⟩

theorem int_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Int) :
    ∃ n : smt_lit_Int, v = SmtValue.Numeral n := by
  cases v with
  | Numeral n =>
      exact ⟨n, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      exfalso
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_int T ⟨f, by simpa [h] using hf⟩

theorem real_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Real) :
    ∃ q : smt_lit_Rat, v = SmtValue.Rational q := by
  cases v with
  | Rational q =>
      exact ⟨q, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      exfalso
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      exfalso
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exfalso
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_real T ⟨f, by simpa [h] using hf⟩

theorem no_value_of_dt_cons_type_of_non_chain
    (T U : SmtType)
    (hU : ¬ dt_cons_chain_result U) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T U := by
  intro h
  rcases h with ⟨v, hv⟩
  exact hU (typeof_value_dt_cons_type_chain_result v T U hv)

theorem no_value_of_dt_cons_type_seq
    (T U : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T (SmtType.Seq U) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.Seq U) (by
    simp [dt_cons_chain_result])

theorem no_value_of_dt_cons_type_reglan
    (T : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T SmtType.RegLan := by
  exact no_value_of_dt_cons_type_of_non_chain T SmtType.RegLan (by
    simp [dt_cons_chain_result])

theorem no_value_of_dt_cons_type_map
    (T A B : SmtType) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T (SmtType.Map A B) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.Map A B) (by
    simp [dt_cons_chain_result])

theorem no_value_of_dt_cons_type_bitvec
    (T : SmtType)
    (w : smt_lit_Int) :
    ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.DtConsType T (SmtType.BitVec w) := by
  exact no_value_of_dt_cons_type_of_non_chain T (SmtType.BitVec w) (by
    simp [dt_cons_chain_result])

theorem bitvec_value_canonical
    {v : SmtValue}
    {w : smt_lit_Int}
    (h : __smtx_typeof_value v = SmtType.BitVec w) :
    ∃ n : smt_lit_Int, v = SmtValue.Binary w n := by
  cases v with
  | Binary w' n =>
      cases hWidth : smt_lit_zleq 0 w' <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
      cases h
      exact ⟨n, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_bitvec T w ⟨f, by simpa [h] using hf⟩

theorem bitvec_width_nonneg
    {w n : smt_lit_Int}
    (h : __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec w) :
    smt_lit_zleq 0 w = true := by
  cases hWidth : smt_lit_zleq 0 w <;>
    simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  simp

theorem typeof_value_binary_of_nonneg
    (w n : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (SmtValue.Binary w n) = SmtType.BitVec w := by
  simp [__smtx_typeof_value, smt_lit_ite, hWidth]

theorem map_value_canonical
    {v : SmtValue}
    {A B : SmtType}
    (h : __smtx_typeof_value v = SmtType.Map A B) :
    ∃ m : SmtMap, v = SmtValue.Map m := by
  cases v with
  | Map m =>
      exact ⟨m, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType T U =>
        cases hNone : smt_lit_Teq T SmtType.None <;>
        cases hEq : smt_lit_Teq T (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_map T A B ⟨f, by simpa [h] using hf⟩

theorem seq_value_canonical
    {v : SmtValue}
    {T : SmtType}
    (h : __smtx_typeof_value v = SmtType.Seq T) :
    ∃ ss : SmtSeq, v = SmtValue.Seq ss := by
  cases v with
  | Seq ss =>
      exact ⟨ss, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType A B =>
        cases hNone : smt_lit_Teq A SmtType.None <;>
        cases hEq : smt_lit_Teq A (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_seq A T ⟨f, by simpa [h] using hf⟩

def list_typed (T : SmtType) : List SmtValue -> Prop
  | [] => True
  | v :: vs => __smtx_typeof_value v = T ∧ list_typed T vs

theorem list_typed_append
    {T : SmtType} :
    ∀ {xs ys : List SmtValue},
      list_typed T xs ->
        list_typed T ys ->
        list_typed T (xs ++ ys)
  | [], ys, hxs, hys => by
      simpa [list_typed] using hys
  | v :: xs, ys, hxs, hys => by
      rcases hxs with ⟨hv, hxs⟩
      exact ⟨hv, list_typed_append hxs hys⟩

theorem list_typed_take
    {T : SmtType} :
    ∀ n {xs : List SmtValue},
      list_typed T xs ->
        list_typed T (xs.take n)
  | 0, xs, hxs => by
      simp [list_typed]
  | Nat.succ n, [], hxs => by
      simp [list_typed]
  | Nat.succ n, v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      exact ⟨hv, list_typed_take n hxs⟩

theorem list_typed_drop
    {T : SmtType} :
    ∀ n {xs : List SmtValue},
      list_typed T xs ->
        list_typed T (xs.drop n)
  | 0, xs, hxs => by
      simpa using hxs
  | Nat.succ n, [], hxs => by
      simp [list_typed]
  | Nat.succ n, v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      simpa using list_typed_drop n hxs

theorem list_typed_reverse
    {T : SmtType} :
    ∀ {xs : List SmtValue},
      list_typed T xs ->
        list_typed T xs.reverse
  | [], hxs => by
      simp [list_typed]
  | v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      simpa [List.reverse_cons, list_typed, hv] using
        list_typed_append (list_typed_reverse hxs) (by simp [list_typed, hv])

theorem list_typed_extract
    {T : SmtType}
    {xs : List SmtValue}
    (hxs : list_typed T xs)
    (i n : smt_lit_Int) :
    list_typed T (smt_lit_seq_extract xs i n) := by
  unfold smt_lit_seq_extract
  dsimp
  by_cases h :
      (decide (i < 0) || decide (n <= 0) || decide (i >= (↑xs.length : Int))) = true
  · rw [if_pos h]
    simp [list_typed]
  · rw [if_neg h]
    exact
      list_typed_take (Int.toNat (min n (Int.ofNat xs.length - i)))
        (list_typed_drop (Int.toNat i) hxs)

theorem list_typed_replace
    {T : SmtType}
    {xs pat repl : List SmtValue}
    (hxs : list_typed T xs)
    (hrepl : list_typed T repl) :
    list_typed T (smt_lit_seq_replace xs pat repl) := by
  unfold smt_lit_seq_replace
  cases pat with
  | nil =>
      simpa [smt_lit_seq_concat] using list_typed_append hrepl hxs
  | cons p ps =>
      by_cases hIdx : smt_lit_seq_indexof xs (p :: ps) 0 < 0
      · simp [hIdx]
        exact hxs
      · simp [hIdx]
        simpa [List.append_assoc] using
          (list_typed_append
            (list_typed_append
              (list_typed_take (Int.toNat (smt_lit_seq_indexof xs (p :: ps) 0)) hxs)
              hrepl)
            (list_typed_drop (Int.toNat (smt_lit_seq_indexof xs (p :: ps) 0) + (p :: ps).length)
              hxs))

theorem list_typed_replace_all_aux
    {T : SmtType} :
    ∀ fuel (pat repl : List SmtValue) {xs : List SmtValue},
      list_typed T repl ->
        list_typed T xs ->
        list_typed T (smt_lit_seq_replace_all_aux fuel pat repl xs)
  | 0, pat, repl, xs, hrepl, hxs => by
      simp [smt_lit_seq_replace_all_aux]
      exact hxs
  | Nat.succ fuel, [], repl, xs, hrepl, hxs => by
      simp [smt_lit_seq_replace_all_aux]
      exact hxs
  | Nat.succ fuel, p :: ps, repl, xs, hrepl, hxs => by
      by_cases hIdx : smt_lit_seq_indexof xs (p :: ps) 0 < 0
      · simp [smt_lit_seq_replace_all_aux, hIdx]
        exact hxs
      · simp [smt_lit_seq_replace_all_aux, hIdx]
        simpa [List.append_assoc] using
          (list_typed_append
            (list_typed_append
              (list_typed_take (Int.toNat (smt_lit_seq_indexof xs (p :: ps) 0)) hxs)
              hrepl)
            (list_typed_replace_all_aux fuel (p :: ps) repl hrepl
              (list_typed_drop
                (Int.toNat (smt_lit_seq_indexof xs (p :: ps) 0) + (p :: ps).length) hxs)))

theorem list_typed_replace_all
    {T : SmtType}
    {xs pat repl : List SmtValue}
    (hxs : list_typed T xs)
    (hrepl : list_typed T repl) :
    list_typed T (smt_lit_seq_replace_all xs pat repl) := by
  unfold smt_lit_seq_replace_all
  exact list_typed_replace_all_aux (xs.length + 1) pat repl hrepl hxs

theorem list_typed_update
    {T : SmtType}
    {xs ys : List SmtValue}
    (hxs : list_typed T xs)
    (hys : list_typed T ys)
    (i : smt_lit_Int) :
    list_typed T (smt_lit_seq_update xs i ys) := by
  unfold smt_lit_seq_update
  dsimp
  by_cases h : (decide (i < 0) || decide ((↑xs.length : Int) <= i)) = true
  · rw [if_pos h]
    exact hxs
  · rw [if_neg h]
    simpa [List.append_assoc] using
      (list_typed_append
        (list_typed_append (list_typed_take (Int.toNat i) hxs) hys)
        (list_typed_drop (Int.toNat i + 1) hxs))

theorem elem_typeof_seq_value_of_typeof_seq_value :
    ∀ {ss : SmtSeq} {T : SmtType},
      __smtx_typeof_seq_value ss = SmtType.Seq T ->
        __smtx_elem_typeof_seq_value ss = T
  | SmtSeq.empty U, T, h => by
      simpa [__smtx_typeof_seq_value, __smtx_elem_typeof_seq_value] using h
  | SmtSeq.cons v vs, T, h => by
      by_cases hEq : smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · have hvs : __smtx_typeof_seq_value vs = SmtType.Seq T := by
          simpa [__smtx_typeof_seq_value, smt_lit_ite, hEq] using h
        simpa [__smtx_elem_typeof_seq_value] using
          (elem_typeof_seq_value_of_typeof_seq_value hvs)
      · simp [__smtx_typeof_seq_value, smt_lit_ite, hEq] at h

theorem typed_unpack_seq_of_typeof_seq_value :
    ∀ {ss : SmtSeq} {T : SmtType},
      __smtx_typeof_seq_value ss = SmtType.Seq T ->
        list_typed T (smt_lit_unpack_seq ss)
  | SmtSeq.empty U, T, h => by
      simp [smt_lit_unpack_seq, list_typed]
  | SmtSeq.cons v vs, T, h => by
      by_cases hEq : smt_lit_Teq (SmtType.Seq (__smtx_typeof_value v)) (__smtx_typeof_seq_value vs)
      · have hEq' : SmtType.Seq (__smtx_typeof_value v) = __smtx_typeof_seq_value vs := by
          simpa [smt_lit_Teq] using hEq
        have hvs : __smtx_typeof_seq_value vs = SmtType.Seq T := by
          simpa [__smtx_typeof_seq_value, smt_lit_ite, hEq] using h
        rw [hvs] at hEq'
        have hv : __smtx_typeof_value v = T := by
          cases hEq'
          rfl
        exact ⟨hv, typed_unpack_seq_of_typeof_seq_value hvs⟩
      · simp [__smtx_typeof_seq_value, smt_lit_ite, hEq] at h

theorem typeof_seq_value_pack_seq_of_typed
    {T : SmtType} :
    ∀ {xs : List SmtValue},
      list_typed T xs ->
        __smtx_typeof_seq_value (smt_lit_pack_seq T xs) = SmtType.Seq T
  | [], hxs => by
      rfl
  | v :: xs, hxs => by
      rcases hxs with ⟨hv, hxs⟩
      have ih := typeof_seq_value_pack_seq_of_typed hxs
      simp [smt_lit_pack_seq, __smtx_typeof_seq_value, hv, ih, smt_lit_ite, smt_lit_Teq]

theorem char_value_list_typed :
    ∀ cs : List Char, list_typed SmtType.Char (cs.map SmtValue.Char)
  | [] => by
      simp [list_typed]
  | _ :: cs => by
      simp [list_typed, char_value_list_typed cs, __smtx_typeof_value]

theorem char_values_of_string_typed
    (s : smt_lit_String) :
    list_typed SmtType.Char (__smtx_ssm_char_values_of_string s) := by
  simpa [__smtx_ssm_char_values_of_string] using char_value_list_typed s.toList

theorem typeof_pack_string
    (s : smt_lit_String) :
    __smtx_typeof_seq_value (smt_lit_pack_string s) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_seq_value
      (smt_lit_pack_seq SmtType.Char (__smtx_ssm_char_values_of_string s)) =
    SmtType.Seq SmtType.Char
  exact typeof_seq_value_pack_seq_of_typed (char_values_of_string_typed s)

theorem typeof_value_model_eval_string
    (M : SmtModel)
    (s : smt_lit_String) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.String s)) =
      __smtx_typeof (SmtTerm.String s) := by
  change __smtx_typeof_seq_value (smt_lit_pack_string s) = SmtType.Seq SmtType.Char
  exact typeof_pack_string s

theorem map_lookup_typed :
    ∀ {m : SmtMap} {A B : SmtType} {i : SmtValue},
      __smtx_typeof_map_value m = SmtType.Map A B ->
        __smtx_typeof_value i = A ->
        __smtx_typeof_value (__smtx_msm_lookup m i) = B
  | SmtMap.default T e, A, B, i, hMap, hi => by
      cases hMap
      simp [__smtx_msm_lookup]
  | SmtMap.cons j e m, A, B, i, hMap, hi => by
      by_cases hEq :
          smt_lit_Teq (SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · have hm : __smtx_typeof_map_value m = SmtType.Map A B := by
          simpa [__smtx_typeof_map_value, smt_lit_ite, hEq] using hMap
        have hEq' :
            SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e) =
              __smtx_typeof_map_value m := by
          simpa [smt_lit_Teq] using hEq
        have hHead : SmtType.Map (__smtx_typeof_value j) (__smtx_typeof_value e) =
            SmtType.Map A B := hEq'.trans hm
        have hj : __smtx_typeof_value j = A := by
          cases hHead
          rfl
        have he : __smtx_typeof_value e = B := by
          cases hHead
          rfl
        have hRec : __smtx_typeof_value (__smtx_msm_lookup m i) = B :=
          map_lookup_typed hm hi
        by_cases hVeq : smt_lit_veq j i
        · simpa [__smtx_msm_lookup, smt_lit_ite, hVeq] using he
        · simpa [__smtx_msm_lookup, smt_lit_ite, hVeq] using hRec
      · simp [__smtx_typeof_map_value, smt_lit_ite, hEq] at hMap

theorem map_store_typed
    {m : SmtMap}
    {A B : SmtType}
    {i e : SmtValue}
    (hMap : __smtx_typeof_map_value m = SmtType.Map A B)
    (hi : __smtx_typeof_value i = A)
    (he : __smtx_typeof_value e = B) :
    __smtx_typeof_value (SmtValue.Map (SmtMap.cons i e m)) = SmtType.Map A B := by
  simp [__smtx_typeof_value, __smtx_typeof_map_value, hMap, hi, he, smt_lit_ite, smt_lit_Teq]

theorem reglan_value_canonical
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.RegLan) :
    ∃ r : smt_lit_RegLan, v = SmtValue.RegLan r := by
  cases v with
  | RegLan r =>
      exact ⟨r, rfl⟩
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w _ =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨A, B, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨A, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      have hShape := typeof_dt_cons_value_rec_chain_result s d (__smtx_dt_substitute s d d) i
      rw [__smtx_typeof_value] at h
      rw [h] at hShape
      simp [dt_cons_chain_result] at hShape
  | Apply f x =>
      exfalso
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf] at h
      case DtConsType A B =>
        cases hNone : smt_lit_Teq A SmtType.None <;>
        cases hEq : smt_lit_Teq A (__smtx_typeof_value x) <;>
          simp [__smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
        exact no_value_of_dt_cons_type_reglan A ⟨f, by simpa [h] using hf⟩

theorem bool_binop_args_bool_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) SmtType.Bool)
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    __smtx_typeof t1 = SmtType.Bool ∧ __smtx_typeof t2 = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  simp

theorem arith_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2, h1, h2] at ht
  · simp
  · simp

theorem arith_binop_ret_bool_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    (__smtx_typeof t1 = SmtType.Int ∧ __smtx_typeof t2 = SmtType.Int) ∨
      (__smtx_typeof t1 = SmtType.Real ∧ __smtx_typeof t2 = SmtType.Real) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, __smtx_typeof_arith_overload_op_2_ret, h1, h2] at ht
  · simp
  · simp

theorem to_real_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_real t)) :
    __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  · simp
  · simp

theorem real_arg_of_non_none
    {op t : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t) SmtType.Real)
          (if op = SmtTerm.to_int then SmtType.Int else SmtType.Bool) SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h] at ht
  simpa [h] using (show SmtType.Real = SmtType.Real from rfl)

theorem int_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.abs t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  simpa [h] using (show SmtType.Int = SmtType.Int from rfl)

theorem typeof_value_model_eval_eq_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_eq v1 v2) = SmtType.Bool := by
  cases v1 <;> cases v2
  case Seq.Seq ss1 ss2 =>
    cases ss1 <;> cases ss2 <;> simp [__smtx_model_eval_eq, __smtx_typeof_value]
  case Apply.Apply f1 a1 f2 a2 =>
    simp [__smtx_model_eval_eq, __smtx_typeof_value]
  all_goals
    simp [__smtx_model_eval_eq, __smtx_typeof_value]

theorem typeof_value_model_eval_xor_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_xor v1 v2) = SmtType.Bool := by
  unfold __smtx_model_eval_xor
  rcases bool_value_canonical (typeof_value_model_eval_eq_value v1 v2) with ⟨b, hb⟩
  rw [hb]
  rfl

theorem typeof_value_model_eval_distinct_value
    (v1 v2 : SmtValue) :
    __smtx_typeof_value (__smtx_model_eval_distinct v1 v2) = SmtType.Bool := by
  unfold __smtx_model_eval_distinct
  rcases bool_value_canonical (typeof_value_model_eval_eq_value v1 v2) with ⟨b, hb⟩
  rw [hb]
  rfl

theorem ite_args_of_non_none
    {c t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2)) :
    ∃ T : SmtType,
      __smtx_typeof c = SmtType.Bool ∧
        __smtx_typeof t1 = T ∧
        __smtx_typeof t2 = T ∧
        T ≠ SmtType.None := by
  unfold term_has_non_none_type at ht
  let T1 := __smtx_typeof t1
  let T2 := __smtx_typeof t2
  have hBool : __smtx_typeof c = SmtType.Bool := by
    cases hc : __smtx_typeof c <;>
      simp [__smtx_typeof, __smtx_typeof_ite, smt_lit_ite, hc] at ht
    simpa [hc] using (show SmtType.Bool = SmtType.Bool from rfl)
  by_cases hEq : smt_lit_Teq T1 T2 = true
  · have hT : T1 = T2 := by
      simpa [smt_lit_Teq] using hEq
    have hNN : T1 ≠ SmtType.None := by
      simpa [__smtx_typeof, __smtx_typeof_ite, smt_lit_ite, hBool, T1, T2, hEq] using ht
    exact ⟨T1, hBool, rfl, by simpa [T1, T2] using hT.symm, hNN⟩
  · exfalso
    apply ht
    simp [__smtx_typeof, __smtx_typeof_ite, smt_lit_ite, hBool, T1, T2, hEq]

theorem typeof_value_model_eval_ite
    (M : SmtModel)
    (c t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2))
    (hpresc : __smtx_typeof_value (__smtx_model_eval M c) = __smtx_typeof c)
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2) := by
  rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) t1) t2) = T by
    simp [__smtx_typeof, __smtx_typeof_ite, smt_lit_ite, smt_lit_Teq, hc, h1, h2, hT]]
  change __smtx_typeof_value
      (__smtx_model_eval_ite (__smtx_model_eval M c) (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = T
  rcases bool_value_canonical (by simpa [hc] using hpresc) with ⟨b, hb⟩
  rw [hb]
  cases b
  · simpa [__smtx_model_eval_ite, h1, h2] using hpres2
  · simpa [__smtx_model_eval_ite, h1, h2] using hpres1

theorem select_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2)) :
    ∃ A B : SmtType,
      __smtx_typeof t1 = SmtType.Map A B ∧
        __smtx_typeof t2 = A := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      by_cases hEq : smt_lit_Teq A (__smtx_typeof t2)
      · have h2' : A = __smtx_typeof t2 := by
          simpa [smt_lit_Teq] using hEq
        exact ⟨A, B, rfl, h2'.symm⟩
      · exfalso
        exact ht (by simp [__smtx_typeof, __smtx_typeof_select, smt_lit_ite, h1, hEq])
  | _ =>
      exfalso
      exact ht (by simp [__smtx_typeof, __smtx_typeof_select, smt_lit_ite, h1])

theorem store_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3)) :
    ∃ A B : SmtType,
      __smtx_typeof t1 = SmtType.Map A B ∧
        __smtx_typeof t2 = A ∧
        __smtx_typeof t3 = B := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Map A B =>
      by_cases hEq1 : smt_lit_Teq A (__smtx_typeof t2)
      · by_cases hEq2 : smt_lit_Teq B (__smtx_typeof t3)
        · have h2' : A = __smtx_typeof t2 := by
            simpa [smt_lit_Teq] using hEq1
          have h3' : B = __smtx_typeof t3 := by
            simpa [smt_lit_Teq] using hEq2
          exact ⟨A, B, rfl, h2'.symm, h3'.symm⟩
        · exfalso
          exact ht (by
            simp [__smtx_typeof, __smtx_typeof_store, smt_lit_ite, h1, hEq1, hEq2])
      · exfalso
        exact ht (by
          simp [__smtx_typeof, __smtx_typeof_store, smt_lit_ite, h1, hEq1])
  | _ =>
      exfalso
      exact ht (by simp [__smtx_typeof, __smtx_typeof_store, smt_lit_ite, h1])

theorem typeof_value_model_eval_select
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2) := by
  rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select t1) t2) = B by
    simp [__smtx_typeof, __smtx_typeof_select, smt_lit_ite, smt_lit_Teq, h1, h2]]
  change
    __smtx_typeof_value
      (__smtx_model_eval_select (__smtx_model_eval M t1) (__smtx_model_eval M t2)) = B
  rcases map_value_canonical (A := A) (B := B) (by simpa [h1] using hpres1) with ⟨m, hm⟩
  rw [hm]
  simpa [__smtx_model_eval_select, __smtx_map_select] using
    map_lookup_typed (m := m) (A := A) (B := B) (i := __smtx_model_eval M t2)
      (by simpa [hm, h1] using hpres1)
      (by simpa [h2] using hpres2)

theorem typeof_value_model_eval_store
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht : term_has_non_none_type
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3) := by
  rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store t1) t2) t3) =
        SmtType.Map A B by
    simp [__smtx_typeof, __smtx_typeof_store, smt_lit_ite, smt_lit_Teq, h1, h2, h3]]
  change
    __smtx_typeof_value
      (__smtx_model_eval_store (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Map A B
  rcases map_value_canonical (A := A) (B := B) (by simpa [h1] using hpres1) with ⟨m, hm⟩
  rw [hm]
  simpa [__smtx_model_eval_store, __smtx_map_store] using
    map_store_typed (m := m) (A := A) (B := B)
      (i := __smtx_model_eval M t2) (e := __smtx_model_eval M t3)
      (by simpa [hm, h1] using hpres1)
      (by simpa [h2] using hpres2)
      (by simpa [h3] using hpres3)

theorem bv_concat_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2)) :
    ∃ w1 w2 : smt_lit_Int,
      __smtx_typeof t1 = SmtType.BitVec w1 ∧
        __smtx_typeof t2 = SmtType.BitVec w2 := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          exact ⟨w1, w2, rfl, rfl⟩
      | _ =>
          simp [__smtx_typeof, __smtx_typeof_concat, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof, __smtx_typeof_concat, h1, h2] at ht

theorem extract_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3)) :
    ∃ i j w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        t2 = SmtTerm.Numeral j ∧
        __smtx_typeof t3 = SmtType.BitVec w ∧
        smt_lit_zleq 0 j = true ∧
        smt_lit_zleq j i = true ∧
        smt_lit_zlt i w = true := by
  unfold term_has_non_none_type at ht
  cases t1 <;> cases t2 <;> cases h3 : __smtx_typeof t3 <;>
    simp [__smtx_typeof, __smtx_typeof_extract, smt_lit_ite, h3] at ht
  case Numeral.Numeral i j =>
    rename_i i j w
    by_cases hj0 : smt_lit_zleq 0 j = true
    · by_cases hji : smt_lit_zleq j i = true
      · by_cases hiw : smt_lit_zlt i w = true
        · exact ⟨i, j, w, rfl, rfl, h3, hj0, hji, hiw⟩
        · exfalso
          exact ht (by
            simp [__smtx_typeof, __smtx_typeof_extract, smt_lit_ite, h3, hj0, hji, hiw])
      · exfalso
        exact ht (by
          simp [__smtx_typeof, __smtx_typeof_extract, smt_lit_ite, h3, hj0, hji])
    · exfalso
      exact ht (by
        simp [__smtx_typeof, __smtx_typeof_extract, smt_lit_ite, h3, hj0])

theorem zero_extend_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2)) :
    ∃ i w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        smt_lit_zleq 0 i = true := by
  unfold term_has_non_none_type at ht
  cases t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_zero_extend, smt_lit_ite, h2] at ht
  case Numeral.Numeral i =>
    rename_i i w
    by_cases hi0 : smt_lit_zleq 0 i = true
    · exact ⟨i, w, rfl, h2, hi0⟩
    · exfalso
      exact ht (by
        simp [__smtx_typeof, __smtx_typeof_zero_extend, smt_lit_ite, h2, hi0])

theorem sign_extend_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2)) :
    ∃ i w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        smt_lit_zleq 0 i = true := by
  unfold term_has_non_none_type at ht
  cases t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_sign_extend, smt_lit_ite, h2] at ht
  case Numeral.Numeral i =>
    rename_i i w
    by_cases hi0 : smt_lit_zleq 0 i = true
    · exact ⟨i, w, rfl, h2, hi0⟩
    · exfalso
      exact ht (by
        simp [__smtx_typeof, __smtx_typeof_sign_extend, smt_lit_ite, h2, hi0])

theorem int_to_bv_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2)) :
    ∃ i : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.Int ∧
        smt_lit_zleq 0 i = true := by
  unfold term_has_non_none_type at ht
  cases t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_int_to_bv, smt_lit_ite, h2] at ht
  case Numeral.Numeral i =>
    by_cases hi0 : smt_lit_zleq 0 i = true
    · exact ⟨i, rfl, h2, hi0⟩
    · exfalso
      exact ht (by
        simp [__smtx_typeof, __smtx_typeof_int_to_bv, smt_lit_ite, h2, hi0])

theorem bv_unop_arg_of_non_none
    {op t : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        __smtx_typeof_bv_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    ∃ w : smt_lit_Int, __smtx_typeof t = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | BitVec w =>
      exact ⟨w, rfl⟩
  | _ =>
      simp [hTy, __smtx_typeof_bv_op_1, h] at ht

theorem bv_unop_ret_arg_of_non_none
    {op t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        __smtx_typeof_bv_op_1_ret (__smtx_typeof t) ret)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    ∃ w : smt_lit_Int, __smtx_typeof t = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | BitVec w =>
      exact ⟨w, rfl⟩
  | _ =>
      simp [hTy, __smtx_typeof_bv_op_1_ret, h] at ht

theorem bv_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    ∃ w : smt_lit_Int,
      __smtx_typeof t1 = SmtType.BitVec w ∧
        __smtx_typeof t2 = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          by_cases hEq : smt_lit_zeq w1 w2 = true
          · have hw : w1 = w2 := by
              simpa [SmtEval.smt_lit_zeq] using hEq
            cases hw
            exact ⟨w1, rfl, rfl⟩
          · exfalso
            exact ht (by
              simp [hTy, __smtx_typeof_bv_op_2, smt_lit_ite, h1, h2, hEq])
      | _ =>
          simp [hTy, __smtx_typeof_bv_op_2, smt_lit_ite, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_bv_op_2, smt_lit_ite, h1, h2] at ht

theorem bv_binop_ret_args_of_non_none
    {op t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    ∃ w : smt_lit_Int,
      __smtx_typeof t1 = SmtType.BitVec w ∧
        __smtx_typeof t2 = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          by_cases hEq : smt_lit_zeq w1 w2 = true
          · have hw : w1 = w2 := by
              simpa [SmtEval.smt_lit_zeq] using hEq
            cases hw
            exact ⟨w1, rfl, rfl⟩
          · exfalso
            exact ht (by
              simp [hTy, __smtx_typeof_bv_op_2_ret, smt_lit_ite, h1, h2, hEq])
      | _ =>
          simp [hTy, __smtx_typeof_bv_op_2_ret, smt_lit_ite, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_bv_op_2_ret, smt_lit_ite, h1, h2] at ht

theorem typeof_value_model_eval_concat
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2) := by
  rcases bv_concat_args_of_non_none ht with ⟨w1, w2, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2) =
      SmtType.BitVec (smt_lit_zplus w1 w2) by
    simp [__smtx_typeof, __smtx_typeof_concat, h1, h2]]
  change __smtx_typeof_value
      (__smtx_model_eval_concat (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus w1 w2)
  rcases bitvec_value_canonical (by simpa [h1] using hpres1) with ⟨n1, hv1⟩
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hv2⟩
  rw [hv1, hv2]
  have hWidth1 : smt_lit_zleq 0 w1 = true := by
    exact bitvec_width_nonneg (by simpa [h1, hv1] using hpres1)
  have hWidth2 : smt_lit_zleq 0 w2 = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv2] using hpres2)
  have hw1 : 0 <= w1 := by
    simpa [SmtEval.smt_lit_zleq] using hWidth1
  have hw2 : 0 <= w2 := by
    simpa [SmtEval.smt_lit_zleq] using hWidth2
  have hWidth : smt_lit_zleq 0 (smt_lit_zplus w1 w2) = true := by
    have hAdd : 0 <= w1 + w2 := Int.add_nonneg hw1 hw2
    simpa [SmtEval.smt_lit_zleq, SmtEval.smt_lit_zplus] using hAdd
  simpa [__smtx_model_eval_concat] using
    typeof_value_binary_of_nonneg (smt_lit_zplus w1 w2)
      (smt_lit_mod_total (smt_lit_binary_concat w1 n1 w2 n2)
        (smt_lit_int_pow2 (smt_lit_zplus w1 w2))) hWidth

theorem typeof_value_model_eval_extract
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht : term_has_non_none_type
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3))
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3) := by
  rcases extract_args_of_non_none ht with ⟨i, j, w, h1, h2, h3, hj0, hji, hiw⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3) =
        SmtType.BitVec (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j)) by
    simp [__smtx_typeof, __smtx_typeof_extract, smt_lit_ite, h1, h2, h3, hj0, hji, hiw,
      SmtEval.smt_lit_zplus, SmtEval.smt_lit_zneg, add_assoc, add_comm, add_left_comm]]
  change __smtx_typeof_value
      (__smtx_model_eval_extract (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) =
    SmtType.BitVec (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j))
  rw [h1, h2]
  change __smtx_typeof_value
      (__smtx_model_eval_extract (SmtValue.Numeral i) (SmtValue.Numeral j)
        (__smtx_model_eval M t3)) =
    SmtType.BitVec (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j))
  rcases bitvec_value_canonical (by simpa [h3] using hpres3) with ⟨n, hv⟩
  rw [hv]
  have hji' : j <= i := by
    simpa [SmtEval.smt_lit_zleq] using hji
  have hWidthInt : 0 <= (i + 1) + -j := by
    have hsub : 0 <= i - j := sub_nonneg.mpr hji'
    have hWidth' : 0 <= (i - j) + 1 := Int.add_nonneg hsub (by decide)
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hWidth'
  have hWidth : smt_lit_zleq 0 (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j)) = true := by
    simpa [SmtEval.smt_lit_zleq, SmtEval.smt_lit_zplus, SmtEval.smt_lit_zneg,
      add_assoc, add_comm, add_left_comm] using hWidthInt
  simpa [__smtx_model_eval_extract] using
    typeof_value_binary_of_nonneg (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j))
      (smt_lit_mod_total (smt_lit_binary_extract w n i j)
        (smt_lit_int_pow2 (smt_lit_zplus (smt_lit_zplus i 1) (smt_lit_zneg j)))) hWidth

theorem typeof_value_model_eval_bv_unop
    (M : SmtModel)
    (op : SmtTerm)
    (eval : SmtValue -> SmtValue)
    (t : SmtTerm)
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        __smtx_typeof_bv_op_1 (__smtx_typeof t))
    (hEvalTerm :
      __smtx_model_eval M (SmtTerm.Apply op t) = eval (__smtx_model_eval M t))
    (ht : term_has_non_none_type (SmtTerm.Apply op t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t)
    (hEvalTy :
      ∀ w n, smt_lit_zleq 0 w = true ->
        __smtx_typeof_value (eval (SmtValue.Binary w n)) = SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply op t)) =
      __smtx_typeof (SmtTerm.Apply op t) := by
  rcases bv_unop_arg_of_non_none hTy ht with ⟨w, hArg⟩
  rw [hEvalTerm]
  rw [show __smtx_typeof (SmtTerm.Apply op t) = SmtType.BitVec w by
    simp [hTy, __smtx_typeof_bv_op_1, hArg]]
  rcases bitvec_value_canonical (by simpa [hArg] using hpres) with ⟨n, hv⟩
  rw [hv]
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [hArg, hv] using hpres)
  simpa using hEvalTy w n hWidth

theorem typeof_value_model_eval_bv_unop_ret
    (M : SmtModel)
    (op : SmtTerm)
    (eval : SmtValue -> SmtValue)
    (ret : SmtType)
    (t : SmtTerm)
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        __smtx_typeof_bv_op_1_ret (__smtx_typeof t) ret)
    (hEvalTerm :
      __smtx_model_eval M (SmtTerm.Apply op t) = eval (__smtx_model_eval M t))
    (ht : term_has_non_none_type (SmtTerm.Apply op t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t)
    (hEvalTy :
      ∀ w n, smt_lit_zleq 0 w = true ->
        __smtx_typeof_value (eval (SmtValue.Binary w n)) = ret) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply op t)) =
      __smtx_typeof (SmtTerm.Apply op t) := by
  rcases bv_unop_ret_arg_of_non_none hTy ht with ⟨w, hArg⟩
  rw [hEvalTerm]
  rw [show __smtx_typeof (SmtTerm.Apply op t) = ret by
    simp [hTy, __smtx_typeof_bv_op_1_ret, hArg]]
  rcases bitvec_value_canonical (by simpa [hArg] using hpres) with ⟨n, hv⟩
  rw [hv]
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [hArg, hv] using hpres)
  simpa using hEvalTy w n hWidth

theorem typeof_value_model_eval_bv_binop
    (M : SmtModel)
    (op : SmtTerm)
    (eval : SmtValue -> SmtValue -> SmtValue)
    (t1 t2 : SmtTerm)
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (hEvalTerm :
      __smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        eval (__smtx_model_eval M t1) (__smtx_model_eval M t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hEvalTy :
      ∀ w n1 n2, smt_lit_zleq 0 w = true ->
        __smtx_typeof_value (eval (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
          SmtType.BitVec w) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) := by
  rcases bv_binop_args_of_non_none hTy ht with ⟨w, h1, h2⟩
  rw [hEvalTerm]
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) = SmtType.BitVec w by
    simp [hTy, __smtx_typeof_bv_op_2, smt_lit_ite, SmtEval.smt_lit_zeq, h1, h2]]
  rcases bitvec_value_canonical (by simpa [h1] using hpres1) with ⟨n1, hv1⟩
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hv2⟩
  rw [hv1, hv2]
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h1, hv1] using hpres1)
  simpa using hEvalTy w n1 n2 hWidth

theorem typeof_value_model_eval_bv_binop_ret
    (M : SmtModel)
    (op : SmtTerm)
    (eval : SmtValue -> SmtValue -> SmtValue)
    (ret : SmtType)
    (t1 t2 : SmtTerm)
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (hEvalTerm :
      __smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        eval (__smtx_model_eval M t1) (__smtx_model_eval M t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hEvalTy :
      ∀ w n1 n2, smt_lit_zleq 0 w = true ->
        __smtx_typeof_value (eval (SmtValue.Binary w n1) (SmtValue.Binary w n2)) = ret) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) := by
  rcases bv_binop_ret_args_of_non_none hTy ht with ⟨w, h1, h2⟩
  rw [hEvalTerm]
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) = ret by
    simp [hTy, __smtx_typeof_bv_op_2_ret, smt_lit_ite, SmtEval.smt_lit_zeq, h1, h2]]
  rcases bitvec_value_canonical (by simpa [h1] using hpres1) with ⟨n1, hv1⟩
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hv2⟩
  rw [hv1, hv2]
  have hWidth : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h1, hv1] using hpres1)
  simpa using hEvalTy w n1 n2 hWidth

theorem typeof_value_model_eval_bvcomp_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvcomp (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.BitVec 1 := by
  unfold __smtx_model_eval_bvcomp
  have hEq :
      __smtx_typeof_value (__smtx_model_eval_eq (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
        SmtType.Bool := by
    exact typeof_value_model_eval_eq_value _ _
  rcases bool_value_canonical hEq with ⟨b, hb⟩
  rw [hb]
  cases b <;> simp [__smtx_model_eval_ite, __smtx_typeof_value, smt_lit_ite, SmtEval.smt_lit_zleq]

theorem typeof_value_model_eval_bvugt_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvugt (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  simp [__smtx_model_eval_bvugt, __smtx_typeof_value]

theorem typeof_value_model_eval_bvuge_value
    (w n1 n2 : smt_lit_Int)
    (hWidth : smt_lit_zleq 0 w = true) :
    __smtx_typeof_value (__smtx_model_eval_bvuge (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  unfold __smtx_model_eval_bvuge
  have h1 :
      __smtx_typeof_value (__smtx_model_eval_bvugt (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
        SmtType.Bool := by
    exact typeof_value_model_eval_bvugt_value w n1 n2 hWidth
  have h2 :
      __smtx_typeof_value (__smtx_model_eval_eq (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
        SmtType.Bool := by
    exact typeof_value_model_eval_eq_value _ _
  rcases bool_value_canonical h1 with ⟨b1, hb1⟩
  rcases bool_value_canonical h2 with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_or, __smtx_typeof_value]

theorem typeof_value_model_eval_bvnot
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.bvnot t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.bvnot t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.bvnot t) := by
  exact typeof_value_model_eval_bv_unop M SmtTerm.bvnot __smtx_model_eval_bvnot t
    rfl rfl ht hpres (fun w n hWidth => by
      simpa [__smtx_model_eval_bvnot] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_binary_not w n) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvand
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvand t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvand __smtx_model_eval_bvand t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvand] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_binary_and w n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvor t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvor __smtx_model_eval_bvor t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvor] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_binary_or w n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvnand
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnand t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvnand __smtx_model_eval_bvnand t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvnand, __smtx_model_eval_bvnot, __smtx_model_eval_bvand] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_binary_not w
              (smt_lit_mod_total (smt_lit_binary_and w n1 n2) (smt_lit_int_pow2 w)))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvnor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvnor t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvnor __smtx_model_eval_bvnor t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvnor, __smtx_model_eval_bvnot, __smtx_model_eval_bvor] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_binary_not w
              (smt_lit_mod_total (smt_lit_binary_or w n1 n2) (smt_lit_int_pow2 w)))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvxor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxor t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvxor __smtx_model_eval_bvxor t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvxor] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_binary_xor w n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvxnor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvxnor t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvxnor __smtx_model_eval_bvxnor t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvxnor, __smtx_model_eval_bvnot, __smtx_model_eval_bvxor] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_binary_not w
              (smt_lit_mod_total (smt_lit_binary_xor w n1 n2) (smt_lit_int_pow2 w)))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvcomp
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvcomp __smtx_model_eval_bvcomp
    (SmtType.BitVec 1) t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvcomp_value w n1 n2)

theorem typeof_value_model_eval_bvneg
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.bvneg t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.bvneg t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.bvneg t) := by
  exact typeof_value_model_eval_bv_unop M SmtTerm.bvneg __smtx_model_eval_bvneg t
    rfl rfl ht hpres (fun w n hWidth => by
      simpa [__smtx_model_eval_bvneg] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_zneg n) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvadd
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvadd t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvadd __smtx_model_eval_bvadd t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvadd] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_zplus n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvmul
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvmul t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvmul __smtx_model_eval_bvmul t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvmul] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_zmult n1 n2) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvudiv
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvudiv t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvudiv __smtx_model_eval_bvudiv t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvudiv] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_ite (smt_lit_zeq n2 0) (smt_lit_binary_max w) (smt_lit_div_total n1 n2))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvurem
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvurem t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvurem __smtx_model_eval_bvurem t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvurem] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_ite (smt_lit_zeq n2 0) n1 (smt_lit_mod_total n1 n2))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvsub
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsub t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvsub __smtx_model_eval_bvsub t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvsub, __smtx_model_eval_bvadd, __smtx_model_eval_bvneg] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total
            (smt_lit_zplus n1
              (smt_lit_mod_total (smt_lit_zneg n2) (smt_lit_int_pow2 w)))
            (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvult
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvult __smtx_model_eval_bvult
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvult, __smtx_model_eval_bvugt, __smtx_typeof_value] using
        typeof_value_model_eval_bvugt_value w n2 n1 hWidth)

theorem typeof_value_model_eval_bvule
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvule t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvule __smtx_model_eval_bvule
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvule, __smtx_model_eval_bvuge] using
        typeof_value_model_eval_bvuge_value w n2 n1 hWidth)

theorem typeof_value_model_eval_bvugt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvugt t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvugt __smtx_model_eval_bvugt
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvugt_value

theorem typeof_value_model_eval_bvuge
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuge t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvuge __smtx_model_eval_bvuge
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 typeof_value_model_eval_bvuge_value

theorem typeof_value_model_eval_bvsgt_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvsgt (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  simp [__smtx_model_eval_bvsgt, __smtx_model_eval__, __smtx_model_eval_extract,
    __smtx_model_eval_eq, __smtx_model_eval_not, __smtx_model_eval_and,
    __smtx_model_eval_or, __smtx_model_eval_bvugt, __smtx_typeof_value,
    SmtEval.smt_lit_zplus, SmtEval.smt_lit_zneg]

theorem typeof_value_model_eval_bvsge_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvsge (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  unfold __smtx_model_eval_bvsge
  rcases bool_value_canonical (typeof_value_model_eval_bvsgt_value w n1 n2) with ⟨b1, hb1⟩
  rcases bool_value_canonical (typeof_value_model_eval_eq_value
      (SmtValue.Binary w n1) (SmtValue.Binary w n2)) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  simp [__smtx_model_eval_or, __smtx_typeof_value]

theorem typeof_value_model_eval_bvslt_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvslt (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  simpa [__smtx_model_eval_bvslt] using typeof_value_model_eval_bvsgt_value w n2 n1

theorem typeof_value_model_eval_bvsle_value
    (w n1 n2 : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval_bvsle (SmtValue.Binary w n1) (SmtValue.Binary w n2)) =
      SmtType.Bool := by
  simpa [__smtx_model_eval_bvsle] using typeof_value_model_eval_bvsge_value w n2 n1

theorem typeof_value_model_eval_bvslt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvslt __smtx_model_eval_bvslt
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvslt_value w n1 n2)

theorem typeof_value_model_eval_bvsle
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsle t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsle __smtx_model_eval_bvsle
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvsle_value w n1 n2)

theorem typeof_value_model_eval_bvsgt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsgt t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsgt __smtx_model_eval_bvsgt
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvsgt_value w n1 n2)

theorem typeof_value_model_eval_bvsge
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsge t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsge __smtx_model_eval_bvsge
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 _ => by
      exact typeof_value_model_eval_bvsge_value w n1 n2)

theorem typeof_value_model_eval_ubv_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.ubv_to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.ubv_to_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.ubv_to_int t) := by
  exact typeof_value_model_eval_bv_unop_ret M SmtTerm.ubv_to_int __smtx_model_eval_ubv_to_int
    SmtType.Int t rfl rfl ht hpres (fun w n hWidth => by
      simp [__smtx_model_eval_ubv_to_int, __smtx_typeof_value])

theorem typeof_value_model_eval_sbv_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.sbv_to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.sbv_to_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.sbv_to_int t) := by
  exact typeof_value_model_eval_bv_unop_ret M SmtTerm.sbv_to_int __smtx_model_eval_sbv_to_int
    SmtType.Int t rfl rfl ht hpres (fun w n hWidth => by
      simp [__smtx_model_eval_sbv_to_int, __smtx_typeof_value])

theorem typeof_value_model_eval_bvshl
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvshl t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvshl __smtx_model_eval_bvshl t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvshl] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_zmult n1 (smt_lit_int_pow2 n2)) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvlshr
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvlshr t1) t2) := by
  exact typeof_value_model_eval_bv_binop M SmtTerm.bvlshr __smtx_model_eval_bvlshr t1 t2
    rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvlshr] using
        typeof_value_binary_of_nonneg w
          (smt_lit_mod_total (smt_lit_div_total n1 (smt_lit_int_pow2 n2)) (smt_lit_int_pow2 w)) hWidth)

theorem typeof_value_model_eval_bvuaddo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvuaddo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvuaddo __smtx_model_eval_bvuaddo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun _ _ _ _ => by
      simp [__smtx_model_eval_bvuaddo, __smtx_typeof_value])

theorem typeof_value_model_eval_bvnego
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.bvnego t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.bvnego t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.bvnego t) := by
  exact typeof_value_model_eval_bv_unop_ret M SmtTerm.bvnego __smtx_model_eval_bvnego
    SmtType.Bool t rfl rfl ht hpres (fun _ _ _ => by
      simp [__smtx_model_eval_bvnego, __smtx_typeof_value])

theorem typeof_value_model_eval_bvsaddo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsaddo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsaddo __smtx_model_eval_bvsaddo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun _ _ _ _ => by
      simp [__smtx_model_eval_bvsaddo, __smtx_typeof_value])

theorem typeof_value_model_eval_bvumulo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvumulo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvumulo __smtx_model_eval_bvumulo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun _ _ _ _ => by
      simp [__smtx_model_eval_bvumulo, __smtx_typeof_value])

theorem typeof_value_model_eval_bvsmulo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvsmulo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvsmulo __smtx_model_eval_bvsmulo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun _ _ _ _ => by
      simp [__smtx_model_eval_bvsmulo, __smtx_typeof_value])

theorem typeof_value_model_eval_bvusubo
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvusubo t1) t2) := by
  exact typeof_value_model_eval_bv_binop_ret M SmtTerm.bvusubo __smtx_model_eval_bvusubo
    SmtType.Bool t1 t2 rfl rfl ht hpres1 hpres2 (fun w n1 n2 hWidth => by
      simpa [__smtx_model_eval_bvusubo, __smtx_model_eval_bvult] using
        typeof_value_model_eval_bvugt_value w n2 n1 hWidth)

theorem typeof_value_model_eval_zero_extend
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2) := by
  rcases zero_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2) =
      SmtType.BitVec (smt_lit_zplus i w) by
    simp [__smtx_typeof, __smtx_typeof_zero_extend, smt_lit_ite, h1, h2, hi0]]
  change __smtx_typeof_value
      (__smtx_model_eval_zero_extend (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus i w)
  rw [h1]
  change __smtx_typeof_value
      (__smtx_model_eval_zero_extend (SmtValue.Numeral i) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus i w)
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv]
  have hi : 0 <= i := by
    simpa [SmtEval.smt_lit_zleq] using hi0
  have hw0 : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  have hw : 0 <= w := by
    simpa [SmtEval.smt_lit_zleq] using hw0
  have hWidth : smt_lit_zleq 0 (smt_lit_zplus i w) = true := by
    have hAdd : 0 <= i + w := Int.add_nonneg hi hw
    simpa [SmtEval.smt_lit_zleq, SmtEval.smt_lit_zplus] using hAdd
  simpa [__smtx_model_eval_zero_extend] using
    typeof_value_binary_of_nonneg (smt_lit_zplus i w) n hWidth

theorem typeof_value_model_eval_sign_extend
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2) := by
  rcases sign_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2) =
      SmtType.BitVec (smt_lit_zplus i w) by
    simp [__smtx_typeof, __smtx_typeof_sign_extend, smt_lit_ite, h1, h2, hi0]]
  change __smtx_typeof_value
      (__smtx_model_eval_sign_extend (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus i w)
  rw [h1]
  change __smtx_typeof_value
      (__smtx_model_eval_sign_extend (SmtValue.Numeral i) (__smtx_model_eval M t2)) =
    SmtType.BitVec (smt_lit_zplus i w)
  rcases bitvec_value_canonical (by simpa [h2] using hpres2) with ⟨n, hv⟩
  rw [hv]
  have hi : 0 <= i := by
    simpa [SmtEval.smt_lit_zleq] using hi0
  have hw0 : smt_lit_zleq 0 w = true := by
    exact bitvec_width_nonneg (by simpa [h2, hv] using hpres2)
  have hw : 0 <= w := by
    simpa [SmtEval.smt_lit_zleq] using hw0
  have hWidth : smt_lit_zleq 0 (smt_lit_zplus i w) = true := by
    have hAdd : 0 <= i + w := Int.add_nonneg hi hw
    simpa [SmtEval.smt_lit_zleq, SmtEval.smt_lit_zplus] using hAdd
  simpa [__smtx_model_eval_sign_extend] using
    typeof_value_binary_of_nonneg (smt_lit_zplus i w)
      (smt_lit_mod_total (smt_lit_binary_uts w n) (smt_lit_int_pow2 (smt_lit_zplus i w))) hWidth

theorem typeof_value_model_eval_int_to_bv
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2))
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2) := by
  rcases int_to_bv_args_of_non_none ht with ⟨i, h1, h2, hi0⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2) =
      SmtType.BitVec i by
    simp [__smtx_typeof, __smtx_typeof_int_to_bv, smt_lit_ite, h1, h2, hi0]]
  change __smtx_typeof_value
      (__smtx_model_eval_int_to_bv (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.BitVec i
  rw [h1]
  change __smtx_typeof_value
      (__smtx_model_eval_int_to_bv (SmtValue.Numeral i) (__smtx_model_eval M t2)) =
    SmtType.BitVec i
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n, hn⟩
  rw [hn]
  simpa [__smtx_model_eval_int_to_bv] using
    typeof_value_binary_of_nonneg i (smt_lit_mod_total n (smt_lit_int_pow2 i)) hi0

theorem eq_term_typeof_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2) = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, h1, h2] at ht ⊢
  all_goals
    first | exact ht

theorem typeof_value_model_eval_not
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.not t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.not t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.not t) := by
  have hArg : __smtx_typeof t = SmtType.Bool := by
    unfold term_has_non_none_type at ht
    cases h : __smtx_typeof t <;>
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
    simpa [h] using (show SmtType.Bool = SmtType.Bool from rfl)
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.not t) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_not (__smtx_model_eval M t)) = SmtType.Bool
  rcases bool_value_canonical (by simpa [hArg] using hpres) with ⟨b, hb⟩
  rw [hb]
  rfl

theorem typeof_value_model_eval_or
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_or (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  rfl

theorem typeof_value_model_eval_and
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_and (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  rfl

theorem typeof_value_model_eval_imp
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_imp (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
    SmtType.Bool
  rcases bool_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨b1, hb1⟩
  rcases bool_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨b2, hb2⟩
  rw [hb1, hb2]
  rfl

theorem typeof_value_model_eval_eq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq t1) t2) := by
  rw [eq_term_typeof_of_non_none ht]
  simpa using typeof_value_model_eval_eq_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem typeof_value_model_eval_xor
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2) := by
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.xor) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor t1) t2) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  simpa using typeof_value_model_eval_xor_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem typeof_value_model_eval_distinct
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct t1) t2) := by
  rw [eq_term_typeof_of_non_none ht]
  simpa using typeof_value_model_eval_distinct_value (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem typeof_value_model_eval_plus
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.plus) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2) = SmtType.Int by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_plus (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_plus (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_neg
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2) = SmtType.Int by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval__ (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval__ (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_mult
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2) := by
  rcases arith_binop_args_of_non_none (op := SmtTerm.mult) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2) = SmtType.Int by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_mult (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Int
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult t1) t2) = SmtType.Real by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_mult (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Real
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_lt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_lt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_lt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_leq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_leq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_leq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_gt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_gt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_gt (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_geq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2) := by
  rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq) rfl ht with hArgs | hArgs
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_geq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases int_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨n1, hn1⟩
    rcases int_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨n2, hn2⟩
    rw [hn1, hn2]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq t1) t2) = SmtType.Bool by
      simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]]
    change __smtx_typeof_value (__smtx_model_eval_geq (__smtx_model_eval M t1) (__smtx_model_eval M t2)) =
      SmtType.Bool
    rcases real_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨q1, hq1⟩
    rcases real_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨q2, hq2⟩
    rw [hq1, hq2]
    rfl

theorem typeof_value_model_eval_to_real
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_real t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.to_real t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.to_real t) := by
  rcases to_real_arg_of_non_none ht with hArg | hArg
  · rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.to_real t) = SmtType.Real by
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
    change __smtx_typeof_value (__smtx_model_eval_to_real (__smtx_model_eval M t)) = SmtType.Real
    rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
    rw [hn]
    rfl
  · rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.to_real t) = SmtType.Real by
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
    change __smtx_typeof_value (__smtx_model_eval_to_real (__smtx_model_eval M t)) = SmtType.Real
    rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
    rw [hq]
    rfl

theorem typeof_value_model_eval_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.to_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.to_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.to_int t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_to_int (__smtx_model_eval M t)) = SmtType.Int
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  rfl

theorem typeof_value_model_eval_is_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.is_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.is_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.is_int t) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.is_int t) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_is_int (__smtx_model_eval M t)) = SmtType.Bool
  rcases real_value_canonical (by simpa [hArg] using hpres) with ⟨q, hq⟩
  rw [hq]
  simpa [__smtx_model_eval_is_int, __smtx_model_eval_to_int, __smtx_model_eval_to_real] using
    typeof_value_model_eval_eq_value
      (SmtValue.Rational (smt_lit_to_real (smt_lit_to_int q))) (SmtValue.Rational q)

theorem typeof_value_model_eval_abs
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.abs t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.abs t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.abs t) := by
  have hArg : __smtx_typeof t = SmtType.Int := int_arg_of_non_none ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.abs t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_abs (__smtx_model_eval M t)) = SmtType.Int
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  cases hlt : smt_lit_zlt n 0 <;>
    simp [__smtx_model_eval_abs, __smtx_model_eval_lt, __smtx_model_eval_ite,
      __smtx_model_eval__, __smtx_typeof_value, hlt]

theorem int_ret_arg_of_non_none
    {op t : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t) SmtType.Int) R SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    __smtx_typeof t = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h] at ht
  simpa [h] using (show SmtType.Int = SmtType.Int from rfl)

theorem seq_arg_of_non_none
    {op t : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        __smtx_typeof_seq_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    ∃ T : SmtType, __smtx_typeof t = SmtType.Seq T := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | Seq T =>
      exact ⟨T, rfl⟩
  | _ =>
      simp [hTy, __smtx_typeof_seq_op_1, h] at ht

theorem seq_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_seq_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧ __smtx_typeof t2 = SmtType.Seq T := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Seq U =>
          have hEq : T = U := by
            simpa [hTy, __smtx_typeof_seq_op_2, smt_lit_ite, smt_lit_Teq, h1, h2] using ht
          subst hEq
          exact ⟨T, rfl, rfl⟩
      | _ =>
          simp [hTy, __smtx_typeof_seq_op_2, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_seq_op_2, smt_lit_ite, smt_lit_Teq, h1, h2] at ht

theorem seq_triop_args_of_non_none
    {op t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply op t1) t2) t3) =
        __smtx_typeof_seq_op_3 (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3))
    (ht :
      term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply op t1) t2) t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Seq T ∧
        __smtx_typeof t3 = SmtType.Seq T := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Seq U =>
          cases h3 : __smtx_typeof t3 with
          | Seq V =>
              have hEq :
                  T = U ∧ U = V := by
                simpa [hTy, __smtx_typeof_seq_op_3, smt_lit_ite, smt_lit_Teq, h1, h2, h3] using
                  ht
              rcases hEq with ⟨hTU, hUV⟩
              subst hTU
              subst hUV
              exact ⟨T, rfl, rfl, rfl⟩
          | _ =>
              simp [hTy, __smtx_typeof_seq_op_3, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [hTy, __smtx_typeof_seq_op_3, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [hTy, __smtx_typeof_seq_op_3, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht

theorem str_substr_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr t1) t2) t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Int ∧
        __smtx_typeof t3 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof, __smtx_typeof_str_substr, h1, h2, h3] at ht
      exact ⟨T, rfl, rfl, rfl⟩
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof, __smtx_typeof_str_substr, h1, h2, h3] at ht

theorem str_indexof_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Seq T ∧
        __smtx_typeof t3 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Seq U =>
          cases h3 : __smtx_typeof t3 with
          | Int =>
              have hEq : T = U := by
                simpa [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2,
                  h3] using ht
              subst hEq
              exact ⟨T, rfl, rfl, rfl⟩
          | _ =>
              simp [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2,
                h3] at ht
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2,
              h3] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht

theorem str_at_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at t1) t2)) :
    ∃ T : SmtType, __smtx_typeof t1 = SmtType.Seq T ∧ __smtx_typeof t2 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof, __smtx_typeof_str_at, h1, h2] at ht
      exact ⟨T, rfl, rfl⟩
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof, __smtx_typeof_str_at, h1, h2] at ht

theorem str_update_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update t1) t2) t3)) :
    ∃ T : SmtType,
      __smtx_typeof t1 = SmtType.Seq T ∧
        __smtx_typeof t2 = SmtType.Int ∧
        __smtx_typeof t3 = SmtType.Seq T := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Int =>
          cases h3 : __smtx_typeof t3 with
          | Seq U =>
              have hEq : T = U := by
                simpa [__smtx_typeof, __smtx_typeof_str_update, smt_lit_ite, smt_lit_Teq, h1, h2,
                  h3] using ht
              subst hEq
              exact ⟨T, rfl, rfl, rfl⟩
          | _ =>
              simp [__smtx_typeof, __smtx_typeof_str_update, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [__smtx_typeof, __smtx_typeof_str_update, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof, __smtx_typeof_str_update, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht

theorem reglan_arg_of_non_none
    {op t : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t) SmtType.RegLan) SmtType.RegLan
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    __smtx_typeof t = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h] at ht
  simpa [h] using (show SmtType.RegLan = SmtType.RegLan from rfl)

theorem reglan_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) SmtType.RegLan)
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    __smtx_typeof t1 = SmtType.RegLan ∧ __smtx_typeof t2 = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  simpa [h1, h2] using
    (show SmtType.RegLan = SmtType.RegLan ∧ SmtType.RegLan = SmtType.RegLan from
      ⟨rfl, rfl⟩)

theorem seq_char_arg_of_non_none
    {op t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char)) ret
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    __smtx_typeof t = SmtType.Seq SmtType.Char := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | Seq A =>
      have hSeq : A = SmtType.Char ∧ ¬ ret = SmtType.None := by
        simpa [hTy, smt_lit_ite, smt_lit_Teq, h] using ht
      have hA : A = SmtType.Char := hSeq.1
      subst hA
      rfl
  | _ =>
      simp [hTy, smt_lit_ite, smt_lit_Teq, h] at ht

theorem seq_char_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) (SmtType.Seq SmtType.Char)) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧
      __smtx_typeof t2 = SmtType.Seq SmtType.Char := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | Seq B =>
          have hSeqs : A = SmtType.Char ∧ B = SmtType.Char ∧ ¬ ret = SmtType.None := by
            simpa [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] using ht
          have hAB : A = SmtType.Char ∧ B = SmtType.Char := ⟨hSeqs.1, hSeqs.2.1⟩
          rcases hAB with ⟨hA, hB⟩
          subst hA
          subst hB
          exact ⟨rfl, rfl⟩
      | _ =>
          simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht

theorem seq_char_reglan_args_of_non_none
    {op t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) SmtType.RegLan) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧ __smtx_typeof t2 = SmtType.RegLan := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | RegLan =>
          have hSeq : A = SmtType.Char ∧ ¬ ret = SmtType.None := by
            simpa [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] using ht
          have hA : A = SmtType.Char := hSeq.1
          subst hA
          exact ⟨rfl, rfl⟩
      | _ =>
          simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2] at ht

theorem str_replace_re_args_of_non_none
    {op t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply op t1) t2) t3) =
        smt_lit_ite (smt_lit_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof t2) SmtType.RegLan)
            (smt_lit_ite (smt_lit_Teq (__smtx_typeof t3) (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply op t1) t2) t3)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧
      __smtx_typeof t2 = SmtType.RegLan ∧
      __smtx_typeof t3 = SmtType.Seq SmtType.Char := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | RegLan =>
          cases h3 : __smtx_typeof t3 with
          | Seq B =>
              have hArgs : A = SmtType.Char ∧ B = SmtType.Char := by
                simpa [hTy, smt_lit_ite, smt_lit_Teq, h1, h2, h3] using ht
              rcases hArgs with ⟨hA, hB⟩
              subst hA
              subst hB
              exact ⟨rfl, rfl, rfl⟩
          | _ =>
              simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [hTy, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht

theorem str_indexof_re_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re t1) t2) t3)) :
    __smtx_typeof t1 = SmtType.Seq SmtType.Char ∧
      __smtx_typeof t2 = SmtType.RegLan ∧
      __smtx_typeof t3 = SmtType.Int := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq A =>
      cases h2 : __smtx_typeof t2 with
      | RegLan =>
          cases h3 : __smtx_typeof t3 with
          | Int =>
              have hA : A = SmtType.Char := by
                simpa [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h1, h2, h3] using ht
              subst hA
              exact ⟨rfl, rfl, rfl⟩
          | _ =>
              simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht
      | _ =>
          cases h3 : __smtx_typeof t3 <;>
            simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;> cases h3 : __smtx_typeof t3 <;>
        simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h1, h2, h3] at ht

theorem typeof_value_model_eval_str_len
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_len t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_len t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_len t) := by
  unfold term_has_non_none_type at ht
  cases hArg : __smtx_typeof t <;>
    simp [__smtx_typeof, __smtx_typeof_seq_op_1_ret, smt_lit_ite, smt_lit_Teq, hArg] at ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_len t) = SmtType.Int by
    simp [__smtx_typeof, __smtx_typeof_seq_op_1_ret, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_len (__smtx_model_eval M t)) = SmtType.Int
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

theorem typeof_value_model_eval_str_to_lower
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_lower t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_to_lower t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_lower t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_lower) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_lower t) = SmtType.Seq SmtType.Char by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_to_lower (__smtx_model_eval M t)) =
    SmtType.Seq SmtType.Char
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  change __smtx_typeof_seq_value
      (smt_lit_pack_string (smt_lit_str_to_lower (smt_lit_unpack_string ss))) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _

theorem typeof_value_model_eval_str_to_upper
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_upper t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_to_upper t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_upper t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_upper) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_upper t) = SmtType.Seq SmtType.Char by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_to_upper (__smtx_model_eval M t)) =
    SmtType.Seq SmtType.Char
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  change __smtx_typeof_seq_value
      (smt_lit_pack_string (smt_lit_str_to_upper (smt_lit_unpack_string ss))) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _

theorem typeof_value_model_eval_str_concat
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat t1) t2) := by
  rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat) rfl ht with ⟨T, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat t1) t2) = SmtType.Seq T by
    simp [__smtx_typeof, __smtx_typeof_seq_op_2, smt_lit_ite, smt_lit_Teq, h1, h2]]
  change __smtx_typeof_value (__smtx_model_eval_str_concat (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hty2 : __smtx_typeof_seq_value ss2 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss2, h2] using hpres2
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (smt_lit_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs2 : list_typed T (smt_lit_unpack_seq ss2) :=
    typed_unpack_seq_of_typeof_seq_value hty2
  rw [hss1, hss2]
  simpa [__smtx_model_eval_str_concat, hElem1, __smtx_typeof_value, smt_lit_seq_concat] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := smt_lit_unpack_seq ss1 ++ smt_lit_unpack_seq ss2)
      (list_typed_append hxs1 hxs2))

theorem typeof_value_model_eval_str_substr
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr t1) t2) t3)) =
      __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr t1) t2) t3) := by
  rcases str_substr_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr t1) t2) t3) =
        SmtType.Seq T by
    simp [__smtx_typeof, __smtx_typeof_str_substr, h1, h2, h3]]
  change __smtx_typeof_value
      (__smtx_model_eval_str_substr (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hn2⟩
  rcases int_value_canonical (by simpa [h3] using hpres3) with ⟨n3, hn3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (smt_lit_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  rw [hss1, hn2, hn3]
  simpa [__smtx_model_eval_str_substr, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := smt_lit_seq_extract (smt_lit_unpack_seq ss1) n2 n3)
      (list_typed_extract hxs1 n2 n3))

theorem typeof_value_model_eval_str_contains
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains t1) t2) := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | Seq T =>
      cases h2 : __smtx_typeof t2 with
      | Seq U =>
          have hEq : T = U := by
            simpa [__smtx_typeof, __smtx_typeof_seq_op_2_ret, smt_lit_ite, smt_lit_Teq, h1, h2] using
              ht
          subst hEq
          rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains t1) t2) =
              SmtType.Bool by
            simp [__smtx_typeof, __smtx_typeof_seq_op_2_ret, smt_lit_ite, smt_lit_Teq, h1, h2]]
          change __smtx_typeof_value (__smtx_model_eval_str_contains (__smtx_model_eval M t1)
              (__smtx_model_eval M t2)) = SmtType.Bool
          rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
          rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
          rw [hss1, hss2]
          rfl
      | _ =>
          simp [__smtx_typeof, __smtx_typeof_seq_op_2_ret, smt_lit_ite, smt_lit_Teq, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof, __smtx_typeof_seq_op_2_ret, smt_lit_ite, smt_lit_Teq, h1, h2] at ht

theorem typeof_value_model_eval_str_indexof
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3)) =
      __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3) := by
  rcases str_indexof_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof t1) t2) t3) =
        SmtType.Int by
    simp [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, h1, h2, h3]]
  change __smtx_typeof_value
      (__smtx_model_eval_str_indexof (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Int
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rcases int_value_canonical (by simpa [h3] using hpres3) with ⟨n, hn⟩
  rw [hss1, hss2, hn]
  rfl

theorem typeof_value_model_eval_str_at
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at t1) t2) := by
  rcases str_at_args_of_non_none ht with ⟨T, h1, h2⟩
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at t1) t2) = SmtType.Seq T by
    simp [__smtx_typeof, __smtx_typeof_str_at, h1, h2]]
  change __smtx_typeof_value (__smtx_model_eval_str_at (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hn2⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (smt_lit_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  rw [hss1, hn2]
  simpa [__smtx_model_eval_str_at, __smtx_model_eval_str_substr, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := smt_lit_seq_extract (smt_lit_unpack_seq ss1) n2 1)
      (list_typed_extract hxs1 n2 1))

theorem typeof_value_model_eval_str_replace
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace t1) t2) t3)) =
      __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace t1) t2) t3) := by
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace) rfl ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace t1) t2) t3) =
        SmtType.Seq T by
    simp [__smtx_typeof, __smtx_typeof_seq_op_3, smt_lit_ite, smt_lit_Teq, h1, h2, h3]]
  change __smtx_typeof_value
      (__smtx_model_eval_str_replace (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rcases seq_value_canonical (by simpa [h3] using hpres3) with ⟨ss3, hss3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hty3 : __smtx_typeof_seq_value ss3 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss3, h3] using hpres3
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (smt_lit_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs3 : list_typed T (smt_lit_unpack_seq ss3) :=
    typed_unpack_seq_of_typeof_seq_value hty3
  rw [hss1, hss2, hss3]
  simpa [__smtx_model_eval_str_replace, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := smt_lit_seq_replace (smt_lit_unpack_seq ss1) (smt_lit_unpack_seq ss2)
        (smt_lit_unpack_seq ss3))
      (list_typed_replace hxs1 hxs3))

theorem typeof_value_model_eval_str_rev
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_rev t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_rev t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_rev t) := by
  rcases seq_arg_of_non_none (op := SmtTerm.str_rev) rfl ht with ⟨T, hArg⟩
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_rev t) = SmtType.Seq T by
    simp [__smtx_typeof, __smtx_typeof_seq_op_1, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_rev (__smtx_model_eval M t)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  have hty : __smtx_typeof_seq_value ss = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss, hArg] using hpres
  have hElem : __smtx_elem_typeof_seq_value ss = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty
  have hxs : list_typed T (smt_lit_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hty
  rw [hss]
  simpa [__smtx_model_eval_str_rev, hElem, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := (smt_lit_unpack_seq ss).reverse)
      (list_typed_reverse hxs))

theorem typeof_value_model_eval_str_update
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update t1) t2) t3)) =
      __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update t1) t2) t3) := by
  rcases str_update_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update t1) t2) t3) =
        SmtType.Seq T by
    simp [__smtx_typeof, __smtx_typeof_str_update, smt_lit_ite, smt_lit_Teq, h1, h2, h3]]
  change __smtx_typeof_value
      (__smtx_model_eval_str_update (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases int_value_canonical (by simpa [h2] using hpres2) with ⟨n2, hn2⟩
  rcases seq_value_canonical (by simpa [h3] using hpres3) with ⟨ss3, hss3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hty3 : __smtx_typeof_seq_value ss3 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss3, h3] using hpres3
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (smt_lit_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs3 : list_typed T (smt_lit_unpack_seq ss3) :=
    typed_unpack_seq_of_typeof_seq_value hty3
  rw [hss1, hn2, hss3]
  simpa [__smtx_model_eval_str_update, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := smt_lit_seq_update (smt_lit_unpack_seq ss1) n2 (smt_lit_unpack_seq ss3))
      (list_typed_update hxs1 hxs3 n2))

theorem typeof_value_model_eval_str_replace_all
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all t1) t2) t3)) =
      __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all t1) t2) t3) := by
  rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all) rfl ht with ⟨T, h1, h2, h3⟩
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all t1) t2) t3) =
        SmtType.Seq T by
    simp [__smtx_typeof, __smtx_typeof_seq_op_3, smt_lit_ite, smt_lit_Teq, h1, h2, h3]]
  change __smtx_typeof_value
      (__smtx_model_eval_str_replace_all (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq T
  rcases seq_value_canonical (by simpa [h1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [h2] using hpres2) with ⟨ss2, hss2⟩
  rcases seq_value_canonical (by simpa [h3] using hpres3) with ⟨ss3, hss3⟩
  have hty1 : __smtx_typeof_seq_value ss1 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss1, h1] using hpres1
  have hty3 : __smtx_typeof_seq_value ss3 = SmtType.Seq T := by
    simpa [__smtx_typeof_value, hss3, h3] using hpres3
  have hElem1 : __smtx_elem_typeof_seq_value ss1 = T :=
    elem_typeof_seq_value_of_typeof_seq_value hty1
  have hxs1 : list_typed T (smt_lit_unpack_seq ss1) :=
    typed_unpack_seq_of_typeof_seq_value hty1
  have hxs3 : list_typed T (smt_lit_unpack_seq ss3) :=
    typed_unpack_seq_of_typeof_seq_value hty3
  rw [hss1, hss2, hss3]
  simpa [__smtx_model_eval_str_replace_all, hElem1, __smtx_typeof_value] using
    (typeof_seq_value_pack_seq_of_typed
      (T := T)
      (xs := smt_lit_seq_replace_all (smt_lit_unpack_seq ss1) (smt_lit_unpack_seq ss2)
        (smt_lit_unpack_seq ss3))
      (list_typed_replace_all hxs1 hxs3))

theorem typeof_value_model_eval_str_replace_re
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re t1) t2) t3)) =
      __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re t1) t2) t3) := by
  have hArgs := str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re) rfl ht
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re t1) t2) t3) =
        SmtType.Seq SmtType.Char by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]]
  change __smtx_typeof_value
      (__smtx_model_eval_str_replace_re (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq SmtType.Char
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2.1] using hpres2) with ⟨r, hr⟩
  rcases seq_value_canonical (by simpa [hArgs.2.2] using hpres3) with ⟨ss3, hss3⟩
  rw [hss1, hr, hss3]
  change __smtx_typeof_seq_value
      (smt_lit_pack_string
        (smt_lit_str_replace_re (smt_lit_unpack_string ss1) r (smt_lit_unpack_string ss3))) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _

theorem typeof_value_model_eval_str_replace_re_all
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all t1) t2) t3)) =
      __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all t1) t2) t3) := by
  have hArgs := str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all) rfl ht
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all t1) t2) t3) =
        SmtType.Seq SmtType.Char by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]]
  change __smtx_typeof_value
      (__smtx_model_eval_str_replace_re_all (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Seq SmtType.Char
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2.1] using hpres2) with ⟨r, hr⟩
  rcases seq_value_canonical (by simpa [hArgs.2.2] using hpres3) with ⟨ss3, hss3⟩
  rw [hss1, hr, hss3]
  change __smtx_typeof_seq_value
      (smt_lit_pack_string
        (smt_lit_str_replace_re_all (smt_lit_unpack_string ss1) r (smt_lit_unpack_string ss3))) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _

theorem typeof_value_model_eval_str_indexof_re
    (M : SmtModel)
    (t1 t2 t3 : SmtTerm)
    (ht :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re t1) t2) t3))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2)
    (hpres3 : __smtx_typeof_value (__smtx_model_eval M t3) = __smtx_typeof t3) :
    __smtx_typeof_value
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re t1) t2) t3)) =
      __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re t1) t2) t3) := by
  have hArgs := str_indexof_re_args_of_non_none ht
  rw [show __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re t1) t2) t3) =
        SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]]
  change __smtx_typeof_value
      (__smtx_model_eval_str_indexof_re (__smtx_model_eval M t1) (__smtx_model_eval M t2)
        (__smtx_model_eval M t3)) = SmtType.Int
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2.1] using hpres2) with ⟨r, hr⟩
  rcases int_value_canonical (by simpa [hArgs.2.2] using hpres3) with ⟨n, hn⟩
  rw [hss1, hr, hn]
  rfl

theorem typeof_value_model_eval_str_to_code
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_code t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_to_code t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_code t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_code) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_code t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_to_code (__smtx_model_eval M t)) =
    SmtType.Int
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

theorem typeof_value_model_eval_str_to_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_to_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_int t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_int t) = SmtType.Int by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_to_int (__smtx_model_eval M t)) =
    SmtType.Int
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

theorem typeof_value_model_eval_str_from_code
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_from_code t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_from_code t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_from_code t) := by
  unfold term_has_non_none_type at ht
  cases hArg : __smtx_typeof t <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg] at ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_from_code t) = SmtType.Seq SmtType.Char by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_from_code (__smtx_model_eval M t)) =
    SmtType.Seq SmtType.Char
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  change __smtx_typeof_seq_value (smt_lit_pack_string (smt_lit_str_from_code n)) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _

theorem typeof_value_model_eval_str_from_int
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_from_int t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_from_int t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_from_int t) := by
  unfold term_has_non_none_type at ht
  cases hArg : __smtx_typeof t <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg] at ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_from_int t) = SmtType.Seq SmtType.Char by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_from_int (__smtx_model_eval M t)) =
    SmtType.Seq SmtType.Char
  rcases int_value_canonical (by simpa [hArg] using hpres) with ⟨n, hn⟩
  rw [hn]
  change __smtx_typeof_seq_value (smt_lit_pack_string (smt_lit_str_from_int n)) =
    SmtType.Seq SmtType.Char
  exact typeof_pack_string _

theorem typeof_value_model_eval_str_to_re
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_re t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_to_re t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_re t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_re) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_to_re t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_to_re (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  rfl

theorem typeof_value_model_eval_re_mult
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_mult t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.re_mult t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.re_mult t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_mult) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.re_mult t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_re_mult (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

theorem typeof_value_model_eval_re_plus
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_plus t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.re_plus t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.re_plus t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_plus) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.re_plus t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_re_plus (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

theorem typeof_value_model_eval_re_opt
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_opt t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.re_opt t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.re_opt t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_opt) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.re_opt t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_re_opt (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

theorem typeof_value_model_eval_re_comp
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_comp t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.re_comp t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.re_comp t) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := SmtTerm.re_comp) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.re_comp t) = SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_re_comp (__smtx_model_eval M t)) =
    SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArg] using hpres) with ⟨r, hr⟩
  rw [hr]
  rfl

theorem typeof_value_model_eval_re_range
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.re_range) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_range (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  rfl

theorem typeof_value_model_eval_re_concat
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat t1) t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_concat) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_concat (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

theorem typeof_value_model_eval_re_inter
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter t1) t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_inter) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_inter (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

theorem typeof_value_model_eval_re_union
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union t1) t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_union) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_union (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

theorem typeof_value_model_eval_re_diff
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff t1) t2) := by
  have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_diff) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff t1) t2) =
      SmtType.RegLan by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_re_diff (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.RegLan
  rcases reglan_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨r1, hr1⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r2, hr2⟩
  rw [hr1, hr2]
  rfl

theorem typeof_value_model_eval_str_in_re
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re t1) t2) := by
  have hArgs := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_in_re (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss, hss⟩
  rcases reglan_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨r, hr⟩
  rw [hss, hr]
  rfl

theorem typeof_value_model_eval_str_lt
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_lt) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_lt (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  rfl

theorem typeof_value_model_eval_str_leq
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_leq) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_leq (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  unfold __smtx_model_eval_str_leq
  rcases bool_value_canonical
      (typeof_value_model_eval_eq_value (SmtValue.Seq ss1) (SmtValue.Seq ss2)) with
    ⟨bEq, hbEq⟩
  rw [hbEq]
  rfl

theorem typeof_value_model_eval_str_prefixof
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_prefixof) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_prefixof (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  unfold __smtx_model_eval_str_prefixof
  simpa using
    typeof_value_model_eval_eq_value
      (SmtValue.Seq ss1)
      (__smtx_model_eval_str_substr (SmtValue.Seq ss2) (SmtValue.Numeral 0)
        (__smtx_model_eval_str_len (SmtValue.Seq ss1)))

theorem typeof_value_model_eval_str_suffixof
    (M : SmtModel)
    (t1 t2 : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof t1) t2))
    (hpres1 : __smtx_typeof_value (__smtx_model_eval M t1) = __smtx_typeof t1)
    (hpres2 : __smtx_typeof_value (__smtx_model_eval M t2) = __smtx_typeof t2) :
    __smtx_typeof_value (__smtx_model_eval M
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof t1) t2)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof t1) t2) := by
  have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_suffixof) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof t1) t2) =
      SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]]
  change __smtx_typeof_value (__smtx_model_eval_str_suffixof (__smtx_model_eval M t1)
      (__smtx_model_eval M t2)) = SmtType.Bool
  rcases seq_value_canonical (by simpa [hArgs.1] using hpres1) with ⟨ss1, hss1⟩
  rcases seq_value_canonical (by simpa [hArgs.2] using hpres2) with ⟨ss2, hss2⟩
  rw [hss1, hss2]
  unfold __smtx_model_eval_str_suffixof
  simpa using
    typeof_value_model_eval_eq_value
      (SmtValue.Seq ss1)
      (__smtx_model_eval_str_substr (SmtValue.Seq ss2)
        (__smtx_model_eval__ (__smtx_model_eval_str_len (SmtValue.Seq ss2))
          (__smtx_model_eval_str_len (SmtValue.Seq ss1)))
        (__smtx_model_eval_str_len (SmtValue.Seq ss1)))

theorem typeof_value_model_eval_str_is_digit
    (M : SmtModel)
    (t : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_is_digit t))
    (hpres : __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply SmtTerm.str_is_digit t)) =
      __smtx_typeof (SmtTerm.Apply SmtTerm.str_is_digit t) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_is_digit) rfl ht
  rw [show __smtx_typeof (SmtTerm.Apply SmtTerm.str_is_digit t) = SmtType.Bool by
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]]
  change __smtx_typeof_value (__smtx_model_eval_str_is_digit (__smtx_model_eval M t)) =
    SmtType.Bool
  rcases seq_value_canonical (by simpa [hArg] using hpres) with ⟨ss, hss⟩
  rw [hss]
  simp [__smtx_model_eval_str_is_digit, __smtx_model_eval_str_to_code, __smtx_model_eval_leq,
    __smtx_model_eval_and, __smtx_typeof_value]

theorem supported_type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  cases hs with
  | boolean b =>
      exact typeof_value_model_eval_boolean M b
  | numeral n =>
      exact typeof_value_model_eval_numeral M n
  | rational q =>
      exact typeof_value_model_eval_rational M q
  | string s =>
      exact typeof_value_model_eval_string M s
  | binary w n =>
      exact typeof_value_model_eval_binary M w n ht
  | var s T =>
      exact typeof_value_model_eval_var M hM s T
  | uconst s T =>
      exact typeof_value_model_eval_uconst M hM s T
  | re_allchar =>
      exact typeof_value_model_eval_re_allchar M
  | re_none =>
      exact typeof_value_model_eval_re_none M
  | re_all =>
      exact typeof_value_model_eval_re_all M
  | seq_empty T =>
      exact typeof_value_model_eval_seq_empty M T
  | set_empty T =>
      exact typeof_value_model_eval_set_empty M T
  | seq_unit ht1 hs1 =>
      exact typeof_value_model_eval_seq_unit M _ ht1
        (supported_type_preservation M hM _ ht1 hs1)
  | set_singleton ht1 hs1 =>
      exact typeof_value_model_eval_set_singleton M _ ht1
        (supported_type_preservation M hM _ ht1 hs1)
  | select ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_select M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | store ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_store M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | ite htc hsc ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_ite M _ _ _ ht
        (supported_type_preservation M hM _ htc hsc)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «exists» s T body =>
      exact typeof_value_model_eval_exists M s T body ht
  | «forall» s T body =>
      exact typeof_value_model_eval_forall M s T body ht
  | choice s T body =>
      exact typeof_value_model_eval_choice M s T body ht
  | «not» ht1 hs1 =>
      exact typeof_value_model_eval_not M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | «or» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_or M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «and» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_and M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «imp» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_imp M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | eq t1 t2 =>
      exact typeof_value_model_eval_eq M t1 t2 ht
  | xor t1 t2 =>
      exact typeof_value_model_eval_xor M t1 t2 ht
  | distinct t1 t2 =>
      exact typeof_value_model_eval_distinct M t1 t2 ht
  | plus ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_plus M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | arith_neg ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_neg M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | mult ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_mult M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | lt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_lt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | leq ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_leq M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | gt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_gt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | geq ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_geq M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | to_real ht1 hs1 =>
      exact typeof_value_model_eval_to_real M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | to_int ht1 hs1 =>
      exact typeof_value_model_eval_to_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | is_int ht1 hs1 =>
      exact typeof_value_model_eval_is_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | abs ht1 hs1 =>
      exact typeof_value_model_eval_abs M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_len ht1 hs1 =>
      exact typeof_value_model_eval_str_len M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_to_lower ht1 hs1 =>
      exact typeof_value_model_eval_str_to_lower M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_to_upper ht1 hs1 =>
      exact typeof_value_model_eval_str_to_upper M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_concat ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_concat M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_substr ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_substr M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_contains ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_contains M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_indexof ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_indexof M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_at ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_at M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_replace ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_replace M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_rev ht1 hs1 =>
      exact typeof_value_model_eval_str_rev M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_update ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_update M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_replace_all ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_replace_all M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_replace_re ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_replace_re M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_replace_re_all ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_replace_re_all M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_indexof_re ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_str_indexof_re M _ _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
        (supported_type_preservation M hM _ ht3 hs3)
  | str_to_code ht1 hs1 =>
      exact typeof_value_model_eval_str_to_code M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_to_int ht1 hs1 =>
      exact typeof_value_model_eval_str_to_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_from_code ht1 hs1 =>
      exact typeof_value_model_eval_str_from_code M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_from_int ht1 hs1 =>
      exact typeof_value_model_eval_str_from_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | str_to_re ht1 hs1 =>
      exact typeof_value_model_eval_str_to_re M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_mult ht1 hs1 =>
      exact typeof_value_model_eval_re_mult M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_plus ht1 hs1 =>
      exact typeof_value_model_eval_re_plus M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_opt ht1 hs1 =>
      exact typeof_value_model_eval_re_opt M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_comp ht1 hs1 =>
      exact typeof_value_model_eval_re_comp M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | re_range ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_range M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | re_concat ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_concat M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | re_inter ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_inter M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | re_union ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_union M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | re_diff ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_re_diff M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_in_re ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_in_re M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_lt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_lt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_leq ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_leq M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_prefixof ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_prefixof M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_suffixof ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_str_suffixof M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | str_is_digit ht1 hs1 =>
      exact typeof_value_model_eval_str_is_digit M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | bv_concat ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_concat M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | extract ht1 hs1 ht2 hs2 ht3 hs3 =>
      exact typeof_value_model_eval_extract M _ _ _ ht
        (supported_type_preservation M hM _ ht3 hs3)
  | bvnot ht1 hs1 =>
      exact typeof_value_model_eval_bvnot M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | bvand ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvand M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvor ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvor M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvnand ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvnand M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvnor ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvnor M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvxor ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvxor M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvxnor ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvxnor M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvcomp ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvcomp M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvneg ht1 hs1 =>
      exact typeof_value_model_eval_bvneg M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | bvadd ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvadd M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvmul ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvmul M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvudiv ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvudiv M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvurem ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvurem M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsub ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsub M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvult ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvult M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvule ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvule M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvugt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvugt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvuge ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvuge M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvslt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvslt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsle ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsle M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsgt ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsgt M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsge ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsge M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvshl ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvshl M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvlshr ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvlshr M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvuaddo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvuaddo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvnego ht1 hs1 =>
      exact typeof_value_model_eval_bvnego M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | bvsaddo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsaddo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvumulo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvumulo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsmulo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsmulo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvusubo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvusubo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | zero_extend ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_zero_extend M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | sign_extend ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_sign_extend M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | int_to_bv ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_int_to_bv M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | ubv_to_int ht1 hs1 =>
      exact typeof_value_model_eval_ubv_to_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | sbv_to_int ht1 hs1 =>
      exact typeof_value_model_eval_sbv_to_int M _ ht
        (supported_type_preservation M hM _ ht1 hs1)

def preservation_counterexample_exists : SmtTerm :=
  SmtTerm.Apply (SmtTerm.exists "x" SmtType.Bool) (SmtTerm.Numeral 0)

theorem preservation_counterexample_exists_typeof :
    __smtx_typeof preservation_counterexample_exists = SmtType.None := by
  rfl

theorem preservation_counterexample_exists_excluded :
    ¬ term_has_non_none_type preservation_counterexample_exists := by
  simp [term_has_non_none_type, preservation_counterexample_exists_typeof]

theorem preservation_counterexample_exists_eval :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_exists) =
      SmtType.Bool := by
  classical
  have hnot :
      ¬ ∃ v : SmtValue,
        __smtx_typeof_value v = SmtType.Bool ∧
          __smtx_model_eval (__smtx_model_push SmtModel.empty "x" SmtType.Bool v)
            (SmtTerm.Numeral 0) = SmtValue.Boolean true := by
    intro h
    rcases h with ⟨v, _, hv⟩
    change SmtValue.Numeral 0 = SmtValue.Boolean true at hv
    cases hv
  change
    __smtx_typeof_value
      (if h :
          ∃ v : SmtValue,
            __smtx_typeof_value v = SmtType.Bool ∧
              __smtx_model_eval (__smtx_model_push SmtModel.empty "x" SmtType.Bool v)
                (SmtTerm.Numeral 0) = SmtValue.Boolean true then
        SmtValue.Boolean true
      else
        SmtValue.Boolean false) = SmtType.Bool
  simp [hnot, __smtx_typeof_value]

theorem no_total_typed_model :
    ¬ ∃ M : SmtModel, model_total_typed M := by
  intro h
  rcases h with ⟨M, hM⟩
  have hTy :
      __smtx_typeof_value
          (__smtx_model_lookup M "x" (SmtType.TypeRef "A")) =
        SmtType.TypeRef "A" :=
    hM "x" (SmtType.TypeRef "A")
  exact
    no_value_of_type_ref "A"
      ⟨__smtx_model_lookup M "x" (SmtType.TypeRef "A"), hTy⟩

def preservation_counterexample_choice_type_ref : SmtTerm :=
  SmtTerm.Apply (SmtTerm.choice "x" (SmtType.TypeRef "A")) (SmtTerm.Boolean true)

theorem preservation_counterexample_choice_type_ref_typeof :
    __smtx_typeof preservation_counterexample_choice_type_ref = SmtType.None := by
  simp [preservation_counterexample_choice_type_ref, __smtx_typeof, smt_lit_ite, smt_lit_Teq,
    no_value_of_type_ref]

theorem preservation_counterexample_choice_type_ref_excluded :
    ¬ term_has_non_none_type preservation_counterexample_choice_type_ref := by
  simp [term_has_non_none_type, preservation_counterexample_choice_type_ref_typeof]

theorem preservation_counterexample_choice_type_ref_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_choice_type_ref =
      SmtValue.NotValue := by
  classical
  have hNo :
      ¬ ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef "A" :=
    no_value_of_type_ref "A"
  have hNoSat :
      ¬ ∃ v : SmtValue,
          __smtx_typeof_value v = SmtType.TypeRef "A" ∧
            __smtx_model_eval
                (__smtx_model_push SmtModel.empty "x" (SmtType.TypeRef "A") v)
                (SmtTerm.Boolean true) =
              SmtValue.Boolean true := by
    intro h
    rcases h with ⟨v, hv, _⟩
    exact hNo ⟨v, hv⟩
  change
    (if hSat :
          ∃ v : SmtValue,
            __smtx_typeof_value v = SmtType.TypeRef "A" ∧
              __smtx_model_eval
                  (__smtx_model_push SmtModel.empty "x" (SmtType.TypeRef "A") v)
                  (SmtTerm.Boolean true) =
                SmtValue.Boolean true then
        Classical.choose hSat
      else
        if hTy : ∃ v : SmtValue, __smtx_typeof_value v = SmtType.TypeRef "A" then
          Classical.choose hTy
        else
          SmtValue.NotValue) = SmtValue.NotValue
  simp [hNoSat, hNo]

theorem preservation_counterexample_choice_type_ref_eval :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_choice_type_ref) =
      SmtType.None := by
  rw [preservation_counterexample_choice_type_ref_eval_value]
  rfl

end Smtm
