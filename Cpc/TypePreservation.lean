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
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
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
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
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
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
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
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
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
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
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
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
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
          simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
            __smtx_typeof_guard, smt_lit_ite, hNone, hEq] at h
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
  simpa [h1, h2] using
    (show SmtType.Bool = SmtType.Bool ∧ SmtType.Bool = SmtType.Bool from ⟨rfl, rfl⟩)

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
  · simpa [h1, h2] using
      (show (SmtType.Int = SmtType.Int ∧ SmtType.Int = SmtType.Int) ∨
          (SmtType.Int = SmtType.Real ∧ SmtType.Int = SmtType.Real) from
        Or.inl ⟨rfl, rfl⟩)
  · simpa [h1, h2] using
      (show (SmtType.Real = SmtType.Int ∧ SmtType.Real = SmtType.Int) ∨
          (SmtType.Real = SmtType.Real ∧ SmtType.Real = SmtType.Real) from
        Or.inr ⟨rfl, rfl⟩)

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
  · simpa [h1, h2] using
      (show (SmtType.Int = SmtType.Int ∧ SmtType.Int = SmtType.Int) ∨
          (SmtType.Int = SmtType.Real ∧ SmtType.Int = SmtType.Real) from
        Or.inl ⟨rfl, rfl⟩)
  · simpa [h1, h2] using
      (show (SmtType.Real = SmtType.Int ∧ SmtType.Real = SmtType.Int) ∨
          (SmtType.Real = SmtType.Real ∧ SmtType.Real = SmtType.Real) from
        Or.inr ⟨rfl, rfl⟩)

theorem to_real_arg_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_real t)) :
    __smtx_typeof t = SmtType.Int ∨ __smtx_typeof t = SmtType.Real := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at ht
  · simpa [h] using (show SmtType.Int = SmtType.Int ∨ SmtType.Int = SmtType.Real from Or.inl rfl)
  · simpa [h] using (show SmtType.Real = SmtType.Int ∨ SmtType.Real = SmtType.Real from Or.inr rfl)

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

def unary_dt : SmtDatatype :=
  SmtDatatype.sum (SmtDatatypeCons.cons SmtType.Int SmtDatatypeCons.unit) SmtDatatype.null

def preservation_counterexample_dt_cons : SmtTerm :=
  SmtTerm.DtCons "D" unary_dt 0

theorem preservation_counterexample_dt_cons_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons =
      SmtValue.DtCons "D" unary_dt 0 := by
  rfl

theorem preservation_counterexample_dt_cons_typeof :
    __smtx_typeof preservation_counterexample_dt_cons =
      SmtType.DtConsType SmtType.Int (SmtType.Datatype "D" unary_dt) := by
  have h :
      __smtx_typeof preservation_counterexample_dt_cons =
        __smtx_typeof_dt_cons_rec (SmtType.Datatype "D" unary_dt)
          (__smtx_dt_substitute "D" unary_dt unary_dt) 0 := by
    rfl
  rw [h]
  native_decide

theorem preservation_counterexample_dt_cons_non_none :
    term_has_non_none_type preservation_counterexample_dt_cons := by
  simp [term_has_non_none_type, preservation_counterexample_dt_cons_typeof]

theorem preservation_counterexample_dt_cons_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons) =
      SmtType.DtConsType SmtType.Int (SmtType.Datatype "D" unary_dt) := by
  rw [preservation_counterexample_dt_cons_eval_value]
  native_decide

theorem typeof_value_model_eval_dt_cons :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons) =
      __smtx_typeof preservation_counterexample_dt_cons := by
  rw [preservation_counterexample_dt_cons_eval_typeof, preservation_counterexample_dt_cons_typeof]

def preservation_counterexample_dt_sel : SmtTerm :=
  SmtTerm.DtSel "D" unary_dt 0 0

theorem preservation_counterexample_dt_sel_typeof :
    __smtx_typeof preservation_counterexample_dt_sel = SmtType.None := by
  rfl

theorem preservation_counterexample_dt_sel_excluded :
    ¬ term_has_non_none_type preservation_counterexample_dt_sel := by
  simp [term_has_non_none_type, preservation_counterexample_dt_sel_typeof]

def preservation_counterexample_dt_tester : SmtTerm :=
  SmtTerm.DtTester "D" unary_dt 0

theorem preservation_counterexample_dt_tester_typeof :
    __smtx_typeof preservation_counterexample_dt_tester = SmtType.None := by
  rfl

theorem preservation_counterexample_dt_tester_excluded :
    ¬ term_has_non_none_type preservation_counterexample_dt_tester := by
  simp [term_has_non_none_type, preservation_counterexample_dt_tester_typeof]

def preservation_counterexample_dt_cons_app : SmtTerm :=
  SmtTerm.Apply preservation_counterexample_dt_cons (SmtTerm.Numeral 7)

theorem preservation_counterexample_dt_cons_app_typeof :
    __smtx_typeof preservation_counterexample_dt_cons_app =
      SmtType.Datatype "D" unary_dt := by
  have h :
      __smtx_typeof preservation_counterexample_dt_cons_app =
        __smtx_typeof_apply (__smtx_typeof preservation_counterexample_dt_cons) SmtType.Int := by
    rfl
  rw [h]
  rw [preservation_counterexample_dt_cons_typeof]
  native_decide

theorem preservation_counterexample_dt_cons_app_non_none :
    term_has_non_none_type preservation_counterexample_dt_cons_app := by
  simp [term_has_non_none_type, preservation_counterexample_dt_cons_app_typeof]

theorem preservation_counterexample_dt_cons_app_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app =
      SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7) := by
  change __smtx_model_eval_apply (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons)
    (SmtValue.Numeral 7) = SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7)
  rw [preservation_counterexample_dt_cons_eval_value]
  rfl

theorem preservation_counterexample_dt_cons_app_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) =
      SmtType.Datatype "D" unary_dt := by
  rw [preservation_counterexample_dt_cons_app_eval_value]
  native_decide

theorem typeof_value_model_eval_dt_cons_app :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) =
      __smtx_typeof preservation_counterexample_dt_cons_app := by
  rw [preservation_counterexample_dt_cons_app_eval_typeof, preservation_counterexample_dt_cons_app_typeof]

def preservation_counterexample_seq_unit_dt_cons_app : SmtTerm :=
  SmtTerm.Apply SmtTerm.seq_unit preservation_counterexample_dt_cons_app

theorem preservation_counterexample_seq_unit_dt_cons_app_typeof :
    __smtx_typeof preservation_counterexample_seq_unit_dt_cons_app =
      SmtType.Seq (SmtType.Datatype "D" unary_dt) := by
  have h :
      __smtx_typeof preservation_counterexample_seq_unit_dt_cons_app =
        smt_lit_ite
          (smt_lit_Teq (__smtx_typeof preservation_counterexample_dt_cons_app) SmtType.None)
          SmtType.None (SmtType.Seq (__smtx_typeof preservation_counterexample_dt_cons_app)) := by
    rfl
  rw [h]
  rw [preservation_counterexample_dt_cons_app_typeof]
  native_decide

theorem preservation_counterexample_seq_unit_dt_cons_app_non_none :
    term_has_non_none_type preservation_counterexample_seq_unit_dt_cons_app := by
  simp [term_has_non_none_type, preservation_counterexample_seq_unit_dt_cons_app_typeof]

theorem preservation_counterexample_seq_unit_dt_cons_app_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_seq_unit_dt_cons_app =
      SmtValue.Seq
        (SmtSeq.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtSeq.empty (SmtType.Datatype "D" unary_dt))) := by
  change
    SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app)
          (SmtSeq.empty
            (__smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app)))) =
      SmtValue.Seq
        (SmtSeq.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtSeq.empty (SmtType.Datatype "D" unary_dt)))
  rw [preservation_counterexample_dt_cons_app_eval_value]
  native_decide

theorem preservation_counterexample_seq_unit_dt_cons_app_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_seq_unit_dt_cons_app) =
      SmtType.Seq (SmtType.Datatype "D" unary_dt) := by
  rw [preservation_counterexample_seq_unit_dt_cons_app_eval_value]
  native_decide

theorem typeof_value_model_eval_seq_unit_dt_cons_app :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_seq_unit_dt_cons_app) =
      __smtx_typeof preservation_counterexample_seq_unit_dt_cons_app := by
  rw [preservation_counterexample_seq_unit_dt_cons_app_eval_typeof,
    preservation_counterexample_seq_unit_dt_cons_app_typeof]

def preservation_counterexample_set_singleton_dt_cons_app : SmtTerm :=
  SmtTerm.Apply SmtTerm.set_singleton preservation_counterexample_dt_cons_app

theorem preservation_counterexample_set_singleton_dt_cons_app_typeof :
    __smtx_typeof preservation_counterexample_set_singleton_dt_cons_app =
      SmtType.Map (SmtType.Datatype "D" unary_dt) SmtType.Bool := by
  have h :
      __smtx_typeof preservation_counterexample_set_singleton_dt_cons_app =
        smt_lit_ite
          (smt_lit_Teq (__smtx_typeof preservation_counterexample_dt_cons_app) SmtType.None)
          SmtType.None
          (SmtType.Map (__smtx_typeof preservation_counterexample_dt_cons_app) SmtType.Bool) := by
    rfl
  rw [h]
  rw [preservation_counterexample_dt_cons_app_typeof]
  native_decide

theorem preservation_counterexample_set_singleton_dt_cons_app_non_none :
    term_has_non_none_type preservation_counterexample_set_singleton_dt_cons_app := by
  simp [term_has_non_none_type, preservation_counterexample_set_singleton_dt_cons_app_typeof]

theorem preservation_counterexample_set_singleton_dt_cons_app_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_set_singleton_dt_cons_app =
      SmtValue.Map
        (SmtMap.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtValue.Boolean true)
          (SmtMap.default (SmtType.Datatype "D" unary_dt) (SmtValue.Boolean false))) := by
  change
    __smtx_model_eval_set_singleton
      (__smtx_model_eval SmtModel.empty preservation_counterexample_dt_cons_app) =
      SmtValue.Map
        (SmtMap.cons (SmtValue.Apply (SmtValue.DtCons "D" unary_dt 0) (SmtValue.Numeral 7))
          (SmtValue.Boolean true)
          (SmtMap.default (SmtType.Datatype "D" unary_dt) (SmtValue.Boolean false)))
  rw [preservation_counterexample_dt_cons_app_eval_value]
  native_decide

theorem preservation_counterexample_set_singleton_dt_cons_app_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_set_singleton_dt_cons_app) =
      SmtType.Map (SmtType.Datatype "D" unary_dt) SmtType.Bool := by
  rw [preservation_counterexample_set_singleton_dt_cons_app_eval_value]
  native_decide

theorem typeof_value_model_eval_set_singleton_dt_cons_app :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_set_singleton_dt_cons_app) =
      __smtx_typeof preservation_counterexample_set_singleton_dt_cons_app := by
  rw [preservation_counterexample_set_singleton_dt_cons_app_eval_typeof,
    preservation_counterexample_set_singleton_dt_cons_app_typeof]

def preservation_counterexample_str_concat : SmtTerm :=
  SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat (SmtTerm.String "a")) (SmtTerm.String "b")

theorem preservation_counterexample_str_concat_typeof :
    __smtx_typeof preservation_counterexample_str_concat = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_seq_op_2 (SmtType.Seq SmtType.Char) (SmtType.Seq SmtType.Char) =
    SmtType.Seq SmtType.Char
  rfl

theorem preservation_counterexample_str_concat_non_none :
    term_has_non_none_type preservation_counterexample_str_concat := by
  simp [term_has_non_none_type, preservation_counterexample_str_concat_typeof]

theorem preservation_counterexample_str_concat_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_str_concat =
      SmtValue.Seq
        (smt_lit_pack_seq (__smtx_elem_typeof_seq_value (smt_lit_pack_string "a"))
          (smt_lit_seq_concat (smt_lit_unpack_seq (smt_lit_pack_string "a"))
            (smt_lit_unpack_seq (smt_lit_pack_string "b")))) := by
  rfl

theorem preservation_counterexample_str_concat_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_concat) =
      SmtType.Seq SmtType.Char := by
  rw [preservation_counterexample_str_concat_eval_value]
  native_decide

theorem typeof_value_model_eval_str_concat_example :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_concat) =
      __smtx_typeof preservation_counterexample_str_concat := by
  rw [preservation_counterexample_str_concat_eval_typeof,
    preservation_counterexample_str_concat_typeof]

def preservation_counterexample_str_substr : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.Apply
      (SmtTerm.Apply SmtTerm.str_substr (SmtTerm.String "ab"))
      (SmtTerm.Numeral 0))
    (SmtTerm.Numeral 1)

theorem preservation_counterexample_str_substr_typeof :
    __smtx_typeof preservation_counterexample_str_substr = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_str_substr (SmtType.Seq SmtType.Char) SmtType.Int SmtType.Int =
    SmtType.Seq SmtType.Char
  rfl

theorem preservation_counterexample_str_substr_non_none :
    term_has_non_none_type preservation_counterexample_str_substr := by
  simp [term_has_non_none_type, preservation_counterexample_str_substr_typeof]

theorem preservation_counterexample_str_substr_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_str_substr =
      SmtValue.Seq
        (smt_lit_pack_seq (__smtx_elem_typeof_seq_value (smt_lit_pack_string "ab"))
          (smt_lit_seq_extract (smt_lit_unpack_seq (smt_lit_pack_string "ab")) 0 1)) := by
  rfl

theorem preservation_counterexample_str_substr_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_substr) =
      SmtType.Seq SmtType.Char := by
  rw [preservation_counterexample_str_substr_eval_value]
  native_decide

theorem typeof_value_model_eval_str_substr_example :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_substr) =
      __smtx_typeof preservation_counterexample_str_substr := by
  rw [preservation_counterexample_str_substr_eval_typeof,
    preservation_counterexample_str_substr_typeof]

def preservation_counterexample_str_rev : SmtTerm :=
  SmtTerm.Apply SmtTerm.str_rev (SmtTerm.String "ab")

theorem preservation_counterexample_str_rev_typeof :
    __smtx_typeof preservation_counterexample_str_rev = SmtType.Seq SmtType.Char := by
  change __smtx_typeof_seq_op_1 (SmtType.Seq SmtType.Char) = SmtType.Seq SmtType.Char
  rfl

theorem preservation_counterexample_str_rev_non_none :
    term_has_non_none_type preservation_counterexample_str_rev := by
  simp [term_has_non_none_type, preservation_counterexample_str_rev_typeof]

theorem preservation_counterexample_str_rev_eval_value :
    __smtx_model_eval SmtModel.empty preservation_counterexample_str_rev =
      SmtValue.Seq
        (smt_lit_pack_seq (__smtx_elem_typeof_seq_value (smt_lit_pack_string "ab"))
          (smt_lit_seq_rev (smt_lit_unpack_seq (smt_lit_pack_string "ab")))) := by
  rfl

theorem preservation_counterexample_str_rev_eval_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_rev) =
      SmtType.Seq SmtType.Char := by
  rw [preservation_counterexample_str_rev_eval_value]
  native_decide

theorem typeof_value_model_eval_str_rev_example :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty preservation_counterexample_str_rev) =
      __smtx_typeof preservation_counterexample_str_rev := by
  rw [preservation_counterexample_str_rev_eval_typeof,
    preservation_counterexample_str_rev_typeof]

end Smtm
