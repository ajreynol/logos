import Cpc.TypePreservation.BitVec
import Cpc.TypePreservation.CoreArith
import Cpc.TypePreservation.Sets
import Cpc.TypePreservation.SeqStringRegex

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

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
  | seq_nth ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_seq_nth M hM _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_union ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_union M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_inter ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_inter M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_minus ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_minus M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_member ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_member M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | set_subset ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_set_subset M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
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
  | div ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_div M hM _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | mod ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_mod M hM _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | multmult ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_multmult M hM _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | divisible ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_divisible M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | int_pow2 ht1 hs1 =>
      exact typeof_value_model_eval_int_pow2 M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | int_log2 ht1 hs1 =>
      exact typeof_value_model_eval_int_log2 M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | div_total ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_div_total M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | mod_total ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_mod_total M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | multmult_total ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_multmult_total M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | qdiv ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_qdiv M hM _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | qdiv_total ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_qdiv_total M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
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
  | re_exp n ht1 hs1 =>
      exact typeof_value_model_eval_re_exp M n _ ht
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
  | re_loop n1 n2 ht1 hs1 =>
      exact typeof_value_model_eval_re_loop M n1 n2 _ ht
        (supported_type_preservation M hM _ ht1 hs1)
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
