import Cpc.Proofs.TypePreservation.BitVec
import Cpc.Proofs.TypePreservation.CoreArith
import Cpc.Proofs.TypePreservation.Datatypes
import Cpc.Proofs.TypePreservation.Sets
import Cpc.Proofs.TypePreservation.SeqStringRegex

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Main type-preservation theorem for evaluation of supported SMT terms in total typed models. -/
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
  | var s T hT =>
      exact typeof_value_model_eval_var M hM s T hT
  | uconst s T hT =>
      exact typeof_value_model_eval_uconst M hM s T hT
  | re_allchar =>
      exact typeof_value_model_eval_re_allchar M
  | re_none =>
      exact typeof_value_model_eval_re_none M
  | re_all =>
      exact typeof_value_model_eval_re_all M
  | seq_empty T hT =>
      exact typeof_value_model_eval_seq_empty M T hT
  | set_empty T hT =>
      exact typeof_value_model_eval_set_empty M T hT
  | seq_unit ht1 hs1 =>
      exact typeof_value_model_eval_seq_unit M _ ht1
        (supported_type_preservation M hM _ ht1 hs1)
  | set_singleton ht1 hs1 =>
      exact typeof_value_model_eval_set_singleton M _ ht1
        (supported_type_preservation M hM _ ht1 hs1)
  | seq_nth ht1 hs1 ht2 hs2 hT =>
      exact typeof_value_model_eval_seq_nth M hM _ _ ht hT
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
  | «repeat» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_repeat M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsdiv ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsdiv M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsrem ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsrem M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsmod ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsmod M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvashr ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvashr M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | rotate_left ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_rotate_left M _ _ ht
        (supported_type_preservation M hM _ ht2 hs2)
  | rotate_right ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_rotate_right M _ _ ht
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
  | bvssubo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvssubo M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | bvsdivo ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_bvsdivo M _ _ ht
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
  | dt_cons s d i =>
      exact typeof_value_model_eval_dt_cons M s d i
  | dt_sel htSel hT htx hsx =>
      exact typeof_value_model_eval_dt_sel M hM _ _ _ _ _ htSel hT
        (supported_type_preservation M hM _ htx hsx)
  | dt_tester s d i x =>
      exact typeof_value_model_eval_dt_tester M s d i x ht
  | apply hTy hEval htf hsf htx hsx =>
      rename_i f x
      have hTy' :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTy']
        exact hNone
      rw [hEval M, hTy']
      exact typeof_value_model_eval_apply_generic M f x hNN
        (supported_type_preservation M hM f htf hsf)
        (supported_type_preservation M hM x htx hsx)

/-- Restates supported type preservation using an inhabited-type hypothesis. -/
theorem supported_type_preservation_of_inhabited_type
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hti : term_has_inhabited_type t)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t :=
  supported_type_preservation M hM t ht hs

/-- Datatype used in the counterexample to universal type preservation. -/
def universal_counterexample_dt : SmtDatatype :=
  SmtDatatype.sum
    SmtDatatypeCons.unit
    (SmtDatatype.sum
      (SmtDatatypeCons.cons
        (SmtType.Map SmtType.Int (SmtType.TypeRef "D")) SmtDatatypeCons.unit)
      SmtDatatype.null)

/-- Datatype type used in the universal counterexample construction. -/
def universal_counterexample_datatype_type : SmtType :=
  SmtType.Datatype "D" universal_counterexample_dt

/-- Witness value used in the universal counterexample construction. -/
def universal_counterexample_value : SmtValue :=
  SmtValue.DtCons "D" universal_counterexample_dt native_nat_zero

/-- Model used to witness failure of universal type preservation. -/
noncomputable def universal_counterexample_model : SmtModel :=
  __smtx_model_push default_typed_model "x"
    universal_counterexample_datatype_type universal_counterexample_value

/-- Selector term used in the universal counterexample construction. -/
def universal_counterexample_sel : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.DtSel "D" universal_counterexample_dt
      (native_nat_succ native_nat_zero) native_nat_zero)
    (SmtTerm.Var "x" universal_counterexample_datatype_type)

/-- Full SMT term used in the universal counterexample construction. -/
def universal_counterexample_term : SmtTerm :=
  SmtTerm.seq_unit universal_counterexample_sel

/-- Ill-typed selector result type used in the universal counterexample lookup. -/
def universal_counterexample_wrong_sel_type : SmtType :=
  SmtType.Map SmtType.Int
    (SmtType.Map SmtType.Int
      (SmtType.Map universal_counterexample_datatype_type
        (SmtType.Map SmtType.Int (SmtType.TypeRef "D"))))

/-- Computes the type of the universal counterexample value. -/
theorem universal_counterexample_value_typeof :
    __smtx_typeof_value universal_counterexample_value =
      universal_counterexample_datatype_type := by
  native_decide

/-- Shows that the counterexample datatype is inhabited. -/
theorem universal_counterexample_datatype_inhabited :
    type_inhabited universal_counterexample_datatype_type :=
  ⟨universal_counterexample_value, universal_counterexample_value_typeof⟩

/-- Shows that the universal counterexample model is total and typed. -/
theorem universal_counterexample_model_typed :
    model_total_typed universal_counterexample_model := by
  exact model_total_typed_push default_typed_model_total_typed "x"
    universal_counterexample_datatype_type universal_counterexample_value
    universal_counterexample_value_typeof

/-- Computes the type of the counterexample variable. -/
theorem universal_counterexample_var_typeof :
    __smtx_typeof (SmtTerm.Var "x" universal_counterexample_datatype_type) =
      universal_counterexample_datatype_type := by
  have hInh : native_inhabited_type universal_counterexample_datatype_type = true :=
    (smtx_inhabited_type_eq_true_iff universal_counterexample_datatype_type).2
      universal_counterexample_datatype_inhabited
  change __smtx_typeof_guard_inhabited
      universal_counterexample_datatype_type universal_counterexample_datatype_type =
    universal_counterexample_datatype_type
  simp [__smtx_typeof_guard_inhabited, native_ite, hInh]

/-- Computes the selector result type used in the counterexample. -/
theorem universal_counterexample_sel_result_type :
    __smtx_ret_typeof_sel "D" universal_counterexample_dt
      (native_nat_succ native_nat_zero) native_nat_zero =
        SmtType.Map SmtType.Int (SmtType.TypeRef "D") := by
  simp [universal_counterexample_dt, __smtx_ret_typeof_sel,
    __smtx_ret_typeof_sel_rec, __smtx_dt_substitute, __smtx_dtc_substitute,
    native_ite, native_Teq]

/-- Computes the type of the counterexample selector term. -/
theorem universal_counterexample_sel_typeof :
    __smtx_typeof universal_counterexample_sel =
      SmtType.Map SmtType.Int (SmtType.TypeRef "D") := by
  have hNN : term_has_non_none_type universal_counterexample_sel := by
    unfold term_has_non_none_type universal_counterexample_sel
    change
      __smtx_typeof_apply
          (SmtType.Map universal_counterexample_datatype_type
            (__smtx_ret_typeof_sel "D" universal_counterexample_dt
              (native_nat_succ native_nat_zero) native_nat_zero))
          (__smtx_typeof (SmtTerm.Var "x" universal_counterexample_datatype_type)) ≠
        SmtType.None
    rw [universal_counterexample_var_typeof, universal_counterexample_sel_result_type]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq,
      universal_counterexample_datatype_type]
  simpa [universal_counterexample_sel_result_type, universal_counterexample_sel] using
    dt_sel_term_typeof_of_non_none hNN

/-- Computes the type of the full universal counterexample term. -/
theorem universal_counterexample_term_typeof :
    __smtx_typeof universal_counterexample_term =
      SmtType.Seq (SmtType.Map SmtType.Int (SmtType.TypeRef "D")) := by
  unfold universal_counterexample_term
  change
    (let _v0 := __smtx_typeof universal_counterexample_sel;
      native_ite (native_Teq _v0 SmtType.None) SmtType.None (SmtType.Seq _v0)) =
      SmtType.Seq (SmtType.Map SmtType.Int (SmtType.TypeRef "D"))
  rw [universal_counterexample_sel_typeof]
  simp [native_ite, native_Teq]

/-- Shows that the universal counterexample term has non-`None` type. -/
theorem universal_counterexample_term_non_none :
    term_has_non_none_type universal_counterexample_term := by
  unfold term_has_non_none_type
  rw [universal_counterexample_term_typeof]
  simp

/-- Shows that the universal counterexample term has inhabited type. -/
theorem universal_counterexample_term_inhabited :
    term_has_inhabited_type universal_counterexample_term := by
  unfold term_has_inhabited_type
  rw [universal_counterexample_term_typeof]
  exact type_inhabited_seq (SmtType.Map SmtType.Int (SmtType.TypeRef "D"))

/-- Shows that the counterexample selector lookup type is uninhabited. -/
theorem universal_counterexample_wrong_sel_type_uninhabited :
    ¬ type_inhabited universal_counterexample_wrong_sel_type := by
  apply not_type_inhabited_map
  apply not_type_inhabited_map
  apply not_type_inhabited_map
  apply not_type_inhabited_map
  simpa [type_inhabited] using no_value_of_type_ref "D"

/-- Computes the failed selector lookup in the counterexample model. -/
theorem universal_counterexample_wrong_sel_lookup :
    __smtx_model_lookup universal_counterexample_model native_wrong_apply_sel_id
      universal_counterexample_wrong_sel_type = SmtValue.NotValue := by
  exact model_total_typed_lookup_uninhabited universal_counterexample_model_typed
    native_wrong_apply_sel_id universal_counterexample_wrong_sel_type
    universal_counterexample_wrong_sel_type_uninhabited

/-- Computes evaluation of the counterexample variable. -/
theorem universal_counterexample_var_eval :
    __smtx_model_eval universal_counterexample_model
      (SmtTerm.Var "x" universal_counterexample_datatype_type) =
        universal_counterexample_value := by
  change __smtx_model_lookup universal_counterexample_model "x"
      universal_counterexample_datatype_type = universal_counterexample_value
  simp [universal_counterexample_model, __smtx_model_lookup, __smtx_model_push,
    __smtx_model_key]

/-- Computes evaluation of the counterexample selector term. -/
theorem universal_counterexample_sel_eval :
    __smtx_model_eval universal_counterexample_model universal_counterexample_sel =
      SmtValue.NotValue := by
  change
    __smtx_model_eval_dt_sel universal_counterexample_model "D"
      universal_counterexample_dt (native_nat_succ native_nat_zero)
      native_nat_zero
      (__smtx_model_eval universal_counterexample_model
        (SmtTerm.Var "x" universal_counterexample_datatype_type)) = SmtValue.NotValue
  rw [universal_counterexample_var_eval]
  have hHead :
      native_veq (__vsm_apply_head universal_counterexample_value)
        (SmtValue.DtCons "D" universal_counterexample_dt
          (native_nat_succ native_nat_zero)) = false := by
    simp [universal_counterexample_value, __vsm_apply_head, native_veq]
  unfold __smtx_model_eval_dt_sel
  rw [universal_counterexample_sel_result_type]
  rw [hHead]
  simp [native_ite]
  have hLookup :
      __smtx_model_lookup universal_counterexample_model native_wrong_apply_sel_id
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype "D" universal_counterexample_dt)
              (SmtType.Map SmtType.Int (SmtType.TypeRef "D"))))) = SmtValue.NotValue := by
    simpa [universal_counterexample_wrong_sel_type, universal_counterexample_datatype_type] using
      universal_counterexample_wrong_sel_lookup
  rw [hLookup]
  simp [__smtx_map_select]

/-- Computes evaluation of the full universal counterexample term. -/
theorem universal_counterexample_term_eval :
    __smtx_model_eval universal_counterexample_model universal_counterexample_term =
      SmtValue.Seq (SmtSeq.cons SmtValue.NotValue (SmtSeq.empty SmtType.None)) := by
  unfold universal_counterexample_term
  change
    (let _v0 := __smtx_model_eval universal_counterexample_model universal_counterexample_sel;
      SmtValue.Seq (SmtSeq.cons _v0 (SmtSeq.empty (__smtx_typeof_value _v0)))) =
      SmtValue.Seq (SmtSeq.cons SmtValue.NotValue (SmtSeq.empty SmtType.None))
  rw [universal_counterexample_sel_eval]
  rfl

/-- Computes the value type produced by evaluating the universal counterexample term. -/
theorem universal_counterexample_term_value_typeof :
    __smtx_typeof_value
      (__smtx_model_eval universal_counterexample_model universal_counterexample_term) =
        SmtType.Seq SmtType.None := by
  rw [universal_counterexample_term_eval]
  simp [__smtx_typeof_value, __smtx_typeof_seq_value, native_ite, native_Teq]

/-- Shows that the universal counterexample violates type preservation. -/
theorem universal_counterexample_not_preserved :
    __smtx_typeof_value
      (__smtx_model_eval universal_counterexample_model universal_counterexample_term) ≠
        __smtx_typeof universal_counterexample_term := by
  rw [universal_counterexample_term_value_typeof,
    universal_counterexample_term_typeof]
  simp

/-- Shows that inhabited supported type preservation does not extend to a universal theorem. -/
theorem supported_type_preservation_of_inhabited_type_not_universal :
    ¬ ∀ (M : SmtModel) (hM : model_total_typed M) (t : SmtTerm),
        term_has_non_none_type t ->
        term_has_inhabited_type t ->
        __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  intro h
  have hEq :=
    h universal_counterexample_model universal_counterexample_model_typed
      universal_counterexample_term universal_counterexample_term_non_none
      universal_counterexample_term_inhabited
  exact universal_counterexample_not_preserved hEq

/-- Shows that total typed SMT models exist. -/
theorem total_typed_model_nonvacuous :
    ∃ M : SmtModel, model_total_typed M :=
  exists_total_typed_model

end Smtm
