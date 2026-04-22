import Cpc.Proofs.TypePreservation.BitVec
import Cpc.Proofs.TypePreservation.CoreArith
import Cpc.Proofs.TypePreservation.Datatypes
import Cpc.Proofs.TypePreservation.Sets
import Cpc.Proofs.TypePreservation.SeqStringRegex

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Induction lemma proving type preservation for supported SMT terms in total typed models. -/
private theorem supported_type_preservation
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
      exact typeof_value_model_eval_var M hM s T hT ht
  | uconst s T hT =>
      exact typeof_value_model_eval_uconst M hM s T hT ht
  | re_allchar =>
      exact typeof_value_model_eval_re_allchar M
  | re_none =>
      exact typeof_value_model_eval_re_none M
  | re_all =>
      exact typeof_value_model_eval_re_all M
  | seq_empty T hT =>
      exact typeof_value_model_eval_seq_empty M T hT ht
  | set_empty T hT =>
      exact typeof_value_model_eval_set_empty M T hT ht
  | seq_unit ht1 hs1 =>
      exact typeof_value_model_eval_seq_unit M _ ht1
        (supported_type_preservation M hM _ ht1 hs1)
  | set_singleton ht1 hs1 =>
      exact typeof_value_model_eval_set_singleton M _ ht1
        (supported_type_preservation M hM _ ht1 hs1)
  | seq_nth ht1 hs1 ht2 hs2 hT =>
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
  | choice s T body n hChoice =>
      exact typeof_value_model_eval_choice_nth M s T body n ht
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
  | uneg ht1 hs1 =>
      exact typeof_value_model_eval_uneg M _ ht
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
      exact typeof_value_model_eval_dt_cons M s d i ht
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

private theorem term_has_non_none_of_type_eq
    {t : SmtTerm}
    {T : SmtType}
    (h : __smtx_typeof t = T)
    (hT : T ≠ SmtType.None) :
    term_has_non_none_type t := by
  unfold term_has_non_none_type
  rw [h]
  exact hT

/-- Extracts inhabitation of the `seq_nth` result type from a non-`None` typing judgment. -/
theorem seq_nth_term_inhabited_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2)) :
    type_inhabited (__smtx_typeof (SmtTerm.seq_nth t1 t2)) := by
  rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_seq_nth_eq t1 t2] at ht
    simpa [__smtx_typeof_seq_nth, h1, h2] using ht
  have hTy :
      __smtx_typeof (SmtTerm.seq_nth t1 t2) = T := by
    have hGuard : __smtx_typeof_guard_wf T T = T :=
      smtx_typeof_guard_wf_of_non_none T T hGuardNN
    rw [typeof_seq_nth_eq t1 t2]
    simpa [__smtx_typeof_seq_nth, h1, h2] using hGuard
  rw [hTy]
  exact smtx_typeof_guard_wf_inhabited_of_non_none T T hGuardNN

/-- Extracts inhabitation of the `dt_sel` result type from a non-`None` typing judgment. -/
theorem dt_sel_term_inhabited_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner :=
    __smtx_typeof_apply
      (SmtType.FunType (SmtType.Datatype s d) R)
      (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_dt_sel_apply_eq] at ht
    simpa [R, inner] using ht
  have hInh : type_inhabited R :=
    smtx_typeof_guard_wf_inhabited_of_non_none R inner hGuardNN
  rw [dt_sel_term_typeof_of_non_none ht]
  exact hInh

/-- Builds support for `seq_unit` directly from support of its argument and a non-`None` typing judgment. -/
theorem supported_seq_unit_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_unit t))
    (hs : supported_preservation_term t) :
    supported_preservation_term (SmtTerm.seq_unit t) := by
  have htArg : term_has_non_none_type t := by
    unfold term_has_non_none_type at ht ⊢
    by_cases hNone : __smtx_typeof t = SmtType.None
    · rw [__smtx_typeof.eq_118, hNone] at ht
      simp [native_ite, native_Teq] at ht
    · exact hNone
  exact supported_preservation_term.seq_unit htArg hs

/-- Builds support for `set_singleton` directly from support of its argument and a non-`None` typing judgment. -/
theorem supported_set_singleton_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.set_singleton t))
    (hs : supported_preservation_term t) :
    supported_preservation_term (SmtTerm.set_singleton t) := by
  have htArg : term_has_non_none_type t := by
    unfold term_has_non_none_type at ht ⊢
    by_cases hNone : __smtx_typeof t = SmtType.None
    · rw [__smtx_typeof.eq_121, hNone] at ht
      simp [native_ite, native_Teq] at ht
    · exact hNone
  exact supported_preservation_term.set_singleton htArg hs

/-- Builds support for `seq_nth` directly from support of its arguments and a non-`None` typing judgment. -/
theorem supported_seq_nth_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2))
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2) :
    supported_preservation_term (SmtTerm.seq_nth t1 t2) := by
  rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
  have ht1 : term_has_non_none_type t1 :=
    term_has_non_none_of_type_eq h1 (by simp)
  have ht2 : term_has_non_none_type t2 :=
    term_has_non_none_of_type_eq h2 (by simp)
  exact supported_preservation_term.seq_nth
    ht1 hs1 ht2 hs2 (seq_nth_term_inhabited_of_non_none ht)

/-- Builds support for datatype-selector applications directly from support of the argument. -/
theorem supported_dt_sel_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) := by
  have htx : term_has_non_none_type x :=
    term_has_non_none_of_type_eq (dt_sel_arg_datatype_of_non_none ht) (by simp)
  exact supported_preservation_term.dt_sel
    ht (dt_sel_term_inhabited_of_non_none ht) htx hsx

/-- Builds support for applications directly from support of their subterms and a non-`None` typing judgment. -/
theorem supported_apply_of_non_none
    {f x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply f x))
    (hsf : supported_preservation_term f)
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply f x) := by
  by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
  · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
    exact supported_dt_sel_of_non_none ht hsx
  · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
    · rcases hTesterWitness with ⟨s, d, i, rfl⟩
      exact supported_preservation_term.dt_tester s d i x
    · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
        intro s d i j hEq
        exact hSelWitness ⟨s, d, i, j, hEq⟩
      have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
        intro s d i hEq
        exact hTesterWitness ⟨s, d, i, hEq⟩
      have hTy : generic_apply_type f x :=
        generic_apply_type_of_non_datatype_head hSel hTester
      have hEval : generic_apply_eval f x :=
        generic_apply_eval_of_non_datatype_head hSel hTester
      have hTyEq :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTyEq]
        exact hNone
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
      have htf : term_has_non_none_type f := by
        cases hF with
        | inl hFun =>
            exact term_has_non_none_of_type_eq hFun (by simp)
        | inr hFun =>
            exact term_has_non_none_of_type_eq hFun (by simp)
      have htx : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hX hA
      exact supported_preservation_term.apply hTy hEval htf hsf htx hsx

private theorem bool_unop_arg_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    __smtx_typeof t = SmtType.Bool := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t <;>
    simp [hTy, native_ite, native_Teq, h] at ht
  simp

private def type_has_no_none_components : SmtType -> Prop
  | SmtType.None => False
  | SmtType.TypeRef _ => False
  | SmtType.Seq A => type_has_no_none_components A
  | SmtType.Set A => type_has_no_none_components A
  | SmtType.Map A B => type_has_no_none_components A ∧
      type_has_no_none_components B
  | SmtType.FunType A B => type_has_no_none_components A ∧
      type_has_no_none_components B
  | SmtType.DtcAppType A B => type_has_no_none_components A ∧
      type_has_no_none_components B
  | _ => True

private theorem type_has_no_none_components_of_wf :
    {T : SmtType} ->
    __smtx_type_wf T = true ->
    type_has_no_none_components T
  | SmtType.None, h => by
      simp [__smtx_type_wf, __smtx_type_wf_rec] at h
  | SmtType.Bool, _ => by
      simp [type_has_no_none_components]
  | SmtType.Int, _ => by
      simp [type_has_no_none_components]
  | SmtType.Real, _ => by
      simp [type_has_no_none_components]
  | SmtType.RegLan, _ => by
      simp [type_has_no_none_components]
  | SmtType.BitVec _, _ => by
      simp [type_has_no_none_components]
  | SmtType.Map A B, h => by
      rcases map_type_wf_components_of_wf h with ⟨hA, hB⟩
      exact ⟨type_has_no_none_components_of_wf (T := A) hA,
        type_has_no_none_components_of_wf (T := B) hB⟩
  | SmtType.Set A, h => by
      exact type_has_no_none_components_of_wf (T := A) (set_type_wf_component_of_wf h)
  | SmtType.Seq A, h => by
      exact type_has_no_none_components_of_wf (T := A) (seq_type_wf_component_of_wf h)
  | SmtType.Char, _ => by
      simp [type_has_no_none_components]
  | SmtType.Datatype _ _, _ => by
      simp [type_has_no_none_components]
  | SmtType.TypeRef _, h => by
      simp [__smtx_type_wf, __smtx_type_wf_rec] at h
  | SmtType.USort _, _ => by
      simp [type_has_no_none_components]
  | SmtType.FunType A B, h => by
      rcases fun_type_wf_components_of_wf h with ⟨hA, hB⟩
      exact ⟨type_has_no_none_components_of_wf (T := A) hA,
        type_has_no_none_components_of_wf (T := B) hB⟩
  | SmtType.DtcAppType _ _, h => by
      simp [__smtx_type_wf, __smtx_type_wf_rec] at h
termination_by T => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

private theorem type_has_no_none_components_of_wf_rec :
    {T : SmtType} ->
    {refs : RefList} ->
    __smtx_type_wf_rec T refs = true ->
    type_has_no_none_components T
  | SmtType.None, _, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.Bool, _, _ => by
      simp [type_has_no_none_components]
  | SmtType.Int, _, _ => by
      simp [type_has_no_none_components]
  | SmtType.Real, _, _ => by
      simp [type_has_no_none_components]
  | SmtType.RegLan, _, _ => by
      simp [type_has_no_none_components]
  | SmtType.BitVec _, _, _ => by
      simp [type_has_no_none_components]
  | SmtType.Map A B, _, h => by
      have h' :
          __smtx_type_wf_rec A native_reflist_nil = true ∧
            __smtx_type_wf_rec B native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using h
      exact ⟨type_has_no_none_components_of_wf_rec (T := A)
          (refs := native_reflist_nil) h'.1,
        type_has_no_none_components_of_wf_rec (T := B)
          (refs := native_reflist_nil) h'.2⟩
  | SmtType.Set A, _, h => by
      have hA : __smtx_type_wf_rec A native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec] using h
      exact type_has_no_none_components_of_wf_rec
        (T := A) (refs := native_reflist_nil) hA
  | SmtType.Seq A, _, h => by
      have hA : __smtx_type_wf_rec A native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec] using h
      exact type_has_no_none_components_of_wf_rec
        (T := A) (refs := native_reflist_nil) hA
  | SmtType.Char, _, _ => by
      simp [type_has_no_none_components]
  | SmtType.Datatype _ _, _, _ => by
      simp [type_has_no_none_components]
  | SmtType.TypeRef _, _, h => by
      simp [__smtx_type_wf_rec] at h
  | SmtType.USort _, _, _ => by
      simp [type_has_no_none_components]
  | SmtType.FunType A B, _, h => by
      have h' :
          __smtx_type_wf_rec A native_reflist_nil = true ∧
            __smtx_type_wf_rec B native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using h
      exact ⟨type_has_no_none_components_of_wf_rec (T := A)
          (refs := native_reflist_nil) h'.1,
        type_has_no_none_components_of_wf_rec (T := B)
          (refs := native_reflist_nil) h'.2⟩
  | SmtType.DtcAppType _ _, _, h => by
      simp [__smtx_type_wf_rec] at h
termination_by T => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals simp [sizeOf]
  all_goals omega

private theorem type_has_no_none_components_non_none
    {T : SmtType}
    (h : type_has_no_none_components T) :
    T ≠ SmtType.None := by
  cases T <;> simp [type_has_no_none_components] at h ⊢

private theorem type_has_no_none_components_seq_component_non_none
    {A : SmtType}
    (h : type_has_no_none_components (SmtType.Seq A)) :
    A ≠ SmtType.None :=
  type_has_no_none_components_non_none h

private theorem type_has_no_none_components_set_component_non_none
    {A : SmtType}
    (h : type_has_no_none_components (SmtType.Set A)) :
    A ≠ SmtType.None :=
  type_has_no_none_components_non_none h

private theorem type_has_no_none_components_map_components_non_none
    {A B : SmtType}
    (h : type_has_no_none_components (SmtType.Map A B)) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  exact ⟨type_has_no_none_components_non_none h.1,
    type_has_no_none_components_non_none h.2⟩

private theorem type_has_no_none_components_fun_components_non_none
    {A B : SmtType}
    (h : type_has_no_none_components (SmtType.FunType A B)) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  exact ⟨type_has_no_none_components_non_none h.1,
    type_has_no_none_components_non_none h.2⟩

private theorem guard_wf_type_has_no_none_components_of_non_none
    {T U : SmtType}
    (hU : type_has_no_none_components U)
    (hNN : __smtx_typeof_guard_wf T U ≠ SmtType.None) :
    type_has_no_none_components (__smtx_typeof_guard_wf T U) := by
  have hGuard : __smtx_typeof_guard_wf T U = U :=
    smtx_typeof_guard_wf_of_non_none T U hNN
  simpa [hGuard] using hU

private theorem var_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.Var s T)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.Var s T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hWf : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  simpa [__smtx_typeof] using
    guard_wf_type_has_no_none_components_of_non_none
      (type_has_no_none_components_of_wf hWf) hGuardNN

private theorem uconst_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.UConst s T)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.UConst s T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hWf : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  simpa [__smtx_typeof] using
    guard_wf_type_has_no_none_components_of_non_none
      (type_has_no_none_components_of_wf hWf) hGuardNN

private theorem seq_empty_type_has_no_none_components_of_non_none
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.seq_empty T)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.seq_empty T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T (SmtType.Seq T) ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hWf : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T (SmtType.Seq T) hGuardNN
  simpa [__smtx_typeof] using
    guard_wf_type_has_no_none_components_of_non_none
      (by
        have hGoodT : type_has_no_none_components T :=
          type_has_no_none_components_of_wf hWf
        simpa [type_has_no_none_components] using hGoodT) hGuardNN

private theorem set_empty_type_has_no_none_components_of_non_none
    {T : SmtType}
    (ht : term_has_non_none_type (SmtTerm.set_empty T)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.set_empty T)) := by
  have hGuardNN : __smtx_typeof_guard_wf T (SmtType.Set T) ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [__smtx_typeof] using ht
  have hWf : __smtx_type_wf T = true :=
    smtx_typeof_guard_wf_wf_of_non_none T (SmtType.Set T) hGuardNN
  simpa [__smtx_typeof] using
    guard_wf_type_has_no_none_components_of_non_none
      (by
        have hGoodT : type_has_no_none_components T :=
          type_has_no_none_components_of_wf hWf
        simpa [type_has_no_none_components] using hGoodT) hGuardNN

private theorem choice_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    {n : native_Nat}
    (ht : term_has_non_none_type (SmtTerm.choice_nth s T body n)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.choice_nth s T body n)) := by
  induction n generalizing s T body with
  | zero =>
      have hTy : __smtx_typeof (SmtTerm.choice_nth s T body 0) = T :=
        choice_term_typeof_of_non_none ht
      have hGuardTy :
          __smtx_typeof (SmtTerm.choice_nth s T body 0) = __smtx_typeof_guard_wf T T :=
        choice_term_guard_type_of_non_none ht
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        rw [← hGuardTy]
        exact ht
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      rw [hTy]
      exact type_has_no_none_components_of_wf hWf
  | succ n ih =>
      cases body with
      | «exists» s' U body' =>
          have hTyEq :
              __smtx_typeof (SmtTerm.choice_nth s T (SmtTerm.exists s' U body')
                (Nat.succ n)) =
                __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
            rw [__smtx_typeof.eq_136, __smtx_typeof.eq_136]
            simp [__smtx_typeof_choice_nth]
          have ht' : term_has_non_none_type (SmtTerm.choice_nth s' U body' n) := by
            unfold term_has_non_none_type
            rw [← hTyEq]
            exact ht
          simpa [hTyEq] using ih (s := s') (T := U) (body := body') ht'
      | _ =>
          exfalso
          apply ht
          rw [__smtx_typeof.eq_136]
          simp [__smtx_typeof_choice_nth]

private theorem supported_apply_term_of_non_none
    {f x : SmtTerm}
    (ihf : term_has_non_none_type f -> supported_preservation_term f)
    (ihx : term_has_non_none_type x -> supported_preservation_term x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x)) :
    supported_preservation_term (SmtTerm.Apply f x) := by
  by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
  · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
    have htx : term_has_non_none_type x :=
      term_has_non_none_of_type_eq (dt_sel_arg_datatype_of_non_none ht) (by simp)
    exact supported_dt_sel_of_non_none ht (ihx htx)
  · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
    · rcases hTesterWitness with ⟨s, d, i, rfl⟩
      exact supported_preservation_term.dt_tester s d i x
    · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
        intro s d i j hEq
        exact hSelWitness ⟨s, d, i, j, hEq⟩
      have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
        intro s d i hEq
        exact hTesterWitness ⟨s, d, i, hEq⟩
      have hTy : generic_apply_type f x :=
        generic_apply_type_of_non_datatype_head hSel hTester
      have hEval : generic_apply_eval f x :=
        generic_apply_eval_of_non_datatype_head hSel hTester
      have hTyEq :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTyEq]
        exact hNone
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
      have htf : term_has_non_none_type f := by
        cases hF with
        | inl hFun =>
            exact term_has_non_none_of_type_eq hFun (by simp)
        | inr hFun =>
            exact term_has_non_none_of_type_eq hFun (by simp)
      have htx : term_has_non_none_type x :=
        term_has_non_none_of_type_eq hX hA
      exact supported_preservation_term.apply
        hTy hEval htf (ihf htf) htx (ihx htx)


/-- Builds support for `ite` directly from support of its subterms and a non-`None` typing judgment. -/
theorem supported_ite_of_non_none
    {c t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.ite c t1 t2))
    (hsc : supported_preservation_term c)
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2) :
    supported_preservation_term (SmtTerm.ite c t1 t2) := by
  rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, _hT⟩
  have htc : term_has_non_none_type c :=
    term_has_non_none_of_type_eq hc (by simp)
  have ht1 : term_has_non_none_type t1 :=
    term_has_non_none_of_type_eq h1 _hT
  have ht2 : term_has_non_none_type t2 :=
    term_has_non_none_of_type_eq h2 _hT
  exact supported_preservation_term.ite htc hsc ht1 hs1 ht2 hs2

/-- Builds support for `select` directly from support of its subterms and a non-`None` typing judgment. -/
private theorem supported_select_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.select t1 t2))
    (hMapTy : type_has_no_none_components (__smtx_typeof t1))
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2) :
    supported_preservation_term (SmtTerm.select t1 t2) := by
  rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  have hMapNN : A ≠ SmtType.None ∧ B ≠ SmtType.None :=
    type_has_no_none_components_map_components_non_none hMapTy'
  have ht1 : term_has_non_none_type t1 :=
    term_has_non_none_of_type_eq h1 (by simp)
  have ht2 : term_has_non_none_type t2 :=
    term_has_non_none_of_type_eq h2 hMapNN.1
  exact supported_preservation_term.select ht1 hs1 ht2 hs2

/-- Builds support for `store` directly from support of its subterms and a non-`None` typing judgment. -/
private theorem supported_store_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.store t1 t2 t3))
    (hMapTy : type_has_no_none_components (__smtx_typeof t1))
    (hs1 : supported_preservation_term t1)
    (hs2 : supported_preservation_term t2)
    (hs3 : supported_preservation_term t3) :
    supported_preservation_term (SmtTerm.store t1 t2 t3) := by
  rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  have hMapNN : A ≠ SmtType.None ∧ B ≠ SmtType.None :=
    type_has_no_none_components_map_components_non_none hMapTy'
  have ht1 : term_has_non_none_type t1 :=
    term_has_non_none_of_type_eq h1 (by simp)
  have ht2 : term_has_non_none_type t2 :=
    term_has_non_none_of_type_eq h2 hMapNN.1
  have ht3 : term_has_non_none_type t3 :=
    term_has_non_none_of_type_eq h3 hMapNN.2
  exact supported_preservation_term.store ht1 hs1 ht2 hs2 ht3 hs3

private theorem binary_type_has_no_none_components_of_non_none
    {w n : native_Int}
    (ht : term_has_non_none_type (SmtTerm.Binary w n)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.Binary w n)) := by
  unfold term_has_non_none_type at ht
  unfold __smtx_typeof at ht ⊢
  cases hWidth : native_zleq 0 w <;>
    simp [native_ite, SmtEval.native_and, hWidth] at ht ⊢
  cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
    simp [hMod, type_has_no_none_components] at ht ⊢

private theorem seq_unit_type_has_no_none_components_of_non_none
    {t : SmtTerm}
    (_ht : term_has_non_none_type (SmtTerm.seq_unit t))
    (hTy : type_has_no_none_components (__smtx_typeof t)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.seq_unit t)) := by
  rw [__smtx_typeof.eq_118]
  have hArgNN : __smtx_typeof t ≠ SmtType.None :=
    type_has_no_none_components_non_none hTy
  simpa [native_ite, native_Teq, type_has_no_none_components, hArgNN] using hTy

private theorem set_singleton_type_has_no_none_components_of_non_none
    {t : SmtTerm}
    (_ht : term_has_non_none_type (SmtTerm.set_singleton t))
    (hTy : type_has_no_none_components (__smtx_typeof t)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.set_singleton t)) := by
  rw [__smtx_typeof.eq_121]
  have hArgNN : __smtx_typeof t ≠ SmtType.None :=
    type_has_no_none_components_non_none hTy
  simpa [native_ite, native_Teq, type_has_no_none_components, hArgNN] using hTy

private theorem seq_nth_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.seq_nth t1 t2))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.seq_nth t1 t2)) := by
  rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  have hT : type_has_no_none_components T := by
    simpa [type_has_no_none_components] using hSeqTy'
  have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_seq_nth_eq t1 t2] at ht
    simpa [__smtx_typeof_seq_nth, h1, h2] using ht
  have hGuard : __smtx_typeof_guard_wf T T = T :=
    smtx_typeof_guard_wf_of_non_none T T hGuardNN
  rw [typeof_seq_nth_eq]
  simpa [__smtx_typeof_seq_nth, h1, h2, hGuard] using hT

private theorem ite_type_has_no_none_components_of_non_none
    {c t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.ite c t1 t2))
    (hTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.ite c t1 t2)) := by
  rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, _hT⟩
  have hT : type_has_no_none_components T := by
    simpa [h1] using hTy
  rw [typeof_ite_eq]
  simpa [__smtx_typeof_ite, native_ite, native_Teq, hc, h1, h2] using hT

private theorem select_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.select t1 t2))
    (hMapTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.select t1 t2)) := by
  rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  rw [typeof_select_eq]
  simpa [__smtx_typeof_select, native_ite, native_Teq, h1, h2] using hMapTy'.2

private theorem store_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.store t1 t2 t3))
    (hMapTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.store t1 t2 t3)) := by
  rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  rw [typeof_store_eq]
  simpa [__smtx_typeof_store, native_ite, native_Teq, h1, h2, h3] using hMapTy'

private theorem dt_wf_cons_of_wf
    {c : SmtDatatypeCons}
    {d : SmtDatatype}
    {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  by_cases hc : __smtx_dt_cons_wf_rec c refs = true
  · exact hc
  · have hFalse : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = false := by
      simp [__smtx_dt_wf_rec, native_ite, hc]
    rw [hFalse] at h
    simp at h

private theorem dt_wf_tail_of_wf
    {c : SmtDatatypeCons}
    {d : SmtDatatype}
    {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_wf_rec d refs = true := by
  by_cases hd : __smtx_dt_wf_rec d refs = true
  · exact hd
  · have hFalse : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = false := by
      simp [__smtx_dt_wf_rec, native_ite, hd]
    rw [hFalse] at h
    simp at h

private theorem dt_cons_wf_tail_of_wf
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  by_cases hc : __smtx_dt_cons_wf_rec c refs = true
  · exact hc
  · have hFalse : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = false := by
      cases T <;> simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, hc]
    rw [hFalse] at h
    simp at h

private theorem typeof_dt_cons_value_rec_zero_has_no_none_components_of_cons_wf
    {s : native_String}
    {d0 : SmtDatatype}
    (hBaseWf : __smtx_dt_wf_rec d0 (native_reflist_insert native_reflist_nil s) = true) :
    ∀ {c : SmtDatatypeCons} {d : SmtDatatype},
      __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true ->
      type_has_no_none_components
        (__smtx_typeof_dt_cons_value_rec
          (SmtType.Datatype s d0)
          (SmtDatatype.sum (__smtx_dtc_substitute s d0 c) (__smtx_dt_substitute s d0 d))
          0)
  | SmtDatatypeCons.unit, d, _ => by
      simp [__smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec, type_has_no_none_components]
  | SmtDatatypeCons.cons T c, d, h => by
      have hTail : __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true :=
        dt_cons_wf_tail_of_wf h
      let tailTy :=
        __smtx_typeof_dt_cons_value_rec
          (SmtType.Datatype s d0)
          (SmtDatatype.sum (__smtx_dtc_substitute s d0 c) (__smtx_dt_substitute s d0 d))
          0
      have hTailTy : type_has_no_none_components tailTy :=
        typeof_dt_cons_value_rec_zero_has_no_none_components_of_cons_wf hBaseWf (d := d) hTail
      cases T with
      | None =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h
      | DtcAppType A B =>
          simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at h
      | Bool =>
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components SmtType.Bool ∧ type_has_no_none_components tailTy from
              ⟨by simp [type_has_no_none_components], hTailTy⟩)
      | Int =>
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components SmtType.Int ∧ type_has_no_none_components tailTy from
              ⟨by simp [type_has_no_none_components], hTailTy⟩)
      | Real =>
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components SmtType.Real ∧ type_has_no_none_components tailTy from
              ⟨by simp [type_has_no_none_components], hTailTy⟩)
      | RegLan =>
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components SmtType.RegLan ∧ type_has_no_none_components tailTy from
              ⟨by simp [type_has_no_none_components], hTailTy⟩)
      | BitVec w =>
          have hHead : type_has_no_none_components (SmtType.BitVec w) := by
            exact type_has_no_none_components_of_wf_rec
              (T := SmtType.BitVec w)
              (refs := native_reflist_insert native_reflist_nil s)
              (by simp [__smtx_type_wf_rec])
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components (SmtType.BitVec w) ∧ type_has_no_none_components tailTy from
              ⟨hHead, hTailTy⟩)
      | Map A B =>
          have hPair :
              __smtx_type_wf_rec (SmtType.Map A B) (native_reflist_insert native_reflist_nil s) = true ∧
                __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true := by
            simpa [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, native_and] using h
          have hHead : type_has_no_none_components (SmtType.Map A B) :=
            type_has_no_none_components_of_wf_rec
              (T := SmtType.Map A B)
              (refs := native_reflist_insert native_reflist_nil s) hPair.1
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components (SmtType.Map A B) ∧ type_has_no_none_components tailTy from
              ⟨hHead, hTailTy⟩)
      | Set A =>
          have hPair :
              __smtx_type_wf_rec (SmtType.Set A) (native_reflist_insert native_reflist_nil s) = true ∧
                __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true := by
            simpa [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] using h
          have hHead : type_has_no_none_components (SmtType.Set A) :=
            type_has_no_none_components_of_wf_rec
              (T := SmtType.Set A)
              (refs := native_reflist_insert native_reflist_nil s) hPair.1
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components (SmtType.Set A) ∧ type_has_no_none_components tailTy from
              ⟨hHead, hTailTy⟩)
      | Seq A =>
          have hPair :
              __smtx_type_wf_rec (SmtType.Seq A) (native_reflist_insert native_reflist_nil s) = true ∧
                __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true := by
            simpa [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] using h
          have hHead : type_has_no_none_components (SmtType.Seq A) :=
            type_has_no_none_components_of_wf_rec
              (T := SmtType.Seq A)
              (refs := native_reflist_insert native_reflist_nil s) hPair.1
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components (SmtType.Seq A) ∧ type_has_no_none_components tailTy from
              ⟨hHead, hTailTy⟩)
      | Char =>
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components SmtType.Char ∧ type_has_no_none_components tailTy from
              ⟨by simp [type_has_no_none_components], hTailTy⟩)
      | Datatype s' d' =>
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_streq] using
            (show
              type_has_no_none_components
                (SmtType.Datatype s' (native_ite (native_streq s s') d' (__smtx_dt_substitute s d0 d'))) ∧
                type_has_no_none_components tailTy from
              ⟨by simp [type_has_no_none_components], hTailTy⟩)
      | TypeRef s' =>
          have hPair :
              (s' = s ∨ s' ∈ native_reflist_nil) ∧
                __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true := by
            simpa [native_reflist_insert, native_reflist_contains,
              __smtx_dt_cons_wf_rec, native_ite] using h
          have hs' : s' = s := by
            simpa [native_reflist_nil] using hPair.1
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq, hs'] using
            (show type_has_no_none_components (SmtType.Datatype s' d0) ∧ type_has_no_none_components tailTy from
              ⟨by simp [type_has_no_none_components], hTailTy⟩)
      | USort n =>
          have hHead : type_has_no_none_components (SmtType.USort n) := by
            exact type_has_no_none_components_of_wf_rec
              (T := SmtType.USort n)
              (refs := native_reflist_insert native_reflist_nil s)
              (by simp [__smtx_type_wf_rec])
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components (SmtType.USort n) ∧ type_has_no_none_components tailTy from
              ⟨hHead, hTailTy⟩)
      | FunType A B =>
          have hPair :
              __smtx_type_wf_rec (SmtType.FunType A B) (native_reflist_insert native_reflist_nil s) = true ∧
                __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true := by
            simpa [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, native_and] using h
          have hHead : type_has_no_none_components (SmtType.FunType A B) :=
            type_has_no_none_components_of_wf_rec
              (T := SmtType.FunType A B)
              (refs := native_reflist_insert native_reflist_nil s) hPair.1
          simpa [tailTy, __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
            type_has_no_none_components, native_ite, native_Teq] using
            (show type_has_no_none_components (SmtType.FunType A B) ∧ type_has_no_none_components tailTy from
              ⟨hHead, hTailTy⟩)

private theorem typeof_dt_cons_value_rec_has_no_none_components_of_non_none
    {s : native_String}
    {d0 : SmtDatatype}
    (hBaseWf : __smtx_dt_wf_rec d0 (native_reflist_insert native_reflist_nil s) = true) :
    ∀ {d : SmtDatatype} {i : Nat},
      __smtx_dt_wf_rec d (native_reflist_insert native_reflist_nil s) = true ->
      __smtx_typeof_dt_cons_value_rec
          (SmtType.Datatype s d0)
          (__smtx_dt_substitute s d0 d) i ≠ SmtType.None ->
      type_has_no_none_components
        (__smtx_typeof_dt_cons_value_rec
          (SmtType.Datatype s d0)
          (__smtx_dt_substitute s d0 d) i)
  | SmtDatatype.null, i, _, hNN => by
      cases i <;> simp [__smtx_dt_substitute, __smtx_typeof_dt_cons_value_rec,
        __smtx_typeof_dt_cons_value_rec] at hNN ⊢
  | SmtDatatype.sum c d, 0, hWf, _ => by
      have hc : __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true :=
        dt_wf_cons_of_wf hWf
      simpa [__smtx_dt_substitute] using
        typeof_dt_cons_value_rec_zero_has_no_none_components_of_cons_wf
          hBaseWf (d := d) hc
  | SmtDatatype.sum c d, Nat.succ i, hWf, hNN => by
      have hd : __smtx_dt_wf_rec d (native_reflist_insert native_reflist_nil s) = true :=
        dt_wf_tail_of_wf hWf
      have hNN' :
          __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s d0)
              (__smtx_dt_substitute s d0 d) i ≠
            SmtType.None := by
        simpa [__smtx_typeof_dt_cons_value_rec, __smtx_dt_substitute] using hNN
      simpa [__smtx_typeof_dt_cons_value_rec, __smtx_dt_substitute] using
        typeof_dt_cons_value_rec_has_no_none_components_of_non_none
          hBaseWf (d := d) (i := i) hd hNN'

private theorem dt_cons_type_has_no_none_components_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    (ht : term_has_non_none_type (SmtTerm.DtCons s d i)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.DtCons s d i)) := by
  have hGuardNN :
      __smtx_typeof_guard_wf (SmtType.Datatype s d)
        (__smtx_typeof_dt_cons_rec
          (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i) ≠
        SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [typeof_dt_cons_eq] using ht
  have hBaseWf : __smtx_dt_wf_rec d (native_reflist_insert native_reflist_nil s) = true := by
    have hWf : __smtx_type_wf (SmtType.Datatype s d) = true :=
      smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Datatype s d)
        (__smtx_typeof_dt_cons_rec
          (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i) hGuardNN
    simpa [__smtx_type_wf, __smtx_type_wf_rec] using hWf
  have hInnerNN :
      __smtx_typeof_dt_cons_value_rec
          (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i ≠
        SmtType.None := by
    rw [typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec]
    intro hNone
    apply hGuardNN
    rw [smtx_typeof_guard_wf_of_non_none
      (SmtType.Datatype s d)
      (__smtx_typeof_dt_cons_rec
        (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i) hGuardNN, hNone]
  have hInnerTy :
      type_has_no_none_components
        (__smtx_typeof_dt_cons_rec
          (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i) := by
    rw [← typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec]
    exact typeof_dt_cons_value_rec_has_no_none_components_of_non_none
      hBaseWf hBaseWf hInnerNN
  rw [typeof_dt_cons_eq]
  exact guard_wf_type_has_no_none_components_of_non_none hInnerTy hGuardNN

private theorem dt_sel_type_has_no_none_components_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type ((SmtTerm.DtSel s d i j).Apply x)) :
    type_has_no_none_components (__smtx_typeof ((SmtTerm.DtSel s d i j).Apply x)) := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner :=
    __smtx_typeof_apply
      (SmtType.FunType (SmtType.Datatype s d) R)
      (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    rw [typeof_dt_sel_apply_eq] at ht
    simpa [R, inner] using ht
  have hWf : __smtx_type_wf R = true :=
    smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
  rw [dt_sel_term_typeof_of_non_none ht]
  exact type_has_no_none_components_of_wf hWf

private theorem dt_tester_type_has_no_none_components_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type ((SmtTerm.DtTester s d i).Apply x)) :
    type_has_no_none_components (__smtx_typeof ((SmtTerm.DtTester s d i).Apply x)) := by
  rw [dt_tester_term_typeof_of_non_none ht]
  simp [type_has_no_none_components]

private theorem apply_type_has_no_none_components_of_non_none
    {f x : SmtTerm}
    (hTy : generic_apply_type f x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x))
    (hFunTy : type_has_no_none_components (__smtx_typeof f)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.Apply f x)) := by
  have hTyEq :
      __smtx_typeof (SmtTerm.Apply f x) =
        __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
    unfold generic_apply_type at hTy
    exact hTy
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    intro hNone
    apply ht
    rw [hTyEq]
    exact hNone
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
  cases hF with
  | inl hFun =>
      have hFunTy' : type_has_no_none_components (SmtType.FunType A B) := by
        simpa [hFun] using hFunTy
      rw [hTyEq]
      simpa [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hFun, hX, hA]
        using hFunTy'.2
  | inr hFun =>
      have hFunTy' : type_has_no_none_components (SmtType.DtcAppType A B) := by
        simpa [hFun] using hFunTy
      rw [hTyEq]
      simpa [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hFun, hX, hA]
        using hFunTy'.2

private theorem seq_op_1_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_seq_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases seq_arg_of_non_none (op := op) hTy ht with ⟨T, hArg⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [hArg] using hSeqTy
  rw [hTy]
  simpa [__smtx_typeof_seq_op_1, native_ite, native_Teq, hArg, type_has_no_none_components]
    using hSeqTy'

private theorem seq_op_2_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_seq_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases seq_binop_args_of_non_none (op := op) hTy ht with ⟨T, h1, h2⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [hTy]
  simpa [__smtx_typeof_seq_op_2, native_ite, native_Teq, h1, h2, type_has_no_none_components]
    using hSeqTy'

private theorem seq_op_3_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2 t3) =
        __smtx_typeof_seq_op_3 (__smtx_typeof t1) (__smtx_typeof t2)
          (__smtx_typeof t3))
    (ht : term_has_non_none_type (op t1 t2 t3))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2 t3)) := by
  rcases seq_triop_args_of_non_none (op := op) hTy ht with ⟨T, h1, h2, h3⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [hTy]
  simpa [__smtx_typeof_seq_op_3, native_ite, native_Teq, h1, h2, h3,
    type_has_no_none_components] using hSeqTy'

private theorem set_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_sets_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2))
    (hSetTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases set_binop_args_of_non_none (op := op) hTy ht with ⟨A, h1, h2⟩
  have hSetTy' : type_has_no_none_components (SmtType.Set A) := by
    simpa [h1] using hSetTy
  rw [hTy]
  simpa [__smtx_typeof_sets_op_2, native_ite, native_Teq, h1, h2, type_has_no_none_components]
    using hSetTy'

private theorem str_substr_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_substr t1 t2 t3))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_substr t1 t2 t3)) := by
  rcases str_substr_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [typeof_str_substr_eq]
  simpa [__smtx_typeof_str_substr, h1, h2, h3, type_has_no_none_components] using hSeqTy'

private theorem str_at_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_at t1 t2))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_at t1 t2)) := by
  rcases str_at_args_of_non_none ht with ⟨T, h1, h2⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [typeof_str_at_eq]
  simpa [__smtx_typeof_str_at, h1, h2, type_has_no_none_components] using hSeqTy'

private theorem str_update_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_update t1 t2 t3))
    (hSeqTy : type_has_no_none_components (__smtx_typeof t1)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_update t1 t2 t3)) := by
  rcases str_update_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  have hSeqTy' : type_has_no_none_components (SmtType.Seq T) := by
    simpa [h1] using hSeqTy
  rw [typeof_str_update_eq]
  simpa [__smtx_typeof_str_update, native_ite, native_Teq, h1, h2, h3,
    type_has_no_none_components] using hSeqTy'

private theorem str_replace_re_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2 t3) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof t3) (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2 t3)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2 t3)) := by
  have hArgs := str_replace_re_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2, type_has_no_none_components]

private theorem bool_unop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Bool) SmtType.Bool SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.Bool := bool_unop_arg_of_non_none hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArg, type_has_no_none_components]

private theorem bool_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Bool) SmtType.Bool SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := bool_binop_args_bool_of_non_none hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2, type_has_no_none_components]

private theorem arith_unop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_arith_overload_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases arith_unop_arg_of_non_none hTy ht with hArg | hArg
  · rw [hTy]
    simp [__smtx_typeof_arith_overload_op_1, hArg, type_has_no_none_components]
  · rw [hTy]
    simp [__smtx_typeof_arith_overload_op_1, hArg, type_has_no_none_components]

private theorem arith_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases arith_binop_args_of_non_none (op := op) hTy ht with hArgs | hArgs
  · rw [hTy]
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2, type_has_no_none_components]
  · rw [hTy]
    simp [__smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2, type_has_no_none_components]

private theorem arith_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {R : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) R)
    (ht : term_has_non_none_type (op t1 t2))
    (hR : type_has_no_none_components R) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases arith_binop_ret_args_of_non_none (op := op) hTy ht with hArgs | hArgs
  · rw [hTy]
    simpa [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2] using hR
  · rw [hTy]
    simpa [__smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2] using hR

private theorem int_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Int) ret SmtType.None)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.Int :=
    int_arg_of_non_none_ret (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArg] using hRet

private theorem int_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.Int)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.Int) ret SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := int_binop_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArgs.1, hArgs.2] using hRet

private theorem real_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.Real) ret SmtType.None)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.Real :=
    real_arg_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArg] using hRet

private theorem seq_op_1_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_seq_op_1_ret (__smtx_typeof t) ret)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases seq_arg_of_non_none_ret (op := op) hTy ht with ⟨T, hArg⟩
  rw [hTy]
  simpa [__smtx_typeof_seq_op_1_ret, hArg] using hRet

private theorem seq_op_2_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_seq_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases seq_binop_args_of_non_none_ret (op := op) hTy ht with ⟨T, h1, h2⟩
  rw [hTy]
  simpa [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq, h1, h2] using hRet

private theorem set_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_sets_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases set_binop_ret_args_of_non_none (op := op) hTy ht with ⟨A, h1, h2⟩
  rw [hTy]
  simpa [__smtx_typeof_sets_op_2_ret, native_ite, native_Teq, h1, h2] using hRet

private theorem seq_char_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) (SmtType.Seq SmtType.Char)) ret
          SmtType.None)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArg] using hRet

private theorem seq_char_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) (SmtType.Seq SmtType.Char)) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := seq_char_binop_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArgs.1, hArgs.2] using hRet

private theorem seq_char_reglan_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) ret
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := seq_char_reglan_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simpa [native_ite, native_Teq, hArgs.1, hArgs.2] using hRet

private theorem reglan_unop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        native_ite (native_Teq (__smtx_typeof t) SmtType.RegLan) SmtType.RegLan
          SmtType.None)
    (ht : term_has_non_none_type (op t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  have hArg : __smtx_typeof t = SmtType.RegLan :=
    reglan_arg_of_non_none (op := op) hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArg, type_has_no_none_components]

private theorem reglan_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan) SmtType.RegLan
            SmtType.None)
          SmtType.None)
    (ht : term_has_non_none_type (op t1 t2)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  have hArgs := reglan_binop_args_of_non_none (op := op) hTy ht
  rw [hTy]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2, type_has_no_none_components]

private theorem bv_unop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_bv_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (op t)) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases bv_unop_arg_of_non_none (op := op) hTy ht with ⟨w, hArg⟩
  rw [hTy]
  simp [__smtx_typeof_bv_op_1, hArg, type_has_no_none_components]

private theorem bv_unop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm}
    {t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t) =
        __smtx_typeof_bv_op_1_ret (__smtx_typeof t) ret)
    (ht : term_has_non_none_type (op t))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t)) := by
  rcases bv_unop_ret_arg_of_non_none (op := op) hTy ht with ⟨w, hArg⟩
  rw [hTy]
  simpa [__smtx_typeof_bv_op_1_ret, hArg] using hRet

private theorem bv_binop_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (op t1 t2)) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases bv_binop_args_of_non_none hTy ht with ⟨w, h1, h2⟩
  rw [hTy]
  simp [__smtx_typeof_bv_op_2, native_ite, native_nateq, SmtEval.native_nateq,
    h1, h2, type_has_no_none_components]

private theorem bv_binop_ret_type_has_no_none_components_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (ht : term_has_non_none_type (op t1 t2))
    (hRet : type_has_no_none_components ret) :
    type_has_no_none_components (__smtx_typeof (op t1 t2)) := by
  rcases bv_binop_ret_args_of_non_none hTy ht with ⟨w, h1, h2⟩
  rw [hTy]
  simpa [__smtx_typeof_bv_op_2_ret, native_ite, native_nateq, SmtEval.native_nateq,
    h1, h2] using hRet

private theorem eq_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.eq t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.eq t1 t2)) := by
  rw [eq_term_typeof_of_non_none ht]
  simp [type_has_no_none_components]

private theorem exists_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.exists s T body)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.exists s T body)) := by
  rw [exists_term_typeof_of_non_none ht]
  simp [type_has_no_none_components]

private theorem forall_type_has_no_none_components_of_non_none
    {s : native_String}
    {T : SmtType}
    {body : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.forall s T body)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.forall s T body)) := by
  rw [forall_term_typeof_of_non_none ht]
  simp [type_has_no_none_components]

private theorem to_real_type_has_no_none_components_of_non_none
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.to_real t)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.to_real t)) := by
  rcases to_real_arg_of_non_none ht with hArg | hArg
  · rw [typeof_to_real_eq]
    simp [native_ite, native_Teq, hArg, type_has_no_none_components]
  · rw [typeof_to_real_eq]
    simp [native_ite, native_Teq, hArg, type_has_no_none_components]

private theorem str_indexof_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_indexof t1 t2 t3)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_indexof t1 t2 t3)) := by
  rcases str_indexof_args_of_non_none ht with ⟨T, h1, h2, h3⟩
  rw [typeof_str_indexof_eq]
  simp [__smtx_typeof_str_indexof, native_ite, native_Teq, h1, h2, h3,
    type_has_no_none_components]

private theorem str_indexof_re_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.str_indexof_re t1 t2 t3)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.str_indexof_re t1 t2 t3)) := by
  have hArgs := str_indexof_re_args_of_non_none ht
  rw [typeof_str_indexof_re_eq]
  simp [native_ite, native_Teq, hArgs.1, hArgs.2.1, hArgs.2.2, type_has_no_none_components]

private theorem re_exp_type_has_no_none_components_of_non_none
    {n : native_Int}
    {t : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.re_exp (SmtTerm.Numeral n) t)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.re_exp (SmtTerm.Numeral n) t)) := by
  have hArgs := re_exp_arg_of_non_none ht
  rw [typeof_re_exp_eq]
  simp [__smtx_typeof_re_exp, native_ite, hArgs.1, hArgs.2, type_has_no_none_components]

private theorem re_loop_type_has_no_none_components_of_non_none
    {n1 n2 : native_Int}
    {t : SmtTerm}
    (ht :
      term_has_non_none_type
        (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t)) :
    type_has_no_none_components
      (__smtx_typeof (SmtTerm.re_loop (SmtTerm.Numeral n1) (SmtTerm.Numeral n2) t)) := by
  have hArgs := re_loop_arg_of_non_none ht
  rw [typeof_re_loop_eq]
  simp [__smtx_typeof_re_loop, native_ite, hArgs.1, hArgs.2.1, hArgs.2.2,
    type_has_no_none_components]

private theorem concat_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.concat t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.concat t1 t2)) := by
  rcases bv_concat_args_of_non_none ht with ⟨w1, w2, h1, h2⟩
  rw [typeof_concat_eq]
  simp [__smtx_typeof_concat, h1, h2, type_has_no_none_components]

private theorem extract_type_has_no_none_components_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.extract t1 t2 t3)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.extract t1 t2 t3)) := by
  rcases extract_args_of_non_none ht with ⟨i, j, w, h1, h2, h3, hj0, hji, hiw⟩
  rw [typeof_extract_eq]
  simp [__smtx_typeof_extract, native_ite, h1, h2, h3, hj0, hji, hiw,
    type_has_no_none_components]

private theorem repeat_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.repeat t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.repeat t1 t2)) := by
  rcases repeat_args_of_non_none ht with ⟨i, w, h1, h2, hi1⟩
  rw [typeof_repeat_eq]
  simp [__smtx_typeof_repeat, native_ite, h1, h2, hi1, type_has_no_none_components]

private theorem zero_extend_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.zero_extend t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.zero_extend t1 t2)) := by
  rcases zero_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [typeof_zero_extend_eq]
  simp [__smtx_typeof_zero_extend, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem sign_extend_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.sign_extend t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.sign_extend t1 t2)) := by
  rcases sign_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [typeof_sign_extend_eq]
  simp [__smtx_typeof_sign_extend, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem rotate_left_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.rotate_left t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.rotate_left t1 t2)) := by
  rcases rotate_left_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [typeof_rotate_left_eq]
  simp [__smtx_typeof_rotate_left, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem rotate_right_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.rotate_right t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.rotate_right t1 t2)) := by
  rcases rotate_right_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
  rw [typeof_rotate_right_eq]
  simp [__smtx_typeof_rotate_right, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem int_to_bv_type_has_no_none_components_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.int_to_bv t1 t2)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.int_to_bv t1 t2)) := by
  rcases int_to_bv_args_of_non_none ht with ⟨i, h1, h2, hi0⟩
  rw [typeof_int_to_bv_eq]
  simp [__smtx_typeof_int_to_bv, native_ite, h1, h2, hi0, type_has_no_none_components]

private theorem apply_term_type_has_no_none_components_of_non_none
    {f x : SmtTerm}
    (ihf : term_has_non_none_type f -> type_has_no_none_components (__smtx_typeof f))
    (ht : term_has_non_none_type (SmtTerm.Apply f x)) :
    type_has_no_none_components (__smtx_typeof (SmtTerm.Apply f x)) := by
  by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
  · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
    exact dt_sel_type_has_no_none_components_of_non_none ht
  · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
    · rcases hTesterWitness with ⟨s, d, i, rfl⟩
      exact dt_tester_type_has_no_none_components_of_non_none ht
    · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
        intro s d i j hEq
        exact hSelWitness ⟨s, d, i, j, hEq⟩
      have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
        intro s d i hEq
        exact hTesterWitness ⟨s, d, i, hEq⟩
      have hTy : generic_apply_type f x :=
        generic_apply_type_of_non_datatype_head hSel hTester
      have hTyEq :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTyEq]
        exact hNone
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
      have htf : term_has_non_none_type f := by
        cases hF with
        | inl hFun =>
            exact term_has_non_none_of_type_eq hFun (by simp)
        | inr hFun =>
            exact term_has_non_none_of_type_eq hFun (by simp)
      exact apply_type_has_no_none_components_of_non_none hTy ht (ihf htf)

private theorem term_type_has_no_none_components_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t -> type_has_no_none_components (__smtx_typeof t) := by
  let rec go (t : SmtTerm) (ht : term_has_non_none_type t) :
      type_has_no_none_components (__smtx_typeof t) := by
    match t with
    | SmtTerm.None =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.Boolean _ =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.Numeral _ =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.Rational _ =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.String _ =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.Binary _ _ =>
        exact binary_type_has_no_none_components_of_non_none ht
    | SmtTerm.Apply f x =>
        exact apply_term_type_has_no_none_components_of_non_none (ihf := fun hf => go f hf) ht
    | SmtTerm.Var _ _ =>
        exact var_type_has_no_none_components_of_non_none ht
    | SmtTerm.ite c t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
          exact term_has_non_none_of_type_eq h1 hT
        exact ite_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.eq _ _ =>
        exact eq_type_has_no_none_components_of_non_none ht
    | SmtTerm.exists _ _ _ =>
        exact exists_type_has_no_none_components_of_non_none ht
    | SmtTerm.forall _ _ _ =>
        exact forall_type_has_no_none_components_of_non_none ht
    | SmtTerm.choice_nth _ _ _ _ =>
        exact choice_type_has_no_none_components_of_non_none ht
    | SmtTerm.DtCons _ _ _ =>
        exact dt_cons_type_has_no_none_components_of_non_none ht
    | SmtTerm.DtSel _ _ _ _ =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.DtTester _ _ _ =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.UConst _ _ =>
        exact uconst_type_has_no_none_components_of_non_none ht
    | SmtTerm.not t1 =>
        exact bool_unop_type_has_no_none_components_of_non_none (typeof_not_eq t1) ht
    | SmtTerm.or t1 t2 =>
        exact bool_binop_type_has_no_none_components_of_non_none (typeof_or_eq t1 t2) ht
    | SmtTerm.and t1 t2 =>
        exact bool_binop_type_has_no_none_components_of_non_none (typeof_and_eq t1 t2) ht
    | SmtTerm.imp t1 t2 =>
        exact bool_binop_type_has_no_none_components_of_non_none (typeof_imp_eq t1 t2) ht
    | SmtTerm.xor t1 t2 =>
        exact bool_binop_type_has_no_none_components_of_non_none (typeof_xor_eq t1 t2) ht
    | SmtTerm.plus t1 t2 =>
        exact arith_binop_type_has_no_none_components_of_non_none (typeof_plus_eq t1 t2) ht
    | SmtTerm.neg t1 t2 =>
        exact arith_binop_type_has_no_none_components_of_non_none (typeof_neg_eq t1 t2) ht
    | SmtTerm.mult t1 t2 =>
        exact arith_binop_type_has_no_none_components_of_non_none (typeof_mult_eq t1 t2) ht
    | SmtTerm.lt t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_lt_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.leq t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_leq_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.gt t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_gt_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.geq t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_geq_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.to_real _ =>
        exact to_real_type_has_no_none_components_of_non_none ht
    | SmtTerm.to_int t1 =>
        exact real_ret_type_has_no_none_components_of_non_none
          (typeof_to_int_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.is_int t1 =>
        exact real_ret_type_has_no_none_components_of_non_none
          (typeof_is_int_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.abs t1 =>
        exact int_ret_type_has_no_none_components_of_non_none
          (typeof_abs_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.uneg t1 =>
        exact arith_unop_type_has_no_none_components_of_non_none (typeof_uneg_eq t1) ht
    | SmtTerm.div t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_div_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.mod t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_mod_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.multmult t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_multmult_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.divisible t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_divisible_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.int_pow2 t1 =>
        exact int_ret_type_has_no_none_components_of_non_none
          (typeof_int_pow2_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.int_log2 t1 =>
        exact int_ret_type_has_no_none_components_of_non_none
          (typeof_int_log2_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.div_total t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_div_total_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.mod_total t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_mod_total_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.multmult_total t1 t2 =>
        exact int_binop_ret_type_has_no_none_components_of_non_none
          (typeof_multmult_total_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.select t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact select_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.store t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact store_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.concat _ _ =>
        exact concat_type_has_no_none_components_of_non_none ht
    | SmtTerm.extract _ _ _ =>
        exact extract_type_has_no_none_components_of_non_none ht
    | SmtTerm.repeat _ _ =>
        exact repeat_type_has_no_none_components_of_non_none ht
    | SmtTerm.bvnot t1 =>
        exact bv_unop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvnot t1) = __smtx_typeof_bv_op_1 (__smtx_typeof t1) by
            rw [__smtx_typeof.eq_37]) ht
    | SmtTerm.bvand t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvand t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_38]) ht
    | SmtTerm.bvor t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvor t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_39]) ht
    | SmtTerm.bvnand t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvnand t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_40]) ht
    | SmtTerm.bvnor t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvnor t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_41]) ht
    | SmtTerm.bvxor t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvxor t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_42]) ht
    | SmtTerm.bvxnor t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvxnor t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_43]) ht
    | SmtTerm.bvcomp t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvcomp t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) (SmtType.BitVec 1) by
            rw [__smtx_typeof.eq_44]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvneg t1 =>
        exact bv_unop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvneg t1) = __smtx_typeof_bv_op_1 (__smtx_typeof t1) by
            rw [__smtx_typeof.eq_45]) ht
    | SmtTerm.bvadd t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvadd t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_46]) ht
    | SmtTerm.bvmul t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvmul t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_47]) ht
    | SmtTerm.bvudiv t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvudiv t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_48]) ht
    | SmtTerm.bvurem t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvurem t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_49]) ht
    | SmtTerm.bvsub t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsub t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_50]) ht
    | SmtTerm.bvsdiv t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsdiv t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_51]) ht
    | SmtTerm.bvsrem t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsrem t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_52]) ht
    | SmtTerm.bvsmod t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsmod t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_53]) ht
    | SmtTerm.bvult t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvult t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_54]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvule t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvule t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_55]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvugt t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvugt t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_56]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvuge t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvuge t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_57]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvslt t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvslt t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_58]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsle t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsle t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_59]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsgt t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsgt t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_60]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsge t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsge t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_61]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvshl t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvshl t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_62]) ht
    | SmtTerm.bvlshr t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvlshr t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_63]) ht
    | SmtTerm.bvashr t1 t2 =>
        exact bv_binop_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvashr t1 t2) =
              __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by
            rw [__smtx_typeof.eq_64]) ht
    | SmtTerm.zero_extend _ _ =>
        exact zero_extend_type_has_no_none_components_of_non_none ht
    | SmtTerm.sign_extend _ _ =>
        exact sign_extend_type_has_no_none_components_of_non_none ht
    | SmtTerm.rotate_left _ _ =>
        exact rotate_left_type_has_no_none_components_of_non_none ht
    | SmtTerm.rotate_right _ _ =>
        exact rotate_right_type_has_no_none_components_of_non_none ht
    | SmtTerm.bvuaddo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvuaddo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_69]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvnego t1 =>
        exact bv_unop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvnego t1) =
              __smtx_typeof_bv_op_1_ret (__smtx_typeof t1) SmtType.Bool by
            rw [__smtx_typeof.eq_70]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsaddo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsaddo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_71]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvumulo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvumulo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_72]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsmulo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsmulo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_73]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvusubo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvusubo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_74]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvssubo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvssubo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_75]) ht (by simp [type_has_no_none_components])
    | SmtTerm.bvsdivo t1 t2 =>
        exact bv_binop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.bvsdivo t1 t2) =
              __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
            rw [__smtx_typeof.eq_76]) ht (by simp [type_has_no_none_components])
    | SmtTerm.seq_empty _ =>
        exact seq_empty_type_has_no_none_components_of_non_none ht
    | SmtTerm.str_len t1 =>
        exact seq_op_1_ret_type_has_no_none_components_of_non_none
          (typeof_str_len_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_concat t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat) (typeof_str_concat_eq t1 t2) ht with
            ⟨T, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact seq_op_2_type_has_no_none_components_of_non_none
          (typeof_str_concat_eq t1 t2) ht (go t1 ht1)
    | SmtTerm.str_substr t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases str_substr_args_of_non_none ht with ⟨T, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact str_substr_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.str_contains t1 t2 =>
        exact seq_op_2_ret_type_has_no_none_components_of_non_none
          (typeof_str_contains_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_replace t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace) (typeof_str_replace_eq t1 t2 t3) ht with
            ⟨T, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact seq_op_3_type_has_no_none_components_of_non_none
          (typeof_str_replace_eq t1 t2 t3) ht (go t1 ht1)
    | SmtTerm.str_indexof _ _ _ =>
        exact str_indexof_type_has_no_none_components_of_non_none ht
    | SmtTerm.str_at t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases str_at_args_of_non_none ht with ⟨T, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact str_at_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.str_prefixof t1 t2 =>
        exact seq_char_binop_ret_type_has_no_none_components_of_non_none
          (typeof_str_prefixof_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_suffixof t1 t2 =>
        exact seq_char_binop_ret_type_has_no_none_components_of_non_none
          (typeof_str_suffixof_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_rev t1 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_arg_of_non_none (op := SmtTerm.str_rev) (typeof_str_rev_eq t1) ht with ⟨T, hArg⟩
          exact term_has_non_none_of_type_eq hArg (by simp)
        exact seq_op_1_type_has_no_none_components_of_non_none
          (typeof_str_rev_eq t1) ht (go t1 ht1)
    | SmtTerm.str_update t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases str_update_args_of_non_none ht with ⟨T, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact str_update_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.str_to_lower t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_lower_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_to_upper t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_upper_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_to_code t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_code_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_from_code t1 =>
        exact int_ret_type_has_no_none_components_of_non_none
          (typeof_str_from_code_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_is_digit t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_is_digit_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_to_int t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_int_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_from_int t1 =>
        exact int_ret_type_has_no_none_components_of_non_none
          (typeof_str_from_int_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_lt t1 t2 =>
        exact seq_char_binop_ret_type_has_no_none_components_of_non_none
          (typeof_str_lt_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_leq t1 t2 =>
        exact seq_char_binop_ret_type_has_no_none_components_of_non_none
          (typeof_str_leq_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.str_replace_all t1 t2 t3 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all) (typeof_str_replace_all_eq t1 t2 t3) ht with
            ⟨T, h1, h2, h3⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact seq_op_3_type_has_no_none_components_of_non_none
          (typeof_str_replace_all_eq t1 t2 t3) ht (go t1 ht1)
    | SmtTerm.str_replace_re t1 t2 t3 =>
        exact str_replace_re_type_has_no_none_components_of_non_none
          (typeof_str_replace_re_eq t1 t2 t3) ht
    | SmtTerm.str_replace_re_all t1 t2 t3 =>
        exact str_replace_re_type_has_no_none_components_of_non_none
          (typeof_str_replace_re_all_eq t1 t2 t3) ht
    | SmtTerm.str_indexof_re _ _ _ =>
        exact str_indexof_re_type_has_no_none_components_of_non_none ht
    | SmtTerm.re_allchar =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.re_none =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.re_all =>
        simp [__smtx_typeof, type_has_no_none_components]
    | SmtTerm.str_to_re t1 =>
        exact seq_char_ret_type_has_no_none_components_of_non_none
          (typeof_str_to_re_eq t1) ht (by simp [type_has_no_none_components])
    | SmtTerm.re_mult t1 =>
        exact reglan_unop_type_has_no_none_components_of_non_none
          (typeof_re_mult_eq t1) ht
    | SmtTerm.re_plus t1 =>
        exact reglan_unop_type_has_no_none_components_of_non_none
          (typeof_re_plus_eq t1) ht
    | SmtTerm.re_exp t1 t2 =>
        cases t1 with
        | Numeral _ =>
            exact re_exp_type_has_no_none_components_of_non_none ht
        | _ =>
            exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_exp]))
    | SmtTerm.re_opt t1 =>
        exact reglan_unop_type_has_no_none_components_of_non_none
          (typeof_re_opt_eq t1) ht
    | SmtTerm.re_comp t1 =>
        exact reglan_unop_type_has_no_none_components_of_non_none
          (typeof_re_comp_eq t1) ht
    | SmtTerm.re_range t1 t2 =>
        exact seq_char_binop_ret_type_has_no_none_components_of_non_none
          (typeof_re_range_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.re_concat t1 t2 =>
        exact reglan_binop_type_has_no_none_components_of_non_none
          (typeof_re_concat_eq t1 t2) ht
    | SmtTerm.re_inter t1 t2 =>
        exact reglan_binop_type_has_no_none_components_of_non_none
          (typeof_re_inter_eq t1 t2) ht
    | SmtTerm.re_union t1 t2 =>
        exact reglan_binop_type_has_no_none_components_of_non_none
          (typeof_re_union_eq t1 t2) ht
    | SmtTerm.re_diff t1 t2 =>
        exact reglan_binop_type_has_no_none_components_of_non_none
          (typeof_re_diff_eq t1 t2) ht
    | SmtTerm.re_loop t1 t2 t3 =>
        cases t1 with
        | Numeral _ =>
            cases t2 with
            | Numeral _ =>
                exact re_loop_type_has_no_none_components_of_non_none ht
            | _ =>
                exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_loop]))
        | _ =>
            exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_loop]))
    | SmtTerm.str_in_re t1 t2 =>
        exact seq_char_reglan_ret_type_has_no_none_components_of_non_none
          (typeof_str_in_re_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.seq_unit t1 =>
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type at ht ⊢
          by_cases hNone : __smtx_typeof t1 = SmtType.None
          · rw [__smtx_typeof.eq_118, hNone] at ht
            simp [native_ite, native_Teq] at ht
          · exact hNone
        exact seq_unit_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.seq_nth t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact seq_nth_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.set_empty _ =>
        exact set_empty_type_has_no_none_components_of_non_none ht
    | SmtTerm.set_singleton t1 =>
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type at ht ⊢
          by_cases hNone : __smtx_typeof t1 = SmtType.None
          · rw [__smtx_typeof.eq_121, hNone] at ht
            simp [native_ite, native_Teq] at ht
          · exact hNone
        exact set_singleton_type_has_no_none_components_of_non_none ht (go t1 ht1)
    | SmtTerm.set_union t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases set_binop_args_of_non_none (op := SmtTerm.set_union) (typeof_set_union_eq t1 t2) ht with
            ⟨A, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact set_binop_type_has_no_none_components_of_non_none
          (typeof_set_union_eq t1 t2) ht (go t1 ht1)
    | SmtTerm.set_inter t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases set_binop_args_of_non_none (op := SmtTerm.set_inter) (typeof_set_inter_eq t1 t2) ht with
            ⟨A, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact set_binop_type_has_no_none_components_of_non_none
          (typeof_set_inter_eq t1 t2) ht (go t1 ht1)
    | SmtTerm.set_minus t1 t2 =>
        have ht1 : term_has_non_none_type t1 := by
          rcases set_binop_args_of_non_none (op := SmtTerm.set_minus) (typeof_set_minus_eq t1 t2) ht with
            ⟨A, h1, h2⟩
          exact term_has_non_none_of_type_eq h1 (by simp)
        exact set_binop_type_has_no_none_components_of_non_none
          (typeof_set_minus_eq t1 t2) ht (go t1 ht1)
    | SmtTerm.set_member _ _ =>
        have hArgs := set_member_args_of_non_none ht
        rcases hArgs with ⟨A, h1, h2⟩
        rw [typeof_set_member_eq]
        simp [__smtx_typeof_set_member, native_ite, native_Teq, h1, h2, type_has_no_none_components]
    | SmtTerm.set_subset t1 t2 =>
        exact set_binop_ret_type_has_no_none_components_of_non_none
          (typeof_set_subset_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.qdiv t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_qdiv_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.qdiv_total t1 t2 =>
        exact arith_binop_ret_type_has_no_none_components_of_non_none
          (typeof_qdiv_total_eq t1 t2) ht (by simp [type_has_no_none_components])
    | SmtTerm.int_to_bv _ _ =>
        exact int_to_bv_type_has_no_none_components_of_non_none ht
    | SmtTerm.ubv_to_int t1 =>
        exact bv_unop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.ubv_to_int t1) =
              __smtx_typeof_bv_op_1_ret (__smtx_typeof t1) SmtType.Int by
            rw [__smtx_typeof.eq_130]) ht (by simp [type_has_no_none_components])
    | SmtTerm.sbv_to_int t1 =>
        exact bv_unop_ret_type_has_no_none_components_of_non_none
          (show __smtx_typeof (SmtTerm.sbv_to_int t1) =
              __smtx_typeof_bv_op_1_ret (__smtx_typeof t1) SmtType.Int by
            rw [__smtx_typeof.eq_131]) ht (by simp [type_has_no_none_components])
  exact go

/-- Every non-`None` SMT term lies in the supported preservation fragment. -/
theorem supported_preservation_term_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t -> supported_preservation_term t := by
  let rec go (t : SmtTerm) (ht : term_has_non_none_type t) :
      supported_preservation_term t := by
    match t with
    | SmtTerm.None =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.Boolean b =>
        exact supported_preservation_term.boolean b
    | SmtTerm.Numeral n =>
        exact supported_preservation_term.numeral n
    | SmtTerm.Rational q =>
        exact supported_preservation_term.rational q
    | SmtTerm.String s =>
        exact supported_preservation_term.string s
    | SmtTerm.Binary w n =>
        exact supported_preservation_term.binary w n
    | SmtTerm.Apply f x =>
        exact supported_apply_term_of_non_none
          (ihf := fun hf => go f hf)
          (ihx := fun hx => go x hx)
          ht
    | SmtTerm.Var _ _ =>
        exact supported_var_of_non_none ht
    | SmtTerm.ite c t1 t2 =>
        rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
        have htc : term_has_non_none_type c :=
          term_has_non_none_of_type_eq hc (by simp)
        have ht1 : term_has_non_none_type t1 :=
          term_has_non_none_of_type_eq h1 hT
        have ht2 : term_has_non_none_type t2 :=
          term_has_non_none_of_type_eq h2 hT
        exact supported_ite_of_non_none ht (go c htc) (go t1 ht1) (go t2 ht2)
    | SmtTerm.eq t1 t2 =>
        exact supported_preservation_term.eq t1 t2
    | SmtTerm.exists s T body =>
        exact supported_preservation_term.exists s T body
    | SmtTerm.forall s T body =>
        exact supported_preservation_term.forall s T body
    | SmtTerm.choice_nth _ _ _ _ =>
        exact supported_choice_of_non_none ht
    | SmtTerm.DtCons s d i =>
        exact supported_preservation_term.dt_cons s d i
    | SmtTerm.DtSel _ _ _ _ =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.DtTester _ _ _ =>
        exact False.elim (ht (by simp [__smtx_typeof]))
    | SmtTerm.UConst _ _ =>
        exact supported_uconst_of_non_none ht
    | SmtTerm.not t1 =>
        have h1 : __smtx_typeof t1 = SmtType.Bool :=
          bool_unop_arg_of_non_none (typeof_not_eq t1) ht
        have ht1 : term_has_non_none_type t1 :=
          term_has_non_none_of_type_eq h1 (by simp)
        exact supported_preservation_term.not ht1 (go t1 ht1)
    | SmtTerm.or t1 t2 =>
        have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) (typeof_or_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.or ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.and t1 t2 =>
        have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) (typeof_and_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.and ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.imp t1 t2 =>
        have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) (typeof_imp_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.imp ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.xor t1 t2 =>
        exact supported_preservation_term.xor t1 t2
    | SmtTerm.plus t1 t2 =>
        rcases arith_binop_args_of_non_none (op := SmtTerm.plus) (typeof_plus_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.plus ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.plus ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.neg t1 t2 =>
        rcases arith_binop_args_of_non_none (op := SmtTerm.neg) (typeof_neg_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.arith_neg ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.arith_neg ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.mult t1 t2 =>
        rcases arith_binop_args_of_non_none (op := SmtTerm.mult) (typeof_mult_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.mult ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.mult ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.lt t1 t2 =>
        rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt) (typeof_lt_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.lt ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.lt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.leq t1 t2 =>
        rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq) (typeof_leq_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.leq ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.leq ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.gt t1 t2 =>
        rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt) (typeof_gt_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.gt ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.gt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.geq t1 t2 =>
        rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq) (typeof_geq_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.geq ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.geq ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.to_real t1 =>
        rcases to_real_arg_of_non_none ht with hArg | hArg
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
          exact supported_preservation_term.to_real ht1 (go t1 ht1)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
          exact supported_preservation_term.to_real ht1 (go t1 ht1)
    | SmtTerm.to_int t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Real :=
          real_arg_of_non_none (op := SmtTerm.to_int) (typeof_to_int_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.to_int ht1 (go t1 ht1)
    | SmtTerm.is_int t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Real :=
          real_arg_of_non_none (op := SmtTerm.is_int) (typeof_is_int_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.is_int ht1 (go t1 ht1)
    | SmtTerm.abs t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Int := int_arg_of_non_none ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.abs ht1 (go t1 ht1)
    | SmtTerm.uneg t1 =>
        rcases arith_unop_arg_of_non_none (op := SmtTerm.uneg) (typeof_uneg_eq t1) ht with hArg | hArg
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
          exact supported_preservation_term.uneg ht1 (go t1 ht1)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
          exact supported_preservation_term.uneg ht1 (go t1 ht1)
    | SmtTerm.div t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.div) (typeof_div_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.div ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.mod t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod) (typeof_mod_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.mod ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.multmult t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.multmult) (typeof_multmult_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.multmult ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.divisible t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.divisible) (typeof_divisible_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.divisible ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.int_pow2 t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Int :=
          int_ret_arg_of_non_none (op := SmtTerm.int_pow2) (typeof_int_pow2_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.int_pow2 ht1 (go t1 ht1)
    | SmtTerm.int_log2 t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Int :=
          int_ret_arg_of_non_none (op := SmtTerm.int_log2) (typeof_int_log2_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.int_log2 ht1 (go t1 ht1)
    | SmtTerm.div_total t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.div_total) (typeof_div_total_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.div_total ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.mod_total t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod_total) (typeof_mod_total_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.mod_total ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.multmult_total t1 t2 =>
        have hArgs := int_binop_args_of_non_none (op := SmtTerm.multmult_total) (typeof_multmult_total_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.multmult_total ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.select t1 t2 =>
        rcases select_args_of_non_none ht with ⟨A, B, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have hMapTy := term_type_has_no_none_components_of_non_none t1 ht1
        have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
          simpa [h1] using hMapTy
        have hMapNN := type_has_no_none_components_map_components_non_none hMapTy'
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 hMapNN.1
        exact supported_select_of_non_none ht hMapTy (go t1 ht1) (go t2 ht2)
    | SmtTerm.store t1 t2 t3 =>
        rcases store_args_of_non_none ht with ⟨A, B, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have hMapTy := term_type_has_no_none_components_of_non_none t1 ht1
        have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
          simpa [h1] using hMapTy
        have hMapNN := type_has_no_none_components_map_components_non_none hMapTy'
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 hMapNN.1
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 hMapNN.2
        exact supported_store_of_non_none ht hMapTy (go t1 ht1) (go t2 ht2) (go t3 ht3)
    | SmtTerm.concat t1 t2 =>
        rcases bv_concat_args_of_non_none ht with ⟨w1, w2, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bv_concat ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.extract t1 t2 t3 =>
        rcases extract_args_of_non_none ht with ⟨i, j, w, h1, h2, h3, hj0, hji, hiw⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := by
          rw [h2]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.extract ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.repeat t1 t2 =>
        rcases repeat_args_of_non_none ht with ⟨i, w, h1, h2, hi1⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.repeat ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvnot t1 =>
        rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot) (by rw [__smtx_typeof.eq_37]) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.bvnot ht1 (go t1 ht1)
    | SmtTerm.bvand t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvand t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_38]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvand ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvor t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvor t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_39]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvor ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvnand t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvnand t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_40]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvnand ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvnor t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvnor t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_41]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvnor ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvxor t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvxor t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_42]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvxor ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvxnor t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvxnor t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_43]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvxnor ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvcomp t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvcomp t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) (SmtType.BitVec 1) by
              rw [__smtx_typeof.eq_44]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvcomp ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvneg t1 =>
        rcases bv_unop_arg_of_non_none (op := SmtTerm.bvneg) (by rw [__smtx_typeof.eq_45]) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.bvneg ht1 (go t1 ht1)
    | SmtTerm.bvadd t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvadd t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_46]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvadd ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvmul t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvmul t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_47]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvmul ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvudiv t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvudiv t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_48]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvudiv ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvurem t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvurem t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_49]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvurem ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsub t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvsub t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_50]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsub ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsdiv t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvsdiv t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_51]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsdiv ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsrem t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvsrem t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_52]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsrem ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsmod t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvsmod t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_53]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsmod ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvult t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvult t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_54]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvult ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvule t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvule t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_55]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvule ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvugt t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvugt t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_56]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvugt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvuge t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvuge t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_57]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvuge ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvslt t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvslt t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_58]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvslt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsle t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsle t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_59]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsle ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsgt t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsgt t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_60]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsgt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsge t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsge t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_61]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsge ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvshl t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvshl t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_62]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvshl ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvlshr t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvlshr t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_63]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvlshr ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvashr t1 t2 =>
        rcases bv_binop_args_of_non_none (show __smtx_typeof (SmtTerm.bvashr t1 t2) =
            __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2) by rw [__smtx_typeof.eq_64]) ht with
          ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvashr ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.zero_extend t1 t2 =>
        rcases zero_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.zero_extend ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.sign_extend t1 t2 =>
        rcases sign_extend_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.sign_extend ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.rotate_left t1 t2 =>
        rcases rotate_left_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.rotate_left ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.rotate_right t1 t2 =>
        rcases rotate_right_args_of_non_none ht with ⟨i, w, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.rotate_right ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvuaddo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvuaddo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_69]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvuaddo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvnego t1 =>
        rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.bvnego) (by rw [__smtx_typeof.eq_70]) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.bvnego ht1 (go t1 ht1)
    | SmtTerm.bvsaddo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsaddo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_71]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsaddo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvumulo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvumulo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_72]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvumulo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsmulo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsmulo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_73]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsmulo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvusubo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvusubo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_74]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvusubo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvssubo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvssubo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_75]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvssubo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.bvsdivo t1 t2 =>
        rcases bv_binop_ret_args_of_non_none (show __smtx_typeof (SmtTerm.bvsdivo t1 t2) =
            __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool by
              rw [__smtx_typeof.eq_76]) ht with ⟨w, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.bvsdivo ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.seq_empty _ =>
        exact supported_seq_empty_of_non_none ht
    | SmtTerm.str_len t1 =>
        rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len) (typeof_str_len_eq t1) ht with ⟨T, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_len ht1 (go t1 ht1)
    | SmtTerm.str_concat t1 t2 =>
        rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat) (typeof_str_concat_eq t1 t2) ht with
          ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.str_concat ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_substr t1 t2 t3 =>
        rcases str_substr_args_of_non_none ht with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_substr ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_contains t1 t2 =>
        rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains) (typeof_str_contains_eq t1 t2) ht with
          ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.str_contains ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_replace t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace) (typeof_str_replace_eq t1 t2 t3) ht with
          ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_replace ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_indexof t1 t2 t3 =>
        rcases str_indexof_args_of_non_none ht with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_indexof ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_at t1 t2 =>
        rcases str_at_args_of_non_none ht with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.str_at ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_prefixof t1 t2 =>
        have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_prefixof) (typeof_str_prefixof_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.str_prefixof ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_suffixof t1 t2 =>
        have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_suffixof) (typeof_str_suffixof_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.str_suffixof ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_rev t1 =>
        rcases seq_arg_of_non_none (op := SmtTerm.str_rev) (typeof_str_rev_eq t1) ht with ⟨T, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_rev ht1 (go t1 ht1)
    | SmtTerm.str_update t1 t2 t3 =>
        rcases str_update_args_of_non_none ht with ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_update ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_to_lower t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_lower) (typeof_str_to_lower_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_lower ht1 (go t1 ht1)
    | SmtTerm.str_to_upper t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_upper) (typeof_str_to_upper_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_upper ht1 (go t1 ht1)
    | SmtTerm.str_to_code t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_code) (typeof_str_to_code_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_code ht1 (go t1 ht1)
    | SmtTerm.str_from_code t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Int :=
          int_arg_of_non_none_ret (op := SmtTerm.str_from_code) (typeof_str_from_code_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_from_code ht1 (go t1 ht1)
    | SmtTerm.str_is_digit t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_is_digit) (typeof_str_is_digit_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_is_digit ht1 (go t1 ht1)
    | SmtTerm.str_to_int t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_int) (typeof_str_to_int_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_int ht1 (go t1 ht1)
    | SmtTerm.str_from_int t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Int :=
          int_arg_of_non_none_ret (op := SmtTerm.str_from_int) (typeof_str_from_int_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_from_int ht1 (go t1 ht1)
    | SmtTerm.str_lt t1 t2 =>
        have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_lt) (typeof_str_lt_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.str_lt ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_leq t1 t2 =>
        have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_leq) (typeof_str_leq_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.str_leq ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.str_replace_all t1 t2 t3 =>
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all) (typeof_str_replace_all_eq t1 t2 t3) ht with
          ⟨T, h1, h2, h3⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq h3 (by simp)
        exact supported_preservation_term.str_replace_all ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_replace_re t1 t2 t3 =>
        have hArgs := str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re) (typeof_str_replace_re_eq t1 t2 t3) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2.1 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
        exact supported_preservation_term.str_replace_re ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_replace_re_all t1 t2 t3 =>
        have hArgs := str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all) (typeof_str_replace_re_all_eq t1 t2 t3) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2.1 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
        exact supported_preservation_term.str_replace_re_all ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.str_indexof_re t1 t2 t3 =>
        have hArgs := str_indexof_re_args_of_non_none ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2.1 (by simp)
        have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
        exact supported_preservation_term.str_indexof_re ht1 (go t1 ht1) ht2 (go t2 ht2) ht3 (go t3 ht3)
    | SmtTerm.re_allchar =>
        exact supported_preservation_term.re_allchar
    | SmtTerm.re_none =>
        exact supported_preservation_term.re_none
    | SmtTerm.re_all =>
        exact supported_preservation_term.re_all
    | SmtTerm.str_to_re t1 =>
        have hArg : __smtx_typeof t1 = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_re) (typeof_str_to_re_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.str_to_re ht1 (go t1 ht1)
    | SmtTerm.re_mult t1 =>
        have hArg : __smtx_typeof t1 = SmtType.RegLan :=
          reglan_arg_of_non_none (op := SmtTerm.re_mult) (typeof_re_mult_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.re_mult ht1 (go t1 ht1)
    | SmtTerm.re_plus t1 =>
        have hArg : __smtx_typeof t1 = SmtType.RegLan :=
          reglan_arg_of_non_none (op := SmtTerm.re_plus) (typeof_re_plus_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.re_plus ht1 (go t1 ht1)
    | SmtTerm.re_exp t1 t2 =>
        cases t1 with
        | Numeral n =>
            have hArgs := re_exp_arg_of_non_none ht
            have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
            exact supported_preservation_term.re_exp n ht2 (go t2 ht2)
        | _ =>
            exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_exp]))
    | SmtTerm.re_opt t1 =>
        have hArg : __smtx_typeof t1 = SmtType.RegLan :=
          reglan_arg_of_non_none (op := SmtTerm.re_opt) (typeof_re_opt_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.re_opt ht1 (go t1 ht1)
    | SmtTerm.re_comp t1 =>
        have hArg : __smtx_typeof t1 = SmtType.RegLan :=
          reglan_arg_of_non_none (op := SmtTerm.re_comp) (typeof_re_comp_eq t1) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.re_comp ht1 (go t1 ht1)
    | SmtTerm.re_range t1 t2 =>
        have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.re_range) (typeof_re_range_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_range ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_concat t1 t2 =>
        have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_concat) (typeof_re_concat_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_concat ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_inter t1 t2 =>
        have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_inter) (typeof_re_inter_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_inter ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_union t1 t2 =>
        have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_union) (typeof_re_union_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_union ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_diff t1 t2 =>
        have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_diff) (typeof_re_diff_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.re_diff ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.re_loop t1 t2 t3 =>
        cases t1 with
        | Numeral n1 =>
            cases t2 with
            | Numeral n2 =>
                have hArgs := re_loop_arg_of_non_none ht
                have ht3 : term_has_non_none_type t3 := term_has_non_none_of_type_eq hArgs.2.2 (by simp)
                exact supported_preservation_term.re_loop n1 n2 ht3 (go t3 ht3)
            | _ =>
                exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_loop]))
        | _ =>
            exact False.elim (ht (by simp [__smtx_typeof, __smtx_typeof_re_loop]))
    | SmtTerm.str_in_re t1 t2 =>
        have hArgs := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re) (typeof_str_in_re_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
        exact supported_preservation_term.str_in_re ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.seq_unit t1 =>
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type at ht ⊢
          by_cases hNone : __smtx_typeof t1 = SmtType.None
          · rw [__smtx_typeof.eq_118, hNone] at ht
            simp [native_ite, native_Teq] at ht
          · exact hNone
        exact supported_seq_unit_of_non_none ht (go t1 ht1)
    | SmtTerm.seq_nth t1 t2 =>
        rcases seq_nth_args_of_non_none ht with ⟨T, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_seq_nth_of_non_none ht (go t1 ht1) (go t2 ht2)
    | SmtTerm.set_empty _ =>
        exact supported_set_empty_of_non_none ht
    | SmtTerm.set_singleton t1 =>
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type at ht ⊢
          by_cases hNone : __smtx_typeof t1 = SmtType.None
          · rw [__smtx_typeof.eq_121, hNone] at ht
            simp [native_ite, native_Teq] at ht
          · exact hNone
        exact supported_set_singleton_of_non_none ht (go t1 ht1)
    | SmtTerm.set_union t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_union) (typeof_set_union_eq t1 t2) ht with
          ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.set_union ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.set_inter t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_inter) (typeof_set_inter_eq t1 t2) ht with
          ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.set_inter ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.set_minus t1 t2 =>
        rcases set_binop_args_of_non_none (op := SmtTerm.set_minus) (typeof_set_minus_eq t1 t2) ht with
          ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.set_minus ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.set_member t1 t2 =>
        rcases set_member_args_of_non_none ht with ⟨A, h1, h2⟩
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        have hSetTy := term_type_has_no_none_components_of_non_none t2 ht2
        have hSetTy' : type_has_no_none_components (SmtType.Set A) := by
          simpa [h2] using hSetTy
        have hA : A ≠ SmtType.None := type_has_no_none_components_set_component_non_none hSetTy'
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 hA
        exact supported_preservation_term.set_member ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.set_subset t1 t2 =>
        rcases set_binop_ret_args_of_non_none (op := SmtTerm.set_subset) (typeof_set_subset_eq t1 t2) ht with
          ⟨A, h1, h2⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq h1 (by simp)
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.set_subset ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.qdiv t1 t2 =>
        rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (typeof_qdiv_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.qdiv ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.qdiv ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.qdiv_total t1 t2 =>
        rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv_total) (typeof_qdiv_total_eq t1 t2) ht with hArgs | hArgs
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.qdiv_total ht1 (go t1 ht1) ht2 (go t2 ht2)
        · have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArgs.1 (by simp)
          have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq hArgs.2 (by simp)
          exact supported_preservation_term.qdiv_total ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.int_to_bv t1 t2 =>
        rcases int_to_bv_args_of_non_none ht with ⟨i, h1, h2, hi0⟩
        have ht1 : term_has_non_none_type t1 := by
          rw [h1]
          simp [term_has_non_none_type, __smtx_typeof]
        have ht2 : term_has_non_none_type t2 := term_has_non_none_of_type_eq h2 (by simp)
        exact supported_preservation_term.int_to_bv ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.ubv_to_int t1 =>
        rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.ubv_to_int) (by rw [__smtx_typeof.eq_130]) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.ubv_to_int ht1 (go t1 ht1)
    | SmtTerm.sbv_to_int t1 =>
        rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.sbv_to_int) (by rw [__smtx_typeof.eq_131]) ht with ⟨w, hArg⟩
        have ht1 : term_has_non_none_type t1 := term_has_non_none_of_type_eq hArg (by simp)
        exact supported_preservation_term.sbv_to_int ht1 (go t1 ht1)
  exact go

/-- Main type-preservation theorem for evaluation of non-`None` SMT terms in total typed models. -/
theorem type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  exact supported_type_preservation M hM t ht
    (supported_preservation_term_of_non_none t ht)

/-- Backwards-compatible wrapper for `type_preservation`. -/
theorem smt_model_eval_preserves_type_of_non_none
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
    term_has_non_none_type t ->
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  intro ht
  exact type_preservation M hM t ht

/-- Derives SMT evaluation type preservation for terms in the supported fragment. -/
theorem smt_model_eval_preserves_type_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (T : SmtType)
    (hTy : __smtx_typeof t = T)
    (hNonNone : T ≠ SmtType.None)
    (_hs : supported_preservation_term t) :
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact hNonNone
  simpa [hTy] using
    type_preservation M hM t hNN

/-- Derives Boolean-value evaluation for supported Boolean-typed SMT terms. -/
theorem smt_model_eval_bool_is_boolean_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool)
    (hs : supported_preservation_term t) :
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool :=
    smt_model_eval_preserves_type_of_supported M hM t SmtType.Bool hTy (by simp) hs
  exact bool_value_canonical hPres

/-- Backwards-compatible wrapper around `type_preservation` for explicit type equalities. -/
theorem smt_model_eval_preserves_type
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (T : SmtType) :
  __smtx_typeof t = T ->
  T ≠ SmtType.None ->
  type_inhabited T ->
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  intro hTy hNonNone _hInh
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact hNonNone
  simpa [hTy] using
    smt_model_eval_preserves_type_of_non_none M hM t hNN

/-- States that evaluating a Boolean-typed SMT term yields a Boolean value. -/
theorem smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
  __smtx_typeof t = SmtType.Bool ->
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  intro hTy
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact bool_value_canonical hPres

/-- Shows that total typed SMT models exist. -/
theorem total_typed_model_nonvacuous :
    ∃ M : SmtModel, model_total_typed M :=
  exists_total_typed_model

end Smtm
