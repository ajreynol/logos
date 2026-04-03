import Cpc.Proofs.CheckerCore
import Cpc.Proofs.Rules.Support
import Cpc.Proofs.Rules.Scope
import Cpc.Proofs.Rules.Process_scope
import Cpc.Proofs.Rules.Ite_eq
import Cpc.Proofs.Rules.Split
import Cpc.Proofs.Rules.Resolution
import Cpc.Proofs.Rules.Chain_resolution
import Cpc.Proofs.Rules.Chain_m_resolution
import Cpc.Proofs.Rules.Factoring
import Cpc.Proofs.Rules.Reordering
import Cpc.Proofs.Rules.Eq_resolve
import Cpc.Proofs.Rules.Modus_ponens
import Cpc.Proofs.Rules.Not_not_elim
import Cpc.Proofs.Rules.Contra
import Cpc.Proofs.Rules.And_elim
import Cpc.Proofs.Rules.And_intro
import Cpc.Proofs.Rules.Not_or_elim
import Cpc.Proofs.Rules.Implies_elim
import Cpc.Proofs.Rules.Not_implies_elim1
import Cpc.Proofs.Rules.Not_implies_elim2
import Cpc.Proofs.Rules.Equiv_elim1
import Cpc.Proofs.Rules.Equiv_elim2
import Cpc.Proofs.Rules.Not_equiv_elim1
import Cpc.Proofs.Rules.Not_equiv_elim2
import Cpc.Proofs.Rules.Xor_elim1
import Cpc.Proofs.Rules.Xor_elim2
import Cpc.Proofs.Rules.Not_xor_elim1
import Cpc.Proofs.Rules.Not_xor_elim2
import Cpc.Proofs.Rules.Ite_elim1
import Cpc.Proofs.Rules.Ite_elim2
import Cpc.Proofs.Rules.Not_ite_elim1
import Cpc.Proofs.Rules.Not_ite_elim2
import Cpc.Proofs.Rules.Not_and
import Cpc.Proofs.Rules.Cnf_and_pos
import Cpc.Proofs.Rules.Cnf_and_neg
import Cpc.Proofs.Rules.Cnf_or_pos
import Cpc.Proofs.Rules.Cnf_or_neg
import Cpc.Proofs.Rules.Cnf_implies_pos
import Cpc.Proofs.Rules.Cnf_implies_neg1
import Cpc.Proofs.Rules.Cnf_implies_neg2
import Cpc.Proofs.Rules.Cnf_equiv_pos1
import Cpc.Proofs.Rules.Cnf_equiv_pos2
import Cpc.Proofs.Rules.Cnf_equiv_neg1
import Cpc.Proofs.Rules.Cnf_equiv_neg2
import Cpc.Proofs.Rules.Cnf_xor_pos1
import Cpc.Proofs.Rules.Cnf_xor_pos2
import Cpc.Proofs.Rules.Cnf_xor_neg1
import Cpc.Proofs.Rules.Cnf_xor_neg2
import Cpc.Proofs.Rules.Cnf_ite_pos1
import Cpc.Proofs.Rules.Cnf_ite_pos2
import Cpc.Proofs.Rules.Cnf_ite_pos3
import Cpc.Proofs.Rules.Cnf_ite_neg1
import Cpc.Proofs.Rules.Cnf_ite_neg2
import Cpc.Proofs.Rules.Cnf_ite_neg3
import Cpc.Proofs.Rules.Arrays_read_over_write
import Cpc.Proofs.Rules.Arrays_read_over_write_contra
import Cpc.Proofs.Rules.Arrays_read_over_write_1
import Cpc.Proofs.Rules.Arrays_ext
import Cpc.Proofs.Rules.Refl
import Cpc.Proofs.Rules.Symm
import Cpc.Proofs.Rules.Trans
import Cpc.Proofs.Rules.Cong
import Cpc.Proofs.Rules.Nary_cong
import Cpc.Proofs.Rules.Pairwise_cong
import Cpc.Proofs.Rules.True_intro
import Cpc.Proofs.Rules.True_elim
import Cpc.Proofs.Rules.False_intro
import Cpc.Proofs.Rules.False_elim
import Cpc.Proofs.Rules.Ho_cong
import Cpc.Proofs.Rules.Distinct_elim
import Cpc.Proofs.Rules.Distinct_true
import Cpc.Proofs.Rules.Distinct_false
import Cpc.Proofs.Rules.Arith_sum_ub
import Cpc.Proofs.Rules.Arith_mult_pos
import Cpc.Proofs.Rules.Arith_mult_neg
import Cpc.Proofs.Rules.Arith_trichotomy
import Cpc.Proofs.Rules.Int_tight_ub
import Cpc.Proofs.Rules.Int_tight_lb
import Cpc.Proofs.Rules.Arith_mult_tangent
import Cpc.Proofs.Rules.Arith_mult_sign
import Cpc.Proofs.Rules.Arith_mult_abs_comparison
import Cpc.Proofs.Rules.Arith_reduction
import Cpc.Proofs.Rules.Arith_poly_norm
import Cpc.Proofs.Rules.Arith_poly_norm_rel
import Cpc.Proofs.Rules.Bv_repeat_elim
import Cpc.Proofs.Rules.Bv_smulo_elim
import Cpc.Proofs.Rules.Bv_umulo_elim
import Cpc.Proofs.Rules.Bv_bitwise_slicing
import Cpc.Proofs.Rules.Bv_bitblast_step
import Cpc.Proofs.Rules.Bv_poly_norm
import Cpc.Proofs.Rules.Bv_poly_norm_eq
import Cpc.Proofs.Rules.String_length_pos
import Cpc.Proofs.Rules.String_length_non_empty
import Cpc.Proofs.Rules.Concat_eq
import Cpc.Proofs.Rules.Concat_unify
import Cpc.Proofs.Rules.Concat_csplit
import Cpc.Proofs.Rules.Concat_split
import Cpc.Proofs.Rules.Concat_lprop
import Cpc.Proofs.Rules.Concat_cprop
import Cpc.Proofs.Rules.String_decompose
import Cpc.Proofs.Rules.Exists_string_length
import Cpc.Proofs.Rules.String_code_inj
import Cpc.Proofs.Rules.String_seq_unit_inj
import Cpc.Proofs.Rules.Re_inter
import Cpc.Proofs.Rules.Re_concat
import Cpc.Proofs.Rules.Re_unfold_pos
import Cpc.Proofs.Rules.Re_unfold_neg_concat_fixed
import Cpc.Proofs.Rules.Re_unfold_neg
import Cpc.Proofs.Rules.String_ext
import Cpc.Proofs.Rules.String_reduction
import Cpc.Proofs.Rules.String_eager_reduction
import Cpc.Proofs.Rules.Arith_string_pred_entail
import Cpc.Proofs.Rules.Arith_string_pred_safe_approx
import Cpc.Proofs.Rules.Str_in_re_eval
import Cpc.Proofs.Rules.Str_in_re_consume
import Cpc.Proofs.Rules.Re_loop_elim
import Cpc.Proofs.Rules.Re_eq_elim
import Cpc.Proofs.Rules.Re_inter_inclusion
import Cpc.Proofs.Rules.Re_union_inclusion
import Cpc.Proofs.Rules.Str_in_re_concat_star_char
import Cpc.Proofs.Rules.Str_in_re_sigma
import Cpc.Proofs.Rules.Str_in_re_sigma_star
import Cpc.Proofs.Rules.Str_ctn_multiset_subset
import Cpc.Proofs.Rules.Str_overlap_split_ctn
import Cpc.Proofs.Rules.Str_overlap_endpoints_ctn
import Cpc.Proofs.Rules.Str_overlap_endpoints_indexof
import Cpc.Proofs.Rules.Str_overlap_endpoints_replace
import Cpc.Proofs.Rules.Str_indexof_re_eval
import Cpc.Proofs.Rules.Str_replace_re_eval
import Cpc.Proofs.Rules.Str_replace_re_all_eval
import Cpc.Proofs.Rules.Seq_eval_op
import Cpc.Proofs.Rules.Sets_singleton_inj
import Cpc.Proofs.Rules.Sets_ext
import Cpc.Proofs.Rules.Sets_eval_op
import Cpc.Proofs.Rules.Sets_insert_elim
import Cpc.Proofs.Rules.Ubv_to_int_elim
import Cpc.Proofs.Rules.Int_to_bv_elim
import Cpc.Proofs.Rules.Instantiate
import Cpc.Proofs.Rules.Skolemize
import Cpc.Proofs.Rules.Skolem_intro
import Cpc.Proofs.Rules.Alpha_equiv
import Cpc.Proofs.Rules.Beta_reduce
import Cpc.Proofs.Rules.Quant_var_reordering
import Cpc.Proofs.Rules.Exists_elim
import Cpc.Proofs.Rules.Quant_unused_vars
import Cpc.Proofs.Rules.Quant_merge_prenex
import Cpc.Proofs.Rules.Quant_miniscope_and
import Cpc.Proofs.Rules.Quant_miniscope_or
import Cpc.Proofs.Rules.Quant_miniscope_ite
import Cpc.Proofs.Rules.Quant_var_elim_eq
import Cpc.Proofs.Rules.Quant_dt_split
import Cpc.Proofs.Rules.Dt_split
import Cpc.Proofs.Rules.Dt_inst
import Cpc.Proofs.Rules.Dt_collapse_selector
import Cpc.Proofs.Rules.Dt_collapse_tester
import Cpc.Proofs.Rules.Dt_collapse_tester_singleton
import Cpc.Proofs.Rules.Dt_cons_eq
import Cpc.Proofs.Rules.Dt_cons_eq_clash
import Cpc.Proofs.Rules.Dt_cycle
import Cpc.Proofs.Rules.Dt_collapse_updater
import Cpc.Proofs.Rules.Dt_updater_elim
import Cpc.Proofs.Rules.Arith_div_total_zero_real
import Cpc.Proofs.Rules.Arith_div_total_zero_int
import Cpc.Proofs.Rules.Arith_int_div_total
import Cpc.Proofs.Rules.Arith_int_div_total_one
import Cpc.Proofs.Rules.Arith_int_div_total_zero
import Cpc.Proofs.Rules.Arith_int_div_total_neg
import Cpc.Proofs.Rules.Arith_int_mod_total
import Cpc.Proofs.Rules.Arith_int_mod_total_one
import Cpc.Proofs.Rules.Arith_int_mod_total_zero
import Cpc.Proofs.Rules.Arith_int_mod_total_neg
import Cpc.Proofs.Rules.Arith_elim_gt
import Cpc.Proofs.Rules.Arith_elim_lt
import Cpc.Proofs.Rules.Arith_elim_int_gt
import Cpc.Proofs.Rules.Arith_elim_int_lt
import Cpc.Proofs.Rules.Arith_elim_leq
import Cpc.Proofs.Rules.Arith_leq_norm
import Cpc.Proofs.Rules.Arith_geq_tighten
import Cpc.Proofs.Rules.Arith_geq_norm1_int
import Cpc.Proofs.Rules.Arith_geq_norm1_real
import Cpc.Proofs.Rules.Arith_eq_elim_real
import Cpc.Proofs.Rules.Arith_eq_elim_int
import Cpc.Proofs.Rules.Arith_to_int_elim_to_real
import Cpc.Proofs.Rules.Arith_mod_over_mod_1
import Cpc.Proofs.Rules.Arith_mod_over_mod
import Cpc.Proofs.Rules.Arith_mod_over_mod_mult
import Cpc.Proofs.Rules.Arith_int_eq_conflict
import Cpc.Proofs.Rules.Arith_int_geq_tighten
import Cpc.Proofs.Rules.Arith_divisible_elim
import Cpc.Proofs.Rules.Arith_abs_eq
import Cpc.Proofs.Rules.Arith_abs_int_gt
import Cpc.Proofs.Rules.Arith_abs_real_gt
import Cpc.Proofs.Rules.Arith_geq_ite_lift
import Cpc.Proofs.Rules.Arith_leq_ite_lift
import Cpc.Proofs.Rules.Arith_min_lt1
import Cpc.Proofs.Rules.Arith_min_lt2
import Cpc.Proofs.Rules.Arith_max_geq1
import Cpc.Proofs.Rules.Arith_max_geq2
import Cpc.Proofs.Rules.Array_read_over_write
import Cpc.Proofs.Rules.Array_read_over_write2
import Cpc.Proofs.Rules.Array_store_overwrite
import Cpc.Proofs.Rules.Array_store_self
import Cpc.Proofs.Rules.Array_read_over_write_split
import Cpc.Proofs.Rules.Array_store_swap
import Cpc.Proofs.Rules.Bool_double_not_elim
import Cpc.Proofs.Rules.Bool_not_true
import Cpc.Proofs.Rules.Bool_not_false
import Cpc.Proofs.Rules.Bool_eq_true
import Cpc.Proofs.Rules.Bool_eq_false
import Cpc.Proofs.Rules.Bool_eq_nrefl
import Cpc.Proofs.Rules.Bool_impl_false1
import Cpc.Proofs.Rules.Bool_impl_false2
import Cpc.Proofs.Rules.Bool_impl_true1
import Cpc.Proofs.Rules.Bool_impl_true2
import Cpc.Proofs.Rules.Bool_impl_elim
import Cpc.Proofs.Rules.Bool_dual_impl_eq
import Cpc.Proofs.Rules.Bool_and_conf
import Cpc.Proofs.Rules.Bool_and_conf2
import Cpc.Proofs.Rules.Bool_or_taut
import Cpc.Proofs.Rules.Bool_or_taut2
import Cpc.Proofs.Rules.Bool_or_de_morgan
import Cpc.Proofs.Rules.Bool_implies_de_morgan
import Cpc.Proofs.Rules.Bool_and_de_morgan
import Cpc.Proofs.Rules.Bool_or_and_distrib
import Cpc.Proofs.Rules.Bool_implies_or_distrib
import Cpc.Proofs.Rules.Bool_xor_refl
import Cpc.Proofs.Rules.Bool_xor_nrefl
import Cpc.Proofs.Rules.Bool_xor_false
import Cpc.Proofs.Rules.Bool_xor_true
import Cpc.Proofs.Rules.Bool_xor_comm
import Cpc.Proofs.Rules.Bool_xor_elim
import Cpc.Proofs.Rules.Bool_not_xor_elim
import Cpc.Proofs.Rules.Bool_not_eq_elim1
import Cpc.Proofs.Rules.Bool_not_eq_elim2
import Cpc.Proofs.Rules.Ite_neg_branch
import Cpc.Proofs.Rules.Ite_then_true
import Cpc.Proofs.Rules.Ite_else_false
import Cpc.Proofs.Rules.Ite_then_false
import Cpc.Proofs.Rules.Ite_else_true
import Cpc.Proofs.Rules.Ite_then_lookahead_self
import Cpc.Proofs.Rules.Ite_else_lookahead_self
import Cpc.Proofs.Rules.Ite_then_lookahead_not_self
import Cpc.Proofs.Rules.Ite_else_lookahead_not_self
import Cpc.Proofs.Rules.Ite_expand
import Cpc.Proofs.Rules.Bool_not_ite_elim
import Cpc.Proofs.Rules.Ite_true_cond
import Cpc.Proofs.Rules.Ite_false_cond
import Cpc.Proofs.Rules.Ite_not_cond
import Cpc.Proofs.Rules.Ite_eq_branch
import Cpc.Proofs.Rules.Ite_then_lookahead
import Cpc.Proofs.Rules.Ite_else_lookahead
import Cpc.Proofs.Rules.Ite_then_neg_lookahead
import Cpc.Proofs.Rules.Ite_else_neg_lookahead
import Cpc.Proofs.Rules.Bv_concat_extract_merge
import Cpc.Proofs.Rules.Bv_extract_extract
import Cpc.Proofs.Rules.Bv_extract_whole
import Cpc.Proofs.Rules.Bv_extract_concat_1
import Cpc.Proofs.Rules.Bv_extract_concat_2
import Cpc.Proofs.Rules.Bv_extract_concat_3
import Cpc.Proofs.Rules.Bv_extract_concat_4
import Cpc.Proofs.Rules.Bv_eq_extract_elim1
import Cpc.Proofs.Rules.Bv_eq_extract_elim2
import Cpc.Proofs.Rules.Bv_eq_extract_elim3
import Cpc.Proofs.Rules.Bv_extract_not
import Cpc.Proofs.Rules.Bv_extract_sign_extend_1
import Cpc.Proofs.Rules.Bv_extract_sign_extend_2
import Cpc.Proofs.Rules.Bv_extract_sign_extend_3
import Cpc.Proofs.Rules.Bv_not_xor
import Cpc.Proofs.Rules.Bv_and_simplify_1
import Cpc.Proofs.Rules.Bv_and_simplify_2
import Cpc.Proofs.Rules.Bv_or_simplify_1
import Cpc.Proofs.Rules.Bv_or_simplify_2
import Cpc.Proofs.Rules.Bv_xor_simplify_1
import Cpc.Proofs.Rules.Bv_xor_simplify_2
import Cpc.Proofs.Rules.Bv_xor_simplify_3
import Cpc.Proofs.Rules.Bv_ult_add_one
import Cpc.Proofs.Rules.Bv_mult_slt_mult_1
import Cpc.Proofs.Rules.Bv_mult_slt_mult_2
import Cpc.Proofs.Rules.Bv_commutative_xor
import Cpc.Proofs.Rules.Bv_commutative_comp
import Cpc.Proofs.Rules.Bv_zero_extend_eliminate_0
import Cpc.Proofs.Rules.Bv_sign_extend_eliminate_0
import Cpc.Proofs.Rules.Bv_not_neq
import Cpc.Proofs.Rules.Bv_ult_ones
import Cpc.Proofs.Rules.Bv_concat_merge_const
import Cpc.Proofs.Rules.Bv_commutative_add
import Cpc.Proofs.Rules.Bv_sub_eliminate
import Cpc.Proofs.Rules.Bv_ite_width_one
import Cpc.Proofs.Rules.Bv_ite_width_one_not
import Cpc.Proofs.Rules.Bv_eq_xor_solve
import Cpc.Proofs.Rules.Bv_eq_not_solve
import Cpc.Proofs.Rules.Bv_ugt_eliminate
import Cpc.Proofs.Rules.Bv_uge_eliminate
import Cpc.Proofs.Rules.Bv_sgt_eliminate
import Cpc.Proofs.Rules.Bv_sge_eliminate
import Cpc.Proofs.Rules.Bv_sle_eliminate
import Cpc.Proofs.Rules.Bv_redor_eliminate
import Cpc.Proofs.Rules.Bv_redand_eliminate
import Cpc.Proofs.Rules.Bv_ule_eliminate
import Cpc.Proofs.Rules.Bv_comp_eliminate
import Cpc.Proofs.Rules.Bv_rotate_left_eliminate_1
import Cpc.Proofs.Rules.Bv_rotate_left_eliminate_2
import Cpc.Proofs.Rules.Bv_rotate_right_eliminate_1
import Cpc.Proofs.Rules.Bv_rotate_right_eliminate_2
import Cpc.Proofs.Rules.Bv_nand_eliminate
import Cpc.Proofs.Rules.Bv_nor_eliminate
import Cpc.Proofs.Rules.Bv_xnor_eliminate
import Cpc.Proofs.Rules.Bv_sdiv_eliminate
import Cpc.Proofs.Rules.Bv_zero_extend_eliminate
import Cpc.Proofs.Rules.Bv_uaddo_eliminate
import Cpc.Proofs.Rules.Bv_saddo_eliminate
import Cpc.Proofs.Rules.Bv_sdivo_eliminate
import Cpc.Proofs.Rules.Bv_smod_eliminate
import Cpc.Proofs.Rules.Bv_srem_eliminate
import Cpc.Proofs.Rules.Bv_usubo_eliminate
import Cpc.Proofs.Rules.Bv_ssubo_eliminate
import Cpc.Proofs.Rules.Bv_nego_eliminate
import Cpc.Proofs.Rules.Bv_ite_equal_children
import Cpc.Proofs.Rules.Bv_ite_const_children_1
import Cpc.Proofs.Rules.Bv_ite_const_children_2
import Cpc.Proofs.Rules.Bv_ite_equal_cond_1
import Cpc.Proofs.Rules.Bv_ite_equal_cond_2
import Cpc.Proofs.Rules.Bv_ite_equal_cond_3
import Cpc.Proofs.Rules.Bv_ite_merge_then_if
import Cpc.Proofs.Rules.Bv_ite_merge_else_if
import Cpc.Proofs.Rules.Bv_ite_merge_then_else
import Cpc.Proofs.Rules.Bv_ite_merge_else_else
import Cpc.Proofs.Rules.Bv_shl_by_const_0
import Cpc.Proofs.Rules.Bv_shl_by_const_1
import Cpc.Proofs.Rules.Bv_shl_by_const_2
import Cpc.Proofs.Rules.Bv_lshr_by_const_0
import Cpc.Proofs.Rules.Bv_lshr_by_const_1
import Cpc.Proofs.Rules.Bv_lshr_by_const_2
import Cpc.Proofs.Rules.Bv_ashr_by_const_0
import Cpc.Proofs.Rules.Bv_ashr_by_const_1
import Cpc.Proofs.Rules.Bv_ashr_by_const_2
import Cpc.Proofs.Rules.Bv_and_concat_pullup
import Cpc.Proofs.Rules.Bv_or_concat_pullup
import Cpc.Proofs.Rules.Bv_xor_concat_pullup
import Cpc.Proofs.Rules.Bv_and_concat_pullup2
import Cpc.Proofs.Rules.Bv_or_concat_pullup2
import Cpc.Proofs.Rules.Bv_xor_concat_pullup2
import Cpc.Proofs.Rules.Bv_and_concat_pullup3
import Cpc.Proofs.Rules.Bv_or_concat_pullup3
import Cpc.Proofs.Rules.Bv_xor_concat_pullup3
import Cpc.Proofs.Rules.Bv_xor_duplicate
import Cpc.Proofs.Rules.Bv_xor_ones
import Cpc.Proofs.Rules.Bv_xor_not
import Cpc.Proofs.Rules.Bv_not_idemp
import Cpc.Proofs.Rules.Bv_ult_zero_1
import Cpc.Proofs.Rules.Bv_ult_zero_2
import Cpc.Proofs.Rules.Bv_ult_self
import Cpc.Proofs.Rules.Bv_lt_self
import Cpc.Proofs.Rules.Bv_ule_self
import Cpc.Proofs.Rules.Bv_ule_zero
import Cpc.Proofs.Rules.Bv_zero_ule
import Cpc.Proofs.Rules.Bv_sle_self
import Cpc.Proofs.Rules.Bv_ule_max
import Cpc.Proofs.Rules.Bv_not_ult
import Cpc.Proofs.Rules.Bv_mult_pow2_1
import Cpc.Proofs.Rules.Bv_mult_pow2_2
import Cpc.Proofs.Rules.Bv_mult_pow2_2b
import Cpc.Proofs.Rules.Bv_extract_mult_leading_bit
import Cpc.Proofs.Rules.Bv_udiv_pow2_not_one
import Cpc.Proofs.Rules.Bv_udiv_zero
import Cpc.Proofs.Rules.Bv_udiv_one
import Cpc.Proofs.Rules.Bv_urem_pow2_not_one
import Cpc.Proofs.Rules.Bv_urem_one
import Cpc.Proofs.Rules.Bv_urem_self
import Cpc.Proofs.Rules.Bv_shl_zero
import Cpc.Proofs.Rules.Bv_lshr_zero
import Cpc.Proofs.Rules.Bv_ashr_zero
import Cpc.Proofs.Rules.Bv_ugt_urem
import Cpc.Proofs.Rules.Bv_ult_one
import Cpc.Proofs.Rules.Bv_merge_sign_extend_1
import Cpc.Proofs.Rules.Bv_merge_sign_extend_2
import Cpc.Proofs.Rules.Bv_sign_extend_eq_const_1
import Cpc.Proofs.Rules.Bv_sign_extend_eq_const_2
import Cpc.Proofs.Rules.Bv_zero_extend_eq_const_1
import Cpc.Proofs.Rules.Bv_zero_extend_eq_const_2
import Cpc.Proofs.Rules.Bv_zero_extend_ult_const_1
import Cpc.Proofs.Rules.Bv_zero_extend_ult_const_2
import Cpc.Proofs.Rules.Bv_sign_extend_ult_const_1
import Cpc.Proofs.Rules.Bv_sign_extend_ult_const_2
import Cpc.Proofs.Rules.Bv_sign_extend_ult_const_3
import Cpc.Proofs.Rules.Bv_sign_extend_ult_const_4
import Cpc.Proofs.Rules.Sets_eq_singleton_emp
import Cpc.Proofs.Rules.Sets_member_singleton
import Cpc.Proofs.Rules.Sets_member_emp
import Cpc.Proofs.Rules.Sets_subset_elim
import Cpc.Proofs.Rules.Sets_union_comm
import Cpc.Proofs.Rules.Sets_inter_comm
import Cpc.Proofs.Rules.Sets_inter_emp1
import Cpc.Proofs.Rules.Sets_inter_emp2
import Cpc.Proofs.Rules.Sets_minus_emp1
import Cpc.Proofs.Rules.Sets_minus_emp2
import Cpc.Proofs.Rules.Sets_union_emp1
import Cpc.Proofs.Rules.Sets_union_emp2
import Cpc.Proofs.Rules.Sets_inter_member
import Cpc.Proofs.Rules.Sets_minus_member
import Cpc.Proofs.Rules.Sets_union_member
import Cpc.Proofs.Rules.Sets_choose_singleton
import Cpc.Proofs.Rules.Sets_minus_self
import Cpc.Proofs.Rules.Sets_is_empty_elim
import Cpc.Proofs.Rules.Sets_is_singleton_elim
import Cpc.Proofs.Rules.Str_eq_ctn_false
import Cpc.Proofs.Rules.Str_eq_ctn_full_false1
import Cpc.Proofs.Rules.Str_eq_ctn_full_false2
import Cpc.Proofs.Rules.Str_eq_len_false
import Cpc.Proofs.Rules.Str_substr_empty_str
import Cpc.Proofs.Rules.Str_substr_empty_range
import Cpc.Proofs.Rules.Str_substr_empty_start
import Cpc.Proofs.Rules.Str_substr_empty_start_neg
import Cpc.Proofs.Rules.Str_substr_substr_start_geq_len
import Cpc.Proofs.Rules.Str_substr_eq_empty
import Cpc.Proofs.Rules.Str_substr_z_eq_empty_leq
import Cpc.Proofs.Rules.Str_substr_eq_empty_leq_len
import Cpc.Proofs.Rules.Str_len_replace_inv
import Cpc.Proofs.Rules.Str_len_replace_all_inv
import Cpc.Proofs.Rules.Str_len_update_inv
import Cpc.Proofs.Rules.Str_update_in_first_concat
import Cpc.Proofs.Rules.Str_len_substr_in_range
import Cpc.Proofs.Rules.Str_concat_clash
import Cpc.Proofs.Rules.Str_concat_clash_rev
import Cpc.Proofs.Rules.Str_concat_clash2
import Cpc.Proofs.Rules.Str_concat_clash2_rev
import Cpc.Proofs.Rules.Str_concat_unify
import Cpc.Proofs.Rules.Str_concat_unify_rev
import Cpc.Proofs.Rules.Str_concat_unify_base
import Cpc.Proofs.Rules.Str_concat_unify_base_rev
import Cpc.Proofs.Rules.Str_prefixof_elim
import Cpc.Proofs.Rules.Str_suffixof_elim
import Cpc.Proofs.Rules.Str_prefixof_eq
import Cpc.Proofs.Rules.Str_suffixof_eq
import Cpc.Proofs.Rules.Str_prefixof_one
import Cpc.Proofs.Rules.Str_suffixof_one
import Cpc.Proofs.Rules.Str_substr_combine1
import Cpc.Proofs.Rules.Str_substr_combine2
import Cpc.Proofs.Rules.Str_substr_combine3
import Cpc.Proofs.Rules.Str_substr_combine4
import Cpc.Proofs.Rules.Str_substr_concat1
import Cpc.Proofs.Rules.Str_substr_concat2
import Cpc.Proofs.Rules.Str_substr_replace
import Cpc.Proofs.Rules.Str_substr_full
import Cpc.Proofs.Rules.Str_substr_full_eq
import Cpc.Proofs.Rules.Str_contains_refl
import Cpc.Proofs.Rules.Str_contains_concat_find
import Cpc.Proofs.Rules.Str_contains_concat_find_contra
import Cpc.Proofs.Rules.Str_contains_split_char
import Cpc.Proofs.Rules.Str_contains_leq_len_eq
import Cpc.Proofs.Rules.Str_contains_emp
import Cpc.Proofs.Rules.Str_contains_char
import Cpc.Proofs.Rules.Str_at_elim
import Cpc.Proofs.Rules.Str_replace_self
import Cpc.Proofs.Rules.Str_replace_id
import Cpc.Proofs.Rules.Str_replace_prefix
import Cpc.Proofs.Rules.Str_replace_no_contains
import Cpc.Proofs.Rules.Str_replace_find_base
import Cpc.Proofs.Rules.Str_replace_find_first_concat
import Cpc.Proofs.Rules.Str_replace_empty
import Cpc.Proofs.Rules.Str_replace_one_pre
import Cpc.Proofs.Rules.Str_replace_find_pre
import Cpc.Proofs.Rules.Str_replace_all_no_contains
import Cpc.Proofs.Rules.Str_replace_all_empty
import Cpc.Proofs.Rules.Str_replace_all_id
import Cpc.Proofs.Rules.Str_replace_all_self
import Cpc.Proofs.Rules.Str_replace_re_none
import Cpc.Proofs.Rules.Str_replace_re_all_none
import Cpc.Proofs.Rules.Str_len_concat_rec
import Cpc.Proofs.Rules.Str_len_eq_zero_concat_rec
import Cpc.Proofs.Rules.Str_len_eq_zero_base
import Cpc.Proofs.Rules.Str_indexof_self
import Cpc.Proofs.Rules.Str_indexof_no_contains
import Cpc.Proofs.Rules.Str_indexof_oob
import Cpc.Proofs.Rules.Str_indexof_oob2
import Cpc.Proofs.Rules.Str_indexof_contains_pre
import Cpc.Proofs.Rules.Str_indexof_contains_concat_pre
import Cpc.Proofs.Rules.Str_indexof_find_emp
import Cpc.Proofs.Rules.Str_indexof_eq_irr
import Cpc.Proofs.Rules.Str_indexof_re_none
import Cpc.Proofs.Rules.Str_indexof_re_emp_re
import Cpc.Proofs.Rules.Str_to_lower_concat
import Cpc.Proofs.Rules.Str_to_upper_concat
import Cpc.Proofs.Rules.Str_to_lower_upper
import Cpc.Proofs.Rules.Str_to_upper_lower
import Cpc.Proofs.Rules.Str_to_lower_len
import Cpc.Proofs.Rules.Str_to_upper_len
import Cpc.Proofs.Rules.Str_to_lower_from_int
import Cpc.Proofs.Rules.Str_to_upper_from_int
import Cpc.Proofs.Rules.Str_to_int_concat_neg_one
import Cpc.Proofs.Rules.Str_is_digit_elim
import Cpc.Proofs.Rules.Str_leq_empty
import Cpc.Proofs.Rules.Str_leq_empty_eq
import Cpc.Proofs.Rules.Str_leq_concat_false
import Cpc.Proofs.Rules.Str_leq_concat_true
import Cpc.Proofs.Rules.Str_leq_concat_base_1
import Cpc.Proofs.Rules.Str_leq_concat_base_2
import Cpc.Proofs.Rules.Str_lt_elim
import Cpc.Proofs.Rules.Str_from_int_no_ctn_nondigit
import Cpc.Proofs.Rules.Str_substr_ctn_contra
import Cpc.Proofs.Rules.Str_substr_ctn
import Cpc.Proofs.Rules.Str_replace_dual_ctn
import Cpc.Proofs.Rules.Str_replace_dual_ctn_false
import Cpc.Proofs.Rules.Str_replace_self_ctn_simp
import Cpc.Proofs.Rules.Str_replace_emp_ctn_src
import Cpc.Proofs.Rules.Str_substr_char_start_eq_len
import Cpc.Proofs.Rules.Str_contains_repl_char
import Cpc.Proofs.Rules.Str_contains_repl_self_tgt_char
import Cpc.Proofs.Rules.Str_contains_repl_self
import Cpc.Proofs.Rules.Str_contains_repl_tgt
import Cpc.Proofs.Rules.Str_repl_repl_len_id
import Cpc.Proofs.Rules.Str_repl_repl_src_tgt_no_ctn
import Cpc.Proofs.Rules.Str_repl_repl_tgt_self
import Cpc.Proofs.Rules.Str_repl_repl_tgt_no_ctn
import Cpc.Proofs.Rules.Str_repl_repl_src_self
import Cpc.Proofs.Rules.Str_repl_repl_src_inv_no_ctn1
import Cpc.Proofs.Rules.Str_repl_repl_src_inv_no_ctn2
import Cpc.Proofs.Rules.Str_repl_repl_src_inv_no_ctn3
import Cpc.Proofs.Rules.Str_repl_repl_dual_self
import Cpc.Proofs.Rules.Str_repl_repl_dual_ite1
import Cpc.Proofs.Rules.Str_repl_repl_dual_ite2
import Cpc.Proofs.Rules.Str_repl_repl_lookahead_id_simp
import Cpc.Proofs.Rules.Re_all_elim
import Cpc.Proofs.Rules.Re_opt_elim
import Cpc.Proofs.Rules.Re_diff_elim
import Cpc.Proofs.Rules.Re_plus_elim
import Cpc.Proofs.Rules.Re_repeat_elim
import Cpc.Proofs.Rules.Re_concat_star_swap
import Cpc.Proofs.Rules.Re_concat_star_repeat
import Cpc.Proofs.Rules.Re_concat_star_subsume1
import Cpc.Proofs.Rules.Re_concat_star_subsume2
import Cpc.Proofs.Rules.Re_concat_merge
import Cpc.Proofs.Rules.Re_union_all
import Cpc.Proofs.Rules.Re_union_const_elim
import Cpc.Proofs.Rules.Re_inter_all
import Cpc.Proofs.Rules.Re_star_none
import Cpc.Proofs.Rules.Re_star_emp
import Cpc.Proofs.Rules.Re_star_star
import Cpc.Proofs.Rules.Re_range_refl
import Cpc.Proofs.Rules.Re_range_emp
import Cpc.Proofs.Rules.Re_range_non_singleton_1
import Cpc.Proofs.Rules.Re_range_non_singleton_2
import Cpc.Proofs.Rules.Re_star_union_char
import Cpc.Proofs.Rules.Re_star_union_drop_emp
import Cpc.Proofs.Rules.Re_loop_neg
import Cpc.Proofs.Rules.Re_inter_cstring
import Cpc.Proofs.Rules.Re_inter_cstring_neg
import Cpc.Proofs.Rules.Str_substr_len_include
import Cpc.Proofs.Rules.Str_substr_len_include_pre
import Cpc.Proofs.Rules.Str_substr_len_norm
import Cpc.Proofs.Rules.Seq_len_rev
import Cpc.Proofs.Rules.Seq_rev_rev
import Cpc.Proofs.Rules.Seq_rev_concat
import Cpc.Proofs.Rules.Str_eq_repl_self_emp
import Cpc.Proofs.Rules.Str_eq_repl_no_change
import Cpc.Proofs.Rules.Str_eq_repl_tgt_eq_len
import Cpc.Proofs.Rules.Str_eq_repl_len_one_emp_prefix
import Cpc.Proofs.Rules.Str_eq_repl_emp_tgt_nemp
import Cpc.Proofs.Rules.Str_eq_repl_nemp_src_emp
import Cpc.Proofs.Rules.Str_eq_repl_self_src
import Cpc.Proofs.Rules.Seq_len_unit
import Cpc.Proofs.Rules.Seq_nth_unit
import Cpc.Proofs.Rules.Seq_rev_unit
import Cpc.Proofs.Rules.Re_in_empty
import Cpc.Proofs.Rules.Re_in_sigma
import Cpc.Proofs.Rules.Re_in_sigma_star
import Cpc.Proofs.Rules.Re_in_cstring
import Cpc.Proofs.Rules.Re_in_comp
import Cpc.Proofs.Rules.Str_in_re_union_elim
import Cpc.Proofs.Rules.Str_in_re_inter_elim
import Cpc.Proofs.Rules.Str_in_re_range_elim
import Cpc.Proofs.Rules.Str_in_re_contains
import Cpc.Proofs.Rules.Str_in_re_from_int_nemp_dig_range
import Cpc.Proofs.Rules.Str_in_re_from_int_dig_range
import Cpc.Proofs.Rules.Eq_refl
import Cpc.Proofs.Rules.Eq_symm
import Cpc.Proofs.Rules.Eq_cond_deq
import Cpc.Proofs.Rules.Eq_ite_lift
import Cpc.Proofs.Rules.Distinct_binary_elim
import Cpc.Proofs.Rules.Uf_bv2nat_int2bv
import Cpc.Proofs.Rules.Uf_bv2nat_int2bv_extend
import Cpc.Proofs.Rules.Uf_bv2nat_int2bv_extract
import Cpc.Proofs.Rules.Uf_int2bv_bv2nat
import Cpc.Proofs.Rules.Uf_bv2nat_geq_elim
import Cpc.Proofs.Rules.Uf_int2bv_bvult_equiv
import Cpc.Proofs.Rules.Uf_int2bv_bvule_equiv
import Cpc.Proofs.Rules.Uf_sbv_to_int_elim
import Cpc.Proofs.Rules.Evaluate
import Cpc.Proofs.Rules.Distinct_values
import Cpc.Proofs.Rules.Aci_norm
import Cpc.Proofs.Rules.Absorb
import Cpc.Proofs.Rules.Distinct_card_conflict


open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- Central expansion point for plain `step` rules.

   To add a new rule handled by `__eo_cmd_step_proven`, add its matching
   pattern here and dispatch to the arity helper matching the rule shape.
   The preservation theorems below then pick the new rule up automatically. -/
theorem cmd_step_proven_facts_of_invariants
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (_hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTruthInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  cmdTranslationOk (CCmd.step r args premises) ->
  __eo_cmd_step_proven s r args premises ≠ Term.Stuck ->
  CmdStepFacts M s (__eo_cmd_step_proven s r args premises)
:=
by
  intro hs hsTy hsTrans hCmdTrans hProg
  have hPremisesBool : AllHaveBoolType (premiseTermList s premises) :=
    premiseTermList_has_bool_type s premises hsTy hsTrans
  cases r with
  | scope =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | process_scope =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_process_scope_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | split =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_split_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | resolution =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_resolution_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | chain_resolution =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_chain_resolution_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | chain_m_resolution =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_chain_m_resolution_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | factoring =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_factoring_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | reordering =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_reordering_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | eq_resolve =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_eq_resolve_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | modus_ponens =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_modus_ponens_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_not_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_not_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | contra =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_contra_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | and_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_and_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | and_intro =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_and_intro_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_or_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_or_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | implies_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_implies_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_implies_elim1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_implies_elim1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_implies_elim2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_implies_elim2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | equiv_elim1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_equiv_elim1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | equiv_elim2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_equiv_elim2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_equiv_elim1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_equiv_elim1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_equiv_elim2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_equiv_elim2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | xor_elim1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_xor_elim1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | xor_elim2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_xor_elim2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_xor_elim1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_xor_elim1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_xor_elim2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_xor_elim2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_elim1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_elim1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_elim2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_elim2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_ite_elim1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_ite_elim1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_ite_elim2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_ite_elim2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | not_and =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_not_and_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_and_pos =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_and_pos_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_and_neg =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_and_neg_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_or_pos =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_or_pos_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_or_neg =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_or_neg_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_implies_pos =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_implies_pos_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_implies_neg1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_implies_neg1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_implies_neg2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_implies_neg2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_equiv_pos1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_equiv_pos1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_equiv_pos2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_equiv_pos2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_equiv_neg1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_equiv_neg1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_equiv_neg2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_equiv_neg2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_xor_pos1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_xor_pos1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_xor_pos2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_xor_pos2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_xor_neg1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_xor_neg1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_xor_neg2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_xor_neg2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_ite_pos1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_ite_pos1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_ite_pos2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_ite_pos2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_ite_pos3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_ite_pos3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_ite_neg1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_ite_neg1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_ite_neg2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_ite_neg2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cnf_ite_neg3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cnf_ite_neg3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arrays_read_over_write =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arrays_read_over_write_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arrays_read_over_write_contra =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arrays_read_over_write_contra_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arrays_read_over_write_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arrays_read_over_write_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arrays_ext =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arrays_ext_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | refl =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_refl_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | symm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_symm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | trans =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_trans_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | cong =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_cong_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | nary_cong =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_nary_cong_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | pairwise_cong =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_pairwise_cong_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | true_intro =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_true_intro_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | true_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_true_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | false_intro =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_false_intro_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | false_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_false_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ho_cong =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ho_cong_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | distinct_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_distinct_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | distinct_true =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_distinct_true_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | distinct_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_distinct_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_sum_ub =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_sum_ub_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_mult_pos =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_mult_pos_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_mult_neg =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_mult_neg_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_trichotomy =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_trichotomy_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | int_tight_ub =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_int_tight_ub_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | int_tight_lb =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_int_tight_lb_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_mult_tangent =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_mult_tangent_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_mult_sign =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_mult_sign_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_mult_abs_comparison =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_mult_abs_comparison_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_reduction =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_reduction_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_poly_norm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_poly_norm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_poly_norm_rel =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_poly_norm_rel_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_repeat_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_repeat_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_smulo_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_smulo_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_umulo_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_umulo_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_bitwise_slicing =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_bitwise_slicing_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_bitblast_step =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_bitblast_step_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_poly_norm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_poly_norm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_poly_norm_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_poly_norm_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | string_length_pos =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_string_length_pos_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | string_length_non_empty =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_string_length_non_empty_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | concat_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_concat_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | concat_unify =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_concat_unify_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | concat_csplit =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_concat_csplit_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | concat_split =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_concat_split_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | concat_lprop =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_concat_lprop_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | concat_cprop =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_concat_cprop_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | string_decompose =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_string_decompose_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | exists_string_length =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_exists_string_length_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | string_code_inj =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_string_code_inj_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | string_seq_unit_inj =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_string_seq_unit_inj_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_inter =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_inter_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_concat =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_concat_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_unfold_pos =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_unfold_pos_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_unfold_neg_concat_fixed =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_unfold_neg_concat_fixed_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_unfold_neg =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_unfold_neg_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | string_ext =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_string_ext_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | string_reduction =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_string_reduction_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | string_eager_reduction =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_string_eager_reduction_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_string_pred_entail =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_string_pred_entail_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_string_pred_safe_approx =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_string_pred_safe_approx_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_eval =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_eval_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_consume =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_consume_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_loop_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_loop_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_eq_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_eq_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_inter_inclusion =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_inter_inclusion_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_union_inclusion =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_union_inclusion_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_concat_star_char =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_concat_star_char_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_sigma =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_sigma_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_sigma_star =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_sigma_star_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_ctn_multiset_subset =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_ctn_multiset_subset_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_overlap_split_ctn =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_overlap_split_ctn_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_overlap_endpoints_ctn =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_overlap_endpoints_ctn_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_overlap_endpoints_indexof =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_overlap_endpoints_indexof_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_overlap_endpoints_replace =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_overlap_endpoints_replace_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_re_eval =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_re_eval_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_re_eval =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_re_eval_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_re_all_eval =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_re_all_eval_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | seq_eval_op =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_seq_eval_op_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_singleton_inj =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_singleton_inj_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_ext =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_ext_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_eval_op =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_eval_op_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_insert_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_insert_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ubv_to_int_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ubv_to_int_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | int_to_bv_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_int_to_bv_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | instantiate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_instantiate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | skolemize =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_skolemize_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | skolem_intro =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_skolem_intro_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | alpha_equiv =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_alpha_equiv_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | beta_reduce =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_beta_reduce_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | quant_var_reordering =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_quant_var_reordering_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | exists_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_exists_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | quant_unused_vars =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_quant_unused_vars_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | quant_merge_prenex =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_quant_merge_prenex_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | quant_miniscope_and =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_quant_miniscope_and_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | quant_miniscope_or =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_quant_miniscope_or_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | quant_miniscope_ite =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_quant_miniscope_ite_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | quant_var_elim_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_quant_var_elim_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | quant_dt_split =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_quant_dt_split_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_split =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_split_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_inst =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_inst_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_collapse_selector =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_collapse_selector_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_collapse_tester =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_collapse_tester_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_collapse_tester_singleton =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_collapse_tester_singleton_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_cons_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_cons_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_cons_eq_clash =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_cons_eq_clash_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_cycle =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_cycle_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_collapse_updater =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_collapse_updater_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | dt_updater_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_dt_updater_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_div_total_zero_real =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_div_total_zero_real_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_div_total_zero_int =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_div_total_zero_int_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_div_total =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_div_total_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_div_total_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_div_total_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_div_total_zero =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_div_total_zero_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_div_total_neg =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_div_total_neg_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_mod_total =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_mod_total_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_mod_total_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_mod_total_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_mod_total_zero =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_mod_total_zero_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_mod_total_neg =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_mod_total_neg_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_elim_gt =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_elim_gt_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_elim_lt =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_elim_lt_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_elim_int_gt =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_elim_int_gt_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_elim_int_lt =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_elim_int_lt_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_elim_leq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_elim_leq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_leq_norm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_leq_norm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_geq_tighten =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_geq_tighten_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_geq_norm1_int =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_geq_norm1_int_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_geq_norm1_real =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_geq_norm1_real_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_eq_elim_real =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_eq_elim_real_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_eq_elim_int =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_eq_elim_int_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_to_int_elim_to_real =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_to_int_elim_to_real_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_mod_over_mod_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_mod_over_mod_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_mod_over_mod =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_mod_over_mod_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_mod_over_mod_mult =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_mod_over_mod_mult_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_eq_conflict =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_eq_conflict_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_int_geq_tighten =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_int_geq_tighten_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_divisible_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_divisible_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_abs_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_abs_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_abs_int_gt =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_abs_int_gt_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_abs_real_gt =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_abs_real_gt_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_geq_ite_lift =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_geq_ite_lift_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_leq_ite_lift =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_leq_ite_lift_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_min_lt1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_min_lt1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_min_lt2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_min_lt2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_max_geq1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_max_geq1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | arith_max_geq2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_arith_max_geq2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | array_read_over_write =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_array_read_over_write_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | array_read_over_write2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_array_read_over_write2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | array_store_overwrite =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_array_store_overwrite_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | array_store_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_array_store_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | array_read_over_write_split =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_array_read_over_write_split_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | array_store_swap =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_array_store_swap_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_double_not_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_double_not_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_not_true =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_not_true_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_not_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_not_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_eq_true =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_eq_true_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_eq_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_eq_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_eq_nrefl =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_eq_nrefl_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_impl_false1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_impl_false1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_impl_false2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_impl_false2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_impl_true1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_impl_true1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_impl_true2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_impl_true2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_impl_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_impl_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_dual_impl_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_dual_impl_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_and_conf =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_and_conf_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_and_conf2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_and_conf2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_or_taut =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_or_taut_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_or_taut2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_or_taut2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_or_de_morgan =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_or_de_morgan_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_implies_de_morgan =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_implies_de_morgan_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_and_de_morgan =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_and_de_morgan_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_or_and_distrib =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_or_and_distrib_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_implies_or_distrib =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_implies_or_distrib_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_xor_refl =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_xor_refl_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_xor_nrefl =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_xor_nrefl_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_xor_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_xor_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_xor_true =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_xor_true_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_xor_comm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_xor_comm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_xor_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_xor_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_not_xor_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_not_xor_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_not_eq_elim1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_not_eq_elim1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_not_eq_elim2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_not_eq_elim2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_neg_branch =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_neg_branch_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_then_true =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_then_true_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_else_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_else_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_then_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_then_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_else_true =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_else_true_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_then_lookahead_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_then_lookahead_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_else_lookahead_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_else_lookahead_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_then_lookahead_not_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_then_lookahead_not_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_else_lookahead_not_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_else_lookahead_not_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_expand =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_expand_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bool_not_ite_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bool_not_ite_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_true_cond =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_true_cond_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_false_cond =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_false_cond_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_not_cond =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_not_cond_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_eq_branch =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_eq_branch_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_then_lookahead =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_then_lookahead_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_else_lookahead =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_else_lookahead_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_then_neg_lookahead =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_then_neg_lookahead_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | ite_else_neg_lookahead =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_ite_else_neg_lookahead_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_concat_extract_merge =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_concat_extract_merge_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_extract =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_extract_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_whole =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_whole_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_concat_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_concat_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_concat_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_concat_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_concat_3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_concat_3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_concat_4 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_concat_4_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_eq_extract_elim1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_eq_extract_elim1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_eq_extract_elim2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_eq_extract_elim2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_eq_extract_elim3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_eq_extract_elim3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_not =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_not_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_sign_extend_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_sign_extend_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_sign_extend_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_sign_extend_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_sign_extend_3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_sign_extend_3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_not_xor =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_not_xor_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_and_simplify_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_and_simplify_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_and_simplify_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_and_simplify_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_or_simplify_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_or_simplify_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_or_simplify_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_or_simplify_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xor_simplify_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xor_simplify_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xor_simplify_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xor_simplify_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xor_simplify_3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xor_simplify_3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ult_add_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ult_add_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_mult_slt_mult_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_mult_slt_mult_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_mult_slt_mult_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_mult_slt_mult_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_commutative_xor =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_commutative_xor_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_commutative_comp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_commutative_comp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_zero_extend_eliminate_0 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_zero_extend_eliminate_0_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sign_extend_eliminate_0 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sign_extend_eliminate_0_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_not_neq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_not_neq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ult_ones =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ult_ones_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_concat_merge_const =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_concat_merge_const_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_commutative_add =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_commutative_add_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sub_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sub_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_width_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_width_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_width_one_not =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_width_one_not_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_eq_xor_solve =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_eq_xor_solve_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_eq_not_solve =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_eq_not_solve_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ugt_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ugt_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_uge_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_uge_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sgt_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sgt_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sge_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sge_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sle_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sle_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_redor_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_redor_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_redand_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_redand_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ule_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ule_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_comp_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_comp_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_rotate_left_eliminate_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_rotate_left_eliminate_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_rotate_left_eliminate_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_rotate_left_eliminate_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_rotate_right_eliminate_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_rotate_right_eliminate_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_rotate_right_eliminate_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_rotate_right_eliminate_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_nand_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_nand_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_nor_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_nor_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xnor_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xnor_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sdiv_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sdiv_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_zero_extend_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_zero_extend_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_uaddo_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_uaddo_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_saddo_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_saddo_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sdivo_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sdivo_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_smod_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_smod_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_srem_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_srem_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_usubo_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_usubo_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ssubo_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ssubo_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_nego_eliminate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_nego_eliminate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_equal_children =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_equal_children_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_const_children_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_const_children_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_const_children_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_const_children_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_equal_cond_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_equal_cond_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_equal_cond_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_equal_cond_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_equal_cond_3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_equal_cond_3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_merge_then_if =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_merge_then_if_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_merge_else_if =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_merge_else_if_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_merge_then_else =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_merge_then_else_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ite_merge_else_else =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ite_merge_else_else_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_shl_by_const_0 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_shl_by_const_0_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_shl_by_const_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_shl_by_const_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_shl_by_const_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_shl_by_const_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_lshr_by_const_0 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_lshr_by_const_0_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_lshr_by_const_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_lshr_by_const_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_lshr_by_const_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_lshr_by_const_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ashr_by_const_0 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ashr_by_const_0_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ashr_by_const_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ashr_by_const_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ashr_by_const_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ashr_by_const_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_and_concat_pullup =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_and_concat_pullup_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_or_concat_pullup =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_or_concat_pullup_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xor_concat_pullup =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xor_concat_pullup_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_and_concat_pullup2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_and_concat_pullup2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_or_concat_pullup2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_or_concat_pullup2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xor_concat_pullup2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xor_concat_pullup2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_and_concat_pullup3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_and_concat_pullup3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_or_concat_pullup3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_or_concat_pullup3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xor_concat_pullup3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xor_concat_pullup3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xor_duplicate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xor_duplicate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xor_ones =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xor_ones_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_xor_not =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_xor_not_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_not_idemp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_not_idemp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ult_zero_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ult_zero_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ult_zero_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ult_zero_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ult_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ult_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_lt_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_lt_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ule_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ule_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ule_zero =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ule_zero_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_zero_ule =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_zero_ule_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sle_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sle_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ule_max =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ule_max_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_not_ult =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_not_ult_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_mult_pow2_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_mult_pow2_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_mult_pow2_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_mult_pow2_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_mult_pow2_2b =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_mult_pow2_2b_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_extract_mult_leading_bit =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_extract_mult_leading_bit_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_udiv_pow2_not_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_udiv_pow2_not_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_udiv_zero =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_udiv_zero_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_udiv_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_udiv_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_urem_pow2_not_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_urem_pow2_not_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_urem_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_urem_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_urem_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_urem_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_shl_zero =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_shl_zero_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_lshr_zero =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_lshr_zero_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ashr_zero =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ashr_zero_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ugt_urem =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ugt_urem_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_ult_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_ult_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_merge_sign_extend_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_merge_sign_extend_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_merge_sign_extend_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_merge_sign_extend_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sign_extend_eq_const_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sign_extend_eq_const_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sign_extend_eq_const_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sign_extend_eq_const_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_zero_extend_eq_const_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_zero_extend_eq_const_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_zero_extend_eq_const_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_zero_extend_eq_const_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_zero_extend_ult_const_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_zero_extend_ult_const_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_zero_extend_ult_const_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_zero_extend_ult_const_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sign_extend_ult_const_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sign_extend_ult_const_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sign_extend_ult_const_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sign_extend_ult_const_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sign_extend_ult_const_3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sign_extend_ult_const_3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | bv_sign_extend_ult_const_4 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_bv_sign_extend_ult_const_4_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_eq_singleton_emp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_eq_singleton_emp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_member_singleton =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_member_singleton_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_member_emp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_member_emp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_subset_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_subset_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_union_comm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_union_comm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_inter_comm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_inter_comm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_inter_emp1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_inter_emp1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_inter_emp2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_inter_emp2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_minus_emp1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_minus_emp1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_minus_emp2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_minus_emp2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_union_emp1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_union_emp1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_union_emp2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_union_emp2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_inter_member =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_inter_member_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_minus_member =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_minus_member_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_union_member =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_union_member_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_choose_singleton =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_choose_singleton_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_minus_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_minus_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_is_empty_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_is_empty_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | sets_is_singleton_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_sets_is_singleton_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_ctn_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_ctn_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_ctn_full_false1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_ctn_full_false1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_ctn_full_false2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_ctn_full_false2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_len_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_len_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_empty_str =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_empty_str_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_empty_range =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_empty_range_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_empty_start =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_empty_start_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_empty_start_neg =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_empty_start_neg_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_substr_start_geq_len =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_substr_start_geq_len_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_eq_empty =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_eq_empty_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_z_eq_empty_leq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_z_eq_empty_leq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_eq_empty_leq_len =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_eq_empty_leq_len_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_len_replace_inv =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_len_replace_inv_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_len_replace_all_inv =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_len_replace_all_inv_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_len_update_inv =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_len_update_inv_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_update_in_first_concat =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_update_in_first_concat_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_len_substr_in_range =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_len_substr_in_range_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_concat_clash =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_concat_clash_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_concat_clash_rev =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_concat_clash_rev_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_concat_clash2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_concat_clash2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_concat_clash2_rev =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_concat_clash2_rev_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_concat_unify =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_concat_unify_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_concat_unify_rev =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_concat_unify_rev_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_concat_unify_base =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_concat_unify_base_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_concat_unify_base_rev =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_concat_unify_base_rev_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_prefixof_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_prefixof_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_suffixof_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_suffixof_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_prefixof_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_prefixof_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_suffixof_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_suffixof_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_prefixof_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_prefixof_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_suffixof_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_suffixof_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_combine1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_combine1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_combine2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_combine2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_combine3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_combine3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_combine4 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_combine4_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_concat1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_concat1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_concat2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_concat2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_replace =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_replace_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_full =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_full_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_full_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_full_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_refl =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_refl_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_concat_find =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_concat_find_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_concat_find_contra =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_concat_find_contra_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_split_char =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_split_char_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_leq_len_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_leq_len_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_emp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_emp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_char =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_char_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_at_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_at_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_id =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_id_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_prefix =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_prefix_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_no_contains =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_no_contains_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_find_base =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_find_base_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_find_first_concat =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_find_first_concat_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_empty =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_empty_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_one_pre =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_one_pre_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_find_pre =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_find_pre_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_all_no_contains =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_all_no_contains_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_all_empty =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_all_empty_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_all_id =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_all_id_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_all_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_all_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_re_none =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_re_none_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_re_all_none =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_re_all_none_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_len_concat_rec =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_len_concat_rec_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_len_eq_zero_concat_rec =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_len_eq_zero_concat_rec_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_len_eq_zero_base =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_len_eq_zero_base_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_no_contains =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_no_contains_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_oob =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_oob_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_oob2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_oob2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_contains_pre =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_contains_pre_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_contains_concat_pre =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_contains_concat_pre_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_find_emp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_find_emp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_eq_irr =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_eq_irr_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_re_none =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_re_none_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_indexof_re_emp_re =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_indexof_re_emp_re_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_to_lower_concat =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_to_lower_concat_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_to_upper_concat =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_to_upper_concat_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_to_lower_upper =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_to_lower_upper_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_to_upper_lower =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_to_upper_lower_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_to_lower_len =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_to_lower_len_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_to_upper_len =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_to_upper_len_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_to_lower_from_int =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_to_lower_from_int_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_to_upper_from_int =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_to_upper_from_int_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_to_int_concat_neg_one =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_to_int_concat_neg_one_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_is_digit_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_is_digit_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_leq_empty =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_leq_empty_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_leq_empty_eq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_leq_empty_eq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_leq_concat_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_leq_concat_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_leq_concat_true =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_leq_concat_true_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_leq_concat_base_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_leq_concat_base_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_leq_concat_base_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_leq_concat_base_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_lt_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_lt_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_from_int_no_ctn_nondigit =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_from_int_no_ctn_nondigit_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_ctn_contra =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_ctn_contra_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_ctn =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_ctn_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_dual_ctn =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_dual_ctn_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_dual_ctn_false =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_dual_ctn_false_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_self_ctn_simp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_self_ctn_simp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_replace_emp_ctn_src =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_replace_emp_ctn_src_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_char_start_eq_len =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_char_start_eq_len_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_repl_char =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_repl_char_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_repl_self_tgt_char =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_repl_self_tgt_char_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_repl_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_repl_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_contains_repl_tgt =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_contains_repl_tgt_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_len_id =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_len_id_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_src_tgt_no_ctn =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_src_tgt_no_ctn_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_tgt_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_tgt_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_tgt_no_ctn =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_tgt_no_ctn_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_src_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_src_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_src_inv_no_ctn1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_src_inv_no_ctn1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_src_inv_no_ctn2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_src_inv_no_ctn2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_src_inv_no_ctn3 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_src_inv_no_ctn3_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_dual_self =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_dual_self_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_dual_ite1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_dual_ite1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_dual_ite2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_dual_ite2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_repl_repl_lookahead_id_simp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_repl_repl_lookahead_id_simp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_all_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_all_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_opt_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_opt_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_diff_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_diff_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_plus_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_plus_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_repeat_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_repeat_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_concat_star_swap =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_concat_star_swap_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_concat_star_repeat =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_concat_star_repeat_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_concat_star_subsume1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_concat_star_subsume1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_concat_star_subsume2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_concat_star_subsume2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_concat_merge =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_concat_merge_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_union_all =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_union_all_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_union_const_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_union_const_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_inter_all =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_inter_all_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_star_none =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_star_none_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_star_emp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_star_emp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_star_star =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_star_star_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_range_refl =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_range_refl_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_range_emp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_range_emp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_range_non_singleton_1 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_range_non_singleton_1_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_range_non_singleton_2 =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_range_non_singleton_2_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_star_union_char =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_star_union_char_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_star_union_drop_emp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_star_union_drop_emp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_loop_neg =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_loop_neg_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_inter_cstring =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_inter_cstring_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_inter_cstring_neg =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_inter_cstring_neg_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_len_include =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_len_include_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_len_include_pre =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_len_include_pre_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_substr_len_norm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_substr_len_norm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | seq_len_rev =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_seq_len_rev_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | seq_rev_rev =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_seq_rev_rev_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | seq_rev_concat =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_seq_rev_concat_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_repl_self_emp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_repl_self_emp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_repl_no_change =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_repl_no_change_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_repl_tgt_eq_len =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_repl_tgt_eq_len_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_repl_len_one_emp_prefix =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_repl_len_one_emp_prefix_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_repl_emp_tgt_nemp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_repl_emp_tgt_nemp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_repl_nemp_src_emp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_repl_nemp_src_emp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_eq_repl_self_src =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_eq_repl_self_src_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | seq_len_unit =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_seq_len_unit_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | seq_nth_unit =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_seq_nth_unit_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | seq_rev_unit =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_seq_rev_unit_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_in_empty =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_in_empty_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_in_sigma =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_in_sigma_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_in_sigma_star =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_in_sigma_star_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_in_cstring =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_in_cstring_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | re_in_comp =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_re_in_comp_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_union_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_union_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_inter_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_inter_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_range_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_range_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_contains =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_contains_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_from_int_nemp_dig_range =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_from_int_nemp_dig_range_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | str_in_re_from_int_dig_range =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_str_in_re_from_int_dig_range_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | eq_refl =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_eq_refl_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | eq_symm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_eq_symm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | eq_cond_deq =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_eq_cond_deq_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | eq_ite_lift =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_eq_ite_lift_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | distinct_binary_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_distinct_binary_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | uf_bv2nat_int2bv =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_uf_bv2nat_int2bv_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | uf_bv2nat_int2bv_extend =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_uf_bv2nat_int2bv_extend_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | uf_bv2nat_int2bv_extract =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_uf_bv2nat_int2bv_extract_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | uf_int2bv_bv2nat =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_uf_int2bv_bv2nat_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | uf_bv2nat_geq_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_uf_bv2nat_geq_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | uf_int2bv_bvult_equiv =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_uf_int2bv_bvult_equiv_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | uf_int2bv_bvule_equiv =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_uf_int2bv_bvule_equiv_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | uf_sbv_to_int_elim =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_uf_sbv_to_int_elim_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | evaluate =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_evaluate_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | distinct_values =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_distinct_values_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | aci_norm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_aci_norm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | absorb =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_absorb_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | distinct_card_conflict =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_distinct_card_conflict_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg


/-
Central expansion point for `step_pop` rules.

If `__eo_cmd_step_pop_proven` grows more supported rules, add a matching
branch below and route it to the rule-specific helper.
-/
theorem cmd_step_pop_proven_facts_of_invariants
    (root tail : CState) (A : Term)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTypeInvariant root ->
  checkerTranslationInvariant root ->
  checkerTypeInvariant (CState.cons (CStateObj.assume_push A) tail) ->
  checkerTranslationInvariant (CState.cons (CStateObj.assume_push A) tail) ->
  __eo_cmd_step_pop_proven root r args A premises ≠ Term.Stuck ->
  CmdStepPopFacts root tail A (__eo_cmd_step_pop_proven root r args A premises)
:=
by
  intro hsRootTy hsRootTrans hsCurTy hsCurTrans hProg
  have hATy : __eo_typeof A = Term.Bool :=
    (checkerTypeInvariant_head_assume_push A tail hsCurTy).2
  have hATrans : RuleProofs.eo_has_smt_translation A :=
    checkerTranslationInvariant_head_assume_push A tail hsCurTrans
  have hPremisesTrans : AllHaveSmtTranslation (premiseTermList root premises) :=
    premiseTermList_has_smt_translation root premises hsRootTrans
  have hPremisesTy : AllTypeofBool (premiseTermList root premises) :=
    premiseTermList_has_typeof_bool root premises hsRootTy
  cases r with
  | scope =>
      exact cmd_step_pop_facts_of_rule_properties root tail A premises <|
        cmd_step_pop_scope_properties A root args premises
          hATrans hATy hPremisesTrans hPremisesTy hProg
  | process_scope =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | split =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | resolution =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | chain_resolution =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | chain_m_resolution =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | factoring =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | reordering =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | eq_resolve =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | modus_ponens =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_not_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | contra =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | and_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | and_intro =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_or_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | implies_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_implies_elim1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_implies_elim2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | equiv_elim1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | equiv_elim2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_equiv_elim1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_equiv_elim2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | xor_elim1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | xor_elim2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_xor_elim1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_xor_elim2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_elim1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_elim2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_ite_elim1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_ite_elim2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | not_and =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_and_pos =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_and_neg =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_or_pos =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_or_neg =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_implies_pos =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_implies_neg1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_implies_neg2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_equiv_pos1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_equiv_pos2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_equiv_neg1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_equiv_neg2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_xor_pos1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_xor_pos2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_xor_neg1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_xor_neg2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_ite_pos1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_ite_pos2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_ite_pos3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_ite_neg1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_ite_neg2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cnf_ite_neg3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arrays_read_over_write =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arrays_read_over_write_contra =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arrays_read_over_write_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arrays_ext =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | refl =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | symm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | trans =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | cong =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | nary_cong =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | pairwise_cong =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | true_intro =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | true_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | false_intro =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | false_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ho_cong =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | distinct_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | distinct_true =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | distinct_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_sum_ub =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_mult_pos =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_mult_neg =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_trichotomy =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | int_tight_ub =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | int_tight_lb =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_mult_tangent =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_mult_sign =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_mult_abs_comparison =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_reduction =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_poly_norm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_poly_norm_rel =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_repeat_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_smulo_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_umulo_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_bitwise_slicing =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_bitblast_step =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_poly_norm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_poly_norm_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | string_length_pos =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | string_length_non_empty =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | concat_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | concat_unify =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | concat_csplit =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | concat_split =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | concat_lprop =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | concat_cprop =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | string_decompose =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | exists_string_length =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | string_code_inj =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | string_seq_unit_inj =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_inter =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_concat =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_unfold_pos =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_unfold_neg_concat_fixed =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_unfold_neg =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | string_ext =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | string_reduction =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | string_eager_reduction =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_string_pred_entail =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_string_pred_safe_approx =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_eval =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_consume =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_loop_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_eq_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_inter_inclusion =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_union_inclusion =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_concat_star_char =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_sigma =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_sigma_star =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_ctn_multiset_subset =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_overlap_split_ctn =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_overlap_endpoints_ctn =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_overlap_endpoints_indexof =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_overlap_endpoints_replace =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_re_eval =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_re_eval =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_re_all_eval =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | seq_eval_op =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_singleton_inj =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_ext =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_eval_op =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_insert_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ubv_to_int_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | int_to_bv_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | instantiate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | skolemize =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | skolem_intro =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | alpha_equiv =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | beta_reduce =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | quant_var_reordering =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | exists_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | quant_unused_vars =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | quant_merge_prenex =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | quant_miniscope_and =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | quant_miniscope_or =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | quant_miniscope_ite =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | quant_var_elim_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | quant_dt_split =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_split =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_inst =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_collapse_selector =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_collapse_tester =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_collapse_tester_singleton =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_cons_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_cons_eq_clash =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_cycle =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_collapse_updater =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | dt_updater_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_div_total_zero_real =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_div_total_zero_int =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_div_total =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_div_total_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_div_total_zero =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_div_total_neg =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_mod_total =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_mod_total_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_mod_total_zero =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_mod_total_neg =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_elim_gt =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_elim_lt =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_elim_int_gt =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_elim_int_lt =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_elim_leq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_leq_norm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_geq_tighten =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_geq_norm1_int =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_geq_norm1_real =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_eq_elim_real =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_eq_elim_int =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_to_int_elim_to_real =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_mod_over_mod_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_mod_over_mod =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_mod_over_mod_mult =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_eq_conflict =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_int_geq_tighten =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_divisible_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_abs_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_abs_int_gt =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_abs_real_gt =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_geq_ite_lift =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_leq_ite_lift =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_min_lt1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_min_lt2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_max_geq1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | arith_max_geq2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | array_read_over_write =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | array_read_over_write2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | array_store_overwrite =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | array_store_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | array_read_over_write_split =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | array_store_swap =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_double_not_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_not_true =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_not_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_eq_true =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_eq_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_eq_nrefl =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_impl_false1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_impl_false2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_impl_true1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_impl_true2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_impl_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_dual_impl_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_and_conf =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_and_conf2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_or_taut =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_or_taut2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_or_de_morgan =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_implies_de_morgan =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_and_de_morgan =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_or_and_distrib =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_implies_or_distrib =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_xor_refl =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_xor_nrefl =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_xor_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_xor_true =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_xor_comm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_xor_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_not_xor_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_not_eq_elim1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_not_eq_elim2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_neg_branch =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_then_true =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_else_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_then_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_else_true =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_then_lookahead_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_else_lookahead_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_then_lookahead_not_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_else_lookahead_not_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_expand =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bool_not_ite_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_true_cond =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_false_cond =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_not_cond =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_eq_branch =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_then_lookahead =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_else_lookahead =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_then_neg_lookahead =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | ite_else_neg_lookahead =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_concat_extract_merge =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_extract =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_whole =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_concat_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_concat_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_concat_3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_concat_4 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_eq_extract_elim1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_eq_extract_elim2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_eq_extract_elim3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_not =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_sign_extend_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_sign_extend_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_sign_extend_3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_not_xor =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_and_simplify_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_and_simplify_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_or_simplify_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_or_simplify_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xor_simplify_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xor_simplify_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xor_simplify_3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ult_add_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_mult_slt_mult_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_mult_slt_mult_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_commutative_xor =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_commutative_comp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_zero_extend_eliminate_0 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sign_extend_eliminate_0 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_not_neq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ult_ones =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_concat_merge_const =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_commutative_add =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sub_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_width_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_width_one_not =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_eq_xor_solve =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_eq_not_solve =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ugt_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_uge_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sgt_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sge_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sle_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_redor_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_redand_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ule_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_comp_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_rotate_left_eliminate_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_rotate_left_eliminate_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_rotate_right_eliminate_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_rotate_right_eliminate_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_nand_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_nor_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xnor_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sdiv_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_zero_extend_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_uaddo_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_saddo_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sdivo_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_smod_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_srem_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_usubo_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ssubo_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_nego_eliminate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_equal_children =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_const_children_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_const_children_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_equal_cond_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_equal_cond_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_equal_cond_3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_merge_then_if =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_merge_else_if =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_merge_then_else =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ite_merge_else_else =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_shl_by_const_0 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_shl_by_const_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_shl_by_const_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_lshr_by_const_0 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_lshr_by_const_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_lshr_by_const_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ashr_by_const_0 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ashr_by_const_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ashr_by_const_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_and_concat_pullup =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_or_concat_pullup =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xor_concat_pullup =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_and_concat_pullup2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_or_concat_pullup2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xor_concat_pullup2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_and_concat_pullup3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_or_concat_pullup3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xor_concat_pullup3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xor_duplicate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xor_ones =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_xor_not =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_not_idemp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ult_zero_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ult_zero_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ult_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_lt_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ule_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ule_zero =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_zero_ule =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sle_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ule_max =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_not_ult =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_mult_pow2_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_mult_pow2_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_mult_pow2_2b =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_extract_mult_leading_bit =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_udiv_pow2_not_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_udiv_zero =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_udiv_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_urem_pow2_not_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_urem_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_urem_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_shl_zero =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_lshr_zero =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ashr_zero =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ugt_urem =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_ult_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_merge_sign_extend_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_merge_sign_extend_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sign_extend_eq_const_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sign_extend_eq_const_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_zero_extend_eq_const_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_zero_extend_eq_const_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_zero_extend_ult_const_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_zero_extend_ult_const_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sign_extend_ult_const_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sign_extend_ult_const_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sign_extend_ult_const_3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | bv_sign_extend_ult_const_4 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_eq_singleton_emp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_member_singleton =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_member_emp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_subset_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_union_comm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_inter_comm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_inter_emp1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_inter_emp2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_minus_emp1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_minus_emp2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_union_emp1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_union_emp2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_inter_member =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_minus_member =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_union_member =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_choose_singleton =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_minus_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_is_empty_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | sets_is_singleton_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_ctn_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_ctn_full_false1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_ctn_full_false2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_len_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_empty_str =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_empty_range =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_empty_start =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_empty_start_neg =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_substr_start_geq_len =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_eq_empty =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_z_eq_empty_leq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_eq_empty_leq_len =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_len_replace_inv =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_len_replace_all_inv =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_len_update_inv =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_update_in_first_concat =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_len_substr_in_range =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_concat_clash =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_concat_clash_rev =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_concat_clash2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_concat_clash2_rev =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_concat_unify =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_concat_unify_rev =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_concat_unify_base =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_concat_unify_base_rev =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_prefixof_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_suffixof_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_prefixof_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_suffixof_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_prefixof_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_suffixof_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_combine1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_combine2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_combine3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_combine4 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_concat1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_concat2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_replace =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_full =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_full_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_refl =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_concat_find =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_concat_find_contra =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_split_char =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_leq_len_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_emp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_char =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_at_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_id =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_prefix =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_no_contains =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_find_base =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_find_first_concat =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_empty =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_one_pre =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_find_pre =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_all_no_contains =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_all_empty =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_all_id =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_all_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_re_none =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_re_all_none =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_len_concat_rec =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_len_eq_zero_concat_rec =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_len_eq_zero_base =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_no_contains =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_oob =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_oob2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_contains_pre =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_contains_concat_pre =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_find_emp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_eq_irr =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_re_none =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_indexof_re_emp_re =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_to_lower_concat =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_to_upper_concat =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_to_lower_upper =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_to_upper_lower =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_to_lower_len =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_to_upper_len =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_to_lower_from_int =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_to_upper_from_int =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_to_int_concat_neg_one =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_is_digit_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_leq_empty =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_leq_empty_eq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_leq_concat_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_leq_concat_true =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_leq_concat_base_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_leq_concat_base_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_lt_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_from_int_no_ctn_nondigit =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_ctn_contra =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_ctn =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_dual_ctn =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_dual_ctn_false =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_self_ctn_simp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_replace_emp_ctn_src =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_char_start_eq_len =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_repl_char =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_repl_self_tgt_char =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_repl_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_contains_repl_tgt =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_len_id =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_src_tgt_no_ctn =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_tgt_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_tgt_no_ctn =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_src_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_src_inv_no_ctn1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_src_inv_no_ctn2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_src_inv_no_ctn3 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_dual_self =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_dual_ite1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_dual_ite2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_repl_repl_lookahead_id_simp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_all_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_opt_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_diff_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_plus_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_repeat_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_concat_star_swap =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_concat_star_repeat =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_concat_star_subsume1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_concat_star_subsume2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_concat_merge =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_union_all =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_union_const_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_inter_all =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_star_none =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_star_emp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_star_star =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_range_refl =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_range_emp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_range_non_singleton_1 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_range_non_singleton_2 =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_star_union_char =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_star_union_drop_emp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_loop_neg =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_inter_cstring =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_inter_cstring_neg =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_len_include =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_len_include_pre =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_substr_len_norm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | seq_len_rev =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | seq_rev_rev =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | seq_rev_concat =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_repl_self_emp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_repl_no_change =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_repl_tgt_eq_len =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_repl_len_one_emp_prefix =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_repl_emp_tgt_nemp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_repl_nemp_src_emp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_eq_repl_self_src =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | seq_len_unit =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | seq_nth_unit =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | seq_rev_unit =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_in_empty =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_in_sigma =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_in_sigma_star =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_in_cstring =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | re_in_comp =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_union_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_inter_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_range_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_contains =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_from_int_nemp_dig_range =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | str_in_re_from_int_dig_range =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | eq_refl =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | eq_symm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | eq_cond_deq =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | eq_ite_lift =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | distinct_binary_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | uf_bv2nat_int2bv =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | uf_bv2nat_int2bv_extend =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | uf_bv2nat_int2bv_extract =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | uf_int2bv_bv2nat =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | uf_bv2nat_geq_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | uf_int2bv_bvult_equiv =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | uf_int2bv_bvule_equiv =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | uf_sbv_to_int_elim =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | evaluate =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | distinct_values =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | aci_norm =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | absorb =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)
  | distinct_card_conflict =>
      cases args <;> cases premises <;> exact False.elim (hProg rfl)

