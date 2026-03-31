import Cpc.Lemmas
import Cpc.Proofs.TypePreservation.Common

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

def eo_has_smt_translation (t : Term) : Prop :=
  Not (__smtx_typeof (__eo_to_smt t) = SmtType.None)

def eo_has_bool_type (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Bool

structure RuleResultFacts (M : SmtModel) (P : Term) : Prop where
  true_in_model : eo_interprets M P true
  has_smt_translation : eo_has_smt_translation P

def premiseAndFormula : List Term -> Term
  | [] => Term.Boolean true
  | p :: ps => Term.Apply (Term.Apply Term.and p) (premiseAndFormula ps)

def AllInterpretedTrue (M : SmtModel) (ts : List Term) : Prop :=
  ∀ t ∈ ts, eo_interprets M t true

def AllHaveSmtTranslation (ts : List Term) : Prop :=
  ∀ t ∈ ts, eo_has_smt_translation t

def AllHaveBoolType (ts : List Term) : Prop :=
  ∀ t ∈ ts, eo_has_bool_type t

structure StepRuleSpecNArgMPrem (M : SmtModel) (mk : List Term -> List Term -> Term) : Prop where
  facts_of_true :
    ∀ args premises,
      AllInterpretedTrue M premises ->
      mk args premises ≠ Term.Stuck ->
      RuleResultFacts M (mk args premises)
  bool_of_translation :
    ∀ args premises,
      AllHaveSmtTranslation args ->
      AllHaveBoolType premises ->
      mk args premises ≠ Term.Stuck ->
      eo_has_bool_type (mk args premises)

end RuleProofs

open RuleProofs

/- The theorem statements.
   CRule.scope is intentionally omitted for now, matching the requested scaffold. -/

theorem spec___eo_prog_process_scope (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_process_scope a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_ite_eq a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_split (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_split a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_resolution (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1, p2] => __eo_prog_resolution a1 a2 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_chain_resolution (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], premises => __eo_prog_chain_resolution a1 a2 (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_chain_m_resolution (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], premises => __eo_prog_chain_m_resolution a1 a2 a3 (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_factoring (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_factoring (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_reordering (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_reordering a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_eq_resolve (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1, p2] => __eo_prog_eq_resolve (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_modus_ponens (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1, p2] => __eo_prog_modus_ponens (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_not_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_not_elim (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_contra (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1, p2] => __eo_prog_contra (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_and_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_and_elim a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_and_intro (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], premises => __eo_prog_and_intro (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_or_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_not_or_elim a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_implies_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_implies_elim (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_implies_elim1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_implies_elim1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_implies_elim2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_implies_elim2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_equiv_elim1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_equiv_elim1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_equiv_elim2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_equiv_elim2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_equiv_elim1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_equiv_elim1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_equiv_elim2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_equiv_elim2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_xor_elim1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_xor_elim1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_xor_elim2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_xor_elim2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_xor_elim1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_xor_elim1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_xor_elim2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_xor_elim2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_elim1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_ite_elim1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_elim2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_ite_elim2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_ite_elim1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_ite_elim1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_ite_elim2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_ite_elim2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_not_and (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_not_and (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_and_pos (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_cnf_and_pos a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_and_neg (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_and_neg a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_or_pos (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_or_pos a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_or_neg (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_cnf_or_neg a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_implies_pos (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_implies_pos a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_implies_neg1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_implies_neg1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_implies_neg2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_implies_neg2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_equiv_pos1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_equiv_pos1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_equiv_pos2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_equiv_pos2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_equiv_neg1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_equiv_neg1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_equiv_neg2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_equiv_neg2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_xor_pos1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_xor_pos1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_xor_pos2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_xor_pos2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_xor_neg1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_xor_neg1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_xor_neg2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_xor_neg2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_ite_pos1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_ite_pos1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_ite_pos2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_ite_pos2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_ite_pos3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_ite_pos3 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_ite_neg1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_ite_neg1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_ite_neg2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_ite_neg2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cnf_ite_neg3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_cnf_ite_neg3 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arrays_read_over_write (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_arrays_read_over_write a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arrays_read_over_write_contra (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_arrays_read_over_write_contra (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arrays_read_over_write_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arrays_read_over_write_1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arrays_ext (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_arrays_ext (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_refl (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_refl a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_symm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_symm (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_trans (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], premises => __eo_prog_trans (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_cong (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], premises => __eo_prog_cong a1 (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_nary_cong (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], premises => __eo_prog_nary_cong a1 (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_pairwise_cong (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], premises => __eo_prog_pairwise_cong a1 (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_true_intro (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_true_intro (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_true_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_true_elim (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_false_intro (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_false_intro (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_false_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_false_elim (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ho_cong (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], premises => __eo_prog_ho_cong (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_distinct_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_distinct_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_distinct_true (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_distinct_true a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_distinct_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_distinct_false a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_sum_ub (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], premises => __eo_prog_arith_sum_ub (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_mult_pos (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_mult_pos a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_mult_neg (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_mult_neg a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_trichotomy (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1, p2] => __eo_prog_arith_trichotomy (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_int_tight_ub (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_int_tight_ub (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_int_tight_lb (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_int_tight_lb (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_mult_tangent (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [] => __eo_prog_arith_mult_tangent a1 a2 a3 a4 a5 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_mult_sign (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_mult_sign a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_mult_abs_comparison (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], premises => __eo_prog_arith_mult_abs_comparison (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_reduction (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_reduction a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_poly_norm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_poly_norm a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_poly_norm_rel (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_arith_poly_norm_rel a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_repeat_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_repeat_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_smulo_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_smulo_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_umulo_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_umulo_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_bitwise_slicing (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_bitwise_slicing a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_bitblast_step (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_bitblast_step a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_poly_norm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_poly_norm a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_poly_norm_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_bv_poly_norm_eq a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_string_length_pos (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_string_length_pos a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_string_length_non_empty (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_string_length_non_empty (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_concat_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_concat_eq a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_concat_unify (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1, p2] => __eo_prog_concat_unify a1 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_concat_csplit (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1, p2] => __eo_prog_concat_csplit a1 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_concat_split (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1, p2] => __eo_prog_concat_split a1 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_concat_lprop (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1, p2] => __eo_prog_concat_lprop a1 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_concat_cprop (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1, p2] => __eo_prog_concat_cprop a1 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_string_decompose (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1, p2] => __eo_prog_string_decompose a1 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_exists_string_length (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_exists_string_length a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_string_code_inj (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_string_code_inj a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_string_seq_unit_inj (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_string_seq_unit_inj (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_inter (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1, p2] => __eo_prog_re_inter (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_concat (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], premises => __eo_prog_re_concat (Proof.pf (premiseAndFormula premises)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_unfold_pos (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_re_unfold_pos (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_unfold_neg_concat_fixed (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_re_unfold_neg_concat_fixed a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_unfold_neg (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_re_unfold_neg (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_string_ext (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_string_ext (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_string_reduction (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_string_reduction a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_string_eager_reduction (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_string_eager_reduction a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_string_pred_entail (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_string_pred_entail a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_string_pred_safe_approx (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_string_pred_safe_approx a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_eval (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_in_re_eval a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_consume (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_in_re_consume a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_loop_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_loop_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_eq_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_eq_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_inter_inclusion (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_inter_inclusion a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_union_inclusion (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_union_inclusion a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_concat_star_char (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_in_re_concat_star_char a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_sigma (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_in_re_sigma a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_sigma_star (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_in_re_sigma_star a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_ctn_multiset_subset (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_ctn_multiset_subset a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_overlap_split_ctn (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_overlap_split_ctn a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_overlap_endpoints_ctn (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_overlap_endpoints_ctn a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_overlap_endpoints_indexof (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_overlap_endpoints_indexof a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_overlap_endpoints_replace (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_overlap_endpoints_replace a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_re_eval (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_indexof_re_eval a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_re_eval (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_replace_re_eval a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_re_all_eval (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_replace_re_all_eval a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_seq_eval_op (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_seq_eval_op a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_singleton_inj (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_sets_singleton_inj (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_ext (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_sets_ext (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_eval_op (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_sets_eval_op a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_insert_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_sets_insert_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ubv_to_int_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_ubv_to_int_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_int_to_bv_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_int_to_bv_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_instantiate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_instantiate a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_skolemize (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [p1] => __eo_prog_skolemize (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_skolem_intro (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_skolem_intro a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_alpha_equiv (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_alpha_equiv a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_beta_reduce (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_beta_reduce a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_quant_var_reordering (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_quant_var_reordering a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_exists_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_exists_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_quant_unused_vars (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_quant_unused_vars a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_quant_merge_prenex (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_quant_merge_prenex a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_quant_miniscope_and (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_quant_miniscope_and a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_quant_miniscope_or (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_quant_miniscope_or a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_quant_miniscope_ite (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_quant_miniscope_ite a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_quant_var_elim_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_quant_var_elim_eq a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_quant_dt_split (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_quant_dt_split a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_split (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_split a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_inst (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_inst a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_collapse_selector (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_collapse_selector a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_collapse_tester (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_collapse_tester a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_collapse_tester_singleton (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_collapse_tester_singleton a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_cons_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_cons_eq a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_cons_eq_clash (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_cons_eq_clash a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_cycle (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_cycle a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_collapse_updater (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_collapse_updater a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_dt_updater_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_dt_updater_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_div_total_zero_real (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_div_total_zero_real a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_div_total_zero_int (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_div_total_zero_int a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_div_total (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_arith_int_div_total a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_div_total_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_int_div_total_one a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_div_total_zero (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_int_div_total_zero a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_div_total_neg (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_arith_int_div_total_neg a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_mod_total (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_arith_int_mod_total a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_mod_total_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_int_mod_total_one a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_mod_total_zero (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_int_mod_total_zero a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_mod_total_neg (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_arith_int_mod_total_neg a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_elim_gt (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_elim_gt a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_elim_lt (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_elim_lt a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_elim_int_gt (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_elim_int_gt a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_elim_int_lt (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_elim_int_lt a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_elim_leq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_elim_leq a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_leq_norm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_leq_norm a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_geq_tighten (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_geq_tighten a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_geq_norm1_int (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_geq_norm1_int a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_geq_norm1_real (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_geq_norm1_real a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_eq_elim_real (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_eq_elim_real a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_eq_elim_int (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_eq_elim_int a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_to_int_elim_to_real (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_arith_to_int_elim_to_real a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_mod_over_mod_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_arith_mod_over_mod_1 a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_mod_over_mod (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_arith_mod_over_mod a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_mod_over_mod_mult (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_arith_mod_over_mod_mult a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_eq_conflict (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_arith_int_eq_conflict a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_int_geq_tighten (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_arith_int_geq_tighten a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_divisible_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_arith_divisible_elim a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_abs_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_abs_eq a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_abs_int_gt (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_abs_int_gt a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_abs_real_gt (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_abs_real_gt a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_geq_ite_lift (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_arith_geq_ite_lift a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_leq_ite_lift (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_arith_leq_ite_lift a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_min_lt1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_min_lt1 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_min_lt2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_min_lt2 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_max_geq1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_max_geq1 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_arith_max_geq2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_arith_max_geq2 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_array_read_over_write (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_array_read_over_write a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_array_read_over_write2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_array_read_over_write2 a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_array_store_overwrite (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_array_store_overwrite a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_array_store_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_array_store_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_array_read_over_write_split (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_array_read_over_write_split a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_array_store_swap (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1] => __eo_prog_array_store_swap a1 a2 a3 a4 a5 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_double_not_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_double_not_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_not_true (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_bool_not_true a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_not_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_bool_not_false a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_eq_true (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_eq_true a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_eq_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_eq_false a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_eq_nrefl (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_eq_nrefl a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_impl_false1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_impl_false1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_impl_false2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_impl_false2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_impl_true1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_impl_true1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_impl_true2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_impl_true2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_impl_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bool_impl_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_dual_impl_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bool_dual_impl_eq a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_and_conf (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bool_and_conf a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_and_conf2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bool_and_conf2 a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_or_taut (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bool_or_taut a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_or_taut2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bool_or_taut2 a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_or_de_morgan (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_bool_or_de_morgan a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_implies_de_morgan (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bool_implies_de_morgan a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_and_de_morgan (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_bool_and_de_morgan a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_or_and_distrib (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [] => __eo_prog_bool_or_and_distrib a1 a2 a3 a4 a5 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_implies_or_distrib (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bool_implies_or_distrib a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_xor_refl (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_xor_refl a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_xor_nrefl (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_xor_nrefl a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_xor_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_xor_false a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_xor_true (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bool_xor_true a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_xor_comm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bool_xor_comm a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_xor_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bool_xor_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_not_xor_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bool_not_xor_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_not_eq_elim1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bool_not_eq_elim1 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_not_eq_elim2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bool_not_eq_elim2 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_neg_branch (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_ite_neg_branch a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_then_true (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_then_true a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_else_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_else_false a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_then_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_then_false a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_else_true (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_else_true a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_then_lookahead_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_then_lookahead_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_else_lookahead_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_else_lookahead_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_then_lookahead_not_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_then_lookahead_not_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_else_lookahead_not_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_else_lookahead_not_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_expand (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_ite_expand a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bool_not_ite_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_bool_not_ite_elim a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_true_cond (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_true_cond a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_false_cond (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_false_cond a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_not_cond (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_ite_not_cond a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_eq_branch (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_ite_eq_branch a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_then_lookahead (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_ite_then_lookahead a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_else_lookahead (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_ite_else_lookahead a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_then_neg_lookahead (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_ite_then_neg_lookahead a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_ite_else_neg_lookahead (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_ite_else_neg_lookahead a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_concat_extract_merge (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1] => __eo_prog_bv_concat_extract_merge a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_extract (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2] => __eo_prog_bv_extract_extract a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_whole (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_bv_extract_whole a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_concat_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1] => __eo_prog_bv_extract_concat_1 a1 a2 a3 a4 a5 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_concat_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2, p3, p4] => __eo_prog_bv_extract_concat_2 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_concat_3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2, p3] => __eo_prog_bv_extract_concat_3 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_concat_4 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1] => __eo_prog_bv_extract_concat_4 a1 a2 a3 a4 a5 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_eq_extract_elim1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2, p3, p4, p5] => __eo_prog_bv_eq_extract_elim1 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) (Proof.pf (p5)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_eq_extract_elim2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_bv_eq_extract_elim2 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_eq_extract_elim3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_bv_eq_extract_elim3 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_not (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_bv_extract_not a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_sign_extend_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_bv_extract_sign_extend_1 a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_sign_extend_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6], [p1, p2, p3, p4] => __eo_prog_bv_extract_sign_extend_2 a1 a2 a3 a4 a5 a6 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_sign_extend_3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6], [p1, p2, p3] => __eo_prog_bv_extract_sign_extend_3 a1 a2 a3 a4 a5 a6 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_not_xor (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_bv_not_xor a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_and_simplify_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1] => __eo_prog_bv_and_simplify_1 a1 a2 a3 a4 a5 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_and_simplify_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1] => __eo_prog_bv_and_simplify_2 a1 a2 a3 a4 a5 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_or_simplify_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1] => __eo_prog_bv_or_simplify_1 a1 a2 a3 a4 a5 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_or_simplify_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1] => __eo_prog_bv_or_simplify_2 a1 a2 a3 a4 a5 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xor_simplify_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bv_xor_simplify_1 a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xor_simplify_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bv_xor_simplify_2 a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xor_simplify_3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bv_xor_simplify_3 a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ult_add_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2] => __eo_prog_bv_ult_add_one a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_mult_slt_mult_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2] => __eo_prog_bv_mult_slt_mult_1 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_mult_slt_mult_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2] => __eo_prog_bv_mult_slt_mult_2 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_commutative_xor (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_commutative_xor a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_commutative_comp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_commutative_comp a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_zero_extend_eliminate_0 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_zero_extend_eliminate_0 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sign_extend_eliminate_0 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_sign_extend_eliminate_0 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_not_neq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_bv_not_neq a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ult_ones (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_bv_ult_ones a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_concat_merge_const (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1] => __eo_prog_bv_concat_merge_const a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_commutative_add (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_commutative_add a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sub_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_sub_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_width_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_ite_width_one a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_width_one_not (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_ite_width_one_not a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_eq_xor_solve (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_bv_eq_xor_solve a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_eq_not_solve (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_eq_not_solve a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ugt_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_ugt_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_uge_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_uge_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sgt_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_sgt_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sge_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_sge_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sle_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_sle_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_redor_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_bv_redor_eliminate a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_redand_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_bv_redand_eliminate a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ule_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_ule_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_comp_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_comp_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_rotate_left_eliminate_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3, p4] => __eo_prog_bv_rotate_left_eliminate_1 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_rotate_left_eliminate_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_bv_rotate_left_eliminate_2 a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_rotate_right_eliminate_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3, p4] => __eo_prog_bv_rotate_right_eliminate_1 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_rotate_right_eliminate_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_bv_rotate_right_eliminate_2 a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_nand_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_nand_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_nor_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_nor_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xnor_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_xnor_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sdiv_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_bv_sdiv_eliminate a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_zero_extend_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_zero_extend_eliminate a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_uaddo_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_bv_uaddo_eliminate a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_saddo_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_bv_saddo_eliminate a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sdivo_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_bv_sdivo_eliminate a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_smod_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_bv_smod_eliminate a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_srem_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_bv_srem_eliminate a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_usubo_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_bv_usubo_eliminate a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ssubo_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_bv_ssubo_eliminate a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_nego_eliminate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_bv_nego_eliminate a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_equal_children (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_ite_equal_children a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_const_children_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_ite_const_children_1 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_const_children_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_ite_const_children_2 a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_equal_cond_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bv_ite_equal_cond_1 a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_equal_cond_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bv_ite_equal_cond_2 a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_equal_cond_3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [] => __eo_prog_bv_ite_equal_cond_3 a1 a2 a3 a4 a5 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_merge_then_if (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bv_ite_merge_then_if a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_merge_else_if (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bv_ite_merge_else_if a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_merge_then_else (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bv_ite_merge_then_else a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ite_merge_else_else (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_bv_ite_merge_else_else a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_shl_by_const_0 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_shl_by_const_0 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_shl_by_const_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_bv_shl_by_const_1 a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_shl_by_const_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2, p3] => __eo_prog_bv_shl_by_const_2 a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_lshr_by_const_0 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_lshr_by_const_0 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_lshr_by_const_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_bv_lshr_by_const_1 a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_lshr_by_const_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_bv_lshr_by_const_2 a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ashr_by_const_0 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_ashr_by_const_0 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ashr_by_const_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_bv_ashr_by_const_1 a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ashr_by_const_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_bv_ashr_by_const_2 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_and_concat_pullup (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8], [p1, p2, p3] => __eo_prog_bv_and_concat_pullup a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_or_concat_pullup (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8], [p1, p2, p3] => __eo_prog_bv_or_concat_pullup a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xor_concat_pullup (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8], [p1, p2, p3] => __eo_prog_bv_xor_concat_pullup a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_and_concat_pullup2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8], [p1, p2, p3] => __eo_prog_bv_and_concat_pullup2 a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_or_concat_pullup2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8], [p1, p2, p3] => __eo_prog_bv_or_concat_pullup2 a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xor_concat_pullup2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8], [p1, p2, p3] => __eo_prog_bv_xor_concat_pullup2 a1 a2 a3 a4 a5 a6 a7 a8 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_and_concat_pullup3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10], [p1, p2, p3, p4, p5] => __eo_prog_bv_and_concat_pullup3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) (Proof.pf (p5)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_or_concat_pullup3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10], [p1, p2, p3, p4, p5] => __eo_prog_bv_or_concat_pullup3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) (Proof.pf (p5)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xor_concat_pullup3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8, a9, a10], [p1, p2, p3, p4, p5] => __eo_prog_bv_xor_concat_pullup3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) (Proof.pf (p5)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xor_duplicate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_bv_xor_duplicate a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xor_ones (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_bv_xor_ones a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_xor_not (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_xor_not a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_not_idemp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_not_idemp a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ult_zero_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_ult_zero_1 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ult_zero_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_ult_zero_2 a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ult_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_ult_self a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_lt_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_lt_self a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ule_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_ule_self a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ule_zero (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_ule_zero a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_zero_ule (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_zero_ule a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sle_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_bv_sle_self a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ule_max (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_bv_ule_max a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_not_ult (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_not_ult a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_mult_pow2_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2, p3] => __eo_prog_bv_mult_pow2_1 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_mult_pow2_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2, p3] => __eo_prog_bv_mult_pow2_2 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_mult_pow2_2b (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_bv_mult_pow2_2b a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_extract_mult_leading_bit (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7, a8, a9], [p1, p2, p3] => __eo_prog_bv_extract_mult_leading_bit a1 a2 a3 a4 a5 a6 a7 a8 a9 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_udiv_pow2_not_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3, p4] => __eo_prog_bv_udiv_pow2_not_one a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_udiv_zero (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_udiv_zero a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_udiv_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_udiv_one a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_urem_pow2_not_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3, p4] => __eo_prog_bv_urem_pow2_not_one a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_urem_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_urem_one a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_urem_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_bv_urem_self a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_shl_zero (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_shl_zero a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_lshr_zero (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_lshr_zero a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ashr_zero (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_bv_ashr_zero a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ugt_urem (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_bv_ugt_urem a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_ult_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_bv_ult_one a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_merge_sign_extend_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_bv_merge_sign_extend_1 a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_merge_sign_extend_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_bv_merge_sign_extend_2 a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sign_extend_eq_const_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2, p3] => __eo_prog_bv_sign_extend_eq_const_1 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sign_extend_eq_const_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6, a7], [p1, p2, p3] => __eo_prog_bv_sign_extend_eq_const_2 a1 a2 a3 a4 a5 a6 a7 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_zero_extend_eq_const_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6], [p1, p2] => __eo_prog_bv_zero_extend_eq_const_1 a1 a2 a3 a4 a5 a6 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_zero_extend_eq_const_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6], [p1, p2] => __eo_prog_bv_zero_extend_eq_const_2 a1 a2 a3 a4 a5 a6 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_zero_extend_ult_const_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2] => __eo_prog_bv_zero_extend_ult_const_1 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_zero_extend_ult_const_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2] => __eo_prog_bv_zero_extend_ult_const_2 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sign_extend_ult_const_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2] => __eo_prog_bv_sign_extend_ult_const_1 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sign_extend_ult_const_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_bv_sign_extend_ult_const_2 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sign_extend_ult_const_3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2] => __eo_prog_bv_sign_extend_ult_const_3 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_bv_sign_extend_ult_const_4 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_bv_sign_extend_ult_const_4 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_eq_singleton_emp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_sets_eq_singleton_emp a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_member_singleton (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_sets_member_singleton a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_member_emp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_sets_member_emp a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_subset_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_sets_subset_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_union_comm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_sets_union_comm a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_inter_comm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_sets_inter_comm a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_inter_emp1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_sets_inter_emp1 a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_inter_emp2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_sets_inter_emp2 a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_minus_emp1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_sets_minus_emp1 a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_minus_emp2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_sets_minus_emp2 a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_union_emp1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_sets_union_emp1 a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_union_emp2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_sets_union_emp2 a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_inter_member (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_sets_inter_member a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_minus_member (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_sets_minus_member a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_union_member (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_sets_union_member a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_choose_singleton (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_sets_choose_singleton a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_minus_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_sets_minus_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_is_empty_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_sets_is_empty_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_sets_is_singleton_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_sets_is_singleton_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_ctn_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_eq_ctn_false a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_ctn_full_false1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_eq_ctn_full_false1 a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_ctn_full_false2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_eq_ctn_full_false2 a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_len_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_eq_len_false a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_empty_str (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_substr_empty_str a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_empty_range (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_substr_empty_range a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_empty_start (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_substr_empty_start a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_empty_start_neg (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_substr_empty_start_neg a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_substr_start_geq_len (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6], [p1] => __eo_prog_str_substr_substr_start_geq_len a1 a2 a3 a4 a5 a6 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_eq_empty (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2, p3] => __eo_prog_str_substr_eq_empty a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_z_eq_empty_leq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_str_substr_z_eq_empty_leq a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_eq_empty_leq_len (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2, p3] => __eo_prog_str_substr_eq_empty_leq_len a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_len_replace_inv (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_len_replace_inv a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_len_replace_all_inv (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_len_replace_all_inv a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_len_update_inv (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_str_len_update_inv a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_update_in_first_concat (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6], [p1, p2, p3, p4] => __eo_prog_str_update_in_first_concat a1 a2 a3 a4 a5 a6 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) (Proof.pf (p4)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_len_substr_in_range (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2, p3] => __eo_prog_str_len_substr_in_range a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_concat_clash (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_concat_clash a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_concat_clash_rev (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_concat_clash_rev a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_concat_clash2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_str_concat_clash2 a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_concat_clash2_rev (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_str_concat_clash2_rev a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_concat_unify (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [] => __eo_prog_str_concat_unify a1 a2 a3 a4 a5 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_concat_unify_rev (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [] => __eo_prog_str_concat_unify_rev a1 a2 a3 a4 a5 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_concat_unify_base (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_str_concat_unify_base a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_concat_unify_base_rev (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_str_concat_unify_base_rev a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_prefixof_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_prefixof_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_suffixof_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_suffixof_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_prefixof_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_prefixof_eq a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_suffixof_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_suffixof_eq a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_prefixof_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_prefixof_one a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_suffixof_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_suffixof_one a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_combine1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_str_substr_combine1 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_combine2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_str_substr_combine2 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_combine3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_str_substr_combine3 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_combine4 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_str_substr_combine4 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_concat1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_substr_concat1 a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_concat2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1] => __eo_prog_str_substr_concat2 a1 a2 a3 a4 a5 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_replace (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_substr_replace a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_full (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_substr_full a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_full_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_substr_full_eq a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_refl (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_contains_refl a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_concat_find (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_contains_concat_find a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_concat_find_contra (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_contains_concat_find_contra a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_split_char (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_contains_split_char a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_leq_len_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_contains_leq_len_eq a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_emp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_contains_emp a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_char (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_contains_char a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_at_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_at_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_replace_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_id (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_replace_id a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_prefix (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_str_replace_prefix a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_no_contains (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_replace_no_contains a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_find_base (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_str_replace_find_base a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_find_first_concat (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5, a6], [p1, p2, p3] => __eo_prog_str_replace_find_first_concat a1 a2 a3 a4 a5 a6 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_empty (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_replace_empty a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_one_pre (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1] => __eo_prog_str_replace_one_pre a1 a2 a3 a4 a5 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_find_pre (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_str_replace_find_pre a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_all_no_contains (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_replace_all_no_contains a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_all_empty (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_replace_all_empty a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_all_id (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_replace_all_id a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_all_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_replace_all_self a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_re_none (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_replace_re_none a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_re_all_none (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_replace_re_all_none a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_len_concat_rec (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_str_len_concat_rec a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_len_eq_zero_concat_rec (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_str_len_eq_zero_concat_rec a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_len_eq_zero_base (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_len_eq_zero_base a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_str_indexof_self a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_no_contains (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_indexof_no_contains a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_oob (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_indexof_oob a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_oob2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_indexof_oob2 a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_contains_pre (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_indexof_contains_pre a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_contains_concat_pre (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_str_indexof_contains_concat_pre a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_find_emp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2, p3] => __eo_prog_str_indexof_find_emp a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_eq_irr (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2, p3] => __eo_prog_str_indexof_eq_irr a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_re_none (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_indexof_re_none a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_indexof_re_emp_re (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2, p3] => __eo_prog_str_indexof_re_emp_re a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_to_lower_concat (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_str_to_lower_concat a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_to_upper_concat (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_str_to_upper_concat a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_to_lower_upper (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_to_lower_upper a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_to_upper_lower (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_to_upper_lower a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_to_lower_len (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_to_lower_len a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_to_upper_len (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_to_upper_len a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_to_lower_from_int (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_to_lower_from_int a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_to_upper_from_int (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_to_upper_from_int a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_to_int_concat_neg_one (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_str_to_int_concat_neg_one a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_is_digit_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_is_digit_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_leq_empty (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_leq_empty a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_leq_empty_eq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_leq_empty_eq a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_leq_concat_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2] => __eo_prog_str_leq_concat_false a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_leq_concat_true (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2, p3] => __eo_prog_str_leq_concat_true a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_leq_concat_base_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_str_leq_concat_base_1 a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_leq_concat_base_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_str_leq_concat_base_2 a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_lt_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_lt_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_from_int_no_ctn_nondigit (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1, p2] => __eo_prog_str_from_int_no_ctn_nondigit a1 a2 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_ctn_contra (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_substr_ctn_contra a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_ctn (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_str_substr_ctn a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_dual_ctn (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_replace_dual_ctn a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_dual_ctn_false (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_replace_dual_ctn_false a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_self_ctn_simp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_replace_self_ctn_simp a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_replace_emp_ctn_src (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_replace_emp_ctn_src a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_char_start_eq_len (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_substr_char_start_eq_len a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_repl_char (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_contains_repl_char a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_repl_self_tgt_char (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_contains_repl_self_tgt_char a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_repl_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_contains_repl_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_contains_repl_tgt (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_str_contains_repl_tgt a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_len_id (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_str_repl_repl_len_id a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_src_tgt_no_ctn (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_repl_repl_src_tgt_no_ctn a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_tgt_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_repl_repl_tgt_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_tgt_no_ctn (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_repl_repl_tgt_no_ctn a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_src_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_str_repl_repl_src_self a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_src_inv_no_ctn1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_repl_repl_src_inv_no_ctn1 a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_src_inv_no_ctn2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_repl_repl_src_inv_no_ctn2 a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_src_inv_no_ctn3 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4, a5], [p1, p2] => __eo_prog_str_repl_repl_src_inv_no_ctn3 a1 a2 a3 a4 a5 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_dual_self (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_repl_repl_dual_self a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_dual_ite1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_repl_repl_dual_ite1 a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_dual_ite2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_repl_repl_dual_ite2 a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_repl_repl_lookahead_id_simp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_str_repl_repl_lookahead_id_simp a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_all_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [] => Term.Apply (Term.Apply Term.eq Term.re_all) (Term.Apply Term.re_mult Term.re_allchar) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_opt_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_opt_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_diff_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_re_diff_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_plus_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_plus_elim a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_repeat_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_re_repeat_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_concat_star_swap (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_re_concat_star_swap a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_concat_star_repeat (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_re_concat_star_repeat a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_concat_star_subsume1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_re_concat_star_subsume1 a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_concat_star_subsume2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_re_concat_star_subsume2 a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_concat_merge (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_re_concat_merge a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_union_all (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_re_union_all a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_union_const_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_re_union_const_elim a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_inter_all (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_re_inter_all a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_star_none (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [], [] => Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_mult Term.re_none)) (Term.Apply Term.str_to_re (Term.String "")) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_star_emp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M
    (fun
      | [], [] =>
          let _v0 := (Term.Apply Term.str_to_re (Term.String ""))
          (Term.Apply (Term.Apply Term.eq (Term.Apply Term.re_mult _v0)) _v0)
      | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_star_star (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_star_star a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_range_refl (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_re_range_refl a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_range_emp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1, p2, p3] => __eo_prog_re_range_emp a1 a2 (Proof.pf (p1)) (Proof.pf (p2)) (Proof.pf (p3)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_range_non_singleton_1 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_re_range_non_singleton_1 a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_range_non_singleton_2 (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_re_range_non_singleton_2 a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_star_union_char (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_re_star_union_char a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_star_union_drop_emp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_re_star_union_drop_emp a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_loop_neg (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_re_loop_neg a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_inter_cstring (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_re_inter_cstring a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_inter_cstring_neg (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_re_inter_cstring_neg a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_len_include (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_substr_len_include a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_len_include_pre (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1] => __eo_prog_str_substr_len_include_pre a1 a2 a3 a4 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_substr_len_norm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_substr_len_norm a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_seq_len_rev (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_seq_len_rev a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_seq_rev_rev (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_seq_rev_rev a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_seq_rev_concat (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [] => __eo_prog_seq_rev_concat a1 a2 a3 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_repl_self_emp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_eq_repl_self_emp a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_repl_no_change (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_eq_repl_no_change a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_repl_tgt_eq_len (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_str_eq_repl_tgt_eq_len a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_repl_len_one_emp_prefix (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_str_eq_repl_len_one_emp_prefix a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_repl_emp_tgt_nemp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_eq_repl_emp_tgt_nemp a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_repl_nemp_src_emp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [p1, p2] => __eo_prog_str_eq_repl_nemp_src_emp a1 a2 a3 a4 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_eq_repl_self_src (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_eq_repl_self_src a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_seq_len_unit (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_seq_len_unit a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_seq_nth_unit (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_seq_nth_unit a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_seq_rev_unit (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_seq_rev_unit a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_in_empty (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_in_empty a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_in_sigma (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_in_sigma a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_in_sigma_star (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_re_in_sigma_star a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_in_cstring (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_re_in_cstring a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_re_in_comp (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_re_in_comp a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_union_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_str_in_re_union_elim a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_inter_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_str_in_re_inter_elim a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_range_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_str_in_re_range_elim a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_contains (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_str_in_re_contains a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_from_int_nemp_dig_range (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [p1] => __eo_prog_str_in_re_from_int_nemp_dig_range a1 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_str_in_re_from_int_dig_range (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_str_in_re_from_int_dig_range a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_eq_refl (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_eq_refl a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_eq_symm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_eq_symm a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_eq_cond_deq (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_eq_cond_deq a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_eq_ite_lift (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3, a4], [] => __eo_prog_eq_ite_lift a1 a2 a3 a4 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_distinct_binary_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_distinct_binary_elim a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_uf_bv2nat_int2bv (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [p1] => __eo_prog_uf_bv2nat_int2bv a1 a2 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_uf_bv2nat_int2bv_extend (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_uf_bv2nat_int2bv_extend a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_uf_bv2nat_int2bv_extract (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_uf_bv2nat_int2bv_extract a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_uf_int2bv_bv2nat (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_uf_int2bv_bv2nat a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_uf_bv2nat_geq_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1] => __eo_prog_uf_bv2nat_geq_elim a1 a2 a3 (Proof.pf (p1)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_uf_int2bv_bvult_equiv (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_uf_int2bv_bvult_equiv a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_uf_int2bv_bvule_equiv (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_uf_int2bv_bvule_equiv a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_uf_sbv_to_int_elim (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2, a3], [p1, p2] => __eo_prog_uf_sbv_to_int_elim a1 a2 a3 (Proof.pf (p1)) (Proof.pf (p2)) | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_evaluate (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_evaluate a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_distinct_values (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1, a2], [] => __eo_prog_distinct_values a1 a2 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_aci_norm (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_aci_norm a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_absorb (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_absorb a1 | _, _ => Term.Stuck) := by
  sorry

theorem spec___eo_prog_distinct_card_conflict (M : SmtModel) (hM : model_total_typed M) :
  StepRuleSpecNArgMPrem M (fun | [a1], [] => __eo_prog_distinct_card_conflict a1 | _, _ => Term.Stuck) := by
  sorry
