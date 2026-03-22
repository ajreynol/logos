import Cpc.SmtModel
import Cpc.Logos
import Cpc.Spec

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


/- The theorem statements -/

/- correctness theorem for __eo_prog_scope -/
theorem correct___eo_prog_scope (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_scope x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_process_scope -/
theorem correct___eo_prog_process_scope (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_process_scope x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_process_scope x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_eq -/
theorem correct___eo_prog_ite_eq (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_ite_eq x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_eq x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_split -/
theorem correct___eo_prog_split (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_split x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_split x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_resolution -/
theorem correct___eo_prog_resolution (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x3 true) ->
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_resolution x1 x2 (Proof.pf x3) (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_resolution x1 x2 (Proof.pf x3) (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_chain_resolution -/
theorem correct___eo_prog_chain_resolution (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_chain_resolution x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_chain_resolution x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_chain_m_resolution -/
theorem correct___eo_prog_chain_m_resolution (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_chain_m_resolution x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_chain_m_resolution x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_factoring -/
theorem correct___eo_prog_factoring (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_factoring (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_factoring (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_reordering -/
theorem correct___eo_prog_reordering (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_reordering x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_reordering x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_resolve -/
theorem correct___eo_prog_eq_resolve (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_eq_resolve (Proof.pf x1) (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_eq_resolve (Proof.pf x1) (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_modus_ponens -/
theorem correct___eo_prog_modus_ponens (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_modus_ponens (Proof.pf x1) (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_modus_ponens (Proof.pf x1) (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_not_elim -/
theorem correct___eo_prog_not_not_elim (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_not_elim (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_not_elim (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_contra -/
theorem correct___eo_prog_contra (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_and_elim -/
theorem correct___eo_prog_and_elim (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_and_elim x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_and_elim x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_and_intro -/
theorem correct___eo_prog_and_intro (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_and_intro (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_and_intro (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_or_elim -/
theorem correct___eo_prog_not_or_elim (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_not_or_elim x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_or_elim x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_implies_elim -/
theorem correct___eo_prog_implies_elim (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_implies_elim (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_implies_elim (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_implies_elim1 -/
theorem correct___eo_prog_not_implies_elim1 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_implies_elim1 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_implies_elim1 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_implies_elim2 -/
theorem correct___eo_prog_not_implies_elim2 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_implies_elim2 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_implies_elim2 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_equiv_elim1 -/
theorem correct___eo_prog_equiv_elim1 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_equiv_elim1 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_equiv_elim1 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_equiv_elim2 -/
theorem correct___eo_prog_equiv_elim2 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_equiv_elim2 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_equiv_elim2 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_equiv_elim1 -/
theorem correct___eo_prog_not_equiv_elim1 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_equiv_elim1 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_equiv_elim1 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_equiv_elim2 -/
theorem correct___eo_prog_not_equiv_elim2 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_equiv_elim2 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_equiv_elim2 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_xor_elim1 -/
theorem correct___eo_prog_xor_elim1 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_xor_elim1 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_xor_elim1 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_xor_elim2 -/
theorem correct___eo_prog_xor_elim2 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_xor_elim2 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_xor_elim2 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_xor_elim1 -/
theorem correct___eo_prog_not_xor_elim1 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_xor_elim1 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_xor_elim1 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_xor_elim2 -/
theorem correct___eo_prog_not_xor_elim2 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_xor_elim2 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_xor_elim2 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_elim1 -/
theorem correct___eo_prog_ite_elim1 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_ite_elim1 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_elim1 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_elim2 -/
theorem correct___eo_prog_ite_elim2 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_ite_elim2 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_elim2 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_ite_elim1 -/
theorem correct___eo_prog_not_ite_elim1 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_ite_elim1 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_ite_elim1 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_ite_elim2 -/
theorem correct___eo_prog_not_ite_elim2 (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_ite_elim2 (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_ite_elim2 (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_not_and -/
theorem correct___eo_prog_not_and (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_not_and (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_not_and (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_and_pos -/
theorem correct___eo_prog_cnf_and_pos (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_cnf_and_pos x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_and_pos x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_and_neg -/
theorem correct___eo_prog_cnf_and_neg (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_and_neg x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_and_neg x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_or_pos -/
theorem correct___eo_prog_cnf_or_pos (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_or_pos x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_or_pos x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_or_neg -/
theorem correct___eo_prog_cnf_or_neg (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_cnf_or_neg x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_or_neg x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_implies_pos -/
theorem correct___eo_prog_cnf_implies_pos (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_implies_pos x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_implies_pos x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_implies_neg1 -/
theorem correct___eo_prog_cnf_implies_neg1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_implies_neg1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_implies_neg1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_implies_neg2 -/
theorem correct___eo_prog_cnf_implies_neg2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_implies_neg2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_implies_neg2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_equiv_pos1 -/
theorem correct___eo_prog_cnf_equiv_pos1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_equiv_pos1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_equiv_pos1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_equiv_pos2 -/
theorem correct___eo_prog_cnf_equiv_pos2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_equiv_pos2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_equiv_pos2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_equiv_neg1 -/
theorem correct___eo_prog_cnf_equiv_neg1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_equiv_neg1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_equiv_neg1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_equiv_neg2 -/
theorem correct___eo_prog_cnf_equiv_neg2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_equiv_neg2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_equiv_neg2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_xor_pos1 -/
theorem correct___eo_prog_cnf_xor_pos1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_xor_pos1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_xor_pos1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_xor_pos2 -/
theorem correct___eo_prog_cnf_xor_pos2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_xor_pos2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_xor_pos2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_xor_neg1 -/
theorem correct___eo_prog_cnf_xor_neg1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_xor_neg1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_xor_neg1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_xor_neg2 -/
theorem correct___eo_prog_cnf_xor_neg2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_xor_neg2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_xor_neg2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_pos1 -/
theorem correct___eo_prog_cnf_ite_pos1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_ite_pos1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_ite_pos1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_pos2 -/
theorem correct___eo_prog_cnf_ite_pos2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_ite_pos2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_ite_pos2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_pos3 -/
theorem correct___eo_prog_cnf_ite_pos3 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_ite_pos3 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_ite_pos3 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_neg1 -/
theorem correct___eo_prog_cnf_ite_neg1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_ite_neg1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_ite_neg1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_neg2 -/
theorem correct___eo_prog_cnf_ite_neg2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_ite_neg2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_ite_neg2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cnf_ite_neg3 -/
theorem correct___eo_prog_cnf_ite_neg3 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_cnf_ite_neg3 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cnf_ite_neg3 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arrays_read_over_write -/
theorem correct___eo_prog_arrays_read_over_write (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_arrays_read_over_write x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arrays_read_over_write x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arrays_read_over_write_contra -/
theorem correct___eo_prog_arrays_read_over_write_contra (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_arrays_read_over_write_contra (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arrays_read_over_write_contra (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arrays_read_over_write_1 -/
theorem correct___eo_prog_arrays_read_over_write_1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arrays_read_over_write_1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arrays_read_over_write_1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arrays_ext -/
theorem correct___eo_prog_arrays_ext (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_arrays_ext (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arrays_ext (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_refl -/
theorem correct___eo_prog_refl (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_refl x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_symm -/
theorem correct___eo_prog_symm (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_symm (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_symm (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_trans -/
theorem correct___eo_prog_trans (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_trans (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_trans (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_cong -/
theorem correct___eo_prog_cong (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_cong x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_cong x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_nary_cong -/
theorem correct___eo_prog_nary_cong (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_nary_cong x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_nary_cong x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_pairwise_cong -/
theorem correct___eo_prog_pairwise_cong (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_pairwise_cong x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_pairwise_cong x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_true_intro -/
theorem correct___eo_prog_true_intro (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_true_intro (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_true_intro (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_true_elim -/
theorem correct___eo_prog_true_elim (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_true_elim (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_true_elim (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_false_intro -/
theorem correct___eo_prog_false_intro (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_false_intro (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_false_intro (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_false_elim -/
theorem correct___eo_prog_false_elim (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_false_elim (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_false_elim (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ho_cong -/
theorem correct___eo_prog_ho_cong (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_ho_cong (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ho_cong (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_elim -/
theorem correct___eo_prog_distinct_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_distinct_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_distinct_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_true -/
theorem correct___eo_prog_distinct_true (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_distinct_true x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_distinct_true x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_false -/
theorem correct___eo_prog_distinct_false (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_distinct_false x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_distinct_false x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_lambda_elim -/
theorem correct___eo_prog_lambda_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_lambda_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_lambda_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_sum_ub -/
theorem correct___eo_prog_arith_sum_ub (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_arith_sum_ub (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_sum_ub (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_pos -/
theorem correct___eo_prog_arith_mult_pos (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_mult_pos x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_mult_pos x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_neg -/
theorem correct___eo_prog_arith_mult_neg (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_mult_neg x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_mult_neg x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_trichotomy -/
theorem correct___eo_prog_arith_trichotomy (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_arith_trichotomy (Proof.pf x1) (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_trichotomy (Proof.pf x1) (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_int_tight_ub -/
theorem correct___eo_prog_int_tight_ub (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_int_tight_ub (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_int_tight_ub (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_int_tight_lb -/
theorem correct___eo_prog_int_tight_lb (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_int_tight_lb (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_int_tight_lb (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_tangent -/
theorem correct___eo_prog_arith_mult_tangent (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (Not ((__eo_prog_arith_mult_tangent x1 x2 x3 x4 x5) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_mult_tangent x1 x2 x3 x4 x5) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_sign -/
theorem correct___eo_prog_arith_mult_sign (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_mult_sign x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_mult_sign x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mult_abs_comparison -/
theorem correct___eo_prog_arith_mult_abs_comparison (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_arith_mult_abs_comparison (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_mult_abs_comparison (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_reduction -/
theorem correct___eo_prog_arith_reduction (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_reduction x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_reduction x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_poly_norm -/
theorem correct___eo_prog_arith_poly_norm (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_poly_norm x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_poly_norm x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_poly_norm_rel -/
theorem correct___eo_prog_arith_poly_norm_rel (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_arith_poly_norm_rel x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_poly_norm_rel x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_repeat_elim -/
theorem correct___eo_prog_bv_repeat_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_repeat_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_repeat_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_smulo_elim -/
theorem correct___eo_prog_bv_smulo_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_smulo_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_smulo_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_umulo_elim -/
theorem correct___eo_prog_bv_umulo_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_umulo_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_umulo_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_bitwise_slicing -/
theorem correct___eo_prog_bv_bitwise_slicing (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_bitwise_slicing x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_bitwise_slicing x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_bitblast_step -/
theorem correct___eo_prog_bv_bitblast_step (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_bitblast_step x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_bitblast_step x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_poly_norm -/
theorem correct___eo_prog_bv_poly_norm (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_poly_norm x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_poly_norm x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_poly_norm_eq -/
theorem correct___eo_prog_bv_poly_norm_eq (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_bv_poly_norm_eq x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_poly_norm_eq x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_string_length_pos -/
theorem correct___eo_prog_string_length_pos (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_string_length_pos x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_string_length_pos x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_string_length_non_empty -/
theorem correct___eo_prog_string_length_non_empty (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_string_length_non_empty (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_string_length_non_empty (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_eq -/
theorem correct___eo_prog_concat_eq (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_concat_eq x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_concat_eq x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_unify -/
theorem correct___eo_prog_concat_unify (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x2 true) ->
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_concat_unify x1 (Proof.pf x2) (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_concat_unify x1 (Proof.pf x2) (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_csplit -/
theorem correct___eo_prog_concat_csplit (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x2 true) ->
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_concat_csplit x1 (Proof.pf x2) (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_concat_csplit x1 (Proof.pf x2) (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_split -/
theorem correct___eo_prog_concat_split (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x2 true) ->
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_concat_split x1 (Proof.pf x2) (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_concat_split x1 (Proof.pf x2) (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_lprop -/
theorem correct___eo_prog_concat_lprop (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x2 true) ->
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_concat_lprop x1 (Proof.pf x2) (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_concat_lprop x1 (Proof.pf x2) (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_concat_cprop -/
theorem correct___eo_prog_concat_cprop (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x2 true) ->
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_concat_cprop x1 (Proof.pf x2) (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_concat_cprop x1 (Proof.pf x2) (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_string_decompose -/
theorem correct___eo_prog_string_decompose (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x2 true) ->
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_string_decompose x1 (Proof.pf x2) (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_string_decompose x1 (Proof.pf x2) (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_exists_string_length -/
theorem correct___eo_prog_exists_string_length (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_exists_string_length x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_exists_string_length x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_string_code_inj -/
theorem correct___eo_prog_string_code_inj (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_string_code_inj x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_string_code_inj x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_string_seq_unit_inj -/
theorem correct___eo_prog_string_seq_unit_inj (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_string_seq_unit_inj (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_string_seq_unit_inj (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter -/
theorem correct___eo_prog_re_inter (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_re_inter (Proof.pf x1) (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_inter (Proof.pf x1) (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat -/
theorem correct___eo_prog_re_concat (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_re_concat (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_concat (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_unfold_pos -/
theorem correct___eo_prog_re_unfold_pos (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_re_unfold_pos (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_unfold_pos (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_unfold_neg_concat_fixed -/
theorem correct___eo_prog_re_unfold_neg_concat_fixed (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_re_unfold_neg_concat_fixed x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_unfold_neg_concat_fixed x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_unfold_neg -/
theorem correct___eo_prog_re_unfold_neg (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_re_unfold_neg (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_unfold_neg (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_string_ext -/
theorem correct___eo_prog_string_ext (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_string_ext (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_string_ext (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_string_reduction -/
theorem correct___eo_prog_string_reduction (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_string_reduction x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_string_reduction x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_string_eager_reduction -/
theorem correct___eo_prog_string_eager_reduction (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_string_eager_reduction x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_string_eager_reduction x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_string_pred_entail -/
theorem correct___eo_prog_arith_string_pred_entail (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_string_pred_entail x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_string_pred_entail x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_string_pred_safe_approx -/
theorem correct___eo_prog_arith_string_pred_safe_approx (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_string_pred_safe_approx x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_string_pred_safe_approx x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_eval -/
theorem correct___eo_prog_str_in_re_eval (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_in_re_eval x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_eval x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_consume -/
theorem correct___eo_prog_str_in_re_consume (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_in_re_consume x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_consume x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_loop_elim -/
theorem correct___eo_prog_re_loop_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_loop_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_loop_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_eq_elim -/
theorem correct___eo_prog_re_eq_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_eq_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_eq_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter_inclusion -/
theorem correct___eo_prog_re_inter_inclusion (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_inter_inclusion x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_inter_inclusion x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_union_inclusion -/
theorem correct___eo_prog_re_union_inclusion (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_union_inclusion x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_union_inclusion x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_concat_star_char -/
theorem correct___eo_prog_str_in_re_concat_star_char (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_in_re_concat_star_char x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_concat_star_char x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_sigma -/
theorem correct___eo_prog_str_in_re_sigma (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_in_re_sigma x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_sigma x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_sigma_star -/
theorem correct___eo_prog_str_in_re_sigma_star (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_in_re_sigma_star x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_sigma_star x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_ctn_multiset_subset -/
theorem correct___eo_prog_str_ctn_multiset_subset (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_ctn_multiset_subset x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_ctn_multiset_subset x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_overlap_split_ctn -/
theorem correct___eo_prog_str_overlap_split_ctn (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_overlap_split_ctn x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_overlap_split_ctn x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_overlap_endpoints_ctn -/
theorem correct___eo_prog_str_overlap_endpoints_ctn (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_overlap_endpoints_ctn x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_overlap_endpoints_ctn x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_overlap_endpoints_indexof -/
theorem correct___eo_prog_str_overlap_endpoints_indexof (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_overlap_endpoints_indexof x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_overlap_endpoints_indexof x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_overlap_endpoints_replace -/
theorem correct___eo_prog_str_overlap_endpoints_replace (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_overlap_endpoints_replace x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_overlap_endpoints_replace x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_re_eval -/
theorem correct___eo_prog_str_indexof_re_eval (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_indexof_re_eval x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_re_eval x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_re_eval -/
theorem correct___eo_prog_str_replace_re_eval (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_replace_re_eval x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_re_eval x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_re_all_eval -/
theorem correct___eo_prog_str_replace_re_all_eval (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_replace_re_all_eval x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_re_all_eval x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_eval_op -/
theorem correct___eo_prog_seq_eval_op (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_seq_eval_op x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_seq_eval_op x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_singleton_inj -/
theorem correct___eo_prog_sets_singleton_inj (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_sets_singleton_inj (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_singleton_inj (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_ext -/
theorem correct___eo_prog_sets_ext (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_sets_ext (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_ext (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_eval_op -/
theorem correct___eo_prog_sets_eval_op (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_sets_eval_op x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_eval_op x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_insert_elim -/
theorem correct___eo_prog_sets_insert_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_sets_insert_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_insert_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ubv_to_int_elim -/
theorem correct___eo_prog_ubv_to_int_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_ubv_to_int_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ubv_to_int_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_int_to_bv_elim -/
theorem correct___eo_prog_int_to_bv_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_int_to_bv_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_int_to_bv_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_instantiate -/
theorem correct___eo_prog_instantiate (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_instantiate x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_instantiate x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_skolemize -/
theorem correct___eo_prog_skolemize (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  (Not ((__eo_prog_skolemize (Proof.pf x1)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_skolemize (Proof.pf x1)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_skolem_intro -/
theorem correct___eo_prog_skolem_intro (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_skolem_intro x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_skolem_intro x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_alpha_equiv -/
theorem correct___eo_prog_alpha_equiv (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_alpha_equiv x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_alpha_equiv x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_beta_reduce -/
theorem correct___eo_prog_beta_reduce (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_beta_reduce x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_beta_reduce x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_var_reordering -/
theorem correct___eo_prog_quant_var_reordering (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_quant_var_reordering x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_quant_var_reordering x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_exists_elim -/
theorem correct___eo_prog_exists_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_exists_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_exists_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_unused_vars -/
theorem correct___eo_prog_quant_unused_vars (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_quant_unused_vars x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_quant_unused_vars x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_merge_prenex -/
theorem correct___eo_prog_quant_merge_prenex (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_quant_merge_prenex x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_quant_merge_prenex x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_miniscope_and -/
theorem correct___eo_prog_quant_miniscope_and (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_quant_miniscope_and x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_quant_miniscope_and x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_miniscope_or -/
theorem correct___eo_prog_quant_miniscope_or (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_quant_miniscope_or x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_quant_miniscope_or x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_miniscope_ite -/
theorem correct___eo_prog_quant_miniscope_ite (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_quant_miniscope_ite x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_quant_miniscope_ite x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_var_elim_eq -/
theorem correct___eo_prog_quant_var_elim_eq (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_quant_var_elim_eq x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_quant_var_elim_eq x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_quant_dt_split -/
theorem correct___eo_prog_quant_dt_split (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_quant_dt_split x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_quant_dt_split x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_split -/
theorem correct___eo_prog_dt_split (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_split x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_split x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_inst -/
theorem correct___eo_prog_dt_inst (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_inst x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_inst x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_collapse_selector -/
theorem correct___eo_prog_dt_collapse_selector (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_collapse_selector x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_collapse_selector x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_collapse_tester -/
theorem correct___eo_prog_dt_collapse_tester (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_collapse_tester x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_collapse_tester x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_collapse_tester_singleton -/
theorem correct___eo_prog_dt_collapse_tester_singleton (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_collapse_tester_singleton x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_collapse_tester_singleton x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_cons_eq -/
theorem correct___eo_prog_dt_cons_eq (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_cons_eq x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_cons_eq x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_cons_eq_clash -/
theorem correct___eo_prog_dt_cons_eq_clash (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_cons_eq_clash x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_cons_eq_clash x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_cycle -/
theorem correct___eo_prog_dt_cycle (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_cycle x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_cycle x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_collapse_updater -/
theorem correct___eo_prog_dt_collapse_updater (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_collapse_updater x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_collapse_updater x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_dt_updater_elim -/
theorem correct___eo_prog_dt_updater_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_dt_updater_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_dt_updater_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_div_total_zero_real -/
theorem correct___eo_prog_arith_div_total_zero_real (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_div_total_zero_real x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_div_total_zero_real x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_div_total_zero_int -/
theorem correct___eo_prog_arith_div_total_zero_int (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_div_total_zero_int x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_div_total_zero_int x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_div_total -/
theorem correct___eo_prog_arith_int_div_total (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_arith_int_div_total x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_div_total x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_div_total_one -/
theorem correct___eo_prog_arith_int_div_total_one (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_int_div_total_one x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_div_total_one x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_div_total_zero -/
theorem correct___eo_prog_arith_int_div_total_zero (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_int_div_total_zero x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_div_total_zero x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_div_total_neg -/
theorem correct___eo_prog_arith_int_div_total_neg (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_arith_int_div_total_neg x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_div_total_neg x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_mod_total -/
theorem correct___eo_prog_arith_int_mod_total (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_arith_int_mod_total x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_mod_total x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_mod_total_one -/
theorem correct___eo_prog_arith_int_mod_total_one (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_int_mod_total_one x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_mod_total_one x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_mod_total_zero -/
theorem correct___eo_prog_arith_int_mod_total_zero (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_int_mod_total_zero x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_mod_total_zero x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_mod_total_neg -/
theorem correct___eo_prog_arith_int_mod_total_neg (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_arith_int_mod_total_neg x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_mod_total_neg x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_gt -/
theorem correct___eo_prog_arith_elim_gt (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_elim_gt x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_elim_gt x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_lt -/
theorem correct___eo_prog_arith_elim_lt (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_elim_lt x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_elim_lt x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_int_gt -/
theorem correct___eo_prog_arith_elim_int_gt (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_elim_int_gt x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_elim_int_gt x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_int_lt -/
theorem correct___eo_prog_arith_elim_int_lt (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_elim_int_lt x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_elim_int_lt x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_elim_leq -/
theorem correct___eo_prog_arith_elim_leq (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_elim_leq x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_elim_leq x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_leq_norm -/
theorem correct___eo_prog_arith_leq_norm (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_leq_norm x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_leq_norm x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_geq_tighten -/
theorem correct___eo_prog_arith_geq_tighten (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_geq_tighten x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_geq_tighten x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_geq_norm1_int -/
theorem correct___eo_prog_arith_geq_norm1_int (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_geq_norm1_int x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_geq_norm1_int x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_geq_norm1_real -/
theorem correct___eo_prog_arith_geq_norm1_real (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_geq_norm1_real x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_geq_norm1_real x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_eq_elim_real -/
theorem correct___eo_prog_arith_eq_elim_real (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_eq_elim_real x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_eq_elim_real x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_eq_elim_int -/
theorem correct___eo_prog_arith_eq_elim_int (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_eq_elim_int x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_eq_elim_int x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_to_int_elim_to_real -/
theorem correct___eo_prog_arith_to_int_elim_to_real (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_arith_to_int_elim_to_real x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_to_int_elim_to_real x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mod_over_mod_1 -/
theorem correct___eo_prog_arith_mod_over_mod_1 (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_arith_mod_over_mod_1 x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_mod_over_mod_1 x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mod_over_mod -/
theorem correct___eo_prog_arith_mod_over_mod (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_arith_mod_over_mod x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_mod_over_mod x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_mod_over_mod_mult -/
theorem correct___eo_prog_arith_mod_over_mod_mult (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_arith_mod_over_mod_mult x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_mod_over_mod_mult x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_eq_conflict -/
theorem correct___eo_prog_arith_int_eq_conflict (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_arith_int_eq_conflict x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_eq_conflict x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_int_geq_tighten -/
theorem correct___eo_prog_arith_int_geq_tighten (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_arith_int_geq_tighten x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_int_geq_tighten x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_divisible_elim -/
theorem correct___eo_prog_arith_divisible_elim (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_arith_divisible_elim x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_divisible_elim x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_abs_eq -/
theorem correct___eo_prog_arith_abs_eq (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_abs_eq x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_abs_eq x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_abs_int_gt -/
theorem correct___eo_prog_arith_abs_int_gt (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_abs_int_gt x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_abs_int_gt x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_abs_real_gt -/
theorem correct___eo_prog_arith_abs_real_gt (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_abs_real_gt x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_abs_real_gt x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_geq_ite_lift -/
theorem correct___eo_prog_arith_geq_ite_lift (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_arith_geq_ite_lift x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_geq_ite_lift x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_leq_ite_lift -/
theorem correct___eo_prog_arith_leq_ite_lift (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_arith_leq_ite_lift x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_leq_ite_lift x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_min_lt1 -/
theorem correct___eo_prog_arith_min_lt1 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_min_lt1 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_min_lt1 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_min_lt2 -/
theorem correct___eo_prog_arith_min_lt2 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_min_lt2 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_min_lt2 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_max_geq1 -/
theorem correct___eo_prog_arith_max_geq1 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_max_geq1 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_max_geq1 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_arith_max_geq2 -/
theorem correct___eo_prog_arith_max_geq2 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_arith_max_geq2 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_arith_max_geq2 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_array_read_over_write -/
theorem correct___eo_prog_array_read_over_write (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_array_read_over_write x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_array_read_over_write x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_array_read_over_write2 -/
theorem correct___eo_prog_array_read_over_write2 (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_array_read_over_write2 x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_array_read_over_write2 x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_array_store_overwrite -/
theorem correct___eo_prog_array_store_overwrite (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_array_store_overwrite x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_array_store_overwrite x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_array_store_self -/
theorem correct___eo_prog_array_store_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_array_store_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_array_store_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_array_read_over_write_split -/
theorem correct___eo_prog_array_read_over_write_split (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_array_read_over_write_split x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_array_read_over_write_split x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_array_store_swap -/
theorem correct___eo_prog_array_store_swap (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_array_store_swap x1 x2 x3 x4 x5 (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_array_store_swap x1 x2 x3 x4 x5 (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_double_not_elim -/
theorem correct___eo_prog_bool_double_not_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_double_not_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_double_not_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_true -/
theorem correct___eo_prog_bool_not_true (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_bool_not_true x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_not_true x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_false -/
theorem correct___eo_prog_bool_not_false (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_bool_not_false x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_not_false x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_eq_true -/
theorem correct___eo_prog_bool_eq_true (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_eq_true x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_eq_true x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_eq_false -/
theorem correct___eo_prog_bool_eq_false (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_eq_false x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_eq_false x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_eq_nrefl -/
theorem correct___eo_prog_bool_eq_nrefl (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_eq_nrefl x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_eq_nrefl x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_false1 -/
theorem correct___eo_prog_bool_impl_false1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_impl_false1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_impl_false1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_false2 -/
theorem correct___eo_prog_bool_impl_false2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_impl_false2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_impl_false2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_true1 -/
theorem correct___eo_prog_bool_impl_true1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_impl_true1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_impl_true1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_true2 -/
theorem correct___eo_prog_bool_impl_true2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_impl_true2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_impl_true2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_impl_elim -/
theorem correct___eo_prog_bool_impl_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bool_impl_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_impl_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_dual_impl_eq -/
theorem correct___eo_prog_bool_dual_impl_eq (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bool_dual_impl_eq x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_dual_impl_eq x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_and_conf -/
theorem correct___eo_prog_bool_and_conf (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bool_and_conf x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_and_conf x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_and_conf2 -/
theorem correct___eo_prog_bool_and_conf2 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bool_and_conf2 x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_and_conf2 x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_or_taut -/
theorem correct___eo_prog_bool_or_taut (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bool_or_taut x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_or_taut x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_or_taut2 -/
theorem correct___eo_prog_bool_or_taut2 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bool_or_taut2 x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_or_taut2 x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_or_de_morgan -/
theorem correct___eo_prog_bool_or_de_morgan (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_bool_or_de_morgan x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_or_de_morgan x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_implies_de_morgan -/
theorem correct___eo_prog_bool_implies_de_morgan (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bool_implies_de_morgan x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_implies_de_morgan x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_and_de_morgan -/
theorem correct___eo_prog_bool_and_de_morgan (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_bool_and_de_morgan x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_and_de_morgan x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_or_and_distrib -/
theorem correct___eo_prog_bool_or_and_distrib (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (Not ((__eo_prog_bool_or_and_distrib x1 x2 x3 x4 x5) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_or_and_distrib x1 x2 x3 x4 x5) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_implies_or_distrib -/
theorem correct___eo_prog_bool_implies_or_distrib (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bool_implies_or_distrib x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_implies_or_distrib x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_refl -/
theorem correct___eo_prog_bool_xor_refl (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_xor_refl x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_xor_refl x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_nrefl -/
theorem correct___eo_prog_bool_xor_nrefl (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_xor_nrefl x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_xor_nrefl x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_false -/
theorem correct___eo_prog_bool_xor_false (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_xor_false x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_xor_false x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_true -/
theorem correct___eo_prog_bool_xor_true (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bool_xor_true x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_xor_true x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_comm -/
theorem correct___eo_prog_bool_xor_comm (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bool_xor_comm x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_xor_comm x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_xor_elim -/
theorem correct___eo_prog_bool_xor_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bool_xor_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_xor_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_xor_elim -/
theorem correct___eo_prog_bool_not_xor_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bool_not_xor_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_not_xor_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_eq_elim1 -/
theorem correct___eo_prog_bool_not_eq_elim1 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bool_not_eq_elim1 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_not_eq_elim1 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_eq_elim2 -/
theorem correct___eo_prog_bool_not_eq_elim2 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bool_not_eq_elim2 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_not_eq_elim2 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_neg_branch -/
theorem correct___eo_prog_ite_neg_branch (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_ite_neg_branch x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_neg_branch x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_true -/
theorem correct___eo_prog_ite_then_true (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_then_true x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_then_true x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_false -/
theorem correct___eo_prog_ite_else_false (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_else_false x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_else_false x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_false -/
theorem correct___eo_prog_ite_then_false (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_then_false x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_then_false x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_true -/
theorem correct___eo_prog_ite_else_true (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_else_true x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_else_true x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_lookahead_self -/
theorem correct___eo_prog_ite_then_lookahead_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_then_lookahead_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_then_lookahead_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_lookahead_self -/
theorem correct___eo_prog_ite_else_lookahead_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_else_lookahead_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_else_lookahead_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_lookahead_not_self -/
theorem correct___eo_prog_ite_then_lookahead_not_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_then_lookahead_not_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_then_lookahead_not_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_lookahead_not_self -/
theorem correct___eo_prog_ite_else_lookahead_not_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_else_lookahead_not_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_else_lookahead_not_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_expand -/
theorem correct___eo_prog_ite_expand (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_ite_expand x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_expand x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bool_not_ite_elim -/
theorem correct___eo_prog_bool_not_ite_elim (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_bool_not_ite_elim x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bool_not_ite_elim x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_true_cond -/
theorem correct___eo_prog_ite_true_cond (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_true_cond x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_true_cond x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_false_cond -/
theorem correct___eo_prog_ite_false_cond (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_false_cond x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_false_cond x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_not_cond -/
theorem correct___eo_prog_ite_not_cond (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_ite_not_cond x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_not_cond x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_eq_branch -/
theorem correct___eo_prog_ite_eq_branch (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_ite_eq_branch x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_eq_branch x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_lookahead -/
theorem correct___eo_prog_ite_then_lookahead (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_ite_then_lookahead x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_then_lookahead x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_lookahead -/
theorem correct___eo_prog_ite_else_lookahead (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_ite_else_lookahead x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_else_lookahead x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_then_neg_lookahead -/
theorem correct___eo_prog_ite_then_neg_lookahead (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_ite_then_neg_lookahead x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_then_neg_lookahead x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_ite_else_neg_lookahead -/
theorem correct___eo_prog_ite_else_neg_lookahead (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_ite_else_neg_lookahead x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_ite_else_neg_lookahead x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_concat_extract_merge -/
theorem correct___eo_prog_bv_concat_extract_merge (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_concat_extract_merge x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_concat_extract_merge x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_extract -/
theorem correct___eo_prog_bv_extract_extract (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (Not ((__eo_prog_bv_extract_extract x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_extract x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_whole -/
theorem correct___eo_prog_bv_extract_whole (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_bv_extract_whole x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_whole x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_concat_1 -/
theorem correct___eo_prog_bv_extract_concat_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_extract_concat_1 x1 x2 x3 x4 x5 (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_concat_1 x1 x2 x3 x4 x5 (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_concat_2 -/
theorem correct___eo_prog_bv_extract_concat_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (eo_interprets M x11 true) ->
  (Not ((__eo_prog_bv_extract_concat_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_concat_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_concat_3 -/
theorem correct___eo_prog_bv_extract_concat_3 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (Not ((__eo_prog_bv_extract_concat_3 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_concat_3 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_concat_4 -/
theorem correct___eo_prog_bv_extract_concat_4 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_extract_concat_4 x1 x2 x3 x4 x5 (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_concat_4 x1 x2 x3 x4 x5 (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_extract_elim1 -/
theorem correct___eo_prog_bv_eq_extract_elim1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (eo_interprets M x11 true) ->
  (eo_interprets M x12 true) ->
  (Not ((__eo_prog_bv_eq_extract_elim1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10) (Proof.pf x11) (Proof.pf x12)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_eq_extract_elim1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10) (Proof.pf x11) (Proof.pf x12)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_extract_elim2 -/
theorem correct___eo_prog_bv_eq_extract_elim2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_eq_extract_elim2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_eq_extract_elim2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_extract_elim3 -/
theorem correct___eo_prog_bv_eq_extract_elim3 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_eq_extract_elim3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_eq_extract_elim3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_not -/
theorem correct___eo_prog_bv_extract_not (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_bv_extract_not x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_not x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_sign_extend_1 -/
theorem correct___eo_prog_bv_extract_sign_extend_1 (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_bv_extract_sign_extend_1 x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_sign_extend_1 x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_sign_extend_2 -/
theorem correct___eo_prog_bv_extract_sign_extend_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (Not ((__eo_prog_bv_extract_sign_extend_2 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_sign_extend_2 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_sign_extend_3 -/
theorem correct___eo_prog_bv_extract_sign_extend_3 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (Not ((__eo_prog_bv_extract_sign_extend_3 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_sign_extend_3 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_not_xor -/
theorem correct___eo_prog_bv_not_xor (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_bv_not_xor x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_not_xor x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_simplify_1 -/
theorem correct___eo_prog_bv_and_simplify_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_and_simplify_1 x1 x2 x3 x4 x5 (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_and_simplify_1 x1 x2 x3 x4 x5 (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_simplify_2 -/
theorem correct___eo_prog_bv_and_simplify_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_and_simplify_2 x1 x2 x3 x4 x5 (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_and_simplify_2 x1 x2 x3 x4 x5 (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_simplify_1 -/
theorem correct___eo_prog_bv_or_simplify_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_or_simplify_1 x1 x2 x3 x4 x5 (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_or_simplify_1 x1 x2 x3 x4 x5 (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_simplify_2 -/
theorem correct___eo_prog_bv_or_simplify_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_or_simplify_2 x1 x2 x3 x4 x5 (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_or_simplify_2 x1 x2 x3 x4 x5 (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_simplify_1 -/
theorem correct___eo_prog_bv_xor_simplify_1 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bv_xor_simplify_1 x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xor_simplify_1 x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_simplify_2 -/
theorem correct___eo_prog_bv_xor_simplify_2 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bv_xor_simplify_2 x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xor_simplify_2 x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_simplify_3 -/
theorem correct___eo_prog_bv_xor_simplify_3 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bv_xor_simplify_3 x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xor_simplify_3 x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_add_one -/
theorem correct___eo_prog_bv_ult_add_one (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_bv_ult_add_one x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ult_add_one x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_slt_mult_1 -/
theorem correct___eo_prog_bv_mult_slt_mult_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (Not ((__eo_prog_bv_mult_slt_mult_1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_mult_slt_mult_1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_slt_mult_2 -/
theorem correct___eo_prog_bv_mult_slt_mult_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (Not ((__eo_prog_bv_mult_slt_mult_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_mult_slt_mult_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_commutative_xor -/
theorem correct___eo_prog_bv_commutative_xor (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_commutative_xor x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_commutative_xor x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_commutative_comp -/
theorem correct___eo_prog_bv_commutative_comp (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_commutative_comp x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_commutative_comp x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_eliminate_0 -/
theorem correct___eo_prog_bv_zero_extend_eliminate_0 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_zero_extend_eliminate_0 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_zero_extend_eliminate_0 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_eliminate_0 -/
theorem correct___eo_prog_bv_sign_extend_eliminate_0 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_sign_extend_eliminate_0 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sign_extend_eliminate_0 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_not_neq -/
theorem correct___eo_prog_bv_not_neq (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_bv_not_neq x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_not_neq x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_ones -/
theorem correct___eo_prog_bv_ult_ones (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_bv_ult_ones x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ult_ones x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_concat_merge_const -/
theorem correct___eo_prog_bv_concat_merge_const (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_concat_merge_const x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_concat_merge_const x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_commutative_add -/
theorem correct___eo_prog_bv_commutative_add (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_commutative_add x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_commutative_add x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sub_eliminate -/
theorem correct___eo_prog_bv_sub_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_sub_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sub_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_width_one -/
theorem correct___eo_prog_bv_ite_width_one (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_ite_width_one x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_width_one x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_width_one_not -/
theorem correct___eo_prog_bv_ite_width_one_not (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_ite_width_one_not x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_width_one_not x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_xor_solve -/
theorem correct___eo_prog_bv_eq_xor_solve (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_bv_eq_xor_solve x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_eq_xor_solve x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_eq_not_solve -/
theorem correct___eo_prog_bv_eq_not_solve (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_eq_not_solve x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_eq_not_solve x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ugt_eliminate -/
theorem correct___eo_prog_bv_ugt_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_ugt_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ugt_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_uge_eliminate -/
theorem correct___eo_prog_bv_uge_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_uge_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_uge_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sgt_eliminate -/
theorem correct___eo_prog_bv_sgt_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_sgt_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sgt_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sge_eliminate -/
theorem correct___eo_prog_bv_sge_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_sge_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sge_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sle_eliminate -/
theorem correct___eo_prog_bv_sle_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_sle_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sle_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_redor_eliminate -/
theorem correct___eo_prog_bv_redor_eliminate (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_bv_redor_eliminate x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_redor_eliminate x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_redand_eliminate -/
theorem correct___eo_prog_bv_redand_eliminate (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_bv_redand_eliminate x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_redand_eliminate x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ule_eliminate -/
theorem correct___eo_prog_bv_ule_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_ule_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ule_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_comp_eliminate -/
theorem correct___eo_prog_bv_comp_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_comp_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_comp_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_rotate_left_eliminate_1 -/
theorem correct___eo_prog_bv_rotate_left_eliminate_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (Not ((__eo_prog_bv_rotate_left_eliminate_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_rotate_left_eliminate_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_rotate_left_eliminate_2 -/
theorem correct___eo_prog_bv_rotate_left_eliminate_2 (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_bv_rotate_left_eliminate_2 x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_rotate_left_eliminate_2 x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_rotate_right_eliminate_1 -/
theorem correct___eo_prog_bv_rotate_right_eliminate_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (Not ((__eo_prog_bv_rotate_right_eliminate_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_rotate_right_eliminate_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_rotate_right_eliminate_2 -/
theorem correct___eo_prog_bv_rotate_right_eliminate_2 (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_bv_rotate_right_eliminate_2 x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_rotate_right_eliminate_2 x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_nand_eliminate -/
theorem correct___eo_prog_bv_nand_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_nand_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_nand_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_nor_eliminate -/
theorem correct___eo_prog_bv_nor_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_nor_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_nor_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xnor_eliminate -/
theorem correct___eo_prog_bv_xnor_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_xnor_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xnor_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sdiv_eliminate -/
theorem correct___eo_prog_bv_sdiv_eliminate (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_bv_sdiv_eliminate x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sdiv_eliminate x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_eliminate -/
theorem correct___eo_prog_bv_zero_extend_eliminate (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_zero_extend_eliminate x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_zero_extend_eliminate x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_uaddo_eliminate -/
theorem correct___eo_prog_bv_uaddo_eliminate (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_bv_uaddo_eliminate x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_uaddo_eliminate x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_saddo_eliminate -/
theorem correct___eo_prog_bv_saddo_eliminate (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_bv_saddo_eliminate x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_saddo_eliminate x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sdivo_eliminate -/
theorem correct___eo_prog_bv_sdivo_eliminate (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_sdivo_eliminate x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sdivo_eliminate x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_smod_eliminate -/
theorem correct___eo_prog_bv_smod_eliminate (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_smod_eliminate x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_smod_eliminate x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_srem_eliminate -/
theorem correct___eo_prog_bv_srem_eliminate (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_bv_srem_eliminate x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_srem_eliminate x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_usubo_eliminate -/
theorem correct___eo_prog_bv_usubo_eliminate (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_bv_usubo_eliminate x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_usubo_eliminate x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ssubo_eliminate -/
theorem correct___eo_prog_bv_ssubo_eliminate (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_bv_ssubo_eliminate x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ssubo_eliminate x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_nego_eliminate -/
theorem correct___eo_prog_bv_nego_eliminate (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_bv_nego_eliminate x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_nego_eliminate x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_equal_children -/
theorem correct___eo_prog_bv_ite_equal_children (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_ite_equal_children x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_equal_children x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_const_children_1 -/
theorem correct___eo_prog_bv_ite_const_children_1 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_ite_const_children_1 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_const_children_1 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_const_children_2 -/
theorem correct___eo_prog_bv_ite_const_children_2 (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_ite_const_children_2 x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_const_children_2 x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_equal_cond_1 -/
theorem correct___eo_prog_bv_ite_equal_cond_1 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bv_ite_equal_cond_1 x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_equal_cond_1 x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_equal_cond_2 -/
theorem correct___eo_prog_bv_ite_equal_cond_2 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bv_ite_equal_cond_2 x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_equal_cond_2 x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_equal_cond_3 -/
theorem correct___eo_prog_bv_ite_equal_cond_3 (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (Not ((__eo_prog_bv_ite_equal_cond_3 x1 x2 x3 x4 x5) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_equal_cond_3 x1 x2 x3 x4 x5) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_merge_then_if -/
theorem correct___eo_prog_bv_ite_merge_then_if (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bv_ite_merge_then_if x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_merge_then_if x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_merge_else_if -/
theorem correct___eo_prog_bv_ite_merge_else_if (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bv_ite_merge_else_if x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_merge_else_if x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_merge_then_else -/
theorem correct___eo_prog_bv_ite_merge_then_else (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bv_ite_merge_then_else x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_merge_then_else x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ite_merge_else_else -/
theorem correct___eo_prog_bv_ite_merge_else_else (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_bv_ite_merge_else_else x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ite_merge_else_else x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_shl_by_const_0 -/
theorem correct___eo_prog_bv_shl_by_const_0 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_shl_by_const_0 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_shl_by_const_0 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_shl_by_const_1 -/
theorem correct___eo_prog_bv_shl_by_const_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_shl_by_const_1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_shl_by_const_1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_shl_by_const_2 -/
theorem correct___eo_prog_bv_shl_by_const_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_bv_shl_by_const_2 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_shl_by_const_2 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lshr_by_const_0 -/
theorem correct___eo_prog_bv_lshr_by_const_0 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_lshr_by_const_0 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_lshr_by_const_0 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lshr_by_const_1 -/
theorem correct___eo_prog_bv_lshr_by_const_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_lshr_by_const_1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_lshr_by_const_1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lshr_by_const_2 -/
theorem correct___eo_prog_bv_lshr_by_const_2 (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_bv_lshr_by_const_2 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_lshr_by_const_2 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ashr_by_const_0 -/
theorem correct___eo_prog_bv_ashr_by_const_0 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_ashr_by_const_0 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ashr_by_const_0 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ashr_by_const_1 -/
theorem correct___eo_prog_bv_ashr_by_const_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_ashr_by_const_1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ashr_by_const_1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ashr_by_const_2 -/
theorem correct___eo_prog_bv_ashr_by_const_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_ashr_by_const_2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ashr_by_const_2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_concat_pullup -/
theorem correct___eo_prog_bv_and_concat_pullup (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (eo_interprets M x11 true) ->
  (Not ((__eo_prog_bv_and_concat_pullup x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_and_concat_pullup x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_concat_pullup -/
theorem correct___eo_prog_bv_or_concat_pullup (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (eo_interprets M x11 true) ->
  (Not ((__eo_prog_bv_or_concat_pullup x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_or_concat_pullup x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_concat_pullup -/
theorem correct___eo_prog_bv_xor_concat_pullup (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (eo_interprets M x11 true) ->
  (Not ((__eo_prog_bv_xor_concat_pullup x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xor_concat_pullup x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_concat_pullup2 -/
theorem correct___eo_prog_bv_and_concat_pullup2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (eo_interprets M x11 true) ->
  (Not ((__eo_prog_bv_and_concat_pullup2 x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_and_concat_pullup2 x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_concat_pullup2 -/
theorem correct___eo_prog_bv_or_concat_pullup2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (eo_interprets M x11 true) ->
  (Not ((__eo_prog_bv_or_concat_pullup2 x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_or_concat_pullup2 x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_concat_pullup2 -/
theorem correct___eo_prog_bv_xor_concat_pullup2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Term) :
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (eo_interprets M x11 true) ->
  (Not ((__eo_prog_bv_xor_concat_pullup2 x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xor_concat_pullup2 x1 x2 x3 x4 x5 x6 x7 x8 (Proof.pf x9) (Proof.pf x10) (Proof.pf x11)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_and_concat_pullup3 -/
theorem correct___eo_prog_bv_and_concat_pullup3 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Term) :
  (eo_interprets M x11 true) ->
  (eo_interprets M x12 true) ->
  (eo_interprets M x13 true) ->
  (eo_interprets M x14 true) ->
  (eo_interprets M x15 true) ->
  (Not ((__eo_prog_bv_and_concat_pullup3 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Proof.pf x11) (Proof.pf x12) (Proof.pf x13) (Proof.pf x14) (Proof.pf x15)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_and_concat_pullup3 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Proof.pf x11) (Proof.pf x12) (Proof.pf x13) (Proof.pf x14) (Proof.pf x15)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_or_concat_pullup3 -/
theorem correct___eo_prog_bv_or_concat_pullup3 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Term) :
  (eo_interprets M x11 true) ->
  (eo_interprets M x12 true) ->
  (eo_interprets M x13 true) ->
  (eo_interprets M x14 true) ->
  (eo_interprets M x15 true) ->
  (Not ((__eo_prog_bv_or_concat_pullup3 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Proof.pf x11) (Proof.pf x12) (Proof.pf x13) (Proof.pf x14) (Proof.pf x15)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_or_concat_pullup3 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Proof.pf x11) (Proof.pf x12) (Proof.pf x13) (Proof.pf x14) (Proof.pf x15)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_concat_pullup3 -/
theorem correct___eo_prog_bv_xor_concat_pullup3 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : Term) :
  (eo_interprets M x11 true) ->
  (eo_interprets M x12 true) ->
  (eo_interprets M x13 true) ->
  (eo_interprets M x14 true) ->
  (eo_interprets M x15 true) ->
  (Not ((__eo_prog_bv_xor_concat_pullup3 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Proof.pf x11) (Proof.pf x12) (Proof.pf x13) (Proof.pf x14) (Proof.pf x15)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xor_concat_pullup3 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 (Proof.pf x11) (Proof.pf x12) (Proof.pf x13) (Proof.pf x14) (Proof.pf x15)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_duplicate -/
theorem correct___eo_prog_bv_xor_duplicate (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_bv_xor_duplicate x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xor_duplicate x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_ones -/
theorem correct___eo_prog_bv_xor_ones (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_bv_xor_ones x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xor_ones x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_xor_not -/
theorem correct___eo_prog_bv_xor_not (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_xor_not x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_xor_not x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_not_idemp -/
theorem correct___eo_prog_bv_not_idemp (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_not_idemp x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_not_idemp x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_zero_1 -/
theorem correct___eo_prog_bv_ult_zero_1 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_ult_zero_1 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ult_zero_1 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_zero_2 -/
theorem correct___eo_prog_bv_ult_zero_2 (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_ult_zero_2 x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ult_zero_2 x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_self -/
theorem correct___eo_prog_bv_ult_self (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_ult_self x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ult_self x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lt_self -/
theorem correct___eo_prog_bv_lt_self (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_lt_self x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_lt_self x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ule_self -/
theorem correct___eo_prog_bv_ule_self (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_ule_self x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ule_self x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ule_zero -/
theorem correct___eo_prog_bv_ule_zero (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_ule_zero x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ule_zero x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_ule -/
theorem correct___eo_prog_bv_zero_ule (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_zero_ule x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_zero_ule x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sle_self -/
theorem correct___eo_prog_bv_sle_self (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_bv_sle_self x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sle_self x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ule_max -/
theorem correct___eo_prog_bv_ule_max (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_bv_ule_max x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ule_max x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_not_ult -/
theorem correct___eo_prog_bv_not_ult (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_not_ult x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_not_ult x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_pow2_1 -/
theorem correct___eo_prog_bv_mult_pow2_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (Not ((__eo_prog_bv_mult_pow2_1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_mult_pow2_1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_pow2_2 -/
theorem correct___eo_prog_bv_mult_pow2_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (Not ((__eo_prog_bv_mult_pow2_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_mult_pow2_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_mult_pow2_2b -/
theorem correct___eo_prog_bv_mult_pow2_2b (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_mult_pow2_2b x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_mult_pow2_2b x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_extract_mult_leading_bit -/
theorem correct___eo_prog_bv_extract_mult_leading_bit (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : Term) :
  (eo_interprets M x10 true) ->
  (eo_interprets M x11 true) ->
  (eo_interprets M x12 true) ->
  (Not ((__eo_prog_bv_extract_mult_leading_bit x1 x2 x3 x4 x5 x6 x7 x8 x9 (Proof.pf x10) (Proof.pf x11) (Proof.pf x12)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_extract_mult_leading_bit x1 x2 x3 x4 x5 x6 x7 x8 x9 (Proof.pf x10) (Proof.pf x11) (Proof.pf x12)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_udiv_pow2_not_one -/
theorem correct___eo_prog_bv_udiv_pow2_not_one (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (Not ((__eo_prog_bv_udiv_pow2_not_one x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_udiv_pow2_not_one x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_udiv_zero -/
theorem correct___eo_prog_bv_udiv_zero (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_udiv_zero x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_udiv_zero x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_udiv_one -/
theorem correct___eo_prog_bv_udiv_one (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_udiv_one x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_udiv_one x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_urem_pow2_not_one -/
theorem correct___eo_prog_bv_urem_pow2_not_one (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (Not ((__eo_prog_bv_urem_pow2_not_one x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_urem_pow2_not_one x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_urem_one -/
theorem correct___eo_prog_bv_urem_one (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_urem_one x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_urem_one x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_urem_self -/
theorem correct___eo_prog_bv_urem_self (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_bv_urem_self x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_urem_self x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_shl_zero -/
theorem correct___eo_prog_bv_shl_zero (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_shl_zero x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_shl_zero x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_lshr_zero -/
theorem correct___eo_prog_bv_lshr_zero (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_lshr_zero x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_lshr_zero x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ashr_zero -/
theorem correct___eo_prog_bv_ashr_zero (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_bv_ashr_zero x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ashr_zero x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ugt_urem -/
theorem correct___eo_prog_bv_ugt_urem (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_bv_ugt_urem x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ugt_urem x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_ult_one -/
theorem correct___eo_prog_bv_ult_one (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_bv_ult_one x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_ult_one x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_merge_sign_extend_1 -/
theorem correct___eo_prog_bv_merge_sign_extend_1 (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_bv_merge_sign_extend_1 x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_merge_sign_extend_1 x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_merge_sign_extend_2 -/
theorem correct___eo_prog_bv_merge_sign_extend_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_bv_merge_sign_extend_2 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_merge_sign_extend_2 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_eq_const_1 -/
theorem correct___eo_prog_bv_sign_extend_eq_const_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (Not ((__eo_prog_bv_sign_extend_eq_const_1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sign_extend_eq_const_1 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_eq_const_2 -/
theorem correct___eo_prog_bv_sign_extend_eq_const_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (Not ((__eo_prog_bv_sign_extend_eq_const_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sign_extend_eq_const_2 x1 x2 x3 x4 x5 x6 x7 (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_eq_const_1 -/
theorem correct___eo_prog_bv_zero_extend_eq_const_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_zero_extend_eq_const_1 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_zero_extend_eq_const_1 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_eq_const_2 -/
theorem correct___eo_prog_bv_zero_extend_eq_const_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_zero_extend_eq_const_2 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_zero_extend_eq_const_2 x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_ult_const_1 -/
theorem correct___eo_prog_bv_zero_extend_ult_const_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_bv_zero_extend_ult_const_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_zero_extend_ult_const_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_zero_extend_ult_const_2 -/
theorem correct___eo_prog_bv_zero_extend_ult_const_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_bv_zero_extend_ult_const_2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_zero_extend_ult_const_2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_ult_const_1 -/
theorem correct___eo_prog_bv_sign_extend_ult_const_1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_bv_sign_extend_ult_const_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sign_extend_ult_const_1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_ult_const_2 -/
theorem correct___eo_prog_bv_sign_extend_ult_const_2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_sign_extend_ult_const_2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sign_extend_ult_const_2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_ult_const_3 -/
theorem correct___eo_prog_bv_sign_extend_ult_const_3 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_bv_sign_extend_ult_const_3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sign_extend_ult_const_3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_bv_sign_extend_ult_const_4 -/
theorem correct___eo_prog_bv_sign_extend_ult_const_4 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_bv_sign_extend_ult_const_4 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_bv_sign_extend_ult_const_4 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_eq_singleton_emp -/
theorem correct___eo_prog_sets_eq_singleton_emp (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_sets_eq_singleton_emp x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_eq_singleton_emp x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_member_singleton -/
theorem correct___eo_prog_sets_member_singleton (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_sets_member_singleton x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_member_singleton x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_member_emp -/
theorem correct___eo_prog_sets_member_emp (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_sets_member_emp x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_member_emp x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_subset_elim -/
theorem correct___eo_prog_sets_subset_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_sets_subset_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_subset_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_union_comm -/
theorem correct___eo_prog_sets_union_comm (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_sets_union_comm x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_union_comm x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_inter_comm -/
theorem correct___eo_prog_sets_inter_comm (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_sets_inter_comm x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_inter_comm x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_inter_emp1 -/
theorem correct___eo_prog_sets_inter_emp1 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_sets_inter_emp1 x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_inter_emp1 x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_inter_emp2 -/
theorem correct___eo_prog_sets_inter_emp2 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_sets_inter_emp2 x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_inter_emp2 x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_minus_emp1 -/
theorem correct___eo_prog_sets_minus_emp1 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_sets_minus_emp1 x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_minus_emp1 x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_minus_emp2 -/
theorem correct___eo_prog_sets_minus_emp2 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_sets_minus_emp2 x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_minus_emp2 x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_union_emp1 -/
theorem correct___eo_prog_sets_union_emp1 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_sets_union_emp1 x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_union_emp1 x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_union_emp2 -/
theorem correct___eo_prog_sets_union_emp2 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_sets_union_emp2 x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_union_emp2 x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_inter_member -/
theorem correct___eo_prog_sets_inter_member (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_sets_inter_member x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_inter_member x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_minus_member -/
theorem correct___eo_prog_sets_minus_member (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_sets_minus_member x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_minus_member x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_union_member -/
theorem correct___eo_prog_sets_union_member (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_sets_union_member x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_union_member x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_choose_singleton -/
theorem correct___eo_prog_sets_choose_singleton (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_sets_choose_singleton x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_choose_singleton x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_minus_self -/
theorem correct___eo_prog_sets_minus_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_sets_minus_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_minus_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_is_empty_elim -/
theorem correct___eo_prog_sets_is_empty_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_sets_is_empty_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_is_empty_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_sets_is_singleton_elim -/
theorem correct___eo_prog_sets_is_singleton_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_sets_is_singleton_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_sets_is_singleton_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_ctn_false -/
theorem correct___eo_prog_str_eq_ctn_false (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_eq_ctn_false x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_ctn_false x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_ctn_full_false1 -/
theorem correct___eo_prog_str_eq_ctn_full_false1 (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_eq_ctn_full_false1 x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_ctn_full_false1 x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_ctn_full_false2 -/
theorem correct___eo_prog_str_eq_ctn_full_false2 (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_eq_ctn_full_false2 x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_ctn_full_false2 x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_len_false -/
theorem correct___eo_prog_str_eq_len_false (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_eq_len_false x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_len_false x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_empty_str -/
theorem correct___eo_prog_str_substr_empty_str (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_substr_empty_str x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_empty_str x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_empty_range -/
theorem correct___eo_prog_str_substr_empty_range (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_substr_empty_range x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_empty_range x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_empty_start -/
theorem correct___eo_prog_str_substr_empty_start (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_substr_empty_start x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_empty_start x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_empty_start_neg -/
theorem correct___eo_prog_str_substr_empty_start_neg (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_substr_empty_start_neg x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_empty_start_neg x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_substr_start_geq_len -/
theorem correct___eo_prog_str_substr_substr_start_geq_len (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_str_substr_substr_start_geq_len x1 x2 x3 x4 x5 x6 (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_substr_start_geq_len x1 x2 x3 x4 x5 x6 (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_eq_empty -/
theorem correct___eo_prog_str_substr_eq_empty (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_str_substr_eq_empty x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_eq_empty x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_z_eq_empty_leq -/
theorem correct___eo_prog_str_substr_z_eq_empty_leq (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_substr_z_eq_empty_leq x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_z_eq_empty_leq x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_eq_empty_leq_len -/
theorem correct___eo_prog_str_substr_eq_empty_leq_len (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_str_substr_eq_empty_leq_len x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_eq_empty_leq_len x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_replace_inv -/
theorem correct___eo_prog_str_len_replace_inv (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_len_replace_inv x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_len_replace_inv x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_replace_all_inv -/
theorem correct___eo_prog_str_len_replace_all_inv (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_len_replace_all_inv x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_len_replace_all_inv x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_update_inv -/
theorem correct___eo_prog_str_len_update_inv (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_str_len_update_inv x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_len_update_inv x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_update_in_first_concat -/
theorem correct___eo_prog_str_update_in_first_concat (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 : Term) :
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (eo_interprets M x10 true) ->
  (Not ((__eo_prog_str_update_in_first_concat x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_update_in_first_concat x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9) (Proof.pf x10)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_substr_in_range -/
theorem correct___eo_prog_str_len_substr_in_range (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_len_substr_in_range x1 x2 x3 (Proof.pf x4) (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_len_substr_in_range x1 x2 x3 (Proof.pf x4) (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_clash -/
theorem correct___eo_prog_str_concat_clash (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_concat_clash x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_concat_clash x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_clash_rev -/
theorem correct___eo_prog_str_concat_clash_rev (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_concat_clash_rev x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_concat_clash_rev x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_clash2 -/
theorem correct___eo_prog_str_concat_clash2 (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_concat_clash2 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_concat_clash2 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_clash2_rev -/
theorem correct___eo_prog_str_concat_clash2_rev (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_concat_clash2_rev x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_concat_clash2_rev x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_unify -/
theorem correct___eo_prog_str_concat_unify (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (Not ((__eo_prog_str_concat_unify x1 x2 x3 x4 x5) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_concat_unify x1 x2 x3 x4 x5) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_unify_rev -/
theorem correct___eo_prog_str_concat_unify_rev (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (Not ((__eo_prog_str_concat_unify_rev x1 x2 x3 x4 x5) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_concat_unify_rev x1 x2 x3 x4 x5) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_unify_base -/
theorem correct___eo_prog_str_concat_unify_base (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_str_concat_unify_base x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_concat_unify_base x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_concat_unify_base_rev -/
theorem correct___eo_prog_str_concat_unify_base_rev (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_str_concat_unify_base_rev x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_concat_unify_base_rev x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_prefixof_elim -/
theorem correct___eo_prog_str_prefixof_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_prefixof_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_prefixof_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_suffixof_elim -/
theorem correct___eo_prog_str_suffixof_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_suffixof_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_suffixof_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_prefixof_eq -/
theorem correct___eo_prog_str_prefixof_eq (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_prefixof_eq x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_prefixof_eq x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_suffixof_eq -/
theorem correct___eo_prog_str_suffixof_eq (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_suffixof_eq x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_suffixof_eq x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_prefixof_one -/
theorem correct___eo_prog_str_prefixof_one (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_prefixof_one x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_prefixof_one x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_suffixof_one -/
theorem correct___eo_prog_str_suffixof_one (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_suffixof_one x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_suffixof_one x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_combine1 -/
theorem correct___eo_prog_str_substr_combine1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_str_substr_combine1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_combine1 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_combine2 -/
theorem correct___eo_prog_str_substr_combine2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_str_substr_combine2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_combine2 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_combine3 -/
theorem correct___eo_prog_str_substr_combine3 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_str_substr_combine3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_combine3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_combine4 -/
theorem correct___eo_prog_str_substr_combine4 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_str_substr_combine4 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_combine4 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_concat1 -/
theorem correct___eo_prog_str_substr_concat1 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_substr_concat1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_concat1 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_concat2 -/
theorem correct___eo_prog_str_substr_concat2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_substr_concat2 x1 x2 x3 x4 x5 (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_concat2 x1 x2 x3 x4 x5 (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_replace -/
theorem correct___eo_prog_str_substr_replace (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_substr_replace x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_replace x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_full -/
theorem correct___eo_prog_str_substr_full (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_substr_full x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_full x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_full_eq -/
theorem correct___eo_prog_str_substr_full_eq (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_substr_full_eq x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_full_eq x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_refl -/
theorem correct___eo_prog_str_contains_refl (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_contains_refl x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_refl x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_concat_find -/
theorem correct___eo_prog_str_contains_concat_find (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_contains_concat_find x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_concat_find x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_concat_find_contra -/
theorem correct___eo_prog_str_contains_concat_find_contra (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_contains_concat_find_contra x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_concat_find_contra x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_split_char -/
theorem correct___eo_prog_str_contains_split_char (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_contains_split_char x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_split_char x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_leq_len_eq -/
theorem correct___eo_prog_str_contains_leq_len_eq (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_contains_leq_len_eq x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_leq_len_eq x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_emp -/
theorem correct___eo_prog_str_contains_emp (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_contains_emp x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_emp x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_char -/
theorem correct___eo_prog_str_contains_char (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_contains_char x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_char x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_at_elim -/
theorem correct___eo_prog_str_at_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_at_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_at_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_self -/
theorem correct___eo_prog_str_replace_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_replace_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_id -/
theorem correct___eo_prog_str_replace_id (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_replace_id x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_id x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_prefix -/
theorem correct___eo_prog_str_replace_prefix (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_str_replace_prefix x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_prefix x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_no_contains -/
theorem correct___eo_prog_str_replace_no_contains (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_replace_no_contains x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_no_contains x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_find_base -/
theorem correct___eo_prog_str_replace_find_base (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_str_replace_find_base x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_find_base x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_find_first_concat -/
theorem correct___eo_prog_str_replace_find_first_concat (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 x9 : Term) :
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (eo_interprets M x9 true) ->
  (Not ((__eo_prog_str_replace_find_first_concat x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_find_first_concat x1 x2 x3 x4 x5 x6 (Proof.pf x7) (Proof.pf x8) (Proof.pf x9)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_empty -/
theorem correct___eo_prog_str_replace_empty (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_replace_empty x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_empty x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_one_pre -/
theorem correct___eo_prog_str_replace_one_pre (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_replace_one_pre x1 x2 x3 x4 x5 (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_one_pre x1 x2 x3 x4 x5 (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_find_pre -/
theorem correct___eo_prog_str_replace_find_pre (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_str_replace_find_pre x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_find_pre x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_all_no_contains -/
theorem correct___eo_prog_str_replace_all_no_contains (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_replace_all_no_contains x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_all_no_contains x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_all_empty -/
theorem correct___eo_prog_str_replace_all_empty (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_replace_all_empty x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_all_empty x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_all_id -/
theorem correct___eo_prog_str_replace_all_id (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_replace_all_id x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_all_id x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_all_self -/
theorem correct___eo_prog_str_replace_all_self (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_replace_all_self x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_all_self x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_re_none -/
theorem correct___eo_prog_str_replace_re_none (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_replace_re_none x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_re_none x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_re_all_none -/
theorem correct___eo_prog_str_replace_re_all_none (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_replace_re_all_none x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_re_all_none x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_concat_rec -/
theorem correct___eo_prog_str_len_concat_rec (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_str_len_concat_rec x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_len_concat_rec x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_eq_zero_concat_rec -/
theorem correct___eo_prog_str_len_eq_zero_concat_rec (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_str_len_eq_zero_concat_rec x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_len_eq_zero_concat_rec x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_len_eq_zero_base -/
theorem correct___eo_prog_str_len_eq_zero_base (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_len_eq_zero_base x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_len_eq_zero_base x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_self -/
theorem correct___eo_prog_str_indexof_self (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_str_indexof_self x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_self x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_no_contains -/
theorem correct___eo_prog_str_indexof_no_contains (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_indexof_no_contains x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_no_contains x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_oob -/
theorem correct___eo_prog_str_indexof_oob (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_indexof_oob x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_oob x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_oob2 -/
theorem correct___eo_prog_str_indexof_oob2 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_indexof_oob2 x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_oob2 x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_contains_pre -/
theorem correct___eo_prog_str_indexof_contains_pre (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_indexof_contains_pre x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_contains_pre x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_contains_concat_pre -/
theorem correct___eo_prog_str_indexof_contains_concat_pre (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_str_indexof_contains_concat_pre x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_contains_concat_pre x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_find_emp -/
theorem correct___eo_prog_str_indexof_find_emp (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_indexof_find_emp x1 x2 x3 (Proof.pf x4) (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_find_emp x1 x2 x3 (Proof.pf x4) (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_eq_irr -/
theorem correct___eo_prog_str_indexof_eq_irr (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_str_indexof_eq_irr x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_eq_irr x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_re_none -/
theorem correct___eo_prog_str_indexof_re_none (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_indexof_re_none x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_re_none x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_indexof_re_emp_re -/
theorem correct___eo_prog_str_indexof_re_emp_re (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_indexof_re_emp_re x1 x2 x3 (Proof.pf x4) (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_indexof_re_emp_re x1 x2 x3 (Proof.pf x4) (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_lower_concat -/
theorem correct___eo_prog_str_to_lower_concat (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_str_to_lower_concat x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_to_lower_concat x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_upper_concat -/
theorem correct___eo_prog_str_to_upper_concat (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_str_to_upper_concat x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_to_upper_concat x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_lower_upper -/
theorem correct___eo_prog_str_to_lower_upper (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_to_lower_upper x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_to_lower_upper x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_upper_lower -/
theorem correct___eo_prog_str_to_upper_lower (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_to_upper_lower x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_to_upper_lower x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_lower_len -/
theorem correct___eo_prog_str_to_lower_len (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_to_lower_len x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_to_lower_len x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_upper_len -/
theorem correct___eo_prog_str_to_upper_len (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_to_upper_len x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_to_upper_len x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_lower_from_int -/
theorem correct___eo_prog_str_to_lower_from_int (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_to_lower_from_int x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_to_lower_from_int x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_upper_from_int -/
theorem correct___eo_prog_str_to_upper_from_int (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_to_upper_from_int x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_to_upper_from_int x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_to_int_concat_neg_one -/
theorem correct___eo_prog_str_to_int_concat_neg_one (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_to_int_concat_neg_one x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_to_int_concat_neg_one x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_is_digit_elim -/
theorem correct___eo_prog_str_is_digit_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_is_digit_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_is_digit_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_empty -/
theorem correct___eo_prog_str_leq_empty (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_leq_empty x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_leq_empty x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_empty_eq -/
theorem correct___eo_prog_str_leq_empty_eq (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_leq_empty_eq x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_leq_empty_eq x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_concat_false -/
theorem correct___eo_prog_str_leq_concat_false (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_str_leq_concat_false x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_leq_concat_false x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_concat_true -/
theorem correct___eo_prog_str_leq_concat_true (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 x8 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (eo_interprets M x8 true) ->
  (Not ((__eo_prog_str_leq_concat_true x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_leq_concat_true x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7) (Proof.pf x8)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_concat_base_1 -/
theorem correct___eo_prog_str_leq_concat_base_1 (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_leq_concat_base_1 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_leq_concat_base_1 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_leq_concat_base_2 -/
theorem correct___eo_prog_str_leq_concat_base_2 (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_leq_concat_base_2 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_leq_concat_base_2 x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_lt_elim -/
theorem correct___eo_prog_str_lt_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_lt_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_lt_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_from_int_no_ctn_nondigit -/
theorem correct___eo_prog_str_from_int_no_ctn_nondigit (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x3 true) ->
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_from_int_no_ctn_nondigit x1 x2 (Proof.pf x3) (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_from_int_no_ctn_nondigit x1 x2 (Proof.pf x3) (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_ctn_contra -/
theorem correct___eo_prog_str_substr_ctn_contra (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_substr_ctn_contra x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_ctn_contra x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_ctn -/
theorem correct___eo_prog_str_substr_ctn (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_str_substr_ctn x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_ctn x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_dual_ctn -/
theorem correct___eo_prog_str_replace_dual_ctn (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_replace_dual_ctn x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_dual_ctn x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_dual_ctn_false -/
theorem correct___eo_prog_str_replace_dual_ctn_false (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_replace_dual_ctn_false x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_dual_ctn_false x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_self_ctn_simp -/
theorem correct___eo_prog_str_replace_self_ctn_simp (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_replace_self_ctn_simp x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_self_ctn_simp x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_replace_emp_ctn_src -/
theorem correct___eo_prog_str_replace_emp_ctn_src (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_replace_emp_ctn_src x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_replace_emp_ctn_src x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_char_start_eq_len -/
theorem correct___eo_prog_str_substr_char_start_eq_len (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_substr_char_start_eq_len x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_char_start_eq_len x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_repl_char -/
theorem correct___eo_prog_str_contains_repl_char (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_contains_repl_char x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_repl_char x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_repl_self_tgt_char -/
theorem correct___eo_prog_str_contains_repl_self_tgt_char (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_contains_repl_self_tgt_char x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_repl_self_tgt_char x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_repl_self -/
theorem correct___eo_prog_str_contains_repl_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_contains_repl_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_repl_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_contains_repl_tgt -/
theorem correct___eo_prog_str_contains_repl_tgt (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_str_contains_repl_tgt x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_contains_repl_tgt x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_len_id -/
theorem correct___eo_prog_str_repl_repl_len_id (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_str_repl_repl_len_id x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_len_id x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_tgt_no_ctn -/
theorem correct___eo_prog_str_repl_repl_src_tgt_no_ctn (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_repl_repl_src_tgt_no_ctn x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_src_tgt_no_ctn x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_tgt_self -/
theorem correct___eo_prog_str_repl_repl_tgt_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_repl_repl_tgt_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_tgt_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_tgt_no_ctn -/
theorem correct___eo_prog_str_repl_repl_tgt_no_ctn (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_repl_repl_tgt_no_ctn x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_tgt_no_ctn x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_self -/
theorem correct___eo_prog_str_repl_repl_src_self (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_str_repl_repl_src_self x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_src_self x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_inv_no_ctn1 -/
theorem correct___eo_prog_str_repl_repl_src_inv_no_ctn1 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_repl_repl_src_inv_no_ctn1 x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_src_inv_no_ctn1 x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_inv_no_ctn2 -/
theorem correct___eo_prog_str_repl_repl_src_inv_no_ctn2 (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_repl_repl_src_inv_no_ctn2 x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_src_inv_no_ctn2 x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_src_inv_no_ctn3 -/
theorem correct___eo_prog_str_repl_repl_src_inv_no_ctn3 (M : SmtModel) (x1 x2 x3 x4 x5 x6 x7 : Term) :
  (eo_interprets M x6 true) ->
  (eo_interprets M x7 true) ->
  (Not ((__eo_prog_str_repl_repl_src_inv_no_ctn3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_src_inv_no_ctn3 x1 x2 x3 x4 x5 (Proof.pf x6) (Proof.pf x7)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_dual_self -/
theorem correct___eo_prog_str_repl_repl_dual_self (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_repl_repl_dual_self x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_dual_self x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_dual_ite1 -/
theorem correct___eo_prog_str_repl_repl_dual_ite1 (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_repl_repl_dual_ite1 x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_dual_ite1 x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_dual_ite2 -/
theorem correct___eo_prog_str_repl_repl_dual_ite2 (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_repl_repl_dual_ite2 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_dual_ite2 x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_repl_repl_lookahead_id_simp -/
theorem correct___eo_prog_str_repl_repl_lookahead_id_simp (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_repl_repl_lookahead_id_simp x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_repl_repl_lookahead_id_simp x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_all_elim -/
theorem correct___eo_prog_re_all_elim (M : SmtModel) :
  (Not (__eo_prog_re_all_elim = Term.Stuck)) ->
  (eo_interprets M __eo_prog_re_all_elim true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_opt_elim -/
theorem correct___eo_prog_re_opt_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_opt_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_opt_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_diff_elim -/
theorem correct___eo_prog_re_diff_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_re_diff_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_diff_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_plus_elim -/
theorem correct___eo_prog_re_plus_elim (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_plus_elim x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_plus_elim x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_repeat_elim -/
theorem correct___eo_prog_re_repeat_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_re_repeat_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_repeat_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_star_swap -/
theorem correct___eo_prog_re_concat_star_swap (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_re_concat_star_swap x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_concat_star_swap x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_star_repeat -/
theorem correct___eo_prog_re_concat_star_repeat (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_re_concat_star_repeat x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_concat_star_repeat x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_star_subsume1 -/
theorem correct___eo_prog_re_concat_star_subsume1 (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_re_concat_star_subsume1 x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_concat_star_subsume1 x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_star_subsume2 -/
theorem correct___eo_prog_re_concat_star_subsume2 (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_re_concat_star_subsume2 x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_concat_star_subsume2 x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_concat_merge -/
theorem correct___eo_prog_re_concat_merge (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_re_concat_merge x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_concat_merge x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_union_all -/
theorem correct___eo_prog_re_union_all (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_re_union_all x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_union_all x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_union_const_elim -/
theorem correct___eo_prog_re_union_const_elim (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_re_union_const_elim x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_union_const_elim x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter_all -/
theorem correct___eo_prog_re_inter_all (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_re_inter_all x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_inter_all x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_none -/
theorem correct___eo_prog_re_star_none (M : SmtModel) :
  (Not (__eo_prog_re_star_none = Term.Stuck)) ->
  (eo_interprets M __eo_prog_re_star_none true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_emp -/
theorem correct___eo_prog_re_star_emp (M : SmtModel) :
  (Not (__eo_prog_re_star_emp = Term.Stuck)) ->
  (eo_interprets M __eo_prog_re_star_emp true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_star -/
theorem correct___eo_prog_re_star_star (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_star_star x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_star_star x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_range_refl -/
theorem correct___eo_prog_re_range_refl (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_re_range_refl x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_range_refl x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_range_emp -/
theorem correct___eo_prog_re_range_emp (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x3 true) ->
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_re_range_emp x1 x2 (Proof.pf x3) (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_range_emp x1 x2 (Proof.pf x3) (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_range_non_singleton_1 -/
theorem correct___eo_prog_re_range_non_singleton_1 (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_re_range_non_singleton_1 x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_range_non_singleton_1 x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_range_non_singleton_2 -/
theorem correct___eo_prog_re_range_non_singleton_2 (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_re_range_non_singleton_2 x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_range_non_singleton_2 x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_union_char -/
theorem correct___eo_prog_re_star_union_char (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_re_star_union_char x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_star_union_char x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_star_union_drop_emp -/
theorem correct___eo_prog_re_star_union_drop_emp (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_re_star_union_drop_emp x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_star_union_drop_emp x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_loop_neg -/
theorem correct___eo_prog_re_loop_neg (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_re_loop_neg x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_loop_neg x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter_cstring -/
theorem correct___eo_prog_re_inter_cstring (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_re_inter_cstring x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_inter_cstring x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_inter_cstring_neg -/
theorem correct___eo_prog_re_inter_cstring_neg (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_re_inter_cstring_neg x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_inter_cstring_neg x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_len_include -/
theorem correct___eo_prog_str_substr_len_include (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_substr_len_include x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_len_include x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_len_include_pre -/
theorem correct___eo_prog_str_substr_len_include_pre (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_substr_len_include_pre x1 x2 x3 x4 (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_len_include_pre x1 x2 x3 x4 (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_substr_len_norm -/
theorem correct___eo_prog_str_substr_len_norm (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_substr_len_norm x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_substr_len_norm x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_len_rev -/
theorem correct___eo_prog_seq_len_rev (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_seq_len_rev x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_seq_len_rev x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_rev_rev -/
theorem correct___eo_prog_seq_rev_rev (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_seq_rev_rev x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_seq_rev_rev x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_rev_concat -/
theorem correct___eo_prog_seq_rev_concat (M : SmtModel) (x1 x2 x3 : Term) :
  (Not ((__eo_prog_seq_rev_concat x1 x2 x3) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_seq_rev_concat x1 x2 x3) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_self_emp -/
theorem correct___eo_prog_str_eq_repl_self_emp (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_eq_repl_self_emp x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_repl_self_emp x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_no_change -/
theorem correct___eo_prog_str_eq_repl_no_change (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_eq_repl_no_change x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_repl_no_change x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_tgt_eq_len -/
theorem correct___eo_prog_str_eq_repl_tgt_eq_len (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_str_eq_repl_tgt_eq_len x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_repl_tgt_eq_len x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_len_one_emp_prefix -/
theorem correct___eo_prog_str_eq_repl_len_one_emp_prefix (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_eq_repl_len_one_emp_prefix x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_repl_len_one_emp_prefix x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_emp_tgt_nemp -/
theorem correct___eo_prog_str_eq_repl_emp_tgt_nemp (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_eq_repl_emp_tgt_nemp x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_repl_emp_tgt_nemp x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_nemp_src_emp -/
theorem correct___eo_prog_str_eq_repl_nemp_src_emp (M : SmtModel) (x1 x2 x3 x4 x5 x6 : Term) :
  (eo_interprets M x5 true) ->
  (eo_interprets M x6 true) ->
  (Not ((__eo_prog_str_eq_repl_nemp_src_emp x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_repl_nemp_src_emp x1 x2 x3 x4 (Proof.pf x5) (Proof.pf x6)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_eq_repl_self_src -/
theorem correct___eo_prog_str_eq_repl_self_src (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_eq_repl_self_src x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_eq_repl_self_src x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_len_unit -/
theorem correct___eo_prog_seq_len_unit (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_seq_len_unit x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_seq_len_unit x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_nth_unit -/
theorem correct___eo_prog_seq_nth_unit (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_seq_nth_unit x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_seq_nth_unit x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_seq_rev_unit -/
theorem correct___eo_prog_seq_rev_unit (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_seq_rev_unit x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_seq_rev_unit x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_empty -/
theorem correct___eo_prog_re_in_empty (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_in_empty x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_in_empty x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_sigma -/
theorem correct___eo_prog_re_in_sigma (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_in_sigma x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_in_sigma x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_sigma_star -/
theorem correct___eo_prog_re_in_sigma_star (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_re_in_sigma_star x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_in_sigma_star x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_cstring -/
theorem correct___eo_prog_re_in_cstring (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_re_in_cstring x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_in_cstring x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_re_in_comp -/
theorem correct___eo_prog_re_in_comp (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_re_in_comp x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_re_in_comp x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_union_elim -/
theorem correct___eo_prog_str_in_re_union_elim (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_str_in_re_union_elim x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_union_elim x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_inter_elim -/
theorem correct___eo_prog_str_in_re_inter_elim (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_str_in_re_inter_elim x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_inter_elim x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_range_elim -/
theorem correct___eo_prog_str_in_re_range_elim (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_str_in_re_range_elim x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_range_elim x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_contains -/
theorem correct___eo_prog_str_in_re_contains (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_str_in_re_contains x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_contains x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_from_int_nemp_dig_range -/
theorem correct___eo_prog_str_in_re_from_int_nemp_dig_range (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x2 true) ->
  (Not ((__eo_prog_str_in_re_from_int_nemp_dig_range x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_from_int_nemp_dig_range x1 (Proof.pf x2)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_str_in_re_from_int_dig_range -/
theorem correct___eo_prog_str_in_re_from_int_dig_range (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_str_in_re_from_int_dig_range x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_str_in_re_from_int_dig_range x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_refl -/
theorem correct___eo_prog_eq_refl (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_eq_refl x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_eq_refl x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_symm -/
theorem correct___eo_prog_eq_symm (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_eq_symm x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_eq_symm x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_cond_deq -/
theorem correct___eo_prog_eq_cond_deq (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_eq_cond_deq x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_eq_cond_deq x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_eq_ite_lift -/
theorem correct___eo_prog_eq_ite_lift (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (Not ((__eo_prog_eq_ite_lift x1 x2 x3 x4) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_eq_ite_lift x1 x2 x3 x4) true) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_binary_elim -/
theorem correct___eo_prog_distinct_binary_elim (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_distinct_binary_elim x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_distinct_binary_elim x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_bv2nat_int2bv -/
theorem correct___eo_prog_uf_bv2nat_int2bv (M : SmtModel) (x1 x2 x3 : Term) :
  (eo_interprets M x3 true) ->
  (Not ((__eo_prog_uf_bv2nat_int2bv x1 x2 (Proof.pf x3)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_uf_bv2nat_int2bv x1 x2 (Proof.pf x3)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_bv2nat_int2bv_extend -/
theorem correct___eo_prog_uf_bv2nat_int2bv_extend (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_uf_bv2nat_int2bv_extend x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_uf_bv2nat_int2bv_extend x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_bv2nat_int2bv_extract -/
theorem correct___eo_prog_uf_bv2nat_int2bv_extract (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_uf_bv2nat_int2bv_extract x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_uf_bv2nat_int2bv_extract x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_int2bv_bv2nat -/
theorem correct___eo_prog_uf_int2bv_bv2nat (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_uf_int2bv_bv2nat x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_uf_int2bv_bv2nat x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_bv2nat_geq_elim -/
theorem correct___eo_prog_uf_bv2nat_geq_elim (M : SmtModel) (x1 x2 x3 x4 : Term) :
  (eo_interprets M x4 true) ->
  (Not ((__eo_prog_uf_bv2nat_geq_elim x1 x2 x3 (Proof.pf x4)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_uf_bv2nat_geq_elim x1 x2 x3 (Proof.pf x4)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_int2bv_bvult_equiv -/
theorem correct___eo_prog_uf_int2bv_bvult_equiv (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_uf_int2bv_bvult_equiv x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_uf_int2bv_bvult_equiv x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_int2bv_bvule_equiv -/
theorem correct___eo_prog_uf_int2bv_bvule_equiv (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_uf_int2bv_bvule_equiv x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_uf_int2bv_bvule_equiv x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_uf_sbv_to_int_elim -/
theorem correct___eo_prog_uf_sbv_to_int_elim (M : SmtModel) (x1 x2 x3 x4 x5 : Term) :
  (eo_interprets M x4 true) ->
  (eo_interprets M x5 true) ->
  (Not ((__eo_prog_uf_sbv_to_int_elim x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_uf_sbv_to_int_elim x1 x2 x3 (Proof.pf x4) (Proof.pf x5)) true) :=
by
  sorry

/- correctness theorem for __eo_prog_evaluate -/
theorem correct___eo_prog_evaluate (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_evaluate x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_evaluate x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_values -/
theorem correct___eo_prog_distinct_values (M : SmtModel) (x1 x2 : Term) :
  (Not ((__eo_prog_distinct_values x1 x2) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_distinct_values x1 x2) true) :=
by
  sorry

/- correctness theorem for __eo_prog_aci_norm -/
theorem correct___eo_prog_aci_norm (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_aci_norm x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_aci_norm x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_absorb -/
theorem correct___eo_prog_absorb (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_absorb x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_absorb x1) true) :=
by
  sorry

/- correctness theorem for __eo_prog_distinct_card_conflict -/
theorem correct___eo_prog_distinct_card_conflict (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_distinct_card_conflict x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_distinct_card_conflict x1) true) :=
by
  sorry




/- Helper definitions -/


