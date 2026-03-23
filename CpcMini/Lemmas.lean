import CpcMini.SmtModel
import CpcMini.Logos
import CpcMini.Spec
import CpcMini.Rules

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000


/- The theorem statements -/

/- correctness theorem for __eo_prog_scope -/
/- `RuleProofs.not_eo_interprets_prog_scope_num_true` shows this statement is
   false as written: non-stuckness alone does not force the antecedent of the
   implication to be Boolean. -/
theorem correct___eo_prog_scope (M : SmtModel) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  (Not ((__eo_prog_scope x1 (Proof.pf x2)) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true) :=
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

/- correctness theorem for __eo_prog_refl -/
/- `RuleProofs.not_eo_interprets_prog_refl_or_true` shows this statement is
   false as written: non-stuckness alone does not force the argument to have a
   semantic type on which equality is Boolean. -/
theorem correct___eo_prog_refl (M : SmtModel) (x1 : Term) :
  (Not ((__eo_prog_refl x1) = Term.Stuck)) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  sorry

/- A typed version of `refl` that is actually provable.
   This is the candidate replacement template if we decide to strengthen the
   rule assumptions in the checker proof. -/
theorem correct___eo_prog_refl_of_smt_translation (M : SmtModel) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  exact RuleProofs.correct___eo_prog_refl_of_smt_translation M x1

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




/- Helper definitions -/



