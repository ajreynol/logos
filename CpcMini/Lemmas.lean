import CpcMini.Rules

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- The theorem statements -/

theorem typed___eo_prog_scope (M : SmtModel) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) :=
by
  exact typed___eo_prog_scope_impl M x1 x2

theorem correct___eo_prog_scope
    (M : SmtModel) (hM : smt_model_well_typed M) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) ->
  (eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true) :=
by
  exact correct___eo_prog_scope_impl M hM x1 x2

theorem typed___eo_prog_contra (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) :=
by
  exact typed___eo_prog_contra_impl M x1 x2

theorem correct___eo_prog_contra
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) ->
  (eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true) :=
by
  exact correct___eo_prog_contra_impl M _hM x1 x2

theorem typed___eo_prog_refl (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_prog_refl x1 ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) :=
by
  exact typed___eo_prog_refl_impl x1

theorem correct___eo_prog_refl
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  exact correct___eo_prog_refl_impl M _hM x1

theorem correct___eo_prog_refl_of_smt_translation
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  exact correct___eo_prog_refl_of_smt_translation_impl M _hM x1

theorem typed___eo_prog_symm (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) :=
by
  exact typed___eo_prog_symm_impl M x1

theorem correct___eo_prog_symm
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  (eo_interprets M x1 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) ->
  (eo_interprets M (__eo_prog_symm (Proof.pf x1)) true) :=
by
  exact correct___eo_prog_symm_impl M _hM x1

theorem eo_requires_not_stuck (x1 x2 x3 : Term) :
  __eo_requires x1 x2 x3 ≠ Term.Stuck ->
  x1 = x2 ∧ x1 ≠ Term.Stuck ∧ x3 ≠ Term.Stuck := by
  exact eo_requires_not_stuck_impl x1 x2 x3

theorem eo_requires_eq_of_eq_not_stuck (x1 x2 x3 : Term) :
  x1 = x2 ->
  x1 ≠ Term.Stuck ->
  __eo_requires x1 x2 x3 = x3 := by
  exact eo_requires_eq_of_eq_not_stuck_impl x1 x2 x3

theorem mk_trans_step_eq (t1 t2 t3 t4 tail : Term) :
  t1 ≠ Term.Stuck ->
  t2 ≠ Term.Stuck ->
  __mk_trans t1 t2 (Term.Apply (Term.Apply Term.and (Term.Apply (Term.Apply Term.eq t3) t4)) tail) =
    __eo_requires t2 t3 (__mk_trans t1 t4 tail) := by
  exact mk_trans_step_eq_impl t1 t2 t3 t4 tail

theorem mk_trans_base_eq (t1 t2 : Term) :
  t1 ≠ Term.Stuck ->
  t2 ≠ Term.Stuck ->
  __mk_trans t1 t2 (Term.Boolean true) = Term.Apply (Term.Apply Term.eq t1) t2 := by
  exact mk_trans_base_eq_impl t1 t2

theorem term_ne_stuck_of_smt_type_not_none (t : Term) :
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
  t ≠ Term.Stuck := by
  exact term_ne_stuck_of_smt_type_not_none_impl t

theorem typed___eo_prog_trans (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  __eo_prog_trans (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_trans (Proof.pf x1)) :=
by
  exact typed___eo_prog_trans_impl M x1

theorem correct___eo_prog_trans
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  (eo_interprets M x1 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_trans (Proof.pf x1)) ->
  (eo_interprets M (__eo_prog_trans (Proof.pf x1)) true) :=
by
  exact correct___eo_prog_trans_impl M _hM x1
