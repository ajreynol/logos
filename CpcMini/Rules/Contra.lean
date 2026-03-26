import CpcMini.Rules.Common

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem typed___eo_prog_contra_impl (M : SmtModel) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) :=
by
  intro hX1True _hX2True hProg
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_interprets_true M x1 hX1True
  cases x2 with
  | Apply f a =>
      cases f with
      | not =>
          by_cases hEq : x1 = a
          · subst hEq
            have hEqTerm : __eo_eq x1 x1 = Term.Boolean true := by
              by_cases hStuck : x1 = Term.Stuck
              · exact False.elim (hX1NotStuck hStuck)
              · simp [__eo_eq, hStuck, eo_lit_teq]
            have hContraFalse :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply Term.not x1)) =
                  Term.Boolean false := by
              rw [__eo_prog_contra, hEqTerm]
              simp [__eo_requires, eo_lit_teq, eo_lit_ite, eo_lit_not, SmtEval.smt_lit_not]
            simpa [RuleProofs.eo_has_bool_type, hContraFalse, __eo_to_smt, __smtx_typeof]
          · have hEqNe : __eo_eq x1 a ≠ Term.Boolean true := by
              intro hEqTerm
              by_cases hXStuck : x1 = Term.Stuck
              · subst hXStuck
                simp [__eo_eq] at hEqTerm
              · by_cases hAStuck : a = Term.Stuck
                · subst hAStuck
                  simp [__eo_eq] at hEqTerm
                · simp [__eo_eq, hXStuck, hAStuck, eo_lit_teq] at hEqTerm
                  exact hEq hEqTerm.symm
            have hContraStuck :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply Term.not a)) = Term.Stuck := by
              rw [__eo_prog_contra]
              simp [__eo_requires, eo_lit_teq, eo_lit_ite, hEqNe]
            exact False.elim (hProg hContraStuck)
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_contra]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_contra]))

theorem translatable___eo_prog_contra_impl (x1 x2 : Term) :
  RuleProofs.eo_has_bool_type x1 ->
  RuleProofs.eo_has_bool_type x2 ->
  __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_smt_translation (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) :=
by
  intro hX1Bool _hX2Bool hProg
  have hX1NotStuck : x1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type x1 hX1Bool
  cases x2 with
  | Apply f a =>
      cases f with
      | not =>
          by_cases hEq : x1 = a
          · subst hEq
            have hEqTerm : __eo_eq x1 x1 = Term.Boolean true := by
              simp [__eo_eq, hX1NotStuck, eo_lit_teq]
            have hContraFalse :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply Term.not x1)) =
                  Term.Boolean false := by
              rw [__eo_prog_contra, hEqTerm]
              simp [__eo_requires, eo_lit_teq, eo_lit_ite, eo_lit_not, SmtEval.smt_lit_not]
            simpa [RuleProofs.eo_has_smt_translation, hContraFalse, __eo_to_smt, __smtx_typeof]
          · have hEqNe : __eo_eq x1 a ≠ Term.Boolean true := by
              intro hEqTerm
              by_cases hAStuck : a = Term.Stuck
              · subst hAStuck
                simp [__eo_eq] at hEqTerm
              · simp [__eo_eq, hX1NotStuck, hAStuck, eo_lit_teq] at hEqTerm
                exact hEq hEqTerm.symm
            have hContraStuck :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply Term.not a)) = Term.Stuck := by
              rw [__eo_prog_contra]
              simp [__eo_requires, eo_lit_teq, eo_lit_ite, hEqNe]
            exact False.elim (hProg hContraStuck)
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_contra]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_contra]))

namespace RuleProofs

theorem correct___eo_prog_contra (M : SmtModel) (x1 x2 : Term) :
  eo_interprets M x1 true ->
  eo_interprets M x2 true ->
  eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) ->
  eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true := by
  intro hX1True hX2True hTy
  have hProgNotStuck : __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck := by
    intro hStuck
    simp [eo_has_bool_type, hStuck, __eo_to_smt, __smtx_typeof] at hTy
  cases x2 with
  | Apply f a =>
      cases f with
      | not =>
          by_cases hEq : x1 = a
          · subst hEq
            have hX1False : eo_interprets M x1 false :=
              eo_interprets_not_true_implies_false M x1 hX2True
            exact False.elim ((eo_interprets_true_not_false M x1 hX1True) hX1False)
          · exfalso
            have hEq' : a ≠ x1 := by
              simpa [eq_comm] using hEq
            have hx1NotStuck : x1 ≠ Term.Stuck :=
              term_ne_stuck_of_interprets_true M x1 hX1True
            have hAFalse : eo_interprets M a false :=
              eo_interprets_not_true_implies_false M a hX2True
            have hANotStuck : a ≠ Term.Stuck :=
              term_ne_stuck_of_interprets_false M a hAFalse
            have hContraStuck :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply Term.not a)) = Term.Stuck := by
              simp [__eo_prog_contra, __eo_requires, __eo_eq, eo_lit_teq, hEq', eo_lit_ite]
            exact hProgNotStuck hContraStuck
      | _ =>
          exact False.elim (hProgNotStuck (by simp [__eo_prog_contra]))
  | _ =>
      exact False.elim (hProgNotStuck (by simp [__eo_prog_contra]))

end RuleProofs

theorem correct___eo_prog_contra_impl
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 x2 : Term) :
  (eo_interprets M x1 true) ->
  (eo_interprets M x2 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) ->
  (eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true) :=
by
  exact RuleProofs.correct___eo_prog_contra M x1 x2
