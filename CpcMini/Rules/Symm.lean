import CpcMini.Rules.Common

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem typed___eo_prog_symm_impl (M : SmtModel) (x1 : Term) :
  (eo_interprets M x1 true) ->
  __eo_prog_symm (Proof.pf x1) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) :=
by
  intro hXTrue hProg
  cases x1 with
  | Apply f a =>
      cases f with
      | Apply g b =>
          cases g with
          | eq =>
              rcases RuleProofs.eo_eq_operands_same_smt_type M b a hXTrue with
                ⟨hTy, hNonNone⟩
              have hNonNone' : __smtx_typeof (__eo_to_smt a) ≠ SmtType.None := by
                simpa [hTy] using hNonNone
              have hEqTy :
                  __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a))
                    (__smtx_typeof (__eo_to_smt b)) = SmtType.Bool := by
                exact (RuleProofs.smtx_typeof_eq_bool_iff
                  (__smtx_typeof (__eo_to_smt a))
                  (__smtx_typeof (__eo_to_smt b))).mpr ⟨hTy.symm, hNonNone'⟩
              exact by
                simp [RuleProofs.eo_has_bool_type, __eo_prog_symm, __mk_symm, __eo_to_smt,
                  __smtx_typeof, hEqTy]
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
      | not =>
          cases a with
          | Apply f2 a2 =>
              cases f2 with
              | Apply g2 b2 =>
                  cases g2 with
                  | eq =>
                      have hEqFalse :
                          eo_interprets M (Term.Apply (Term.Apply Term.eq b2) a2) false :=
                        RuleProofs.eo_interprets_not_true_implies_false M _ hXTrue
                      rcases RuleProofs.eo_eq_operands_same_smt_type_of_false M b2 a2 hEqFalse with
                        ⟨hTy, hNonNone⟩
                      have hNonNone' : __smtx_typeof (__eo_to_smt a2) ≠ SmtType.None := by
                        simpa [hTy] using hNonNone
                      have hEqTy :
                          __smtx_typeof_eq (__smtx_typeof (__eo_to_smt a2))
                            (__smtx_typeof (__eo_to_smt b2)) = SmtType.Bool := by
                        exact (RuleProofs.smtx_typeof_eq_bool_iff
                          (__smtx_typeof (__eo_to_smt a2))
                          (__smtx_typeof (__eo_to_smt b2))).mpr ⟨hTy.symm, hNonNone'⟩
                      exact by
                        simp [RuleProofs.eo_has_bool_type, __eo_prog_symm, __mk_symm, __eo_to_smt,
                          __smtx_typeof, hEqTy, smt_lit_ite, smt_lit_Teq]
                  | _ =>
                      exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
              | _ =>
                  exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
          | _ =>
              exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
      | _ =>
          exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))
  | _ =>
      exact False.elim (hProg (by simp [__eo_prog_symm, __mk_symm]))

theorem correct___eo_prog_symm_impl
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  (eo_interprets M x1 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_symm (Proof.pf x1)) ->
  (eo_interprets M (__eo_prog_symm (Proof.pf x1)) true) :=
by
  sorry
