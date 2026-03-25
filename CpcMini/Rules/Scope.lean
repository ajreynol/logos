import CpcMini.Rules.Common

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem typed___eo_prog_scope_impl (M : SmtModel) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  __eo_prog_scope x1 (Proof.pf x2) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) :=
by
  sorry

namespace RuleProofs

theorem correct___eo_prog_scope
    (M : SmtModel) (hM : smt_model_well_typed M) (x1 x2 : Term) :
  (eo_interprets M x1 true -> eo_interprets M x2 true) ->
  eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) ->
  eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true := by
  intro hImp hTy
  by_cases hStuck : x1 = Term.Stuck
  · subst hStuck
    simp [eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof] at hTy
  · have hTy1 : __smtx_typeof (__eo_to_smt x1) = SmtType.Bool := by
      by_cases hx1 : __smtx_typeof (__eo_to_smt x1) = SmtType.Bool
      · exact hx1
      · simp [eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof,
          smt_lit_ite, smt_lit_Teq, hx1] at hTy
    have hTy2 : __smtx_typeof (__eo_to_smt x2) = SmtType.Bool := by
      by_cases hx2 : __smtx_typeof (__eo_to_smt x2) = SmtType.Bool
      · exact hx2
      · simp [eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof,
          smt_lit_ite, smt_lit_Teq, hTy1, hx2] at hTy
    have hTy1' : eo_has_bool_type x1 := hTy1
    have hTy2' : eo_has_bool_type x2 := hTy2
    rcases eo_eval_is_boolean_of_has_bool_type M hM x1 hTy1' with ⟨b1, hEval1⟩
    rw [eo_interprets_iff_smt_interprets]
    refine smt_interprets.intro_true M (__eo_to_smt (__eo_prog_scope x1 (Proof.pf x2))) ?_ ?_
    · simpa [eo_has_bool_type, __eo_prog_scope, hStuck, __eo_to_smt] using hTy
    · cases b1 with
      | false =>
          rcases eo_eval_is_boolean_of_has_bool_type M hM x2 hTy2' with ⟨b2, hEval2⟩
          cases b2 <;>
            simp [__eo_prog_scope, __eo_to_smt, __smtx_model_eval, hEval1, hEval2,
              __smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
              SmtEval.smt_lit_not, SmtEval.smt_lit_or]
      | true =>
          have hX1True : eo_interprets M x1 true :=
            eo_interprets_of_bool_eval M x1 true hTy1' hEval1
          have hX2True : eo_interprets M x2 true := hImp hX1True
          rw [eo_interprets_iff_smt_interprets] at hX2True
          cases hX2True with
          | intro_true _ hEval2 =>
              simp [__eo_prog_scope, __eo_to_smt, __smtx_model_eval, hEval1, hEval2,
                __smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
                SmtEval.smt_lit_not, SmtEval.smt_lit_or]

theorem not_eo_interprets_prog_scope_num_true (M : SmtModel) :
  ¬ eo_interprets M (__eo_prog_scope (Term.Numeral 0) (Proof.pf (Term.Boolean true))) true := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy hEval =>
      simp [__eo_prog_scope, __eo_to_smt, __smtx_typeof, smt_lit_ite, smt_lit_Teq] at hTy

end RuleProofs

theorem correct___eo_prog_scope_impl
    (M : SmtModel) (hM : smt_model_well_typed M) (x1 x2 : Term) :
  ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
  RuleProofs.eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) ->
  (eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true) :=
by
  exact RuleProofs.correct___eo_prog_scope M hM x1 x2
