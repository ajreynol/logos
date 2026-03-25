import CpcMini.Rules.Common

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem typed___eo_prog_refl_impl (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  __eo_prog_refl x1 ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) :=
by
  intro hTrans _hProg
  by_cases hStuck : x1 = Term.Stuck
  · exfalso
    apply hTrans
    simp [RuleProofs.eo_has_smt_translation, hStuck, __eo_to_smt, __smtx_typeof]
  · have hRefl :
        __eo_prog_refl x1 = Term.Apply (Term.Apply Term.eq x1) x1 := by
      simp [__eo_prog_refl, hStuck]
    rw [hRefl]
    unfold RuleProofs.eo_has_bool_type
    simpa [__eo_to_smt, __smtx_typeof] using
      RuleProofs.smtx_typeof_eq_refl (__smtx_typeof (__eo_to_smt x1)) hTrans

namespace RuleProofs

theorem correct___eo_prog_refl_of_smt_translation (M : SmtModel) (x1 : Term) :
  eo_has_smt_translation x1 ->
  eo_has_bool_type (__eo_prog_refl x1) ->
  eo_interprets M (__eo_prog_refl x1) true := by
  intro hTy _
  have hNotEqStuck : x1 ≠ Term.Stuck := by
    intro hStuck
    subst hStuck
    simp [eo_has_smt_translation, __eo_to_smt, __smtx_typeof] at hTy
  rw [eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M (__eo_to_smt (__eo_prog_refl x1)) ?_ ?_
  · simp [__eo_prog_refl, __eo_to_smt, __smtx_typeof]
    exact smtx_typeof_eq_refl (__smtx_typeof (__eo_to_smt x1)) hTy
  · simpa [__eo_prog_refl, hNotEqStuck, __eo_to_smt, __smtx_model_eval] using
      smtx_model_eval_eq_refl (__smtx_model_eval M (__eo_to_smt x1))

theorem not_eo_interprets_prog_refl_or_true (M : SmtModel) :
  ¬ eo_interprets M (__eo_prog_refl Term.or) true := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy hEval =>
      simp [__eo_prog_refl, __eo_to_smt, __smtx_typeof, __smtx_typeof_eq,
        __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at hTy

end RuleProofs

theorem correct___eo_prog_refl_impl
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  exact RuleProofs.correct___eo_prog_refl_of_smt_translation M x1

theorem correct___eo_prog_refl_of_smt_translation_impl
    (M : SmtModel) (_hM : smt_model_well_typed M) (x1 : Term) :
  RuleProofs.eo_has_smt_translation x1 ->
  RuleProofs.eo_has_bool_type (__eo_prog_refl x1) ->
  (eo_interprets M (__eo_prog_refl x1) true) :=
by
  exact RuleProofs.correct___eo_prog_refl_of_smt_translation M x1
