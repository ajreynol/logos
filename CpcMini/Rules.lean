import CpcMini.Spec

open Eo
open Smtm

namespace RuleProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem eo_interprets_iff_smt_interprets (M : SmtModel) (t : Term) (b : Bool) :
  eo_interprets M t b ↔ smt_interprets M (__eo_to_smt t) b := by
  constructor
  · intro h
    rcases h with ⟨s, hs, hInterp⟩
    cases hs
    simpa using hInterp
  · intro h
    exact ⟨__eo_to_smt t, eo_is_obj.intro t, h⟩

theorem eo_interprets_true (M : SmtModel) :
  eo_interprets M (Term.Boolean true) true := by
  rw [eo_interprets_iff_smt_interprets]
  exact smt_interprets.intro_true M (__eo_to_smt (Term.Boolean true)) rfl rfl

theorem eo_interprets_true_not_false (M : SmtModel) (t : Term) :
  eo_interprets M t true -> ¬ eo_interprets M t false := by
  intro hTrue hFalse
  rw [eo_interprets_iff_smt_interprets] at hTrue hFalse
  cases hTrue with
  | intro_true hTyTrue hEvalTrue =>
      cases hFalse with
      | intro_false hTyFalse hEvalFalse =>
          rw [hEvalTrue] at hEvalFalse
          cases hEvalFalse

set_option linter.unusedSimpArgs false in
theorem eo_interprets_not_true_implies_false (M : SmtModel) (t : Term) :
  eo_interprets M (Term.Apply Term.not t) true -> eo_interprets M t false := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  cases h with
  | intro_true hty hEval =>
      have htyt : __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
        simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite] at hty
        exact hty
      cases ht : __smtx_model_eval M (__eo_to_smt t) <;>
        simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_not, ht, SmtEval.smt_lit_not] at hEval
      case Boolean b =>
        cases b <;> simp [SmtEval.smt_lit_not] at hEval
        exact smt_interprets.intro_false M (__eo_to_smt t) htyt ht

theorem not_eo_interprets_prog_refl_or_true (M : SmtModel) :
  ¬ eo_interprets M (__eo_prog_refl Term.or) true := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy hEval =>
      simp [__eo_prog_refl, __eo_to_smt, __smtx_typeof, __smtx_typeof_eq,
        __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at hTy

theorem not_eo_interprets_prog_scope_num_true (M : SmtModel) :
  ¬ eo_interprets M (__eo_prog_scope (Term.Numeral 0) (Proof.pf (Term.Boolean true))) true := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy hEval =>
      simp [__eo_prog_scope, __eo_to_smt, __smtx_typeof, smt_lit_ite, smt_lit_Teq] at hTy

end RuleProofs
