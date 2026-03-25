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

def eo_has_smt_translation (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

def eo_has_bool_type (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Bool

/-
Bridge from the checker-facing `__eo_typeof` guard to trusted SMT typing.

The intended use is: if a Eunoia term translates to some non-`None` SMT term
and the checker says its type is `Bool`, then the SMT translation should also
have SMT type `Bool`.

For now this is an assumed property of the future real `__eo_typeof`.
-/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  s ≠ SmtTerm.None ->
  __eo_typeof t = Term.Bool ->
  __smtx_typeof s = SmtType.Bool := by
  sorry

theorem eo_typeof_bool_implies_has_bool_type
    (t : Term) :
  eo_has_smt_translation t ->
  __eo_typeof t = Term.Bool ->
  eo_has_bool_type t := by
  intro hTrans hTy
  have hNotNone : __eo_to_smt t ≠ SmtTerm.None := by
    intro hNone
    apply hTrans
    simp [hNone, __smtx_typeof]
  exact eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t (__eo_to_smt t) rfl hNotNone hTy

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

theorem eo_interprets_not_of_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> eo_interprets M (Term.Apply Term.not t) true := by
  intro hFalse
  rw [eo_interprets_iff_smt_interprets] at hFalse ⊢
  cases hFalse with
  | intro_false hTy hEval =>
      refine smt_interprets.intro_true M (__eo_to_smt (Term.Apply Term.not t)) ?_ ?_
      · simp [__eo_to_smt, __smtx_typeof, hTy, smt_lit_Teq, smt_lit_ite]
      · simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_not, hEval,
          SmtEval.smt_lit_not]

theorem term_ne_stuck_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets] at h
  cases h with
  | intro_true hTy _ =>
      simp [__eo_to_smt, __smtx_typeof] at hTy

theorem term_ne_stuck_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets] at h
  cases h with
  | intro_false hTy _ =>
      simp [__eo_to_smt, __smtx_typeof] at hTy

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

theorem smtx_typeof_eq_refl (T : SmtType) :
  T ≠ SmtType.None -> __smtx_typeof_eq T T = SmtType.Bool := by
  intro hT
  unfold __smtx_typeof_eq __smtx_typeof_guard
  simp [smt_lit_ite, smt_lit_Teq, hT]

theorem smtx_model_eval_eq_refl (v : SmtValue) :
  __smtx_model_eval_eq v v = SmtValue.Boolean true := by
  unfold __smtx_model_eval_eq
  cases v <;> simp [smt_lit_veq]

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
