import CpcMini.Spec
import CpcMini.Lemmas

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
The final checker proof splits naturally into:
1. uniform rule-dispatch lemmas, one branch per `CRule`;
2. an execution invariant for command lists; and
3. a semantic bridge from `¬ eo_interprets F true` to `eo_interprets F false`
   for formulas accepted by `__eo_invoke_assume_list`.
-/

/-- The checker premises selected by a rule all interpret to `true`. -/
inductive PremisesTrue (S : CState) : CIndexList -> Prop
  | nil : PremisesTrue S CIndexList.nil
  | cons (i : CIndex) (is : CIndexList) :
      eo_interprets (__eo_state_proven_nth S i) true ->
      PremisesTrue S is ->
      PremisesTrue S (CIndexList.cons i is)

theorem not_smt_model_interprets_none_false (M : SmtModel) :
  ¬ smt_model_interprets M SmtTerm.None false := by
  intro h
  cases h with
  | intro_false hty _ =>
      simp [__smtx_typeof] at hty

theorem not_smt_interprets_none_false :
  ¬ smt_interprets SmtTerm.None false := by
  intro h
  cases h with
  | intro_false hnone =>
      exact not_smt_model_interprets_none_false SmtModel.empty (hnone SmtModel.empty)

theorem not_eo_interprets_stuck_false :
  ¬ eo_interprets Term.Stuck false := by
  intro h
  rcases h with ⟨s, hs, hi⟩
  cases hs
  exact not_smt_interprets_none_false (by simpa [obj_interprets, __eo_to_smt] using hi)

theorem eo_interprets_boolean_false_false :
  eo_interprets (Term.Boolean false) false := by
  refine ⟨SmtTerm.Boolean false, ?_, ?_⟩
  · simpa [__eo_to_smt] using (eo_is_obj.intro (Term.Boolean false))
  · apply smt_interprets.intro_false
    intro M
    exact smt_model_interprets.intro_false M (SmtTerm.Boolean false) rfl rfl

theorem not_eo_interprets_boolean_false_true :
  ¬ eo_interprets (Term.Boolean false) true := by
  intro h
  rcases h with ⟨s, hs, hi⟩
  cases hs
  cases hi with
  | intro_true hsat =>
      rcases hsat with ⟨M, hM⟩
      cases hM with
      | intro_true _ heval =>
          cases heval

/--
Uniform soundness dispatcher for non-pop checker steps.
Adding a new proof rule should amount to adding one new branch here and one
new local theorem in `Lemmas.lean`.
-/
theorem step_sound
    (S : CState) (r : CRule) (args : CArgList) (is : CIndexList)
    (h : PremisesTrue S is) :
    Not (eo_interprets (__eo_cmd_step_proven S r args is) false) := by
  cases r with
  | scope =>
      simpa [__eo_cmd_step_proven] using not_eo_interprets_stuck_false
  | contra =>
      cases h with
      | nil =>
          simpa [__eo_cmd_step_proven] using not_eo_interprets_stuck_false
      | cons i is hi hrest =>
          cases hrest with
          | nil =>
              simpa [__eo_cmd_step_proven] using not_eo_interprets_stuck_false
          | cons j js hj hrest2 =>
              cases hrest2 with
              | nil =>
                  cases args with
                  | nil =>
                      simpa [__eo_cmd_step_proven] using
                        correct___eo_prog_contra
                          (__eo_state_proven_nth S i)
                          (__eo_state_proven_nth S j)
                          hi
                          hj
                  | cons a args =>
                      simpa [__eo_cmd_step_proven] using not_eo_interprets_stuck_false
              | cons k ks hk hrest3 =>
                  simpa [__eo_cmd_step_proven] using not_eo_interprets_stuck_false
  | symm =>
      cases h with
      | nil =>
          simpa [__eo_cmd_step_proven] using not_eo_interprets_stuck_false
      | cons i is hi hrest =>
          cases hrest with
          | nil =>
              cases args with
              | nil =>
                  simpa [__eo_cmd_step_proven] using
                    correct___eo_prog_symm (__eo_state_proven_nth S i) hi
              | cons a args =>
                  simpa [__eo_cmd_step_proven] using not_eo_interprets_stuck_false
          | cons j js hj hrest2 =>
              simpa [__eo_cmd_step_proven] using not_eo_interprets_stuck_false

/--
Uniform soundness dispatcher for `step_pop`.
This is the place where new scoped rules can be added without reshaping the
final theorem.
-/
theorem step_pop_sound
    (S : CState) (r : CRule) (args : CArgList) (A : Term) (is : CIndexList)
    (h : PremisesTrue S is) :
    Not (eo_interprets (__eo_cmd_step_pop_proven S r args A is) false) := by
  cases r with
  | contra =>
      cases A <;> simpa [__eo_cmd_step_pop_proven] using not_eo_interprets_stuck_false
  | symm =>
      cases A <;> simpa [__eo_cmd_step_pop_proven] using not_eo_interprets_stuck_false
  | scope =>
      cases h with
      | nil =>
          cases A <;> simpa [__eo_cmd_step_pop_proven] using not_eo_interprets_stuck_false
      | cons i is hi hrest =>
          cases hrest with
          | nil =>
              cases args with
              | nil =>
                  cases A <;>
                    first
                    | simpa [__eo_cmd_step_pop_proven] using not_eo_interprets_stuck_false
                    | simpa [__eo_cmd_step_pop_proven] using
                        correct___eo_prog_scope _ (__eo_state_proven_nth S i) hi
              | cons a args =>
                  cases A <;> simpa [__eo_cmd_step_pop_proven] using not_eo_interprets_stuck_false
          | cons j js hj hrest2 =>
              cases A <;> simpa [__eo_cmd_step_pop_proven] using not_eo_interprets_stuck_false

theorem invoke_cmd_list_stuck (pf : CCmdList) :
  __eo_invoke_cmd_list CState.Stuck pf = CState.Stuck := by
  induction pf with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [__eo_invoke_cmd_list, __eo_invoke_cmd, ih]

theorem assume_list_not_stuck_of_refutation (F : Term) (pf : CCmdList) :
  eo_is_refutation F pf ->
  __eo_invoke_assume_list CState.nil F ≠ CState.Stuck := by
  intro href hstuck
  cases href with
  | intro hcheck =>
      have hfalse : __eo_checker_is_refutation F pf = false := by
        simp [__eo_checker_is_refutation, hstuck, invoke_cmd_list_stuck,
          __eo_state_is_refutation, __eo_invoke_cmd_check_proven, __eo_state_is_closed]
      have : false = true := hfalse.symm.trans hcheck
      cases this

/--
The remaining hard part is an execution invariant saying that a successful
certificate cannot start from assumptions that are jointly interpretable as
`true`.
-/
theorem checker_refutes_not_true (F : Term) (pf : CCmdList) :
  eo_is_refutation F pf ->
  ¬ eo_interprets F true := by
  sorry

/--
`__eo_invoke_assume_list` only accepts conjunction-chains ending in
`Term.Boolean true`, so the final bridge from `¬ true` to `false` can be
proved separately from the command-list induction.
-/
theorem assume_list_not_true_implies_false (F : Term) :
  __eo_invoke_assume_list CState.nil F ≠ CState.Stuck ->
  ¬ eo_interprets F true ->
  eo_interprets F false := by
  sorry

/- correctness theorem for the checker -/
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  (eo_is_refutation F pf) ->
  (eo_interprets F false) :=
by
  intro href
  exact assume_list_not_true_implies_false F
    (assume_list_not_stuck_of_refutation F pf href)
    (checker_refutes_not_true F pf href)
