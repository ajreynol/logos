module

public import Cpc.Proofs.CheckerState
import all Cpc.Proofs.CheckerState

/-!
# The variable-stability invariant

The checker invariant carrying the `StableWhenTrueInAnyVarModel` side
condition, kept apart from the rest because it is the one invariant a calculus
may not need.

It exists so that binder-sensitive rules -- `instantiate`, `skolemize`,
`alpha_equiv` -- can be handed premise truth in a *variable-variant* model,
which is the `RulePremiseEvidence.true_in_var_model` field.  A calculus whose
rules never look under a binder can define `StableWhenTrueInAnyVarModel` as
`True`, as `CpcMini` does, and everything here is then discharged for free by
`checkerAssumptionStabilityInvariant_any`.

Keeping it in its own module is what lets `Cpc/Proofs/CheckerState.lean` stay
free of it entirely, and confines the rest of the commitment to the five decls
of `Cpc/Proofs/CheckerCore.lean` that mention it.
-/

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 0
/-- Assumptions in an input formula remain true under variable-model changes. -/
inductive StableAssumptionList (M : SmtModel) : Term -> Prop
  | base : StableAssumptionList M (Term.Boolean true)
  | step (A rest : Term) :
      StableWhenTrueInAnyVarModel A ->
      StableAssumptionList M rest ->
      StableAssumptionList M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest)
/-- The model-dependent stability side condition for commands that introduce assumptions. -/
def cmdAssumptionStabilityOk (M : SmtModel) : CCmd -> Prop
  | CCmd.assume_push A => StableWhenTrueInAnyVarModel A
  | _ => True
/-- Every command in a checker command list satisfies `cmdAssumptionStabilityOk`. -/
inductive CmdListAssumptionStabilityOk (M : SmtModel) : CCmdList -> Prop
  | nil : CmdListAssumptionStabilityOk M CCmdList.nil
  | cons (c : CCmd) (cs : CCmdList) :
      cmdAssumptionStabilityOk M c ->
      CmdListAssumptionStabilityOk M cs ->
      CmdListAssumptionStabilityOk M (CCmdList.cons c cs)
/- Variable-model stability for assumptions.

   The local truth invariant already records stability for derived facts.
   Assumptions and local pushes are base facts, so the checker needs one
   extra invariant for precisely those entries if they may be used as
   binder-congruence premises.
-/
/-- Assumptions and pushed assumptions remain true under variable-model changes whenever true. -/
def checkerAssumptionStabilityInvariant (M : SmtModel) : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume A) s =>
      StableWhenTrueInAnyVarModel A ∧ checkerAssumptionStabilityInvariant M s
  | CState.cons (CStateObj.assume_push A) s =>
      StableWhenTrueInAnyVarModel A ∧ checkerAssumptionStabilityInvariant M s
  | CState.cons (CStateObj.proven _) s =>
      checkerAssumptionStabilityInvariant M s
  | CState.Stuck => True
/-- Describes `checkerAssumptionStabilityInvariant` on the stuck state. -/
theorem checkerAssumptionStabilityInvariant_stuck (M : SmtModel) :
  checkerAssumptionStabilityInvariant M CState.Stuck :=
by
  trivial
/-- Derives `checkerAssumptionStabilityInvariant` from `stateStepPopSuffix`. -/
theorem checkerAssumptionStabilityInvariant_of_stateStepPopSuffix (M : SmtModel) :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    checkerAssumptionStabilityInvariant M root ->
    checkerAssumptionStabilityInvariant M cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      intro hsRoot
      exact hsRoot
  | proven P hSuffix ih =>
      intro hsRoot
      exact ih (by simpa [checkerAssumptionStabilityInvariant] using hsRoot)
/-- Shows how `checkerAssumptionStabilityInvariant` behaves on suffix tails. -/
theorem checkerAssumptionStabilityInvariant_tail (M : SmtModel) :
  forall {so : CStateObj} {s : CState},
    checkerAssumptionStabilityInvariant M (CState.cons so s) ->
    checkerAssumptionStabilityInvariant M s
:=
by
  intro so s hs
  cases so with
  | assume A =>
      exact hs.2
  | assume_push A =>
      exact hs.2
  | proven P =>
      simpa [checkerAssumptionStabilityInvariant] using hs
/-- The assumption-stability invariant is independent of the current model. -/
theorem checkerAssumptionStabilityInvariant_rebase (M N : SmtModel) :
  forall {s : CState},
    checkerAssumptionStabilityInvariant M s ->
    checkerAssumptionStabilityInvariant N s
:=
by
  intro s hs
  induction s with
  | nil =>
      trivial
  | Stuck =>
      trivial
  | cons so s ih =>
      cases so with
      | assume A =>
          exact ⟨hs.1, ih hs.2⟩
      | assume_push A =>
          exact ⟨hs.1, ih hs.2⟩
      | proven P =>
          exact ih (by simpa [checkerAssumptionStabilityInvariant] using hs)
/-- Transfers the active input assumptions across a variable-model change. -/
theorem stateAssumes_true_in_var_model_of_assumptionStability
    (M : SmtModel) (hM : model_wf M) :
  forall {s : CState},
    checkerAssumptionStabilityInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    forall (N : SmtModel),
      model_wf N ->
      model_agrees_on_globals M N ->
      eo_interprets N (stateAssumes s) true
:=
by
  intro s hStable hAss
  induction s with
  | nil =>
      intro N hN hAgree
      simpa [stateAssumes] using eo_interprets_true N
  | Stuck =>
      intro N hN hAgree
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro N hN hAgree
      cases so with
      | assume A =>
          have hA : eo_interprets M A true :=
            eo_interprets_and_left M A (stateAssumes s) hAss
          have hTailAss : eo_interprets M (stateAssumes s) true :=
            eo_interprets_and_right M A (stateAssumes s) hAss
          have hA' : eo_interprets N A true :=
            hStable.1 M hM hA N hN hAgree
          have hTail' : eo_interprets N (stateAssumes s) true :=
            ih hStable.2 hTailAss N hN hAgree
          simpa [stateAssumes] using
            eo_interprets_and_intro N A (stateAssumes s) hA' hTail'
      | assume_push A =>
          exact ih hStable.2 (by simpa [stateAssumes] using hAss) N hN hAgree
      | proven P =>
          exact ih (by simpa [checkerAssumptionStabilityInvariant] using hStable)
            (by simpa [stateAssumes] using hAss) N hN hAgree
/-- Transfers the active pushed assumptions across a variable-model change. -/
theorem statePushes_true_in_var_model_of_assumptionStability
    (M : SmtModel) (hM : model_wf M) :
  forall {s : CState},
    checkerAssumptionStabilityInvariant M s ->
    eo_interprets M (statePushes s) true ->
    forall (N : SmtModel),
      model_wf N ->
      model_agrees_on_globals M N ->
      eo_interprets N (statePushes s) true
:=
by
  intro s hStable hPush
  induction s with
  | nil =>
      intro N hN hAgree
      simpa [statePushes] using eo_interprets_true N
  | Stuck =>
      intro N hN hAgree
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [statePushes] using hPush))
  | cons so s ih =>
      intro N hN hAgree
      cases so with
      | assume A =>
          exact ih hStable.2 (by simpa [statePushes] using hPush) N hN hAgree
      | assume_push A =>
          have hA : eo_interprets M A true :=
            eo_interprets_and_left M A (statePushes s) hPush
          have hTailPush : eo_interprets M (statePushes s) true :=
            eo_interprets_and_right M A (statePushes s) hPush
          have hA' : eo_interprets N A true :=
            hStable.1 M hM hA N hN hAgree
          have hTail' : eo_interprets N (statePushes s) true :=
            ih hStable.2 hTailPush N hN hAgree
          simpa [statePushes] using
            eo_interprets_and_intro N A (statePushes s) hA' hTail'
      | proven P =>
          exact ih (by simpa [checkerAssumptionStabilityInvariant] using hStable)
            (by simpa [statePushes] using hPush) N hN hAgree
/-- Describes `checkerAssumptionStabilityInvariant` after `assume_list`. -/
theorem checkerAssumptionStabilityInvariant_after_assume_list
    (M : SmtModel) (F : Term) :
  StableAssumptionList M F ->
  checkerAssumptionStabilityInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hStable
  induction hStable with
  | base =>
      simp [__eo_invoke_assume_list, checkerAssumptionStabilityInvariant]
  | step A rest hA hRest ih =>
      by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
      · change checkerAssumptionStabilityInvariant M
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_cons_of_guard_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        simpa [checkerAssumptionStabilityInvariant] using
          (show StableWhenTrueInAnyVarModel A ∧
              checkerAssumptionStabilityInvariant M
                (__eo_invoke_assume_list CState.nil rest) from
            ⟨hA, ih⟩)
      · change checkerAssumptionStabilityInvariant M
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_stuck_of_guard_ne_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        exact checkerAssumptionStabilityInvariant_stuck M
/-- A successful checked input-assumption pass yields stable assumptions. -/
theorem stableAssumptionList_of_stateOk_assume_list (M : SmtModel) :
  forall {F : Term},
    ValidAssumptionList F ->
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    StableAssumptionList M F
:=
by
  intro F hValid
  induction hValid with
  | base =>
      intro hOk
      exact StableAssumptionList.base
  | step A rest hRest ih =>
      intro hOk
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list, assumptionCheckGuard] using hOk
      have hClosed : __eo_is_closed A = Term.Boolean true :=
        push_input_assume_closed_of_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hRestOk : stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      exact StableAssumptionList.step A rest
        (stableWhenTrueInAnyVarModel_of_closed A hClosed)
        (ih hRestOk)
/-- A successful checked command invocation yields any stability invariant that the command introduces. -/
theorem cmdAssumptionStabilityOk_of_stateOk_invoke_cmd (M : SmtModel) :
  forall (s : CState) (c : CCmd),
    stateOk (__eo_invoke_cmd s c) ->
    cmdAssumptionStabilityOk M c
:=
by
  intro s c
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          intro hOk
          have hPushOk :
              stateOk (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil) := by
            simpa [__eo_invoke_cmd, assumptionCheckGuard] using hOk
          exact stableWhenTrueInAnyVarModel_of_closed A
            (push_assume_closed_of_stateOk A CState.nil hPushOk)
      | Stuck =>
          intro hOk
          simp [__eo_invoke_cmd, stateOk] at hOk
      | cons so s =>
          intro hOk
          have hPushOk :
              stateOk (__eo_push_assume_check (assumptionCheckGuard A) A
                (CState.cons so s)) := by
            simpa [__eo_invoke_cmd, assumptionCheckGuard] using hOk
          exact stableWhenTrueInAnyVarModel_of_closed A
            (push_assume_closed_of_stateOk A (CState.cons so s) hPushOk)
  | check_proven proven =>
      intro hOk
      simp [cmdAssumptionStabilityOk]
  | step r args premises =>
      intro hOk
      simp [cmdAssumptionStabilityOk]
  | step_pop r args premises =>
      intro hOk
      simp [cmdAssumptionStabilityOk]
/-- A successful checked command list yields stability for every command-introduced assumption. -/
theorem cmdListAssumptionStabilityOk_of_stateOk_invoke_cmd_list (M : SmtModel) :
  forall (s : CState) (cs : CCmdList),
    stateOk (__eo_invoke_cmd_list s cs) ->
    CmdListAssumptionStabilityOk M cs
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      intro hOk
      exact CmdListAssumptionStabilityOk.nil
  | cons c cs ih =>
      intro hOk
      have hTailOk :
          stateOk (__eo_invoke_cmd_list (__eo_invoke_cmd s c) cs) := by
        simpa [__eo_invoke_cmd_list] using hOk
      have hStepOk : stateOk (__eo_invoke_cmd s c) :=
        invoke_cmd_list_reflects_stateOk (__eo_invoke_cmd s c) cs hTailOk
      exact CmdListAssumptionStabilityOk.cons c cs
        (cmdAssumptionStabilityOk_of_stateOk_invoke_cmd M s c hStepOk)
        (ih (__eo_invoke_cmd s c) hTailOk)
