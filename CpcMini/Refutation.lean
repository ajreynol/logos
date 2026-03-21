import CpcMini.Spec
import CpcMini.Lemmas

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
The refutation proof has three layers.

1. `smt_interprets ... false` is the semantic negation of `... true`.
2. A structural invariant says every usable formula stored in the checker state
   interprets to `true`.
3. Each checker command preserves that invariant, with rule-specific reasoning
   isolated in `step_sound` and `step_pop_sound`.
-/

theorem smt_interprets_false_iff_not_true (t : SmtTerm) :
    smt_interprets t false ↔ ¬ smt_interprets t true := by
  constructor
  · intro hfalse htrue
    cases hfalse with
    | intro_false hnone =>
        cases htrue with
        | intro_true hsat =>
            rcases hsat with ⟨M, hM⟩
            exact hnone M hM
  · intro hnot
    exact smt_interprets.intro_false t (by
      intro M hM
      exact hnot (smt_interprets.intro_true t ⟨M, hM⟩))

theorem smt_interprets_true_of_not_false (t : SmtTerm) :
    ¬ smt_interprets t false -> smt_interprets t true := by
  intro hfalse
  by_cases htrue : smt_interprets t true
  · exact htrue
  · exact False.elim (hfalse ((smt_interprets_false_iff_not_true t).2 htrue))

theorem eo_interprets_true_iff (t : Term) :
    eo_interprets t true ↔ smt_interprets (__eo_to_smt t) true := by
  constructor
  · intro h
    rcases h with ⟨s, hs, hi⟩
    cases hs
    simpa using hi
  · intro h
    exact ⟨__eo_to_smt t, eo_is_obj.intro t, h⟩

theorem eo_interprets_false_iff (t : Term) :
    eo_interprets t false ↔ smt_interprets (__eo_to_smt t) false := by
  constructor
  · intro h
    rcases h with ⟨s, hs, hi⟩
    cases hs
    simpa using hi
  · intro h
    exact ⟨__eo_to_smt t, eo_is_obj.intro t, h⟩

theorem eo_interprets_false_iff_not_true (t : Term) :
    eo_interprets t false ↔ ¬ eo_interprets t true := by
  rw [eo_interprets_false_iff, eo_interprets_true_iff, smt_interprets_false_iff_not_true]

theorem eo_interprets_true_of_not_false (t : Term) :
    ¬ eo_interprets t false -> eo_interprets t true := by
  intro hfalse
  by_cases htrue : eo_interprets t true
  · exact htrue
  · exact False.elim (hfalse ((eo_interprets_false_iff_not_true t).2 htrue))

theorem eo_interprets_false_of_not_true (t : Term) :
    ¬ eo_interprets t true -> eo_interprets t false :=
  (eo_interprets_false_iff_not_true t).2

theorem eo_interprets_boolean_true_true :
    eo_interprets (Term.Boolean true) true := by
  refine ⟨SmtTerm.Boolean true, eo_is_obj.intro (Term.Boolean true), ?_⟩
  refine smt_interprets.intro_true (SmtTerm.Boolean true) ?_
  exact ⟨SmtModel.empty, smt_model_interprets.intro_true SmtModel.empty (SmtTerm.Boolean true) rfl rfl⟩

theorem not_smt_interprets_boolean_false_true :
    ¬ smt_interprets (SmtTerm.Boolean false) true := by
  intro h
  cases h with
  | intro_true hsat =>
      rcases hsat with ⟨M, hM⟩
      cases hM with
      | intro_true _ heval =>
          cases heval

theorem not_eo_interprets_boolean_false_true :
    ¬ eo_interprets (Term.Boolean false) true := by
  intro h
  exact not_smt_interprets_boolean_false_true ((eo_interprets_true_iff (Term.Boolean false)).1 h)

theorem not_smt_interprets_none_true :
    ¬ smt_interprets SmtTerm.None true := by
  intro h
  cases h with
  | intro_true hsat =>
      rcases hsat with ⟨M, hM⟩
      cases hM with
      | intro_true hty _ =>
          simp [__smtx_typeof] at hty

theorem not_eo_interprets_stuck_true :
    ¬ eo_interprets Term.Stuck true := by
  intro h
  exact not_smt_interprets_none_true ((eo_interprets_true_iff Term.Stuck).1 h)

theorem eo_prog_contra_stuck_left (t : Term) :
    __eo_prog_contra (Proof.pf Term.Stuck) (Proof.pf t) = Term.Stuck := by
  cases t <;>
    simp [__eo_prog_contra, __eo_requires, __eo_eq, eo_lit_teq, eo_lit_not,
      SmtEval.smt_lit_not, eo_lit_ite]
  case Apply f a =>
    cases f <;>
      simp [__eo_prog_contra, __eo_requires, __eo_eq, eo_lit_teq, eo_lit_not,
        SmtEval.smt_lit_not, eo_lit_ite]

theorem eo_prog_contra_stuck_right (t : Term) :
    __eo_prog_contra (Proof.pf t) (Proof.pf Term.Stuck) = Term.Stuck := by
  simp [__eo_prog_contra]

theorem eo_prog_symm_stuck :
    __eo_prog_symm (Proof.pf Term.Stuck) = Term.Stuck := by
  simp [__eo_prog_symm, __mk_symm]

theorem eo_prog_scope_stuck_right (A : Term) :
    __eo_prog_scope A (Proof.pf Term.Stuck) = Term.Stuck := by
  cases A <;> simp [__eo_prog_scope]

theorem smt_model_interprets_and_true_left (M : SmtModel) (x y : SmtTerm) :
    smt_model_interprets M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x) y) true ->
    smt_model_interprets M x true := by
  intro h
  cases h with
  | intro_true hty heval =>
      have htx : __smtx_typeof x = SmtType.Bool := by
        cases hx : __smtx_typeof x <;> cases hy : __smtx_typeof y <;>
          simp [__smtx_typeof, smt_lit_Teq, SmtEval.smt_lit_ite, hx, hy] at hty
        all_goals first | contradiction | simpa [hx]
      have hxeval : __smtx_model_eval M x = SmtValue.Boolean true := by
        cases hxv : __smtx_model_eval M x <;> cases hyv : __smtx_model_eval M y <;>
          simp [__smtx_model_eval, __smtx_model_eval_and, SmtEval.smt_lit_and, hxv, hyv] at heval
        all_goals first | contradiction | simpa [hxv] using heval.1
      exact smt_model_interprets.intro_true M x htx hxeval

theorem smt_model_interprets_and_true_right (M : SmtModel) (x y : SmtTerm) :
    smt_model_interprets M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and x) y) true ->
    smt_model_interprets M y true := by
  intro h
  cases h with
  | intro_true hty heval =>
      have hty' : __smtx_typeof y = SmtType.Bool := by
        cases hx : __smtx_typeof x <;> cases hy : __smtx_typeof y <;>
          simp [__smtx_typeof, smt_lit_Teq, SmtEval.smt_lit_ite, hx, hy] at hty
        all_goals first | contradiction | simpa [hy]
      have hyeval : __smtx_model_eval M y = SmtValue.Boolean true := by
        cases hxv : __smtx_model_eval M x <;> cases hyv : __smtx_model_eval M y <;>
          simp [__smtx_model_eval, __smtx_model_eval_and, SmtEval.smt_lit_and, hxv, hyv] at heval
        all_goals first | contradiction | simpa [hyv] using heval.2
      exact smt_model_interprets.intro_true M y hty' hyeval

theorem eo_interprets_and_true_left (x y : Term) :
    eo_interprets (Term.Apply (Term.Apply Term.and x) y) true ->
    eo_interprets x true := by
  intro h
  have hAnd :
      smt_interprets
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (__eo_to_smt x)) (__eo_to_smt y))
        true := by
    simpa [__eo_to_smt] using ((eo_interprets_true_iff (Term.Apply (Term.Apply Term.and x) y)).1 h)
  cases hAnd with
  | intro_true hsat =>
      rcases hsat with ⟨M, hM⟩
      exact (eo_interprets_true_iff x).2 <|
        smt_interprets.intro_true (__eo_to_smt x) ⟨M, smt_model_interprets_and_true_left M (__eo_to_smt x) (__eo_to_smt y) hM⟩

theorem eo_interprets_and_true_right (x y : Term) :
    eo_interprets (Term.Apply (Term.Apply Term.and x) y) true ->
    eo_interprets y true := by
  intro h
  have hAnd :
      smt_interprets
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (__eo_to_smt x)) (__eo_to_smt y))
        true := by
    simpa [__eo_to_smt] using ((eo_interprets_true_iff (Term.Apply (Term.Apply Term.and x) y)).1 h)
  cases hAnd with
  | intro_true hsat =>
      rcases hsat with ⟨M, hM⟩
      exact (eo_interprets_true_iff y).2 <|
        smt_interprets.intro_true (__eo_to_smt y) ⟨M, smt_model_interprets_and_true_right M (__eo_to_smt x) (__eo_to_smt y) hM⟩

/-- Every non-`Stuck` formula retrievable from the checker state is true. -/
inductive StateTrue : CState -> Prop where
  | nil :
      StateTrue CState.nil
  | assume (F : Term) (S : CState) :
      eo_interprets F true ->
      StateTrue S ->
      StateTrue (CState.cons (CStateObj.assume F) S)
  | assume_push (F : Term) (S : CState) :
      StateTrue S ->
      StateTrue (CState.cons (CStateObj.assume_push F) S)
  | proven (F : Term) (S : CState) :
      eo_interprets F true ->
      StateTrue S ->
      StateTrue (CState.cons (CStateObj.proven F) S)
  | stuck :
      StateTrue CState.Stuck

theorem state_true_nth (S : CState) (hS : StateTrue S) (i : CIndex) :
    __eo_state_proven_nth S i ≠ Term.Stuck ->
    eo_interprets (__eo_state_proven_nth S i) true := by
  induction hS generalizing i with
  | nil =>
      intro _
      simpa [__eo_state_proven_nth] using eo_interprets_boolean_true_true
  | assume F S hF hS ih =>
      intro hi
      cases i using Int.casesOn with
      | ofNat n =>
          cases n with
          | zero =>
              simpa [__eo_state_proven_nth, __eo_StateObj_proven] using hF
          | succ n =>
              simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
                ih (eo_lit_zplus (Int.ofNat (Nat.succ n)) (eo_lit_zneg 1)) hi
      | negSucc n =>
          simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
            ih (eo_lit_zplus (Int.negSucc n) (eo_lit_zneg 1)) hi
  | assume_push F S hS ih =>
      intro hi
      cases i using Int.casesOn with
      | ofNat n =>
          cases n with
          | zero =>
              exact False.elim (hi (by simp [__eo_state_proven_nth, __eo_StateObj_proven]))
          | succ n =>
              simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
                ih (eo_lit_zplus (Int.ofNat (Nat.succ n)) (eo_lit_zneg 1)) hi
      | negSucc n =>
          simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
            ih (eo_lit_zplus (Int.negSucc n) (eo_lit_zneg 1)) hi
  | proven F S hF hS ih =>
      intro hi
      cases i using Int.casesOn with
      | ofNat n =>
          cases n with
          | zero =>
              simpa [__eo_state_proven_nth, __eo_StateObj_proven] using hF
          | succ n =>
              simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
                ih (eo_lit_zplus (Int.ofNat (Nat.succ n)) (eo_lit_zneg 1)) hi
      | negSucc n =>
          simpa [__eo_state_proven_nth, __eo_StateObj_proven] using
            ih (eo_lit_zplus (Int.negSucc n) (eo_lit_zneg 1)) hi
  | stuck =>
      intro _
      simpa [__eo_state_proven_nth] using eo_interprets_boolean_true_true

theorem push_proven_eq_cons (F : Term) (S : CState) (hF : F ≠ Term.Stuck) :
    __eo_push_proven F S = CState.cons (CStateObj.proven F) S := by
  have hok : __eo_is_ok F = Term.Boolean true := by
    by_cases h : F = Term.Stuck
    · exact False.elim (hF h)
    · simp [__eo_is_ok, eo_lit_teq, eo_lit_not, SmtEval.smt_lit_not, h]
  simp [__eo_push_proven, __eo_push_proven_check, hok]

theorem state_true_push_proven (F : Term) (S : CState)
    (hF : eo_interprets F true) (hS : StateTrue S) :
    StateTrue (__eo_push_proven F S) := by
  have hne : F ≠ Term.Stuck := by
    intro hstuck
    subst hstuck
    exact not_eo_interprets_stuck_true hF
  simpa [push_proven_eq_cons F S hne] using StateTrue.proven F S hF hS

/--
Uniform soundness dispatcher for non-pop checker steps.
Adding a new proof rule should amount to adding one new branch here and one
new local theorem in `Lemmas.lean`.
-/
theorem step_sound
    (S : CState) (r : CRule) (args : CArgList) (is : CIndexList)
    (hS : StateTrue S)
    (hstep : __eo_cmd_step_proven S r args is ≠ Term.Stuck) :
    eo_interprets (__eo_cmd_step_proven S r args is) true := by
  cases r with
  | scope =>
      simp [__eo_cmd_step_proven] at hstep
  | contra =>
      cases args with
      | cons a args =>
          simp [__eo_cmd_step_proven] at hstep
      | nil =>
          cases is with
          | nil =>
              simp [__eo_cmd_step_proven] at hstep
          | cons i is =>
              cases is with
              | nil =>
                  simp [__eo_cmd_step_proven] at hstep
              | cons j js =>
                  cases js with
                  | nil =>
                      let t1 := __eo_state_proven_nth S i
                      let t2 := __eo_state_proven_nth S j
                      have ht1 : t1 ≠ Term.Stuck := by
                        intro h1
                        apply hstep
                        simpa [t1, t2, __eo_cmd_step_proven, h1] using eo_prog_contra_stuck_left t2
                      have ht2 : t2 ≠ Term.Stuck := by
                        intro h2
                        apply hstep
                        simpa [t1, t2, __eo_cmd_step_proven, h2] using eo_prog_contra_stuck_right t1
                      have h1 : eo_interprets t1 true := state_true_nth S hS i ht1
                      have h2 : eo_interprets t2 true := state_true_nth S hS j ht2
                      exact eo_interprets_true_of_not_false _ (correct___eo_prog_contra t1 t2 h1 h2)
                  | cons k ks =>
                      simp [__eo_cmd_step_proven] at hstep
  | symm =>
      cases args with
      | cons a args =>
          simp [__eo_cmd_step_proven] at hstep
      | nil =>
          cases is with
          | nil =>
              simp [__eo_cmd_step_proven] at hstep
          | cons i is =>
              cases is with
              | nil =>
                  let t := __eo_state_proven_nth S i
                  have ht : t ≠ Term.Stuck := by
                    intro h
                    apply hstep
                    simpa [t, __eo_cmd_step_proven, h] using eo_prog_symm_stuck
                  have htrue : eo_interprets t true := state_true_nth S hS i ht
                  exact eo_interprets_true_of_not_false _ (correct___eo_prog_symm t htrue)
              | cons j js =>
                  simp [__eo_cmd_step_proven] at hstep

/--
Uniform soundness dispatcher for `step_pop`.
This is the place where new scoped rules can be added without reshaping the
final theorem.
-/
theorem step_pop_sound
    (S : CState) (r : CRule) (args : CArgList) (A : Term) (is : CIndexList)
    (hS : StateTrue S)
    (hstep : __eo_cmd_step_pop_proven S r args A is ≠ Term.Stuck) :
    eo_interprets (__eo_cmd_step_pop_proven S r args A is) true := by
  cases r with
  | contra =>
      cases A <;> cases hstep (by simp [__eo_cmd_step_pop_proven])
  | symm =>
      cases A <;> cases hstep (by simp [__eo_cmd_step_pop_proven])
  | scope =>
      by_cases hA : A = Term.Stuck
      · subst hA
        cases hstep (by simp [__eo_cmd_step_pop_proven])
      cases args with
      | cons a args =>
          cases hstep (by simp [__eo_cmd_step_pop_proven, hA])
      | nil =>
          cases is with
          | nil =>
              cases hstep (by simp [__eo_cmd_step_pop_proven, hA])
          | cons i is =>
              cases is with
              | nil =>
                  let t := __eo_state_proven_nth S i
                  have ht : t ≠ Term.Stuck := by
                    intro h
                    apply hstep
                    simpa [t, __eo_cmd_step_pop_proven, h] using eo_prog_scope_stuck_right A
                  have htrue : eo_interprets t true := state_true_nth S hS i ht
                  have hnf :
                      ¬ eo_interprets (__eo_cmd_step_pop_proven S CRule.scope CArgList.nil A
                        (CIndexList.cons i CIndexList.nil)) false := by
                    simpa [__eo_cmd_step_pop_proven, hA] using correct___eo_prog_scope A t htrue
                  exact eo_interprets_true_of_not_false _ hnf
              | cons j js =>
                  cases hstep (by simp [__eo_cmd_step_pop_proven, hA])

theorem invoke_assume_list_state_true
    (S : CState) (F : Term) (hS : StateTrue S)
    (hF : eo_interprets F true) :
    StateTrue (__eo_invoke_assume_list S F) := by
  match F with
  | Term.Boolean true =>
      simpa [__eo_invoke_assume_list] using hS
  | Term.Boolean false =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | and =>
              simp [__eo_invoke_assume_list]
              exact StateTrue.assume x (__eo_invoke_assume_list S a)
                (eo_interprets_and_true_left x a (by simpa using hF))
                (invoke_assume_list_state_true S a hS (eo_interprets_and_true_right x a (by simpa using hF)))
          | _ =>
              simpa [__eo_invoke_assume_list] using StateTrue.stuck
      | _ =>
          simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.__eo_pf t =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Int =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Real =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.BitVec =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Char =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Seq =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Bool =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Numeral n =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Rational r =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.String s =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Binary w n =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Type =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Stuck =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.FunType =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.Var s T =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.DatatypeType s d =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.DtCons s d i =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.DtSel s d i j =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.USort i =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.UConst i T =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.not =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.or =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.and =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.imp =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
  | Term.eq =>
      simpa [__eo_invoke_assume_list] using StateTrue.stuck
termination_by sizeOf F
decreasing_by
  simp_wf
  have h : 0 < Nat.succ (sizeOf f) := Nat.succ_pos _
  simpa [Nat.succ_eq_add_one, Nat.add_comm] using h

theorem invoke_cmd_step_pop_state_true
    (S cursor : CState) (r : CRule) (args : CArgList) (is : CIndexList)
    (hS : StateTrue S) (hCursor : StateTrue cursor) :
    StateTrue (__eo_invoke_cmd_step_pop S cursor r args is) := by
  induction hCursor generalizing S with
  | nil =>
      simpa [__eo_invoke_cmd_step_pop] using StateTrue.stuck
  | stuck =>
      simpa [__eo_invoke_cmd_step_pop] using StateTrue.stuck
  | assume A S2 hA hS2 ih =>
      simpa [__eo_invoke_cmd_step_pop] using ih S hS
  | proven A S2 hA hS2 ih =>
      simpa [__eo_invoke_cmd_step_pop] using ih S hS
  | assume_push A S2 hS2 =>
      by_cases hstep : __eo_cmd_step_pop_proven S r args A is = Term.Stuck
      · simp [__eo_invoke_cmd_step_pop, __eo_push_proven, __eo_push_proven_check,
          __eo_is_ok, eo_lit_teq, hstep]
        exact StateTrue.stuck
      · simpa [__eo_invoke_cmd_step_pop] using
          state_true_push_proven (__eo_cmd_step_pop_proven S r args A is) S2
            (step_pop_sound S r args A is hS hstep) hS2

theorem invoke_cmd_state_true (S : CState) (c : CCmd) (hS : StateTrue S) :
    StateTrue (__eo_invoke_cmd S c) := by
  cases hS with
  | nil =>
      cases c with
      | assume_push A =>
          simpa [__eo_invoke_cmd, __eo_push_assume] using
            StateTrue.assume_push A CState.nil StateTrue.nil
      | check_proven proven =>
          simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven] using StateTrue.stuck
      | step r args premises =>
          by_cases hstep : __eo_cmd_step_proven CState.nil r args premises = Term.Stuck
          · simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
              eo_lit_teq, hstep]
            exact StateTrue.stuck
          · simpa [__eo_invoke_cmd] using
              state_true_push_proven (__eo_cmd_step_proven CState.nil r args premises) CState.nil
                (step_sound CState.nil r args premises StateTrue.nil hstep) StateTrue.nil
      | step_pop r args premises =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_state_true CState.nil CState.nil r args premises StateTrue.nil StateTrue.nil
  | assume F S hF hTail =>
      cases c with
      | assume_push A =>
          simpa [__eo_invoke_cmd, __eo_push_assume] using
            StateTrue.assume_push A _ (StateTrue.assume F S hF hTail)
      | check_proven proven =>
          simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven] using StateTrue.stuck
      | step r args premises =>
          by_cases hstep : __eo_cmd_step_proven (CState.cons (CStateObj.assume F) S) r args premises = Term.Stuck
          · simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
              eo_lit_teq, hstep]
            exact StateTrue.stuck
          · simpa [__eo_invoke_cmd] using
              state_true_push_proven (__eo_cmd_step_proven (CState.cons (CStateObj.assume F) S) r args premises)
                (CState.cons (CStateObj.assume F) S)
                (step_sound (CState.cons (CStateObj.assume F) S) r args premises
                  (StateTrue.assume F S hF hTail) hstep)
                (StateTrue.assume F S hF hTail)
      | step_pop r args premises =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_state_true
              (CState.cons (CStateObj.assume F) S)
              (CState.cons (CStateObj.assume F) S)
              r args premises
              (StateTrue.assume F S hF hTail)
              (StateTrue.assume F S hF hTail)
  | assume_push F S hTail =>
      cases c with
      | assume_push A =>
          simpa [__eo_invoke_cmd, __eo_push_assume] using
            StateTrue.assume_push A _ (StateTrue.assume_push F S hTail)
      | check_proven proven =>
          simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven] using StateTrue.stuck
      | step r args premises =>
          by_cases hstep : __eo_cmd_step_proven (CState.cons (CStateObj.assume_push F) S) r args premises = Term.Stuck
          · simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
              eo_lit_teq, hstep]
            exact StateTrue.stuck
          · simpa [__eo_invoke_cmd] using
              state_true_push_proven (__eo_cmd_step_proven (CState.cons (CStateObj.assume_push F) S) r args premises)
                (CState.cons (CStateObj.assume_push F) S)
                (step_sound (CState.cons (CStateObj.assume_push F) S) r args premises
                  (StateTrue.assume_push F S hTail) hstep)
                (StateTrue.assume_push F S hTail)
      | step_pop r args premises =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_state_true
              (CState.cons (CStateObj.assume_push F) S)
              (CState.cons (CStateObj.assume_push F) S)
              r args premises
              (StateTrue.assume_push F S hTail)
              (StateTrue.assume_push F S hTail)
  | proven F S hF hTail =>
      cases c with
      | assume_push A =>
          simpa [__eo_invoke_cmd, __eo_push_assume] using
            StateTrue.assume_push A _ (StateTrue.proven F S hF hTail)
      | check_proven proven =>
          cases hEq : __eo_eq F proven with
          | Stuck =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check, hEq]
              exact StateTrue.stuck
          | Boolean b =>
              cases b with
              | false =>
                  simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check, hEq]
                  exact StateTrue.stuck
              | true =>
                  simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check, hEq] using
                    StateTrue.proven F S hF hTail
          | _ =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check, hEq]
              exact StateTrue.stuck
      | step r args premises =>
          by_cases hstep : __eo_cmd_step_proven (CState.cons (CStateObj.proven F) S) r args premises = Term.Stuck
          · simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
              eo_lit_teq, hstep]
            exact StateTrue.stuck
          · simpa [__eo_invoke_cmd] using
              state_true_push_proven (__eo_cmd_step_proven (CState.cons (CStateObj.proven F) S) r args premises)
                (CState.cons (CStateObj.proven F) S)
                (step_sound (CState.cons (CStateObj.proven F) S) r args premises
                  (StateTrue.proven F S hF hTail) hstep)
                (StateTrue.proven F S hF hTail)
      | step_pop r args premises =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_state_true
              (CState.cons (CStateObj.proven F) S)
              (CState.cons (CStateObj.proven F) S)
              r args premises
              (StateTrue.proven F S hF hTail)
              (StateTrue.proven F S hF hTail)
  | stuck =>
      cases c <;> simpa [__eo_invoke_cmd] using StateTrue.stuck

theorem invoke_cmd_list_state_true (S : CState) (pf : CCmdList) (hS : StateTrue S) :
    StateTrue (__eo_invoke_cmd_list S pf) := by
  induction pf generalizing S with
  | nil =>
      simpa [__eo_invoke_cmd_list] using hS
  | cons c cs ih =>
      simpa [__eo_invoke_cmd_list] using ih (__eo_invoke_cmd S c) (invoke_cmd_state_true S c hS)

theorem state_true_not_refutation (S : CState) (hS : StateTrue S) :
    __eo_state_is_refutation S ≠ true := by
  cases hS with
  | nil =>
      simp [__eo_state_is_refutation, __eo_invoke_cmd_check_proven, __eo_state_is_closed]
  | assume F S hF hTail =>
      simp [__eo_state_is_refutation, __eo_invoke_cmd_check_proven, __eo_state_is_closed]
  | assume_push F S hTail =>
      simp [__eo_state_is_refutation, __eo_invoke_cmd_check_proven, __eo_state_is_closed]
  | stuck =>
      simp [__eo_state_is_refutation, __eo_invoke_cmd_check_proven, __eo_state_is_closed]
  | proven F S hF hTail =>
      intro href
      cases hEq : __eo_eq F (Term.Boolean false) <;>
        simp [__eo_state_is_refutation, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
          __eo_state_is_closed, hEq] at href
      case Boolean b =>
        cases b with
        | false =>
            simp [__eo_state_is_refutation, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
              __eo_state_is_closed, hEq] at href
        | true =>
            have hfalse : F = Term.Boolean false := by
              cases F <;> simp [__eo_eq, eo_lit_teq] at hEq
              case Boolean b =>
                simpa [hEq]
            subst hfalse
            exact not_eo_interprets_boolean_false_true hF

/--
The checker can only certify refutation if the assumptions are not jointly
satisfiable.
-/
theorem checker_refutes_not_true (F : Term) (pf : CCmdList) :
    eo_is_refutation F pf ->
    ¬ eo_interprets F true := by
  intro href hF
  cases href with
  | intro hcheck =>
      have hInit : StateTrue (__eo_invoke_assume_list CState.nil F) :=
        invoke_assume_list_state_true CState.nil F StateTrue.nil hF
      have hFinal : StateTrue (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) :=
        invoke_cmd_list_state_true (__eo_invoke_assume_list CState.nil F) pf hInit
      exact state_true_not_refutation
        (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf)
        hFinal
        (by simpa [__eo_checker_is_refutation] using hcheck)

theorem assume_list_not_true_implies_false (F : Term) :
    __eo_invoke_assume_list CState.nil F ≠ CState.Stuck ->
    ¬ eo_interprets F true ->
    eo_interprets F false := by
  intro _ hnot
  exact eo_interprets_false_of_not_true F hnot

/- correctness theorem for the checker -/
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
    eo_is_refutation F pf ->
    eo_interprets F false := by
  intro href
  exact eo_interprets_false_of_not_true F (checker_refutes_not_true F pf href)
