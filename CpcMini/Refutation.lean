import CpcMini.Spec
import CpcMini.Lemmas

open Eo
open Smtm

inductive ValidAssumptionList : Term -> Prop
  | base : ValidAssumptionList (Term.Boolean true)
  | step (A rest : Term) : ValidAssumptionList rest ->
      ValidAssumptionList (Term.Apply (Term.Apply Term.and A) rest)

def stateOk : CState -> Prop
  | CState.nil => True
  | CState.cons _ s => stateOk s
  | CState.Stuck => False

theorem eo_interprets_iff_smt_interprets (M : SmtModel) (t : Term) (b : Bool) :
  eo_interprets M t b ↔ smt_interprets M (__eo_to_smt t) b :=
by
  constructor
  · intro h
    rcases h with ⟨s, hs, hInterp⟩
    cases hs
    simpa using hInterp
  · intro h
    exact ⟨__eo_to_smt t, eo_is_obj.intro t, h⟩

theorem eo_interprets_true (M : SmtModel) :
  eo_interprets M (Term.Boolean true) true :=
by
  rw [eo_interprets_iff_smt_interprets]
  exact smt_interprets.intro_true M (__eo_to_smt (Term.Boolean true)) rfl rfl

theorem eo_interprets_false (M : SmtModel) :
  eo_interprets M (Term.Boolean false) false :=
by
  rw [eo_interprets_iff_smt_interprets]
  exact smt_interprets.intro_false M (__eo_to_smt (Term.Boolean false)) rfl rfl

theorem eo_interprets_false_true_absurd (M : SmtModel) :
  ¬ eo_interprets M (Term.Boolean false) true :=
by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true _ hEval =>
      cases hEval

theorem eo_interprets_stuck_false_absurd (M : SmtModel) :
  ¬ eo_interprets M Term.Stuck false :=
by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_false hty _ =>
      simp [__eo_to_smt, __smtx_typeof] at hty

theorem eo_interprets_stuck_true_absurd (M : SmtModel) :
  ¬ eo_interprets M Term.Stuck true :=
by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hty _ =>
      simp [__eo_to_smt, __smtx_typeof] at hty

theorem eo_interprets_true_not_false (M : SmtModel) (t : Term) :
  eo_interprets M t true ->
  ¬ eo_interprets M t false :=
by
  intro hTrue hFalse
  rw [eo_interprets_iff_smt_interprets] at hTrue hFalse
  cases hTrue with
  | intro_true hTyTrue hEvalTrue =>
      cases hFalse with
      | intro_false hTyFalse hEvalFalse =>
          rw [hEvalTrue] at hEvalFalse
          cases hEvalFalse

theorem eo_interprets_and_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) true ->
  eo_interprets M A true :=
by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  cases h with
  | intro_true hty hEval =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        by_cases hA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool
        · exact hA
        · have : False := by
            simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite, hA] at hty
          exact False.elim this
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __eo_to_smt, __smtx_model_eval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.smt_lit_and] at hEval
          simp [hAeval, hEval]
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

theorem eo_interprets_and_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) true ->
  eo_interprets M B true :=
by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  cases h with
  | intro_true hty hEval =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        by_cases hB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool
        · exact hB
        · have : False := by
            simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite, hB] at hty
          exact False.elim this
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __eo_to_smt, __smtx_model_eval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.smt_lit_and] at hEval
          simp [hBeval, hEval]
      exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

theorem eo_interprets_imp_elim (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) true ->
  eo_interprets M A true ->
  eo_interprets M B true :=
by
  intro hImp hA
  rw [eo_interprets_iff_smt_interprets] at hImp hA ⊢
  cases hImp with
  | intro_true htyImp hEvalImp =>
      cases hA with
      | intro_true htyA hEvalA =>
          have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
            simp [__eo_to_smt, __smtx_typeof, htyA, smt_lit_Teq, smt_lit_ite] at htyImp
            exact htyImp
          have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
            cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
              simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_imp, __smtx_model_eval_or,
                __smtx_model_eval_not, hEvalA, hBeval, SmtEval.smt_lit_or, SmtEval.smt_lit_not] at hEvalImp
            case Boolean a =>
              cases a <;> simp at hEvalImp
              simp [hBeval, hEvalImp]
          exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

theorem eo_interprets_imp_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) true :=
by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · simp [__eo_to_smt, __smtx_typeof, htyA, htyB, smt_lit_Teq, smt_lit_ite]
          · simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_imp, __smtx_model_eval_or,
              __smtx_model_eval_not, hEvalA, hEvalB, SmtEval.smt_lit_or, SmtEval.smt_lit_not]

theorem eo_interprets_imp_false_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) false ->
  eo_interprets M A true :=
by
  intro hImp
  rw [eo_interprets_iff_smt_interprets] at hImp ⊢
  cases hImp with
  | intro_false htyImp hEvalImp =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        by_cases hA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool
        · exact hA
        · have : False := by
            simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite, hA] at htyImp
          exact False.elim this
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_imp, __smtx_model_eval_or,
            __smtx_model_eval_not, hAeval, hBeval, SmtEval.smt_lit_or, SmtEval.smt_lit_not] at hEvalImp
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp at hEvalImp
          simp [hAeval, hEvalImp]
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

theorem eo_interprets_imp_false_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) false ->
  eo_interprets M B false :=
by
  intro hImp
  rw [eo_interprets_iff_smt_interprets] at hImp ⊢
  cases hImp with
  | intro_false htyImp hEvalImp =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
          by_cases hA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool
          · exact hA
          · have : False := by
              simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite, hA] at htyImp
            exact False.elim this
        by_cases hB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool
        · exact hB
        · have : False := by
            simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite, htyA, hB] at htyImp
          exact False.elim this
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean false := by
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_imp, __smtx_model_eval_or,
            __smtx_model_eval_not, hAeval, hBeval, SmtEval.smt_lit_or, SmtEval.smt_lit_not] at hEvalImp
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp at hEvalImp
          simp [hBeval, hEvalImp]
      exact smt_interprets.intro_false M (__eo_to_smt B) htyB hEvalB

theorem eo_interprets_imp_false_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B false ->
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) false :=
by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_false htyB hEvalB =>
          apply smt_interprets.intro_false
          · simp [__eo_to_smt, __smtx_typeof, htyA, htyB, smt_lit_Teq, smt_lit_ite]
          · simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_imp, __smtx_model_eval_or,
              __smtx_model_eval_not, hEvalA, hEvalB, SmtEval.smt_lit_or, SmtEval.smt_lit_not]

theorem eo_interprets_and_false_left_of_right_not_false (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) false ->
  ¬ eo_interprets M B false ->
  eo_interprets M A false :=
by
  intro hAnd hBNotFalse
  rw [eo_interprets_iff_smt_interprets] at hAnd hBNotFalse ⊢
  cases hAnd with
  | intro_false hty hEval =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        by_cases hA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool
        · exact hA
        · have : False := by
            simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite, hA] at hty
          exact False.elim this
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        by_cases hB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool
        · exact hB
        · have : False := by
            simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite, htyA, hB] at hty
          exact False.elim this
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false := by
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_and, hAeval, hBeval] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b
          · simp [SmtEval.smt_lit_and] at hEval
            have hBFalse : smt_interprets M (__eo_to_smt B) false :=
              smt_interprets.intro_false M (__eo_to_smt B) htyB hBeval
            exact False.elim (hBNotFalse hBFalse)
          · simp [SmtEval.smt_lit_and] at hEval
            simp [hAeval]
          · simp [SmtEval.smt_lit_and] at hEval
            have hBFalse : smt_interprets M (__eo_to_smt B) false :=
              smt_interprets.intro_false M (__eo_to_smt B) htyB hBeval
            exact False.elim (hBNotFalse hBFalse)
          · simp [SmtEval.smt_lit_and] at hEval
      exact smt_interprets.intro_false M (__eo_to_smt A) htyA hEvalA

theorem eo_interprets_and_false_right_true_of_left_false_and_right_not_false
    (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) false ->
  eo_interprets M A false ->
  ¬ eo_interprets M B false ->
  eo_interprets M B true :=
by
  intro hAnd hAFalse hBNotFalse
  rw [eo_interprets_iff_smt_interprets] at hAnd hAFalse hBNotFalse ⊢
  cases hAnd with
  | intro_false htyAnd hEvalAnd =>
      cases hAFalse with
      | intro_false htyA hEvalA =>
          have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
            simp [__eo_to_smt, __smtx_typeof, htyA, smt_lit_Teq, smt_lit_ite] at htyAnd
            exact htyAnd
          have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
            cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
              simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_and, hEvalA, hBeval] at hEvalAnd
            case Boolean b =>
              cases b with
              | false =>
                  have hBFalse : smt_interprets M (__eo_to_smt B) false :=
                    smt_interprets.intro_false M (__eo_to_smt B) htyB hBeval
                  exact False.elim (hBNotFalse hBFalse)
              | true =>
                  simpa using hBeval
          exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

def stateAssumes : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.assume F) s => Term.Apply (Term.Apply Term.and F) (stateAssumes s)
  | CState.cons _ s => stateAssumes s
  | CState.Stuck => Term.Stuck

def statePushes : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.assume_push F) s => Term.Apply (Term.Apply Term.and F) (statePushes s)
  | CState.cons _ s => statePushes s
  | CState.Stuck => Term.Stuck

def stateProvens : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.proven F) s => Term.Apply (Term.Apply Term.and F) (stateProvens s)
  | CState.cons _ s => stateProvens s
  | CState.Stuck => Term.Stuck

/-
Because the checker pushes new entries at the head of the state, the initial
assumptions from `__eo_invoke_assume_list` live in a tail block of reachable
states. This is the structural fact that lets `step_pop` discard a prefix
without changing the assumption component.
-/
def stateAssumptionTail : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume _) s => stateAssumptionTail s
  | _ => False

def stateAssumptionSuffix : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume _) s => stateAssumptionTail s
  | CState.cons _ s => stateAssumptionSuffix s
  | CState.Stuck => False

theorem stateAssumptionSuffix_of_tail :
  forall {s : CState}, stateAssumptionTail s -> stateAssumptionSuffix s
:=
by
  intro s hTail
  cases s with
  | nil =>
      trivial
  | Stuck =>
      cases hTail
  | cons so s =>
      cases so <;> simp [stateAssumptionTail, stateAssumptionSuffix] at hTail ⊢
      exact hTail

theorem stateOk_not_stuck {s : CState} :
  stateOk s -> s ≠ CState.Stuck :=
by
  intro hOk hStuck
  subst hStuck
  simpa [stateOk] using hOk

/- Legacy whole-state summary of a state.
   The checker correctness proof below now uses `checkerConjunctInvariant`
   as its primary invariant, but this formula view is still useful for
   isolated semantic experiments. -/
def eo_state_to_formula : CState -> Term
  | CState.Stuck => Term.Stuck
  | s =>
      Term.Apply (Term.Apply Term.imp (stateAssumes s))
        (Term.Apply (Term.Apply Term.imp (statePushes s)) (stateProvens s))

def checkerInvariant (M : SmtModel) (s : CState) : Prop :=
  ¬ eo_interprets M (eo_state_to_formula s) false

theorem checkerInvariant_stuck (M : SmtModel) : checkerInvariant M CState.Stuck :=
by
  unfold checkerInvariant
  simpa [eo_state_to_formula] using eo_interprets_stuck_false_absurd M

/-
Primary checker invariant: under globally true assumptions and local pushes,
no individual proven conjunct in the state may interpret as false.

This is stronger in exactly the way needed for the final contradiction:
if the checker finishes with a top proved `false`, then that conjunct
itself violates the invariant.
-/
def checkerConjunctInvariant (M : SmtModel) : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.proven P) s =>
      (eo_interprets M (stateAssumes s) true ->
       eo_interprets M (statePushes s) true ->
       ¬ eo_interprets M P false) ∧
      checkerConjunctInvariant M s
  | CState.cons _ s => checkerConjunctInvariant M s
  | CState.Stuck => True

theorem checkerConjunctInvariant_stuck (M : SmtModel) :
  checkerConjunctInvariant M CState.Stuck :=
by
  trivial

/- Supplementary indexed-truth invariant: under globally true assumptions and
   local pushes, every indexed state entry is true. Since `CStateObj.Stuck`
   has been removed, indexed lookup can be handled directly from the semantic
   context, without extra per-rule premise side lemmas. We keep the conjunct
   invariant as the contradiction-friendly summary used at the end of the
   checker proof. -/
def checkerTruthInvariant (M : SmtModel) : CState -> Prop
  | CState.Stuck => True
  | s =>
      ∀ n : eo_lit_Int,
        eo_interprets M (stateAssumes s) true ->
        eo_interprets M (statePushes s) true ->
        eo_interprets M (__eo_state_proven_nth s n) true

theorem checkerTruthInvariant_stuck (M : SmtModel) :
  checkerTruthInvariant M CState.Stuck :=
by
  trivial

def checkerStateInvariant (M : SmtModel) (s : CState) : Prop :=
  checkerConjunctInvariant M s ∧ checkerTruthInvariant M s

theorem checkerConjunctInvariant_after_assume_list (M : SmtModel) (F : Term) :
  ValidAssumptionList F ->
  checkerConjunctInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hValid
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, checkerConjunctInvariant]
  | step A rest hRest ih =>
      simpa [__eo_invoke_assume_list, checkerConjunctInvariant] using ih

theorem push_proven_preserves_conjunctInvariant_of_not_false
    (M : SmtModel) (s : CState) (P : Term) :
  checkerConjunctInvariant M s ->
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   ¬ eo_interprets M P false) ->
  checkerConjunctInvariant M (CState.cons (CStateObj.proven P) s) :=
by
  intro hInv hP
  exact ⟨hP, hInv⟩

theorem top_proven_not_false_of_conjunctInvariant
    (M : SmtModel) (s : CState) (P : Term) :
  checkerConjunctInvariant M (CState.cons (CStateObj.proven P) s) ->
  eo_interprets M (stateAssumes s) true ->
  eo_interprets M (statePushes s) true ->
  ¬ eo_interprets M P false :=
by
  intro hInv hAss hPush
  exact hInv.1 hAss hPush

theorem provens_not_false_of_invariant (M : SmtModel) (s : CState) :
  checkerInvariant M s ->
  eo_interprets M (stateAssumes s) true ->
  eo_interprets M (statePushes s) true ->
  ¬ eo_interprets M (stateProvens s) false :=
by
  intro hInv hAss hPush hProvFalse
  cases s with
  | nil =>
      unfold checkerInvariant at hInv
      have hStateFalse : eo_interprets M (eo_state_to_formula CState.nil) false := by
        simpa [eo_state_to_formula, stateAssumes, statePushes, stateProvens] using
          (eo_interprets_imp_false_intro M (stateAssumes CState.nil)
            (Term.Apply (Term.Apply Term.imp (statePushes CState.nil)) (stateProvens CState.nil)) hAss
            (eo_interprets_imp_false_intro M (statePushes CState.nil) (stateProvens CState.nil) hPush hProvFalse))
      exact hInv hStateFalse
  | cons so s =>
      unfold checkerInvariant at hInv
      have hStateFalse : eo_interprets M (eo_state_to_formula (CState.cons so s)) false := by
        simpa [eo_state_to_formula, stateAssumes, statePushes, stateProvens] using
          (eo_interprets_imp_false_intro M (stateAssumes (CState.cons so s))
            (Term.Apply (Term.Apply Term.imp (statePushes (CState.cons so s))) (stateProvens (CState.cons so s))) hAss
            (eo_interprets_imp_false_intro M (statePushes (CState.cons so s)) (stateProvens (CState.cons so s)) hPush hProvFalse))
      exact hInv hStateFalse
  | Stuck =>
      cases (eo_interprets_stuck_false_absurd M hProvFalse)

theorem pushed_proven_false_of_post_false (M : SmtModel) (s : CState) (P : Term) :
  checkerInvariant M s ->
  eo_interprets M (eo_state_to_formula (CState.cons (CStateObj.proven P) s)) false ->
  eo_interprets M P false :=
by
  intro hs hPostFalse
  have hAssumesTrue : eo_interprets M (stateAssumes s) true :=
    eo_interprets_imp_false_left M (stateAssumes s)
      (Term.Apply (Term.Apply Term.imp (statePushes s))
        (Term.Apply (Term.Apply Term.and P) (stateProvens s)))
      (by simpa [eo_state_to_formula, stateAssumes, statePushes, stateProvens] using hPostFalse)
  have hInnerFalse :
      eo_interprets M
        (Term.Apply (Term.Apply Term.imp (statePushes s))
          (Term.Apply (Term.Apply Term.and P) (stateProvens s))) false :=
    eo_interprets_imp_false_right M (stateAssumes s)
      (Term.Apply (Term.Apply Term.imp (statePushes s))
        (Term.Apply (Term.Apply Term.and P) (stateProvens s)))
      (by simpa [eo_state_to_formula, stateAssumes, statePushes, stateProvens] using hPostFalse)
  have hPushesTrue : eo_interprets M (statePushes s) true :=
    eo_interprets_imp_false_left M (statePushes s)
      (Term.Apply (Term.Apply Term.and P) (stateProvens s))
      hInnerFalse
  have hAndFalse :
      eo_interprets M (Term.Apply (Term.Apply Term.and P) (stateProvens s)) false :=
    eo_interprets_imp_false_right M (statePushes s)
      (Term.Apply (Term.Apply Term.and P) (stateProvens s))
      hInnerFalse
  have hOldProvensNotFalse : ¬ eo_interprets M (stateProvens s) false :=
    provens_not_false_of_invariant M s hs hAssumesTrue hPushesTrue
  exact eo_interprets_and_false_left_of_right_not_false M P (stateProvens s)
    hAndFalse hOldProvensNotFalse

theorem push_proven_preserves_invariant_of_not_false (M : SmtModel) (s : CState) (P : Term) :
  checkerInvariant M s ->
  ¬ eo_interprets M P false ->
  checkerInvariant M (CState.cons (CStateObj.proven P) s) :=
by
  intro hs hPFalse
  unfold checkerInvariant
  intro hPostFalse
  exact hPFalse (pushed_proven_false_of_post_false M s P hs hPostFalse)

theorem checkerInvariant_of_eq_stuck (M : SmtModel) {s : CState} :
  s = CState.Stuck -> checkerInvariant M s :=
by
  intro hStuck
  subst hStuck
  exact checkerInvariant_stuck M

theorem invoke_step_eq_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_invoke_cmd s (CCmd.step r args premises) =
    __eo_push_proven (__eo_cmd_step_proven s r args premises) s :=
by
  cases s with
  | nil =>
      simp [__eo_invoke_cmd]
  | cons so s =>
      simp [__eo_invoke_cmd]
  | Stuck =>
      exact False.elim (hNotStuck rfl)

theorem invoke_step_eq_stuck_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
by
  intro hStep
  rw [invoke_step_eq_of_nonstuck s hNotStuck r args premises, hStep]
  simp [__eo_push_proven, __eo_push_proven_check, __eo_is_ok, eo_lit_teq, eo_lit_not,
    SmtEval.smt_lit_not]

theorem invoke_step_eq_cons_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  __eo_cmd_step_proven s r args premises = P ->
  P ≠ Term.Stuck ->
  __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
by
  intro hStep hNe
  rw [invoke_step_eq_of_nonstuck s hNotStuck r args premises, hStep]
  simp [__eo_push_proven, __eo_push_proven_check, __eo_is_ok, eo_lit_teq, eo_lit_not,
    SmtEval.smt_lit_not, hNe]

theorem invoke_step_preserves_invariant_of_stuck
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  checkerInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hStep
  exact checkerInvariant_of_eq_stuck M
    (invoke_step_eq_stuck_of_nonstuck s hNotStuck r args premises hStep)

theorem invoke_step_preserves_invariant_of_not_false
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  checkerInvariant M s ->
  __eo_cmd_step_proven s r args premises = P ->
  P ≠ Term.Stuck ->
  ¬ eo_interprets M P false ->
  checkerInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hStep hNe hPFalse
  have hPost :
      __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
    invoke_step_eq_cons_of_nonstuck s hNotStuck r args premises P hStep hNe
  simpa [hPost] using push_proven_preserves_invariant_of_not_false M s P hs hPFalse

theorem invoke_step_preserves_invariant_of_cmd_step_proven
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerInvariant M s ->
  ¬ eo_interprets M (__eo_cmd_step_proven s r args premises) false ->
  checkerInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hStepNotFalse
  by_cases hStep : __eo_cmd_step_proven s r args premises = Term.Stuck
  · exact invoke_step_preserves_invariant_of_stuck M s hNotStuck r args premises hStep
  · exact invoke_step_preserves_invariant_of_not_false M s hNotStuck r args premises
      (__eo_cmd_step_proven s r args premises) hs rfl hStep hStepNotFalse

theorem post_proven_context_true_of_false (M : SmtModel) (s : CState) (P : Term) :
  checkerInvariant M s ->
  eo_interprets M (eo_state_to_formula (CState.cons (CStateObj.proven P) s)) false ->
  eo_interprets M P false ∧
  eo_interprets M (stateAssumes s) true ∧
  eo_interprets M (statePushes s) true ∧
  eo_interprets M (stateProvens s) true :=
by
  intro hs hPostFalse
  have hPFalse : eo_interprets M P false :=
    pushed_proven_false_of_post_false M s P hs hPostFalse
  have hAssumesTrue : eo_interprets M (stateAssumes s) true :=
    eo_interprets_imp_false_left M (stateAssumes s)
      (Term.Apply (Term.Apply Term.imp (statePushes s))
        (Term.Apply (Term.Apply Term.and P) (stateProvens s)))
      (by simpa [eo_state_to_formula, stateAssumes, statePushes, stateProvens] using hPostFalse)
  have hInnerFalse :
      eo_interprets M
        (Term.Apply (Term.Apply Term.imp (statePushes s))
          (Term.Apply (Term.Apply Term.and P) (stateProvens s))) false :=
    eo_interprets_imp_false_right M (stateAssumes s)
      (Term.Apply (Term.Apply Term.imp (statePushes s))
        (Term.Apply (Term.Apply Term.and P) (stateProvens s)))
      (by simpa [eo_state_to_formula, stateAssumes, statePushes, stateProvens] using hPostFalse)
  have hPushesTrue : eo_interprets M (statePushes s) true :=
    eo_interprets_imp_false_left M (statePushes s)
      (Term.Apply (Term.Apply Term.and P) (stateProvens s))
      hInnerFalse
  have hAndFalse :
      eo_interprets M (Term.Apply (Term.Apply Term.and P) (stateProvens s)) false :=
    eo_interprets_imp_false_right M (statePushes s)
      (Term.Apply (Term.Apply Term.and P) (stateProvens s))
      hInnerFalse
  have hOldProvensNotFalse : ¬ eo_interprets M (stateProvens s) false :=
    provens_not_false_of_invariant M s hs hAssumesTrue hPushesTrue
  have hProvensTrue : eo_interprets M (stateProvens s) true :=
    eo_interprets_and_false_right_true_of_left_false_and_right_not_false M P (stateProvens s)
      hAndFalse hPFalse hOldProvensNotFalse
  exact ⟨hPFalse, hAssumesTrue, hPushesTrue, hProvensTrue⟩

theorem state_proven_nth_true_of_context (M : SmtModel) :
  forall (s : CState) (n : eo_lit_Int),
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M (stateProvens s) true ->
    eo_interprets M (__eo_state_proven_nth s n) true
:=
by
  intro s
  induction s with
  | nil =>
      intro n hAss hPush hProv
      simpa [__eo_state_proven_nth] using eo_interprets_true M
  | Stuck =>
      intro n hAss hPush hProv
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro n hAss hPush hProv
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth] using eo_interprets_and_left M A (stateAssumes s) hAss
        | assume_push A =>
            simpa [__eo_state_proven_nth] using eo_interprets_and_left M A (statePushes s) hPush
        | proven A =>
            simpa [__eo_state_proven_nth] using eo_interprets_and_left M A (stateProvens s) hProv
      ·
        cases so with
        | assume A =>
            have hAssTail : eo_interprets M (stateAssumes s) true :=
              eo_interprets_and_right M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hAssTail hPush hProv
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hAss hPushTail hProv
        | proven A =>
            have hProvTail : eo_interprets M (stateProvens s) true :=
              eo_interprets_and_right M A (stateProvens s) hProv
            simpa [__eo_state_proven_nth, hZero] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hAss hPush hProvTail

theorem checkerTruthInvariant_at (M : SmtModel) {s : CState} :
  checkerTruthInvariant M s ->
  ∀ n : eo_lit_Int,
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M (__eo_state_proven_nth s n) true
:=
by
  intro hs n hAss hPush
  cases s with
  | Stuck =>
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | nil =>
      have hs' : ∀ n : eo_lit_Int,
          eo_interprets M (stateAssumes CState.nil) true ->
          eo_interprets M (statePushes CState.nil) true ->
          eo_interprets M (__eo_state_proven_nth CState.nil n) true := by
        simpa [checkerTruthInvariant] using hs
      exact hs' n hAss hPush
  | cons so s =>
      have hs' : ∀ n : eo_lit_Int,
          eo_interprets M (stateAssumes (CState.cons so s)) true ->
          eo_interprets M (statePushes (CState.cons so s)) true ->
          eo_interprets M (__eo_state_proven_nth (CState.cons so s) n) true := by
        simpa [checkerTruthInvariant] using hs
      exact hs' n hAss hPush

theorem push_assume_preserves_truthInvariant
    (M : SmtModel) (s : CState) (A : Term) :
  checkerTruthInvariant M s ->
  checkerTruthInvariant M (__eo_push_assume A s) :=
by
  intro hs n hAss hPush
  by_cases hZero : n = 0
  · subst hZero
    have hPush' :
        eo_interprets M
          (Term.Apply (Term.Apply Term.and A) (statePushes s)) true := by
      simpa [__eo_push_assume, statePushes] using hPush
    simpa [__eo_push_assume, __eo_state_proven_nth] using
      eo_interprets_and_left M A (statePushes s) hPush'
  · have hAss' : eo_interprets M (stateAssumes s) true := by
      simpa [__eo_push_assume, stateAssumes] using hAss
    have hPush' :
        eo_interprets M
          (Term.Apply (Term.Apply Term.and A) (statePushes s)) true := by
      simpa [__eo_push_assume, statePushes] using hPush
    have hPushTail : eo_interprets M (statePushes s) true :=
      eo_interprets_and_right M A (statePushes s) hPush'
    simpa [__eo_push_assume, __eo_state_proven_nth, hZero] using
      checkerTruthInvariant_at M hs
        (eo_lit_zplus n (eo_lit_zneg 1)) hAss' hPushTail

theorem push_proven_preserves_truthInvariant_of_contextual_true
    (M : SmtModel) (s : CState) (P : Term) :
  checkerTruthInvariant M s ->
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   eo_interprets M P true) ->
  checkerTruthInvariant M (CState.cons (CStateObj.proven P) s) :=
by
  intro hs hP n hAss hPush
  by_cases hZero : n = 0
  · subst hZero
    have hAss' : eo_interprets M (stateAssumes s) true := by
      simpa [stateAssumes] using hAss
    have hPush' : eo_interprets M (statePushes s) true := by
      simpa [statePushes] using hPush
    simpa [__eo_state_proven_nth] using hP hAss' hPush'
  · have hAss' : eo_interprets M (stateAssumes s) true := by
      simpa [stateAssumes] using hAss
    have hPush' : eo_interprets M (statePushes s) true := by
      simpa [statePushes] using hPush
    simpa [__eo_state_proven_nth, hZero] using
      checkerTruthInvariant_at M hs
        (eo_lit_zplus n (eo_lit_zneg 1)) hAss' hPush'

theorem state_proven_nth_not_false_of_conjunctInvariant (M : SmtModel) :
  forall (s : CState) (n : eo_lit_Int),
    checkerConjunctInvariant M s ->
    __eo_state_proven_nth s n ≠ Term.Stuck ->
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    ¬ eo_interprets M (__eo_state_proven_nth s n) false
:=
by
  intro s
  induction s with
  | nil =>
      intro n hInv hNth hAss hPush
      simpa [__eo_state_proven_nth] using
        (eo_interprets_true_not_false M (Term.Boolean true) (eo_interprets_true M))
  | Stuck =>
      intro n hInv hNth hAss hPush
      simpa [__eo_state_proven_nth] using
        (eo_interprets_true_not_false M (Term.Boolean true) (eo_interprets_true M))
  | cons so s ih =>
      intro n hInv hNth hAss hPush
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            have hATrue : eo_interprets M A true := by
              simpa [__eo_state_proven_nth] using
                eo_interprets_and_left M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth] using
              (eo_interprets_true_not_false M A hATrue)
        | assume_push A =>
            have hATrue : eo_interprets M A true := by
              simpa [__eo_state_proven_nth] using
                eo_interprets_and_left M A (statePushes s) hPush
            simpa [__eo_state_proven_nth] using
              (eo_interprets_true_not_false M A hATrue)
        | proven A =>
            simpa [__eo_state_proven_nth, stateAssumes, statePushes] using
              (hInv.1 hAss hPush)
      · have hNthTail :
            __eo_state_proven_nth s (eo_lit_zplus n (eo_lit_zneg 1)) ≠ Term.Stuck := by
          intro hTail
          apply hNth
          simpa [__eo_state_proven_nth, hZero] using hTail
        cases so with
        | assume A =>
            have hAssTail : eo_interprets M (stateAssumes s) true :=
              eo_interprets_and_right M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero, checkerConjunctInvariant] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hInv hNthTail hAssTail hPush
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero, checkerConjunctInvariant] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hInv hNthTail hAss hPushTail
        | proven A =>
            simpa [__eo_state_proven_nth, hZero, checkerConjunctInvariant] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hInv.2 hNthTail hAss hPush

theorem eo_state_to_formula_assume_push (A : Term) (s : CState) :
  eo_state_to_formula (CState.cons (CStateObj.assume_push A) s) =
    Term.Apply (Term.Apply Term.imp (stateAssumes s))
      (Term.Apply (Term.Apply Term.imp
        (Term.Apply (Term.Apply Term.and A) (statePushes s))) (stateProvens s)) :=
by
  cases s <;> simp [eo_state_to_formula, stateAssumes, statePushes, stateProvens]

theorem assume_push_state_to_formula_false_backward (M : SmtModel) (A : Term) (s : CState) :
  eo_interprets M (eo_state_to_formula (CState.cons (CStateObj.assume_push A) s)) false ->
  eo_interprets M (eo_state_to_formula s) false :=
by
  intro h
  cases s with
  | nil =>
      have hOuterTrue :
          eo_interprets M (Term.Boolean true) true :=
        eo_interprets_imp_false_left M (Term.Boolean true)
          (Term.Apply (Term.Apply Term.imp
            (Term.Apply (Term.Apply Term.and A) (Term.Boolean true))) (Term.Boolean true))
          (by simpa [eo_state_to_formula_assume_push, eo_state_to_formula] using h)
      have hInnerFalse :
          eo_interprets M
            (Term.Apply (Term.Apply Term.imp
              (Term.Apply (Term.Apply Term.and A) (Term.Boolean true))) (Term.Boolean true)) false :=
        eo_interprets_imp_false_right M (Term.Boolean true)
          (Term.Apply (Term.Apply Term.imp
            (Term.Apply (Term.Apply Term.and A) (Term.Boolean true))) (Term.Boolean true))
          (by simpa [eo_state_to_formula_assume_push, eo_state_to_formula] using h)
      have hPushTrue :
          eo_interprets M (Term.Boolean true) true :=
        eo_interprets_and_right M A (Term.Boolean true)
          (eo_interprets_imp_false_left M
            (Term.Apply (Term.Apply Term.and A) (Term.Boolean true)) (Term.Boolean true) hInnerFalse)
      have hProvFalse :
          eo_interprets M (Term.Boolean true) false :=
        eo_interprets_imp_false_right M
          (Term.Apply (Term.Apply Term.and A) (Term.Boolean true)) (Term.Boolean true) hInnerFalse
      exact eo_interprets_imp_false_intro M (Term.Boolean true)
        (Term.Apply (Term.Apply Term.imp (Term.Boolean true)) (Term.Boolean true))
        hOuterTrue
        (eo_interprets_imp_false_intro M (Term.Boolean true) (Term.Boolean true) hPushTrue hProvFalse)
  | cons so s =>
      have hOuterTrue :
          eo_interprets M (stateAssumes (CState.cons so s)) true :=
        eo_interprets_imp_false_left M (stateAssumes (CState.cons so s))
          (Term.Apply (Term.Apply Term.imp
            (Term.Apply (Term.Apply Term.and A) (statePushes (CState.cons so s))))
            (stateProvens (CState.cons so s)))
          (by simpa [eo_state_to_formula_assume_push, eo_state_to_formula] using h)
      have hInnerFalse :
          eo_interprets M
            (Term.Apply (Term.Apply Term.imp
              (Term.Apply (Term.Apply Term.and A) (statePushes (CState.cons so s))))
              (stateProvens (CState.cons so s))) false :=
        eo_interprets_imp_false_right M (stateAssumes (CState.cons so s))
          (Term.Apply (Term.Apply Term.imp
            (Term.Apply (Term.Apply Term.and A) (statePushes (CState.cons so s))))
            (stateProvens (CState.cons so s)))
          (by simpa [eo_state_to_formula_assume_push, eo_state_to_formula] using h)
      have hPushTrue :
          eo_interprets M (statePushes (CState.cons so s)) true :=
        eo_interprets_and_right M A (statePushes (CState.cons so s))
          (eo_interprets_imp_false_left M
            (Term.Apply (Term.Apply Term.and A) (statePushes (CState.cons so s)))
            (stateProvens (CState.cons so s)) hInnerFalse)
      have hProvFalse :
          eo_interprets M (stateProvens (CState.cons so s)) false :=
        eo_interprets_imp_false_right M
          (Term.Apply (Term.Apply Term.and A) (statePushes (CState.cons so s)))
          (stateProvens (CState.cons so s)) hInnerFalse
      exact eo_interprets_imp_false_intro M (stateAssumes (CState.cons so s))
        (Term.Apply (Term.Apply Term.imp (statePushes (CState.cons so s)))
          (stateProvens (CState.cons so s))) hOuterTrue
        (eo_interprets_imp_false_intro M (statePushes (CState.cons so s))
          (stateProvens (CState.cons so s)) hPushTrue hProvFalse)
  | Stuck =>
      have : False := by
        rw [eo_interprets_iff_smt_interprets] at h
        cases h with
        | intro_false hty _ =>
            simp [eo_state_to_formula, stateAssumes, statePushes, stateProvens,
              __eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite] at hty
      exact False.elim this

theorem state_to_formula_decompose :
  forall {s : CState}, stateOk s ->
    eo_state_to_formula s =
      Term.Apply (Term.Apply Term.imp (stateAssumes s))
        (Term.Apply (Term.Apply Term.imp (statePushes s)) (stateProvens s))
:=
by
  intro s hOk
  cases s with
  | nil =>
      simp [eo_state_to_formula, stateAssumes, statePushes, stateProvens]
  | cons so s =>
      cases so with
      | assume F =>
          simp [eo_state_to_formula, stateAssumes, statePushes, stateProvens]
      | assume_push F =>
          simp [eo_state_to_formula, stateAssumes, statePushes, stateProvens]
      | proven F =>
          simp [eo_state_to_formula, stateAssumes, statePushes, stateProvens]
  | Stuck =>
      cases hOk

theorem stateAssumptionTail_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateAssumptionTail (__eo_invoke_assume_list CState.nil F)
:=
by
  intro F hValid
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, stateAssumptionTail]
  | step A rest hRest ih =>
      simpa [__eo_invoke_assume_list, stateAssumptionTail] using ih

theorem stateAssumptionSuffix_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateAssumptionSuffix (__eo_invoke_assume_list CState.nil F)
:=
by
  intro F hValid
  exact stateAssumptionSuffix_of_tail (stateAssumptionTail_invoke_assume_list hValid)

theorem stateOk_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateOk (__eo_invoke_assume_list CState.nil F)
:=
by
  intro F hValid
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, stateOk]
  | step A rest hRest ih =>
      simpa [__eo_invoke_assume_list, stateOk] using ih

theorem stateAssumes_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateAssumes (__eo_invoke_assume_list CState.nil F) = F
:=
by
  intro F hValid
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, stateAssumes]
  | step A rest hRest ih =>
      simpa [__eo_invoke_assume_list, stateAssumes] using ih

theorem statePushes_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    statePushes (__eo_invoke_assume_list CState.nil F) = Term.Boolean true
:=
by
  intro F hValid
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, statePushes]
  | step A rest hRest ih =>
      simpa [__eo_invoke_assume_list, statePushes] using ih

theorem stateProvens_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateProvens (__eo_invoke_assume_list CState.nil F) = Term.Boolean true
:=
by
  intro F hValid
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, stateProvens]
  | step A rest hRest ih =>
      simpa [__eo_invoke_assume_list, stateProvens] using ih

theorem checkerTruthInvariant_after_assume_list (M : SmtModel) (F : Term) :
  ValidAssumptionList F ->
  checkerTruthInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hValid
  have hNotStuck :
      __eo_invoke_assume_list CState.nil F ≠ CState.Stuck :=
    stateOk_not_stuck (stateOk_invoke_assume_list hValid)
  have hProvens :
      stateProvens (__eo_invoke_assume_list CState.nil F) = Term.Boolean true :=
    stateProvens_invoke_assume_list hValid
  cases hS : __eo_invoke_assume_list CState.nil F with
  | nil =>
      intro n hAss hPush
      have hProvens' : stateProvens CState.nil = Term.Boolean true := by
        simpa [hS] using hProvens
      have hProv :
          eo_interprets M (stateProvens CState.nil) true := by
        rw [hProvens']
        exact eo_interprets_true M
      exact state_proven_nth_true_of_context M CState.nil n hAss hPush hProv
  | cons so s =>
      intro n hAss hPush
      have hProvens' : stateProvens (CState.cons so s) = Term.Boolean true := by
        simpa [hS] using hProvens
      have hProv :
          eo_interprets M (stateProvens (CState.cons so s)) true := by
        rw [hProvens']
        exact eo_interprets_true M
      exact state_proven_nth_true_of_context M (CState.cons so s) n hAss hPush hProv
  | Stuck =>
      exact False.elim (hNotStuck hS)

theorem checkerStateInvariant_after_assume_list (M : SmtModel) (F : Term) :
  ValidAssumptionList F ->
  checkerStateInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hValid
  exact ⟨
    checkerConjunctInvariant_after_assume_list M F hValid,
    checkerTruthInvariant_after_assume_list M F hValid
  ⟩

theorem state_to_formula_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    eo_state_to_formula (__eo_invoke_assume_list CState.nil F) =
      Term.Apply (Term.Apply Term.imp F)
        (Term.Apply (Term.Apply Term.imp (Term.Boolean true)) (Term.Boolean true))
:=
by
  intro F hValid
  have hAssumes : stateAssumes (__eo_invoke_assume_list CState.nil F) = F :=
    stateAssumes_invoke_assume_list hValid
  have hPushes : statePushes (__eo_invoke_assume_list CState.nil F) = Term.Boolean true :=
    statePushes_invoke_assume_list hValid
  have hProvens : stateProvens (__eo_invoke_assume_list CState.nil F) = Term.Boolean true :=
    stateProvens_invoke_assume_list hValid
  cases hS : __eo_invoke_assume_list CState.nil F with
  | nil =>
      simp [hS, stateAssumes, statePushes, stateProvens] at hAssumes hPushes hProvens
      simpa [hS, eo_state_to_formula, stateAssumes, statePushes, stateProvens, hAssumes, hPushes, hProvens]
  | cons so s =>
      simp [hS, stateAssumes, statePushes, stateProvens] at hAssumes hPushes hProvens
      simpa [hS, eo_state_to_formula, stateAssumes, statePushes, stateProvens, hAssumes, hPushes, hProvens]
  | Stuck =>
      cases hValid with
      | base =>
          simp [__eo_invoke_assume_list] at hS
      | step A rest hRest =>
          simp [__eo_invoke_assume_list] at hS

/- After loading a well-formed assumption list, `state_to_formula` is
   `F => true => true`, so any model of `F` satisfies the invariant. -/
theorem invariant_after_assume_list (M : SmtModel) (F : Term) :
  ValidAssumptionList F ->
  eo_interprets M F true ->
  checkerInvariant M (__eo_invoke_assume_list CState.nil F) :=
by
  intro hValid hF
  have hTT : eo_interprets M
      (Term.Apply (Term.Apply Term.imp (Term.Boolean true)) (Term.Boolean true)) true :=
    eo_interprets_imp_intro M (Term.Boolean true) (Term.Boolean true)
      (eo_interprets_true M) (eo_interprets_true M)
  have hInit : eo_interprets M
      (Term.Apply (Term.Apply Term.imp F)
        (Term.Apply (Term.Apply Term.imp (Term.Boolean true)) (Term.Boolean true))) true :=
    eo_interprets_imp_intro M F
      (Term.Apply (Term.Apply Term.imp (Term.Boolean true)) (Term.Boolean true))
      hF hTT
  unfold checkerInvariant
  simpa [state_to_formula_invoke_assume_list hValid] using
    (eo_interprets_true_not_false M
      (Term.Apply (Term.Apply Term.imp F)
        (Term.Apply (Term.Apply Term.imp (Term.Boolean true)) (Term.Boolean true)))
      hInit)

theorem stateOk_of_state_closed_true :
  forall {s : CState}, __eo_state_is_closed s = true -> stateOk s
:=
by
  intro s hClosed
  induction s with
  | nil =>
      trivial
  | Stuck =>
      cases hClosed
  | cons so s ih =>
      cases so with
      | assume A =>
          exact ih hClosed
      | assume_push A =>
          cases hClosed
      | proven A =>
          exact ih hClosed

theorem statePushes_of_state_closed_true :
  forall {s : CState}, __eo_state_is_closed s = true -> statePushes s = Term.Boolean true
:=
by
  intro s hClosed
  induction s with
  | nil =>
      simp [statePushes]
  | Stuck =>
      cases hClosed
  | cons so s ih =>
      cases so with
      | assume A =>
          simpa [__eo_state_is_closed, statePushes] using ih hClosed
      | assume_push A =>
          cases hClosed
      | proven A =>
          simpa [__eo_state_is_closed, statePushes] using ih hClosed

theorem validAssumptionList_of_stateOk_assume_list :
  forall {F : Term}, stateOk (__eo_invoke_assume_list CState.nil F) -> ValidAssumptionList F
:=
by
  intro F hOk
  cases F with
  | Boolean b =>
      cases b with
      | false =>
          simp [__eo_invoke_assume_list, stateOk] at hOk
      | true =>
          exact ValidAssumptionList.base
  | Apply f a =>
      cases f with
      | Apply g lhs =>
          cases g with
          | and =>
              exact ValidAssumptionList.step lhs a
                (validAssumptionList_of_stateOk_assume_list
                  (by simpa [__eo_invoke_assume_list, stateOk] using hOk))
          | _ =>
              simp [__eo_invoke_assume_list, stateOk] at hOk
      | _ =>
          simp [__eo_invoke_assume_list, stateOk] at hOk
  | _ =>
      simp [__eo_invoke_assume_list, stateOk] at hOk

theorem invoke_cmd_step_pop_of_assumptionTail :
  forall (s cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateAssumptionTail cur ->
    __eo_invoke_cmd_step_pop s cur r args premises = CState.Stuck
:=
by
  intro s cur
  induction cur with
  | nil =>
      intro r args premises hTail
      simp [__eo_invoke_cmd_step_pop]
  | Stuck =>
      intro r args premises hTail
      cases hTail
  | cons so cur ih =>
      intro r args premises hTail
      cases so with
      | assume A =>
          simpa [__eo_invoke_cmd_step_pop, stateAssumptionTail] using
            ih r args premises (by simpa [stateAssumptionTail] using hTail)
      | assume_push A =>
          cases hTail
      | proven A =>
          cases hTail

theorem stateAssumptionSuffix_invoke_cmd_step_pop :
  forall (s cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateAssumptionSuffix cur ->
    stateOk (__eo_invoke_cmd_step_pop s cur r args premises) ->
    stateAssumptionSuffix (__eo_invoke_cmd_step_pop s cur r args premises)
:=
by
  intro s cur
  induction cur with
  | nil =>
      intro r args premises hSuffix hOk
      simp [__eo_invoke_cmd_step_pop, stateOk] at hOk
  | Stuck =>
      intro r args premises hSuffix hOk
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hSuffix hOk
      cases so with
      | assume_push A =>
          cases hStep : eo_lit_teq (__eo_cmd_step_pop_proven s r args A premises) Term.Stuck with
          | false =>
              have hTailSuffix : stateAssumptionSuffix cur := by
                simpa [stateAssumptionSuffix] using hSuffix
              simpa [__eo_invoke_cmd_step_pop, __eo_push_proven, __eo_push_proven_check,
                __eo_is_ok, hStep, SmtEval.smt_lit_not, stateAssumptionSuffix] using hTailSuffix
          | true =>
              simp [__eo_invoke_cmd_step_pop, __eo_push_proven, __eo_push_proven_check,
                __eo_is_ok, hStep, SmtEval.smt_lit_not, stateOk] at hOk
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop s cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail s cur r args premises hTail
          simp [__eo_invoke_cmd_step_pop, hStuck, stateOk] at hOk
      | proven A =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          exact ih r args premises hTailSuffix
            (by simpa [__eo_invoke_cmd_step_pop, stateOk] using hOk)

theorem stateAssumes_invoke_cmd_step_pop :
  forall (s cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateAssumptionSuffix cur ->
    stateOk (__eo_invoke_cmd_step_pop s cur r args premises) ->
    stateAssumes (__eo_invoke_cmd_step_pop s cur r args premises) = stateAssumes cur
:=
by
  intro s cur
  induction cur with
  | nil =>
      intro r args premises hSuffix hOk
      simp [__eo_invoke_cmd_step_pop, stateOk] at hOk
  | Stuck =>
      intro r args premises hSuffix hOk
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hSuffix hOk
      cases so with
      | assume_push A =>
          cases hStep : eo_lit_teq (__eo_cmd_step_pop_proven s r args A premises) Term.Stuck with
          | false =>
              simpa [__eo_invoke_cmd_step_pop, __eo_push_proven, __eo_push_proven_check,
                __eo_is_ok, hStep, SmtEval.smt_lit_not, stateAssumes]
          | true =>
              simp [__eo_invoke_cmd_step_pop, __eo_push_proven, __eo_push_proven_check,
                __eo_is_ok, hStep, SmtEval.smt_lit_not, stateOk] at hOk
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop s cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail s cur r args premises hTail
          simp [__eo_invoke_cmd_step_pop, hStuck, stateOk] at hOk
      | proven A =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          simpa [__eo_invoke_cmd_step_pop, stateAssumes] using
            ih r args premises hTailSuffix (by simpa [__eo_invoke_cmd_step_pop, stateOk] using hOk)

theorem invoke_cmd_step_pop_reflects_stateOk :
  forall (s cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateOk (__eo_invoke_cmd_step_pop s cur r args premises) -> stateOk cur
:=
by
  intro s cur
  induction cur with
  | nil =>
      intro r args premises
      simp [__eo_invoke_cmd_step_pop, stateOk]
  | Stuck =>
      intro r args premises
      simp [__eo_invoke_cmd_step_pop, stateOk]
  | cons so cur ih =>
      intro r args premises
      cases so with
      | assume_push A =>
          intro hOk
          cases hStep : eo_lit_teq (__eo_cmd_step_pop_proven s r args A premises) Term.Stuck with
          | false =>
              simpa [__eo_invoke_cmd_step_pop, __eo_push_proven, __eo_push_proven_check,
                __eo_is_ok, hStep, stateOk] using hOk
          | true =>
              simp [__eo_invoke_cmd_step_pop, __eo_push_proven, __eo_push_proven_check,
                __eo_is_ok, hStep, SmtEval.smt_lit_not] at hOk
              cases hOk
      | assume A =>
          intro hOk
          exact ih r args premises (by simpa [__eo_invoke_cmd_step_pop, stateOk] using hOk)
      | proven A =>
          intro hOk
          exact ih r args premises (by simpa [__eo_invoke_cmd_step_pop, stateOk] using hOk)

theorem invoke_cmd_reflects_stateOk :
  forall (s : CState) (c : CCmd), stateOk (__eo_invoke_cmd s c) -> stateOk s
:=
by
  intro s c
  cases s with
  | nil =>
      cases c <;> simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven,
        __eo_push_proven_check, stateOk]
  | Stuck =>
      simp [__eo_invoke_cmd, stateOk]
  | cons so s =>
      cases c with
      | assume_push A =>
          intro hOk
          simpa [__eo_invoke_cmd, __eo_push_assume, stateOk] using hOk
      | check_proven proven =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk]
          | proven F =>
              intro hOk
              cases hEq : __eo_eq F proven <;>
                simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                  hEq, stateOk] at hOk ⊢
              case Boolean b =>
                cases b with
                | false =>
                    simp [stateOk] at hOk
                | true =>
                    exact hOk
      | step r args premises =>
          intro hOk
          cases hStep : eo_lit_teq (__eo_cmd_step_proven (CState.cons so s) r args premises) Term.Stuck with
          | false =>
              simpa [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, stateOk] using hOk
          | true =>
              simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, SmtEval.smt_lit_not] at hOk
              cases hOk
      | step_pop r args premises =>
          intro hOk
          exact invoke_cmd_step_pop_reflects_stateOk (CState.cons so s) (CState.cons so s)
            r args premises (by simpa [__eo_invoke_cmd] using hOk)

theorem stateAssumptionSuffix_invoke_cmd :
  forall (s : CState) (c : CCmd),
    stateAssumptionSuffix s ->
    stateOk (__eo_invoke_cmd s c) ->
    stateAssumptionSuffix (__eo_invoke_cmd s c)
:=
by
  intro s c
  cases c with
  | assume_push A =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd, __eo_push_assume, stateAssumptionSuffix] using hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd, __eo_push_assume, stateAssumptionSuffix] using hSuffix
      | Stuck =>
          cases hSuffix
  | check_proven proven =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
      | Stuck =>
          cases hSuffix
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                  hEq, stateOk] at hOk
              case Boolean b =>
                cases b with
                | false =>
                    contradiction
                | true =>
                    have hTailSuffix : stateAssumptionSuffix s := by
                      simpa [stateAssumptionSuffix] using hSuffix
                    simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                      hEq] using hTailSuffix
  | step r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          cases hStep : eo_lit_teq (__eo_cmd_step_proven CState.nil r args premises) Term.Stuck with
          | false =>
              simpa [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, SmtEval.smt_lit_not, stateAssumptionSuffix] using hSuffix
          | true =>
              simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, SmtEval.smt_lit_not, stateOk] at hOk
      | Stuck =>
          cases hSuffix
      | cons so s =>
          cases hStep : eo_lit_teq (__eo_cmd_step_proven (CState.cons so s) r args premises) Term.Stuck with
          | false =>
              simpa [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, SmtEval.smt_lit_not, stateAssumptionSuffix] using hSuffix
          | true =>
              simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, SmtEval.smt_lit_not, stateOk] at hOk
  | step_pop r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            stateAssumptionSuffix_invoke_cmd_step_pop CState.nil CState.nil r args premises hSuffix hOk
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            stateAssumptionSuffix_invoke_cmd_step_pop (CState.cons so s) (CState.cons so s) r args premises hSuffix hOk
      | Stuck =>
          cases hSuffix

theorem stateAssumes_invoke_cmd :
  forall (s : CState) (c : CCmd),
    stateAssumptionSuffix s ->
    stateOk (__eo_invoke_cmd s c) ->
    stateAssumes (__eo_invoke_cmd s c) = stateAssumes s
:=
by
  intro s c
  cases c with
  | assume_push A =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_push_assume, stateAssumes]
      | cons so s =>
          simp [__eo_invoke_cmd, __eo_push_assume, stateAssumes]
      | Stuck =>
          cases hSuffix
  | check_proven proven =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
      | Stuck =>
          cases hSuffix
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk] at hOk
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                  hEq, stateOk] at hOk
              case Boolean b =>
                cases b with
                | false =>
                    contradiction
                | true =>
                    simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                      hEq, stateAssumes]
  | step r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          cases hStep : eo_lit_teq (__eo_cmd_step_proven CState.nil r args premises) Term.Stuck with
          | false =>
              simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, SmtEval.smt_lit_not, stateAssumes]
          | true =>
              simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, SmtEval.smt_lit_not, stateOk] at hOk
      | Stuck =>
          cases hSuffix
      | cons so s =>
          cases hStep : eo_lit_teq (__eo_cmd_step_proven (CState.cons so s) r args premises) Term.Stuck with
          | false =>
              simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, SmtEval.smt_lit_not, stateAssumes]
          | true =>
              simp [__eo_invoke_cmd, __eo_push_proven, __eo_push_proven_check, __eo_is_ok,
                hStep, SmtEval.smt_lit_not, stateOk] at hOk
  | step_pop r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            stateAssumes_invoke_cmd_step_pop CState.nil CState.nil r args premises hSuffix hOk
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            stateAssumes_invoke_cmd_step_pop (CState.cons so s) (CState.cons so s) r args premises hSuffix hOk
      | Stuck =>
          cases hSuffix

theorem invoke_cmd_list_reflects_stateOk :
  forall (s : CState) (cs : CCmdList), stateOk (__eo_invoke_cmd_list s cs) -> stateOk s
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      simp [__eo_invoke_cmd_list]
  | cons c cs ih =>
      intro hOk
      have hTail : stateOk (__eo_invoke_cmd s c) := by
        exact ih (__eo_invoke_cmd s c) (by simpa [__eo_invoke_cmd_list] using hOk)
      exact invoke_cmd_reflects_stateOk s c hTail

theorem stateAssumptionSuffix_invoke_cmd_list :
  forall (s : CState) (cs : CCmdList),
    stateAssumptionSuffix s ->
    stateOk (__eo_invoke_cmd_list s cs) ->
    stateAssumptionSuffix (__eo_invoke_cmd_list s cs)
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      intro hSuffix hOk
      simpa [__eo_invoke_cmd_list] using hSuffix
  | cons c cs ih =>
      intro hSuffix hOk
      have hStepOk : stateOk (__eo_invoke_cmd s c) := by
        exact invoke_cmd_list_reflects_stateOk (__eo_invoke_cmd s c) cs
          (by simpa [__eo_invoke_cmd_list] using hOk)
      have hStepSuffix : stateAssumptionSuffix (__eo_invoke_cmd s c) :=
        stateAssumptionSuffix_invoke_cmd s c hSuffix hStepOk
      exact ih (__eo_invoke_cmd s c) hStepSuffix
        (by simpa [__eo_invoke_cmd_list] using hOk)

theorem stateAssumes_invoke_cmd_list :
  forall (s : CState) (cs : CCmdList),
    stateAssumptionSuffix s ->
    stateOk (__eo_invoke_cmd_list s cs) ->
    stateAssumes (__eo_invoke_cmd_list s cs) = stateAssumes s
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      intro hSuffix hOk
      simp [__eo_invoke_cmd_list]
  | cons c cs ih =>
      intro hSuffix hOk
      have hStepOk : stateOk (__eo_invoke_cmd s c) := by
        exact invoke_cmd_list_reflects_stateOk (__eo_invoke_cmd s c) cs
          (by simpa [__eo_invoke_cmd_list] using hOk)
      have hStepSuffix : stateAssumptionSuffix (__eo_invoke_cmd s c) :=
        stateAssumptionSuffix_invoke_cmd s c hSuffix hStepOk
      have hStepAssumes :
          stateAssumes (__eo_invoke_cmd s c) = stateAssumes s :=
        stateAssumes_invoke_cmd s c hSuffix hStepOk
      calc
        stateAssumes (__eo_invoke_cmd_list s (CCmdList.cons c cs))
            = stateAssumes (__eo_invoke_cmd s c) := by
                simpa [__eo_invoke_cmd_list] using
                  ih (__eo_invoke_cmd s c) hStepSuffix
                    (by simpa [__eo_invoke_cmd_list] using hOk)
        _ = stateAssumes s := hStepAssumes

theorem validAssumptionList_of_checker_true (F : Term) (pf : CCmdList) :
  (__eo_checker_is_refutation F pf) = true ->
  ValidAssumptionList F :=
by
  intro hChecker
  let S0 := __eo_invoke_assume_list CState.nil F
  let S1 := __eo_invoke_cmd_list S0 pf
  have hClosed : __eo_state_is_closed (__eo_invoke_cmd_check_proven S1 (Term.Boolean false)) = true := by
    simpa [__eo_checker_is_refutation, __eo_state_is_refutation, S0, S1] using hChecker
  have hCheckedOk : stateOk (__eo_invoke_cmd_check_proven S1 (Term.Boolean false)) :=
    stateOk_of_state_closed_true hClosed
  have hCheckedOk' : stateOk (__eo_invoke_cmd S1 (CCmd.check_proven (Term.Boolean false))) := by
    cases hS1 : S1 <;> simpa [__eo_invoke_cmd, hS1] using hCheckedOk
  have hFinalOk : stateOk S1 :=
    invoke_cmd_reflects_stateOk S1 (CCmd.check_proven (Term.Boolean false))
      hCheckedOk'
  have hInitOk : stateOk S0 := by
    simpa [S1] using invoke_cmd_list_reflects_stateOk S0 pf hFinalOk
  simpa [S0] using validAssumptionList_of_stateOk_assume_list hInitOk

theorem final_stateOk_of_checker_true (F : Term) (pf : CCmdList) :
  (__eo_checker_is_refutation F pf) = true ->
  stateOk (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) :=
by
  intro hChecker
  let S1 := __eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf
  have hClosed : __eo_state_is_closed (__eo_invoke_cmd_check_proven S1 (Term.Boolean false)) = true := by
    simpa [__eo_checker_is_refutation, __eo_state_is_refutation, S1] using hChecker
  have hCheckedOk : stateOk (__eo_invoke_cmd_check_proven S1 (Term.Boolean false)) :=
    stateOk_of_state_closed_true hClosed
  have hCheckedOk' : stateOk (__eo_invoke_cmd S1 (CCmd.check_proven (Term.Boolean false))) := by
    cases hS1 : S1 <;> simpa [__eo_invoke_cmd, hS1] using hCheckedOk
  simpa using invoke_cmd_reflects_stateOk S1 (CCmd.check_proven (Term.Boolean false)) hCheckedOk'

theorem eo_eq_false_true_implies_eq_false (t : Term) :
  __eo_eq t (Term.Boolean false) = Term.Boolean true ->
  t = Term.Boolean false :=
by
  intro hEq
  cases t <;> simp [__eo_eq, eo_lit_teq] at hEq ⊢ <;> assumption

theorem final_state_shape_of_checker_true (F : Term) (pf : CCmdList) :
  (__eo_checker_is_refutation F pf) = true ->
  ∃ s : CState,
    __eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf =
      CState.cons (CStateObj.proven (Term.Boolean false)) s ∧
    __eo_state_is_closed s = true :=
by
  intro hChecker
  let S1 := __eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf
  have hClosed : __eo_state_is_closed (__eo_invoke_cmd_check_proven S1 (Term.Boolean false)) = true := by
    simpa [__eo_checker_is_refutation, __eo_state_is_refutation, S1] using hChecker
  cases hS1 : S1 with
  | nil =>
      simp [S1, hS1, __eo_invoke_cmd_check_proven, __eo_state_is_closed] at hClosed
  | Stuck =>
      simp [S1, hS1, __eo_invoke_cmd_check_proven, __eo_state_is_closed] at hClosed
  | cons so s =>
      cases so with
      | assume A =>
          simp [S1, hS1, __eo_invoke_cmd_check_proven, __eo_state_is_closed] at hClosed
      | assume_push A =>
          simp [S1, hS1, __eo_invoke_cmd_check_proven, __eo_state_is_closed] at hClosed
      | proven P =>
          cases hEq : __eo_eq P (Term.Boolean false) <;>
            simp [S1, hS1, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
              __eo_state_is_closed, hEq] at hClosed
          case Boolean b =>
            cases b with
            | false =>
                contradiction
            | true =>
                have hP : P = Term.Boolean false :=
                  eo_eq_false_true_implies_eq_false P hEq
                subst hP
                exact ⟨s, by simpa [S1, hS1], hClosed⟩

theorem stateAssumes_of_checker_true (F : Term) (pf : CCmdList) :
  (__eo_checker_is_refutation F pf) = true ->
  stateAssumes (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) = F :=
by
  intro hChecker
  let S0 := __eo_invoke_assume_list CState.nil F
  let S1 := __eo_invoke_cmd_list S0 pf
  have hValid : ValidAssumptionList F :=
    validAssumptionList_of_checker_true F pf hChecker
  have hShape0 : stateAssumptionSuffix S0 := by
    simpa [S0] using stateAssumptionSuffix_invoke_assume_list hValid
  have hS1Ok : stateOk S1 := by
    simpa [S1, S0] using final_stateOk_of_checker_true F pf hChecker
  calc
    stateAssumes S1 = stateAssumes S0 := by
      simpa [S1] using stateAssumes_invoke_cmd_list S0 pf hShape0 hS1Ok
    _ = F := by
      simpa [S0] using stateAssumes_invoke_assume_list hValid

theorem refutation_contradiction_of_conjunctInvariant
    (M : SmtModel) (F : Term) (pf : CCmdList) :
  eo_interprets M F true ->
  checkerConjunctInvariant M (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) ->
  (__eo_checker_is_refutation F pf) = true ->
  False :=
by
  intro hF hConj hChecker
  let S1 := __eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf
  rcases final_state_shape_of_checker_true F pf hChecker with ⟨s, hShape, hClosed⟩
  have hAssumes : eo_interprets M (stateAssumes s) true := by
    have hAssumesEq : stateAssumes S1 = F := by
      simpa [S1] using stateAssumes_of_checker_true F pf hChecker
    have hAssumesEqS : stateAssumes s = F := by
      simpa [S1, hShape, stateAssumes] using hAssumesEq
    simpa [hAssumesEqS] using hF
  have hPushes : eo_interprets M (statePushes s) true := by
    have hPushesEq : statePushes s = Term.Boolean true :=
      statePushes_of_state_closed_true hClosed
    simpa [hPushesEq] using eo_interprets_true M
  have hTopNotFalse : ¬ eo_interprets M (Term.Boolean false) false := by
    have hConjHead :
        checkerConjunctInvariant M (CState.cons (CStateObj.proven (Term.Boolean false)) s) := by
      simpa [S1, hShape] using hConj
    exact top_proven_not_false_of_conjunctInvariant M s (Term.Boolean false) hConjHead hAssumes hPushes
  exact hTopNotFalse (eo_interprets_false M)

theorem refutation_contradiction_of_truthInvariant
    (M : SmtModel) (F : Term) (pf : CCmdList) :
  eo_interprets M F true ->
  checkerTruthInvariant M (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) ->
  (__eo_checker_is_refutation F pf) = true ->
  False :=
by
  intro hF hTruth hChecker
  let S1 := __eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf
  rcases final_state_shape_of_checker_true F pf hChecker with ⟨s, hShape, hClosed⟩
  have hAssumes : eo_interprets M (stateAssumes (CState.cons (CStateObj.proven (Term.Boolean false)) s)) true := by
    have hAssumesEq : stateAssumes S1 = F := by
      simpa [S1] using stateAssumes_of_checker_true F pf hChecker
    have hAssumesEqS : stateAssumes s = F := by
      simpa [S1, hShape, stateAssumes] using hAssumesEq
    simpa [stateAssumes, hAssumesEqS] using hF
  have hPushes : eo_interprets M (statePushes (CState.cons (CStateObj.proven (Term.Boolean false)) s)) true := by
    have hPushesEq : statePushes s = Term.Boolean true :=
      statePushes_of_state_closed_true hClosed
    simpa [statePushes, hPushesEq] using eo_interprets_true M
  have hFalseTrue :
      eo_interprets M (Term.Boolean false) true := by
    have hAt := checkerTruthInvariant_at M
      (by simpa [S1, hShape] using hTruth)
      0 hAssumes hPushes
    simpa [__eo_state_proven_nth] using hAt
  exact eo_interprets_false_true_absurd M hFalseTrue

theorem checkerConjunctInvariant_of_eq_stuck (M : SmtModel) {s : CState} :
  s = CState.Stuck -> checkerConjunctInvariant M s :=
by
  intro hStuck
  subst hStuck
  exact checkerConjunctInvariant_stuck M

theorem checkerTruthInvariant_of_eq_stuck (M : SmtModel) {s : CState} :
  s = CState.Stuck -> checkerTruthInvariant M s :=
by
  intro hStuck
  subst hStuck
  exact checkerTruthInvariant_stuck M

theorem invoke_step_preserves_truthInvariant_of_stuck
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  checkerTruthInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hStep
  exact checkerTruthInvariant_of_eq_stuck M
    (invoke_step_eq_stuck_of_nonstuck s hNotStuck r args premises hStep)

theorem invoke_step_preserves_truthInvariant_of_contextual_true
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  checkerTruthInvariant M s ->
  __eo_cmd_step_proven s r args premises = P ->
  P ≠ Term.Stuck ->
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   eo_interprets M P true) ->
  checkerTruthInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hStep hNe hP
  have hPost :
      __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
    invoke_step_eq_cons_of_nonstuck s hNotStuck r args premises P hStep hNe
  simpa [hPost] using
    push_proven_preserves_truthInvariant_of_contextual_true M s P hs hP

/- Central expansion point for plain `step` rules.

   To add a new rule handled by `__eo_cmd_step_proven`, add its matching
   pattern here and invoke the corresponding correctness lemma from
   `Lemmas.lean`. The truth invariant already provides premise truth directly,
   so this checker proof can treat the rules as black boxes. The preservation
   theorems below then pick the new rule up automatically. -/
theorem cmd_step_proven_true_of_truthInvariant
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTruthInvariant M s ->
  __eo_cmd_step_proven s r args premises ≠ Term.Stuck ->
  eo_interprets M (stateAssumes s) true ->
  eo_interprets M (statePushes s) true ->
  eo_interprets M (__eo_cmd_step_proven s r args premises) true
:=
by
  intro hs hProg hAss hPush
  cases r with
  | scope =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | contra =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
          | cons n1 premises =>
              cases premises with
              | nil =>
                  exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
              | cons n2 premises =>
                  cases premises with
                  | nil =>
                      let X1 := __eo_state_proven_nth s n1
                      let X2 := __eo_state_proven_nth s n2
                      let P := __eo_prog_contra (Proof.pf X1) (Proof.pf X2)
                      have hPNotStuck : P ≠ Term.Stuck := by
                        simpa [P, X1, X2, __eo_cmd_step_proven] using hProg
                      have hX1True :
                          eo_interprets M X1 true :=
                        checkerTruthInvariant_at M hs n1 hAss hPush
                      have hX2True :
                          eo_interprets M X2 true :=
                        checkerTruthInvariant_at M hs n2 hAss hPush
                      simpa [P, X1, X2, __eo_cmd_step_proven] using
                        correct___eo_prog_contra M X1 X2 hX1True hX2True hPNotStuck
                  | cons n3 premises =>
                      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons a args =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | refl =>
      cases args with
      | nil =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons a1 args =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  have hPNotStuck : __eo_prog_refl a1 ≠ Term.Stuck := by
                    simpa [__eo_cmd_step_proven] using hProg
                  simpa [__eo_cmd_step_proven] using correct___eo_prog_refl M a1 hPNotStuck
              | cons n ns =>
                  exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
          | cons a2 args =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | symm =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
          | cons n1 premises =>
              cases premises with
              | nil =>
                  let X := __eo_state_proven_nth s n1
                  let P := __eo_prog_symm (Proof.pf X)
                  have hPNotStuck : P ≠ Term.Stuck := by
                    simpa [P, X, __eo_cmd_step_proven] using hProg
                  have hXTrue :
                      eo_interprets M X true :=
                    checkerTruthInvariant_at M hs n1 hAss hPush
                  simpa [P, X, __eo_cmd_step_proven] using
                    correct___eo_prog_symm M X hXTrue hPNotStuck
              | cons n2 premises =>
                  exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons a args =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))

theorem cmd_step_proven_not_false_of_truthInvariant
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTruthInvariant M s ->
  __eo_cmd_step_proven s r args premises ≠ Term.Stuck ->
  eo_interprets M (stateAssumes s) true ->
  eo_interprets M (statePushes s) true ->
  ¬ eo_interprets M (__eo_cmd_step_proven s r args premises) false
:=
by
  intro hs hProg hAss hPush
  exact eo_interprets_true_not_false M _ <|
    cmd_step_proven_true_of_truthInvariant M s hNotStuck r args premises hs hProg hAss hPush

theorem invoke_step_preserves_conjunctInvariant_of_stuck
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  checkerConjunctInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hStep
  exact checkerConjunctInvariant_of_eq_stuck M
    (invoke_step_eq_stuck_of_nonstuck s hNotStuck r args premises hStep)

theorem invoke_step_preserves_conjunctInvariant_of_contextual_not_false
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  checkerConjunctInvariant M s ->
  __eo_cmd_step_proven s r args premises = P ->
  P ≠ Term.Stuck ->
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   ¬ eo_interprets M P false) ->
  checkerConjunctInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hStep hNe hP
  have hPost :
      __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
    invoke_step_eq_cons_of_nonstuck s hNotStuck r args premises P hStep hNe
  simpa [hPost] using push_proven_preserves_conjunctInvariant_of_not_false M s P hs hP

theorem invoke_step_preserves_conjunctInvariant
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerConjunctInvariant M s ->
  checkerTruthInvariant M s ->
  checkerConjunctInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hConj hTruth
  by_cases hProg : __eo_cmd_step_proven s r args premises = Term.Stuck
  · exact invoke_step_preserves_conjunctInvariant_of_stuck M s hNotStuck r args premises hProg
  · exact invoke_step_preserves_conjunctInvariant_of_contextual_not_false M s hNotStuck
      r args premises (__eo_cmd_step_proven s r args premises) hConj rfl hProg
      (fun hAss hPush =>
        cmd_step_proven_not_false_of_truthInvariant M s hNotStuck r args premises
          hTruth hProg hAss hPush)

theorem invoke_step_preserves_truthInvariant
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTruthInvariant M s ->
  checkerTruthInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hTruth
  by_cases hProg : __eo_cmd_step_proven s r args premises = Term.Stuck
  · exact invoke_step_preserves_truthInvariant_of_stuck M s hNotStuck r args premises hProg
  · exact invoke_step_preserves_truthInvariant_of_contextual_true M s hNotStuck
      r args premises (__eo_cmd_step_proven s r args premises) hTruth rfl hProg
      (fun hAss hPush =>
        cmd_step_proven_true_of_truthInvariant M s hNotStuck r args premises
          hTruth hProg hAss hPush)

theorem invoke_cmd_preserves_conjunctInvariant_nonstuck (M : SmtModel) :
  forall s : CState, forall c : CCmd,
    checkerConjunctInvariant M s ->
    checkerTruthInvariant M s ->
    s ≠ CState.Stuck ->
    checkerConjunctInvariant M (__eo_invoke_cmd s c)
:=
by
  intro s c hConj hTruth hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd, __eo_push_assume, checkerConjunctInvariant] using hConj
      | cons so s =>
          simpa [__eo_invoke_cmd, __eo_push_assume, checkerConjunctInvariant] using hConj
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerConjunctInvariant] using
            checkerConjunctInvariant_stuck M
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerConjunctInvariant] using
                checkerConjunctInvariant_stuck M
          | assume_push A =>
              simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerConjunctInvariant] using
                checkerConjunctInvariant_stuck M
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                try
                  (simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                    hEq, checkerConjunctInvariant] using checkerConjunctInvariant_stuck M)
              case Boolean b =>
                cases b with
                | false =>
                    simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                      hEq, checkerConjunctInvariant] using checkerConjunctInvariant_stuck M
                | true =>
                    simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                      hEq, checkerConjunctInvariant] using hConj
  | step r args premises =>
      exact invoke_step_preserves_conjunctInvariant M s hNotStuck r args premises hConj hTruth
  | step_pop r args premises =>
      sorry

theorem invoke_cmd_preserves_truthInvariant_nonstuck (M : SmtModel) :
  forall s : CState, forall c : CCmd,
    checkerTruthInvariant M s ->
    s ≠ CState.Stuck ->
    checkerTruthInvariant M (__eo_invoke_cmd s c)
:=
by
  intro s c hs hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd, __eo_push_assume] using
            push_assume_preserves_truthInvariant M CState.nil A hs
      | cons so s =>
          simpa [__eo_invoke_cmd, __eo_push_assume] using
            push_assume_preserves_truthInvariant M (CState.cons so s) A hs
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTruthInvariant] using
            checkerTruthInvariant_stuck M
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTruthInvariant] using
                checkerTruthInvariant_stuck M
          | assume_push A =>
              simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTruthInvariant] using
                checkerTruthInvariant_stuck M
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                try
                  (simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                    hEq, checkerTruthInvariant] using checkerTruthInvariant_stuck M)
              case Boolean b =>
                cases b with
                | false =>
                    simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                      hEq, checkerTruthInvariant] using checkerTruthInvariant_stuck M
                | true =>
                    simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                      hEq, checkerTruthInvariant] using hs
  | step r args premises =>
      exact invoke_step_preserves_truthInvariant M s hNotStuck r args premises hs
  | step_pop r args premises =>
      sorry

theorem invoke_cmd_preserves_stateInvariant_nonstuck (M : SmtModel) :
  forall s : CState, forall c : CCmd,
    checkerStateInvariant M s ->
    s ≠ CState.Stuck ->
    checkerStateInvariant M (__eo_invoke_cmd s c)
:=
by
  intro s c hs hNotStuck
  exact ⟨
    invoke_cmd_preserves_conjunctInvariant_nonstuck M s c hs.1 hs.2 hNotStuck,
    invoke_cmd_preserves_truthInvariant_nonstuck M s c hs.2 hNotStuck
  ⟩

theorem invoke_cmd_preserves_stateInvariant (M : SmtModel) :
  forall s : CState, forall c : CCmd,
    checkerStateInvariant M s ->
    checkerStateInvariant M (__eo_invoke_cmd s c)
:=
by
  intro s c hs
  by_cases hStuck : s = CState.Stuck
  · subst hStuck
    have hInvStuck : checkerStateInvariant M CState.Stuck := by
      exact ⟨checkerConjunctInvariant_stuck M, checkerTruthInvariant_stuck M⟩
    cases c <;> simpa [__eo_invoke_cmd, checkerStateInvariant] using hInvStuck
  · exact invoke_cmd_preserves_stateInvariant_nonstuck M s c hs hStuck

theorem invoke_cmd_list_preserves_stateInvariant (M : SmtModel) :
  forall s : CState, forall cs : CCmdList,
    checkerStateInvariant M s ->
    checkerStateInvariant M (__eo_invoke_cmd_list s cs)
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      intro hs
      simpa [__eo_invoke_cmd_list] using hs
  | cons c cs ih =>
      intro hs
      have hstep : checkerStateInvariant M (__eo_invoke_cmd s c) :=
        invoke_cmd_preserves_stateInvariant M s c hs
      simpa [__eo_invoke_cmd_list] using ih (__eo_invoke_cmd s c) hstep

/- If the checker reports refutation, the final checked state has top
   proved conjunct `false`. The conjunct invariant rules that out under
   any model of the original assumptions. -/
theorem refutation_contradiction (M : SmtModel) (F : Term) (pf : CCmdList) :
  eo_interprets M F true ->
  checkerConjunctInvariant M (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) ->
  (__eo_checker_is_refutation F pf) = true ->
  False :=
by
  exact refutation_contradiction_of_conjunctInvariant M F pf

/- correctness theorem for the checker -/
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  (eo_is_refutation F pf) ->
  (forall M : SmtModel, ¬ (eo_interprets M F true)) :=
by
  intro hRef M hF
  cases hRef with
  | intro hChecker =>
      let S0 := __eo_invoke_assume_list CState.nil F
      let S1 := __eo_invoke_cmd_list S0 pf
      have hValid : ValidAssumptionList F :=
        validAssumptionList_of_checker_true F pf hChecker
      have hInit : checkerStateInvariant M S0 := by
        simpa [S0] using checkerStateInvariant_after_assume_list M F hValid
      have hSteps : checkerStateInvariant M S1 := by
        simpa [S0, S1] using invoke_cmd_list_preserves_stateInvariant M S0 pf hInit
      exact refutation_contradiction M F pf hF hSteps.1 hChecker
