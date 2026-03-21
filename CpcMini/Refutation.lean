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

def stateFormulaOk : CState -> Prop
  | CState.nil => True
  | CState.cons CStateObj.Stuck _ => False
  | CState.cons _ s => stateFormulaOk s
  | CState.Stuck => False

def checkerInvariant (M : SmtModel) (s : CState) : Prop :=
  eo_interprets M (__eo_lem_state_to_formula s) true

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

theorem eo_interprets_false_true_absurd (M : SmtModel) :
  ¬ eo_interprets M (Term.Boolean false) true :=
by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true _ hEval =>
      cases hEval

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

theorem state_to_formula_decompose :
  forall {s : CState}, stateFormulaOk s ->
    __eo_lem_state_to_formula s =
      Term.Apply (Term.Apply Term.imp (stateAssumes s))
        (Term.Apply (Term.Apply Term.imp (statePushes s)) (stateProvens s))
:=
by
  intro s hOk
  induction s with
  | nil =>
      simp [__eo_lem_state_to_formula, __eo_lem_state_to_formula_rec, stateAssumes, statePushes, stateProvens]
  | Stuck =>
      cases hOk
  | cons so s ih =>
      cases so with
      | assume F =>
          unfold __eo_lem_state_to_formula at ih ⊢
          simpa [__eo_lem_state_to_formula_rec, __eo_lem_state_to_formula_step,
            stateAssumes, statePushes, stateProvens] using
            congrArg (__eo_lem_state_to_formula_step (CStateObj.assume F)) (ih hOk)
      | assume_push F =>
          unfold __eo_lem_state_to_formula at ih ⊢
          simpa [__eo_lem_state_to_formula_rec, __eo_lem_state_to_formula_step,
            stateAssumes, statePushes, stateProvens] using
            congrArg (__eo_lem_state_to_formula_step (CStateObj.assume_push F)) (ih hOk)
      | proven F =>
          unfold __eo_lem_state_to_formula at ih ⊢
          simpa [__eo_lem_state_to_formula_rec, __eo_lem_state_to_formula_step,
            stateAssumes, statePushes, stateProvens] using
            congrArg (__eo_lem_state_to_formula_step (CStateObj.proven F)) (ih hOk)
      | Stuck =>
          cases hOk

theorem state_to_formula_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    __eo_lem_state_to_formula (__eo_invoke_assume_list CState.nil F) =
      Term.Apply (Term.Apply Term.imp F)
        (Term.Apply (Term.Apply Term.imp (Term.Boolean true)) (Term.Boolean true))
:=
by
  intro F hValid
  induction hValid with
  | base =>
      simp [__eo_lem_state_to_formula, __eo_lem_state_to_formula_rec, __eo_invoke_assume_list]
  | step A rest hRest ih =>
      unfold __eo_lem_state_to_formula at ih ⊢
      simpa [__eo_invoke_assume_list, __eo_lem_state_to_formula_rec, __eo_lem_state_to_formula_step] using
        congrArg (__eo_lem_state_to_formula_step (CStateObj.assume A)) ih

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
  simpa [checkerInvariant, state_to_formula_invoke_assume_list hValid] using hInit

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
      | Stuck =>
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
      | Stuck =>
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
      | Stuck =>
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
          | Stuck =>
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

/- One checker step preserves the state-to-formula invariant.
   The structural commands are straightforward; the `step` and `step_pop`
   cases should appeal to the rule-correctness theorems from `Lemmas.lean`
   after extracting the relevant premises from the old invariant. -/
theorem invoke_cmd_preserves_invariant (M : SmtModel) :
  forall s : CState, forall c : CCmd,
    checkerInvariant M s -> checkerInvariant M (__eo_invoke_cmd s c)
:=
by
  intro s c hs
  cases c with
  | assume_push A =>
      sorry
  | check_proven proven =>
      sorry
  | step r args premises =>
      sorry
  | step_pop r args premises =>
      sorry

theorem invoke_cmd_list_preserves_invariant (M : SmtModel) :
  forall s : CState, forall cs : CCmdList,
    checkerInvariant M s -> checkerInvariant M (__eo_invoke_cmd_list s cs)
:=
by
  intro s cs
  induction cs generalizing s with
  | nil =>
      intro hs
      simpa [__eo_invoke_cmd_list] using hs
  | cons c cs ih =>
      intro hs
      have hstep : checkerInvariant M (__eo_invoke_cmd s c) :=
        invoke_cmd_preserves_invariant M s c hs
      simpa [__eo_invoke_cmd_list] using ih (__eo_invoke_cmd s c) hstep

/- If the checker reports refutation, then checking the final proved `false`
   yields a closed state whose `state_to_formula` has the shape
   `F => true => (false ^ G)`. Together with a model of `F` and the invariant,
   this is impossible. -/
theorem refutation_contradiction (M : SmtModel) (F : Term) (pf : CCmdList) :
  eo_interprets M F true ->
  checkerInvariant M (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) ->
  (__eo_checker_is_refutation F pf) = true ->
  False :=
by
  sorry

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
      have hInit : checkerInvariant M S0 := by
        simpa [S0] using invariant_after_assume_list M F hValid hF
      have hSteps : checkerInvariant M S1 := by
        simpa [S0, S1] using invoke_cmd_list_preserves_invariant M S0 pf hInit
      exact refutation_contradiction M F pf hF hSteps hChecker
