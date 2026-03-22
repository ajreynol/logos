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

theorem eo_interprets_stuck_false_absurd (M : SmtModel) :
  ¬ eo_interprets M Term.Stuck false :=
by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_false hty _ =>
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
    __eo_state_proven_nth s n ≠ Term.Stuck ->
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M (stateProvens s) true ->
    eo_interprets M (__eo_state_proven_nth s n) true
:=
by
  intro s
  induction s with
  | nil =>
      intro n hNth hAss hPush hProv
      simpa [__eo_state_proven_nth] using eo_interprets_true M
  | Stuck =>
      intro n hNth hAss hPush hProv
      simpa [__eo_state_proven_nth] using eo_interprets_true M
  | cons so s ih =>
      intro n hNth hAss hPush hProv
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth] using eo_interprets_and_left M A (stateAssumes s) hAss
        | assume_push A =>
            simpa [__eo_state_proven_nth] using eo_interprets_and_left M A (statePushes s) hPush
        | proven A =>
            simpa [__eo_state_proven_nth] using eo_interprets_and_left M A (stateProvens s) hProv
        | Stuck =>
            exact False.elim (hNth rfl)
      · have hNthTail :
            __eo_state_proven_nth s (eo_lit_zplus n (eo_lit_zneg 1)) ≠ Term.Stuck := by
          intro hTail
          apply hNth
          simpa [__eo_state_proven_nth, hZero] using hTail
        cases so with
        | assume A =>
            have hAssTail : eo_interprets M (stateAssumes s) true :=
              eo_interprets_and_right M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hNthTail hAssTail hPush hProv
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hNthTail hAss hPushTail hProv
        | proven A =>
            have hProvTail : eo_interprets M (stateProvens s) true :=
              eo_interprets_and_right M A (stateProvens s) hProv
            simpa [__eo_state_proven_nth, hZero] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hNthTail hAss hPush hProvTail
        | Stuck =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (eo_lit_zplus n (eo_lit_zneg 1)) hNthTail hAss hPush hProv

theorem invoke_step_preserves_invariant_symm
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck) (n1 : eo_lit_Int) :
  checkerInvariant M s ->
  checkerInvariant M (__eo_invoke_cmd s (CCmd.step CRule.symm CArgList.nil (CIndexList.cons n1 CIndexList.nil))) :=
by
  intro hs
  unfold checkerInvariant
  intro hPostFalse
  let X := __eo_state_proven_nth s n1
  let P := __eo_prog_symm (Proof.pf X)
  by_cases hPStuck : P = Term.Stuck
  · have hStepStuck :
        __eo_invoke_cmd s (CCmd.step CRule.symm CArgList.nil (CIndexList.cons n1 CIndexList.nil)) =
          CState.Stuck :=
        invoke_step_eq_stuck_of_nonstuck s hNotStuck CRule.symm CArgList.nil
          (CIndexList.cons n1 CIndexList.nil) (by simpa [P, X, __eo_cmd_step_proven] using hPStuck)
    exact eo_interprets_stuck_false_absurd M (by simpa [hStepStuck, eo_state_to_formula] using hPostFalse)
  · have hStepEq :
        __eo_invoke_cmd s (CCmd.step CRule.symm CArgList.nil (CIndexList.cons n1 CIndexList.nil)) =
          CState.cons (CStateObj.proven P) s :=
      invoke_step_eq_cons_of_nonstuck s hNotStuck CRule.symm CArgList.nil
        (CIndexList.cons n1 CIndexList.nil) P
        (by simp [P, X, __eo_cmd_step_proven]) hPStuck
    rcases post_proven_context_true_of_false M s P hs
        (by simpa [hStepEq] using hPostFalse) with
      ⟨hPFalse, hAssumesTrue, hPushesTrue, hProvensTrue⟩
    have hXNotStuck : X ≠ Term.Stuck := by
      intro hX
      apply hPStuck
      simp [P, X, __eo_prog_symm, __mk_symm, hX]
    have hXTrue : eo_interprets M X true :=
      state_proven_nth_true_of_context M s n1 hXNotStuck hAssumesTrue hPushesTrue hProvensTrue
    exact correct___eo_prog_symm M X hXTrue hPFalse

theorem invoke_step_preserves_invariant_contra
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (n1 n2 : eo_lit_Int) :
  checkerInvariant M s ->
  checkerInvariant M (__eo_invoke_cmd s
    (CCmd.step CRule.contra CArgList.nil (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil)))) :=
by
  intro hs
  unfold checkerInvariant
  intro hPostFalse
  let X1 := __eo_state_proven_nth s n1
  let X2 := __eo_state_proven_nth s n2
  let P := __eo_prog_contra (Proof.pf X1) (Proof.pf X2)
  by_cases hPStuck : P = Term.Stuck
  · have hStepStuck :
        __eo_invoke_cmd s
          (CCmd.step CRule.contra CArgList.nil (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil))) =
            CState.Stuck :=
        invoke_step_eq_stuck_of_nonstuck s hNotStuck CRule.contra CArgList.nil
          (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil))
          (by simpa [P, X1, X2, __eo_cmd_step_proven] using hPStuck)
    exact eo_interprets_stuck_false_absurd M (by simpa [hStepStuck, eo_state_to_formula] using hPostFalse)
  · have hStepEq :
        __eo_invoke_cmd s
          (CCmd.step CRule.contra CArgList.nil (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil))) =
            CState.cons (CStateObj.proven P) s :=
      invoke_step_eq_cons_of_nonstuck s hNotStuck CRule.contra CArgList.nil
        (CIndexList.cons n1 (CIndexList.cons n2 CIndexList.nil)) P
        (by simp [P, X1, X2, __eo_cmd_step_proven]) hPStuck
    rcases post_proven_context_true_of_false M s P hs
        (by simpa [hStepEq] using hPostFalse) with
      ⟨hPFalse, hAssumesTrue, hPushesTrue, hProvensTrue⟩
    have hX1NotStuck : X1 ≠ Term.Stuck := by
      intro hX1
      apply hPStuck
      cases hX2 : X2 with
      | Apply f a =>
          cases f <;>
            simpa [P, X1, X2, __eo_prog_contra, __eo_requires, __eo_eq, eo_lit_teq, eo_lit_ite,
              hX1, hX2]
      | _ =>
          simpa [P, X1, X2, __eo_prog_contra, __eo_requires, __eo_eq, eo_lit_teq, eo_lit_ite,
            hX1, hX2]
    have hX2NotStuck : X2 ≠ Term.Stuck := by
      intro hX2
      apply hPStuck
      simp [P, X1, X2, __eo_prog_contra, __eo_requires, __eo_eq, hX2]
    have hX1True : eo_interprets M X1 true :=
      state_proven_nth_true_of_context M s n1 hX1NotStuck hAssumesTrue hPushesTrue hProvensTrue
    have hX2True : eo_interprets M X2 true :=
      state_proven_nth_true_of_context M s n2 hX2NotStuck hAssumesTrue hPushesTrue hProvensTrue
    exact correct___eo_prog_contra M X1 X2 hX1True hX2True hPFalse

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
  forall {s : CState}, stateFormulaOk s ->
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
  | Stuck =>
      cases hOk

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
theorem invoke_cmd_preserves_invariant_nonstuck (M : SmtModel) :
  forall s : CState, forall c : CCmd,
    checkerInvariant M s -> s ≠ CState.Stuck -> checkerInvariant M (__eo_invoke_cmd s c)
:=
by
  intro s c hs hNotStuck
  cases c with
  | assume_push A =>
      unfold checkerInvariant at hs ⊢
      cases s with
      | nil =>
          intro hFalse
          have hOldFalse :
              eo_interprets M (eo_state_to_formula CState.nil) false :=
            assume_push_state_to_formula_false_backward M A CState.nil
              (by simpa [__eo_invoke_cmd, __eo_push_assume, eo_state_to_formula_assume_push] using hFalse)
          exact hs hOldFalse
      | cons so s =>
          intro hFalse
          have hOldFalse :
              eo_interprets M (eo_state_to_formula (CState.cons so s)) false :=
            assume_push_state_to_formula_false_backward M A (CState.cons so s)
              (by simpa [__eo_invoke_cmd, __eo_push_assume, eo_state_to_formula_assume_push] using hFalse)
          exact hs hOldFalse
      | Stuck =>
          simpa [__eo_invoke_cmd, checkerInvariant, eo_state_to_formula] using
            eo_interprets_stuck_false_absurd M
  | check_proven proven =>
      unfold checkerInvariant at hs ⊢
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, eo_state_to_formula] using
            eo_interprets_stuck_false_absurd M
      | Stuck =>
          simpa [__eo_invoke_cmd, eo_state_to_formula] using
            eo_interprets_stuck_false_absurd M
      | cons so s =>
          cases so with
          | assume A =>
              simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, eo_state_to_formula] using
                eo_interprets_stuck_false_absurd M
          | assume_push A =>
              simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, eo_state_to_formula] using
                eo_interprets_stuck_false_absurd M
          | Stuck =>
              simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, eo_state_to_formula] using
                eo_interprets_stuck_false_absurd M
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                try
                  (simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                    hEq, checkerInvariant, eo_state_to_formula] using
                    eo_interprets_stuck_false_absurd M)
              case Boolean b =>
                cases b with
                | false =>
                    simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                      hEq, checkerInvariant, eo_state_to_formula] using
                      eo_interprets_stuck_false_absurd M
                | true =>
                    simpa [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, __eo_push_proven_check,
                      hEq, checkerInvariant] using hs
  | step r args premises =>
      cases r with
      | scope =>
          exact invoke_step_preserves_invariant_of_stuck M s hNotStuck CRule.scope args premises
            (by simp [__eo_cmd_step_proven])
      | contra =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                    CRule.contra CArgList.nil CIndexList.nil
                    (by simp [__eo_cmd_step_proven])
              | cons n1 premises =>
                  cases premises with
                  | nil =>
                      exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                        CRule.contra CArgList.nil (CIndexList.cons n1 CIndexList.nil)
                        (by simp [__eo_cmd_step_proven])
                  | cons n2 premises =>
                      cases premises with
                      | nil =>
                          exact invoke_step_preserves_invariant_contra M s hNotStuck n1 n2 hs
                      | cons n3 premises =>
                          exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                            CRule.contra CArgList.nil
                            (CIndexList.cons n1 (CIndexList.cons n2 (CIndexList.cons n3 premises)))
                            (by simp [__eo_cmd_step_proven])
          | cons a args =>
              exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                CRule.contra (CArgList.cons a args) premises
                (by simp [__eo_cmd_step_proven])
      | refl =>
          cases args with
          | nil =>
              exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                CRule.refl CArgList.nil premises
                (by simp [__eo_cmd_step_proven])
          | cons a1 args =>
              cases args with
              | nil =>
                  cases premises with
                  | nil =>
                      cases hStep : eo_lit_teq (__eo_prog_refl a1) Term.Stuck with
                      | true =>
                          have hEq : __eo_prog_refl a1 = Term.Stuck := by
                            simpa [eo_lit_teq] using hStep
                          exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                            CRule.refl (CArgList.cons a1 CArgList.nil) CIndexList.nil
                            (by simp [__eo_cmd_step_proven, hEq])
                      | false =>
                          have hNe : __eo_prog_refl a1 ≠ Term.Stuck := by
                            simpa [eo_lit_teq] using hStep
                          exact invoke_step_preserves_invariant_of_not_false M s hNotStuck
                            CRule.refl (CArgList.cons a1 CArgList.nil) CIndexList.nil
                            (__eo_prog_refl a1) hs
                            (by simp [__eo_cmd_step_proven]) hNe (correct___eo_prog_refl M a1)
                  | cons n ns =>
                      exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                        CRule.refl (CArgList.cons a1 CArgList.nil) (CIndexList.cons n ns)
                        (by simp [__eo_cmd_step_proven])
              | cons a2 args =>
                  exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                    CRule.refl (CArgList.cons a1 (CArgList.cons a2 args)) premises
                    (by simp [__eo_cmd_step_proven])
      | symm =>
          cases args with
          | nil =>
              cases premises with
              | nil =>
                  exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                    CRule.symm CArgList.nil CIndexList.nil
                    (by simp [__eo_cmd_step_proven])
              | cons n1 premises =>
                  cases premises with
                  | nil =>
                      exact invoke_step_preserves_invariant_symm M s hNotStuck n1 hs
                  | cons n2 premises =>
                      exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                        CRule.symm CArgList.nil (CIndexList.cons n1 (CIndexList.cons n2 premises))
                        (by simp [__eo_cmd_step_proven])
          | cons a args =>
              exact invoke_step_preserves_invariant_of_stuck M s hNotStuck
                CRule.symm (CArgList.cons a args) premises
                (by simp [__eo_cmd_step_proven])
  | step_pop r args premises =>
      sorry

theorem invoke_cmd_preserves_invariant (M : SmtModel) :
  forall s : CState, forall c : CCmd,
    checkerInvariant M s -> checkerInvariant M (__eo_invoke_cmd s c)
:=
by
  intro s c hs
  by_cases hStuck : s = CState.Stuck
  · subst hStuck
    cases c <;> simpa [__eo_invoke_cmd, checkerInvariant, eo_state_to_formula] using
      checkerInvariant_stuck M
  · exact invoke_cmd_preserves_invariant_nonstuck M s c hs hStuck

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
