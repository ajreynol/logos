import CpcMini.Spec
import CpcMini.Proofs.RuleLemmas

open Eo
open Smtm

inductive ValidAssumptionList : Term -> Prop
  | base : ValidAssumptionList (Term.Boolean true)
  | step (A rest : Term) : ValidAssumptionList rest ->
      ValidAssumptionList (Term.Apply (Term.Apply Term.and A) rest)

inductive TypedAssumptionList : Term -> Prop
  | base : TypedAssumptionList (Term.Boolean true)
  | step (A rest : Term) :
      A ≠ Term.Stuck ->
      __eo_typeof A = Term.Bool ->
      TypedAssumptionList rest ->
      TypedAssumptionList (Term.Apply (Term.Apply Term.and A) rest)

inductive TranslatableAssumptionList : Term -> Prop
  | base : TranslatableAssumptionList (Term.Boolean true)
  | step (A rest : Term) :
      RuleProofs.eo_has_smt_translation A ->
      TranslatableAssumptionList rest ->
      TranslatableAssumptionList (Term.Apply (Term.Apply Term.and A) rest)

def cmdTranslationOk : CCmd -> Prop
  | CCmd.assume_push A => RuleProofs.eo_has_smt_translation A
  | CCmd.step CRule.refl (CArgList.cons a1 CArgList.nil) CIndexList.nil =>
      RuleProofs.eo_has_smt_translation a1
  | _ => True

inductive CmdListTranslationOk : CCmdList -> Prop
  | nil : CmdListTranslationOk CCmdList.nil
  | cons (c : CCmd) (cs : CCmdList) :
      cmdTranslationOk c ->
      CmdListTranslationOk cs ->
      CmdListTranslationOk (CCmdList.cons c cs)

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
          simp
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
          simp
      exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

theorem eo_interprets_and_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) true :=
by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · simp [__eo_to_smt, __smtx_typeof, htyA, htyB, smt_lit_Teq, smt_lit_ite]
          · simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_and, hEvalA, hEvalB,
              SmtEval.smt_lit_and]

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
              simp
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
          simp
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
          simp
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
            simp
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
                  simp
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
  simp [stateOk] at hOk

@[simp] theorem eo_eq_bool_true_iff (t : Term) :
  __eo_eq t Term.Bool = Term.Boolean true ↔ t = Term.Bool :=
by
  cases t <;> simp [__eo_eq, eo_lit_teq]

theorem typeof_stuck_ne_bool :
  __eo_typeof Term.Stuck ≠ Term.Bool :=
by
  native_decide

@[simp] theorem eo_is_bool_type_eq_true_iff (t : Term) :
  __eo_is_bool_type t = Term.Boolean true ↔ __eo_typeof t = Term.Bool :=
by
  by_cases hStuck : t = Term.Stuck
  · subst hStuck
    constructor
    · simp [__eo_is_bool_type]
    · exact False.elim ∘ typeof_stuck_ne_bool
  · simp [__eo_is_bool_type, eo_eq_bool_true_iff]

@[simp] theorem eo_is_bool_type_eq_true_of_typeof_bool (t : Term) :
  __eo_typeof t = Term.Bool ->
  __eo_is_bool_type t = Term.Boolean true :=
by
  intro hTy
  exact (eo_is_bool_type_eq_true_iff t).2 hTy

theorem term_ne_stuck_of_typeof_bool (t : Term) :
  __eo_typeof t = Term.Bool ->
  t ≠ Term.Stuck :=
by
  intro hTy hStuck
  subst hStuck
  exact False.elim (typeof_stuck_ne_bool hTy)

@[simp] theorem push_assume_eq_cons_of_typeof_bool (A : Term) (s : CState) :
  __eo_typeof A = Term.Bool ->
  __eo_push_assume A s = CState.cons (CStateObj.assume_push A) s :=
by
  intro hTy
  simp [__eo_push_assume, __eo_push_assume_check,
    eo_is_bool_type_eq_true_of_typeof_bool, hTy]

@[simp] theorem push_assume_eq_stuck_of_eq_stuck (s : CState) :
  __eo_push_assume Term.Stuck s = CState.Stuck :=
by
  simp [__eo_push_assume, __eo_push_assume_check, __eo_is_bool_type]

@[simp] theorem push_assume_eq_stuck_of_typeof_ne_bool (A : Term) (s : CState) :
  __eo_typeof A ≠ Term.Bool ->
  __eo_push_assume A s = CState.Stuck :=
by
  intro hTy
  have hBool : __eo_is_bool_type A ≠ Term.Boolean true := by
    intro h
    exact hTy ((eo_is_bool_type_eq_true_iff A).1 h)
  cases hCheck : __eo_is_bool_type A <;> simp [__eo_push_assume, __eo_push_assume_check, hCheck]
  case Boolean b =>
    cases b <;> simp [hCheck] at hBool ⊢

theorem assume_push_arg_ne_stuck_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume A s) -> A ≠ Term.Stuck :=
by
  intro hOk hA
  subst hA
  simp [push_assume_eq_stuck_of_eq_stuck, stateOk] at hOk

theorem push_assume_reflects_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume A s) -> stateOk s :=
by
  intro hOk
  have hTy : __eo_typeof A = Term.Bool := by
    have hBool : __eo_is_bool_type A = Term.Boolean true := by
      cases hCheck : __eo_is_bool_type A <;> simp [__eo_push_assume, __eo_push_assume_check, hCheck, stateOk] at hOk
      case Boolean b =>
        cases b <;> simp [stateOk] at hOk
        simp
    exact (eo_is_bool_type_eq_true_iff A).1 hBool
  simpa [push_assume_eq_cons_of_typeof_bool, hTy, stateOk] using hOk

theorem push_assume_typeof_bool_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume A s) -> __eo_typeof A = Term.Bool :=
by
  intro hOk
  have hBool : __eo_is_bool_type A = Term.Boolean true := by
    cases hCheck : __eo_is_bool_type A <;>
      simp [__eo_push_assume, __eo_push_assume_check, hCheck, stateOk] at hOk
    case Boolean b =>
      cases b <;> simp [stateOk] at hOk
      simp
  exact (eo_is_bool_type_eq_true_iff A).1 hBool

theorem push_assume_eq_cons_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume A s) ->
  __eo_push_assume A s = CState.cons (CStateObj.assume_push A) s :=
by
  intro hOk
  exact push_assume_eq_cons_of_typeof_bool A s (push_assume_typeof_bool_of_stateOk A s hOk)

@[simp] theorem push_proven_eq_cons_of_typeof_bool (P : Term) (s : CState) :
  __eo_typeof P = Term.Bool ->
  __eo_push_proven P s = CState.cons (CStateObj.proven P) s :=
by
  intro hTy
  simp [__eo_push_proven, __eo_push_proven_check,
    eo_is_bool_type_eq_true_of_typeof_bool, hTy]

@[simp] theorem push_proven_eq_stuck_of_eq_stuck (s : CState) :
  __eo_push_proven Term.Stuck s = CState.Stuck :=
by
  simp [__eo_push_proven, __eo_push_proven_check, __eo_is_bool_type]

@[simp] theorem push_proven_eq_stuck_of_typeof_ne_bool (P : Term) (s : CState) :
  __eo_typeof P ≠ Term.Bool ->
  __eo_push_proven P s = CState.Stuck :=
by
  intro hTy
  have hBool : __eo_is_bool_type P ≠ Term.Boolean true := by
    intro h
    exact hTy ((eo_is_bool_type_eq_true_iff P).1 h)
  cases hCheck : __eo_is_bool_type P <;> simp [__eo_push_proven, __eo_push_proven_check, hCheck]
  case Boolean b =>
    cases b <;> simp [hCheck] at hBool ⊢

theorem push_proven_typeof_bool_of_stateOk (P : Term) (s : CState) :
  stateOk (__eo_push_proven P s) -> __eo_typeof P = Term.Bool :=
by
  intro hOk
  have hBool : __eo_is_bool_type P = Term.Boolean true := by
    cases hCheck : __eo_is_bool_type P <;>
      simp [__eo_push_proven, __eo_push_proven_check, hCheck, stateOk] at hOk
    case Boolean b =>
      cases b <;> simp [stateOk] at hOk
      simp
  exact (eo_is_bool_type_eq_true_iff P).1 hBool

theorem push_proven_eq_cons_of_stateOk (P : Term) (s : CState) :
  stateOk (__eo_push_proven P s) ->
  __eo_push_proven P s = CState.cons (CStateObj.proven P) s :=
by
  intro hOk
  exact push_proven_eq_cons_of_typeof_bool P s (push_proven_typeof_bool_of_stateOk P s hOk)

theorem push_proven_reflects_stateOk (P : Term) (s : CState) :
  stateOk (__eo_push_proven P s) -> stateOk s :=
by
  intro hOk
  have hTy := push_proven_typeof_bool_of_stateOk P s hOk
  simpa [push_proven_eq_cons_of_typeof_bool, hTy, stateOk] using hOk

@[simp] theorem invoke_cmd_check_proven_proven_eq_push_proven_check
    (F proven : Term) (s : CState) :
  __eo_invoke_cmd_check_proven (CState.cons (CStateObj.proven F) s) proven =
    __eo_push_proven_check (__eo_eq F proven) F s :=
by
  rw [__eo_invoke_cmd_check_proven]

@[simp] theorem invoke_cmd_check_proven_proven_eq_push_proven_check_cmd
    (F proven : Term) (s : CState) :
  __eo_invoke_cmd (CState.cons (CStateObj.proven F) s) (CCmd.check_proven proven) =
    __eo_push_proven_check (__eo_eq F proven) F s :=
by
  simp [__eo_invoke_cmd]

/- Indexed truth invariant: under globally true assumptions and local pushes,
   every indexed state entry is true. Since `CStateObj.Stuck` has been
   removed, indexed lookup can be handled directly from the semantic context,
   without extra per-rule premise side lemmas. -/
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

/- Structural checker-side typing invariant.

   Every state entry recorded by the checker carries a checker-side Bool guard.
   This matches the operational checks for `assume_push` / `push_proven`, and
   for initial assumptions we thread a separate `TypedAssumptionList` premise.
-/
def checkerTypeInvariant : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume A) s =>
      A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool ∧ checkerTypeInvariant s
  | CState.cons (CStateObj.assume_push A) s =>
      A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool ∧ checkerTypeInvariant s
  | CState.cons (CStateObj.proven P) s =>
      P ≠ Term.Stuck ∧ __eo_typeof P = Term.Bool ∧ checkerTypeInvariant s
  | CState.Stuck => True

theorem checkerTypeInvariant_stuck :
  checkerTypeInvariant CState.Stuck :=
by
  trivial

def checkerTranslationInvariant : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume A) s =>
      RuleProofs.eo_has_smt_translation A ∧ checkerTranslationInvariant s
  | CState.cons (CStateObj.assume_push A) s =>
      RuleProofs.eo_has_smt_translation A ∧ checkerTranslationInvariant s
  | CState.cons (CStateObj.proven P) s =>
      RuleProofs.eo_has_smt_translation P ∧ checkerTranslationInvariant s
  | CState.Stuck => True

theorem checkerTranslationInvariant_stuck :
  checkerTranslationInvariant CState.Stuck :=
by
  trivial

/- Local recursive truth invariant.

   A proved formula is stored together with the tail state whose assumptions
   and local pushes form the context in which that proof is valid. This is the
   invariant shape that matches `step_pop`, since popping a local assumption
   keeps the tail unchanged and only replaces the scoped prefix by one new
   proved implication. -/
def checkerLocalTruthInvariant (M : SmtModel) : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.proven P) s =>
      (eo_interprets M (stateAssumes s) true ->
       eo_interprets M (statePushes s) true ->
       eo_interprets M P true) ∧
      checkerLocalTruthInvariant M s
  | CState.cons _ s => checkerLocalTruthInvariant M s
  | CState.Stuck => True

theorem checkerLocalTruthInvariant_stuck (M : SmtModel) :
  checkerLocalTruthInvariant M CState.Stuck :=
by
  trivial

theorem checkerTypeInvariant_tail :
  forall {so : CStateObj} {s : CState},
    checkerTypeInvariant (CState.cons so s) ->
    checkerTypeInvariant s
:=
by
  intro so s hs
  cases so with
  | assume A =>
      exact hs.2.2
  | assume_push A =>
      exact hs.2.2
  | proven P =>
      exact hs.2.2

theorem checkerTypeInvariant_head_assume
    (A : Term) (s : CState) :
  checkerTypeInvariant (CState.cons (CStateObj.assume A) s) ->
  A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool :=
by
  intro hs
  exact ⟨hs.1, hs.2.1⟩

theorem checkerTypeInvariant_head_assume_push
    (A : Term) (s : CState) :
  checkerTypeInvariant (CState.cons (CStateObj.assume_push A) s) ->
  A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool :=
by
  intro hs
  exact ⟨hs.1, hs.2.1⟩

theorem checkerTypeInvariant_head_proven
    (P : Term) (s : CState) :
  checkerTypeInvariant (CState.cons (CStateObj.proven P) s) ->
  P ≠ Term.Stuck ∧ __eo_typeof P = Term.Bool :=
by
  intro hs
  exact ⟨hs.1, hs.2.1⟩

theorem checkerTypeInvariant_at :
  forall {s : CState},
    checkerTypeInvariant s ->
    forall n : eo_lit_Int,
      __eo_state_proven_nth s n ≠ Term.Stuck ∧
      __eo_typeof (__eo_state_proven_nth s n) = Term.Bool
:=
by
  intro s hs
  induction s with
  | nil =>
      intro n
      constructor
      · simp [__eo_state_proven_nth]
      · change __eo_typeof (Term.Boolean true) = Term.Bool
        native_decide
  | Stuck =>
      intro n
      constructor
      · simp [__eo_state_proven_nth]
      · change __eo_typeof (Term.Boolean true) = Term.Bool
        native_decide
  | cons so s ih =>
      intro n
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth] using checkerTypeInvariant_head_assume A s hs
        | assume_push A =>
            simpa [__eo_state_proven_nth] using checkerTypeInvariant_head_assume_push A s hs
        | proven P =>
            simpa [__eo_state_proven_nth] using checkerTypeInvariant_head_proven P s hs
      · cases so with
        | assume A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTypeInvariant_tail hs) (eo_lit_zplus n (eo_lit_zneg 1))
        | assume_push A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTypeInvariant_tail hs) (eo_lit_zplus n (eo_lit_zneg 1))
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTypeInvariant_tail hs) (eo_lit_zplus n (eo_lit_zneg 1))

theorem checkerTranslationInvariant_tail :
  forall {so : CStateObj} {s : CState},
    checkerTranslationInvariant (CState.cons so s) ->
    checkerTranslationInvariant s
:=
by
  intro so s hs
  cases so <;> exact hs.2

theorem checkerTranslationInvariant_head_assume
    (A : Term) (s : CState) :
  checkerTranslationInvariant (CState.cons (CStateObj.assume A) s) ->
  RuleProofs.eo_has_smt_translation A :=
by
  intro hs
  exact hs.1

theorem checkerTranslationInvariant_head_assume_push
    (A : Term) (s : CState) :
  checkerTranslationInvariant (CState.cons (CStateObj.assume_push A) s) ->
  RuleProofs.eo_has_smt_translation A :=
by
  intro hs
  exact hs.1

theorem checkerTranslationInvariant_head_proven
    (P : Term) (s : CState) :
  checkerTranslationInvariant (CState.cons (CStateObj.proven P) s) ->
  RuleProofs.eo_has_smt_translation P :=
by
  intro hs
  exact hs.1

theorem checkerTranslationInvariant_at :
  forall {s : CState},
    checkerTranslationInvariant s ->
    forall n : eo_lit_Int,
      RuleProofs.eo_has_smt_translation (__eo_state_proven_nth s n)
:=
by
  intro s hs
  induction s with
  | nil =>
      intro n
      simp [__eo_state_proven_nth, RuleProofs.eo_has_smt_translation, __eo_to_smt, __smtx_typeof]
  | Stuck =>
      intro n
      simp [__eo_state_proven_nth, RuleProofs.eo_has_smt_translation, __eo_to_smt, __smtx_typeof]
  | cons so s ih =>
      intro n
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth] using checkerTranslationInvariant_head_assume A s hs
        | assume_push A =>
            simpa [__eo_state_proven_nth] using checkerTranslationInvariant_head_assume_push A s hs
        | proven P =>
            simpa [__eo_state_proven_nth] using checkerTranslationInvariant_head_proven P s hs
      · cases so with
        | assume A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTranslationInvariant_tail hs) (eo_lit_zplus n (eo_lit_zneg 1))
        | assume_push A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTranslationInvariant_tail hs) (eo_lit_zplus n (eo_lit_zneg 1))
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTranslationInvariant_tail hs) (eo_lit_zplus n (eo_lit_zneg 1))

theorem checkerEntry_has_bool_type_at :
  forall {s : CState},
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    forall n : eo_lit_Int,
      RuleProofs.eo_has_bool_type (__eo_state_proven_nth s n)
:=
by
  intro s hsTy hsTrans n
  rcases checkerTypeInvariant_at hsTy n with ⟨_hNe, hTy⟩
  have hTrans : RuleProofs.eo_has_smt_translation (__eo_state_proven_nth s n) :=
    checkerTranslationInvariant_at hsTrans n
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type
    (__eo_state_proven_nth s n) hTrans hTy

theorem checkerLocalTruthInvariant_tail (M : SmtModel) :
  forall {so : CStateObj} {s : CState},
    checkerLocalTruthInvariant M (CState.cons so s) ->
    checkerLocalTruthInvariant M s
:=
by
  intro so s hs
  cases so with
  | assume A =>
      simpa [checkerLocalTruthInvariant] using hs
  | assume_push A =>
      simpa [checkerLocalTruthInvariant] using hs
  | proven P =>
      exact hs.2

theorem checkerLocalTruthInvariant_head_proven
    (M : SmtModel) (s : CState) (P : Term) :
  checkerLocalTruthInvariant M (CState.cons (CStateObj.proven P) s) ->
  eo_interprets M (stateAssumes s) true ->
  eo_interprets M (statePushes s) true ->
  eo_interprets M P true :=
by
  intro hs hAss hPush
  exact hs.1 hAss hPush

theorem checkerLocalTruthInvariant_at (M : SmtModel) :
  forall {s : CState},
    checkerLocalTruthInvariant M s ->
    forall n : eo_lit_Int,
      eo_interprets M (stateAssumes s) true ->
      eo_interprets M (statePushes s) true ->
      eo_interprets M (__eo_state_proven_nth s n) true
:=
by
  intro s hs
  induction s with
  | nil =>
      intro n hAss hPush
      simpa [__eo_state_proven_nth] using eo_interprets_true M
  | Stuck =>
      intro n hAss hPush
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro n hAss hPush
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth] using
              eo_interprets_and_left M A (stateAssumes s) hAss
        | assume_push A =>
            simpa [__eo_state_proven_nth] using
              eo_interprets_and_left M A (statePushes s) hPush
        | proven P =>
            have hAss' : eo_interprets M (stateAssumes s) true := by
              simpa [stateAssumes] using hAss
            have hPush' : eo_interprets M (statePushes s) true := by
              simpa [statePushes] using hPush
            simpa [__eo_state_proven_nth] using hs.1 hAss' hPush'
      · cases so with
        | assume A =>
            have hAssTail : eo_interprets M (stateAssumes s) true :=
              eo_interprets_and_right M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                (eo_lit_zplus n (eo_lit_zneg 1)) hAssTail hPush
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                (eo_lit_zplus n (eo_lit_zneg 1)) hAss hPushTail
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih hs.2 (eo_lit_zplus n (eo_lit_zneg 1))
                (by simpa [stateAssumes] using hAss)
                (by simpa [statePushes] using hPush)

theorem checkerLocalTruthInvariant_implies_truthInvariant (M : SmtModel) :
  forall {s : CState},
    checkerLocalTruthInvariant M s ->
    checkerTruthInvariant M s
:=
by
  intro s hs
  cases s with
  | Stuck =>
      exact checkerTruthInvariant_stuck M
  | nil =>
      intro n hAss hPush
      exact checkerLocalTruthInvariant_at M hs n hAss hPush
  | cons so s =>
      intro n hAss hPush
      exact checkerLocalTruthInvariant_at M hs n hAss hPush

theorem checkerLocalTruthInvariant_after_assume_list (M : SmtModel) (F : Term) :
  ValidAssumptionList F ->
  checkerLocalTruthInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hValid
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, checkerLocalTruthInvariant]
  | step A rest hRest ih =>
      simpa [__eo_invoke_assume_list, checkerLocalTruthInvariant] using ih

theorem checkerTypeInvariant_after_assume_list (F : Term) :
  TypedAssumptionList F ->
  checkerTypeInvariant (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hTyped
  induction hTyped with
  | base =>
      simp [__eo_invoke_assume_list, checkerTypeInvariant]
  | step A rest hA hTy hRest ih =>
      simpa [__eo_invoke_assume_list, checkerTypeInvariant, hA, hTy] using ih

theorem checkerTranslationInvariant_after_assume_list (F : Term) :
  TranslatableAssumptionList F ->
  checkerTranslationInvariant (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hTrans
  induction hTrans with
  | base =>
      simp [__eo_invoke_assume_list, checkerTranslationInvariant]
  | step A rest hA hRest ih =>
      exact ⟨hA, ih⟩

theorem push_assume_preserves_localTruthInvariant
    (M : SmtModel) (s : CState) (A : Term) :
  checkerLocalTruthInvariant M s ->
  checkerLocalTruthInvariant M (__eo_push_assume A s) :=
by
  intro hs
  by_cases hTy : __eo_typeof A = Term.Bool
  · simpa [push_assume_eq_cons_of_typeof_bool, hTy, checkerLocalTruthInvariant] using hs
  · simpa [push_assume_eq_stuck_of_typeof_ne_bool, hTy] using checkerLocalTruthInvariant_stuck M

theorem push_assume_preserves_typeInvariant
    (s : CState) (A : Term) :
  checkerTypeInvariant s ->
  checkerTypeInvariant (__eo_push_assume A s) :=
by
  intro hs
  by_cases hTy : __eo_typeof A = Term.Bool
  · have hA : A ≠ Term.Stuck := term_ne_stuck_of_typeof_bool A hTy
    simpa [push_assume_eq_cons_of_typeof_bool, hTy, checkerTypeInvariant, hA] using hs
  · simpa [push_assume_eq_stuck_of_typeof_ne_bool, hTy] using checkerTypeInvariant_stuck

theorem push_assume_preserves_translationInvariant
    (s : CState) (A : Term) :
  checkerTranslationInvariant s ->
  RuleProofs.eo_has_smt_translation A ->
  checkerTranslationInvariant (__eo_push_assume A s) :=
by
  intro hs hA
  by_cases hTy : __eo_typeof A = Term.Bool
  · simpa [push_assume_eq_cons_of_typeof_bool, hTy, checkerTranslationInvariant] using
      (show RuleProofs.eo_has_smt_translation A ∧ checkerTranslationInvariant s from ⟨hA, hs⟩)
  · simpa [push_assume_eq_stuck_of_typeof_ne_bool, hTy] using checkerTranslationInvariant_stuck

theorem push_proven_preserves_typeInvariant
    (s : CState) (P : Term) :
  checkerTypeInvariant s ->
  checkerTypeInvariant (__eo_push_proven P s) :=
by
  intro hs
  by_cases hTy : __eo_typeof P = Term.Bool
  · have hP : P ≠ Term.Stuck := term_ne_stuck_of_typeof_bool P hTy
    simpa [push_proven_eq_cons_of_typeof_bool, hTy, checkerTypeInvariant, hP] using hs
  · simpa [push_proven_eq_stuck_of_typeof_ne_bool, hTy] using checkerTypeInvariant_stuck

theorem push_proven_preserves_translationInvariant
    (s : CState) (P : Term) :
  checkerTranslationInvariant s ->
  RuleProofs.eo_has_smt_translation P ->
  checkerTranslationInvariant (__eo_push_proven P s) :=
by
  intro hs hP
  by_cases hTy : __eo_typeof P = Term.Bool
  · simpa [push_proven_eq_cons_of_typeof_bool, hTy, checkerTranslationInvariant] using
      (show RuleProofs.eo_has_smt_translation P ∧ checkerTranslationInvariant s from ⟨hP, hs⟩)
  · simpa [push_proven_eq_stuck_of_typeof_ne_bool, hTy] using checkerTranslationInvariant_stuck

theorem push_proven_preserves_localTruthInvariant_of_contextual_true
    (M : SmtModel) (s : CState) (P : Term) :
  checkerLocalTruthInvariant M s ->
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   eo_interprets M P true) ->
  checkerLocalTruthInvariant M (CState.cons (CStateObj.proven P) s) :=
by
  intro hs hP
  exact ⟨hP, hs⟩

def checkerShapeInvariant : CState -> Prop
  | CState.Stuck => True
  | s => stateAssumptionSuffix s

theorem checkerShapeInvariant_of_suffix {s : CState} :
  stateAssumptionSuffix s ->
  checkerShapeInvariant s :=
by
  cases s <;> simp [checkerShapeInvariant, stateAssumptionSuffix]

theorem suffix_of_checkerShapeInvariant_nonstuck {s : CState} :
  checkerShapeInvariant s ->
  s ≠ CState.Stuck ->
  stateAssumptionSuffix s :=
by
  intro hShape hNotStuck
  cases s with
  | Stuck =>
      exact False.elim (hNotStuck rfl)
  | nil =>
      simpa [checkerShapeInvariant]
  | cons so s =>
      simpa [checkerShapeInvariant] using hShape

def checkerStateInvariant (M : SmtModel) (s : CState) : Prop :=
  checkerShapeInvariant s ∧
  checkerLocalTruthInvariant M s ∧
  checkerTypeInvariant s ∧
  checkerTranslationInvariant s

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
  simp [__eo_push_proven, __eo_push_proven_check, __eo_is_bool_type]

theorem invoke_step_eq_cons_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  __eo_cmd_step_proven s r args premises = P ->
  __eo_typeof P = Term.Bool ->
  __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
by
  intro hStep hTy
  rw [invoke_step_eq_of_nonstuck s hNotStuck r args premises, hStep]
  simp [push_proven_eq_cons_of_typeof_bool, hTy]

theorem invoke_step_eq_stuck_of_typeof_ne_bool
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  __eo_cmd_step_proven s r args premises = P ->
  __eo_typeof P ≠ Term.Bool ->
  __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
by
  intro hStep hTy
  rw [invoke_step_eq_of_nonstuck s hNotStuck r args premises, hStep]
  simp [push_proven_eq_stuck_of_typeof_ne_bool, hTy]

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
  intro hs
  by_cases hTy : __eo_typeof A = Term.Bool
  · rw [push_assume_eq_cons_of_typeof_bool A s hTy]
    intro n hAss hPush
    by_cases hZero : n = 0
    · subst hZero
      have hPush' :
          eo_interprets M
            (Term.Apply (Term.Apply Term.and A) (statePushes s)) true := by
        simpa [push_assume_eq_cons_of_typeof_bool, hTy, statePushes] using hPush
      simpa [push_assume_eq_cons_of_typeof_bool, hTy, __eo_state_proven_nth] using
        eo_interprets_and_left M A (statePushes s) hPush'
    · have hAss' : eo_interprets M (stateAssumes s) true := by
        simpa [push_assume_eq_cons_of_typeof_bool, hTy, stateAssumes] using hAss
      have hPush' :
          eo_interprets M
            (Term.Apply (Term.Apply Term.and A) (statePushes s)) true := by
        simpa [push_assume_eq_cons_of_typeof_bool, hTy, statePushes] using hPush
      have hPushTail : eo_interprets M (statePushes s) true :=
        eo_interprets_and_right M A (statePushes s) hPush'
      simpa [push_assume_eq_cons_of_typeof_bool, hTy, __eo_state_proven_nth, hZero] using
        checkerTruthInvariant_at M hs
          (eo_lit_zplus n (eo_lit_zneg 1)) hAss' hPushTail
  · simpa [push_assume_eq_stuck_of_typeof_ne_bool, hTy] using checkerTruthInvariant_stuck M

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
  TypedAssumptionList F ->
  TranslatableAssumptionList F ->
  checkerStateInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hValid hTyped hTrans
  exact ⟨
    checkerShapeInvariant_of_suffix (stateAssumptionSuffix_invoke_assume_list hValid),
    checkerLocalTruthInvariant_after_assume_list M F hValid,
    checkerTypeInvariant_after_assume_list F hTyped,
    checkerTranslationInvariant_after_assume_list F hTrans
  ⟩

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
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur) := by
            simpa [__eo_invoke_cmd_step_pop] using hOk
          have hPushEq :
              __eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur =
                CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven s r args A premises)) cur :=
            push_proven_eq_cons_of_stateOk (__eo_cmd_step_pop_proven s r args A premises) cur hPushOk
          simpa [__eo_invoke_cmd_step_pop, hPushEq, stateAssumptionSuffix] using hTailSuffix
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
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur) := by
            simpa [__eo_invoke_cmd_step_pop] using hOk
          have hPushEq :
              __eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur =
                CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven s r args A premises)) cur :=
            push_proven_eq_cons_of_stateOk (__eo_cmd_step_pop_proven s r args A premises) cur hPushOk
          simp [__eo_invoke_cmd_step_pop, hPushEq, stateAssumes]
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
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_pop_proven s r args A premises) cur) := by
            simpa [__eo_invoke_cmd_step_pop] using hOk
          exact push_proven_reflects_stateOk (__eo_cmd_step_pop_proven s r args A premises) cur hPushOk
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
          exact push_assume_reflects_stateOk A (CState.cons so s) (by
            simpa [__eo_invoke_cmd] using hOk)
      | check_proven proven =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, stateOk]
          | proven F =>
              intro hOk
              cases hEq : __eo_eq F proven <;>
                simp [__eo_invoke_cmd, __eo_push_proven_check,
                  hEq, stateOk] at hOk ⊢
              case Boolean b =>
                cases b with
                | false =>
                    simp [stateOk] at hOk
                | true =>
                    exact hOk
      | step r args premises =>
          intro hOk
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven (CState.cons so s) r args premises)
                (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          exact push_proven_reflects_stateOk
            (__eo_cmd_step_proven (CState.cons so s) r args premises) (CState.cons so s) hPushOk
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
          have hPushOk : stateOk (__eo_push_assume A CState.nil) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A CState.nil hPushOk
          simp [__eo_invoke_cmd, hPushEq, stateAssumptionSuffix]
      | cons so s =>
          have hPushOk : stateOk (__eo_push_assume A (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A (CState.cons so s) hPushOk
          simpa [__eo_invoke_cmd, hPushEq, stateAssumptionSuffix] using hSuffix
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
                simp [__eo_invoke_cmd, __eo_push_proven_check,
                  hEq, stateOk] at hOk
              case Boolean b =>
                cases b with
                | false =>
                    contradiction
                | true =>
                    have hTailSuffix : stateAssumptionSuffix s := by
                      simpa [stateAssumptionSuffix] using hSuffix
                    simpa [__eo_invoke_cmd, __eo_push_proven_check,
                      hEq] using hTailSuffix
  | step r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven CState.nil r args premises) CState.nil) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_proven_eq_cons_of_stateOk
            (__eo_cmd_step_proven CState.nil r args premises) CState.nil hPushOk
          simp [__eo_invoke_cmd, hPushEq, stateAssumptionSuffix]
      | Stuck =>
          cases hSuffix
      | cons so s =>
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven (CState.cons so s) r args premises)
                (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_proven_eq_cons_of_stateOk
            (__eo_cmd_step_proven (CState.cons so s) r args premises) (CState.cons so s) hPushOk
          simpa [__eo_invoke_cmd, hPushEq, stateAssumptionSuffix] using hSuffix
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
          have hPushOk : stateOk (__eo_push_assume A CState.nil) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A CState.nil hPushOk
          simp [__eo_invoke_cmd, hPushEq, stateAssumes]
      | cons so s =>
          have hPushOk : stateOk (__eo_push_assume A (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A (CState.cons so s) hPushOk
          simp [__eo_invoke_cmd, hPushEq, stateAssumes]
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
                simp [__eo_invoke_cmd, __eo_push_proven_check,
                  hEq, stateOk] at hOk
              case Boolean b =>
                cases b with
                | false =>
                    contradiction
                | true =>
                    simp [__eo_invoke_cmd, __eo_push_proven_check,
                      hEq, stateAssumes]
  | step r args premises =>
      intro hSuffix hOk
      cases s with
      | nil =>
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven CState.nil r args premises) CState.nil) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_proven_eq_cons_of_stateOk
            (__eo_cmd_step_proven CState.nil r args premises) CState.nil hPushOk
          simp [__eo_invoke_cmd, hPushEq, stateAssumes]
      | Stuck =>
          cases hSuffix
      | cons so s =>
          have hPushOk :
              stateOk (__eo_push_proven (__eo_cmd_step_proven (CState.cons so s) r args premises)
                (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_proven_eq_cons_of_stateOk
            (__eo_cmd_step_proven (CState.cons so s) r args premises) (CState.cons so s) hPushOk
          simp [__eo_invoke_cmd, hPushEq, stateAssumes]
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
            simp [S1, hS1, __eo_push_proven_check,
              __eo_state_is_closed, hEq] at hClosed
          case Boolean b =>
            cases b with
            | false =>
                contradiction
            | true =>
                have hP : P = Term.Boolean false :=
                  eo_eq_false_true_implies_eq_false P hEq
                subst hP
                refine ⟨s, ?_, hClosed⟩
                simp [S1, hS1]

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

def premiseAndFormula (s : CState) : CIndexList -> Term
  | CIndexList.nil => Term.Boolean true
  | CIndexList.cons n premises =>
      Term.Apply (Term.Apply Term.and (__eo_state_proven_nth s n))
        (premiseAndFormula s premises)

def premiseTermList (s : CState) : CIndexList -> List Term
  | CIndexList.nil => []
  | CIndexList.cons n premises =>
      __eo_state_proven_nth s n :: premiseTermList s premises

theorem premiseAndFormula_is_and_list :
  forall (s : CState) (premises : CIndexList),
    __eo_is_list Term.and (premiseAndFormula s premises) = Term.Boolean true
:=
by
  have hGetNil :
      forall (s : CState) (premises : CIndexList),
        __eo_get_nil_rec Term.and (premiseAndFormula s premises) ≠ Term.Stuck
  :=
  by
    intro s premises
    induction premises with
    | nil =>
        unfold premiseAndFormula
        unfold __eo_get_nil_rec
        unfold __eo_requires
        unfold __eo_is_list_nil
        simp [eo_lit_ite, eo_lit_teq, eo_lit_not, SmtEval.smt_lit_not]
    | cons n premises ih =>
        unfold premiseAndFormula
        unfold __eo_get_nil_rec
        unfold __eo_requires
        simpa [eo_lit_ite, eo_lit_teq, eo_lit_not, SmtEval.smt_lit_not] using ih
  intro s premises
  have hNotStuck :
      __eo_get_nil_rec Term.and (premiseAndFormula s premises) ≠ Term.Stuck :=
    hGetNil s premises
  have hPremNotStuck : premiseAndFormula s premises ≠ Term.Stuck :=
    by
      induction premises with
      | nil =>
          simp [premiseAndFormula]
      | cons n premises ih =>
          simp [premiseAndFormula]
  unfold __eo_is_list
  unfold __eo_is_ok
  simpa [eo_lit_teq, eo_lit_not, SmtEval.smt_lit_not] using hNotStuck

theorem mk_premise_list_and_eq_premiseAndFormula :
  forall (s : CState) (premises : CIndexList),
    __eo_mk_premise_list Term.and premises s = premiseAndFormula s premises
:=
by
  intro s premises
  induction premises with
  | nil =>
      simp [__eo_mk_premise_list, premiseAndFormula, __eo_nil]
  | cons n premises ih =>
      simp [__eo_mk_premise_list, premiseAndFormula, __eo_cons, __eo_requires, eo_lit_ite,
        eo_lit_teq, eo_lit_not, ih, premiseAndFormula_is_and_list, SmtEval.smt_lit_not]

theorem premiseAndFormulaList_eq_premiseAndFormula :
  forall (s : CState) (premises : CIndexList),
    premiseAndFormulaList (premiseTermList s premises) = premiseAndFormula s premises
:=
by
  intro s premises
  induction premises with
  | nil =>
      simp [premiseTermList, premiseAndFormulaList, premiseAndFormula]
  | cons n premises ih =>
      simp [premiseTermList, premiseAndFormulaList, premiseAndFormula, ih]

theorem premiseTermList_has_bool_type (s : CState) :
  forall (premises : CIndexList),
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    AllHaveBoolType (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hsTy hsTrans t ht
      cases ht
  | cons n premises ih =>
      intro hsTy hsTrans t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerEntry_has_bool_type_at hsTy hsTrans n
      · exact ih hsTy hsTrans t ht

theorem premiseAndFormula_has_bool_type :
  forall (s : CState) (premises : CIndexList),
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    RuleProofs.eo_has_bool_type (premiseAndFormula s premises)
:=
by
  intro s premises
  induction premises with
  | nil =>
      intro hsTy hsTrans
      simpa [premiseAndFormula] using RuleProofs.eo_has_bool_type_true
  | cons n premises ih =>
      intro hsTy hsTrans
      apply RuleProofs.eo_has_bool_type_and_of_bool_args
      · exact checkerEntry_has_bool_type_at hsTy hsTrans n
      · exact ih hsTy hsTrans

theorem mk_premise_list_and_has_bool_type (s : CState) (premises : CIndexList) :
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  RuleProofs.eo_has_bool_type (__eo_mk_premise_list Term.and premises s) :=
by
  intro hsTy hsTrans
  rw [mk_premise_list_and_eq_premiseAndFormula]
  exact premiseAndFormula_has_bool_type s premises hsTy hsTrans

theorem premiseAndFormula_true_of_truthInvariant (M : SmtModel) (s : CState) :
  forall (premises : CIndexList),
    checkerTruthInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M (premiseAndFormula s premises) true
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hs hAss hPush
      simpa [premiseAndFormula] using eo_interprets_true M
  | cons n premises ih =>
      intro hs hAss hPush
      apply eo_interprets_and_intro
      · exact checkerTruthInvariant_at M hs n hAss hPush
      · exact ih hs hAss hPush

theorem mk_premise_list_and_true_of_truthInvariant (M : SmtModel) (s : CState)
    (premises : CIndexList) :
  checkerTruthInvariant M s ->
  eo_interprets M (stateAssumes s) true ->
  eo_interprets M (statePushes s) true ->
  eo_interprets M (__eo_mk_premise_list Term.and premises s) true
:=
by
  intro hs hAss hPush
  rw [mk_premise_list_and_eq_premiseAndFormula]
  exact premiseAndFormula_true_of_truthInvariant M s premises hs hAss hPush

theorem premiseTermList_true_of_truthInvariant
    (M : SmtModel) (s : CState) :
  forall (premises : CIndexList),
    checkerTruthInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    AllInterpretedTrue M (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hs hAss hPush t ht
      cases ht
  | cons n premises ih =>
      intro hs hAss hPush t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerTruthInvariant_at M hs n hAss hPush
      · exact ih hs hAss hPush t ht

structure CmdStepFacts (M : SmtModel) (s : CState) (P : Term) : Prop where
  true_of_context :
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P

theorem cmdStepFacts_of_contextual_true_and_bool
    (M : SmtModel) (s : CState) (P : Term) :
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   eo_interprets M P true) ->
  RuleProofs.eo_has_bool_type P ->
  CmdStepFacts M s P :=
by
  intro hTrue hBool
  refine ⟨hTrue, ?_⟩
  exact RuleProofs.eo_has_smt_translation_of_has_bool_type P hBool

theorem step_rule_facts_narg_mprem
    (M : SmtModel) (s : CState)
    (args premises : List Term) (mk : List Term -> List Term -> Term) :
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   AllInterpretedTrue M premises) ->
  AllHaveSmtTranslation args ->
  AllHaveBoolType premises ->
  StepRuleSpecNArgMPrem M mk ->
  mk args premises ≠ Term.Stuck ->
  CmdStepFacts M s (mk args premises) :=
by
  intro hPremTrue hArgs hPremBool hSpec hProg
  refine ⟨?_, ?_⟩
  · intro hAss hPush
    exact (hSpec.facts_of_true args premises hArgs (hPremTrue hAss hPush) hProg).true_in_model
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
      (hSpec.bool_of_translation args premises hArgs hPremBool hProg)

/- Central expansion point for plain `step` rules.

   To add a new rule handled by `__eo_cmd_step_proven`, add its matching
   pattern here and dispatch to the arity helper matching the rule shape.
   The preservation theorems below then pick the new rule up automatically. -/
theorem cmd_step_proven_facts_of_invariants
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (_hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTruthInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  cmdTranslationOk (CCmd.step r args premises) ->
  __eo_cmd_step_proven s r args premises ≠ Term.Stuck ->
  CmdStepFacts M s (__eo_cmd_step_proven s r args premises)
:=
by
  intro hs hsTy hsTrans hCmdTrans hProg
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
                      have hArgsTrans : AllHaveSmtTranslation [] := by
                        intro t ht
                        cases ht
                      have hPremisesBool : AllHaveBoolType [X1, X2] := by
                        intro t ht
                        simp [X1, X2] at ht
                        rcases ht with rfl | rfl
                        · exact checkerEntry_has_bool_type_at hsTy hsTrans n1
                        · exact checkerEntry_has_bool_type_at hsTy hsTrans n2
                      exact step_rule_facts_narg_mprem M s [] [X1, X2]
                        (fun
                          | [], [X1, X2] => __eo_prog_contra (Proof.pf X1) (Proof.pf X2)
                          | _, _ => Term.Stuck)
                        (fun hAss hPush => by
                          intro t ht
                          simp [X1, X2] at ht
                          rcases ht with rfl | rfl
                          · exact checkerTruthInvariant_at M hs n1 hAss hPush
                          · exact checkerTruthInvariant_at M hs n2 hAss hPush)
                        hArgsTrans hPremisesBool (spec___eo_prog_contra M hM)
                        (by simpa [P, X1, X2, __eo_cmd_step_proven] using hProg)
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
                  have hATrans : RuleProofs.eo_has_smt_translation a1 := by
                    simpa [cmdTranslationOk] using hCmdTrans
                  have hArgsTrans : AllHaveSmtTranslation [a1] := by
                    intro t ht
                    simp at ht
                    rcases ht with rfl
                    exact hATrans
                  have hPremisesBool : AllHaveBoolType [] := by
                    intro t ht
                    cases ht
                  exact step_rule_facts_narg_mprem M s [a1] []
                    (fun
                      | [a1], [] => __eo_prog_refl a1
                      | _, _ => Term.Stuck)
                    (fun _hAss _hPush => by
                      intro t ht
                      cases ht)
                    hArgsTrans hPremisesBool (spec___eo_prog_refl M hM)
                    (by simpa [__eo_cmd_step_proven] using hProg)
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
                  have hArgsTrans : AllHaveSmtTranslation [] := by
                    intro t ht
                    cases ht
                  have hPremisesBool : AllHaveBoolType [X] := by
                    intro t ht
                    simp [X] at ht
                    rcases ht with rfl
                    exact checkerEntry_has_bool_type_at hsTy hsTrans n1
                  exact step_rule_facts_narg_mprem M s [] [X]
                    (fun
                      | [], [X] => __eo_prog_symm (Proof.pf X)
                      | _, _ => Term.Stuck)
                    (fun hAss hPush => by
                      intro t ht
                      simp [X] at ht
                      rcases ht with rfl
                      exact checkerTruthInvariant_at M hs n1 hAss hPush)
                    hArgsTrans hPremisesBool (spec___eo_prog_symm M hM)
                    (by simpa [P, X, __eo_cmd_step_proven] using hProg)
              | cons n2 premises =>
                  exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
      | cons a args =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | trans =>
      cases args with
      | nil =>
          let X := __eo_mk_premise_list Term.and premises s
          let premisesL := premiseTermList s premises
          let P := __eo_prog_trans (Proof.pf X)
          have hArgsTrans : AllHaveSmtTranslation [] := by
            intro t ht
            cases ht
          have hPremisesBool : AllHaveBoolType premisesL :=
            premiseTermList_has_bool_type s premises hsTy hsTrans
          simpa [P, X, premisesL, __eo_cmd_step_proven,
              mk_premise_list_and_eq_premiseAndFormula,
              premiseAndFormulaList_eq_premiseAndFormula] using
            (step_rule_facts_narg_mprem M s [] premisesL
              (fun
                | [], premises => __eo_prog_trans (Proof.pf (premiseAndFormulaList premises))
                | _, _ => Term.Stuck)
              (fun hAss hPush =>
                premiseTermList_true_of_truthInvariant M s premises hs hAss hPush)
              hArgsTrans hPremisesBool (spec___eo_prog_trans M hM)
              (by
                simpa [P, X, premisesL, __eo_cmd_step_proven,
                  mk_premise_list_and_eq_premiseAndFormula,
                  premiseAndFormulaList_eq_premiseAndFormula] using hProg))
      | cons a args =>
          exact False.elim (hProg (by simp [__eo_cmd_step_proven]))

theorem invoke_step_preserves_localTruthInvariant_of_stuck
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  checkerLocalTruthInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hStep
  have hStuck :
      __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
    invoke_step_eq_stuck_of_nonstuck s hNotStuck r args premises hStep
  simpa [hStuck] using checkerLocalTruthInvariant_stuck M

theorem invoke_step_preserves_localTruthInvariant_of_contextual_true
    (M : SmtModel) (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  checkerLocalTruthInvariant M s ->
  __eo_cmd_step_proven s r args premises = P ->
  P ≠ Term.Stuck ->
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   eo_interprets M P true) ->
  checkerLocalTruthInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hStep hNe hP
  by_cases hTy : __eo_typeof P = Term.Bool
  · have hPost :
        __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
      invoke_step_eq_cons_of_nonstuck s hNotStuck r args premises P hStep hTy
    simpa [hPost] using
      push_proven_preserves_localTruthInvariant_of_contextual_true M s P hs hP
  · have hPost :
        __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
      invoke_step_eq_stuck_of_typeof_ne_bool s hNotStuck r args premises P hStep hTy
    simpa [hPost] using checkerLocalTruthInvariant_stuck M

theorem invoke_step_preserves_localTruthInvariant
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerLocalTruthInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  cmdTranslationOk (CCmd.step r args premises) ->
  checkerLocalTruthInvariant M (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hsTy hsTrans hCmdTrans
  have hTruth : checkerTruthInvariant M s :=
    checkerLocalTruthInvariant_implies_truthInvariant M hs
  by_cases hProg : __eo_cmd_step_proven s r args premises = Term.Stuck
  · exact invoke_step_preserves_localTruthInvariant_of_stuck M s hNotStuck r args premises hProg
  · have hFacts :
        CmdStepFacts M s (__eo_cmd_step_proven s r args premises) :=
      cmd_step_proven_facts_of_invariants M hM s hNotStuck r args premises
        hTruth hsTy hsTrans hCmdTrans hProg
    exact invoke_step_preserves_localTruthInvariant_of_contextual_true M s hNotStuck
      r args premises (__eo_cmd_step_proven s r args premises) hs rfl hProg
      hFacts.true_of_context

theorem invoke_step_preserves_typeInvariant_of_stuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  checkerTypeInvariant (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hStep
  have hStuck :
      __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
    invoke_step_eq_stuck_of_nonstuck s hNotStuck r args premises hStep
  simpa [hStuck] using checkerTypeInvariant_stuck

theorem invoke_step_preserves_typeInvariant_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) (P : Term) :
  checkerTypeInvariant s ->
  __eo_cmd_step_proven s r args premises = P ->
  P ≠ Term.Stuck ->
  checkerTypeInvariant (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hStep hNe
  by_cases hTy : __eo_typeof P = Term.Bool
  · have hPost :
        __eo_invoke_cmd s (CCmd.step r args premises) = CState.cons (CStateObj.proven P) s :=
      invoke_step_eq_cons_of_nonstuck s hNotStuck r args premises P hStep hTy
    have hPush :
        checkerTypeInvariant (__eo_push_proven P s) :=
      push_proven_preserves_typeInvariant s P hs
    rw [push_proven_eq_cons_of_typeof_bool P s hTy] at hPush
    simpa [hPost] using hPush
  · have hPost :
        __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
      invoke_step_eq_stuck_of_typeof_ne_bool s hNotStuck r args premises P hStep hTy
    simpa [hPost] using checkerTypeInvariant_stuck

theorem invoke_step_preserves_typeInvariant
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTypeInvariant s ->
  checkerTypeInvariant (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs
  by_cases hProg : __eo_cmd_step_proven s r args premises = Term.Stuck
  · exact invoke_step_preserves_typeInvariant_of_stuck s hNotStuck r args premises hProg
  · exact invoke_step_preserves_typeInvariant_of_nonstuck s hNotStuck
      r args premises (__eo_cmd_step_proven s r args premises) hs rfl hProg

theorem invoke_step_preserves_translationInvariant
    (M : SmtModel) (_hM : model_total_typed M)
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerLocalTruthInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  cmdTranslationOk (CCmd.step r args premises) ->
  checkerTranslationInvariant (__eo_invoke_cmd s (CCmd.step r args premises)) :=
by
  intro hs hsTy hsTrans hCmdTrans
  by_cases hProg : __eo_cmd_step_proven s r args premises = Term.Stuck
  · have hStuck :
        __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
      invoke_step_eq_stuck_of_nonstuck s hNotStuck r args premises hProg
    simpa [hStuck] using checkerTranslationInvariant_stuck
  · have hTruth : checkerTruthInvariant M s :=
        checkerLocalTruthInvariant_implies_truthInvariant M hs
    have hFacts :
        CmdStepFacts M s (__eo_cmd_step_proven s r args premises) :=
      cmd_step_proven_facts_of_invariants M _hM s hNotStuck r args premises
        hTruth hsTy hsTrans hCmdTrans hProg
    have hPTrans :
        RuleProofs.eo_has_smt_translation (__eo_cmd_step_proven s r args premises) :=
      hFacts.has_smt_translation
    by_cases hTy : __eo_typeof (__eo_cmd_step_proven s r args premises) = Term.Bool
    · have hPost :
          __eo_invoke_cmd s (CCmd.step r args premises) =
            CState.cons (CStateObj.proven (__eo_cmd_step_proven s r args premises)) s :=
        invoke_step_eq_cons_of_nonstuck s hNotStuck r args premises
          (__eo_cmd_step_proven s r args premises) rfl hTy
      have hPush :
          checkerTranslationInvariant
            (__eo_push_proven (__eo_cmd_step_proven s r args premises) s) :=
        push_proven_preserves_translationInvariant s
          (__eo_cmd_step_proven s r args premises) hsTrans hPTrans
      rw [push_proven_eq_cons_of_typeof_bool (__eo_cmd_step_proven s r args premises) s hTy] at hPush
      simpa [hPost] using hPush
    · have hPost :
          __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
        invoke_step_eq_stuck_of_typeof_ne_bool s hNotStuck r args premises
          (__eo_cmd_step_proven s r args premises) rfl hTy
      simpa [hPost] using checkerTranslationInvariant_stuck

theorem cmd_step_pop_proven_has_smt_translation
    (root tail : CState) (A : Term)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTypeInvariant root ->
  checkerTranslationInvariant root ->
  checkerTypeInvariant (CState.cons (CStateObj.assume_push A) tail) ->
  checkerTranslationInvariant (CState.cons (CStateObj.assume_push A) tail) ->
  __eo_cmd_step_pop_proven root r args A premises ≠ Term.Stuck ->
  RuleProofs.eo_has_smt_translation (__eo_cmd_step_pop_proven root r args A premises)
:=
by
  intro hsRootTy hsRootTrans hsCurTy hsCurTrans hProg
  by_cases hA : A = Term.Stuck
  · exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven, hA]))
  · cases r with
    | scope =>
        cases args with
        | nil =>
            cases premises with
            | nil =>
                exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
            | cons n1 premises =>
                cases premises with
                | nil =>
                    let X := __eo_state_proven_nth root n1
                    let P := __eo_prog_scope A (Proof.pf X)
                    have hATy : __eo_typeof A = Term.Bool :=
                      (checkerTypeInvariant_head_assume_push A tail hsCurTy).2
                    have hATrans : RuleProofs.eo_has_smt_translation A :=
                      checkerTranslationInvariant_head_assume_push A tail hsCurTrans
                    have hXTy : __eo_typeof X = Term.Bool :=
                      (checkerTypeInvariant_at hsRootTy n1).2
                    have hXTrans : RuleProofs.eo_has_smt_translation X :=
                      checkerTranslationInvariant_at hsRootTrans n1
                    have hABool : RuleProofs.eo_has_bool_type A :=
                      RuleProofs.eo_typeof_bool_implies_has_bool_type A hATrans hATy
                    have hXBool : RuleProofs.eo_has_bool_type X :=
                      RuleProofs.eo_typeof_bool_implies_has_bool_type X hXTrans hXTy
                    have hPBool :
                        RuleProofs.eo_has_bool_type (__eo_prog_scope A (Proof.pf X)) :=
                      typed___eo_prog_scope A X hABool hXBool
                        (by simpa [P, X, __eo_cmd_step_pop_proven, hA] using hProg)
                    simpa [P, X, __eo_cmd_step_pop_proven, hA] using
                      RuleProofs.eo_has_smt_translation_of_has_bool_type (__eo_prog_scope A (Proof.pf X)) hPBool
                | cons n2 premises =>
                    exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
        | cons a args =>
            exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
    | contra =>
        exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
    | refl =>
        exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
    | symm =>
        exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
    | trans =>
        exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))

theorem cmd_step_pop_proven_true_of_localTruthInvariant
    (M : SmtModel) (hM : model_total_typed M)
    (root tail : CState) (A : Term)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerLocalTruthInvariant M root ->
  checkerTypeInvariant root ->
  checkerTranslationInvariant root ->
  checkerTypeInvariant (CState.cons (CStateObj.assume_push A) tail) ->
  checkerTranslationInvariant (CState.cons (CStateObj.assume_push A) tail) ->
  __eo_cmd_step_pop_proven root r args A premises ≠ Term.Stuck ->
  stateAssumes root = stateAssumes tail ->
  statePushes root = Term.Apply (Term.Apply Term.and A) (statePushes tail) ->
  eo_interprets M (stateAssumes tail) true ->
  eo_interprets M (statePushes tail) true ->
  eo_interprets M (__eo_cmd_step_pop_proven root r args A premises) true
:=
by
  intro hsRoot hsRootTy hsRootTrans hsCurTy hsCurTrans hProg hAssEq hPushEq hAss hPush
  by_cases hA : A = Term.Stuck
  · exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven, hA]))
  · cases r with
    | scope =>
        cases args with
        | nil =>
            cases premises with
            | nil =>
                exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
            | cons n1 premises =>
                cases premises with
                | nil =>
                    let X := __eo_state_proven_nth root n1
                    let P := __eo_prog_scope A (Proof.pf X)
                    have hScoped :
                        eo_interprets M A true -> eo_interprets M X true := by
                      intro hATrue
                      have hAssRoot : eo_interprets M (stateAssumes root) true := by
                        rw [hAssEq]
                        exact hAss
                      have hPushRoot : eo_interprets M (statePushes root) true := by
                        rw [hPushEq]
                        exact eo_interprets_and_intro M A (statePushes tail) hATrue hPush
                      exact checkerLocalTruthInvariant_at M hsRoot n1 hAssRoot hPushRoot
                    have hATy : __eo_typeof A = Term.Bool :=
                      (checkerTypeInvariant_head_assume_push A tail hsCurTy).2
                    have hATrans : RuleProofs.eo_has_smt_translation A :=
                      checkerTranslationInvariant_head_assume_push A tail hsCurTrans
                    have hXTy : __eo_typeof X = Term.Bool :=
                      (checkerTypeInvariant_at hsRootTy n1).2
                    have hXTrans : RuleProofs.eo_has_smt_translation X :=
                      checkerTranslationInvariant_at hsRootTrans n1
                    simpa [P, X, __eo_cmd_step_pop_proven, hA] using
                      (facts___eo_prog_scope M hM A X hScoped
                        hATrans hXTrans hATy hXTy
                        (by simpa [P, X, __eo_cmd_step_pop_proven, hA] using hProg)).true_in_model
                | cons n2 premises =>
                    exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
        | cons a args =>
            exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
    | contra =>
        exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
    | refl =>
        exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
    | symm =>
        exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
    | trans =>
        exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))

theorem invoke_cmd_step_pop_preserves_localTruthInvariant_aux
    (M : SmtModel) (hM : model_total_typed M) :
  forall (root cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    checkerLocalTruthInvariant M root ->
    checkerLocalTruthInvariant M cur ->
    checkerTypeInvariant root ->
    checkerTypeInvariant cur ->
    checkerTranslationInvariant root ->
    checkerTranslationInvariant cur ->
    stateAssumptionSuffix cur ->
    stateAssumes root = stateAssumes cur ->
    statePushes root = statePushes cur ->
    checkerLocalTruthInvariant M (__eo_invoke_cmd_step_pop root cur r args premises)
:=
by
  intro root cur
  induction cur with
  | nil =>
      intro r args premises hsRoot hCur hsRootTy hsCurTy hsRootTrans hsCurTrans hSuffix hAssEq hPushEq
      simpa [__eo_invoke_cmd_step_pop] using checkerLocalTruthInvariant_stuck M
  | Stuck =>
      intro r args premises hsRoot hCur hsRootTy hsCurTy hsRootTrans hsCurTrans hSuffix hAssEq hPushEq
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hsRoot hCur hsRootTy hsCurTy hsRootTrans hsCurTrans hSuffix hAssEq hPushEq
      cases so with
      | assume_push A =>
          cases hStep : eo_lit_teq (__eo_cmd_step_pop_proven root r args A premises) Term.Stuck with
          | false =>
              have hProg : __eo_cmd_step_pop_proven root r args A premises ≠ Term.Stuck := by
                intro hEq
                simp [eo_lit_teq, hEq] at hStep
              have hTail : checkerLocalTruthInvariant M cur := by
                simpa [checkerLocalTruthInvariant] using hCur
              have hAssEqTail : stateAssumes root = stateAssumes cur := by
                simpa [stateAssumes] using hAssEq
              have hPushEqTail :
                  statePushes root = Term.Apply (Term.Apply Term.and A) (statePushes cur) := by
                simpa [statePushes] using hPushEq
              have hContext :
                  eo_interprets M (stateAssumes cur) true ->
                  eo_interprets M (statePushes cur) true ->
                  eo_interprets M (__eo_cmd_step_pop_proven root r args A premises) true := by
                intro hAss hPush
                exact cmd_step_pop_proven_true_of_localTruthInvariant M hM root cur A r args premises
                  hsRoot hsRootTy hsRootTrans hsCurTy hsCurTrans hProg hAssEqTail hPushEqTail hAss hPush
              by_cases hTy : __eo_typeof (__eo_cmd_step_pop_proven root r args A premises) = Term.Bool
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven root r args A premises)) cur := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_cons_of_typeof_bool, hTy]
                simpa [hPost] using
                  push_proven_preserves_localTruthInvariant_of_contextual_true M cur
                    (__eo_cmd_step_pop_proven root r args A premises) hTail hContext
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.Stuck := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_stuck_of_typeof_ne_bool, hTy]
                simpa [hPost] using checkerLocalTruthInvariant_stuck M
          | true =>
              have hEq : __eo_cmd_step_pop_proven root r args A premises = Term.Stuck := by
                simpa [eo_lit_teq] using hStep
              simpa [__eo_invoke_cmd_step_pop, hEq, push_proven_eq_stuck_of_eq_stuck] using
                checkerLocalTruthInvariant_stuck M
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop root cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail root cur r args premises hTail
          simpa [__eo_invoke_cmd_step_pop, hStuck] using checkerLocalTruthInvariant_stuck M
      | proven P =>
          have hCurTail : checkerLocalTruthInvariant M cur :=
            checkerLocalTruthInvariant_tail M hCur
          have hSuffixTail : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hAssEqTail : stateAssumes root = stateAssumes cur := by
            simpa [stateAssumes] using hAssEq
          have hPushEqTail : statePushes root = statePushes cur := by
            simpa [statePushes] using hPushEq
          exact ih r args premises hsRoot hCurTail hsRootTy (checkerTypeInvariant_tail hsCurTy)
            hsRootTrans (checkerTranslationInvariant_tail hsCurTrans)
            hSuffixTail hAssEqTail hPushEqTail

theorem invoke_cmd_step_pop_preserves_localTruthInvariant
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerLocalTruthInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  stateAssumptionSuffix s ->
  checkerLocalTruthInvariant M (__eo_invoke_cmd_step_pop s s r args premises) :=
by
  intro hs hsTy hsTrans hSuffix
  exact invoke_cmd_step_pop_preserves_localTruthInvariant_aux M hM s s r args premises
    hs hs hsTy hsTy hsTrans hsTrans hSuffix rfl rfl

theorem invoke_cmd_step_pop_preserves_typeInvariant_aux :
  forall (root cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    checkerTypeInvariant cur ->
    stateAssumptionSuffix cur ->
    checkerTypeInvariant (__eo_invoke_cmd_step_pop root cur r args premises)
:=
by
  intro root cur
  induction cur with
  | nil =>
      intro r args premises hCur hSuffix
      simpa [__eo_invoke_cmd_step_pop] using checkerTypeInvariant_stuck
  | Stuck =>
      intro r args premises hCur hSuffix
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hCur hSuffix
      cases so with
      | assume_push A =>
          have hTail : checkerTypeInvariant cur :=
            checkerTypeInvariant_tail hCur
          simpa [__eo_invoke_cmd_step_pop] using
            push_proven_preserves_typeInvariant cur (__eo_cmd_step_pop_proven root r args A premises) hTail
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hTailSuffix : stateAssumptionSuffix cur := stateAssumptionSuffix_of_tail hTail
          simpa [__eo_invoke_cmd_step_pop] using
            ih r args premises (checkerTypeInvariant_tail hCur) hTailSuffix
      | proven P =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          simpa [__eo_invoke_cmd_step_pop] using
            ih r args premises (checkerTypeInvariant_tail hCur) hTailSuffix

theorem invoke_cmd_step_pop_preserves_typeInvariant
    (s : CState) (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTypeInvariant s ->
  stateAssumptionSuffix s ->
  checkerTypeInvariant (__eo_invoke_cmd_step_pop s s r args premises) :=
by
  intro hs hSuffix
  exact invoke_cmd_step_pop_preserves_typeInvariant_aux s s r args premises hs hSuffix

theorem invoke_cmd_step_pop_preserves_translationInvariant_aux :
  forall (root cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    checkerTypeInvariant root ->
    checkerTypeInvariant cur ->
    checkerTranslationInvariant root ->
    checkerTranslationInvariant cur ->
    stateAssumptionSuffix cur ->
    checkerTranslationInvariant (__eo_invoke_cmd_step_pop root cur r args premises)
:=
by
  intro root cur
  induction cur with
  | nil =>
      intro r args premises hsRootTy hsCurTy hsRootTrans hsCurTrans hSuffix
      simpa [__eo_invoke_cmd_step_pop] using checkerTranslationInvariant_stuck
  | Stuck =>
      intro r args premises hsRootTy hsCurTy hsRootTrans hsCurTrans hSuffix
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hsRootTy hsCurTy hsRootTrans hsCurTrans hSuffix
      cases so with
      | assume_push A =>
          cases hStep : eo_lit_teq (__eo_cmd_step_pop_proven root r args A premises) Term.Stuck with
          | false =>
              have hProg : __eo_cmd_step_pop_proven root r args A premises ≠ Term.Stuck := by
                intro hEq
                simp [eo_lit_teq, hEq] at hStep
              have hTail : checkerTranslationInvariant cur :=
                checkerTranslationInvariant_tail hsCurTrans
              have hPTrans :
                  RuleProofs.eo_has_smt_translation (__eo_cmd_step_pop_proven root r args A premises) :=
                cmd_step_pop_proven_has_smt_translation root cur A r args premises
                  hsRootTy hsRootTrans hsCurTy hsCurTrans hProg
              by_cases hTy : __eo_typeof (__eo_cmd_step_pop_proven root r args A premises) = Term.Bool
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven root r args A premises)) cur := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_cons_of_typeof_bool, hTy]
                have hPush :
                    checkerTranslationInvariant
                      (__eo_push_proven (__eo_cmd_step_pop_proven root r args A premises) cur) :=
                  push_proven_preserves_translationInvariant cur
                    (__eo_cmd_step_pop_proven root r args A premises) hTail hPTrans
                rw [push_proven_eq_cons_of_typeof_bool (__eo_cmd_step_pop_proven root r args A premises) cur hTy] at hPush
                simpa [hPost] using hPush
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.Stuck := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_stuck_of_typeof_ne_bool, hTy]
                simpa [hPost] using checkerTranslationInvariant_stuck
          | true =>
              have hEq : __eo_cmd_step_pop_proven root r args A premises = Term.Stuck := by
                simpa [eo_lit_teq] using hStep
              simpa [__eo_invoke_cmd_step_pop, hEq, push_proven_eq_stuck_of_eq_stuck] using
                checkerTranslationInvariant_stuck
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hTailSuffix : stateAssumptionSuffix cur := stateAssumptionSuffix_of_tail hTail
          simpa [__eo_invoke_cmd_step_pop] using
            ih r args premises hsRootTy (checkerTypeInvariant_tail hsCurTy)
              hsRootTrans (checkerTranslationInvariant_tail hsCurTrans) hTailSuffix
      | proven P =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          simpa [__eo_invoke_cmd_step_pop] using
            ih r args premises hsRootTy (checkerTypeInvariant_tail hsCurTy)
              hsRootTrans (checkerTranslationInvariant_tail hsCurTrans) hTailSuffix

theorem invoke_cmd_step_pop_preserves_translationInvariant
    (s : CState) (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  stateAssumptionSuffix s ->
  checkerTranslationInvariant (__eo_invoke_cmd_step_pop s s r args premises) :=
by
  intro hsTy hsTrans hSuffix
  exact invoke_cmd_step_pop_preserves_translationInvariant_aux s s r args premises
    hsTy hsTy hsTrans hsTrans hSuffix

theorem invoke_cmd_step_pop_preserves_shapeInvariant_aux :
  forall (root cur : CState) (r : CRule) (args : CArgList) (premises : CIndexList),
    stateAssumptionSuffix cur ->
    checkerShapeInvariant (__eo_invoke_cmd_step_pop root cur r args premises)
:=
by
  intro root cur
  induction cur with
  | nil =>
      intro r args premises hSuffix
      simp [__eo_invoke_cmd_step_pop, checkerShapeInvariant]
  | Stuck =>
      intro r args premises hSuffix
      cases hSuffix
  | cons so cur ih =>
      intro r args premises hSuffix
      cases so with
      | assume_push A =>
          cases hStep : eo_lit_teq (__eo_cmd_step_pop_proven root r args A premises) Term.Stuck with
          | false =>
              have hTailSuffix : stateAssumptionSuffix cur := by
                simpa [stateAssumptionSuffix] using hSuffix
              by_cases hTy : __eo_typeof (__eo_cmd_step_pop_proven root r args A premises) = Term.Bool
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.cons (CStateObj.proven (__eo_cmd_step_pop_proven root r args A premises)) cur := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_cons_of_typeof_bool, hTy]
                simpa [hPost, checkerShapeInvariant, stateAssumptionSuffix] using hTailSuffix
              · have hPost :
                    __eo_invoke_cmd_step_pop root (CState.cons (CStateObj.assume_push A) cur) r args premises =
                      CState.Stuck := by
                  simp [__eo_invoke_cmd_step_pop, push_proven_eq_stuck_of_typeof_ne_bool, hTy]
                simp [hPost, checkerShapeInvariant]
          | true =>
              have hEq : __eo_cmd_step_pop_proven root r args A premises = Term.Stuck := by
                simp [eo_lit_teq] at hStep
                exact hStep
              simp [__eo_invoke_cmd_step_pop, hEq, push_proven_eq_stuck_of_eq_stuck, checkerShapeInvariant]
      | assume A =>
          have hTail : stateAssumptionTail cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          have hStuck : __eo_invoke_cmd_step_pop root cur r args premises = CState.Stuck :=
            invoke_cmd_step_pop_of_assumptionTail root cur r args premises hTail
          simp [__eo_invoke_cmd_step_pop, hStuck, checkerShapeInvariant]
      | proven P =>
          have hTailSuffix : stateAssumptionSuffix cur := by
            simpa [stateAssumptionSuffix] using hSuffix
          simpa [__eo_invoke_cmd_step_pop] using ih r args premises hTailSuffix

theorem invoke_cmd_step_pop_preserves_shapeInvariant
    (s : CState) (r : CRule) (args : CArgList) (premises : CIndexList) :
  stateAssumptionSuffix s ->
  checkerShapeInvariant (__eo_invoke_cmd_step_pop s s r args premises) :=
by
  intro hSuffix
  exact invoke_cmd_step_pop_preserves_shapeInvariant_aux s s r args premises hSuffix

set_option linter.unusedSimpArgs false in
theorem invoke_cmd_preserves_localTruthInvariant_nonstuck (M : SmtModel) :
  forall _hM : model_total_typed M,
  forall s : CState, forall c : CCmd,
    checkerLocalTruthInvariant M s ->
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    cmdTranslationOk c ->
    stateAssumptionSuffix s ->
    s ≠ CState.Stuck ->
    checkerLocalTruthInvariant M (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hsTy hsTrans hCmdTrans hSuffix hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          change checkerLocalTruthInvariant M (__eo_push_assume A CState.nil)
          exact push_assume_preserves_localTruthInvariant M CState.nil A hs
      | cons so s =>
          change checkerLocalTruthInvariant M (__eo_push_assume A (CState.cons so s))
          exact push_assume_preserves_localTruthInvariant M (CState.cons so s) A hs
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerLocalTruthInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerLocalTruthInvariant]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerLocalTruthInvariant]
          | proven F =>
              cases hEq : __eo_eq F proven <;>
                try
                  (simp [__eo_invoke_cmd, __eo_push_proven_check,
                    hEq, checkerLocalTruthInvariant])
              case Boolean b =>
                cases b with
                | false =>
                    simp [__eo_invoke_cmd, __eo_push_proven_check,
                      hEq, checkerLocalTruthInvariant]
                | true =>
                    simp [__eo_invoke_cmd, __eo_push_proven_check,
                      hEq, checkerLocalTruthInvariant] at hs ⊢
                    exact hs
  | step r args premises =>
      exact invoke_step_preserves_localTruthInvariant M hM s hNotStuck r args premises
        hs hsTy hsTrans hCmdTrans
  | step_pop r args premises =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_localTruthInvariant M hM CState.nil r args premises hs hsTy hsTrans hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_localTruthInvariant M hM (CState.cons so s) r args premises hs hsTy hsTrans hSuffix
      | Stuck =>
          exact False.elim (hNotStuck rfl)

set_option linter.unusedSimpArgs false in
theorem invoke_cmd_preserves_shapeInvariant_nonstuck :
  forall s : CState, forall c : CCmd,
    checkerShapeInvariant s ->
    s ≠ CState.Stuck ->
    checkerShapeInvariant (__eo_invoke_cmd s c)
:=
by
  intro s c hShape hNotStuck
  have hSuffix : stateAssumptionSuffix s :=
    suffix_of_checkerShapeInvariant_nonstuck hShape hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          by_cases hTy : __eo_typeof A = Term.Bool
          · simp [__eo_invoke_cmd, push_assume_eq_cons_of_typeof_bool, hTy, checkerShapeInvariant,
              stateAssumptionSuffix]
          · simp [__eo_invoke_cmd, push_assume_eq_stuck_of_typeof_ne_bool, hTy, checkerShapeInvariant]
      | cons so s =>
          by_cases hTy : __eo_typeof A = Term.Bool
          · simpa [__eo_invoke_cmd, push_assume_eq_cons_of_typeof_bool, hTy, checkerShapeInvariant] using hSuffix
          · simp [__eo_invoke_cmd, push_assume_eq_stuck_of_typeof_ne_bool, hTy, checkerShapeInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerShapeInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerShapeInvariant]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerShapeInvariant]
          | proven F =>
              have hSuffixTail : stateAssumptionSuffix s := by
                simpa [stateAssumptionSuffix] using hSuffix
              cases hEq : __eo_eq F proven <;>
                try
                  (simp [__eo_invoke_cmd, __eo_push_proven_check,
                    hEq, checkerShapeInvariant])
              case Boolean b =>
                cases b with
                | false =>
                    simp [__eo_invoke_cmd, __eo_push_proven_check,
                      hEq, checkerShapeInvariant]
                | true =>
                    simpa [__eo_invoke_cmd, __eo_push_proven_check,
                      hEq, checkerShapeInvariant, stateAssumptionSuffix] using
                      hSuffixTail
  | step r args premises =>
      cases s with
      | nil =>
          by_cases hTy : __eo_typeof (__eo_cmd_step_proven CState.nil r args premises) = Term.Bool
          · simp [__eo_invoke_cmd, push_proven_eq_cons_of_typeof_bool, hTy, checkerShapeInvariant,
              stateAssumptionSuffix]
          · simp [__eo_invoke_cmd, push_proven_eq_stuck_of_typeof_ne_bool, hTy, checkerShapeInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          by_cases hTy : __eo_typeof (__eo_cmd_step_proven (CState.cons so s) r args premises) = Term.Bool
          · simpa [__eo_invoke_cmd, push_proven_eq_cons_of_typeof_bool, hTy, checkerShapeInvariant] using hSuffix
          · simp [__eo_invoke_cmd, push_proven_eq_stuck_of_typeof_ne_bool, hTy, checkerShapeInvariant]
  | step_pop r args premises =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using invoke_cmd_step_pop_preserves_shapeInvariant CState.nil r args premises hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_shapeInvariant (CState.cons so s) r args premises hSuffix
      | Stuck =>
          exact False.elim (hNotStuck rfl)

set_option linter.unusedSimpArgs false in
theorem invoke_cmd_preserves_truthInvariant_nonstuck (M : SmtModel) :
  forall _hM : model_total_typed M,
  forall s : CState, forall c : CCmd,
    checkerLocalTruthInvariant M s ->
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    cmdTranslationOk c ->
    stateAssumptionSuffix s ->
    s ≠ CState.Stuck ->
    checkerTruthInvariant M (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hsTy hsTrans hCmdTrans hSuffix hNotStuck
  exact checkerLocalTruthInvariant_implies_truthInvariant M <|
    invoke_cmd_preserves_localTruthInvariant_nonstuck M hM s c hs hsTy hsTrans hCmdTrans hSuffix hNotStuck

theorem invoke_cmd_preserves_typeInvariant_nonstuck :
  forall s : CState, forall c : CCmd,
    checkerTypeInvariant s ->
    stateAssumptionSuffix s ->
    s ≠ CState.Stuck ->
    checkerTypeInvariant (__eo_invoke_cmd s c)
:=
by
  intro s c hs hSuffix hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          change checkerTypeInvariant (__eo_push_assume A CState.nil)
          exact push_assume_preserves_typeInvariant CState.nil A hs
      | cons so s =>
          change checkerTypeInvariant (__eo_push_assume A (CState.cons so s))
          exact push_assume_preserves_typeInvariant (CState.cons so s) A hs
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTypeInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTypeInvariant]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTypeInvariant]
          | proven F =>
              have hHead := checkerTypeInvariant_head_proven F s hs
              have hTail : checkerTypeInvariant s := checkerTypeInvariant_tail hs
              cases hEq : __eo_eq F proven with
              | Boolean b =>
                  cases b with
                  | false =>
                      simp [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTypeInvariant]
                  | true =>
                      simpa [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTypeInvariant,
                        hHead.1, hHead.2] using hTail
              | _ =>
                  simp [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTypeInvariant]
  | step r args premises =>
      exact invoke_step_preserves_typeInvariant s hNotStuck r args premises hs
  | step_pop r args premises =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_typeInvariant CState.nil r args premises hs hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_typeInvariant (CState.cons so s) r args premises hs hSuffix
      | Stuck =>
          exact False.elim (hNotStuck rfl)

theorem invoke_cmd_preserves_translationInvariant_nonstuck (M : SmtModel) :
  forall _hM : model_total_typed M,
  forall s : CState, forall c : CCmd,
    checkerLocalTruthInvariant M s ->
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    cmdTranslationOk c ->
    stateAssumptionSuffix s ->
    s ≠ CState.Stuck ->
    checkerTranslationInvariant (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hsTy hsTrans hCmdTrans hSuffix hNotStuck
  cases c with
  | assume_push A =>
      cases s with
      | nil =>
          change checkerTranslationInvariant (__eo_push_assume A CState.nil)
          exact push_assume_preserves_translationInvariant CState.nil A hsTrans
            (by simpa [cmdTranslationOk] using hCmdTrans)
      | cons so s =>
          change checkerTranslationInvariant (__eo_push_assume A (CState.cons so s))
          exact push_assume_preserves_translationInvariant (CState.cons so s) A hsTrans
            (by simpa [cmdTranslationOk] using hCmdTrans)
      | Stuck =>
          exact False.elim (hNotStuck rfl)
  | check_proven proven =>
      cases s with
      | nil =>
          simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTranslationInvariant]
      | Stuck =>
          exact False.elim (hNotStuck rfl)
      | cons so s =>
          cases so with
          | assume A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTranslationInvariant]
          | assume_push A =>
              simp [__eo_invoke_cmd, __eo_invoke_cmd_check_proven, checkerTranslationInvariant]
          | proven F =>
              have hHead := checkerTranslationInvariant_head_proven F s hsTrans
              have hTail : checkerTranslationInvariant s := checkerTranslationInvariant_tail hsTrans
              cases hEq : __eo_eq F proven with
              | Boolean b =>
                  cases b with
                  | false =>
                      simp [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTranslationInvariant]
                  | true =>
                      simpa [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTranslationInvariant] using
                        (show RuleProofs.eo_has_smt_translation F ∧ checkerTranslationInvariant s from ⟨hHead, hTail⟩)
              | _ =>
                  simp [__eo_invoke_cmd, __eo_push_proven_check, hEq, checkerTranslationInvariant]
  | step r args premises =>
      exact invoke_step_preserves_translationInvariant M hM s hNotStuck r args premises
        hs hsTy hsTrans hCmdTrans
  | step_pop r args premises =>
      cases s with
      | nil =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_translationInvariant CState.nil r args premises hsTy hsTrans hSuffix
      | cons so s =>
          simpa [__eo_invoke_cmd] using
            invoke_cmd_step_pop_preserves_translationInvariant (CState.cons so s) r args premises hsTy hsTrans hSuffix
      | Stuck =>
          exact False.elim (hNotStuck rfl)

theorem invoke_cmd_preserves_stateInvariant_nonstuck (M : SmtModel) :
  forall _hM : model_total_typed M,
  forall s : CState, forall c : CCmd,
    checkerStateInvariant M s ->
    cmdTranslationOk c ->
    s ≠ CState.Stuck ->
    checkerStateInvariant M (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hCmdTrans hNotStuck
  have hLocal :
      checkerLocalTruthInvariant M (__eo_invoke_cmd s c) :=
    invoke_cmd_preserves_localTruthInvariant_nonstuck M hM s c hs.2.1 hs.2.2.1 hs.2.2.2 hCmdTrans
      (suffix_of_checkerShapeInvariant_nonstuck hs.1 hNotStuck) hNotStuck
  have hType :
      checkerTypeInvariant (__eo_invoke_cmd s c) :=
    invoke_cmd_preserves_typeInvariant_nonstuck s c hs.2.2.1
      (suffix_of_checkerShapeInvariant_nonstuck hs.1 hNotStuck) hNotStuck
  have hTrans :
      checkerTranslationInvariant (__eo_invoke_cmd s c) :=
    invoke_cmd_preserves_translationInvariant_nonstuck M hM s c hs.2.1 hs.2.2.1 hs.2.2.2
      hCmdTrans (suffix_of_checkerShapeInvariant_nonstuck hs.1 hNotStuck) hNotStuck
  have hShape :
      checkerShapeInvariant (__eo_invoke_cmd s c) :=
    invoke_cmd_preserves_shapeInvariant_nonstuck s c hs.1 hNotStuck
  exact ⟨hShape, hLocal, hType, hTrans⟩

theorem invoke_cmd_preserves_stateInvariant (M : SmtModel) :
  forall _hM : model_total_typed M,
  forall s : CState, forall c : CCmd,
    checkerStateInvariant M s ->
    cmdTranslationOk c ->
    checkerStateInvariant M (__eo_invoke_cmd s c)
:=
by
  intro hM s c hs hCmdTrans
  by_cases hStuck : s = CState.Stuck
  · subst hStuck
    have hInvStuck : checkerStateInvariant M CState.Stuck := by
      exact ⟨trivial, checkerLocalTruthInvariant_stuck M, checkerTypeInvariant_stuck,
        checkerTranslationInvariant_stuck⟩
    cases c <;> simpa [__eo_invoke_cmd, checkerStateInvariant] using hInvStuck
  · exact invoke_cmd_preserves_stateInvariant_nonstuck M hM s c hs hCmdTrans hStuck

theorem invoke_cmd_list_preserves_stateInvariant (M : SmtModel) :
  forall _hM : model_total_typed M,
  forall s : CState, forall cs : CCmdList,
    checkerStateInvariant M s ->
    CmdListTranslationOk cs ->
    checkerStateInvariant M (__eo_invoke_cmd_list s cs)
:=
by
  intro hM s cs
  induction cs generalizing s with
  | nil =>
      intro hs hTrans
      simpa [__eo_invoke_cmd_list] using hs
  | cons c cs ih =>
      intro hs hTrans
      cases hTrans with
      | cons _ _ hCmd hTail =>
      have hstep : checkerStateInvariant M (__eo_invoke_cmd s c) :=
        invoke_cmd_preserves_stateInvariant M hM s c hs hCmd
      simpa [__eo_invoke_cmd_list] using ih (__eo_invoke_cmd s c) hstep hTail

/- correctness theorem for the checker -/
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  TypedAssumptionList F ->
  TranslatableAssumptionList F ->
  CmdListTranslationOk pf ->
  (eo_is_refutation F pf) ->
  (forall M : SmtModel, model_total_typed M -> ¬ (eo_interprets M F true)) :=
by
  intro hTyped hFTrans hPfTrans hRef M hM hF
  cases hRef with
  | intro hChecker =>
      let S0 := __eo_invoke_assume_list CState.nil F
      let S1 := __eo_invoke_cmd_list S0 pf
      have hValid : ValidAssumptionList F :=
        validAssumptionList_of_checker_true F pf hChecker
      have hInit : checkerStateInvariant M S0 := by
        simpa [S0] using checkerStateInvariant_after_assume_list M F hValid hTyped hFTrans
      have hSteps : checkerStateInvariant M S1 := by
        simpa [S0, S1] using invoke_cmd_list_preserves_stateInvariant M hM S0 pf hInit hPfTrans
      exact refutation_contradiction_of_truthInvariant M F pf hF
        (checkerLocalTruthInvariant_implies_truthInvariant M hSteps.2.1) hChecker
