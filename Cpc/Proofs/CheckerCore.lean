import Cpc.Spec
import Cpc.Logos
import Cpc.Proofs.Assumptions
import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 0

/-- Inductive predicate for assumption terms that are well-formed `and`-chains ending in `true`. -/
inductive ValidAssumptionList : Term -> Prop
  | base : ValidAssumptionList (Term.Boolean true)
  | step (A rest : Term) : ValidAssumptionList rest ->
      ValidAssumptionList (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest)

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

/-- Predicate asserting that a checker state is structurally well-formed and not `Stuck`. -/
def stateOk : CState -> Prop
  | CState.nil => True
  | CState.cons _ s => stateOk s
  | CState.Stuck => False

/-- Simplifies EO-to-SMT translation for `true_eq`. -/
private theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rfl

/-- Simplifies EO-to-SMT translation for `false_eq`. -/
private theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rfl

/-- Simplifies EO-to-SMT translation for `stuck_eq`. -/
private theorem eo_to_smt_stuck_eq :
    __eo_to_smt Term.Stuck = SmtTerm.None := by
  rfl

/-- Simplifies EO-to-SMT translation for `and_eq`. -/
private theorem eo_to_smt_and_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

/-- Simplifies EO-to-SMT translation for `imp_eq`. -/
private theorem eo_to_smt_imp_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) =
      SmtTerm.imp (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

/-- Lemma about `eo_has_smt_translation_true`. -/
private theorem eo_has_smt_translation_true :
    RuleProofs.eo_has_smt_translation (Term.Boolean true) := by
  rw [RuleProofs.eo_has_smt_translation, eo_to_smt_true_eq, __smtx_typeof.eq_1]
  decide

/-- Characterizes EO interpretation in terms of the translated SMT interpretation. -/
theorem eo_interprets_iff_smt_interprets (M : SmtModel) (t : Term) (b : Bool) :
  eo_interprets M t b ↔ smt_interprets M (__eo_to_smt t) b :=
by
  exact RuleProofs.eo_interprets_iff_smt_interprets M t b

/-- Shows that the EO term `true` is interpreted as `true` in every model. -/
theorem eo_interprets_true (M : SmtModel) :
  eo_interprets M (Term.Boolean true) true :=
by
  exact RuleProofs.eo_interprets_true M

/-- Lemma about `eo_interprets_false_true_absurd`. -/
theorem eo_interprets_false_true_absurd (M : SmtModel) :
  ¬ eo_interprets M (Term.Boolean false) true :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_false_eq]
  intro h
  cases h with
  | intro_true _ hEval =>
      simp [__smtx_model_eval] at hEval

/-- Lemma about `eo_interprets_stuck_false_absurd`. -/
theorem eo_interprets_stuck_false_absurd (M : SmtModel) :
  ¬ eo_interprets M Term.Stuck false :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq]
  intro h
  cases h with
  | intro_false hty _ =>
      simp at hty

/-- Lemma about `eo_interprets_stuck_true_absurd`. -/
theorem eo_interprets_stuck_true_absurd (M : SmtModel) :
  ¬ eo_interprets M Term.Stuck true :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq]
  intro h
  cases h with
  | intro_true hty _ =>
      simp at hty

/-- Lemma about `eo_interprets_true_not_false`. -/
theorem eo_interprets_true_not_false (M : SmtModel) (t : Term) :
  eo_interprets M t true ->
  ¬ eo_interprets M t false :=
by
  exact RuleProofs.eo_interprets_true_not_false M t

/-- Left-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M A true :=
by
  exact RuleProofs.eo_interprets_and_left M A B

/-- Right-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M B true :=
by
  exact RuleProofs.eo_interprets_and_right M A B

/-- Introduction lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true :=
by
  exact RuleProofs.eo_interprets_and_intro M A B

/-- Elimination lemma for `eo_interprets_imp`. -/
theorem eo_interprets_imp_elim (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true ->
  eo_interprets M A true ->
  eo_interprets M B true :=
by
  exact RuleProofs.eo_interprets_imp_elim M A B

/-- Introduction lemma for `eo_interprets_imp`. -/
theorem eo_interprets_imp_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) true :=
by
  exact RuleProofs.eo_interprets_imp_intro M A B

/-- Left-projection lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) false ->
  eo_interprets M A true :=
by
  exact RuleProofs.eo_interprets_imp_false_left M A B

/-- Right-projection lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) false ->
  eo_interprets M B false :=
by
  exact RuleProofs.eo_interprets_imp_false_right M A B

/-- Introduction lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B false ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.imp) A) B) false :=
by
  exact RuleProofs.eo_interprets_imp_false_intro M A B

/-- Derives `eo_interprets_and_false_left` from `right_not_false`. -/
theorem eo_interprets_and_false_left_of_right_not_false (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) false ->
  ¬ eo_interprets M B false ->
  eo_interprets M A false :=
by
  intro hAnd hBNotFalse
  rw [eo_interprets_iff_smt_interprets] at hAnd hBNotFalse ⊢
  rw [eo_to_smt_and_eq A B] at hAnd
  cases hAnd with
  | intro_false hty hEval =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
          (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false := by
        rw [__smtx_model_eval.eq_8] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b
          · simp [SmtEval.native_and] at hEval
            have hBFalse : smt_interprets M (__eo_to_smt B) false :=
              smt_interprets.intro_false M (__eo_to_smt B) htyB hBeval
            exact False.elim (hBNotFalse hBFalse)
          · simp [SmtEval.native_and] at hEval
            simp
          · simp [SmtEval.native_and] at hEval
            have hBFalse : smt_interprets M (__eo_to_smt B) false :=
              smt_interprets.intro_false M (__eo_to_smt B) htyB hBeval
            exact False.elim (hBNotFalse hBFalse)
          · simp [SmtEval.native_and] at hEval
      exact smt_interprets.intro_false M (__eo_to_smt A) htyA hEvalA

/-- Derives `eo_interprets_and_false_right_true` from `left_false_and_right_not_false`. -/
theorem eo_interprets_and_false_right_true_of_left_false_and_right_not_false
    (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) false ->
  eo_interprets M A false ->
  ¬ eo_interprets M B false ->
  eo_interprets M B true :=
by
  intro hAnd hAFalse hBNotFalse
  rw [eo_interprets_iff_smt_interprets] at hAnd hAFalse hBNotFalse ⊢
  rw [eo_to_smt_and_eq A B] at hAnd
  cases hAnd with
  | intro_false htyAnd hEvalAnd =>
      cases hAFalse with
      | intro_false htyA hEvalA =>
          have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
            have hNN : term_has_non_none_type
                (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
              unfold term_has_non_none_type
              rw [htyAnd]
              simp
            exact (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
              (typeof_and_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2
          have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
            rw [__smtx_model_eval.eq_8] at hEvalAnd
            cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
              simp [hEvalA, hBeval, __smtx_model_eval_and] at hEvalAnd
            case Boolean b =>
              cases b with
              | false =>
                  have hBFalse : smt_interprets M (__eo_to_smt B) false :=
                    smt_interprets.intro_false M (__eo_to_smt B) htyB hBeval
                  exact False.elim (hBNotFalse hBFalse)
              | true =>
                  simp
          exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

/-- Extracts the conjunction of active assumptions from a checker state. -/
def stateAssumes : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.assume F) s =>
      Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (stateAssumes s)
  | CState.cons _ s => stateAssumes s
  | CState.Stuck => Term.Stuck

/-- Extracts the list of assumptions introduced by `assume_push` commands in a checker state. -/
def statePushes : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.assume_push F) s =>
      Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (statePushes s)
  | CState.cons _ s => statePushes s
  | CState.Stuck => Term.Stuck

/-- Extracts the list of proven terms stored in a checker state. -/
def stateProvens : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.proven F) s =>
      Term.Apply (Term.Apply (Term.UOp UserOp.and) F) (stateProvens s)
  | CState.cons _ s => stateProvens s
  | CState.Stuck => Term.Stuck

/-
Because the checker pushes new entries at the head of the state, the initial
assumptions from `__eo_invoke_assume_list` live in a tail block of reachable
states. This is the structural fact that lets `step_pop` discard a prefix
without changing the assumption component.
-/
/-- Predicate asserting that a state appears as the tail of another checker state. -/
def stateAssumptionTail : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume _) s => stateAssumptionTail s
  | _ => False

/-- Predicate asserting that a state occurs as a suffix reached by repeatedly dropping assumptions. -/
def stateAssumptionSuffix : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume _) s => stateAssumptionTail s
  | CState.cons _ s => stateAssumptionSuffix s
  | CState.Stuck => False

/-- Derives `stateAssumptionSuffix` from `tail`. -/
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

/- `step_pop` traverses only across proved entries before it either finds the
   leading `assume_push` to discharge or falls into the assumption tail. This
   relation records the suffixes reachable by discarding only a proved prefix. -/
/-- Inductive relation describing suffix states reachable by repeated `step_pop` operations. -/
inductive stateStepPopSuffix : CState -> CState -> Prop
  | refl (s : CState) : stateStepPopSuffix s s
  | proven (P : Term) {cur root : CState} :
      stateStepPopSuffix cur root ->
      stateStepPopSuffix cur (CState.cons (CStateObj.proven P) root)

/-- Transitivity lemma for `stateStepPopSuffix`. -/
theorem stateStepPopSuffix_trans :
  forall {s t u : CState},
    stateStepPopSuffix s t ->
    stateStepPopSuffix t u ->
    stateStepPopSuffix s u
:=
by
  intro s t u hst htu
  induction htu generalizing s with
  | refl _ =>
      exact hst
  | proven P htu ih =>
      exact stateStepPopSuffix.proven P (ih hst)

/-- Derives `stateAssumes_eq` from `stateStepPopSuffix`. -/
theorem stateAssumes_eq_of_stateStepPopSuffix :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    stateAssumes root = stateAssumes cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      rfl
  | proven P hSuffix ih =>
      simpa [stateAssumes] using ih

/-- Derives `statePushes_eq` from `stateStepPopSuffix`. -/
theorem statePushes_eq_of_stateStepPopSuffix :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    statePushes root = statePushes cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      rfl
  | proven P hSuffix ih =>
      simpa [statePushes] using ih

/-- Derives `stateAssumes_eq` from `stateStepPopSuffix_assume_push`. -/
theorem stateAssumes_eq_of_stateStepPopSuffix_assume_push
    {root tail : CState} {A : Term} :
  stateStepPopSuffix (CState.cons (CStateObj.assume_push A) tail) root ->
  stateAssumes root = stateAssumes tail :=
by
  intro hSuffix
  simpa [stateAssumes] using stateAssumes_eq_of_stateStepPopSuffix hSuffix

/-- Derives `statePushes_eq` from `stateStepPopSuffix_assume_push`. -/
theorem statePushes_eq_of_stateStepPopSuffix_assume_push
    {root tail : CState} {A : Term} :
  stateStepPopSuffix (CState.cons (CStateObj.assume_push A) tail) root ->
  statePushes root = Term.Apply (Term.Apply (Term.UOp UserOp.and) A) (statePushes tail) :=
by
  intro hSuffix
  simpa [statePushes] using statePushes_eq_of_stateStepPopSuffix hSuffix

/-- Lemma about `stateOk_not_stuck`. -/
theorem stateOk_not_stuck {s : CState} :
  stateOk s -> s ≠ CState.Stuck :=
by
  intro hOk hStuck
  subst hStuck
  simp [stateOk] at hOk

/-- Establishes an equality relating `eo` and `bool_true_iff`. -/
@[simp] theorem eo_eq_bool_true_iff (t : Term) :
  __eo_eq t Term.Bool = Term.Boolean true ↔ t = Term.Bool :=
by
  cases t <;> simp [__eo_eq, native_teq]

/-- Lemma about `typeof_stuck_ne_bool`. -/
theorem typeof_stuck_ne_bool :
  __eo_typeof Term.Stuck ≠ Term.Bool :=
by
  native_decide

/-- Establishes an equality relating `eo_is_bool_type` and `true_iff`. -/
@[simp] theorem eo_is_bool_type_eq_true_iff (t : Term) :
  __eo_is_bool_type t = Term.Boolean true ↔ __eo_typeof t = Term.Bool :=
by
  by_cases hStuck : t = Term.Stuck
  · subst hStuck
    constructor
    · simp [__eo_is_bool_type]
    · exact False.elim ∘ typeof_stuck_ne_bool
  · simp [__eo_is_bool_type, eo_eq_bool_true_iff]

/-- Derives `eo_is_bool_type_eq_true` from `typeof_bool`. -/
@[simp] theorem eo_is_bool_type_eq_true_of_typeof_bool (t : Term) :
  __eo_typeof t = Term.Bool ->
  __eo_is_bool_type t = Term.Boolean true :=
by
  intro hTy
  exact (eo_is_bool_type_eq_true_iff t).2 hTy

/-- The combined guard used for assumptions and pushed assumptions. -/
def assumptionCheckGuard (A : Term) : Term :=
  __eo_and (__eo_is_bool_type A) (__eo_is_closed A)

/-- Splits a successful assumption guard. -/
theorem assumptionCheckGuard_eq_true_cases (A : Term) :
  assumptionCheckGuard A = Term.Boolean true ->
  __eo_is_bool_type A = Term.Boolean true ∧ __eo_is_closed A = Term.Boolean true :=
by
  intro h
  unfold assumptionCheckGuard at h
  cases hb : __eo_is_bool_type A <;> cases hc : __eo_is_closed A <;>
    simp [__eo_and, hb, hc, native_and, __eo_requires, native_ite, native_teq] at h
  case Binary.Binary =>
    split at h <;> contradiction
  case Boolean.Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp at h ⊢

/-- Simplifies the successful checked assume push. -/
theorem push_assume_check_true (A : Term) (s : CState) :
  __eo_push_assume_check (Term.Boolean true) A s =
    CState.cons (CStateObj.assume_push A) s :=
by
  simp [__eo_push_assume_check]

/-- Derives `push_assume_eq_cons` from a successful combined guard. -/
theorem push_assume_eq_cons_of_guard_true (A : Term) (s : CState) :
  assumptionCheckGuard A = Term.Boolean true ->
  __eo_push_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume_push A) s :=
by
  intro hGuard
  change __eo_push_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume_push A) s
  rw [hGuard]
  simp [__eo_push_assume_check]

/-- Derives `push_assume_eq_stuck` from `eq_stuck`. -/
theorem push_assume_eq_stuck_of_eq_stuck (s : CState) :
  __eo_push_assume_check (assumptionCheckGuard Term.Stuck) Term.Stuck s =
    CState.Stuck :=
by
  simp [assumptionCheckGuard, __eo_push_assume_check, __eo_is_bool_type, __eo_and]

/-- Derives `push_assume_eq_stuck` from an unsuccessful combined guard. -/
theorem push_assume_eq_stuck_of_guard_ne_true (A : Term) (s : CState) :
  assumptionCheckGuard A ≠ Term.Boolean true ->
  __eo_push_assume_check (assumptionCheckGuard A) A s = CState.Stuck :=
by
  intro hGuard
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_assume_check]
  case Boolean b =>
    cases b <;> simp [hCheck] at hGuard ⊢

/-- Derives `push_assume_eq_stuck` from `typeof_ne_bool`. -/
theorem push_assume_eq_stuck_of_typeof_ne_bool (A : Term) (s : CState) :
  __eo_typeof A ≠ Term.Bool ->
  __eo_push_assume_check (assumptionCheckGuard A) A s = CState.Stuck :=
by
  intro hTy
  apply push_assume_eq_stuck_of_guard_ne_true
  intro hGuard
  exact hTy ((eo_is_bool_type_eq_true_iff A).1
    (assumptionCheckGuard_eq_true_cases A hGuard).1)

/-- Derives `assume_push_arg_ne_stuck` from `stateOk`. -/
theorem assume_push_arg_ne_stuck_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) -> A ≠ Term.Stuck :=
by
  intro hOk hA
  subst hA
  simp [push_assume_eq_stuck_of_eq_stuck, stateOk] at hOk

/-- Shows that `push_assume` reflects `stateOk`. -/
theorem push_assume_reflects_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) -> stateOk s :=
by
  intro hOk
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_assume_check, hCheck, stateOk] at hOk
  case Boolean b =>
    cases b
    · simp [stateOk] at hOk
    · simpa [__eo_push_assume_check, hCheck, stateOk] using hOk

/-- Derives the successful combined guard from `stateOk`. -/
theorem push_assume_guard_true_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) ->
  assumptionCheckGuard A = Term.Boolean true :=
by
  intro hOk
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_assume_check, hCheck, stateOk] at hOk
  case Boolean b =>
    cases b <;> simp [stateOk] at hOk ⊢

/-- Derives `push_assume_typeof_bool` from `stateOk`. -/
theorem push_assume_typeof_bool_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) -> __eo_typeof A = Term.Bool :=
by
  intro hOk
  have hGuard := push_assume_guard_true_of_stateOk A s hOk
  have hBool := (assumptionCheckGuard_eq_true_cases A hGuard).1
  exact (eo_is_bool_type_eq_true_iff A).1 hBool

/-- Derives `__eo_is_closed` from a successful checked assume push. -/
theorem push_assume_closed_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) ->
  __eo_is_closed A = Term.Boolean true :=
by
  intro hOk
  have hGuard := push_assume_guard_true_of_stateOk A s hOk
  exact (assumptionCheckGuard_eq_true_cases A hGuard).2

/-- Derives `push_assume_eq_cons` from `stateOk`. -/
theorem push_assume_eq_cons_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume_check (assumptionCheckGuard A) A s) ->
  __eo_push_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume_push A) s :=
by
  intro hOk
  exact push_assume_eq_cons_of_guard_true A s
    (push_assume_guard_true_of_stateOk A s hOk)

/-- Simplifies the successful checked input-assumption push. -/
theorem push_input_assume_check_true (A : Term) (s : CState) :
  __eo_push_input_assume_check (Term.Boolean true) A s =
    CState.cons (CStateObj.assume A) s :=
by
  simp [__eo_push_input_assume_check]

/-- Derives `push_input_assume_eq_cons` from a successful combined guard. -/
theorem push_input_assume_eq_cons_of_guard_true (A : Term) (s : CState) :
  assumptionCheckGuard A = Term.Boolean true ->
  __eo_push_input_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume A) s :=
by
  intro hGuard
  change __eo_push_input_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume A) s
  rw [hGuard]
  simp [__eo_push_input_assume_check]

/-- Derives `push_input_assume_eq_stuck` from `eq_stuck`. -/
theorem push_input_assume_eq_stuck_of_eq_stuck (s : CState) :
  __eo_push_input_assume_check (assumptionCheckGuard Term.Stuck) Term.Stuck s =
    CState.Stuck :=
by
  simp [assumptionCheckGuard, __eo_push_input_assume_check, __eo_is_bool_type, __eo_and]

/-- Derives `push_input_assume_eq_stuck` from an unsuccessful combined guard. -/
theorem push_input_assume_eq_stuck_of_guard_ne_true (A : Term) (s : CState) :
  assumptionCheckGuard A ≠ Term.Boolean true ->
  __eo_push_input_assume_check (assumptionCheckGuard A) A s = CState.Stuck :=
by
  intro hGuard
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_input_assume_check]
  case Boolean b =>
    cases b <;> simp [hCheck] at hGuard ⊢

/-- Derives `push_input_assume_eq_stuck` from `typeof_ne_bool`. -/
theorem push_input_assume_eq_stuck_of_typeof_ne_bool (A : Term) (s : CState) :
  __eo_typeof A ≠ Term.Bool ->
  __eo_push_input_assume_check (assumptionCheckGuard A) A s = CState.Stuck :=
by
  intro hTy
  apply push_input_assume_eq_stuck_of_guard_ne_true
  intro hGuard
  exact hTy ((eo_is_bool_type_eq_true_iff A).1
    (assumptionCheckGuard_eq_true_cases A hGuard).1)

/-- Shows that `push_input_assume` reflects `stateOk`. -/
theorem push_input_assume_reflects_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) -> stateOk s :=
by
  intro hOk
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_input_assume_check, hCheck, stateOk] at hOk
  case Boolean b =>
    cases b
    · simp [stateOk] at hOk
    · simpa [__eo_push_input_assume_check, hCheck, stateOk] using hOk

/-- Derives the successful combined guard from `stateOk`. -/
theorem push_input_assume_guard_true_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) ->
  assumptionCheckGuard A = Term.Boolean true :=
by
  intro hOk
  cases hCheck : assumptionCheckGuard A <;>
    simp [__eo_push_input_assume_check, hCheck, stateOk] at hOk
  case Boolean b =>
    cases b <;> simp [stateOk] at hOk ⊢

/-- Derives `push_input_assume_typeof_bool` from `stateOk`. -/
theorem push_input_assume_typeof_bool_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) ->
  __eo_typeof A = Term.Bool :=
by
  intro hOk
  have hGuard := push_input_assume_guard_true_of_stateOk A s hOk
  have hBool := (assumptionCheckGuard_eq_true_cases A hGuard).1
  exact (eo_is_bool_type_eq_true_iff A).1 hBool

/-- Derives `__eo_is_closed` from a successful checked input assumption. -/
theorem push_input_assume_closed_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) ->
  __eo_is_closed A = Term.Boolean true :=
by
  intro hOk
  have hGuard := push_input_assume_guard_true_of_stateOk A s hOk
  exact (assumptionCheckGuard_eq_true_cases A hGuard).2

/-- Derives `push_input_assume_eq_cons` from `stateOk`. -/
theorem push_input_assume_eq_cons_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A s) ->
  __eo_push_input_assume_check (assumptionCheckGuard A) A s =
    CState.cons (CStateObj.assume A) s :=
by
  intro hOk
  exact push_input_assume_eq_cons_of_guard_true A s
    (push_input_assume_guard_true_of_stateOk A s hOk)

/-- Derives `push_proven_eq_cons` from `typeof_bool`. -/
@[simp] theorem push_proven_eq_cons_of_typeof_bool (P : Term) (s : CState) :
  __eo_typeof P = Term.Bool ->
  __eo_push_proven P s = CState.cons (CStateObj.proven P) s :=
by
  intro hTy
  simp [__eo_push_proven, __eo_push_proven_check,
    eo_is_bool_type_eq_true_of_typeof_bool, hTy]

/-- Derives `push_proven_eq_stuck` from `eq_stuck`. -/
@[simp] theorem push_proven_eq_stuck_of_eq_stuck (s : CState) :
  __eo_push_proven Term.Stuck s = CState.Stuck :=
by
  simp [__eo_push_proven, __eo_push_proven_check, __eo_is_bool_type]

/-- Derives `push_proven_eq_stuck` from `typeof_ne_bool`. -/
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

/-- Derives `push_proven_typeof_bool` from `stateOk`. -/
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

/-- Derives `push_proven_eq_cons` from `stateOk`. -/
theorem push_proven_eq_cons_of_stateOk (P : Term) (s : CState) :
  stateOk (__eo_push_proven P s) ->
  __eo_push_proven P s = CState.cons (CStateObj.proven P) s :=
by
  intro hOk
  exact push_proven_eq_cons_of_typeof_bool P s (push_proven_typeof_bool_of_stateOk P s hOk)

/-- Shows that `push_proven` reflects `stateOk`. -/
theorem push_proven_reflects_stateOk (P : Term) (s : CState) :
  stateOk (__eo_push_proven P s) -> stateOk s :=
by
  intro hOk
  have hTy := push_proven_typeof_bool_of_stateOk P s hOk
  simpa [push_proven_eq_cons_of_typeof_bool, hTy, stateOk] using hOk

/-- Establishes an equality relating `invoke_cmd_check_proven_proven` and `push_proven_check`. -/
@[simp] theorem invoke_cmd_check_proven_proven_eq_push_proven_check
    (F proven : Term) (s : CState) :
  __eo_invoke_cmd_check_proven (CState.cons (CStateObj.proven F) s) proven =
    __eo_push_proven_check (__eo_eq F proven) F s :=
by
  rw [__eo_invoke_cmd_check_proven]

/-- Establishes an equality relating `invoke_cmd_check_proven_proven` and `push_proven_check_cmd`. -/
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
/-- Global truth invariant requiring every proven term in the state to evaluate to `true`. -/
def checkerTruthInvariant (M : SmtModel) : CState -> Prop
  | CState.Stuck => True
  | s =>
      ∀ n : native_Int,
        eo_interprets M (stateAssumes s) true ->
        eo_interprets M (statePushes s) true ->
        eo_interprets M (__eo_state_proven_nth s n) true

/-- Describes `checkerTruthInvariant` on the stuck state. -/
theorem checkerTruthInvariant_stuck (M : SmtModel) :
  checkerTruthInvariant M CState.Stuck :=
by
  trivial

/- Structural checker-side typing invariant.

   Every state entry recorded by the checker carries a checker-side Bool guard.
   This matches the operational checks for initial assumptions, `assume_push`,
   and `push_proven`.
-/
/-- Type invariant requiring every stored assumption and proven term to have EO Boolean type. -/
def checkerTypeInvariant : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume A) s =>
      A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool ∧ checkerTypeInvariant s
  | CState.cons (CStateObj.assume_push A) s =>
      A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool ∧ checkerTypeInvariant s
  | CState.cons (CStateObj.proven P) s =>
      P ≠ Term.Stuck ∧ __eo_typeof P = Term.Bool ∧ checkerTypeInvariant s
  | CState.Stuck => True

/-- Describes `checkerTypeInvariant` on the stuck state. -/
theorem checkerTypeInvariant_stuck :
  checkerTypeInvariant CState.Stuck :=
by
  trivial

/-- Translation invariant requiring every stored assumption and proven term to admit SMT translation. -/
def checkerTranslationInvariant : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.assume A) s =>
      RuleProofs.eo_has_smt_translation A ∧ checkerTranslationInvariant s
  | CState.cons (CStateObj.assume_push A) s =>
      RuleProofs.eo_has_smt_translation A ∧ checkerTranslationInvariant s
  | CState.cons (CStateObj.proven P) s =>
      RuleProofs.eo_has_smt_translation P ∧ checkerTranslationInvariant s
  | CState.Stuck => True

/-- Describes `checkerTranslationInvariant` on the stuck state. -/
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
/-- Local truth invariant relating each proven term to the assumptions that were active when it was derived. -/
def checkerLocalTruthInvariant (M : SmtModel) : CState -> Prop
  | CState.nil => True
  | CState.cons (CStateObj.proven P) s =>
      ContextualTruth M (stateAssumes s) (statePushes s) P ∧
      checkerLocalTruthInvariant M s
  | CState.cons _ s => checkerLocalTruthInvariant M s
  | CState.Stuck => True

/-- Describes `checkerLocalTruthInvariant` on the stuck state. -/
theorem checkerLocalTruthInvariant_stuck (M : SmtModel) :
  checkerLocalTruthInvariant M CState.Stuck :=
by
  trivial

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

/-- Shows how `checkerTypeInvariant` behaves on suffix tails. -/
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

/-- Lemma about `checkerTypeInvariant_head_assume`. -/
theorem checkerTypeInvariant_head_assume
    (A : Term) (s : CState) :
  checkerTypeInvariant (CState.cons (CStateObj.assume A) s) ->
  A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool :=
by
  intro hs
  exact ⟨hs.1, hs.2.1⟩

/-- Lemma about `checkerTypeInvariant_head_assume_push`. -/
theorem checkerTypeInvariant_head_assume_push
    (A : Term) (s : CState) :
  checkerTypeInvariant (CState.cons (CStateObj.assume_push A) s) ->
  A ≠ Term.Stuck ∧ __eo_typeof A = Term.Bool :=
by
  intro hs
  exact ⟨hs.1, hs.2.1⟩

/-- Lemma about `checkerTypeInvariant_head_proven`. -/
theorem checkerTypeInvariant_head_proven
    (P : Term) (s : CState) :
  checkerTypeInvariant (CState.cons (CStateObj.proven P) s) ->
  P ≠ Term.Stuck ∧ __eo_typeof P = Term.Bool :=
by
  intro hs
  exact ⟨hs.1, hs.2.1⟩

/-- Retrieves the `checkerTypeInvariant` fact at a given index. -/
theorem checkerTypeInvariant_at :
  forall {s : CState},
    checkerTypeInvariant s ->
    forall n : native_Int,
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
              ih (checkerTypeInvariant_tail hs) (native_zplus n (native_zneg 1))
        | assume_push A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTypeInvariant_tail hs) (native_zplus n (native_zneg 1))
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTypeInvariant_tail hs) (native_zplus n (native_zneg 1))

/-- Shows how `checkerTranslationInvariant` behaves on suffix tails. -/
theorem checkerTranslationInvariant_tail :
  forall {so : CStateObj} {s : CState},
    checkerTranslationInvariant (CState.cons so s) ->
    checkerTranslationInvariant s
:=
by
  intro so s hs
  cases so <;> exact hs.2

/-- Lemma about `checkerTranslationInvariant_head_assume`. -/
theorem checkerTranslationInvariant_head_assume
    (A : Term) (s : CState) :
  checkerTranslationInvariant (CState.cons (CStateObj.assume A) s) ->
  RuleProofs.eo_has_smt_translation A :=
by
  intro hs
  exact hs.1

/-- Lemma about `checkerTranslationInvariant_head_assume_push`. -/
theorem checkerTranslationInvariant_head_assume_push
    (A : Term) (s : CState) :
  checkerTranslationInvariant (CState.cons (CStateObj.assume_push A) s) ->
  RuleProofs.eo_has_smt_translation A :=
by
  intro hs
  exact hs.1

/-- Lemma about `checkerTranslationInvariant_head_proven`. -/
theorem checkerTranslationInvariant_head_proven
    (P : Term) (s : CState) :
  checkerTranslationInvariant (CState.cons (CStateObj.proven P) s) ->
  RuleProofs.eo_has_smt_translation P :=
by
  intro hs
  exact hs.1

/-- Retrieves the `checkerTranslationInvariant` fact at a given index. -/
theorem checkerTranslationInvariant_at :
  forall {s : CState},
    checkerTranslationInvariant s ->
    forall n : native_Int,
      RuleProofs.eo_has_smt_translation (__eo_state_proven_nth s n)
:=
by
  intro s hs
  induction s with
  | nil =>
      intro n
      simpa [__eo_state_proven_nth] using eo_has_smt_translation_true
  | Stuck =>
      intro n
      simpa [__eo_state_proven_nth] using eo_has_smt_translation_true
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
              ih (checkerTranslationInvariant_tail hs) (native_zplus n (native_zneg 1))
        | assume_push A =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTranslationInvariant_tail hs) (native_zplus n (native_zneg 1))
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih (checkerTranslationInvariant_tail hs) (native_zplus n (native_zneg 1))

/-- Retrieves the `checkerEntry_has_bool_type` fact at a given index. -/
theorem checkerEntry_has_bool_type_at :
  forall {s : CState},
    checkerTypeInvariant s ->
    checkerTranslationInvariant s ->
    forall n : native_Int,
      RuleProofs.eo_has_bool_type (__eo_state_proven_nth s n)
:=
by
  intro s hsTy hsTrans n
  rcases checkerTypeInvariant_at hsTy n with ⟨_hNe, hTy⟩
  have hTrans : RuleProofs.eo_has_smt_translation (__eo_state_proven_nth s n) :=
    checkerTranslationInvariant_at hsTrans n
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type
    (__eo_state_proven_nth s n) hTrans hTy

/-- Derives `checkerTypeInvariant` from `stateStepPopSuffix`. -/
theorem checkerTypeInvariant_of_stateStepPopSuffix :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    checkerTypeInvariant root ->
    checkerTypeInvariant cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      intro hsRoot
      exact hsRoot
  | proven P hSuffix ih =>
      intro hsRoot
      exact ih (checkerTypeInvariant_tail hsRoot)

/-- Derives `checkerTranslationInvariant` from `stateStepPopSuffix`. -/
theorem checkerTranslationInvariant_of_stateStepPopSuffix :
  forall {cur root : CState},
    stateStepPopSuffix cur root ->
    checkerTranslationInvariant root ->
    checkerTranslationInvariant cur
:=
by
  intro cur root hSuffix
  induction hSuffix with
  | refl _ =>
      intro hsRoot
      exact hsRoot
  | proven P hSuffix ih =>
      intro hsRoot
      exact ih (checkerTranslationInvariant_tail hsRoot)

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

/-- Shows how `checkerLocalTruthInvariant` behaves on suffix tails. -/
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
    (M : SmtModel) (hM : model_total_typed M) :
  forall {s : CState},
    checkerAssumptionStabilityInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    forall (N : SmtModel),
      model_total_typed N ->
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
    (M : SmtModel) (hM : model_total_typed M) :
  forall {s : CState},
    checkerAssumptionStabilityInvariant M s ->
    eo_interprets M (statePushes s) true ->
    forall (N : SmtModel),
      model_total_typed N ->
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

/-- Lemma about `checkerLocalTruthInvariant_head_proven`. -/
theorem checkerLocalTruthInvariant_head_proven
    (M : SmtModel) (s : CState) (P : Term) :
  checkerLocalTruthInvariant M (CState.cons (CStateObj.proven P) s) ->
  eo_interprets M (stateAssumes s) true ->
  eo_interprets M (statePushes s) true ->
  eo_interprets M P true :=
by
  intro hs hAss hPush
  exact hs.1.true_here hAss hPush

/-- Retrieves the `checkerLocalTruthInvariant` fact at a given index. -/
theorem checkerLocalTruthInvariant_at (M : SmtModel) :
  forall {s : CState},
    checkerLocalTruthInvariant M s ->
    forall n : native_Int,
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
            simpa [__eo_state_proven_nth] using hs.1.true_here hAss' hPush'
      · cases so with
        | assume A =>
            have hAssTail : eo_interprets M (stateAssumes s) true :=
              eo_interprets_and_right M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                (native_zplus n (native_zneg 1)) hAssTail hPush
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                (native_zplus n (native_zneg 1)) hAss hPushTail
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih hs.2 (native_zplus n (native_zneg 1))
                (by simpa [stateAssumes] using hAss)
                (by simpa [statePushes] using hPush)

/-- Retrieves an indexed local-truth fact in any variable-variant model. -/
theorem checkerLocalTruthInvariant_at_var_model (M : SmtModel) :
  forall {s : CState},
    checkerLocalTruthInvariant M s ->
    forall (N : SmtModel),
      model_total_typed N ->
      model_agrees_on_globals M N ->
      forall n : native_Int,
        eo_interprets N (stateAssumes s) true ->
        eo_interprets N (statePushes s) true ->
        eo_interprets N (__eo_state_proven_nth s n) true
:=
by
  intro s hs
  induction s with
  | nil =>
      intro N hN hAgree n hAss hPush
      simpa [__eo_state_proven_nth] using eo_interprets_true N
  | Stuck =>
      intro N hN hAgree n hAss hPush
      exact False.elim (eo_interprets_stuck_true_absurd N (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro N hN hAgree n hAss hPush
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            simpa [__eo_state_proven_nth] using
              eo_interprets_and_left N A (stateAssumes s) hAss
        | assume_push A =>
            simpa [__eo_state_proven_nth] using
              eo_interprets_and_left N A (statePushes s) hPush
        | proven P =>
            have hAss' : eo_interprets N (stateAssumes s) true := by
              simpa [stateAssumes] using hAss
            have hPush' : eo_interprets N (statePushes s) true := by
              simpa [statePushes] using hPush
            simpa [__eo_state_proven_nth] using
              hs.1.true_in_var_model N hN hAgree hAss' hPush'
      · cases so with
        | assume A =>
            have hAssTail : eo_interprets N (stateAssumes s) true :=
              eo_interprets_and_right N A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                N hN hAgree (native_zplus n (native_zneg 1)) hAssTail hPush
        | assume_push A =>
            have hPushTail : eo_interprets N (statePushes s) true :=
              eo_interprets_and_right N A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                N hN hAgree (native_zplus n (native_zneg 1)) hAss hPushTail
        | proven P =>
            simpa [__eo_state_proven_nth, hZero] using
              ih hs.2 N hN hAgree (native_zplus n (native_zneg 1))
                (by simpa [stateAssumes] using hAss)
                (by simpa [statePushes] using hPush)

/-- Retrieves an indexed fact in a variable-variant model using a stable true context. -/
theorem checkerLocalTruthInvariant_at_stable_var_model (M : SmtModel) :
  forall {s : CState},
    model_total_typed M ->
    checkerLocalTruthInvariant M s ->
    checkerAssumptionStabilityInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    forall (N : SmtModel),
      model_total_typed N ->
      model_agrees_on_globals M N ->
      forall n : native_Int,
        eo_interprets N (__eo_state_proven_nth s n) true
:=
by
  intro s hM hs hStable hAss hPush
  induction s with
  | nil =>
      intro N hN hAgree n
      simpa [__eo_state_proven_nth] using eo_interprets_true N
  | Stuck =>
      intro N hN hAgree n
      exact False.elim (eo_interprets_stuck_true_absurd M (by simpa [stateAssumes] using hAss))
  | cons so s ih =>
      intro N hN hAgree n
      by_cases hZero : n = 0
      · subst hZero
        cases so with
        | assume A =>
            have hA : eo_interprets M A true :=
              eo_interprets_and_left M A (stateAssumes s) hAss
            exact hStable.1 M hM hA N hN hAgree
        | assume_push A =>
            have hA : eo_interprets M A true :=
              eo_interprets_and_left M A (statePushes s) hPush
            exact hStable.1 M hM hA N hN hAgree
        | proven P =>
            have hAssTail : eo_interprets M (stateAssumes s) true := by
              simpa [stateAssumes] using hAss
            have hPushTail : eo_interprets M (statePushes s) true := by
              simpa [statePushes] using hPush
            have hAssN : eo_interprets N (stateAssumes s) true :=
              stateAssumes_true_in_var_model_of_assumptionStability M hM
                (by simpa [checkerAssumptionStabilityInvariant] using hStable)
                hAssTail N hN hAgree
            have hPushN : eo_interprets N (statePushes s) true :=
              statePushes_true_in_var_model_of_assumptionStability M hM
                (by simpa [checkerAssumptionStabilityInvariant] using hStable)
                hPushTail N hN hAgree
            simpa [__eo_state_proven_nth] using
              hs.1.true_in_var_model N hN hAgree hAssN hPushN
      · cases so with
        | assume A =>
            have hAssTail : eo_interprets M (stateAssumes s) true :=
              eo_interprets_and_right M A (stateAssumes s) hAss
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                hStable.2 hAssTail hPush N hN hAgree
                (native_zplus n (native_zneg 1))
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (by simpa [checkerLocalTruthInvariant] using hs)
                hStable.2 hAss hPushTail N hN hAgree
                (native_zplus n (native_zneg 1))
        | proven P =>
            have hAssTail : eo_interprets M (stateAssumes s) true := by
              simpa [stateAssumes] using hAss
            have hPushTail : eo_interprets M (statePushes s) true := by
              simpa [statePushes] using hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih hs.2
                (by simpa [checkerAssumptionStabilityInvariant] using hStable)
                hAssTail hPushTail N hN hAgree (native_zplus n (native_zneg 1))

/-- Shows that `checkerLocalTruthInvariant` implies `truthInvariant`. -/
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

/-- Describes `checkerLocalTruthInvariant` after `assume_list`. -/
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
      by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
      · change checkerLocalTruthInvariant M
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_cons_of_guard_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        simpa [checkerLocalTruthInvariant] using ih
      · change checkerLocalTruthInvariant M
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_stuck_of_guard_ne_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        exact checkerLocalTruthInvariant_stuck M

/-- Describes `checkerTypeInvariant` after `assume_list`. -/
theorem checkerTypeInvariant_after_assume_list (F : Term) :
  ValidAssumptionList F ->
  stateOk (__eo_invoke_assume_list CState.nil F) ->
  checkerTypeInvariant (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hValid hOk
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, checkerTypeInvariant]
  | step A rest hRest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list] using hOk
      have hTy : __eo_typeof A = Term.Bool :=
        push_input_assume_typeof_bool_of_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hA : A ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hTy
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change checkerTypeInvariant
        (__eo_push_input_assume_check (assumptionCheckGuard A) A
          (__eo_invoke_assume_list CState.nil rest))
      rw [hPushEq]
      simpa [checkerTypeInvariant, hA] using
        (show __eo_typeof A = Term.Bool ∧
            checkerTypeInvariant (__eo_invoke_assume_list CState.nil rest) from
          ⟨hTy, ih hRestOk⟩)

/-- Describes `checkerTranslationInvariant` after `assume_list`. -/
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
      by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
      · change checkerTranslationInvariant
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_cons_of_guard_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        simpa [checkerTranslationInvariant] using
          (show RuleProofs.eo_has_smt_translation A ∧
              checkerTranslationInvariant (__eo_invoke_assume_list CState.nil rest) from
            ⟨RuleProofs.eo_has_smt_translation_of_has_bool_type A hA, ih⟩)
      · change checkerTranslationInvariant
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest))
        rw [push_input_assume_eq_stuck_of_guard_ne_true A
          (__eo_invoke_assume_list CState.nil rest) hGuard]
        exact checkerTranslationInvariant_stuck

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
        simpa [__eo_invoke_assume_list] using hOk
      have hClosed : __eo_is_closed A = Term.Boolean true :=
        push_input_assume_closed_of_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hRestOk : stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      exact StableAssumptionList.step A rest
        (stableWhenTrueInAnyVarModel_of_closed A hClosed)
        (ih hRestOk)

/-- Shows that `push_assume` preserves `localTruthInvariant`. -/
theorem push_assume_preserves_localTruthInvariant
    (M : SmtModel) (s : CState) (A : Term) :
  checkerLocalTruthInvariant M s ->
  checkerLocalTruthInvariant M (__eo_push_assume_check (assumptionCheckGuard A) A s) :=
by
  intro hs
  by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
  · simpa [push_assume_eq_cons_of_guard_true, hGuard,
      checkerLocalTruthInvariant] using hs
  · simpa [push_assume_eq_stuck_of_guard_ne_true, hGuard] using
      checkerLocalTruthInvariant_stuck M

/-- Shows that `push_assume` preserves `typeInvariant`. -/
theorem push_assume_preserves_typeInvariant
    (s : CState) (A : Term) :
  checkerTypeInvariant s ->
  checkerTypeInvariant (__eo_push_assume_check (assumptionCheckGuard A) A s) :=
by
  intro hs
  by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
  · have hTy : __eo_typeof A = Term.Bool :=
      (eo_is_bool_type_eq_true_iff A).1
        (assumptionCheckGuard_eq_true_cases A hGuard).1
    have hA : A ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hTy
    rw [push_assume_eq_cons_of_guard_true A s hGuard]
    simpa [checkerTypeInvariant, hA] using
      (show __eo_typeof A = Term.Bool ∧ checkerTypeInvariant s from ⟨hTy, hs⟩)
  · simpa [push_assume_eq_stuck_of_guard_ne_true, hGuard] using
      checkerTypeInvariant_stuck

/-- Shows that `push_assume` preserves `translationInvariant`. -/
theorem push_assume_preserves_translationInvariant
    (s : CState) (A : Term) :
  checkerTranslationInvariant s ->
  RuleProofs.eo_has_smt_translation A ->
  checkerTranslationInvariant (__eo_push_assume_check (assumptionCheckGuard A) A s) :=
by
  intro hs hA
  by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
  · simpa [push_assume_eq_cons_of_guard_true, hGuard,
      checkerTranslationInvariant] using
      (show RuleProofs.eo_has_smt_translation A ∧ checkerTranslationInvariant s from ⟨hA, hs⟩)
  · simpa [push_assume_eq_stuck_of_guard_ne_true, hGuard] using
      checkerTranslationInvariant_stuck

/-- Shows that `push_proven` preserves `typeInvariant`. -/
theorem push_proven_preserves_typeInvariant
    (s : CState) (P : Term) :
  checkerTypeInvariant s ->
  checkerTypeInvariant (__eo_push_proven P s) :=
by
  intro hs
  by_cases hTy : __eo_typeof P = Term.Bool
  · have hP : P ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hTy
    simpa [push_proven_eq_cons_of_typeof_bool, hTy, checkerTypeInvariant, hP] using hs
  · simpa [push_proven_eq_stuck_of_typeof_ne_bool, hTy] using checkerTypeInvariant_stuck

/-- Shows that `push_proven` preserves `translationInvariant`. -/
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

/-- Shows that `push_proven` preserves `localTruthInvariant_of_contextual_true`. -/
theorem push_proven_preserves_localTruthInvariant_of_contextual_true
    (M : SmtModel) (s : CState) (P : Term) :
  checkerLocalTruthInvariant M s ->
  ContextualTruth M (stateAssumes s) (statePushes s) P ->
  checkerLocalTruthInvariant M (CState.cons (CStateObj.proven P) s) :=
by
  intro hs hP
  exact ⟨hP, hs⟩

/-- Shape invariant asserting that the checker state forms a valid assumption suffix chain. -/
def checkerShapeInvariant : CState -> Prop
  | CState.Stuck => True
  | s => stateAssumptionSuffix s

/-- Derives `checkerShapeInvariant` from `suffix`. -/
theorem checkerShapeInvariant_of_suffix {s : CState} :
  stateAssumptionSuffix s ->
  checkerShapeInvariant s :=
by
  cases s <;> simp [checkerShapeInvariant, stateAssumptionSuffix]

/-- Derives `suffix` from `checkerShapeInvariant_nonstuck`. -/
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

/-- Combined checker invariant bundling shape, truth, stability, typing, and translation. -/
def checkerStateInvariant (M : SmtModel) (s : CState) : Prop :=
  checkerShapeInvariant s ∧
  checkerLocalTruthInvariant M s ∧
  checkerAssumptionStabilityInvariant M s ∧
  checkerTypeInvariant s ∧
  checkerTranslationInvariant s

/-- Derives `invoke_step_eq` from `nonstuck`. -/
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

/-- Derives `invoke_step_eq_stuck` from `nonstuck`. -/
theorem invoke_step_eq_stuck_of_nonstuck
    (s : CState) (hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  __eo_cmd_step_proven s r args premises = Term.Stuck ->
  __eo_invoke_cmd s (CCmd.step r args premises) = CState.Stuck :=
by
  intro hStep
  rw [invoke_step_eq_of_nonstuck s hNotStuck r args premises, hStep]
  simp [__eo_push_proven, __eo_push_proven_check, __eo_is_bool_type]

/-- Derives `invoke_step_eq_cons` from `nonstuck`. -/
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

/-- Derives `invoke_step_eq_stuck` from `typeof_ne_bool`. -/
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

/-- Derives `state_proven_nth_true` from `context`. -/
theorem state_proven_nth_true_of_context (M : SmtModel) :
  forall (s : CState) (n : native_Int),
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
              ih (native_zplus n (native_zneg 1)) hAssTail hPush hProv
        | assume_push A =>
            have hPushTail : eo_interprets M (statePushes s) true :=
              eo_interprets_and_right M A (statePushes s) hPush
            simpa [__eo_state_proven_nth, hZero] using
              ih (native_zplus n (native_zneg 1)) hAss hPushTail hProv
        | proven A =>
            have hProvTail : eo_interprets M (stateProvens s) true :=
              eo_interprets_and_right M A (stateProvens s) hProv
            simpa [__eo_state_proven_nth, hZero] using
              ih (native_zplus n (native_zneg 1)) hAss hPush hProvTail

/-- Retrieves the `checkerTruthInvariant` fact at a given index. -/
theorem checkerTruthInvariant_at (M : SmtModel) {s : CState} :
  checkerTruthInvariant M s ->
  ∀ n : native_Int,
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
      have hs' : ∀ n : native_Int,
          eo_interprets M (stateAssumes CState.nil) true ->
          eo_interprets M (statePushes CState.nil) true ->
          eo_interprets M (__eo_state_proven_nth CState.nil n) true := by
        simpa [checkerTruthInvariant] using hs
      exact hs' n hAss hPush
  | cons so s =>
      have hs' : ∀ n : native_Int,
          eo_interprets M (stateAssumes (CState.cons so s)) true ->
          eo_interprets M (statePushes (CState.cons so s)) true ->
          eo_interprets M (__eo_state_proven_nth (CState.cons so s) n) true := by
        simpa [checkerTruthInvariant] using hs
      exact hs' n hAss hPush

/-- Shows that `push_assume` preserves `truthInvariant`. -/
theorem push_assume_preserves_truthInvariant
    (M : SmtModel) (s : CState) (A : Term) :
  checkerTruthInvariant M s ->
  checkerTruthInvariant M (__eo_push_assume_check (assumptionCheckGuard A) A s) :=
by
  intro hs
  by_cases hGuard : assumptionCheckGuard A = Term.Boolean true
  · rw [push_assume_eq_cons_of_guard_true A s hGuard]
    intro n hAss hPush
    by_cases hZero : n = 0
    · subst hZero
      have hPush' :
          eo_interprets M
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) (statePushes s)) true := by
        simpa [push_assume_eq_cons_of_guard_true, hGuard, statePushes] using hPush
      simpa [push_assume_eq_cons_of_guard_true, hGuard, __eo_state_proven_nth] using
        eo_interprets_and_left M A (statePushes s) hPush'
    · have hAss' : eo_interprets M (stateAssumes s) true := by
        simpa [push_assume_eq_cons_of_guard_true, hGuard, stateAssumes] using hAss
      have hPush' :
          eo_interprets M
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) (statePushes s)) true := by
        simpa [push_assume_eq_cons_of_guard_true, hGuard, statePushes] using hPush
      have hPushTail : eo_interprets M (statePushes s) true :=
        eo_interprets_and_right M A (statePushes s) hPush'
      simpa [push_assume_eq_cons_of_guard_true, hGuard, __eo_state_proven_nth, hZero] using
        checkerTruthInvariant_at M hs
          (native_zplus n (native_zneg 1)) hAss' hPushTail
  · simpa [push_assume_eq_stuck_of_guard_ne_true, hGuard] using checkerTruthInvariant_stuck M

/-- Shows that `push_proven` preserves `truthInvariant_of_contextual_true`. -/
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
        (native_zplus n (native_zneg 1)) hAss' hPush'

/-- Describes `stateAssumptionTail` after `invoke_assume_list`. -/
theorem stateAssumptionTail_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    stateAssumptionTail (__eo_invoke_assume_list CState.nil F)
:=
by
  intro F hValid hOk
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, stateAssumptionTail]
  | step A rest hRest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list] using hOk
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change stateAssumptionTail
        (__eo_push_input_assume_check (assumptionCheckGuard A) A
          (__eo_invoke_assume_list CState.nil rest))
      rw [hPushEq]
      simpa [stateAssumptionTail] using ih hRestOk

/-- Describes `stateAssumptionSuffix` after `invoke_assume_list`. -/
theorem stateAssumptionSuffix_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    stateAssumptionSuffix (__eo_invoke_assume_list CState.nil F)
:=
by
  intro F hValid hOk
  exact stateAssumptionSuffix_of_tail (stateAssumptionTail_invoke_assume_list hValid hOk)

/-- Describes `stateAssumes` after `invoke_assume_list`. -/
theorem stateAssumes_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    stateAssumes (__eo_invoke_assume_list CState.nil F) = F
:=
by
  intro F hValid hOk
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, stateAssumes]
  | step A rest hRest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list] using hOk
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change stateAssumes
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) =
        Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest
      rw [hPushEq]
      simpa [stateAssumes] using ih hRestOk

/-- Describes `statePushes` after `invoke_assume_list`. -/
theorem statePushes_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    statePushes (__eo_invoke_assume_list CState.nil F) = Term.Boolean true
:=
by
  intro F hValid hOk
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, statePushes]
  | step A rest hRest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list] using hOk
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change statePushes
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) =
        Term.Boolean true
      rw [hPushEq]
      simpa [statePushes] using ih hRestOk

/-- Describes `stateProvens` after `invoke_assume_list`. -/
theorem stateProvens_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateOk (__eo_invoke_assume_list CState.nil F) ->
    stateProvens (__eo_invoke_assume_list CState.nil F) = Term.Boolean true
:=
by
  intro F hValid hOk
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, stateProvens]
  | step A rest hRest ih =>
      have hPushOk :
          stateOk (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) := by
        simpa [__eo_invoke_assume_list] using hOk
      have hRestOk :
          stateOk (__eo_invoke_assume_list CState.nil rest) :=
        push_input_assume_reflects_stateOk A
          (__eo_invoke_assume_list CState.nil rest) hPushOk
      have hPushEq := push_input_assume_eq_cons_of_stateOk A
        (__eo_invoke_assume_list CState.nil rest) hPushOk
      change stateProvens
          (__eo_push_input_assume_check (assumptionCheckGuard A) A
            (__eo_invoke_assume_list CState.nil rest)) =
        Term.Boolean true
      rw [hPushEq]
      simpa [stateProvens] using ih hRestOk

/-- Describes `checkerTruthInvariant` after `assume_list`. -/
theorem checkerTruthInvariant_after_assume_list (M : SmtModel) (F : Term) :
  ValidAssumptionList F ->
  stateOk (__eo_invoke_assume_list CState.nil F) ->
  checkerTruthInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hValid hOk
  have hNotStuck :
      __eo_invoke_assume_list CState.nil F ≠ CState.Stuck :=
    stateOk_not_stuck hOk
  have hProvens :
      stateProvens (__eo_invoke_assume_list CState.nil F) = Term.Boolean true :=
    stateProvens_invoke_assume_list hValid hOk
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

/-- Describes `checkerStateInvariant` after `assume_list`. -/
theorem checkerStateInvariant_after_assume_list (M : SmtModel) (F : Term) :
  ValidAssumptionList F ->
  stateOk (__eo_invoke_assume_list CState.nil F) ->
  TranslatableAssumptionList F ->
  StableAssumptionList M F ->
  checkerStateInvariant M (__eo_invoke_assume_list CState.nil F)
:=
by
  intro hValid hOk hTrans hStable
  exact ⟨
    checkerShapeInvariant_of_suffix (stateAssumptionSuffix_invoke_assume_list hValid hOk),
    checkerLocalTruthInvariant_after_assume_list M F hValid,
    checkerAssumptionStabilityInvariant_after_assume_list M F hStable,
    checkerTypeInvariant_after_assume_list F hValid hOk,
    checkerTranslationInvariant_after_assume_list F hTrans
  ⟩

/-- Derives `stateOk` from `state_closed_true`. -/
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

/-- Derives `statePushes` from `state_closed_true`. -/
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

/-- Derives `validAssumptionList` from `stateOk_assume_list`. -/
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
          | UOp op =>
              cases op with
              | and =>
                  have hPushOk :
                      stateOk (__eo_push_input_assume_check (assumptionCheckGuard lhs) lhs
                        (__eo_invoke_assume_list CState.nil a)) := by
                    simpa [__eo_invoke_assume_list] using hOk
                  have hRestOk :
                      stateOk (__eo_invoke_assume_list CState.nil a) :=
                    push_input_assume_reflects_stateOk lhs
                      (__eo_invoke_assume_list CState.nil a) hPushOk
                  exact ValidAssumptionList.step lhs a
                    (validAssumptionList_of_stateOk_assume_list hRestOk)
              | _ =>
                  simp [__eo_invoke_assume_list, stateOk] at hOk
          | _ =>
              simp [__eo_invoke_assume_list, stateOk] at hOk
      | _ =>
          simp [__eo_invoke_assume_list, stateOk] at hOk
  | _ =>
      simp [__eo_invoke_assume_list, stateOk] at hOk

/-- Derives `invoke_cmd_step_pop` from `assumptionTail`. -/
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

/-- Describes `stateAssumptionSuffix` after `invoke_cmd_step_pop`. -/
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

/-- Describes `stateAssumes` after `invoke_cmd_step_pop`. -/
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

/-- Shows that `invoke_cmd_step_pop` reflects `stateOk`. -/
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

/-- Shows that `invoke_cmd` reflects `stateOk`. -/
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
            simpa [__eo_invoke_cmd] using hOk
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
            simpa [__eo_invoke_cmd] using hOk
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

/-- Describes `stateAssumptionSuffix` after `invoke_cmd`. -/
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
          have hPushOk : stateOk (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A CState.nil hPushOk
          change stateAssumptionSuffix
            (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil)
          rw [hPushEq]
          simp [stateAssumptionSuffix]
      | cons so s =>
          have hPushOk : stateOk (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A (CState.cons so s) hPushOk
          change stateAssumptionSuffix
            (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s))
          rw [hPushEq]
          simpa [stateAssumptionSuffix] using hSuffix
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

/-- Describes `stateAssumes` after `invoke_cmd`. -/
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
          have hPushOk : stateOk (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A CState.nil hPushOk
          change stateAssumes
              (__eo_push_assume_check (assumptionCheckGuard A) A CState.nil) =
            stateAssumes CState.nil
          rw [hPushEq]
          simp [stateAssumes]
      | cons so s =>
          have hPushOk : stateOk (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s)) := by
            simpa [__eo_invoke_cmd] using hOk
          have hPushEq := push_assume_eq_cons_of_stateOk A (CState.cons so s) hPushOk
          change stateAssumes
              (__eo_push_assume_check (assumptionCheckGuard A) A (CState.cons so s)) =
            stateAssumes (CState.cons so s)
          rw [hPushEq]
          simp [stateAssumes]
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

/-- Shows that `invoke_cmd_list` reflects `stateOk`. -/
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

/-- Describes `stateAssumptionSuffix` after `invoke_cmd_list`. -/
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

/-- Describes `stateAssumes` after `invoke_cmd_list`. -/
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

/-- Derives `validAssumptionList` from `checker_true`. -/
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

/-- Derives `final_stateOk` from `checker_true`. -/
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

/-- Shows that `eo_eq_false_true` implies `eq_false`. -/
theorem eo_eq_false_true_implies_eq_false (t : Term) :
  __eo_eq t (Term.Boolean false) = Term.Boolean true ->
  t = Term.Boolean false :=
by
  intro hEq
  cases t <;> simp [__eo_eq, native_teq] at hEq ⊢ <;> assumption

/-- Derives `final_state_shape` from `checker_true`. -/
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

/-- Derives `stateAssumes` from `checker_true`. -/
theorem stateAssumes_of_checker_true (F : Term) (pf : CCmdList) :
  (__eo_checker_is_refutation F pf) = true ->
  stateAssumes (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil F) pf) = F :=
by
  intro hChecker
  let S0 := __eo_invoke_assume_list CState.nil F
  let S1 := __eo_invoke_cmd_list S0 pf
  have hValid : ValidAssumptionList F :=
    validAssumptionList_of_checker_true F pf hChecker
  have hS1Ok : stateOk S1 := by
    simpa [S1, S0] using final_stateOk_of_checker_true F pf hChecker
  have hS0Ok : stateOk S0 := by
    simpa [S1] using invoke_cmd_list_reflects_stateOk S0 pf hS1Ok
  have hShape0 : stateAssumptionSuffix S0 := by
    simpa [S0] using stateAssumptionSuffix_invoke_assume_list hValid hS0Ok
  calc
    stateAssumes S1 = stateAssumes S0 := by
      simpa [S1] using stateAssumes_invoke_cmd_list S0 pf hShape0 hS1Ok
    _ = F := by
      simpa [S0] using stateAssumes_invoke_assume_list hValid hS0Ok

/-- Derives `refutation_contradiction` from `truthInvariant`. -/
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

/-- Lemma about `premiseTermList_has_bool_type`. -/
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

/-- Lemma about `premiseTermList_has_smt_translation`. -/
theorem premiseTermList_has_smt_translation (s : CState) :
  forall (premises : CIndexList),
    checkerTranslationInvariant s ->
    AllHaveSmtTranslation (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hsTrans t ht
      cases ht
  | cons n premises ih =>
      intro hsTrans t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerTranslationInvariant_at hsTrans n
      · exact ih hsTrans t ht

/-- Lemma about `premiseTermList_has_typeof_bool`. -/
theorem premiseTermList_has_typeof_bool (s : CState) :
  forall (premises : CIndexList),
    checkerTypeInvariant s ->
    AllTypeofBool (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hsTy t ht
      cases ht
  | cons n premises ih =>
      intro hsTy t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact (checkerTypeInvariant_at hsTy n).2
      · exact ih hsTy t ht

/-- Derives `premiseTermList_true` from `truthInvariant`. -/
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

/-- Derives premise truth in a variable-variant model from the local invariant. -/
theorem premiseTermList_true_of_localTruthInvariant_var_model
    (M : SmtModel) (s : CState) :
  forall (premises : CIndexList),
    checkerLocalTruthInvariant M s ->
    forall (N : SmtModel),
      model_total_typed N ->
      model_agrees_on_globals M N ->
      eo_interprets N (stateAssumes s) true ->
      eo_interprets N (statePushes s) true ->
      AllInterpretedTrue N (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hs N hN hAgree hAss hPush t ht
      cases ht
  | cons n premises ih =>
      intro hs N hN hAgree hAss hPush t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerLocalTruthInvariant_at_var_model M hs N hN hAgree n hAss hPush
      · exact ih hs N hN hAgree hAss hPush t ht

/-- Derives premise truth in a variable-variant model from a stable true context. -/
theorem premiseTermList_true_of_localTruthInvariant_stable_var_model
    (M : SmtModel) (s : CState) :
  forall (premises : CIndexList),
    model_total_typed M ->
    checkerLocalTruthInvariant M s ->
    checkerAssumptionStabilityInvariant M s ->
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    forall (N : SmtModel),
      model_total_typed N ->
      model_agrees_on_globals M N ->
      AllInterpretedTrue N (premiseTermList s premises)
:=
by
  intro premises
  induction premises with
  | nil =>
      intro hM hs hStable hAss hPush N hN hAgree t ht
      cases ht
  | cons n premises ih =>
      intro hM hs hStable hAss hPush N hN hAgree t ht
      simp [premiseTermList] at ht
      rcases ht with rfl | ht
      · exact checkerLocalTruthInvariant_at_stable_var_model M hM hs hStable
          hAss hPush N hN hAgree n
      · exact ih hM hs hStable hAss hPush N hN hAgree t ht

/-- Builds the contextual premise evidence used by the richer rule-correctness template. -/
theorem premiseEvidence_of_localTruthInvariant
    (M N : SmtModel) (s : CState) (premises : CIndexList) :
  checkerLocalTruthInvariant M s ->
  checkerAssumptionStabilityInvariant M s ->
  model_total_typed N ->
  model_agrees_on_globals M N ->
  eo_interprets N (stateAssumes s) true ->
  eo_interprets N (statePushes s) true ->
  RulePremiseEvidence N
    (premiseTermList s premises) :=
by
  intro hs hStable hN hAgree hAss hPush
  refine ⟨?_, ?_⟩
  · exact premiseTermList_true_of_localTruthInvariant_var_model
      M s premises hs N hN hAgree hAss hPush
  · intro K hK hAgreeNK
    have hStableN : checkerAssumptionStabilityInvariant N s :=
      checkerAssumptionStabilityInvariant_rebase M N hStable
    have hAssK : eo_interprets K (stateAssumes s) true :=
      stateAssumes_true_in_var_model_of_assumptionStability N hN
        hStableN hAss K hK hAgreeNK
    have hPushK : eo_interprets K (statePushes s) true :=
      statePushes_true_in_var_model_of_assumptionStability N hN
        hStableN hPush K hK hAgreeNK
    exact premiseTermList_true_of_localTruthInvariant_var_model
      M s premises hs K hK
      (model_agrees_on_globals_trans hAgree hAgreeNK) hAssK hPushK

/-- Structure bundling the premise facts needed to justify a single checker step. -/
structure CmdStepFacts (M : SmtModel) (s : CState) (P : Term) : Prop where
  true_of_context :
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M P true
  true_in_var_model :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      eo_interprets N (stateAssumes s) true ->
      eo_interprets N (statePushes s) true ->
      eo_interprets N P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P

/-- Converts command-step facts into the local invariant payload for `push_proven`. -/
theorem CmdStepFacts.contextualTruth
    {M : SmtModel} {s : CState} {P : Term} :
  CmdStepFacts M s P ->
  ContextualTruth M (stateAssumes s) (statePushes s) P :=
by
  intro hFacts
  exact ⟨hFacts.true_of_context, hFacts.true_in_var_model⟩

/-- Packages rule-level step properties into the checker facts required for a single step. -/
theorem cmd_step_facts_of_rule_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (premises : CIndexList) {P : Term} :
  checkerLocalTruthInvariant M s ->
  checkerAssumptionStabilityInvariant M s ->
  (hProps : ∀ N, model_total_typed N ->
    model_agrees_on_globals M N ->
    StepRuleProperties N (premiseTermList s premises) P) ->
  CmdStepFacts M s P :=
by
  intro hs hAssumptionsStable hProps
  refine ⟨?_, ?_, ?_⟩
  · intro hAss hPush
    have hPM := hProps M hM (model_agrees_on_globals_refl M)
    exact hPM.facts_of_true
      (premiseEvidence_of_localTruthInvariant M M s premises hs hAssumptionsStable hM
        (model_agrees_on_globals_refl M) hAss hPush)
  · intro N hN hAgree hAss hPush
    have hPN := hProps N hN hAgree
    exact hPN.facts_of_true
      (premiseEvidence_of_localTruthInvariant M N s premises hs hAssumptionsStable
        hN hAgree hAss hPush)
  · exact (hProps M hM (model_agrees_on_globals_refl M)).has_smt_translation

/-- Packages rule-level step-pop properties into the checker facts required for a pop step. -/
theorem cmd_step_pop_facts_of_rule_properties
    (M : SmtModel) (hM : model_total_typed M)
    (root tail : CState) (A : Term) (premises : CIndexList) {P : Term} :
  checkerLocalTruthInvariant M root ->
  checkerAssumptionStabilityInvariant M root ->
  stateStepPopSuffix (CState.cons (CStateObj.assume_push A) tail) root ->
  (hProps : StepPopRuleProperties A (premiseTermList root premises) P) ->
  CmdStepFacts M tail P :=
by
  intro hsRoot hAssumptionsStableRoot hSuffix hProps
  rcases hProps with ⟨X, hXMem, hFactsOfImp, hPopTrans⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hAss hPush
    have hAssRoot : eo_interprets M (stateAssumes root) true := by
      rw [stateAssumes_eq_of_stateStepPopSuffix_assume_push hSuffix]
      exact hAss
    have hScoped :
        eo_interprets M A true -> eo_interprets M X true := by
      intro hATrue
      have hPushRoot : eo_interprets M (statePushes root) true := by
        rw [statePushes_eq_of_stateStepPopSuffix_assume_push hSuffix]
        exact eo_interprets_and_intro M A (statePushes tail) hATrue hPush
      exact (premiseTermList_true_of_localTruthInvariant_var_model
          M root premises hsRoot M hM (model_agrees_on_globals_refl M)
          hAssRoot hPushRoot)
        X hXMem
    exact hFactsOfImp M hM hScoped
  · intro N hN hAgree hAss hPush
    have hAssRoot : eo_interprets N (stateAssumes root) true := by
      rw [stateAssumes_eq_of_stateStepPopSuffix_assume_push hSuffix]
      exact hAss
    have hScoped :
        eo_interprets N A true -> eo_interprets N X true := by
      intro hATrue
      have hPushRoot : eo_interprets N (statePushes root) true := by
        rw [statePushes_eq_of_stateStepPopSuffix_assume_push hSuffix]
        exact eo_interprets_and_intro N A (statePushes tail) hATrue hPush
      exact (premiseTermList_true_of_localTruthInvariant_var_model
          M root premises hsRoot N hN hAgree hAssRoot hPushRoot)
        X hXMem
    exact hFactsOfImp N hN hScoped
  · exact hPopTrans
