import CpcMini.Spec
import CpcMini.Proofs.Support

open Eo
open SmtEval
open Smtm

/-- Inductive predicate for assumption terms that are well-formed `and`-chains ending in `true`. -/
inductive ValidAssumptionList : Term -> Prop
  | base : ValidAssumptionList (Term.Boolean true)
  | step (A rest : Term) : ValidAssumptionList rest ->
      ValidAssumptionList (Term.Apply (Term.Apply Term.and A) rest)

/-- Inductive predicate for valid assumption lists whose entries are non-stuck EO Boolean terms. -/
inductive TypedAssumptionList : Term -> Prop
  | base : TypedAssumptionList (Term.Boolean true)
  | step (A rest : Term) :
      A ≠ Term.Stuck ->
      __eo_typeof A = Term.Bool ->
      TypedAssumptionList rest ->
      TypedAssumptionList (Term.Apply (Term.Apply Term.and A) rest)

/-- Inductive predicate for valid assumption lists whose entries all admit SMT translations. -/
inductive TranslatableAssumptionList : Term -> Prop
  | base : TranslatableAssumptionList (Term.Boolean true)
  | step (A rest : Term) :
      RuleProofs.eo_has_smt_translation A ->
      TranslatableAssumptionList rest ->
      TranslatableAssumptionList (Term.Apply (Term.Apply Term.and A) rest)

/-- Predicate asserting that a checker state is structurally well-formed and not `Stuck`. -/
def stateOk : CState -> Prop
  | CState.nil => True
  | CState.cons _ s => stateOk s
  | CState.Stuck => False

/-- Simplifies EO-to-SMT translation for `true_eq`. -/
private theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `false_eq`. -/
private theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `stuck_eq`. -/
private theorem eo_to_smt_stuck_eq :
    __eo_to_smt Term.Stuck = SmtTerm.None := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `and_eq`. -/
private theorem eo_to_smt_and_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.and A) B) =
      SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) (__eo_to_smt A))
        (__eo_to_smt B) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `imp_eq`. -/
private theorem eo_to_smt_imp_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.imp A) B) =
      SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) (__eo_to_smt A))
        (__eo_to_smt B) := by
  rw [__eo_to_smt.eq_def]

/-- Characterizes EO interpretation in terms of the translated SMT interpretation. -/
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

/-- Shows that the EO term `true` is interpreted as `true` in every model. -/
theorem eo_interprets_true (M : SmtModel) :
  eo_interprets M (Term.Boolean true) true :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_true_eq]
  refine smt_interprets.intro_true M (SmtTerm.Boolean true) ?_ ?_
  · simpa using Smtm.__smtx_typeof.eq_1 true
  · simpa using Smtm.__smtx_model_eval.eq_1 M true

/-- Lemma about `eo_interprets_false_true_absurd`. -/
theorem eo_interprets_false_true_absurd (M : SmtModel) :
  ¬ eo_interprets M (Term.Boolean false) true :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_false_eq]
  intro h
  cases h with
  | intro_true _ hEval =>
      rw [Smtm.__smtx_model_eval.eq_1] at hEval
      cases hEval

/-- Lemma about `eo_interprets_stuck_false_absurd`. -/
theorem eo_interprets_stuck_false_absurd (M : SmtModel) :
  ¬ eo_interprets M Term.Stuck false :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq]
  intro h
  cases h with
  | intro_false hty _ =>
      have : SmtType.None = SmtType.Bool := by
        simp [Smtm.__smtx_typeof.eq_def] at hty
      cases this

/-- Lemma about `eo_interprets_stuck_true_absurd`. -/
theorem eo_interprets_stuck_true_absurd (M : SmtModel) :
  ¬ eo_interprets M Term.Stuck true :=
by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq]
  intro h
  cases h with
  | intro_true hty _ =>
      have : SmtType.None = SmtType.Bool := by
        simp [Smtm.__smtx_typeof.eq_def] at hty
      cases this

/-- Lemma about `eo_interprets_true_not_false`. -/
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

/-- Left-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) true ->
  eo_interprets M A true :=
by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_and_eq A B] at h
  cases h with
  | intro_true hty hEval =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) (__eo_to_smt A))
              (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact
          (bool_binop_args_bool_of_non_none
            (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) t1) t2)
            (Smtm.__smtx_typeof.eq_8 (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        rw [Smtm.__smtx_model_eval.eq_8] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.native_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

/-- Right-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) true ->
  eo_interprets M B true :=
by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_and_eq A B] at h
  cases h with
  | intro_true hty hEval =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) (__eo_to_smt A))
              (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact
          (bool_binop_args_bool_of_non_none
            (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) t1) t2)
            (Smtm.__smtx_typeof.eq_8 (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
        rw [Smtm.__smtx_model_eval.eq_8] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.native_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) true :=
by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_and_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · simp [Smtm.__smtx_typeof.eq_8, htyA, htyB, native_Teq, native_ite]
          · simp [Smtm.__smtx_model_eval.eq_8, __smtx_model_eval_and, hEvalA, hEvalB, SmtEval.native_and]

/-- Elimination lemma for `eo_interprets_imp`. -/
theorem eo_interprets_imp_elim (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) true ->
  eo_interprets M A true ->
  eo_interprets M B true :=
by
  intro hImp hA
  rw [eo_interprets_iff_smt_interprets] at hImp hA ⊢
  rw [eo_to_smt_imp_eq A B] at hImp
  cases hImp with
  | intro_true htyImp hEvalImp =>
      cases hA with
      | intro_true htyA hEvalA =>
          have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
            have hNN : term_has_non_none_type
                (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) (__eo_to_smt A))
                  (__eo_to_smt B)) := by
              unfold term_has_non_none_type
              rw [htyImp]
              simp
            exact
              (bool_binop_args_bool_of_non_none
                (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) t1) t2)
                (Smtm.__smtx_typeof.eq_9 (__eo_to_smt A) (__eo_to_smt B)) hNN).2
          have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
            rw [Smtm.__smtx_model_eval.eq_9] at hEvalImp
            cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
              simp [hEvalA, hBeval, __smtx_model_eval_imp, __smtx_model_eval_or,
                __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not] at hEvalImp
            case Boolean a =>
              cases a <;> simp at hEvalImp
              simp
          exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_imp`. -/
theorem eo_interprets_imp_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) true :=
by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_imp_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · simp [Smtm.__smtx_typeof.eq_9, htyA, htyB, native_Teq, native_ite]
          · simp [Smtm.__smtx_model_eval.eq_9, __smtx_model_eval_imp, __smtx_model_eval_or,
              __smtx_model_eval_not, hEvalA, hEvalB, SmtEval.native_or, SmtEval.native_not]

/-- Left-projection lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) false ->
  eo_interprets M A true :=
by
  intro hImp
  rw [eo_interprets_iff_smt_interprets] at hImp ⊢
  rw [eo_to_smt_imp_eq A B] at hImp
  cases hImp with
  | intro_false htyImp hEvalImp =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) (__eo_to_smt A))
              (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [htyImp]
          simp
        exact
          (bool_binop_args_bool_of_non_none
            (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) t1) t2)
            (Smtm.__smtx_typeof.eq_9 (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        rw [Smtm.__smtx_model_eval.eq_9] at hEvalImp
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_imp, __smtx_model_eval_or,
            __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not] at hEvalImp
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp at hEvalImp
          simp
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

/-- Right-projection lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) false ->
  eo_interprets M B false :=
by
  intro hImp
  rw [eo_interprets_iff_smt_interprets] at hImp ⊢
  rw [eo_to_smt_imp_eq A B] at hImp
  cases hImp with
  | intro_false htyImp hEvalImp =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) (__eo_to_smt A))
              (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [htyImp]
          simp
        exact
          (bool_binop_args_bool_of_non_none
            (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.imp) t1) t2)
            (Smtm.__smtx_typeof.eq_9 (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean false := by
        rw [Smtm.__smtx_model_eval.eq_9] at hEvalImp
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_imp, __smtx_model_eval_or,
            __smtx_model_eval_not, SmtEval.native_or, SmtEval.native_not] at hEvalImp
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp at hEvalImp
          simp
      exact smt_interprets.intro_false M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_imp_false`. -/
theorem eo_interprets_imp_false_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B false ->
  eo_interprets M (Term.Apply (Term.Apply Term.imp A) B) false :=
by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_imp_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_false htyB hEvalB =>
          apply smt_interprets.intro_false
          · simp [Smtm.__smtx_typeof.eq_9, htyA, htyB, native_Teq, native_ite]
          · simp [Smtm.__smtx_model_eval.eq_9, __smtx_model_eval_imp, __smtx_model_eval_or,
              __smtx_model_eval_not, hEvalA, hEvalB, SmtEval.native_or, SmtEval.native_not]

/-- Derives `eo_interprets_and_false_left` from `right_not_false`. -/
theorem eo_interprets_and_false_left_of_right_not_false (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) false ->
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
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) (__eo_to_smt A))
              (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact
          (bool_binop_args_bool_of_non_none
            (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) t1) t2)
            (Smtm.__smtx_typeof.eq_8 (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) (__eo_to_smt A))
              (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact
          (bool_binop_args_bool_of_non_none
            (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) t1) t2)
            (Smtm.__smtx_typeof.eq_8 (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false := by
        rw [Smtm.__smtx_model_eval.eq_8] at hEval
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
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) false ->
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
                (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) (__eo_to_smt A))
                  (__eo_to_smt B)) := by
              unfold term_has_non_none_type
              rw [htyAnd]
              simp
            exact
              (bool_binop_args_bool_of_non_none
                (op := fun t1 t2 => SmtTerm.Apply (SmtTerm.Apply (SmtTerm.TheoryOp SmtTheoryOp.and) t1) t2)
                (Smtm.__smtx_typeof.eq_8 (__eo_to_smt A) (__eo_to_smt B)) hNN).2
          have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
            rw [Smtm.__smtx_model_eval.eq_8] at hEvalAnd
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
  | CState.cons (CStateObj.assume F) s => Term.Apply (Term.Apply Term.and F) (stateAssumes s)
  | CState.cons _ s => stateAssumes s
  | CState.Stuck => Term.Stuck

/-- Extracts the list of assumptions introduced by `assume_push` commands in a checker state. -/
def statePushes : CState -> Term
  | CState.nil => Term.Boolean true
  | CState.cons (CStateObj.assume_push F) s => Term.Apply (Term.Apply Term.and F) (statePushes s)
  | CState.cons _ s => statePushes s
  | CState.Stuck => Term.Stuck

/-- Extracts the list of proven terms stored in a checker state. -/
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
  statePushes root = Term.Apply (Term.Apply Term.and A) (statePushes tail) :=
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

/-- Derives `push_assume_eq_cons` from `typeof_bool`. -/
@[simp] theorem push_assume_eq_cons_of_typeof_bool (A : Term) (s : CState) :
  __eo_typeof A = Term.Bool ->
  __eo_push_assume A s = CState.cons (CStateObj.assume_push A) s :=
by
  intro hTy
  simp [__eo_push_assume, __eo_push_assume_check,
    eo_is_bool_type_eq_true_of_typeof_bool, hTy]

/-- Derives `push_assume_eq_stuck` from `eq_stuck`. -/
@[simp] theorem push_assume_eq_stuck_of_eq_stuck (s : CState) :
  __eo_push_assume Term.Stuck s = CState.Stuck :=
by
  simp [__eo_push_assume, __eo_push_assume_check, __eo_is_bool_type]

/-- Derives `push_assume_eq_stuck` from `typeof_ne_bool`. -/
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

/-- Derives `assume_push_arg_ne_stuck` from `stateOk`. -/
theorem assume_push_arg_ne_stuck_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume A s) -> A ≠ Term.Stuck :=
by
  intro hOk hA
  subst hA
  simp [push_assume_eq_stuck_of_eq_stuck, stateOk] at hOk

/-- Shows that `push_assume` reflects `stateOk`. -/
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

/-- Derives `push_assume_typeof_bool` from `stateOk`. -/
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

/-- Derives `push_assume_eq_cons` from `stateOk`. -/
theorem push_assume_eq_cons_of_stateOk (A : Term) (s : CState) :
  stateOk (__eo_push_assume A s) ->
  __eo_push_assume A s = CState.cons (CStateObj.assume_push A) s :=
by
  intro hOk
  exact push_assume_eq_cons_of_typeof_bool A s (push_assume_typeof_bool_of_stateOk A s hOk)

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
   This matches the operational checks for `assume_push` / `push_proven`, and
   for initial assumptions we thread a separate `TypedAssumptionList` premise.
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
      (eo_interprets M (stateAssumes s) true ->
       eo_interprets M (statePushes s) true ->
       eo_interprets M P true) ∧
      checkerLocalTruthInvariant M s
  | CState.cons _ s => checkerLocalTruthInvariant M s
  | CState.Stuck => True

/-- Describes `checkerLocalTruthInvariant` on the stuck state. -/
theorem checkerLocalTruthInvariant_stuck (M : SmtModel) :
  checkerLocalTruthInvariant M CState.Stuck :=
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
      simpa [__eo_state_proven_nth] using RuleProofs.eo_has_smt_translation_true
  | Stuck =>
      intro n
      simpa [__eo_state_proven_nth] using RuleProofs.eo_has_smt_translation_true
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

/-- Lemma about `checkerLocalTruthInvariant_head_proven`. -/
theorem checkerLocalTruthInvariant_head_proven
    (M : SmtModel) (s : CState) (P : Term) :
  checkerLocalTruthInvariant M (CState.cons (CStateObj.proven P) s) ->
  eo_interprets M (stateAssumes s) true ->
  eo_interprets M (statePushes s) true ->
  eo_interprets M P true :=
by
  intro hs hAss hPush
  exact hs.1 hAss hPush

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
            simpa [__eo_state_proven_nth] using hs.1 hAss' hPush'
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
      simpa [__eo_invoke_assume_list, checkerLocalTruthInvariant] using ih

/-- Describes `checkerTypeInvariant` after `assume_list`. -/
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
      exact ⟨hA, ih⟩

/-- Shows that `push_assume` preserves `localTruthInvariant`. -/
theorem push_assume_preserves_localTruthInvariant
    (M : SmtModel) (s : CState) (A : Term) :
  checkerLocalTruthInvariant M s ->
  checkerLocalTruthInvariant M (__eo_push_assume A s) :=
by
  intro hs
  by_cases hTy : __eo_typeof A = Term.Bool
  · simpa [push_assume_eq_cons_of_typeof_bool, hTy, checkerLocalTruthInvariant] using hs
  · simpa [push_assume_eq_stuck_of_typeof_ne_bool, hTy] using checkerLocalTruthInvariant_stuck M

/-- Shows that `push_assume` preserves `typeInvariant`. -/
theorem push_assume_preserves_typeInvariant
    (s : CState) (A : Term) :
  checkerTypeInvariant s ->
  checkerTypeInvariant (__eo_push_assume A s) :=
by
  intro hs
  by_cases hTy : __eo_typeof A = Term.Bool
  · have hA : A ≠ Term.Stuck := term_ne_stuck_of_typeof_bool hTy
    simpa [push_assume_eq_cons_of_typeof_bool, hTy, checkerTypeInvariant, hA] using hs
  · simpa [push_assume_eq_stuck_of_typeof_ne_bool, hTy] using checkerTypeInvariant_stuck

/-- Shows that `push_assume` preserves `translationInvariant`. -/
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
  (eo_interprets M (stateAssumes s) true ->
   eo_interprets M (statePushes s) true ->
   eo_interprets M P true) ->
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

/-- Combined checker invariant bundling the shape, truth, typing, and translation conditions. -/
def checkerStateInvariant (M : SmtModel) (s : CState) : Prop :=
  checkerShapeInvariant s ∧
  checkerLocalTruthInvariant M s ∧
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
          (native_zplus n (native_zneg 1)) hAss' hPushTail
  · simpa [push_assume_eq_stuck_of_typeof_ne_bool, hTy] using checkerTruthInvariant_stuck M

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
    stateAssumptionTail (__eo_invoke_assume_list CState.nil F)
:=
by
  intro F hValid
  induction hValid with
  | base =>
      simp [__eo_invoke_assume_list, stateAssumptionTail]
  | step A rest hRest ih =>
      simpa [__eo_invoke_assume_list, stateAssumptionTail] using ih

/-- Describes `stateAssumptionSuffix` after `invoke_assume_list`. -/
theorem stateAssumptionSuffix_invoke_assume_list :
  forall {F : Term}, ValidAssumptionList F ->
    stateAssumptionSuffix (__eo_invoke_assume_list CState.nil F)
:=
by
  intro F hValid
  exact stateAssumptionSuffix_of_tail (stateAssumptionTail_invoke_assume_list hValid)

/-- Describes `stateOk` after `invoke_assume_list`. -/
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

/-- Describes `stateAssumes` after `invoke_assume_list`. -/
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

/-- Describes `statePushes` after `invoke_assume_list`. -/
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

/-- Describes `stateProvens` after `invoke_assume_list`. -/
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

/-- Describes `checkerTruthInvariant` after `assume_list`. -/
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

/-- Describes `checkerStateInvariant` after `assume_list`. -/
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
  have hShape0 : stateAssumptionSuffix S0 := by
    simpa [S0] using stateAssumptionSuffix_invoke_assume_list hValid
  have hS1Ok : stateOk S1 := by
    simpa [S1, S0] using final_stateOk_of_checker_true F pf hChecker
  calc
    stateAssumes S1 = stateAssumes S0 := by
      simpa [S1] using stateAssumes_invoke_cmd_list S0 pf hShape0 hS1Ok
    _ = F := by
      simpa [S0] using stateAssumes_invoke_assume_list hValid

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

/-- Structure bundling the premise facts needed to justify a single checker step. -/
structure CmdStepFacts (M : SmtModel) (s : CState) (P : Term) : Prop where
  true_of_context :
    eo_interprets M (stateAssumes s) true ->
    eo_interprets M (statePushes s) true ->
    eo_interprets M P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P

/-- Packages rule-level step properties into the checker facts required for a single step. -/
theorem cmd_step_facts_of_rule_properties
    (M : SmtModel) (s : CState) (premises : CIndexList) {P : Term} :
  checkerTruthInvariant M s ->
  StepRuleProperties M (premiseTermList s premises) P ->
  CmdStepFacts M s P :=
by
  intro hs hProps
  refine ⟨?_, ?_⟩
  · intro hAss hPush
    exact hProps.facts_of_true
      (premiseTermList_true_of_truthInvariant M s premises hs hAss hPush)
  · exact hProps.has_smt_translation

/-- Packages rule-level step-pop properties into the checker facts required for a pop step. -/
theorem cmd_step_pop_facts_of_rule_properties
    (M : SmtModel) (hM : model_total_typed M)
    (root tail : CState) (A : Term) (premises : CIndexList) {P : Term} :
  checkerTruthInvariant M root ->
  stateStepPopSuffix (CState.cons (CStateObj.assume_push A) tail) root ->
  StepPopRuleProperties A (premiseTermList root premises) P ->
  CmdStepFacts M tail P :=
by
  intro hsRoot hSuffix hProps
  rcases hProps with ⟨X, hXMem, hFactsOfImp, hPopTrans⟩
  refine ⟨?_, ?_⟩
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
      exact (premiseTermList_true_of_truthInvariant M root premises hsRoot hAssRoot hPushRoot)
        X hXMem
    exact hFactsOfImp M hM hScoped
  · exact hPopTrans
