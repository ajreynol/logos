import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.StringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CnfSupport

/-- Shows that `false` is interpreted as `false` in every model. -/
theorem eo_interprets_false (M : SmtModel) :
    eo_interprets M (Term.Boolean false) false := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by
    rw [__eo_to_smt.eq_def]]
  refine smt_interprets.intro_false M (SmtTerm.Boolean false) ?_ ?_
  · rw [__smtx_typeof.eq_1]
  · rw [__smtx_model_eval.eq_1]

/-- Splits a Boolean EO term into the `true` and `false` cases. -/
theorem eo_interprets_bool_cases
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
    RuleProofs.eo_has_bool_type t ->
    eo_interprets M t true ∨ eo_interprets M t false := by
  intro hTy
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM t hTy with ⟨b, hEval⟩
  cases b with
  | true =>
      exact Or.inl (RuleProofs.eo_interprets_of_bool_eval M t true hTy hEval)
  | false =>
      exact Or.inr (RuleProofs.eo_interprets_of_bool_eval M t false hTy hEval)

/-- If `A ∨ B` is false, then `A` is false. -/
theorem eo_interprets_or_false_left
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) false ->
    eo_interprets M A false := by
  intro hOrFalse
  have hOrBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) :=
    RuleProofs.eo_has_bool_type_of_interprets_false M _ hOrFalse
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_or_left A B hOrBool
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_or_right A B hOrBool
  rcases eo_interprets_bool_cases M hM A hABool with hATrue | hAFalse
  · have hOrTrue : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) true :=
      RuleProofs.eo_interprets_or_left_intro M hM A B hATrue hBBool
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hOrTrue) hOrFalse)
  · exact hAFalse

/-- If `A ∨ B` is false, then `B` is false. -/
theorem eo_interprets_or_false_right
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
    eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) false ->
    eo_interprets M B false := by
  intro hOrFalse
  have hOrBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) :=
    RuleProofs.eo_has_bool_type_of_interprets_false M _ hOrFalse
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_or_left A B hOrBool
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_or_right A B hOrBool
  rcases eo_interprets_bool_cases M hM B hBBool with hBTrue | hBFalse
  · have hOrTrue : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) true :=
      RuleProofs.eo_interprets_or_right_intro M hM A B hABool hBTrue
    exact False.elim ((RuleProofs.eo_interprets_true_not_false M _ hOrTrue) hOrFalse)
  · exact hBFalse

/-- If `__eo_typeof_not t` is Boolean, then `t` is Boolean. -/
theorem typeof_not_eq_bool {t : Term} :
    __eo_typeof_not t = Term.Bool ->
    t = Term.Bool := by
  cases t <;> simp [__eo_typeof_not]

/-- If `__eo_typeof_or t1 t2` is Boolean, then `t1` is Boolean. -/
theorem typeof_or_eq_bool_left {t1 t2 : Term} :
    __eo_typeof_or t1 t2 = Term.Bool ->
    t1 = Term.Bool := by
  cases t1 <;> cases t2 <;> simp [__eo_typeof_or]

/-- If `__eo_typeof_or t1 t2` is Boolean, then `t2` is Boolean. -/
theorem typeof_or_eq_bool_right {t1 t2 : Term} :
    __eo_typeof_or t1 t2 = Term.Bool ->
    t2 = Term.Bool := by
  cases t1 <;> cases t2 <;> simp [__eo_typeof_or]

private theorem is_ok_true_of_ne_stuck {x : Term} :
    x ≠ Term.Stuck ->
    __eo_is_ok x = Term.Boolean true := by
  intro hNe
  cases x <;> simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at hNe ⊢

private theorem is_list_true_of_get_nil_rec_ne_stuck {f x : Term} :
    __eo_get_nil_rec f x ≠ Term.Stuck ->
    __eo_is_list f x = Term.Boolean true := by
  intro hRec
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst hF
    simpa [__eo_get_nil_rec] using hRec
  have hX : x ≠ Term.Stuck := by
    intro hX
    subst hX
    simpa [__eo_get_nil_rec] using hRec
  simp [__eo_is_list, hF, hX, is_ok_true_of_ne_stuck hRec]

/-- Structural characterization of EO `and`-lists. -/
inductive AndList : Term -> Prop where
  | true : AndList (Term.Boolean true)
  | cons (x xs : Term) : AndList xs ->
      AndList (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs)

/-- Structural characterization of EO `or`-lists. -/
inductive OrList : Term -> Prop where
  | false : OrList (Term.Boolean false)
  | cons (x xs : Term) : OrList xs ->
      OrList (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs)

private theorem andList_of_is_list_true {c : Term} :
    __eo_is_list (Term.UOp UserOp.and) c = Term.Boolean true ->
    AndList c := by
  intro hList
  cases c with
  | Stuck =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, native_teq, native_not,
        SmtEval.native_not] at hList
  | Boolean b =>
      cases b with
      | true =>
          exact AndList.true
      | false =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | and =>
                  unfold __eo_is_list at hList
                  unfold __eo_is_ok at hList
                  unfold __eo_get_nil_rec at hList
                  unfold __eo_requires at hList
                  simp [native_ite, native_teq, native_not, SmtEval.native_not] at hList
                  exact AndList.cons x a
                    (andList_of_is_list_true (is_list_true_of_get_nil_rec_ne_stuck hList))
              | _ =>
                  simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                    __eo_is_list_nil, native_ite, native_teq, native_not,
                    SmtEval.native_not] at hList
          | _ =>
              simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                __eo_is_list_nil, native_ite, native_teq, native_not,
                SmtEval.native_not] at hList
      | _ =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | _ =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList

private theorem andList_get_nil_rec_ne_stuck {c : Term} :
    AndList c ->
    __eo_get_nil_rec (Term.UOp UserOp.and) c ≠ Term.Stuck := by
  intro hList
  induction hList with
  | true =>
      simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | cons x xs hXs ih =>
      simpa [__eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] using ih

/-- Every structural EO `and`-list is accepted by `__eo_is_list`. -/
theorem andList_is_list_true {c : Term} :
    AndList c ->
    __eo_is_list (Term.UOp UserOp.and) c = Term.Boolean true := by
  intro hList
  exact is_list_true_of_get_nil_rec_ne_stuck (andList_get_nil_rec_ne_stuck hList)

/-- A structural EO `and`-list is never `Stuck`. -/
theorem andList_ne_stuck {c : Term} :
    AndList c ->
    c ≠ Term.Stuck := by
  intro hList
  cases hList <;> simp

private theorem orList_of_is_list_true {c : Term} :
    __eo_is_list (Term.UOp UserOp.or) c = Term.Boolean true ->
    OrList c := by
  intro hList
  cases c with
  | Stuck =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, native_teq, native_not,
        SmtEval.native_not] at hList
  | Boolean b =>
      cases b with
      | false =>
          exact OrList.false
      | true =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op with
              | or =>
                  unfold __eo_is_list at hList
                  unfold __eo_is_ok at hList
                  unfold __eo_get_nil_rec at hList
                  unfold __eo_requires at hList
                  simp [native_ite, native_teq, native_not, SmtEval.native_not] at hList
                  exact OrList.cons x a
                    (orList_of_is_list_true (is_list_true_of_get_nil_rec_ne_stuck hList))
              | _ =>
                  simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                    __eo_is_list_nil, native_ite, native_teq, native_not,
                    SmtEval.native_not] at hList
          | _ =>
              simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
                __eo_is_list_nil, native_ite, native_teq, native_not,
                SmtEval.native_not] at hList
      | _ =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | _ =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList

private theorem orList_get_nil_rec_ne_stuck {c : Term} :
    OrList c ->
    __eo_get_nil_rec (Term.UOp UserOp.or) c ≠ Term.Stuck := by
  intro hList
  induction hList with
  | false =>
      simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | cons x xs hXs ih =>
      simpa [__eo_get_nil_rec, __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] using ih

/-- Every structural EO `or`-list is accepted by `__eo_is_list`. -/
theorem orList_is_list_true {c : Term} :
    OrList c ->
    __eo_is_list (Term.UOp UserOp.or) c = Term.Boolean true := by
  intro hList
  exact is_list_true_of_get_nil_rec_ne_stuck (orList_get_nil_rec_ne_stuck hList)

/-- A structural EO `or`-list is never `Stuck`. -/
theorem orList_ne_stuck {c : Term} :
    OrList c ->
    c ≠ Term.Stuck := by
  intro hList
  cases hList <;> simp

private theorem list_nth_nonstuck_is_list_true {f c i : Term} :
    __eo_list_nth f c i ≠ Term.Stuck ->
    __eo_is_list f c = Term.Boolean true := by
  intro hNth
  cases hIs : __eo_is_list f c with
  | Boolean b =>
      cases b with
      | true =>
          rfl
      | false =>
          simp [__eo_list_nth, __eo_requires, hIs, native_ite, native_teq, native_not,
            SmtEval.native_not] at hNth
  | _ =>
      simp [__eo_list_nth, __eo_requires, hIs, native_ite, native_teq, native_not,
        SmtEval.native_not] at hNth

/-- A non-stuck `and`-list selection implies the list structure is valid. -/
theorem andList_of_list_nth_ne_stuck {c i : Term} :
    __eo_list_nth (Term.UOp UserOp.and) c i ≠ Term.Stuck ->
    AndList c := by
  intro hNth
  exact andList_of_is_list_true (list_nth_nonstuck_is_list_true hNth)

/-- A non-stuck `or`-list selection implies the list structure is valid. -/
theorem orList_of_list_nth_ne_stuck {c i : Term} :
    __eo_list_nth (Term.UOp UserOp.or) c i ≠ Term.Stuck ->
    OrList c := by
  intro hNth
  exact orList_of_is_list_true (list_nth_nonstuck_is_list_true hNth)

private theorem list_nth_rec_cons_ne_zero
    (f x xs i : Term) :
    i ≠ Term.Stuck ->
    i ≠ Term.Numeral 0 ->
    __eo_list_nth_rec (Term.Apply (Term.Apply f x) xs) i =
      __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) := by
  intro hStuck hZero
  cases i with
  | Stuck =>
      exact False.elim (hStuck rfl)
  | Numeral n =>
      by_cases hN : n = 0
      · subst hN
        exact False.elim (hZero rfl)
      · simp [__eo_list_nth_rec, hN]
  | _ =>
      simp [__eo_list_nth_rec]

private theorem list_nth_rec_cons_tail_ne_stuck
    (f x xs i : Term) :
    i ≠ Term.Stuck ->
    i ≠ Term.Numeral 0 ->
    __eo_list_nth_rec (Term.Apply (Term.Apply f x) xs) i ≠ Term.Stuck ->
    __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠ Term.Stuck := by
  intro hStuck hZero hNth
  rw [← list_nth_rec_cons_ne_zero f x xs i hStuck hZero]
  exact hNth

private theorem andList_nth_rec_has_bool_type {c i : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    __eo_list_nth_rec c i ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_nth_rec c i) := by
  intro hList hCBool hNth
  induction hList generalizing i with
  | true =>
      cases i <;> simp [__eo_list_nth_rec] at hNth
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      by_cases hStuck : i = Term.Stuck
      · subst hStuck
        simp [__eo_list_nth_rec] at hNth
      · by_cases hZero : i = Term.Numeral 0
        · subst hZero
          simpa [__eo_list_nth_rec] using hXBool
        · have hTail : __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠
              Term.Stuck :=
            list_nth_rec_cons_tail_ne_stuck (Term.UOp UserOp.and) x xs i hStuck hZero hNth
          rw [list_nth_rec_cons_ne_zero (Term.UOp UserOp.and) x xs i hStuck hZero]
          exact ih hXsBool hTail

/-- A non-stuck selection from a typed EO `and`-list is Boolean. -/
theorem andList_nth_has_bool_type {c i : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    __eo_list_nth (Term.UOp UserOp.and) c i ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_nth (Term.UOp UserOp.and) c i) := by
  intro hList hCBool hNth
  simp [__eo_list_nth, __eo_requires, andList_is_list_true hList, native_ite,
    native_teq, native_not, SmtEval.native_not] at hNth ⊢
  exact andList_nth_rec_has_bool_type hList hCBool hNth

private theorem andList_nth_rec_true_of_true
    (M : SmtModel) {c i : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    __eo_list_nth_rec c i ≠ Term.Stuck ->
    eo_interprets M (__eo_list_nth_rec c i) true := by
  intro hList hCBool hCTrue hNth
  induction hList generalizing i with
  | true =>
      cases i <;> simp [__eo_list_nth_rec] at hNth
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hAndTrue : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) true := by
        simpa using hCTrue
      by_cases hStuck : i = Term.Stuck
      · subst hStuck
        simp [__eo_list_nth_rec] at hNth
      · by_cases hZero : i = Term.Numeral 0
        · subst hZero
          simpa [__eo_list_nth_rec] using RuleProofs.eo_interprets_and_left M x xs hAndTrue
        · have hTail : __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠
              Term.Stuck :=
            list_nth_rec_cons_tail_ne_stuck (Term.UOp UserOp.and) x xs i hStuck hZero hNth
          have hXsTrue : eo_interprets M xs true :=
            RuleProofs.eo_interprets_and_right M x xs hAndTrue
          rw [list_nth_rec_cons_ne_zero (Term.UOp UserOp.and) x xs i hStuck hZero]
          exact ih hXsBool hXsTrue hTail

/-- Selecting from a true EO `and`-list yields a true conjunct. -/
theorem andList_nth_true_of_true
    (M : SmtModel) {c i : Term} :
    AndList c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    __eo_list_nth (Term.UOp UserOp.and) c i ≠ Term.Stuck ->
    eo_interprets M (__eo_list_nth (Term.UOp UserOp.and) c i) true := by
  intro hList hCBool hCTrue hNth
  simp [__eo_list_nth, __eo_requires, andList_is_list_true hList, native_ite,
    native_teq, native_not, SmtEval.native_not] at hNth ⊢
  exact andList_nth_rec_true_of_true M hList hCBool hCTrue hNth

private theorem orList_nth_rec_has_bool_type {c i : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    __eo_list_nth_rec c i ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_nth_rec c i) := by
  intro hList hCBool hNth
  induction hList generalizing i with
  | false =>
      cases i <;> simp [__eo_list_nth_rec] at hNth
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      by_cases hStuck : i = Term.Stuck
      · subst hStuck
        simp [__eo_list_nth_rec] at hNth
      · by_cases hZero : i = Term.Numeral 0
        · subst hZero
          simpa [__eo_list_nth_rec] using hXBool
        · have hTail : __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠
              Term.Stuck :=
            list_nth_rec_cons_tail_ne_stuck (Term.UOp UserOp.or) x xs i hStuck hZero hNth
          rw [list_nth_rec_cons_ne_zero (Term.UOp UserOp.or) x xs i hStuck hZero]
          exact ih hXsBool hTail

/-- A non-stuck selection from a typed EO `or`-list is Boolean. -/
theorem orList_nth_has_bool_type {c i : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    __eo_list_nth (Term.UOp UserOp.or) c i ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_nth (Term.UOp UserOp.or) c i) := by
  intro hList hCBool hNth
  simp [__eo_list_nth, __eo_requires, orList_is_list_true hList, native_ite,
    native_teq, native_not, SmtEval.native_not] at hNth ⊢
  exact orList_nth_rec_has_bool_type hList hCBool hNth

private theorem orList_nth_rec_false_of_false
    (M : SmtModel) (hM : model_total_typed M) {c i : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c false ->
    __eo_list_nth_rec c i ≠ Term.Stuck ->
    eo_interprets M (__eo_list_nth_rec c i) false := by
  intro hList hCBool hCFalse hNth
  induction hList generalizing i with
  | false =>
      cases i <;> simp [__eo_list_nth_rec] at hNth
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_or_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_or_right x xs hCBool
      have hOrFalse :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) false := by
        simpa using hCFalse
      by_cases hStuck : i = Term.Stuck
      · subst hStuck
        simp [__eo_list_nth_rec] at hNth
      · by_cases hZero : i = Term.Numeral 0
        · subst hZero
          simpa [__eo_list_nth_rec] using eo_interprets_or_false_left M hM x xs hOrFalse
        · have hTail : __eo_list_nth_rec xs (__eo_add i (Term.Numeral (-1 : native_Int))) ≠
              Term.Stuck :=
            list_nth_rec_cons_tail_ne_stuck (Term.UOp UserOp.or) x xs i hStuck hZero hNth
          have hXsFalse : eo_interprets M xs false :=
            eo_interprets_or_false_right M hM x xs hOrFalse
          rw [list_nth_rec_cons_ne_zero (Term.UOp UserOp.or) x xs i hStuck hZero]
          exact ih hXsBool hXsFalse hTail

/-- Selecting from a false EO `or`-list yields a false disjunct. -/
theorem orList_nth_false_of_false
    (M : SmtModel) (hM : model_total_typed M) {c i : Term} :
    OrList c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c false ->
    __eo_list_nth (Term.UOp UserOp.or) c i ≠ Term.Stuck ->
    eo_interprets M (__eo_list_nth (Term.UOp UserOp.or) c i) false := by
  intro hList hCBool hCFalse hNth
  simp [__eo_list_nth, __eo_requires, orList_is_list_true hList, native_ite,
    native_teq, native_not, SmtEval.native_not] at hNth ⊢
  exact orList_nth_rec_false_of_false M hM hList hCBool hCFalse hNth

end CnfSupport
