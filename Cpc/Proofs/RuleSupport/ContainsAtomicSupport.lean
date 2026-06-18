import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

/-- If a `requires` term is not stuck, its guard arguments matched. -/
theorem eq_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hEq : native_teq x y = true
  · simpa [native_teq] using hEq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    unfold __eo_requires at hReq
    simp [hEqFalse, native_ite] at hReq

/-- If a `requires` term is not stuck, the selected body is not stuck. -/
theorem body_ne_stuck_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    B ≠ Term.Stuck := by
  intro hReq hB
  subst B
  unfold __eo_requires at hReq
  by_cases hEq : native_teq x y = true
  · by_cases hStuck : native_teq x Term.Stuck = true
    · simp [hEq, hStuck, native_ite] at hReq
    · have hStuckFalse : native_teq x Term.Stuck = false := by
        cases h : native_teq x Term.Stuck <;> simp [h] at hStuck ⊢
      simp [hEq, hStuckFalse, native_ite] at hReq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    simp [hEqFalse, native_ite] at hReq

/-- Boolean `or` can be true only if one of its operands is true. -/
theorem eo_or_eq_true_cases_local (x y : Term) :
    __eo_or x y = Term.Boolean true ->
    x = Term.Boolean true ∨ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_or] at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [native_or] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [__eo_requires, hNumNe, native_ite, native_teq] at h

/-- A false conditional whose then-branch is false exposes the condition or else-branch. -/
theorem eo_ite_false_cases (c e : Term) :
    __eo_ite c (Term.Boolean false) e = Term.Boolean false ->
    c = Term.Boolean true ∨ e = Term.Boolean false := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h
  case Boolean b =>
    cases b
    · exact Or.inr (by simpa using h rfl)
    · exact Or.inl rfl

/-- A false conditional whose then-branch is true forces false condition and false else-branch. -/
theorem eo_ite_true_eq_false (c e : Term) :
    __eo_ite c (Term.Boolean true) e = Term.Boolean false ->
    c = Term.Boolean false ∧ e = Term.Boolean false := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h
  case Boolean b =>
    cases b <;> simp at h
    exact ⟨rfl, h⟩

/-- A false `requires guard true false` means the guard evaluated to true. -/
theorem eo_requires_false_eq_false_guard_true (x : Term) :
    __eo_requires x (Term.Boolean true) (Term.Boolean false) =
      Term.Boolean false ->
    x = Term.Boolean true := by
  intro h
  cases x <;> simp [__eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at h
  case Boolean b =>
    cases b <;> simp at h ⊢

/-- Characterize why a variable passed `contains_atomic` with result false. -/
theorem contains_atomic_var_false_cases
    (name T xs bvs : Term)
    (h :
      __contains_atomic_term_list_free_rec (Term.Var name T) xs bvs =
        Term.Boolean false) :
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons xs (Term.Var name T)) =
      Term.Boolean true ∨
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons bvs (Term.Var name T)) =
      Term.Boolean false := by
  cases xs <;> cases bvs <;>
    simp [__contains_atomic_term_list_free_rec] at h ⊢
  all_goals exact eo_ite_false_cases _ _ h

/-- For a binder-shaped application, `contains_atomic=false` propagates to the body. -/
theorem contains_atomic_binder_body_false
    (q x ys a xs bvs : Term)
    (h :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
            a)
          xs bvs = Term.Boolean false) :
      __contains_atomic_term_list_free_rec a xs
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons x) ys) bvs) =
      Term.Boolean false := by
  cases xs <;> cases bvs <;>
    simpa [__contains_atomic_term_list_free_rec] using h

/-- For non-application, non-variable atoms, `contains_atomic=false` gives closedness. -/
theorem contains_atomic_atom_false_is_closed_rec
    (t xs bvs : Term)
    (hNotApply : ∀ f a, t ≠ Term.Apply f a)
    (hNotVar : ∀ name T, t ≠ Term.Var name T)
    (h :
      __contains_atomic_term_list_free_rec t xs bvs =
        Term.Boolean false) :
    __is_closed_rec t Term.__eo_List_nil = Term.Boolean true := by
  cases t
  case Stuck =>
    cases xs <;> simp [__contains_atomic_term_list_free_rec] at h
  case Apply f a =>
    exact False.elim (hNotApply f a rfl)
  case Var name T =>
    exact False.elim (hNotVar name T rfl)
  all_goals
    apply eo_requires_false_eq_false_guard_true
    cases xs <;> cases bvs <;>
      simpa [__contains_atomic_term_list_free_rec] using h

/-- For unary operator applications, `contains_atomic=false` propagates to the argument. -/
theorem contains_atomic_apply_uop_arg_false
    (op : UserOp) (a xs bvs : Term)
    (h :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.UOp op) a) xs bvs =
        Term.Boolean false) :
    __contains_atomic_term_list_free_rec a xs bvs = Term.Boolean false := by
  cases xs <;> cases bvs <;>
    simpa [__contains_atomic_term_list_free_rec]
      using h
