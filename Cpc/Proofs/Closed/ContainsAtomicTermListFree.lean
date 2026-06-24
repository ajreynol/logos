import Cpc.Proofs.Closed.IsClosedRec

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/--
Models agree everywhere except possibly on the variables in `except` that are
not currently shadowed by `bound`.

This is the semantic relation matched to
`__contains_atomic_term_list_free_rec t except bound = false`: free variables in
`except` are the only variables on which the two models may differ, while
variables in `bound` are considered locally bound and therefore must agree after
the evaluator pushes matching witnesses on both sides.
-/
structure model_agrees_except_on_env
    (except bound : List SmtVarKey) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq :
    ∀ s T, (s, T) ∈ bound ∨ (s, T) ∉ except ->
      native_model_var_lookup M s T = native_model_var_lookup N s T

theorem model_agrees_except_on_env_refl
    (except bound : List SmtVarKey) (M : SmtModel) :
  model_agrees_except_on_env except bound M M :=
by
  exact ⟨model_agrees_on_globals_refl M, by intro s T _; rfl⟩

theorem model_agrees_except_on_env_symm
    {except bound : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except bound N M :=
by
  refine ⟨?_, ?_⟩
  · exact ⟨by intro s T; exact (hAgree.globals.1 s T).symm,
      by intro fid T U; exact (hAgree.globals.2 fid T U).symm⟩
  · intro s T hKey
    exact (hAgree.vars_eq s T hKey).symm

theorem model_agrees_except_on_env_push_same
    {except bound : List SmtVarKey} {M N : SmtModel}
    {s : native_String} {T : SmtType} {v : SmtValue}
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except ((s, T) :: bound)
    (native_model_push M s T v) (native_model_push N s T v) :=
by
  refine ⟨model_agrees_on_globals_push₂ hAgree.globals, ?_⟩
  intro s' T' hKeyAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := T' } : SmtModelKey) =
        { isVar := true, name := s, ty := T }
  · cases hKey
    simp [native_model_var_lookup, native_model_push]
  · have hAllowedTail : (s', T') ∈ bound ∨ (s', T') ∉ except := by
      rcases hKeyAllowed with hBound | hNotExcept
      · cases hBound with
        | head =>
            exfalso
            exact hKey rfl
        | tail _ hTail =>
            exact Or.inl hTail
      · exact Or.inr hNotExcept
    simpa [native_model_var_lookup, native_model_push, hKey]
      using hAgree.vars_eq s' T' hAllowedTail

theorem model_agrees_except_on_env_shrink_bound
    {except bound bound' : List SmtVarKey} {M N : SmtModel}
    (hSub : ∀ key, key ∈ bound' -> key ∈ bound)
    (hAgree : model_agrees_except_on_env except bound M N) :
  model_agrees_except_on_env except bound' M N :=
by
  refine ⟨hAgree.globals, ?_⟩
  intro s T hAllowed
  apply hAgree.vars_eq
  rcases hAllowed with hBound' | hNotExcept
  · exact Or.inl (hSub (s, T) hBound')
  · exact Or.inr hNotExcept

private theorem eo_ite_false_eq_false_cases
    {c e : Term}
    (h : __eo_ite c (Term.Boolean false) e = Term.Boolean false) :
  c = Term.Boolean true ∨ e = Term.Boolean false :=
by
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b
    · right
      simpa [__eo_ite, native_ite, native_teq] using h
    · left
      rfl

/--
The variable case of `__contains_atomic_term_list_free_rec`.

For a variable, returning `false` means exactly the checker's local condition:
either the variable is absent from the exception list, or it is present in the
current bound-variable stack.
-/
theorem contains_atomic_term_list_free_rec_var_false_cases
    {name T except bound : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec (Term.Var name T) except bound =
        Term.Boolean false) :
  __eo_is_neg
      (__eo_list_find Term.__eo_List_cons except (Term.Var name T)) =
      Term.Boolean true ∨
    __eo_is_neg
      (__eo_list_find Term.__eo_List_cons bound (Term.Var name T)) =
      Term.Boolean false :=
by
  cases except <;> cases bound <;>
    simp [__contains_atomic_term_list_free_rec] at hNoFree ⊢
  all_goals
    exact eo_ite_false_eq_false_cases hNoFree

/--
The quantifier-shaped/list-binder branch only asks the body about free
variables, with the binder list appended to the bound-variable stack.
-/
theorem contains_atomic_term_list_free_rec_list_branch_false_body
    {q x ys body except bound : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply
            (Term.Apply q
              (Term.Apply (Term.Apply Term.__eo_List_cons x) ys))
            body)
          except bound =
        Term.Boolean false)
    :
  __contains_atomic_term_list_free_rec body except
      (__eo_list_concat Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) ys) bound) =
    Term.Boolean false :=
by
  cases except <;> cases bound <;>
    simp [__contains_atomic_term_list_free_rec] at hNoFree ⊢
  all_goals
    exact hNoFree
