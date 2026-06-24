import Cpc.Proofs.Closed.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

abbrev EoVarKey : Type := native_String × Term

def EoVarKey.toSmt (key : EoVarKey) : SmtVarKey :=
  (key.1, __eo_to_smt_type key.2)

/--
An EO variable environment that remembers the original EO type syntax.

`EoSmtVarEnv` is the right relation for SMT closedness, but it stores only the
translated SMT type.  The free-variable checker searches for exact EO variables,
so this relation keeps the EO type term around for the membership facts.
-/
inductive EoVarEnv : Term -> List EoVarKey -> Prop where
  | nil :
      EoVarEnv Term.__eo_List_nil []
  | cons {s : native_String} {T env : Term} {vars : List EoVarKey} :
      EoVarEnv env vars ->
        EoVarEnv
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) env)
          ((s, T) :: vars)

namespace EoVarEnv

theorem to_smt :
    ∀ {env : Term} {vars : List EoVarKey},
      EoVarEnv env vars ->
        EoSmtVarEnv env (vars.map EoVarKey.toSmt)
  | _, _, nil =>
      by
        exact EoSmtVarEnv.nil
  | _, _, cons hTail =>
      by
        simpa [EoVarKey.toSmt] using EoSmtVarEnv.cons (to_smt hTail)

theorem is_list
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  __eo_is_list Term.__eo_List_cons env = Term.Boolean true :=
by
  simpa using hEnv.to_smt.is_list

theorem cons_mk_apply
    {s : native_String} {T env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  EoVarEnv
    (__eo_mk_apply
      (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T))
      env)
    ((s, T) :: vars) :=
by
  cases hEnv with
  | nil =>
      simpa [__eo_mk_apply] using
        EoVarEnv.cons (s := s) (T := T) EoVarEnv.nil
  | cons hTail =>
      simpa [__eo_mk_apply] using
        EoVarEnv.cons (s := s) (T := T)
          (EoVarEnv.cons hTail)

theorem concat_rec :
    ∀ {vs env : Term} {binderVars vars : List EoVarKey},
      EoVarEnv vs binderVars ->
        EoVarEnv env vars ->
          EoVarEnv
            (__eo_list_concat_rec vs env)
            (binderVars ++ vars)
  | _, _, _, _, nil, hEnv =>
      by
        cases hEnv with
        | nil =>
            simpa [__eo_list_concat_rec] using EoVarEnv.nil
        | cons hTail =>
            rename_i s' T' env' vars'
            simpa [__eo_list_concat_rec] using
              EoVarEnv.cons (s := s') (T := T') hTail
  | _, _, _, _, cons (s := s) (T := T) hTail, hEnv =>
      by
        cases hEnv with
        | nil =>
            have hTailConcat := concat_rec hTail EoVarEnv.nil
            simpa [__eo_list_concat_rec, List.cons_append]
              using cons_mk_apply (s := s) (T := T) hTailConcat
        | cons hEnvTail =>
            rename_i s' T' env' vars'
            have hTailConcat :=
              concat_rec hTail
                (EoVarEnv.cons (s := s') (T := T') hEnvTail)
            simpa [__eo_list_concat_rec, List.cons_append]
              using cons_mk_apply (s := s) (T := T) hTailConcat

theorem concat :
    ∀ {vs env : Term} {binderVars vars : List EoVarKey},
      EoVarEnv vs binderVars ->
        EoVarEnv env vars ->
          EoVarEnv
            (__eo_list_concat Term.__eo_List_cons vs env)
            (binderVars ++ vars)
  | _, _, _, _, hVs, hEnv =>
      by
        have hVsList := hVs.is_list
        have hEnvList := hEnv.is_list
        simpa [__eo_list_concat, __eo_requires, hVsList, hEnvList,
          native_ite, native_teq]
          using concat_rec hVs hEnv

theorem find_rec_neg_false_of_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  ∀ {s : native_String} {T : Term} {n : native_Int},
    (s, T) ∈ vars ->
      0 ≤ n ->
        __eo_is_neg
            (__eo_list_find_rec env (Term.Var (Term.String s) T)
              (Term.Numeral n)) =
          Term.Boolean false :=
by
  induction hEnv with
  | nil =>
      intro s T n hMem hNonneg
      cases hMem
  | cons hTail ih =>
      rename_i s' T' env' vars'
      intro s T n hMem hNonneg
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq.symm]
        have hNotLt : native_zlt n 0 = false := by
          simp [native_zlt, Int.not_lt_of_ge hNonneg]
        simp [__eo_list_find_rec, hFindEq, __eo_ite, __eo_is_neg,
          native_ite, native_teq, hNotLt]
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hTailMem : (s, T) ∈ vars' := by
          cases hMem with
          | head =>
              exfalso
              exact hVarEq rfl
          | tail _ hTailMem =>
              exact hTailMem
        have hSuccNonneg : 0 ≤ native_zplus n 1 := by
          simpa [native_zplus] using
            Int.add_nonneg hNonneg (by decide : (0 : Int) ≤ 1)
        simpa [__eo_list_find_rec, hFindEq, __eo_ite, __eo_add,
          native_ite, native_teq]
          using ih hTailMem hSuccNonneg

theorem find_rec_neg_true_of_not_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  ∀ {s : native_String} {T : Term} {n : native_Int},
    (s, T) ∉ vars ->
      0 ≤ n ->
        __eo_is_neg
            (__eo_list_find_rec env (Term.Var (Term.String s) T)
              (Term.Numeral n)) =
          Term.Boolean true :=
by
  induction hEnv with
  | nil =>
      intro s T n hNotMem hNonneg
      simp [__eo_list_find_rec, __eo_is_neg, native_zlt]
  | cons hTail ih =>
      rename_i s' T' env' vars'
      intro s T n hNotMem hNonneg
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · exfalso
        injection hVarEq with hName hTy
        injection hName with hs
        cases hs
        cases hTy
        exact hNotMem (List.Mem.head _)
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hTailNotMem : (s, T) ∉ vars' := by
          intro hMem
          exact hNotMem (List.Mem.tail _ hMem)
        have hSuccNonneg : 0 ≤ native_zplus n 1 := by
          simpa [native_zplus] using
            Int.add_nonneg hNonneg (by decide : (0 : Int) ≤ 1)
        simpa [__eo_list_find_rec, hFindEq, __eo_ite, __eo_add,
          native_ite, native_teq]
          using ih hTailNotMem hSuccNonneg

theorem find_neg_false_of_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    {s : native_String} {T : Term}
    (hMem : (s, T) ∈ vars) :
  __eo_is_neg
      (__eo_list_find Term.__eo_List_cons env
        (Term.Var (Term.String s) T)) =
    Term.Boolean false :=
by
  have hList := hEnv.is_list
  simpa [__eo_list_find, __eo_requires, hList, native_ite, native_teq]
    using
      hEnv.find_rec_neg_false_of_mem hMem
        (show (0 : native_Int) ≤ (0 : native_Int) by
          exact Int.le_refl 0)

theorem find_neg_true_of_not_mem
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars)
    {s : native_String} {T : Term}
    (hNotMem : (s, T) ∉ vars) :
  __eo_is_neg
      (__eo_list_find Term.__eo_List_cons env
        (Term.Var (Term.String s) T)) =
    Term.Boolean true :=
by
  have hList := hEnv.is_list
  simpa [__eo_list_find, __eo_requires, hList, native_ite, native_teq]
    using
      hEnv.find_rec_neg_true_of_not_mem hNotMem
        (show (0 : native_Int) ≤ (0 : native_Int) by
          exact Int.le_refl 0)

end EoVarEnv

def EoVarEnvEquiv (xs ys : List EoVarKey) : Prop :=
  ∀ key, key ∈ xs ↔ key ∈ ys

theorem EoVarEnvEquiv.refl (xs : List EoVarKey) :
  EoVarEnvEquiv xs xs :=
by
  intro key
  rfl

theorem EoVarEnvEquiv.reverse (xs : List EoVarKey) :
  EoVarEnvEquiv xs xs.reverse :=
by
  intro key
  simp

theorem EoVarEnvEquiv.append
    {xs xs' ys ys' : List EoVarKey}
    (hxs : EoVarEnvEquiv xs xs')
    (hys : EoVarEnvEquiv ys ys') :
  EoVarEnvEquiv (xs ++ ys) (xs' ++ ys') :=
by
  intro key
  constructor
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append.2 (Or.inl ((hxs key).1 h))
    · exact List.mem_append.2 (Or.inr ((hys key).1 h))
  · intro h
    rcases List.mem_append.1 h with h | h
    · exact List.mem_append.2 (Or.inl ((hxs key).2 h))
    · exact List.mem_append.2 (Or.inr ((hys key).2 h))

def EoVarEnvPerm (env : Term) (vars : List EoVarKey) : Prop :=
  ∃ exactVars, EoVarEnv env exactVars ∧ EoVarEnvEquiv exactVars vars

theorem EoVarEnvPerm.of_exact
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv env vars) :
  EoVarEnvPerm env vars :=
by
  exact ⟨vars, hEnv, EoVarEnvEquiv.refl vars⟩

theorem EoVarEnvPerm.mem_of_find_neg_false
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons env
            (Term.Var (Term.String s) T)) =
        Term.Boolean false) :
  (s, T) ∈ vars :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  by_cases hMem : (s, T) ∈ exactVars
  · exact (hEquiv (s, T)).1 hMem
  · have hFindTrue := hExact.find_neg_true_of_not_mem hMem
    rw [hFindTrue] at hFind
    cases hFind

theorem EoVarEnvPerm.not_mem_of_find_neg_true
    {env : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnvPerm env vars)
    {s : native_String} {T : Term}
    (hFind :
      __eo_is_neg
          (__eo_list_find Term.__eo_List_cons env
            (Term.Var (Term.String s) T)) =
        Term.Boolean true) :
  (s, T) ∉ vars :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  intro hMem
  have hExactMem : (s, T) ∈ exactVars := (hEquiv (s, T)).2 hMem
  have hFindFalse := hExact.find_neg_false_of_mem hExactMem
  rw [hFind] at hFindFalse
  cases hFindFalse

theorem EoVarEnvPerm.concat_rev
    {vs env : Term} {binderVars vars : List EoVarKey}
    (hVs : EoVarEnv vs binderVars)
    (hEnv : EoVarEnvPerm env vars) :
  EoVarEnvPerm
    (__eo_list_concat Term.__eo_List_cons vs env)
    (binderVars.reverse ++ vars) :=
by
  rcases hEnv with ⟨exactVars, hExact, hEquiv⟩
  refine ⟨binderVars ++ exactVars, EoVarEnv.concat hVs hExact, ?_⟩
  exact EoVarEnvEquiv.append
    (EoVarEnvEquiv.reverse binderVars)
    hEquiv

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

/--
Exact-EO-variable version of `model_agrees_except_on_env`.

The checker's free-variable test compares whole EO variables, including the EO
type syntax.  This relation preserves that exactness while still comparing SMT
model lookups at the translated type.
-/
structure model_agrees_except_on_eo_env
    (except bound : List EoVarKey) (M N : SmtModel) : Prop where
  globals : model_agrees_on_globals M N
  vars_eq :
    ∀ s T, (s, T) ∈ bound ∨ (s, T) ∉ except ->
      native_model_var_lookup M s (__eo_to_smt_type T) =
        native_model_var_lookup N s (__eo_to_smt_type T)

theorem model_agrees_except_on_eo_env_refl
    (except bound : List EoVarKey) (M : SmtModel) :
  model_agrees_except_on_eo_env except bound M M :=
by
  exact ⟨model_agrees_on_globals_refl M, by intro s T _; rfl⟩

theorem model_agrees_except_on_eo_env_symm
    {except bound : List EoVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_eo_env except bound M N) :
  model_agrees_except_on_eo_env except bound N M :=
by
  refine ⟨?_, ?_⟩
  · exact ⟨by intro s T; exact (hAgree.globals.1 s T).symm,
      by intro fid T U; exact (hAgree.globals.2 fid T U).symm⟩
  · intro s T hKey
    exact (hAgree.vars_eq s T hKey).symm

theorem model_agrees_except_on_eo_env_push_same
    {except bound : List EoVarKey} {M N : SmtModel}
    {s : native_String} {T : Term} {v : SmtValue}
    (hAgree : model_agrees_except_on_eo_env except bound M N) :
  model_agrees_except_on_eo_env except ((s, T) :: bound)
    (native_model_push M s (__eo_to_smt_type T) v)
    (native_model_push N s (__eo_to_smt_type T) v) :=
by
  refine ⟨model_agrees_on_globals_push₂ hAgree.globals, ?_⟩
  intro s' T' hKeyAllowed
  by_cases hKey :
      ({ isVar := true, name := s', ty := __eo_to_smt_type T' } :
          SmtModelKey) =
        { isVar := true, name := s, ty := __eo_to_smt_type T }
  · simp [native_model_var_lookup, native_model_push, hKey]
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

theorem native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N) :
  native_model_var_lookup M s (__eo_to_smt_type T) =
    native_model_var_lookup N s (__eo_to_smt_type T) :=
by
  rcases contains_atomic_term_list_free_rec_var_false_cases hNoFree with
    hNotExcept | hBoundVar
  · have hNotMem :
        (s, T) ∉ exceptVars :=
      EoVarEnvPerm.not_mem_of_find_neg_true hExcept hNotExcept
    exact hAgree.vars_eq s T (Or.inr hNotMem)
  · have hMem :
        (s, T) ∈ boundVars :=
      EoVarEnvPerm.mem_of_find_neg_false hBound hBoundVar
    exact hAgree.vars_eq s T (Or.inl hMem)

theorem smt_model_eval_var_eq_of_contains_atomic_term_list_free_rec_false
    {s : native_String} {T except bound : Term}
    {exceptVars boundVars : List EoVarKey}
    {M N : SmtModel}
    (hExcept : EoVarEnvPerm except exceptVars)
    (hBound : EoVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Var (Term.String s) T) except bound =
        Term.Boolean false)
    (hAgree :
      model_agrees_except_on_eo_env exceptVars boundVars M N) :
  __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
    __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) :=
by
  rw [__smtx_model_eval.eq_def, __smtx_model_eval.eq_def]
  exact
    native_model_var_lookup_eq_of_contains_atomic_term_list_free_rec_var_false
      hExcept hBound hNoFree hAgree

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
