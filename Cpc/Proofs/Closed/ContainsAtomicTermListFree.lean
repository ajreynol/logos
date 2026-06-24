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

/--
Main semantic bridge needed by quantifier unused-variable rules.

If `__contains_atomic_term_list_free_rec t except bound` says that no variable
from `except` occurs free in `t` under the current bound-variable stack, then
the SMT interpretation of `t` is insensitive to model changes on exactly those
excepted variables.

The proof is intentionally isolated here: it should be a structural induction on
`t`, with the quantifier-shaped branch extending `bound` and using
`model_agrees_except_on_env_push_same`.
-/
theorem smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false
    {t except bound : Term}
    {exceptVars boundVars : List SmtVarKey}
    {M N : SmtModel}
    (hTrans : eoHasSmtTranslation t)
    (hExcept : EoSmtVarEnvPerm except exceptVars)
    (hBound : EoSmtVarEnvPerm bound boundVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec t except bound =
        Term.Boolean false)
    (hAgree : model_agrees_except_on_env exceptVars boundVars M N) :
  __smtx_model_eval M (__eo_to_smt t) =
    __smtx_model_eval N (__eo_to_smt t) :=
by
  sorry
