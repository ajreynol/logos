import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Canonical
import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import Cpc.Proofs.Closed.Substitute

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
# CPC rule `instantiate` — proof scaffold

The `instantiate` rule has one premise, a universally quantified formula, and one
argument, a list of instantiation terms:

```
premise:  (forall (x1 T1) ... (xn Tn) F)
arg:      ts = [t1, ..., tn]
conclude: F[x1 ↦ t1, ..., xn ↦ tn]
```

Operationally the conclusion is `__substitute_simul_rec false F xs ts nil`
(see `__eo_prog_instantiate`, `Cpc/Logos.lean:3775`).

The soundness obligation (`StepRuleProperties.facts_of_true`) is:

> if `(forall xs F)` interprets `true` in `M`, then `F[xs ↦ ts]` interprets `true` in `M`.

The proof factors into four pieces, in dependency order:

1. **`pushSubstModel`** — the model that assigns each bound variable `xᵢ:Tᵢ` the
   value of `tᵢ` evaluated in the *ambient* `M` (simultaneous substitution: the
   `tᵢ` see `M`, not the partially-extended model).

2. **`substitute_simul_eval`** (THE crux, `sorry`) — evaluating the translation of
   the substituted body in `M` equals evaluating the translation of `F` in
   `pushSubstModel M xs ts`. This is the capture-avoiding substitution /
   coincidence lemma, proved by structural induction. See the doc comment on the
   lemma for the case breakdown and the `bvs`-generalisation it needs. The
   per-case machinery (`SubstFalseRel`, `substFalse_eval_var`, `substFalseRel_push`)
   already lives in `Cpc/Proofs/Closed/Substitute.lean`; what remains is the
   well-founded recursion tying them together (analogous to
   `smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt`).

3. **`instantiate_body_true`** (`sorry`) — from `forall xs F` true and the
   well-typedness of `ts`, the body is true under `pushSubstModel M xs ts`. The
   pure quantifier-instantiation part is now proved by
   `forall_instantiation_body_true`; the remaining bridge is to show that
   `pushSubstModel M xs ts` supplies canonical, correctly typed assignments for
   the binder list. The support lemmas `pushSubstModel_agrees_except` and
   `pushSubstModel_total_typed_of_actuals` isolate the agreement and total-typed
   halves of that bridge.

4. **`prog_instantiate_shape`** (DONE) — a non-`Stuck` result forces the
   premise to be `forall xs F` and pins the conclusion to the substitution.

Status (2026-06-26):
  * `prog_instantiate_shape`  — PROVEN.
  * `instantiate_sound`       — PROVEN (pure wiring of the two cruxes + `hResBool`).
  * main theorem `hWf`        — PROVEN (premise is Bool-typed ⇒ translatable).
  * `substitute_simul_eval`   — sorry (crux; see above).
  * `instantiate_body_true`   — one bridge sorry remains: prove `pushSubstModel`
    is an admissible instantiation model from the actuals/binders invariants.
  * `substitute_simul_has_smt_translation_of_typeof_bool` — sorry; needs a
    *type-preservation* lemma for `__substitute_simul_rec` (translatable
    premise + translatable actuals + checker Bool result ⇒ SMT Bool result).
    No generic `__eo_typeof t = Bool → eo_has_smt_translation t` exists, so
    this is its own structural induction.

The main theorem then wires these together with the standard single-arg /
single-premise boilerplate (mirrors `BooleanElimSupport.cmd_step_and_elim_properties`).
-/

namespace InstantiateRule

/-- Model extension realising a simultaneous substitution `[xs ↦ ts]`.

Recurses over the parallel EO cons-lists `xs` (binders `Var (String s) T`) and
`ts` (instantiation terms), pushing `s : __eo_to_smt_type T` to the value of the
corresponding term **evaluated in the original `M`**. Ill-formed / mismatched
lists fall through to `M` unchanged.

Note: for distinct binder variables the push order is irrelevant. The `nil`-`bvs`
case of the substitution is exactly substitution into this model. -/
noncomputable def pushSubstModel (M : SmtModel) : Term -> Term -> SmtModel
  | (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs),
    (Term.Apply (Term.Apply Term.__eo_List_cons t) ts) =>
      native_model_push (pushSubstModel M xs ts) s (__eo_to_smt_type T)
        (__smtx_model_eval M (__eo_to_smt t))
  | _, _ => M

@[simp] theorem pushSubstModel_nil_left (M : SmtModel) (ts : Term) :
    pushSubstModel M Term.__eo_List_nil ts = M := by
  cases ts <;> rfl

@[simp] theorem pushSubstModel_nil_right (M : SmtModel) (xs : Term) :
    pushSubstModel M xs Term.__eo_List_nil = M := by
  cases xs with
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g <;> cases x <;> try rfl
          case Var name T =>
            cases name <;> rfl
      | _ => rfl
  | _ => rfl

@[simp] theorem pushSubstModel_cons_var
    (M : SmtModel) (s : native_String) (T xs t ts : Term) :
    pushSubstModel M
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) ts) =
      native_model_push (pushSubstModel M xs ts) s (__eo_to_smt_type T)
        (__smtx_model_eval M (__eo_to_smt t)) := by
  rfl

/-- One `pushSubstModel` cons step preserves globals whenever the tail does. -/
theorem pushSubstModel_cons_var_globals
    (M : SmtModel) (s : native_String) (T xs t ts : Term)
    (hTail : model_agrees_on_globals M (pushSubstModel M xs ts)) :
    model_agrees_on_globals M
      (pushSubstModel M
        (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) ts)) := by
  rw [pushSubstModel_cons_var]
  exact model_agrees_on_globals_trans hTail
    (model_agrees_on_globals_push (pushSubstModel M xs ts) s
      (__eo_to_smt_type T) (__smtx_model_eval M (__eo_to_smt t)))

/-- The substitution model only changes variable assignments, never globals. -/
theorem pushSubstModel_globals
    (M : SmtModel) : ∀ xs ts : Term,
    model_agrees_on_globals M (pushSubstModel M xs ts)
  | xs, ts => by
      cases xs with
      | Apply f xsTail =>
          cases f with
          | Apply g x =>
              cases g <;> try exact model_agrees_on_globals_refl M
              case __eo_List_cons =>
                cases x <;> try exact model_agrees_on_globals_refl M
                case Var name T =>
                  cases name <;> try exact model_agrees_on_globals_refl M
                  case String s =>
                    cases ts with
                    | Apply ft tsTail =>
                        cases ft with
                        | Apply gt t =>
                            cases gt <;> try exact model_agrees_on_globals_refl M
                            case __eo_List_cons =>
                              exact
                                pushSubstModel_cons_var_globals M s T xsTail t tsTail
                                  (pushSubstModel_globals M xsTail tsTail)
                        | _ => exact model_agrees_on_globals_refl M
                    | _ => exact model_agrees_on_globals_refl M
          | _ => exact model_agrees_on_globals_refl M
      | _ => exact model_agrees_on_globals_refl M
termination_by xs ts => xs

theorem model_agrees_except_on_env_weaken_except
    {except except' bound : List SmtVarKey} {M N : SmtModel}
    (hSub : ∀ key, key ∈ except -> key ∈ except')
    (hAgree : model_agrees_except_on_env except bound M N) :
    model_agrees_except_on_env except' bound M N := by
  refine ⟨hAgree.globals, ?_⟩
  intro s T hAllowed
  apply hAgree.vars_eq
  rcases hAllowed with hBound | hNotExcept'
  · exact Or.inl hBound
  · exact Or.inr (by
      intro hMem
      exact hNotExcept' (hSub (s, T) hMem))

theorem smtVar_mem_cons_map_tail
    {s : native_String} {T : Term} {vars : List EoVarKey} {key : SmtVarKey}
    (hMem : key ∈ vars.map EoVarKey.toSmt) :
    key ∈ ((s, T) :: vars).map EoVarKey.toSmt := by
  exact List.Mem.tail _ hMem

theorem model_agrees_except_on_env_weaken_cons
    {s : native_String} {T : Term} {vars : List EoVarKey}
    {bound : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env (vars.map EoVarKey.toSmt) bound M N) :
    model_agrees_except_on_env (((s, T) :: vars).map EoVarKey.toSmt) bound M N :=
  model_agrees_except_on_env_weaken_except
    (fun key hMem => smtVar_mem_cons_map_tail hMem) hAgree

theorem model_agrees_on_env_of_agrees_everywhere
    {vars : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env [] [] M N) :
    model_agrees_on_env vars M N := by
  refine ⟨hAgree.globals, ?_⟩
  intro s T _hMem
  exact hAgree.vars_eq s T (Or.inr (by simp))

/-- `pushSubstModel` agrees with the original model outside the binder keys. -/
theorem pushSubstModel_agrees_except
    (M : SmtModel) :
    ∀ {xs : Term} {vars : List EoVarKey} (ts : Term),
      EoVarEnv xs vars ->
        model_agrees_except_on_env (vars.map EoVarKey.toSmt) []
          (pushSubstModel M xs ts) M
  | _, _, ts, EoVarEnv.nil => by
      simp [pushSubstModel]
      exact model_agrees_except_on_env_refl [] [] M
  | _, _, ts, EoVarEnv.cons (s := s) (T := T) (env := env) (vars := vars) hTail => by
      have hBase :
          model_agrees_except_on_env (((s, T) :: vars).map EoVarKey.toSmt) [] M M :=
        model_agrees_except_on_env_weaken_cons
          (s := s) (T := T) (vars := vars) (bound := [])
          (M := M) (N := M)
          (model_agrees_except_on_env_refl (vars.map EoVarKey.toSmt) [] M)
      cases ts with
      | Apply ft tsTail =>
          cases ft with
          | Apply gt t =>
              cases gt <;> try simpa [pushSubstModel] using hBase
              case __eo_List_cons =>
                have hTailAgree :
                    model_agrees_except_on_env (vars.map EoVarKey.toSmt) []
                      (pushSubstModel M env tsTail) M :=
                  pushSubstModel_agrees_except M tsTail hTail
                have hTailAgreeWeak :
                    model_agrees_except_on_env (((s, T) :: vars).map EoVarKey.toSmt) []
                      (pushSubstModel M env tsTail) M :=
                  model_agrees_except_on_env_weaken_cons
                    (s := s) (T := T) (vars := vars) (bound := [])
                    (M := pushSubstModel M env tsTail) (N := M)
                    hTailAgree
                have hHeadMem :
                    (s, __eo_to_smt_type T) ∈ ((s, T) :: vars).map EoVarKey.toSmt :=
                  List.mem_map.2 ⟨(s, T), List.Mem.head _, rfl⟩
                simpa [pushSubstModel, EoVarKey.toSmt] using
                  model_agrees_except_on_env_push_left hTailAgreeWeak
                    hHeadMem (by simp)
          | _ =>
              simpa [pushSubstModel] using hBase
      | _ =>
          simpa [pushSubstModel] using hBase

/-- A translatable universal quantifier has a Boolean-translatable body. -/
theorem forall_body_has_bool_type_of_has_smt_translation
    (xs F : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) :
    RuleProofs.eo_has_bool_type F := by
  unfold RuleProofs.eo_has_smt_translation at hForall
  unfold RuleProofs.eo_has_bool_type
  by_cases hNil : xs = Term.__eo_List_nil
  · subst xs
    exact False.elim (by
      apply hForall
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none)
  · have hForallNN :
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))) ≠
          SmtType.None := by
      cases xs with
      | __eo_List_nil =>
          exact False.elim (hNil rfl)
      | _ =>
          change
            __smtx_typeof
                (SmtTerm.not
                  (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt F)))) ≠
              SmtType.None at hForall
          exact hForall
    have hNotBool :
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))) =
          SmtType.Bool :=
      smtx_typeof_not_eq_bool_of_non_none
        (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) hForallNN
    have hExistsBool :
        __smtx_typeof
            (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) =
          SmtType.Bool :=
      smtx_typeof_not_arg_eq_bool
        (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) hNotBool
    have hBodyNotBool :
        __smtx_typeof (SmtTerm.not (__eo_to_smt F)) = SmtType.Bool :=
      TranslationProofs.eo_to_smt_exists_body_bool_of_bool xs
        (SmtTerm.not (__eo_to_smt F)) hExistsBool
    exact smtx_typeof_not_arg_eq_bool (__eo_to_smt F) hBodyNotBool

/-- A translatable universal quantifier carries a reflected EO binder environment. -/
theorem forall_binders_env_of_has_smt_translation
    (xs F : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) :
    ∃ vars, EoVarEnv xs vars := by
  exact eo_var_env_of_forall_has_smt_translation
    (by
      simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
        using hForall)

/-- Peels one binder from a Boolean-typed encoded existential. -/
theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  intro hTy
  have hExists :
      __smtx_typeof
          (SmtTerm.exists s (__eo_to_smt_type T)
            (__eo_to_smt_exists xs body)) = SmtType.Bool := by
    simpa [__eo_to_smt_exists] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists xs body)) := by
    unfold term_has_non_none_type
    rw [hExists]
    simp
  exact exists_body_bool_of_non_none hNN

/-- The head type of a Boolean-typed encoded existential is well-formed. -/
theorem smtx_type_wf_of_exists_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠
        SmtType.None := by
    intro hNone
    have hExists :
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs body)) = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    rw [smtx_typeof_exists_term_eq, hTail] at hExists
    simp [native_ite, native_Teq, hNone] at hExists
  exact smtx_typeof_guard_wf_wf_of_non_none
    (__eo_to_smt_type T) SmtType.Bool hGuardNN

/-- Every binder in a Boolean-typed encoded existential has a well-formed type. -/
theorem smtx_type_wf_of_eo_var_env_exists_bool
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool) :
    ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true := by
  induction hEnv generalizing body with
  | nil =>
      intro s T hMem
      cases hMem
  | cons hTail ih =>
      rename_i s T xs tailVars
      intro s' T' hMem
      cases hMem with
      | head =>
          exact smtx_type_wf_of_exists_cons_bool s T xs body hTy
      | tail _ hTailMem =>
          have hTailTy :
              __smtx_typeof (__eo_to_smt_exists xs body) =
                SmtType.Bool :=
            smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
          exact ih hTailTy s' T' hTailMem

/-- A translatable universal quantifier has well-formed SMT binder types. -/
theorem forall_binder_types_wf_of_has_smt_translation
    {xs F : Term} {vars : List EoVarKey}
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hEnv : EoVarEnv xs vars) :
    ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true := by
  cases hEnv with
  | nil =>
      intro s T hMem
      cases hMem
  | cons hTail =>
      rename_i s T env tailVars
      have hNotTy :
          __smtx_typeof
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F)))) =
            SmtType.Bool :=
        smtx_typeof_not_eq_bool_of_non_none
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (SmtTerm.not (__eo_to_smt F)))
          (by
            change
              __smtx_typeof
                  (SmtTerm.not
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T)) env)
                      (SmtTerm.not (__eo_to_smt F)))) ≠
                SmtType.None
            simpa [RuleProofs.eo_has_smt_translation] using hForall)
      have hExistsTy :
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (SmtTerm.not (__eo_to_smt F))) =
            SmtType.Bool :=
        smtx_typeof_not_arg_eq_bool
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (SmtTerm.not (__eo_to_smt F)))
          hNotTy
      exact
        smtx_type_wf_of_eo_var_env_exists_bool
          (EoVarEnv.cons (s := s) (T := T) hTail) hExistsTy

/-- A translatable universal quantifier has a translatable body. -/
theorem forall_body_has_smt_translation_of_has_smt_translation
    (xs F : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) :
    RuleProofs.eo_has_smt_translation F :=
  RuleProofs.eo_has_smt_translation_of_has_bool_type F
    (forall_body_has_bool_type_of_has_smt_translation xs F hForall)

/-- A translatable universal quantifier has a nonempty binder list. -/
theorem forall_binders_non_nil_of_has_smt_translation
    (xs F : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) :
    xs ≠ Term.__eo_List_nil := by
  intro hNil
  subst xs
  unfold RuleProofs.eo_has_smt_translation at hForall
  exact hForall (by
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none)

/-- Unfolds the EO-to-SMT encoding of a nonempty universal quantifier. -/
theorem eo_to_smt_forall_eq_of_non_nil
    (xs F : Term) (hXs : xs ≠ Term.__eo_List_nil) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) =
      SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) := by
  cases xs with
  | __eo_List_nil => exact False.elim (hXs rfl)
  | _ => rfl

/-- A translated EO term evaluates to a canonical value of its SMT type. -/
theorem eo_to_smt_eval_typed_canonical
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t) :
    __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) ∧
      __smtx_value_canonical (__smtx_model_eval M (__eo_to_smt t)) := by
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    simpa [RuleProofs.eo_has_smt_translation, term_has_non_none_type] using hTrans
  exact ⟨smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hNN,
    Smtm.model_eval_canonical M hM (__eo_to_smt t) hNN⟩

/-- The semantic shape of a model obtained by instantiating an EO binder list. -/
inductive ForallInstantiationModel : SmtModel -> Term -> SmtModel -> Prop where
  | nil (M : SmtModel) :
      ForallInstantiationModel M Term.__eo_List_nil M
  | cons {M N : SmtModel} {s : native_String} {T env : Term} {v : SmtValue} :
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      __smtx_typeof_value v = __eo_to_smt_type T ->
      __smtx_value_canonical_bool v = true ->
      ForallInstantiationModel
        (native_model_push M s (__eo_to_smt_type T) v) env N ->
      ForallInstantiationModel M
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) env) N

/--
Builds the quantifier-assignment model obtained by reading each binder value
from `Source` and pushing it, in binder order, onto the base model `M`.
-/
noncomputable def forallAssignmentModel (Source : SmtModel) :
    SmtModel -> Term -> SmtModel
  | M,
    (Term.Apply (Term.Apply Term.__eo_List_cons
      (Term.Var (Term.String s) T)) env) =>
      forallAssignmentModel Source
        (native_model_push M s (__eo_to_smt_type T)
          (native_model_var_lookup Source s (__eo_to_smt_type T)))
        env
  | M, _ => M

@[simp] theorem forallAssignmentModel_nil
    (Source M : SmtModel) :
    forallAssignmentModel Source M Term.__eo_List_nil = M := by
  rfl

@[simp] theorem forallAssignmentModel_cons_var
    (Source M : SmtModel) (s : native_String) (T env : Term) :
    forallAssignmentModel Source M
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) env) =
      forallAssignmentModel Source
        (native_model_push M s (__eo_to_smt_type T)
          (native_model_var_lookup Source s (__eo_to_smt_type T)))
        env := by
  rfl

/-- Well-typed canonical instantiation preserves total typedness of models. -/
theorem ForallInstantiationModel.total_typed
    {M N : SmtModel} {xs : Term}
    (hInst : ForallInstantiationModel M xs N)
    (hM : model_total_typed M) :
    model_total_typed N := by
  induction hInst with
  | nil M =>
      exact hM
  | cons hWf hValTy hValCan _hTail ih =>
      rename_i M N s T env v
      exact ih
        (model_total_typed_push hM s (__eo_to_smt_type T) v
          hWf hValTy
          (by simpa [__smtx_value_canonical] using hValCan))

/--
An instantiation model agrees with its base model outside the quantified binder
keys. The instantiated values may differ exactly on those keys.
-/
theorem ForallInstantiationModel.agrees_except
    {M N : SmtModel} {xs : Term} {vars : List EoVarKey}
    (hInst : ForallInstantiationModel M xs N)
    (hEnv : EoVarEnv xs vars) :
    model_agrees_except_on_env (vars.map EoVarKey.toSmt) [] N M := by
  induction hInst generalizing vars with
  | nil M =>
      cases hEnv
      exact model_agrees_except_on_env_refl [] [] M
  | cons hWf hValTy hValCan hTail ih =>
      rename_i M N s T env v
      cases hEnv with
      | cons hEnvTail =>
          rename_i tailVars
          have hTailAgree :
              model_agrees_except_on_env
                (tailVars.map EoVarKey.toSmt) [] N
                (native_model_push M s (__eo_to_smt_type T) v) :=
            ih hEnvTail
          have hPushGlobals :
              model_agrees_on_globals
                (native_model_push M s (__eo_to_smt_type T) v) M :=
            ⟨by
                intro s' T'
                exact
                  ((model_agrees_on_globals_push M s (__eo_to_smt_type T) v).1
                    s' T').symm,
              by
                intro fid T' U'
                exact
                  ((model_agrees_on_globals_push M s (__eo_to_smt_type T) v).2
                    fid T' U').symm⟩
          refine
            ⟨model_agrees_on_globals_trans hTailAgree.globals hPushGlobals, ?_⟩
          intro s' T' hAllowed
          rcases hAllowed with hBound | hNotExcept
          · cases hBound
          · have hNotTail :
                (s', T') ∉ tailVars.map EoVarKey.toSmt := by
              intro hMem
              exact hNotExcept (List.Mem.tail _ hMem)
            have hKeyNe :
                ({ isVar := true, name := s', ty := T' } : SmtModelKey) ≠
                  { isVar := true, name := s, ty := __eo_to_smt_type T } := by
              intro hKey
              apply hNotExcept
              cases hKey
              simp [EoVarKey.toSmt]
            have hTailEq :
                native_model_var_lookup N s' T' =
                  native_model_var_lookup
                    (native_model_push M s (__eo_to_smt_type T) v) s' T' :=
              hTailAgree.vars_eq s' T' (Or.inr hNotTail)
            have hPushEq :
                native_model_var_lookup
                    (native_model_push M s (__eo_to_smt_type T) v) s' T' =
                  native_model_var_lookup M s' T' := by
              simp [native_model_var_lookup, native_model_push, hKeyNe]
            exact hTailEq.trans hPushEq

/--
Values read from a total model produce a legal instantiation model for any
well-formed binder environment.
-/
theorem forallAssignmentModel_instantiation
    (Source : SmtModel) (hSource : model_total_typed Source)
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (M : SmtModel) :
    ForallInstantiationModel M xs
      (forallAssignmentModel Source M xs) := by
  induction hEnv generalizing M with
  | nil =>
      simp [forallAssignmentModel]
      exact ForallInstantiationModel.nil M
  | cons hTail ih =>
      rename_i s T env tailVars
      rw [forallAssignmentModel_cons_var]
      let ST := __eo_to_smt_type T
      have hHeadWf : __smtx_type_wf ST = true :=
        hWf s T (List.Mem.head _)
      refine ForallInstantiationModel.cons (M := M)
        (N := forallAssignmentModel Source
          (native_model_push M s ST
            (native_model_var_lookup Source s ST)) env)
        (s := s) (T := T) (env := env)
        (v := native_model_var_lookup Source s ST)
        (by simpa [ST] using hHeadWf)
        (by
          simpa [ST] using
            model_total_typed_var_lookup hSource s ST hHeadWf)
        (by
          simpa [ST, __smtx_value_canonical] using
            model_total_typed_var_lookup_canonical hSource s ST hHeadWf)
        ?_
      exact ih
        (by
          intro s' T' hMem
          exact hWf s' T' (List.Mem.tail _ hMem))
        (native_model_push M s ST
          (native_model_var_lookup Source s ST))

theorem forallAssignmentModel_total_typed
    (Source M : SmtModel)
    (hSource : model_total_typed Source) (hM : model_total_typed M)
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true) :
    model_total_typed (forallAssignmentModel Source M xs) :=
  (forallAssignmentModel_instantiation Source hSource hEnv hWf M).total_typed hM

theorem forallAssignmentModel_agrees_except_base
    (Source M : SmtModel)
    {xs : Term} {vars : List EoVarKey}
    (hSource : model_total_typed Source)
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true) :
    model_agrees_except_on_env (vars.map EoVarKey.toSmt) []
      (forallAssignmentModel Source M xs) M :=
  (forallAssignmentModel_instantiation Source hSource hEnv hWf M).agrees_except hEnv

/--
If `M` and `Source` already agree outside the binder keys, assigning the binder
keys from `Source` makes the resulting model agree with `Source` everywhere.
-/
theorem forallAssignmentModel_agrees_source
    (Source M : SmtModel)
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hBase :
      model_agrees_except_on_env (vars.map EoVarKey.toSmt) [] M Source) :
    model_agrees_except_on_env [] []
      (forallAssignmentModel Source M xs) Source := by
  induction hEnv generalizing M with
  | nil =>
      simpa [forallAssignmentModel] using hBase
  | cons hTail ih =>
      rename_i s T env tailVars
      rw [forallAssignmentModel_cons_var]
      let ST := __eo_to_smt_type T
      let v := native_model_var_lookup Source s ST
      have hPushGlobals :
          model_agrees_on_globals (native_model_push M s ST v) Source := by
        have hPushToBase :
            model_agrees_on_globals (native_model_push M s ST v) M :=
          ⟨by
              intro s' T'
              exact ((model_agrees_on_globals_push M s ST v).1 s' T').symm,
            by
              intro fid T' U'
              exact
                ((model_agrees_on_globals_push M s ST v).2 fid T' U').symm⟩
        exact model_agrees_on_globals_trans hPushToBase hBase.globals
      have hPushBase :
          model_agrees_except_on_env (tailVars.map EoVarKey.toSmt) []
            (native_model_push M s ST v) Source := by
        refine ⟨hPushGlobals, ?_⟩
        intro s' T' hAllowed
        rcases hAllowed with hBound | hNotTail
        · cases hBound
        · by_cases hPair : (s', T') = (s, ST)
          · cases hPair
            simp [native_model_var_lookup, native_model_push, v]
          · have hKeyNe :
                ({ isVar := true, name := s', ty := T' } : SmtModelKey) ≠
                  { isVar := true, name := s, ty := ST } := by
              intro hKey
              apply hPair
              cases hKey
              rfl
            have hNotFull :
                (s', T') ∉ ((s, T) :: tailVars).map EoVarKey.toSmt := by
              intro hMem
              cases hMem with
              | head =>
                  exact hPair rfl
              | tail _ hTailMem =>
                  exact hNotTail hTailMem
            have hPushEq :
                native_model_var_lookup
                    (native_model_push M s ST v) s' T' =
                  native_model_var_lookup M s' T' := by
              simp [native_model_var_lookup, native_model_push, hKeyNe]
            exact hPushEq.trans (hBase.vars_eq s' T' (Or.inr hNotFull))
      exact ih (native_model_push M s ST v) hPushBase

/-- Actuals are well-typed for the binders they instantiate in the ambient model. -/
inductive SubstActualsTyped (M : SmtModel) : Term -> Term -> Prop where
  | nil (ts : Term) :
      SubstActualsTyped M Term.__eo_List_nil ts
  | cons {s : native_String} {T env t ts : Term} :
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __eo_to_smt_type T ->
      __smtx_value_canonical_bool (__smtx_model_eval M (__eo_to_smt t)) = true ->
      SubstActualsTyped M env ts ->
      SubstActualsTyped M
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) env)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) ts)

theorem pushSubstModel_total_typed_of_actuals
    (M : SmtModel) (hM : model_total_typed M)
    {xs ts : Term}
    (hActuals : SubstActualsTyped M xs ts) :
    model_total_typed (pushSubstModel M xs ts) := by
  induction hActuals with
  | nil ts =>
      simp [pushSubstModel]
      exact hM
  | cons hWf hValTy hValCan _hTail ih =>
      rename_i s T env t ts
      rw [pushSubstModel_cons_var]
      exact model_total_typed_push ih s (__eo_to_smt_type T)
        (__smtx_model_eval M (__eo_to_smt t)) hWf hValTy
        (by simpa [__smtx_value_canonical] using hValCan)

theorem smtx_model_eval_not_true_iff (v : SmtValue) :
    __smtx_model_eval_not v = SmtValue.Boolean true ↔
      v = SmtValue.Boolean false := by
  cases v <;> simp [__smtx_model_eval_not, SmtEval.native_not]

theorem smtx_model_eval_not_not_true_iff (v : SmtValue) :
    __smtx_model_eval_not (__smtx_model_eval_not v) =
        SmtValue.Boolean true ↔
      v = SmtValue.Boolean true := by
  cases v <;> simp [__smtx_model_eval_not, SmtEval.native_not]

theorem forall_instantiation_exists_type_bool
    {M N : SmtModel} {xs : Term}
    (hInst : ForallInstantiationModel M xs N)
    (body : SmtTerm)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction hInst generalizing body with
  | nil M =>
      simpa [__eo_to_smt_exists] using hBodyTy
  | cons hWf _hValTy _hValCan _hTail ih =>
      rename_i M N s T env v
      exact
        closed_smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
          s T env body hWf (ih body hBodyTy)

/--
If an encoded universal quantifier is true, its body is true in any model that
is obtained by a well-typed canonical instantiation of its binder list.
-/
theorem forall_instantiation_body_true
    {M N : SmtModel} {xs : Term} {body : SmtTerm}
    (hInst : ForallInstantiationModel M xs N)
    (hM : model_total_typed M)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hEval :
      __smtx_model_eval M
        (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
        SmtValue.Boolean true) :
    __smtx_model_eval N body = SmtValue.Boolean true := by
  induction hInst generalizing body with
  | nil M =>
      exact
        (smtx_model_eval_not_not_true_iff
          (__smtx_model_eval M body)).1
          (by simpa [__eo_to_smt_exists, __smtx_model_eval] using hEval)
  | cons hWf hValTy hValCan hTail ih =>
      rename_i M N s T env v
      let ST := __eo_to_smt_type T
      let tail := __eo_to_smt_exists env (SmtTerm.not body)
      have hOuterNot :
          __smtx_model_eval_not
              (__smtx_model_eval M (SmtTerm.exists s ST tail)) =
            SmtValue.Boolean true := by
        simpa [ST, tail, __eo_to_smt_exists, __smtx_model_eval] using hEval
      have hExistsFalse :
          __smtx_model_eval M (SmtTerm.exists s ST tail) =
            SmtValue.Boolean false :=
        (smtx_model_eval_not_true_iff
          (__smtx_model_eval M (SmtTerm.exists s ST tail))).1 hOuterNot
      have hNoSat :
          ¬ ∃ w : SmtValue,
            __smtx_typeof_value w = ST ∧
              __smtx_value_canonical_bool w = true ∧
              __smtx_model_eval (native_model_push M s ST w) tail =
                SmtValue.Boolean true := by
        intro hSat
        have hExistsTrue :
            __smtx_model_eval M (SmtTerm.exists s ST tail) =
              SmtValue.Boolean true := by
          simp [__smtx_model_eval, hSat]
        rw [hExistsFalse] at hExistsTrue
        cases hExistsTrue
      have hNotBodyTy :
          __smtx_typeof (SmtTerm.not body) = SmtType.Bool :=
        smtx_typeof_not_eq_bool_of_non_none body
          (by
            rw [typeof_not_eq, hBodyTy]
            simp [native_ite, native_Teq])
      have hTailTy :
          __smtx_typeof tail = SmtType.Bool := by
        simpa [tail] using
          forall_instantiation_exists_type_bool hTail
            (SmtTerm.not body) hNotBodyTy
      have hPushTotal :
          model_total_typed (native_model_push M s ST v) :=
        model_total_typed_push hM s ST v
          (by simpa [ST] using hWf)
          (by simpa [ST] using hValTy)
          (by simpa [__smtx_value_canonical] using hValCan)
      have hTailNotTrue :
          __smtx_model_eval (native_model_push M s ST v) tail ≠
            SmtValue.Boolean true := by
        intro hTailTrue
        exact hNoSat ⟨v, by simpa [ST] using hValTy, hValCan, hTailTrue⟩
      rcases smt_model_eval_bool_is_boolean
          (native_model_push M s ST v) hPushTotal tail hTailTy with
        ⟨b, hTailEval⟩
      cases b
      · have hEvalTail :
            __smtx_model_eval (native_model_push M s ST v)
                (SmtTerm.not tail) =
              SmtValue.Boolean true := by
          simp [__smtx_model_eval, hTailEval, __smtx_model_eval_not,
            SmtEval.native_not]
        exact ih hPushTotal hBodyTy (by simpa [tail] using hEvalTail)
      · exact False.elim (hTailNotTrue hTailEval)

/--
Pure universal instantiation using binder values read from an arbitrary total
source model.
-/
theorem forall_assignment_body_true
    {M Source : SmtModel} {xs : Term} {vars : List EoVarKey}
    {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hSource : model_total_typed Source)
    (hM : model_total_typed M)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hEval :
      __smtx_model_eval M
        (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
        SmtValue.Boolean true) :
    __smtx_model_eval (forallAssignmentModel Source M xs) body =
      SmtValue.Boolean true :=
  forall_instantiation_body_true
    (forallAssignmentModel_instantiation Source hSource hEnv hWf M)
    hM hBodyTy hEval

/--
SMT-translatability preservation for the instantiate substitution result.

The checker gives the last hypothesis (`__eo_typeof result = Bool`) after running
the program, while `cmdTranslationOk` only gives elementwise translation of the
actuals `ts`. This is the structural substitution theorem, separate from the
semantic substitution lemma below.
-/
theorem substitute_simul_has_smt_translation_of_typeof_bool
    (F xs ts : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) := by
  have hBodyTrans :
      RuleProofs.eo_has_smt_translation F :=
    forall_body_has_smt_translation_of_has_smt_translation xs F hForall
  rcases forall_binders_env_of_has_smt_translation xs F hForall with
    ⟨binderVars, hXsEnv⟩
  sorry

/--
Typing preservation for the instantiate substitution result, packaged as SMT
Boolean-typedness.
-/
theorem substitute_simul_has_bool_type_of_typeof_bool
    (F xs ts : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
        Term.Bool) :
    RuleProofs.eo_has_bool_type
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) :=
  RuleProofs.eo_typeof_bool_implies_has_bool_type
    (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)
    (substitute_simul_has_smt_translation_of_typeof_bool F xs ts
      hForall hTs hTy)
    hTy

/--
**Substitution–evaluation lemma (crux).**

Evaluating the SMT translation of the simultaneously-substituted body in `M`
coincides with evaluating the translation of `F` in the extended model
`pushSubstModel M xs ts`.

This is stated for the top-level `bvs = nil`; it is proved by structural
induction on `F` after generalising over an accumulator `bvs` of locally bound
variables (the third recursion argument of `__substitute_simul_rec`). The
generalised invariant is: variables occurring in `bvs` are *not* substituted
(they are bound by an inner quantifier) and remain interpreted by the ambient
model, while variables in `xs \ bvs` are replaced.

Induction cases (following `__substitute_simul_rec`, `Cpc/Logos.lean:2298`):

* **Application `Apply f a`** — translation is structural (`SmtTerm` mirrors the
  EO head), so `eval` commutes with the recursive substitutions on `f` and `a`.
* **Quantifier `Apply (Apply q (cons v vs)) a`** — the capture-avoidance
  side-condition `__contains_atomic_term_list_free_rec ts (cons v vs) = false`
  guarantees the substituted terms have no free occurrence of the bound `v`, so
  pushing `v` and substituting commute (the `bvs` accumulator gains `v`). Uses
  the `native_model_push` commutation lemmas in `Cpc/Proofs/Closed/Support.lean`.
* **Variable `Var s S`** — if `s ∈ bvs` it is kept (bound); otherwise it is
  looked up in `xs` and either replaced by the matching `ts` entry (whose value
  is exactly what `pushSubstModel` assigns) or kept if absent.
* **Closed atom (default)** — `__is_closed_rec` holds, the term is unchanged and
  ground, so its evaluation is model-independent.

Side hypotheses to be threaded through (placeholders — to be pinned down against
the typing/translation context in the main theorem):
* `F` has an SMT translation and is `Bool`-typed under the binders;
* `xs` is a well-formed binder list and `ts` matches it in length/type;
* `model_total_typed M`.
-/
theorem substitute_simul_eval
    (M : SmtModel) (hM : model_total_typed M)
    (F xs ts : Term) :
    __smtx_model_eval M
        (__eo_to_smt (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) =
      __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) := by
  sorry

/--
From `(forall xs F)` true in `M` and well-typed instantiation terms `ts`, the
body `F` is true under the substitution model `pushSubstModel M xs ts`.

Proof sketch: `eo_interprets M (forall xs F) true` unfolds via
`__eo_to_smt (forall xs F) = not (exists xs (not (toSmt F)))` and the
`native_eval_texists` semantics to: for every assignment of canonical,
correctly-typed values to `xs`, `eval (push…) (toSmt F) = Boolean true`. The
values assigned by `pushSubstModel M xs ts` are canonical of the right types
because each `tᵢ` is a well-typed term (from `cmdTranslationOk` / the binder
types), so the universal instantiates to give the body true here. -/
theorem instantiate_body_true
    (M : SmtModel) (hM : model_total_typed M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) = SmtValue.Boolean true := by
  have hXsNonNil : xs ≠ Term.__eo_List_nil :=
    forall_binders_non_nil_of_has_smt_translation xs F hWf
  have hBodyBool : RuleProofs.eo_has_bool_type F :=
    forall_body_has_bool_type_of_has_smt_translation xs F hWf
  have hBodyTrans : RuleProofs.eo_has_smt_translation F :=
    forall_body_has_smt_translation_of_has_smt_translation xs F hWf
  rcases forall_binders_env_of_has_smt_translation xs F hWf with
    ⟨binderVars, hXsEnv⟩
  cases hPrem with
  | intro_true hForallTy hForallEval =>
      rw [eo_to_smt_forall_eq_of_non_nil xs F hXsNonNil] at hForallTy hForallEval
      have hInst :
          ForallInstantiationModel M xs (pushSubstModel M xs ts) := by
        sorry
      exact forall_instantiation_body_true hInst hM hBodyBool hForallEval

/--
A non-`Stuck` result of `__eo_prog_instantiate` forces the premise to be a
`forall` and pins the conclusion to the substituted body. -/
theorem prog_instantiate_shape
    (ts prem : Term)
    (hNe : __eo_prog_instantiate ts (Proof.pf prem) ≠ Term.Stuck) :
    ∃ xs F,
      prem = Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F ∧
      __eo_prog_instantiate ts (Proof.pf prem) =
        __substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil := by
  cases prem with
  | Apply f F =>
      cases f with
      | Apply g xs =>
          cases g with
          | UOp op =>
              cases op with
              | «forall» =>
                  refine ⟨xs, F, rfl, ?_⟩
                  cases ts <;> first | rfl | exact absurd rfl hNe
              | _ => cases ts <;> exact absurd rfl hNe
          | _ => cases ts <;> exact absurd rfl hNe
      | _ => cases ts <;> exact absurd rfl hNe
  | _ => cases ts <;> exact absurd rfl hNe

/--
Soundness core: if the premise `(forall xs F)` is true in `M`, the conclusion
`F[xs ↦ ts]` is true in `M`. Combines `instantiate_body_true` and
`substitute_simul_eval`, plus the `Bool`-typedness of the result to package as
`eo_interprets`. -/
theorem instantiate_sound
    (M : SmtModel) (hM : model_total_typed M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hResBool : RuleProofs.eo_has_bool_type
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) :
    eo_interprets M
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) true := by
  -- chain: subst-eval ▸ body-true, then repackage with hResBool
  have hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) =
        SmtValue.Boolean true := by
    rw [substitute_simul_eval M hM F xs ts]
    exact instantiate_body_true M hM xs F ts hPrem hWf
  have hTy :
      __smtx_typeof
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) =
        SmtType.Bool := hResBool
  exact smt_interprets.intro_true M _ hTy hEval

end InstantiateRule

/--
`instantiate` rule properties.

Boilerplate (arg/premise destructuring, `Stuck` discharge, translation
obligation) mirrors `BooleanElimSupport.cmd_step_and_elim_properties`; the
soundness obligation delegates to `InstantiateRule.instantiate_sound`.
-/
theorem cmd_step_instantiate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.instantiate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.instantiate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.instantiate args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.instantiate args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  -- The single premise term is `prem`; the program result is the substitution.
                  let prem : Term := __eo_state_proven_nth s n1
                  change __eo_prog_instantiate a1 (Proof.pf prem) ≠ Term.Stuck at hProg
                  -- Shape: prem is a `forall`, result is the substitution.
                  obtain ⟨xs, F, hPremShape, hResEq⟩ :=
                    InstantiateRule.prog_instantiate_shape a1 prem hProg
                  -- The premise (the forall) is Bool-typed, hence translatable.
                  have hPremBool : RuleProofs.eo_has_bool_type prem :=
                    hPremisesBool prem (by simp [prem, premiseTermList])
                  rw [hPremShape] at hPremBool
                  -- The premise (the forall) has an SMT translation.
                  have hWf :
                      RuleProofs.eo_has_smt_translation
                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) :=
                    RuleProofs.eo_has_smt_translation_of_has_bool_type _ hPremBool
                  -- The instantiate argument is a list of translatable actuals.
                  have hActualsTrans : EoListAllHaveSmtTranslation a1 := by
                    simpa [cmdTranslationOk, cArgListTranslationOkMask,
                      argTranslationOkMasked] using hCmdTrans
                  -- The program result has EO Bool type.
                  have hSubstTypeof :
                      __eo_typeof
                        (__substitute_simul_rec (Term.Boolean false) F xs a1
                          Term.__eo_List_nil) = Term.Bool := by
                    change __eo_typeof (__eo_prog_instantiate a1 (Proof.pf prem)) =
                      Term.Bool at hResultTy
                    rw [hResEq] at hResultTy
                    exact hResultTy
                  -- The result is SMT Bool-typed by substitution type preservation.
                  have hResBool :
                      RuleProofs.eo_has_bool_type
                        (__substitute_simul_rec (Term.Boolean false) F xs a1
                          Term.__eo_List_nil) :=
                    InstantiateRule.substitute_simul_has_bool_type_of_typeof_bool
                      F xs a1 hWf hActualsTrans hSubstTypeof
                  refine ⟨?_, ?_⟩
                  · -- facts_of_true
                    intro hEvid
                    have hPremTrue : eo_interprets M prem true :=
                      hEvid prem (by simp [prem, premiseTermList])
                    rw [hPremShape] at hPremTrue
                    change eo_interprets M (__eo_prog_instantiate a1 (Proof.pf prem)) true
                    rw [hResEq]
                    exact InstantiateRule.instantiate_sound M hM xs F a1
                      hPremTrue hWf hResBool
                  · -- has_smt_translation
                    change RuleProofs.eo_has_smt_translation
                      (__eo_prog_instantiate a1 (Proof.pf prem))
                    rw [hResEq]
                    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hResBool
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
