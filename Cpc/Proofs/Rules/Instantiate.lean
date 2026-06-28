import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Canonical
import Cpc.Proofs.Closed.ContainsAtomicTermListFree
import Cpc.Proofs.Closed.Substitute

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

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

3. **`instantiate_body_true`** (DONE) — from `forall xs F` true and the
   well-typedness of `ts`, the body is true under `pushSubstModel M xs ts`.
   The well-typedness of the actuals is exactly what the checker's
   `__is_instantiation xs ts = true` guard certifies: it requires
   `__eo_typeof tᵢ = Tᵢ` for each binder. `substActualsHaveSmtTypes_of_is_instantiation`
   reflects that guard into `SubstActualsHaveSmtTypes`, and the existing
   `instantiate_body_true_of_smt_typed_actuals` finishes the quantifier
   instantiation. `prog_instantiate_shape` exposes the guard from the checker.

4. **`prog_instantiate_shape`** (DONE) — a non-`Stuck` result forces the
   premise to be `forall xs F`, pins the conclusion to the substitution, AND
   exposes the `__is_instantiation xs ts = true` guard (the `__eo_requires`
   wrapper around `__substitute_simul_rec` collapses only when the guard holds).

Status (2026-06-27):
  * `prog_instantiate_shape`  — PROVEN (now also returns the `__is_instantiation`
    fact; previously this proof was broken because it ignored the guard wrapper).
  * `instantiate_body_true`   — PROVEN (via the `__is_instantiation` reflection).
  * `instantiate_sound`       — depends only on the `substitute_simul_eval` crux.
  * main theorem `hWf`        — PROVEN (premise is Bool-typed ⇒ translatable).
  * `substFalse_eval_gen_lt`  — general substitution-eval induction. PROVEN:
    variable / atom / `Stuck`; 9 unary heads (not, to_real, to_int, is_int, abs,
    uneg, int_pow2, int_log2, purify) via `substFalse_eval_unary_op`; 20 binary
    heads (and, or, imp, xor, eq, plus, neg, mult, lt, leq, gt, geq, div, mod,
    multmult, select, divisible, div_total, mod_total, multmult_total) via
    `substFalse_eval_binary_op` — div/mod/multmult use a `SubstFalseRel.globals`-
    aware congruence (their eval reads `native_div_by_zero_id` from the model).
    REMAINING: ternary (ite/store; needs the middle head's non-binder-shape from
    translatability), theory ops (strings/seq/set/bv/regex — same helper
    pattern), the generic application, and the binder/quantifier case. The quant
    case reduces, via `smt_model_eval_eo_to_smt_exists_eq_of_body_eval_eq`-style
    chain congruence (but a *different-body* variant: `toSmt (subst a)` vs
    `toSmt a`) threaded with `SubstituteSupport.substFalseRel_push` per binder
    (its `hNoCollide` discharged by `eo_to_smt_type_injective_of_field_wf_rec`),
    to the body IH. This is the reusable core of the crux.
  * `substitute_simul_eval`   — sorry (crux); reduces to `substFalse_eval_gen_lt`
    plus the `SubstFalseRel M (pushSubstModel …) xs ts nil` base relation.
  * `substitute_simul_has_smt_translation_of_typeof_ne_stuck_lt` — one `sorry`
    remains in the generic / non-special-head application case (line ~2955).
    This is a *type-preservation* obligation for `__substitute_simul_rec`: it
    must reprove EO→SMT translatability for every remaining operator head under
    substitution (`__eo_to_smt`, `Cpc/Spec.lean:204`, special-cases dozens of
    unary/binary/ternary heads). The induction now threads the
    `SubstActualsHaveSmtTypes` reflection of the `__is_instantiation` guard,
    which is required for the statement to be true (e.g. EO `abs` accepts arith,
    but SMT `abs` is `Int`-only). The remaining work is to exploit that guard for
    exact substitution type preservation in the special-head cases. No generic
    `__eo_typeof t = Bool → eo_has_smt_translation t` exists, so this remains its
    own large structural induction.

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

theorem model_agrees_on_env_of_agrees_except_empty
    {vars bound : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env [] bound M N) :
    model_agrees_on_env vars M N := by
  refine ⟨hAgree.globals, ?_⟩
  intro s T _hMem
  exact hAgree.vars_eq s T (Or.inr (by simp))

theorem model_agrees_on_env_of_agrees_everywhere
    {vars : List SmtVarKey} {M N : SmtModel}
    (hAgree : model_agrees_except_on_env [] [] M N) :
    model_agrees_on_env vars M N := by
  exact model_agrees_on_env_of_agrees_except_empty hAgree

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

theorem smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  induction hEnv generalizing body with
  | nil =>
      simpa [__eo_to_smt_exists] using hBodyTy
  | cons hTail ih =>
      rename_i s T env tailVars
      exact
        closed_smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
          s T env body
          (hWf s T (List.Mem.head _))
          (ih
            (by
              intro s' T' hMem
              exact hWf s' T' (List.Mem.tail _ hMem))
            hBodyTy)

theorem smtx_typeof_not_of_arg_bool (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  rw [__smtx_typeof.eq_def]
  change
    native_ite (native_Teq (__smtx_typeof t) SmtType.Bool)
      SmtType.Bool SmtType.None = SmtType.Bool
  rw [hTy]
  simp [native_Teq, native_ite]

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

theorem SubstActualsTyped.env
    {M : SmtModel} :
    ∀ {xs ts : Term},
      SubstActualsTyped M xs ts ->
        ∃ vars, EoVarEnv xs vars
  | _, _, SubstActualsTyped.nil ts =>
      ⟨[], EoVarEnv.nil⟩
  | _, _, SubstActualsTyped.cons _hWf _hValTy _hValCan hTail =>
      by
        rename_i s T env t ts
        rcases SubstActualsTyped.env hTail with ⟨vars, hEnv⟩
        exact ⟨(s, T) :: vars, EoVarEnv.cons hEnv⟩

/-- Syntactic actual-list typing against a binder list. -/
inductive SubstActualsHaveSmtTypes : Term -> Term -> Prop where
  | nil (ts : Term) :
      SubstActualsHaveSmtTypes Term.__eo_List_nil ts
  | cons {s : native_String} {T env t ts : Term} :
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      RuleProofs.eo_has_smt_translation t ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type T ->
      SubstActualsHaveSmtTypes env ts ->
      SubstActualsHaveSmtTypes
        (Term.Apply (Term.Apply Term.__eo_List_cons
          (Term.Var (Term.String s) T)) env)
        (Term.Apply (Term.Apply Term.__eo_List_cons t) ts)

theorem SubstActualsHaveSmtTypes.env :
    ∀ {xs ts : Term},
      SubstActualsHaveSmtTypes xs ts ->
        ∃ vars, EoVarEnv xs vars
  | _, _, SubstActualsHaveSmtTypes.nil ts =>
      ⟨[], EoVarEnv.nil⟩
  | _, _, SubstActualsHaveSmtTypes.cons _hWf _hTrans _hTy hTail =>
      by
        rename_i s T env t ts
        rcases SubstActualsHaveSmtTypes.env hTail with ⟨vars, hEnv⟩
        exact ⟨(s, T) :: vars, EoVarEnv.cons hEnv⟩

theorem SubstActualsHaveSmtTypes.to_typed
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ {xs ts : Term},
      SubstActualsHaveSmtTypes xs ts ->
        SubstActualsTyped M xs ts
  | _, _, SubstActualsHaveSmtTypes.nil ts =>
      SubstActualsTyped.nil ts
  | _, _, SubstActualsHaveSmtTypes.cons hWf hTrans hTy hTail =>
      by
        rename_i s T env t ts
        rcases eo_to_smt_eval_typed_canonical M hM t hTrans with
          ⟨hEvalTy, hEvalCan⟩
        exact SubstActualsTyped.cons hWf
          (by simpa [hTy] using hEvalTy)
          (by simpa [__smtx_value_canonical] using hEvalCan)
          (SubstActualsHaveSmtTypes.to_typed M hM hTail)

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

theorem pushSubstModel_total_typed_of_smt_typed_actuals
    (M : SmtModel) (hM : model_total_typed M)
    {xs ts : Term}
    (hActuals : SubstActualsHaveSmtTypes xs ts) :
    model_total_typed (pushSubstModel M xs ts) :=
  pushSubstModel_total_typed_of_actuals M hM
    (SubstActualsHaveSmtTypes.to_typed M hM hActuals)

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
Bridge from pure universal instantiation to the substitution model.

The two remaining facts needed by the full instantiate proof are kept explicit:
`pushSubstModel` must be total-typed, and the translated body must be closed in
some finite SMT-variable environment. The assignment model then agrees with the
substitution model everywhere, so closed-term evaluation coincidence transfers
the truth of the body.
-/
theorem instantiate_body_true_of_push_total_and_closedIn
    (M : SmtModel) (hM : model_total_typed M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hPushTotal : model_total_typed (pushSubstModel M xs ts))
    (hBodyClosed :
      ∃ bodyVars : List SmtVarKey,
        SmtTermClosedIn bodyVars (__eo_to_smt F)) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) =
      SmtValue.Boolean true := by
  have hXsNonNil : xs ≠ Term.__eo_List_nil :=
    forall_binders_non_nil_of_has_smt_translation xs F hWf
  have hBodyBool : RuleProofs.eo_has_bool_type F :=
    forall_body_has_bool_type_of_has_smt_translation xs F hWf
  rcases forall_binders_env_of_has_smt_translation xs F hWf with
    ⟨binderVars, hXsEnv⟩
  cases hPrem with
  | intro_true hForallTy hForallEval =>
      rw [eo_to_smt_forall_eq_of_non_nil xs F hXsNonNil] at hForallTy hForallEval
      let Source := pushSubstModel M xs ts
      have hBinderWf :
          ∀ s T, (s, T) ∈ binderVars ->
            __smtx_type_wf (__eo_to_smt_type T) = true :=
        forall_binder_types_wf_of_has_smt_translation hWf hXsEnv
      have hAssignTrue :
          __smtx_model_eval (forallAssignmentModel Source M xs)
              (__eo_to_smt F) =
            SmtValue.Boolean true :=
        forall_assignment_body_true
          (M := M) (Source := Source) (xs := xs) (vars := binderVars)
          (body := __eo_to_smt F)
          hXsEnv
          (by simpa [Source] using hPushTotal)
          hM hBinderWf hBodyBool hForallEval
      have hBase :
          model_agrees_except_on_env (binderVars.map EoVarKey.toSmt) []
            M Source :=
        model_agrees_except_on_env_symm
          (by
            simpa [Source] using
              pushSubstModel_agrees_except M ts hXsEnv)
      have hAgreeAll :
          model_agrees_except_on_env [] []
            (forallAssignmentModel Source M xs) Source :=
        forallAssignmentModel_agrees_source Source M hXsEnv hBase
      rcases hBodyClosed with ⟨bodyVars, hClosed⟩
      have hEvalEq :
          __smtx_model_eval (forallAssignmentModel Source M xs)
              (__eo_to_smt F) =
            __smtx_model_eval Source (__eo_to_smt F) :=
        smt_model_eval_eq_of_closedIn (__eo_to_smt F) bodyVars
          (forallAssignmentModel Source M xs) Source hClosed
          (model_agrees_on_env_of_agrees_everywhere hAgreeAll)
      simpa [Source, ← hEvalEq] using hAssignTrue

/-- Variant of `instantiate_body_true_of_push_total_and_closedIn` using the
finite support of SMT terms as the closedness environment. -/
theorem instantiate_body_true_of_push_total
    (M : SmtModel) (hM : model_total_typed M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hPushTotal : model_total_typed (pushSubstModel M xs ts)) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) =
      SmtValue.Boolean true := by
  exact instantiate_body_true_of_push_total_and_closedIn M hM xs F ts
    hPrem hWf hPushTotal (SmtTermClosedIn.exists_env (__eo_to_smt F))

/-- Bridge specialised to actual terms that already evaluate to canonical values
of the corresponding binder SMT types in the ambient model. -/
theorem instantiate_body_true_of_actuals
    (M : SmtModel) (hM : model_total_typed M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hActuals : SubstActualsTyped M xs ts) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) =
      SmtValue.Boolean true := by
  exact instantiate_body_true_of_push_total M hM xs F ts
    hPrem hWf (pushSubstModel_total_typed_of_actuals M hM hActuals)

/-- Same bridge, with syntactic SMT typing of actual terms converted through
evaluation type preservation in the ambient model. -/
theorem instantiate_body_true_of_smt_typed_actuals
    (M : SmtModel) (hM : model_total_typed M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hActuals : SubstActualsHaveSmtTypes xs ts) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) =
      SmtValue.Boolean true := by
  exact instantiate_body_true_of_push_total M hM xs F ts hPrem hWf
    (pushSubstModel_total_typed_of_smt_typed_actuals M hM hActuals)

/-- EO closedness of a body under its binder list gives the SMT closedness
environment needed by the model-coincidence theorem. -/
theorem smt_body_closedIn_of_eo_closed_under_binders
    {xs F : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hClosed : __eo_is_closed_rec F xs = Term.Boolean true) :
    SmtTermClosedIn (vars.map EoVarKey.toSmt) (__eo_to_smt F) := by
  exact smtTermClosedIn_of_eo_is_closed_rec_perm
    (hEnv := EoSmtVarEnvPerm.of_exact (EoVarEnv.to_smt hEnv))
    hClosed

/--
Bridge specialised to the natural instantiate side conditions: the actual terms
produce well-typed canonical binder values, and the body is EO-closed under the
binder list.
-/
theorem instantiate_body_true_of_actuals_and_eo_closed
    (M : SmtModel) (hM : model_total_typed M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hActuals : SubstActualsTyped M xs ts)
    (hBodyClosed : __eo_is_closed_rec F xs = Term.Boolean true) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) =
      SmtValue.Boolean true := by
  rcases forall_binders_env_of_has_smt_translation xs F hWf with
    ⟨binderVars, hXsEnv⟩
  exact instantiate_body_true_of_push_total_and_closedIn M hM xs F ts
    hPrem hWf
    (pushSubstModel_total_typed_of_actuals M hM hActuals)
    ⟨binderVars.map EoVarKey.toSmt,
      smt_body_closedIn_of_eo_closed_under_binders hXsEnv hBodyClosed⟩

/-- Same bridge, with syntactic actual typing converted through SMT evaluation
type preservation in the ambient model. -/
theorem instantiate_body_true_of_smt_typed_actuals_and_eo_closed
    (M : SmtModel) (hM : model_total_typed M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hBodyClosed : __eo_is_closed_rec F xs = Term.Boolean true) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) =
      SmtValue.Boolean true := by
  rcases forall_binders_env_of_has_smt_translation xs F hWf with
    ⟨binderVars, hXsEnv⟩
  exact instantiate_body_true_of_push_total_and_closedIn M hM xs F ts
    hPrem hWf
    (pushSubstModel_total_typed_of_smt_typed_actuals M hM hActuals)
    ⟨binderVars.map EoVarKey.toSmt,
      smt_body_closedIn_of_eo_closed_under_binders hXsEnv hBodyClosed⟩

/-- A translated EO term list is never `Stuck`. -/
theorem eoListAllHaveSmtTranslation_ne_stuck {ts : Term}
    (hTs : EoListAllHaveSmtTranslation ts) : ts ≠ Term.Stuck := by
  intro h
  subst ts
  cases hTs

theorem substitute_simul_rec_uop_eq_self
    (op : UserOp) (xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts) :
    __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ts bvs =
      Term.UOp op := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ts bvs =
        __eo_requires
          (__is_closed_rec (Term.UOp op) Term.__eo_List_nil)
          (Term.Boolean true) (Term.UOp op) :=
    SubstituteSupport.substitute_simul_rec_atom
      (Term.Boolean false) (Term.UOp op) xs ts bvs
      hisr hxs hts hbvs
      (by intro f a h; cases h)
      (by intro s S h; cases h)
      (by intro h; cases h)
  rw [hHeadEq]
  simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]

set_option linter.unusedSimpArgs false in
theorem eo_typeof_to_real_arg_arith_of_ne_stuck {A : Term}
    (h : __eo_typeof_to_real A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int ∨ A = Term.UOp UserOp.Real := by
  cases A <;>
    simp [__eo_typeof_to_real, __is_arith_type, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;>
      simp [__eo_typeof_to_real, __is_arith_type, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_to_int_arg_real_of_ne_stuck {A : Term}
    (h : __eo_typeof_to_int A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Real := by
  cases A <;> simp [__eo_typeof_to_int] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_to_int] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_is_int_arg_real_of_ne_stuck {A : Term}
    (h : __eo_typeof_is_int A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Real := by
  cases A <;> simp [__eo_typeof_is_int] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_is_int] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_abs_arg_arith_of_ne_stuck {A : Term}
    (h : __eo_typeof_abs A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int ∨ A = Term.UOp UserOp.Real := by
  cases A <;>
    simp [__eo_typeof_abs, __is_arith_type, __eo_requires,
      native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢
  case UOp op =>
    cases op <;>
      simp [__eo_typeof_abs, __is_arith_type, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_int_pow2_arg_int_of_ne_stuck {A : Term}
    (h : __eo_typeof_int_pow2 A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int := by
  cases A <;> simp [__eo_typeof_int_pow2] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_int_pow2] at h ⊢

set_option linter.unusedSimpArgs false in
theorem eo_typeof_int_ispow2_arg_int_of_ne_stuck {A : Term}
    (h : __eo_typeof_int_ispow2 A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int := by
  cases A <;> simp [__eo_typeof_int_ispow2] at h ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_int_ispow2] at h ⊢

theorem eo_typeof_at_div_by_zero_arg_real_of_ne_stuck {A : Term}
    (h : __eo_typeof__at_div_by_zero A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Real := by
  cases A <;> simp [__eo_typeof__at_div_by_zero] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem eo_typeof_purify_eq (A : Term) :
    __eo_typeof__at_purify A = A := by
  cases A <;> rfl

theorem eo_typeof_bvnot_arg_bitvec_of_ne_stuck {A : Term}
    (h : __eo_typeof_bvnot A ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A <;> simp [__eo_typeof_bvnot] at h ⊢
  case Apply f w =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem eo_typeof_bvnego_arg_bitvec_of_ne_stuck {A : Term}
    (h : __eo_typeof_bvnego A ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A <;> simp [__eo_typeof_bvnego] at h ⊢
  case Apply f w =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem smt_typeof_bvnot_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnot t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_38]

theorem smt_typeof_bvneg_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvneg t) =
      __smtx_typeof_bv_op_1 (__smtx_typeof t) := by
  rw [__smtx_typeof.eq_46]

theorem smt_typeof_bvnego_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.bvnego t) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Bool := by
  rw [__smtx_typeof.eq_71]

theorem smt_typeof_ubv_to_int_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.ubv_to_int t) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smt_typeof_sbv_to_int_eq (t : SmtTerm) :
    __smtx_typeof (SmtTerm.sbv_to_int t) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
    {X w : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.Apply (Term.UOp UserOp.BitVec) w) :
    ∃ n : native_Nat, __smtx_typeof (__eo_to_smt X) = SmtType.BitVec n := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hXNonNone :
      __smtx_typeof (__eo_to_smt X) ≠ SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hXTrans
  rw [hXTy] at hXMatch
  cases w <;> simp [__eo_to_smt_type] at hXMatch hXNonNone
  case Numeral n =>
    by_cases hn : native_zleq 0 n = true
    · refine ⟨native_int_to_nat n, ?_⟩
      rw [hXMatch]
      simp [hn, native_ite]
    · rw [hXMatch] at hXNonNone
      simp [hn, native_ite] at hXNonNone
  all_goals
    exact False.elim (hXNonNone hXMatch)

theorem eo_typeof_str_len_arg_seq_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_len A ≠ Term.Stuck) :
    ∃ V, A = Term.Apply (Term.UOp UserOp.Seq) V := by
  cases A <;> simp [__eo_typeof_str_len] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem eo_typeof_str_rev_arg_seq_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_rev A ≠ Term.Stuck) :
    ∃ V, A = Term.Apply (Term.UOp UserOp.Seq) V := by
  cases A <;> simp [__eo_typeof_str_rev] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_to_lower A ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases A <;> simp [__eo_typeof_str_to_lower] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      cases V <;> simp at h ⊢
      case UOp vop =>
        cases vop <;> simp at h ⊢

theorem eo_typeof_str_to_code_arg_seq_char_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_to_code A ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases A <;> simp [__eo_typeof_str_to_code] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      cases V <;> simp at h ⊢
      case UOp vop =>
        cases vop <;> simp at h ⊢

theorem eo_typeof_str_from_code_arg_int_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_from_code A ≠ Term.Stuck) :
    A = Term.UOp UserOp.Int := by
  cases A <;> simp [__eo_typeof_str_from_code] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem eo_typeof_str_is_digit_arg_seq_char_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_is_digit A ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases A <;> simp [__eo_typeof_str_is_digit] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      cases V <;> simp at h ⊢
      case UOp vop =>
        cases vop <;> simp at h ⊢

theorem eo_typeof_str_to_re_arg_seq_char_of_ne_stuck {A : Term}
    (h : __eo_typeof_str_to_re A ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases A <;> simp [__eo_typeof_str_to_re] at h ⊢
  case Apply f V =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢
      cases V <;> simp at h ⊢
      case UOp vop =>
        cases vop <;> simp at h ⊢

theorem eo_typeof_re_mult_arg_reglan_of_ne_stuck {A : Term}
    (h : __eo_typeof_re_mult A ≠ Term.Stuck) :
    A = Term.UOp UserOp.RegLan := by
  cases A <;> simp [__eo_typeof_re_mult] at h ⊢
  case UOp op =>
    cases op <;> simp at h ⊢

theorem eo_typeof_bvsize_arg_bitvec_of_ne_stuck {A : Term}
    (h : __eo_typeof__at_bvsize A ≠ Term.Stuck) :
    ∃ w, A = Term.Apply (Term.UOp UserOp.BitVec) w := by
  cases A <;> simp [__eo_typeof__at_bvsize] at h ⊢
  case Apply f w =>
    cases f <;> simp at h ⊢
    case UOp op =>
      cases op <;> simp at h ⊢

theorem smt_typeof_eo_to_smt_seq_of_typeof_seq
    {X V : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.Apply (Term.UOp UserOp.Seq) V) :
    ∃ T : SmtType, __smtx_typeof (__eo_to_smt X) = SmtType.Seq T := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hXNonNone :
      __smtx_typeof (__eo_to_smt X) ≠ SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hXTrans
  rw [hXTy] at hXMatch
  cases hV : __eo_to_smt_type V <;>
    simp [__eo_to_smt_type, __smtx_typeof_guard, hV] at hXMatch hXNonNone
  case None =>
    exact False.elim (hXNonNone hXMatch)
  all_goals
    exact ⟨_, hXMatch⟩

theorem smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
    {X : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy :
      __eo_typeof X =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __smtx_typeof (__eo_to_smt X) = SmtType.Seq SmtType.Char := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  rw [hXMatch, hXTy]
  rfl

theorem smt_typeof_eo_to_smt_reglan_of_typeof_reglan
    {X : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.UOp UserOp.RegLan) :
    __smtx_typeof (__eo_to_smt X) = SmtType.RegLan := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  rw [hXMatch, hXTy]
  rfl

theorem smt_typeof_eo_to_smt_int_of_typeof_int
    {X : Term}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hXTy : __eo_typeof X = Term.UOp UserOp.Int) :
    __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
  have hXMatch :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (__eo_typeof X) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  rw [hXMatch, hXTy]
  rfl

theorem instantiate_smt_term_ne_dt_sel_of_non_none_type
    {F : SmtTerm}
    (hF : __smtx_typeof F ≠ SmtType.None) :
    ∀ s d i j, F ≠ SmtTerm.DtSel s d i j := by
  intro s d i j h
  subst h
  exact hF (by simp)

theorem instantiate_smt_term_ne_dt_tester_of_non_none_type
    {F : SmtTerm}
    (hF : __smtx_typeof F ≠ SmtType.None) :
    ∀ s d i, F ≠ SmtTerm.DtTester s d i := by
  intro s d i h
  subst h
  exact hF (by simp)

theorem instantiate_generic_apply_type_of_has_smt_translation
    (f x : Term)
    (hF : RuleProofs.eo_has_smt_translation f) :
    generic_apply_type (__eo_to_smt f) (__eo_to_smt x) :=
  generic_apply_type_of_non_datatype_head
    (instantiate_smt_term_ne_dt_sel_of_non_none_type hF)
    (instantiate_smt_term_ne_dt_tester_of_non_none_type hF)

theorem instantiate_eo_typeof_apply_arg_stuck (F : Term) :
    __eo_typeof_apply F Term.Stuck = Term.Stuck := by
  cases F <;> rfl

theorem instantiate_eo_typeof_apply_head_ne_stuck {F X : Term} :
    __eo_typeof_apply F X ≠ Term.Stuck ->
    F ≠ Term.Stuck := by
  intro h hF
  subst F
  cases X <;> simp [__eo_typeof_apply] at h

theorem instantiate_eo_typeof_apply_arg_ne_stuck {F X : Term} :
    __eo_typeof_apply F X ≠ Term.Stuck ->
    X ≠ Term.Stuck := by
  intro h hX
  subst X
  exact h (instantiate_eo_typeof_apply_arg_stuck F)

theorem instantiate_eo_typeof_apply_dtc_eq_of_arg_ne_stuck
    (T U X : Term)
    (hX : X ≠ Term.Stuck) :
    __eo_typeof_apply (Term.DtcAppType T U) X =
      __eo_requires T X U := by
  cases X <;> simp [__eo_typeof_apply] at hX ⊢

theorem instantiate_eo_typeof_apply_fun_eq_of_arg_ne_stuck
    (T U X : Term)
    (hX : X ≠ Term.Stuck) :
    __eo_typeof_apply (Term.Apply (Term.Apply Term.FunType T) U) X =
      __eo_requires T X U := by
  cases X <;> simp [__eo_typeof_apply] at hX ⊢

theorem instantiate_eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

theorem instantiate_eo_requires_result_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [hxy, hx, native_ite, SmtEval.native_not] at h
    · simp [hxy, hx, native_ite, SmtEval.native_not]
  · simp [hxy, native_ite] at h

theorem instantiate_smtx_typeof_apply_non_none_of_eo_typeof_apply_non_stuck
    (F X : Term)
    (hFValid : TranslationProofs.eo_type_valid F)
    (hApp : __eo_typeof_apply F X ≠ Term.Stuck) :
    __smtx_typeof_apply (__eo_to_smt_type F) (__eo_to_smt_type X) ≠
      SmtType.None := by
  cases F with
  | DtcAppType T U =>
      have hXNN : X ≠ Term.Stuck := by
        intro hX
        subst X
        exact hApp (instantiate_eo_typeof_apply_arg_stuck _)
      rw [instantiate_eo_typeof_apply_dtc_eq_of_arg_ne_stuck T U X hXNN] at hApp
      have hAppReq : __eo_requires T X U ≠ Term.Stuck := hApp
      have hX : T = X := instantiate_eo_requires_arg_eq_of_ne_stuck hAppReq
      subst X
      have hValid : TranslationProofs.eo_type_valid_rec [] (Term.DtcAppType T U) := by
        simpa [TranslationProofs.eo_type_valid] using hFValid
      rcases (by simpa [TranslationProofs.eo_type_valid_rec] using hValid :
        TranslationProofs.eo_type_valid_rec [] T ∧
          TranslationProofs.eo_type_valid_rec [] U) with ⟨hT, hU⟩
      have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
        TranslationProofs.eo_type_valid_rec_non_none hT
      have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
        TranslationProofs.eo_type_valid_rec_non_none hU
      simp [__eo_to_smt_type, __smtx_typeof_apply, __smtx_typeof_guard,
        native_ite, native_Teq, hTNN, hUNN]
  | Apply f U =>
      cases f with
      | Apply f' T =>
          cases f' with
          | FunType =>
              have hXNN : X ≠ Term.Stuck := by
                intro hX
                subst X
                exact hApp (instantiate_eo_typeof_apply_arg_stuck _)
              rw [instantiate_eo_typeof_apply_fun_eq_of_arg_ne_stuck T U X hXNN] at hApp
              have hAppReq : __eo_requires T X U ≠ Term.Stuck := hApp
              have hX : T = X := instantiate_eo_requires_arg_eq_of_ne_stuck hAppReq
              subst X
              have hValid :
                  TranslationProofs.eo_type_valid_rec []
                    (Term.Apply (Term.Apply Term.FunType T) U) := by
                simpa [TranslationProofs.eo_type_valid] using hFValid
              rcases (by
                  simpa [TranslationProofs.eo_type_valid_rec] using hValid :
                    TranslationProofs.eo_type_valid_rec [] T ∧
                      TranslationProofs.eo_type_valid_rec [] U) with
                ⟨hT, hU⟩
              have hTNN : __eo_to_smt_type T ≠ SmtType.None :=
                TranslationProofs.eo_type_valid_rec_non_none hT
              have hUNN : __eo_to_smt_type U ≠ SmtType.None :=
                TranslationProofs.eo_type_valid_rec_non_none hU
              simp [TranslationProofs.eo_to_smt_type_fun,
                __smtx_typeof_apply, __smtx_typeof_guard, native_ite,
                native_Teq, hTNN, hUNN]
          | _ =>
              exact False.elim (hApp (by cases X <;> simp [__eo_typeof_apply]))
      | _ =>
          exact False.elim (hApp (by cases X <;> simp [__eo_typeof_apply]))
  | _ =>
      exact False.elim (hApp (by cases X <;> simp [__eo_typeof_apply]))

theorem instantiate_eo_to_smt_apply_generic_of_has_smt_translation
    (f x : Term)
    (hTransF : RuleProofs.eo_has_smt_translation f) :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x) := by
  unfold RuleProofs.eo_has_smt_translation at hTransF
  cases f <;> try rfl
  case UOp op =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp1 op i =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp2 op i j =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply,
          TranslationProofs.smtx_typeof_none]
    case UOp1 op i =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply,
          TranslationProofs.smtx_typeof_none]
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exfalso
          apply hTransF
          change
            __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt b))
                (__eo_to_smt a)) = SmtType.None
          simp [__smtx_typeof, __smtx_typeof_apply,
            TranslationProofs.smtx_typeof_none]

theorem instantiate_eo_typeof_apply_eq_of_has_smt_translation
    (f x : Term)
    (hTransF : RuleProofs.eo_has_smt_translation f) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  cases f <;> try rfl
  case __eo_List_cons =>
    exfalso
    apply hTransF
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case UOp op =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp1 op i =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp2 op i j =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply,
          TranslationProofs.smtx_typeof_none]
    case UOp1 op i =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply,
          TranslationProofs.smtx_typeof_none]
    case FunType =>
      exfalso
      apply hTransF
      change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
        SmtType.None
      simp [__smtx_typeof, __smtx_typeof_apply,
        TranslationProofs.smtx_typeof_none]
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exfalso
          apply hTransF
          change
            __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt b))
                (__eo_to_smt a)) = SmtType.None
          simp [__smtx_typeof, __smtx_typeof_apply,
            TranslationProofs.smtx_typeof_none]

theorem eo_has_smt_translation_apply_of_head_arg_translation_and_type
    (f x : Term)
    (hF : RuleProofs.eo_has_smt_translation f)
    (hX : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof (Term.Apply f x) ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation (Term.Apply f x) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [instantiate_eo_to_smt_apply_generic_of_has_smt_translation f x hF]
  have hGeneric : generic_apply_type (__eo_to_smt f) (__eo_to_smt x) :=
    instantiate_generic_apply_type_of_has_smt_translation f x hF
  unfold generic_apply_type at hGeneric
  rw [hGeneric]
  have hFMatch :
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation f hF
  have hXMatch :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hX
  rw [hFMatch, hXMatch]
  have hEoApply :
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) ≠ Term.Stuck := by
    have hEq := instantiate_eo_typeof_apply_eq_of_has_smt_translation f x hF
    rwa [← hEq]
  have hFValid :
      TranslationProofs.eo_type_valid (__eo_typeof f) :=
    TranslationProofs.eo_type_valid_typeof_of_smt_translation f hF
  exact instantiate_smtx_typeof_apply_non_none_of_eo_typeof_apply_non_stuck
    (__eo_typeof f) (__eo_typeof x) hFValid hEoApply

theorem eo_has_smt_translation_mk_apply_of_head_arg_translation_and_type
    (f x : Term)
    (hF : RuleProofs.eo_has_smt_translation f)
    (hX : RuleProofs.eo_has_smt_translation x)
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation (__eo_mk_apply f x) := by
  have hfNe : f ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation f hF
  have hxNe : x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation x hX
  have hMk : __eo_mk_apply f x = Term.Apply f x := by
    cases f <;> cases x <;> simp [__eo_mk_apply] at hfNe hxNe ⊢
  rw [hMk] at hTy ⊢
  exact eo_has_smt_translation_apply_of_head_arg_translation_and_type
    f x hF hX hTy

theorem instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
      f ≠ Term.Stuck := by
  intro h hf
  subst f
  cases x <;> simp [__eo_mk_apply] at h

theorem instantiate_eo_mk_apply_arg_ne_stuck_of_ne_stuck {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
      x ≠ Term.Stuck := by
  intro h hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

theorem instantiate_eo_mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  have hf := instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck h
  have hx := instantiate_eo_mk_apply_arg_ne_stuck_of_ne_stuck h
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck {f x : Term}
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    __eo_mk_apply f x ≠ Term.Stuck := by
  intro hStuck
  apply hTy
  rw [hStuck]
  rfl

theorem instantiate_eo_mk_apply_eq_apply_of_typeof_ne_stuck (f x : Term)
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x :=
  instantiate_eo_mk_apply_eq_apply_of_ne_stuck f x
    (instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTy)

theorem eo_typeof_eo_var_env_eq_list
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars) :
    __eo_typeof xs = Term.__eo_List := by
  induction hEnv with
  | nil => rfl
  | cons hTail ih =>
      exact TranslationProofs.eo_typeof_list_cons_var _ _ _ ih

theorem eo_typeof_forall_body_bool_of_ne_stuck {T U : Term}
    (hT : T = Term.__eo_List)
    (hTy : __eo_typeof_forall T U ≠ Term.Stuck) :
    U = Term.Bool := by
  subst T
  cases U <;> try rfl
  all_goals
    exfalso
    apply hTy
    simp [__eo_typeof_forall]

theorem eo_typeof_body_bool_of_quant_type_ne_stuck
    {q xs body : Term} {vars : List EoVarKey}
    (hQ : q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists)
    (hEnv : EoVarEnv xs vars)
    (hTy :
      __eo_typeof (Term.Apply (Term.Apply q xs) body) ≠ Term.Stuck) :
    __eo_typeof body = Term.Bool := by
  rcases hQ with rfl | rfl
  · change
      __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) ≠
        Term.Stuck at hTy
    exact eo_typeof_forall_body_bool_of_ne_stuck
      (eo_typeof_eo_var_env_eq_list hEnv) hTy
  · change
      __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) ≠
        Term.Stuck at hTy
    exact eo_typeof_forall_body_bool_of_ne_stuck
      (eo_typeof_eo_var_env_eq_list hEnv) hTy

theorem eo_has_smt_translation_quant_of_body_translation_and_type
    (q xs body : Term)
    {vars : List EoVarKey}
    (hQ : q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists)
    (hEnv : EoVarEnv xs vars)
    (hNonNil : xs ≠ Term.__eo_List_nil)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTrans : RuleProofs.eo_has_smt_translation body)
    (hTy : __eo_typeof (Term.Apply (Term.Apply q xs) body) ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply q xs) body) := by
  have hBodyEoBool : __eo_typeof body = Term.Bool :=
    eo_typeof_body_bool_of_quant_type_ne_stuck hQ hEnv hTy
  have hBodySmtBool : __smtx_typeof (__eo_to_smt body) = SmtType.Bool := by
    have hMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation body hBodyTrans
    rw [hMatch, hBodyEoBool]
    rfl
  rcases hQ with rfl | rfl
  · cases hEnv with
    | nil =>
        exact False.elim (hNonNil rfl)
    | cons hTail =>
      rename_i s T env tailVars
      unfold RuleProofs.eo_has_smt_translation
      change
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (SmtTerm.not (__eo_to_smt body)))) ≠
          SmtType.None
      have hNotBodyBool :
          __smtx_typeof (SmtTerm.not (__eo_to_smt body)) = SmtType.Bool :=
        smtx_typeof_not_of_arg_bool (__eo_to_smt body) hBodySmtBool
      have hExistsBool :
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (SmtTerm.not (__eo_to_smt body))) =
            SmtType.Bool :=
        smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
          (EoVarEnv.cons (s := s) (T := T) hTail)
          hWf hNotBodyBool
      have hForallBool :
          __smtx_typeof
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt body)))) =
            SmtType.Bool :=
        smtx_typeof_not_of_arg_bool
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (SmtTerm.not (__eo_to_smt body))) hExistsBool
      intro hNone
      rw [hForallBool] at hNone
      cases hNone
  · cases hEnv with
    | nil =>
        exact False.elim (hNonNil rfl)
    | cons hTail =>
      rename_i s T env tailVars
      unfold RuleProofs.eo_has_smt_translation
      change
        __smtx_typeof
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) env)
              (__eo_to_smt body)) ≠
          SmtType.None
      have hExistsBool :
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (__eo_to_smt body)) =
            SmtType.Bool :=
        smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
          (EoVarEnv.cons (s := s) (T := T) hTail)
          hWf hBodySmtBool
      intro hNone
      rw [hExistsBool] at hNone
      cases hNone

theorem quant_binder_types_wf_of_has_smt_translation
    {Q xs F : Term} {vars : List EoVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply Q xs) F))
    (hEnv : EoVarEnv xs vars) :
    ∀ s T, (s, T) ∈ vars ->
      __smtx_type_wf (__eo_to_smt_type T) = true := by
  rcases hQ with hForall | hExists
  · subst Q
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
              simpa [RuleProofs.eo_has_smt_translation] using hTrans)
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
              (SmtTerm.not (__eo_to_smt F))) hNotTy
        exact
          smtx_type_wf_of_eo_var_env_exists_bool
            (EoVarEnv.cons (s := s) (T := T) hTail) hExistsTy
  · subst Q
    cases hEnv with
    | nil =>
        intro s T hMem
        cases hMem
    | cons hTail =>
        rename_i s T env tailVars
        have hExistsTy :
            __smtx_typeof
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (__eo_to_smt F)) =
              SmtType.Bool :=
          smtx_typeof_eo_to_smt_exists_cons_eq_bool_of_non_none
            (Term.Var (Term.String s) T) env (__eo_to_smt F)
            (by
              change
                __smtx_typeof
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T)) env)
                      (__eo_to_smt F)) ≠
                  SmtType.None
              simpa [RuleProofs.eo_has_smt_translation] using hTrans)
        exact
          smtx_type_wf_of_eo_var_env_exists_bool
            (EoVarEnv.cons (s := s) (T := T) hTail) hExistsTy

/-- Non-binder application case for substitution-result translatability. The
recursive calls provide translatability for the substituted head and argument;
the non-`Stuck` result type then reconstructs translatability of the rebuilt
application. -/
theorem substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
    (f a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) f xs ts bvs))
    (hASubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) a xs ts bvs))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply f a) xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Apply f a) xs ts bvs) := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply f a) xs ts bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean false) f xs ts bvs)
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) :=
    SubstituteSupport.substitute_simul_rec_apply
      (Term.Boolean false) f a xs ts bvs
      hisr hxs hts hbvs hNotBinder
  rw [hSubstEq] at hTy ⊢
  exact
    eo_has_smt_translation_mk_apply_of_head_arg_translation_and_type
      (__substitute_simul_rec (Term.Boolean false) f xs ts bvs)
      (__substitute_simul_rec (Term.Boolean false) a xs ts bvs)
      hFSubTrans hASubTrans hTy

/-- Boolean-typed variant of the non-binder application substitution case. -/
theorem substitute_simul_apply_has_smt_translation_of_typeof_bool
    (f a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) f xs ts bvs))
    (hASubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) a xs ts bvs))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply f a) xs ts bvs) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Apply f a) xs ts bvs) := by
  exact
    substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
      f a xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFSubTrans hASubTrans
      (by
        intro hStuck
        rw [hStuck] at hTy
        cases hTy)

/-- Common substitution-result translatability proof for unary special heads.

The bare operator head is not necessarily an SMT-translatable term, so the
generic application lemma cannot be used directly. This helper performs the
shared substitution/mk-apply reconstruction and leaves only the operator's
argument translatability and rebuilt application translatability to the caller.
-/
theorem substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
    (op : UserOp) (a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.UOp op ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp op) a))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ts bvs) ≠
        Term.Stuck)
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) a) ->
        eoHasSmtTranslation a)
    (hArgTyNe :
      ∀ X,
        __eo_typeof (Term.Apply (Term.UOp op) X) ≠ Term.Stuck ->
          __eo_typeof X ≠ Term.Stuck)
    (hBuild :
      ∀ X,
        RuleProofs.eo_has_smt_translation X ->
          __eo_typeof (Term.Apply (Term.UOp op) X) ≠ Term.Stuck ->
            RuleProofs.eo_has_smt_translation
              (Term.Apply (Term.UOp op) X))
    (hRecArg :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
          Term.Stuck ->
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs)) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.UOp op) a) xs ts bvs) := by
  let aSub := __substitute_simul_rec (Term.Boolean false) a xs ts bvs
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.UOp op) xs ts bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ts bvs hXsEnv hBvsEnv hTs
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ts bvs =
        __eo_mk_apply (Term.UOp op) aSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.UOp op) a xs ts bvs
        hisr hxs hts hbvs hNotBinder
    simpa [aSub, hHeadSub] using hApplyEq
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.UOp op) aSub) ≠ Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hMk :
      __eo_mk_apply (Term.UOp op) aSub =
        Term.Apply (Term.UOp op) aSub :=
    instantiate_eo_mk_apply_eq_apply_of_typeof_ne_stuck
      (Term.UOp op) aSub hTyMk
  have hTyApply :
      __eo_typeof (Term.Apply (Term.UOp op) aSub) ≠ Term.Stuck := by
    rwa [hMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  have hATrans :
      RuleProofs.eo_has_smt_translation a := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hArgExtract hFTransEo
  have hASubTrans :
      RuleProofs.eo_has_smt_translation aSub :=
    hRecArg hATrans (hArgTyNe aSub hTyApply)
  rw [hSubstEq, hMk]
  exact hBuild aSub hASubTrans hTyApply

/-- Quantifier-shaped substitution case: a non-`Stuck` type for the whole
substitution result forces the capture-avoidance `requires` guard to return the
rebuilt quantified body. This isolates the binder-specific unfolding from the
ordinary application case. -/
theorem substitute_simul_quant_eq_of_typeof_ne_stuck
    (q v vs a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs) ≠
        Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
        xs ts bvs =
      __eo_mk_apply
        (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        (__substitute_simul_rec (Term.Boolean false) a xs ts
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)) := by
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) :=
    SubstituteSupport.substFalse_quant q v vs a xs ts bvs hxs hts hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    apply hTy
    rw [hSubstEq, hReqStuck]
    rfl
  rw [hSubstEq]
  exact instantiate_eo_requires_result_eq_of_ne_stuck hReqNe

theorem substitute_simul_quant_guard_false_of_typeof_ne_stuck
    (q v vs a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs) ≠
        Term.Stuck) :
    __contains_atomic_term_list_free_rec ts
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        Term.__eo_List_nil =
      Term.Boolean false := by
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) :=
    SubstituteSupport.substFalse_quant q v vs a xs ts bvs hxs hts hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ts
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    apply hTy
    rw [hSubstEq, hReqStuck]
    rfl
  exact instantiate_eo_requires_arg_eq_of_ne_stuck hReqNe

theorem eo_mk_apply_apply_head_eq_apply_of_typeof_ne_stuck
    (f x y : Term)
    (hTy : __eo_typeof (__eo_mk_apply (Term.Apply f x) y) ≠ Term.Stuck) :
    __eo_mk_apply (Term.Apply f x) y =
      Term.Apply (Term.Apply f x) y := by
  cases y <;> simp [__eo_mk_apply] at hTy ⊢
  exact False.elim (hTy rfl)

theorem substitute_simul_quant_has_smt_translation_of_typeof_ne_stuck
    (q v vs a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hQuantTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a))
    (hBodySubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) a xs ts
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
        xs ts bvs) := by
  have hSubstEq :=
    substitute_simul_quant_eq_of_typeof_ne_stuck
      q v vs a xs ts bvs hXsEnv hBvsEnv hTs hTy
  rw [hSubstEq] at hTy ⊢
  have hMk :
      __eo_mk_apply
          (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ts
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)) =
        Term.Apply
          (Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ts
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)) :=
    eo_mk_apply_apply_head_eq_apply_of_typeof_ne_stuck
      q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (__substitute_simul_rec (Term.Boolean false) a xs ts
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))
      hTy
  rw [hMk] at hTy ⊢
  have hQuantTrans' :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hQuantTrans
  have hQ :
      q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists :=
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hQuantTrans'
  rcases eo_var_env_of_list_branch_has_smt_translation hQuantTrans' with
    ⟨binderVars, hBinderEnv⟩
  have hBinderNonNil :
      Term.Apply (Term.Apply Term.__eo_List_cons v) vs ≠
        Term.__eo_List_nil := by
    intro h
    cases h
  exact
    eo_has_smt_translation_quant_of_body_translation_and_type
      q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (__substitute_simul_rec (Term.Boolean false) a xs ts
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs))
      hQ hBinderEnv hBinderNonNil
      (quant_binder_types_wf_of_has_smt_translation
        hQ hQuantTrans hBinderEnv)
      hBodySubTrans hTy

/-- Boolean-typed variant of the quantifier-shaped substitution case. -/
theorem substitute_simul_quant_has_smt_translation_of_typeof_bool
    (q v vs a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hQuantTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a))
    (hBodySubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) a xs ts
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) bvs)))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
          xs ts bvs) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) a)
        xs ts bvs) := by
  exact
    substitute_simul_quant_has_smt_translation_of_typeof_ne_stuck
      q v vs a xs ts bvs hXsEnv hBvsEnv hTs hQuantTrans hBodySubTrans
      (by
        intro hStuck
        rw [hStuck] at hTy
        cases hTy)

/-- A variable whose name is not an EO string cannot have an SMT translation. -/
theorem false_of_non_string_var_has_smt_translation
    {name S : Term} {P : Prop}
    (hName : ∀ s, name ≠ Term.String s)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Var name S)) :
    P := by
  exfalso
  apply hTrans
  cases name <;>
    try
      (change __smtx_typeof SmtTerm.None = SmtType.None
       exact TranslationProofs.smtx_typeof_none)
  case String s =>
    exact False.elim (hName s rfl)

/-- Variable case for substitution-result translatability under an arbitrary
bound-variable accumulator, in the general non-`Stuck` typing form needed by
recursive application cases. -/
theorem substitute_simul_var_has_smt_translation_of_typeof_ne_stuck
    (s : native_String) (S xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var (Term.String s) S))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Var (Term.String s) S) xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Var (Term.String s) S) xs ts bvs) := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  rcases hBvsEnv with ⟨bvsExact, hBvsExact, _hBvsEquiv⟩
  by_cases hBound : (s, S) ∈ bvsExact
  · have hb :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) S)) =
          Term.Boolean false :=
      hBvsExact.find_neg_false_of_mem hBound
    have hSubstEq :
        __substitute_simul_rec (Term.Boolean false)
            (Term.Var (Term.String s) S) xs ts bvs =
          Term.Var (Term.String s) S :=
      SubstituteSupport.substitute_simul_rec_var_bound
        (Term.Boolean false) (Term.String s) S xs ts bvs
        hisr hxs hts hbvs hb
    simpa [hSubstEq] using hVarTrans
  · have hFree :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) S)) =
          Term.Boolean true :=
      hBvsExact.find_neg_true_of_not_mem hBound
    rcases hXsEnv with ⟨xsExact, hXsExact, _hXsEquiv⟩
    by_cases hMapped : (s, S) ∈ xsExact
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) =
            Term.Boolean false :=
        hXsExact.find_neg_false_of_mem hMapped
      have hSubstEq :
          __substitute_simul_rec (Term.Boolean false)
              (Term.Var (Term.String s) S) xs ts bvs =
            __assoc_nil_nth Term.__eo_List_cons ts
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) :=
        SubstituteSupport.substitute_simul_rec_var_mapped
          (Term.Boolean false) (Term.String s) S xs ts bvs
          hisr hxs hts hbvs hFree hx
      rw [hSubstEq] at hTy ⊢
      exact
        SubstituteSupport.assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_ne_stuck
          ts
          (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) S))
          hTs hTy
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) =
            Term.Boolean true :=
        hXsExact.find_neg_true_of_not_mem hMapped
      have hSubstEq :
          __substitute_simul_rec (Term.Boolean false)
              (Term.Var (Term.String s) S) xs ts bvs =
            Term.Var (Term.String s) S :=
        SubstituteSupport.substitute_simul_rec_var_unmapped
          (Term.Boolean false) (Term.String s) S xs ts bvs
          hisr hxs hts hbvs hFree hx
      simpa [hSubstEq] using hVarTrans

/-- Variable case for arbitrary EO variable names. Non-string names are ruled
out by the translation hypothesis; string names use the main variable helper. -/
theorem substitute_simul_var_any_has_smt_translation_of_typeof_ne_stuck
    (name S xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name S))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Var name S) xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Var name S) xs ts bvs) := by
  by_cases hString : ∃ s, name = Term.String s
  · rcases hString with ⟨s, rfl⟩
    exact
      substitute_simul_var_has_smt_translation_of_typeof_ne_stuck
        s S xs ts bvs hXsEnv hBvsEnv hVarTrans hTs hTy
  · exact
      false_of_non_string_var_has_smt_translation
        (fun s hEq => hString ⟨s, hEq⟩) hVarTrans

/-- Variable case for substitution-result translatability under an arbitrary
bound-variable accumulator. If the substituted variable result is EO
Boolean-typed, then it has an SMT translation. -/
theorem substitute_simul_var_has_smt_translation_of_typeof_bool
    (s : native_String) (S xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var (Term.String s) S))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Var (Term.String s) S) xs ts bvs) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Var (Term.String s) S) xs ts bvs) := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  rcases hBvsEnv with ⟨bvsExact, hBvsExact, _hBvsEquiv⟩
  by_cases hBound : (s, S) ∈ bvsExact
  · have hb :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) S)) =
          Term.Boolean false :=
      hBvsExact.find_neg_false_of_mem hBound
    have hSubstEq :
        __substitute_simul_rec (Term.Boolean false)
            (Term.Var (Term.String s) S) xs ts bvs =
          Term.Var (Term.String s) S :=
      SubstituteSupport.substitute_simul_rec_var_bound
        (Term.Boolean false) (Term.String s) S xs ts bvs
        hisr hxs hts hbvs hb
    simpa [hSubstEq] using hVarTrans
  · have hFree :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) S)) =
          Term.Boolean true :=
      hBvsExact.find_neg_true_of_not_mem hBound
    rcases hXsEnv with ⟨xsExact, hXsExact, _hXsEquiv⟩
    by_cases hMapped : (s, S) ∈ xsExact
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) =
            Term.Boolean false :=
        hXsExact.find_neg_false_of_mem hMapped
      have hSubstEq :
          __substitute_simul_rec (Term.Boolean false)
              (Term.Var (Term.String s) S) xs ts bvs =
            __assoc_nil_nth Term.__eo_List_cons ts
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) :=
        SubstituteSupport.substitute_simul_rec_var_mapped
          (Term.Boolean false) (Term.String s) S xs ts bvs
          hisr hxs hts hbvs hFree hx
      rw [hSubstEq] at hTy ⊢
      exact
        SubstituteSupport.assoc_nil_nth_has_smt_translation_of_list_all_and_typeof_bool
          ts
          (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) S))
          hTs hTy
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) S)) =
            Term.Boolean true :=
        hXsExact.find_neg_true_of_not_mem hMapped
      have hSubstEq :
          __substitute_simul_rec (Term.Boolean false)
              (Term.Var (Term.String s) S) xs ts bvs =
            Term.Var (Term.String s) S :=
        SubstituteSupport.substitute_simul_rec_var_unmapped
          (Term.Boolean false) (Term.String s) S xs ts bvs
          hisr hxs hts hbvs hFree hx
      simpa [hSubstEq] using hVarTrans

/-- Boolean-typed variant of the arbitrary-name variable helper. -/
theorem substitute_simul_var_any_has_smt_translation_of_typeof_bool
    (name S xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name S))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Var name S) xs ts bvs) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Var name S) xs ts bvs) := by
  by_cases hString : ∃ s, name = Term.String s
  · rcases hString with ⟨s, rfl⟩
    exact
      substitute_simul_var_has_smt_translation_of_typeof_bool
        s S xs ts bvs hXsEnv hBvsEnv hVarTrans hTs hTy
  · exact
      false_of_non_string_var_has_smt_translation
        (fun s hEq => hString ⟨s, hEq⟩) hVarTrans

/-- Top-level variable case for substitution-result translatability. -/
theorem substitute_simul_var_has_smt_translation_of_typeof_bool_nil
    (s : native_String) (S xs ts : Term)
    {xsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var (Term.String s) S))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Var (Term.String s) S) xs ts Term.__eo_List_nil) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Var (Term.String s) S) xs ts Term.__eo_List_nil) := by
  exact
    substitute_simul_var_has_smt_translation_of_typeof_bool
      s S xs ts Term.__eo_List_nil
      hXsEnv
      (EoVarEnvPerm.of_exact EoVarEnv.nil)
      hVarTrans hTs hTy

/-- Atom/default case for substitution-result translatability under an arbitrary
bound-variable accumulator, in the general non-`Stuck` typing form needed by
recursive application cases. -/
theorem substitute_simul_atom_has_smt_translation_of_typeof_ne_stuck
    (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ts bvs) := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false) F xs ts bvs =
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F :=
    SubstituteSupport.substitute_simul_rec_atom
      (Term.Boolean false) F xs ts bvs
      hisr hxs hts hbvs hNotApply hNotVar hNotStuck
  rw [hSubstEq] at hTy ⊢
  by_cases hck :
      native_teq (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) = true
  · have hcTrue : __is_closed_rec F Term.__eo_List_nil = Term.Boolean true := by
      simpa only [native_teq, decide_eq_true_eq] using hck
    have hReq :
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F =
          F := by
      simp [__eo_requires, hcTrue, native_ite, native_teq, native_not,
        SmtEval.native_not]
    simpa [hReq] using hFTrans
  · have hReq :
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F =
          Term.Stuck := by
      simp [__eo_requires, native_ite, hck]
    exfalso
    apply hTy
    rw [hReq]
    rfl

/-- Atom/default case for substitution-result translatability under an arbitrary
bound-variable accumulator. -/
theorem substitute_simul_atom_has_smt_translation_of_typeof_bool
    (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts bvs) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ts bvs) := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false) F xs ts bvs =
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F :=
    SubstituteSupport.substitute_simul_rec_atom
      (Term.Boolean false) F xs ts bvs
      hisr hxs hts hbvs hNotApply hNotVar hNotStuck
  rw [hSubstEq] at hTy ⊢
  by_cases hck :
      native_teq (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) = true
  · have hcTrue : __is_closed_rec F Term.__eo_List_nil = Term.Boolean true := by
      simpa only [native_teq, decide_eq_true_eq] using hck
    have hReq :
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F =
          F := by
      simp [__eo_requires, hcTrue, native_ite, native_teq, native_not,
        SmtEval.native_not]
    simpa [hReq] using hFTrans
  · have hReq :
        __eo_requires (__is_closed_rec F Term.__eo_List_nil) (Term.Boolean true) F =
          Term.Stuck := by
      simp [__eo_requires, native_ite, hck]
    rw [hReq] at hTy
    change Term.Stuck = Term.Bool at hTy
    cases hTy

/-- Atom/default case for top-level substitution-result translatability. -/
theorem substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
    (F xs ts : Term)
    {xsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
        Term.Bool) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) := by
  exact
    substitute_simul_atom_has_smt_translation_of_typeof_bool
      F xs ts Term.__eo_List_nil
      hXsEnv
      (EoVarEnvPerm.of_exact EoVarEnv.nil)
      hTs hNotApply hNotVar hNotStuck hFTrans hTy

/-- Size-recursive form of general substitution-result translatability, under
an arbitrary bound-variable accumulator. The instantiate guard (`hActuals`) is
threaded through because several EO heads are more permissive than their SMT
translations unless substitution preserves the exact binder types. The remaining
recursive work is the application case, where SMT-translatable EO applications
must be inverted by operator shape before rebuilding the substituted application. -/
theorem substitute_simul_has_smt_translation_of_typeof_ne_stuck_lt
    (n : Nat) (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hLt : sizeOf F < n)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ts bvs) := by
  cases n with
  | zero =>
      omega
  | succ n =>
      let hRec :
          ∀ {G xs' ts' bvs' : Term} {xsVars' bvsVars' : List EoVarKey},
            sizeOf G < sizeOf F ->
            EoVarEnvPerm xs' xsVars' ->
            EoVarEnvPerm bvs' bvsVars' ->
            RuleProofs.eo_has_smt_translation G ->
            EoListAllHaveSmtTranslation ts' ->
            SubstActualsHaveSmtTypes xs' ts' ->
            __eo_typeof
                (__substitute_simul_rec (Term.Boolean false) G xs' ts' bvs') ≠
              Term.Stuck ->
            RuleProofs.eo_has_smt_translation
              (__substitute_simul_rec (Term.Boolean false) G xs' ts' bvs') :=
        fun {G xs' ts' bvs'} {xsVars' bvsVars'} hGLt hXsEnv' hBvsEnv'
            hGTrans hTs' hActuals' hGTy =>
          substitute_simul_has_smt_translation_of_typeof_ne_stuck_lt
            n G xs' ts' bvs'
            (by omega) hXsEnv' hBvsEnv' hGTrans hTs' hActuals' hGTy
      cases F
      case Apply f a =>
          by_cases hBinder :
              ∃ q v vs,
                f =
                  Term.Apply q
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
          · rcases hBinder with ⟨q, v, vs, rfl⟩
            let binders := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
            let bodySub :=
              __substitute_simul_rec (Term.Boolean false) a xs ts
                (__eo_list_concat Term.__eo_List_cons binders bvs)
            have hFTrans' :
                eoHasSmtTranslation
                  (Term.Apply (Term.Apply q binders) a) := by
              simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                binders] using hFTrans
            have hQ :
                q = Term.UOp UserOp.forall ∨
                  q = Term.UOp UserOp.exists :=
              is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                hFTrans'
            rcases eo_var_env_of_list_branch_has_smt_translation hFTrans' with
              ⟨binderVars, hBinderEnv⟩
            have hSubstEq :
                __substitute_simul_rec (Term.Boolean false)
                    (Term.Apply (Term.Apply q binders) a) xs ts bvs =
                  __eo_mk_apply (Term.Apply q binders) bodySub := by
              simpa [binders, bodySub] using
                substitute_simul_quant_eq_of_typeof_ne_stuck
                  q v vs a xs ts bvs hXsEnv hBvsEnv hTs hTy
            have hTyMk :
                __eo_typeof
                    (__eo_mk_apply (Term.Apply q binders) bodySub) ≠
                  Term.Stuck := by
              rwa [hSubstEq] at hTy
            have hMk :
                __eo_mk_apply (Term.Apply q binders) bodySub =
                  Term.Apply (Term.Apply q binders) bodySub :=
              eo_mk_apply_apply_head_eq_apply_of_typeof_ne_stuck
                q binders bodySub hTyMk
            have hTyApply :
                __eo_typeof (Term.Apply (Term.Apply q binders) bodySub) ≠
                  Term.Stuck := by
              rwa [hMk] at hTyMk
            have hBodyBool : __eo_typeof bodySub = Term.Bool :=
              eo_typeof_body_bool_of_quant_type_ne_stuck
                hQ hBinderEnv hTyApply
            have hBodyTy : __eo_typeof bodySub ≠ Term.Stuck := by
              rw [hBodyBool]
              intro h
              cases h
            have hBodyTrans :
                RuleProofs.eo_has_smt_translation a := by
              simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                using
                  body_has_smt_translation_of_list_branch_has_smt_translation
                    hFTrans'
            have hBvsEnv' :
                EoVarEnvPerm
                  (__eo_list_concat Term.__eo_List_cons binders bvs)
                  (binderVars.reverse ++ bvsVars) :=
              EoVarEnvPerm.concat_rev hBinderEnv hBvsEnv
            have hBodySubTrans :
                RuleProofs.eo_has_smt_translation bodySub :=
              hRec
                (G := a) (xs' := xs) (ts' := ts)
                (bvs' := __eo_list_concat Term.__eo_List_cons binders bvs)
                (by simp; omega)
                hXsEnv hBvsEnv' hBodyTrans hTs hActuals
                (by simpa [bodySub] using hBodyTy)
            exact
              substitute_simul_quant_has_smt_translation_of_typeof_ne_stuck
                q v vs a xs ts bvs hXsEnv hBvsEnv hTs hFTrans
                (by simpa [binders, bodySub] using hBodySubTrans)
                hTy
          · by_cases hNot : f = Term.UOp UserOp.not
            · subst f
              let aSub :=
                __substitute_simul_rec (Term.Boolean false) a xs ts bvs
              have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
              have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
              have hts : ts ≠ Term.Stuck :=
                eoListAllHaveSmtTranslation_ne_stuck hTs
              have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
              have hHeadSub :
                  __substitute_simul_rec (Term.Boolean false)
                      (Term.UOp UserOp.not) xs ts bvs =
                    Term.UOp UserOp.not := by
                have hHeadEq :
                    __substitute_simul_rec (Term.Boolean false)
                        (Term.UOp UserOp.not) xs ts bvs =
                      __eo_requires
                        (__is_closed_rec (Term.UOp UserOp.not)
                          Term.__eo_List_nil)
                        (Term.Boolean true) (Term.UOp UserOp.not) :=
                  SubstituteSupport.substitute_simul_rec_atom
                    (Term.Boolean false) (Term.UOp UserOp.not) xs ts bvs
                    hisr hxs hts hbvs
                    (by intro f a h; cases h)
                    (by intro s S h; cases h)
                    (by intro h; cases h)
                rw [hHeadEq]
                simp [__is_closed_rec, __eo_requires, native_ite,
                  native_teq, native_not, SmtEval.native_not]
              have hSubstEq :
                  __substitute_simul_rec (Term.Boolean false)
                      (Term.Apply (Term.UOp UserOp.not) a) xs ts bvs =
                    __eo_mk_apply (Term.UOp UserOp.not) aSub := by
                have hApplyEq :=
                  SubstituteSupport.substitute_simul_rec_apply
                    (Term.Boolean false) (Term.UOp UserOp.not) a xs ts bvs
                    hisr hxs hts hbvs
                    (by
                      intro q v vs hEq
                      exact hBinder ⟨q, v, vs, hEq⟩)
                simpa [aSub, hHeadSub] using hApplyEq
              have hTyMk :
                  __eo_typeof (__eo_mk_apply (Term.UOp UserOp.not) aSub) ≠
                    Term.Stuck := by
                rwa [hSubstEq] at hTy
              have hMk :
                  __eo_mk_apply (Term.UOp UserOp.not) aSub =
                    Term.Apply (Term.UOp UserOp.not) aSub :=
                instantiate_eo_mk_apply_eq_apply_of_typeof_ne_stuck
                  (Term.UOp UserOp.not) aSub hTyMk
              have hTyApply :
                  __eo_typeof (Term.Apply (Term.UOp UserOp.not) aSub) ≠
                    Term.Stuck := by
                rwa [hMk] at hTyMk
              have hASubBool : __eo_typeof aSub = Term.Bool := by
                change __eo_typeof_not (__eo_typeof aSub) ≠
                  Term.Stuck at hTyApply
                cases hAType : __eo_typeof aSub <;>
                  simp [__eo_typeof_not, hAType] at hTyApply ⊢
              have hFTransEo :
                  eoHasSmtTranslation
                    (Term.Apply (Term.UOp UserOp.not) a) := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using hFTrans
              have hATrans :
                  RuleProofs.eo_has_smt_translation a := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using
                    not_arg_has_smt_translation_of_has_smt_translation
                      hFTransEo
              have hASubTrans :
                  RuleProofs.eo_has_smt_translation aSub :=
                hRec
                  (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                  (by simp)
                  hXsEnv hBvsEnv hATrans hTs hActuals
                  (by
                    rw [hASubBool]
                    intro h
                    cases h)
              have hASubBoolType : RuleProofs.eo_has_bool_type aSub :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  aSub hASubTrans hASubBool
              have hNotTrans :
                  RuleProofs.eo_has_smt_translation
                    (Term.Apply (Term.UOp UserOp.not) aSub) :=
                RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (Term.Apply (Term.UOp UserOp.not) aSub)
                  (RuleProofs.eo_has_bool_type_not_of_bool_arg
                    aSub hASubBoolType)
              rwa [hSubstEq, hMk]
            · by_cases hToReal : f = Term.UOp UserOp.to_real
              · subst f
                let aSub :=
                  __substitute_simul_rec (Term.Boolean false) a xs ts bvs
                have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
                have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
                have hts : ts ≠ Term.Stuck :=
                  eoListAllHaveSmtTranslation_ne_stuck hTs
                have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
                have hHeadSub :
                    __substitute_simul_rec (Term.Boolean false)
                        (Term.UOp UserOp.to_real) xs ts bvs =
                      Term.UOp UserOp.to_real :=
                  substitute_simul_rec_uop_eq_self
                    UserOp.to_real xs ts bvs hXsEnv hBvsEnv hTs
                have hSubstEq :
                    __substitute_simul_rec (Term.Boolean false)
                        (Term.Apply (Term.UOp UserOp.to_real) a) xs ts bvs =
                      __eo_mk_apply (Term.UOp UserOp.to_real) aSub := by
                  have hApplyEq :=
                    SubstituteSupport.substitute_simul_rec_apply
                      (Term.Boolean false) (Term.UOp UserOp.to_real) a xs ts bvs
                      hisr hxs hts hbvs
                      (by
                        intro q v vs hEq
                        exact hBinder ⟨q, v, vs, hEq⟩)
                  simpa [aSub, hHeadSub] using hApplyEq
                have hTyMk :
                    __eo_typeof (__eo_mk_apply (Term.UOp UserOp.to_real) aSub) ≠
                      Term.Stuck := by
                  rwa [hSubstEq] at hTy
                have hMk :
                    __eo_mk_apply (Term.UOp UserOp.to_real) aSub =
                      Term.Apply (Term.UOp UserOp.to_real) aSub :=
                  instantiate_eo_mk_apply_eq_apply_of_typeof_ne_stuck
                    (Term.UOp UserOp.to_real) aSub hTyMk
                have hTyApply :
                    __eo_typeof (Term.Apply (Term.UOp UserOp.to_real) aSub) ≠
                      Term.Stuck := by
                  rwa [hMk] at hTyMk
                have hASubTyNe : __eo_typeof aSub ≠ Term.Stuck := by
                  intro hAStuck
                  apply hTyApply
                  change __eo_typeof_to_real (__eo_typeof aSub) = Term.Stuck
                  rw [hAStuck]
                  rfl
                have hArgArith :
                    __eo_typeof aSub = Term.UOp UserOp.Int ∨
                      __eo_typeof aSub = Term.UOp UserOp.Real := by
                  apply eo_typeof_to_real_arg_arith_of_ne_stuck
                  change __eo_typeof_to_real (__eo_typeof aSub) ≠
                    Term.Stuck at hTyApply
                  exact hTyApply
                have hFTransEo :
                    eoHasSmtTranslation
                      (Term.Apply (Term.UOp UserOp.to_real) a) := by
                  simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                    using hFTrans
                have hATrans :
                    RuleProofs.eo_has_smt_translation a := by
                  simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                    using
                      to_real_arg_has_smt_translation_of_has_smt_translation
                        hFTransEo
                have hASubTrans :
                    RuleProofs.eo_has_smt_translation aSub :=
                  hRec
                    (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                    (by simp)
                    hXsEnv hBvsEnv hATrans hTs hActuals hASubTyNe
                have hASubMatch :
                    __smtx_typeof (__eo_to_smt aSub) =
                      __eo_to_smt_type (__eo_typeof aSub) :=
                  TranslationProofs.eo_to_smt_typeof_matches_translation
                    aSub hASubTrans
                have hToRealTrans :
                    RuleProofs.eo_has_smt_translation
                      (Term.Apply (Term.UOp UserOp.to_real) aSub) := by
                  unfold RuleProofs.eo_has_smt_translation
                  change
                    __smtx_typeof (SmtTerm.to_real (__eo_to_smt aSub)) ≠
                      SmtType.None
                  rw [typeof_to_real_eq]
                  rcases hArgArith with hArgInt | hArgReal
                  · have hSmtArg :
                        __smtx_typeof (__eo_to_smt aSub) = SmtType.Int := by
                      rw [hASubMatch, hArgInt]
                      rfl
                    simp [hSmtArg, native_ite, native_Teq]
                  · have hSmtArg :
                        __smtx_typeof (__eo_to_smt aSub) = SmtType.Real := by
                      rw [hASubMatch, hArgReal]
                      rfl
                    simp [hSmtArg, native_ite, native_Teq]
                rw [hSubstEq, hMk]
                exact hToRealTrans
              · by_cases hToInt : f = Term.UOp UserOp.to_int
                · subst f
                  let aSub :=
                    __substitute_simul_rec (Term.Boolean false) a xs ts bvs
                  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
                  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
                  have hts : ts ≠ Term.Stuck :=
                    eoListAllHaveSmtTranslation_ne_stuck hTs
                  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
                  have hHeadSub :
                      __substitute_simul_rec (Term.Boolean false)
                          (Term.UOp UserOp.to_int) xs ts bvs =
                        Term.UOp UserOp.to_int :=
                    substitute_simul_rec_uop_eq_self
                      UserOp.to_int xs ts bvs hXsEnv hBvsEnv hTs
                  have hSubstEq :
                      __substitute_simul_rec (Term.Boolean false)
                          (Term.Apply (Term.UOp UserOp.to_int) a) xs ts bvs =
                        __eo_mk_apply (Term.UOp UserOp.to_int) aSub := by
                    have hApplyEq :=
                      SubstituteSupport.substitute_simul_rec_apply
                        (Term.Boolean false) (Term.UOp UserOp.to_int) a xs ts bvs
                        hisr hxs hts hbvs
                        (by
                          intro q v vs hEq
                          exact hBinder ⟨q, v, vs, hEq⟩)
                    simpa [aSub, hHeadSub] using hApplyEq
                  have hTyMk :
                      __eo_typeof (__eo_mk_apply (Term.UOp UserOp.to_int) aSub) ≠
                        Term.Stuck := by
                    rwa [hSubstEq] at hTy
                  have hMk :
                      __eo_mk_apply (Term.UOp UserOp.to_int) aSub =
                        Term.Apply (Term.UOp UserOp.to_int) aSub :=
                    instantiate_eo_mk_apply_eq_apply_of_typeof_ne_stuck
                      (Term.UOp UserOp.to_int) aSub hTyMk
                  have hTyApply :
                      __eo_typeof (Term.Apply (Term.UOp UserOp.to_int) aSub) ≠
                        Term.Stuck := by
                    rwa [hMk] at hTyMk
                  have hArgReal :
                      __eo_typeof aSub = Term.UOp UserOp.Real := by
                    apply eo_typeof_to_int_arg_real_of_ne_stuck
                    change __eo_typeof_to_int (__eo_typeof aSub) ≠
                      Term.Stuck at hTyApply
                    exact hTyApply
                  have hASubTyNe : __eo_typeof aSub ≠ Term.Stuck := by
                    rw [hArgReal]
                    intro h
                    cases h
                  have hFTransEo :
                      eoHasSmtTranslation
                        (Term.Apply (Term.UOp UserOp.to_int) a) := by
                    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                      using hFTrans
                  have hATrans :
                      RuleProofs.eo_has_smt_translation a := by
                    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                      using
                        to_int_arg_has_smt_translation_of_has_smt_translation
                          hFTransEo
                  have hASubTrans :
                      RuleProofs.eo_has_smt_translation aSub :=
                    hRec
                      (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                      (by simp)
                      hXsEnv hBvsEnv hATrans hTs hActuals hASubTyNe
                  have hASubMatch :
                      __smtx_typeof (__eo_to_smt aSub) =
                        __eo_to_smt_type (__eo_typeof aSub) :=
                    TranslationProofs.eo_to_smt_typeof_matches_translation
                      aSub hASubTrans
                  have hToIntTrans :
                      RuleProofs.eo_has_smt_translation
                        (Term.Apply (Term.UOp UserOp.to_int) aSub) := by
                    unfold RuleProofs.eo_has_smt_translation
                    change
                      __smtx_typeof (SmtTerm.to_int (__eo_to_smt aSub)) ≠
                        SmtType.None
                    rw [typeof_to_int_eq]
                    have hSmtArg :
                        __smtx_typeof (__eo_to_smt aSub) = SmtType.Real := by
                      rw [hASubMatch, hArgReal]
                      rfl
                    simp [hSmtArg, native_ite, native_Teq]
                  rw [hSubstEq, hMk]
                  exact hToIntTrans
                · by_cases hIsInt : f = Term.UOp UserOp.is_int
                  · subst f
                    let aSub :=
                      __substitute_simul_rec (Term.Boolean false) a xs ts bvs
                    have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
                    have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
                    have hts : ts ≠ Term.Stuck :=
                      eoListAllHaveSmtTranslation_ne_stuck hTs
                    have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
                    have hHeadSub :
                        __substitute_simul_rec (Term.Boolean false)
                            (Term.UOp UserOp.is_int) xs ts bvs =
                          Term.UOp UserOp.is_int :=
                      substitute_simul_rec_uop_eq_self
                        UserOp.is_int xs ts bvs hXsEnv hBvsEnv hTs
                    have hSubstEq :
                        __substitute_simul_rec (Term.Boolean false)
                            (Term.Apply (Term.UOp UserOp.is_int) a) xs ts bvs =
                          __eo_mk_apply (Term.UOp UserOp.is_int) aSub := by
                      have hApplyEq :=
                        SubstituteSupport.substitute_simul_rec_apply
                          (Term.Boolean false) (Term.UOp UserOp.is_int) a xs ts bvs
                          hisr hxs hts hbvs
                          (by
                            intro q v vs hEq
                            exact hBinder ⟨q, v, vs, hEq⟩)
                      simpa [aSub, hHeadSub] using hApplyEq
                    have hTyMk :
                        __eo_typeof (__eo_mk_apply (Term.UOp UserOp.is_int) aSub) ≠
                          Term.Stuck := by
                      rwa [hSubstEq] at hTy
                    have hMk :
                        __eo_mk_apply (Term.UOp UserOp.is_int) aSub =
                          Term.Apply (Term.UOp UserOp.is_int) aSub :=
                      instantiate_eo_mk_apply_eq_apply_of_typeof_ne_stuck
                        (Term.UOp UserOp.is_int) aSub hTyMk
                    have hTyApply :
                        __eo_typeof (Term.Apply (Term.UOp UserOp.is_int) aSub) ≠
                          Term.Stuck := by
                      rwa [hMk] at hTyMk
                    have hArgReal :
                        __eo_typeof aSub = Term.UOp UserOp.Real := by
                      apply eo_typeof_is_int_arg_real_of_ne_stuck
                      change __eo_typeof_is_int (__eo_typeof aSub) ≠
                        Term.Stuck at hTyApply
                      exact hTyApply
                    have hASubTyNe : __eo_typeof aSub ≠ Term.Stuck := by
                      rw [hArgReal]
                      intro h
                      cases h
                    have hFTransEo :
                        eoHasSmtTranslation
                          (Term.Apply (Term.UOp UserOp.is_int) a) := by
                      simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                        using hFTrans
                    have hATrans :
                        RuleProofs.eo_has_smt_translation a := by
                      simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                        using
                          is_int_arg_has_smt_translation_of_has_smt_translation
                            hFTransEo
                    have hASubTrans :
                        RuleProofs.eo_has_smt_translation aSub :=
                      hRec
                        (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                        (by simp)
                        hXsEnv hBvsEnv hATrans hTs hActuals hASubTyNe
                    have hASubMatch :
                        __smtx_typeof (__eo_to_smt aSub) =
                          __eo_to_smt_type (__eo_typeof aSub) :=
                      TranslationProofs.eo_to_smt_typeof_matches_translation
                        aSub hASubTrans
                    have hIsIntTrans :
                        RuleProofs.eo_has_smt_translation
                          (Term.Apply (Term.UOp UserOp.is_int) aSub) := by
                      unfold RuleProofs.eo_has_smt_translation
                      change
                        __smtx_typeof (SmtTerm.is_int (__eo_to_smt aSub)) ≠
                          SmtType.None
                      rw [typeof_is_int_eq]
                      have hSmtArg :
                          __smtx_typeof (__eo_to_smt aSub) = SmtType.Real := by
                        rw [hASubMatch, hArgReal]
                        rfl
                      simp [hSmtArg, native_ite, native_Teq]
                    rw [hSubstEq, hMk]
                    exact hIsIntTrans
                  · by_cases hUneg : f = Term.UOp UserOp.__eoo_neg_2
                    · subst f
                      exact
                        substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                          UserOp.__eoo_neg_2 a xs ts bvs hXsEnv hBvsEnv hTs
                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                          hFTrans hTy
                          (fun h => uneg_arg_has_smt_translation_of_has_smt_translation h)
                          (fun X hApp => by
                            change __eo_typeof_abs (__eo_typeof X) ≠ Term.Stuck at hApp
                            rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with hArg | hArg
                            · rw [hArg]
                              intro h
                              cases h
                            · rw [hArg]
                              intro h
                              cases h)
                          (fun X hXTrans hApp => by
                            have hXMatch :
                                __smtx_typeof (__eo_to_smt X) =
                                  __eo_to_smt_type (__eo_typeof X) :=
                              TranslationProofs.eo_to_smt_typeof_matches_translation
                                X hXTrans
                            unfold RuleProofs.eo_has_smt_translation
                            change
                              __smtx_typeof (SmtTerm.uneg (__eo_to_smt X)) ≠
                                SmtType.None
                            rw [typeof_uneg_eq]
                            change __eo_typeof_abs (__eo_typeof X) ≠ Term.Stuck at hApp
                            rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with hArgInt | hArgReal
                            · have hSmtArg :
                                  __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                rw [hXMatch, hArgInt]
                                rfl
                              simp [__smtx_typeof_arith_overload_op_1,
                                hSmtArg]
                            · have hSmtArg :
                                  __smtx_typeof (__eo_to_smt X) = SmtType.Real := by
                                rw [hXMatch, hArgReal]
                                rfl
                              simp [__smtx_typeof_arith_overload_op_1,
                                hSmtArg])
                          (fun hATrans hATy =>
                            hRec
                              (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                              (by simp)
                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                    · by_cases hPow2 : f = Term.UOp UserOp.int_pow2
                      · subst f
                        exact
                          substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                            UserOp.int_pow2 a xs ts bvs hXsEnv hBvsEnv hTs
                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                            hFTrans hTy
                            (fun h => int_pow2_arg_has_smt_translation_of_has_smt_translation h)
                            (fun X hApp => by
                              change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                Term.Stuck at hApp
                              rw [eo_typeof_int_pow2_arg_int_of_ne_stuck hApp]
                              intro h
                              cases h)
                            (fun X hXTrans hApp => by
                              have hXMatch :
                                  __smtx_typeof (__eo_to_smt X) =
                                    __eo_to_smt_type (__eo_typeof X) :=
                                TranslationProofs.eo_to_smt_typeof_matches_translation
                                  X hXTrans
                              unfold RuleProofs.eo_has_smt_translation
                              change
                                __smtx_typeof (SmtTerm.int_pow2 (__eo_to_smt X)) ≠
                                  SmtType.None
                              rw [typeof_int_pow2_eq]
                              change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                Term.Stuck at hApp
                              have hArgInt :=
                                eo_typeof_int_pow2_arg_int_of_ne_stuck hApp
                              have hSmtArg :
                                  __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                rw [hXMatch, hArgInt]
                                rfl
                              simp [hSmtArg, native_ite, native_Teq])
                            (fun hATrans hATy =>
                              hRec
                                (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                (by simp)
                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                      · by_cases hLog2 : f = Term.UOp UserOp.int_log2
                        · subst f
                          exact
                            substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                              UserOp.int_log2 a xs ts bvs hXsEnv hBvsEnv hTs
                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                              hFTrans hTy
                              (fun h => int_log2_arg_has_smt_translation_of_has_smt_translation h)
                              (fun X hApp => by
                                change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                rw [eo_typeof_int_pow2_arg_int_of_ne_stuck hApp]
                                intro h
                                cases h)
                              (fun X hXTrans hApp => by
                                have hXMatch :
                                    __smtx_typeof (__eo_to_smt X) =
                                      __eo_to_smt_type (__eo_typeof X) :=
                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                    X hXTrans
                                unfold RuleProofs.eo_has_smt_translation
                                change
                                  __smtx_typeof (SmtTerm.int_log2 (__eo_to_smt X)) ≠
                                    SmtType.None
                                rw [typeof_int_log2_eq]
                                change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                have hArgInt :=
                                  eo_typeof_int_pow2_arg_int_of_ne_stuck hApp
                                have hSmtArg :
                                    __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                  rw [hXMatch, hArgInt]
                                  rfl
                                simp [hSmtArg, native_ite, native_Teq])
                              (fun hATrans hATy =>
                                hRec
                                  (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                  (by simp)
                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                        · by_cases hIntIspow2 : f = Term.UOp UserOp.int_ispow2
                          · subst f
                            exact
                              substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                UserOp.int_ispow2 a xs ts bvs hXsEnv hBvsEnv hTs
                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                hFTrans hTy
                                (fun h => int_ispow2_arg_has_smt_translation_of_has_smt_translation h)
                                (fun X hApp => by
                                  change __eo_typeof_int_ispow2 (__eo_typeof X) ≠
                                    Term.Stuck at hApp
                                  rw [eo_typeof_int_ispow2_arg_int_of_ne_stuck hApp]
                                  intro h
                                  cases h)
                                (fun X hXTrans hApp => by
                                  have hXMatch :
                                      __smtx_typeof (__eo_to_smt X) =
                                        __eo_to_smt_type (__eo_typeof X) :=
                                    TranslationProofs.eo_to_smt_typeof_matches_translation
                                      X hXTrans
                                  unfold RuleProofs.eo_has_smt_translation
                                  change
                                    __smtx_typeof
                                        (SmtTerm.and
                                          (SmtTerm.geq (__eo_to_smt X)
                                            (SmtTerm.Numeral 0))
                                          (SmtTerm.eq (__eo_to_smt X)
                                            (SmtTerm.int_pow2
                                              (SmtTerm.int_log2 (__eo_to_smt X))))) ≠
                                      SmtType.None
                                  change __eo_typeof_int_ispow2 (__eo_typeof X) ≠
                                    Term.Stuck at hApp
                                  have hArgInt :=
                                    eo_typeof_int_ispow2_arg_int_of_ne_stuck hApp
                                  have hSmtArg :
                                      __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                    rw [hXMatch, hArgInt]
                                    rfl
                                  rw [typeof_and_eq, typeof_geq_eq, typeof_eq_eq,
                                    typeof_int_pow2_eq, typeof_int_log2_eq, hSmtArg,
                                    __smtx_typeof.eq_2]
                                  simp [__smtx_typeof_arith_overload_op_2_ret,
                                    __smtx_typeof_eq, __smtx_typeof_guard,
                                    native_ite, native_Teq])
                                (fun hATrans hATy =>
                                  hRec
                                    (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                    (by simp)
                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                          · by_cases hIntDivByZero :
                              f = Term.UOp UserOp._at_int_div_by_zero
                            · subst f
                              exact
                                substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                  UserOp._at_int_div_by_zero a xs ts bvs hXsEnv hBvsEnv hTs
                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                  hFTrans hTy
                                  (fun h => int_div_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                  (fun X hApp => by
                                    change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                      Term.Stuck at hApp
                                    rw [eo_typeof_int_pow2_arg_int_of_ne_stuck hApp]
                                    intro h
                                    cases h)
                                  (fun X hXTrans hApp => by
                                    have hXMatch :
                                        __smtx_typeof (__eo_to_smt X) =
                                          __eo_to_smt_type (__eo_typeof X) :=
                                      TranslationProofs.eo_to_smt_typeof_matches_translation
                                        X hXTrans
                                    unfold RuleProofs.eo_has_smt_translation
                                    change
                                      __smtx_typeof
                                          (SmtTerm.div (__eo_to_smt X)
                                            (SmtTerm.Numeral 0)) ≠
                                        SmtType.None
                                    rw [typeof_div_eq]
                                    change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                      Term.Stuck at hApp
                                    have hArgInt :=
                                      eo_typeof_int_pow2_arg_int_of_ne_stuck hApp
                                    have hSmtArg :
                                        __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                      rw [hXMatch, hArgInt]
                                      rfl
                                    simp [hSmtArg, __smtx_typeof.eq_2,
                                      native_ite, native_Teq])
                                  (fun hATrans hATy =>
                                    hRec
                                      (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                      (by simp)
                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                            · by_cases hModByZero :
                                f = Term.UOp UserOp._at_mod_by_zero
                              · subst f
                                exact
                                  substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                    UserOp._at_mod_by_zero a xs ts bvs hXsEnv hBvsEnv hTs
                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                    hFTrans hTy
                                    (fun h => mod_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                    (fun X hApp => by
                                      change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                        Term.Stuck at hApp
                                      rw [eo_typeof_int_pow2_arg_int_of_ne_stuck hApp]
                                      intro h
                                      cases h)
                                    (fun X hXTrans hApp => by
                                      have hXMatch :
                                          __smtx_typeof (__eo_to_smt X) =
                                            __eo_to_smt_type (__eo_typeof X) :=
                                        TranslationProofs.eo_to_smt_typeof_matches_translation
                                          X hXTrans
                                      unfold RuleProofs.eo_has_smt_translation
                                      change
                                        __smtx_typeof
                                            (SmtTerm.mod (__eo_to_smt X)
                                              (SmtTerm.Numeral 0)) ≠
                                          SmtType.None
                                      rw [typeof_mod_eq]
                                      change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                        Term.Stuck at hApp
                                      have hArgInt :=
                                        eo_typeof_int_pow2_arg_int_of_ne_stuck hApp
                                      have hSmtArg :
                                          __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                        rw [hXMatch, hArgInt]
                                        rfl
                                      simp [hSmtArg, __smtx_typeof.eq_2,
                                        native_ite, native_Teq])
                                    (fun hATrans hATy =>
                                      hRec
                                        (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                        (by simp)
                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                              · by_cases hQdivByZero :
                                  f = Term.UOp UserOp._at_div_by_zero
                                · subst f
                                  exact
                                    substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                      UserOp._at_div_by_zero a xs ts bvs hXsEnv hBvsEnv hTs
                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                      hFTrans hTy
                                      (fun h => qdiv_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                      (fun X hApp => by
                                        change __eo_typeof__at_div_by_zero (__eo_typeof X) ≠
                                          Term.Stuck at hApp
                                        rw [eo_typeof_at_div_by_zero_arg_real_of_ne_stuck hApp]
                                        intro h
                                        cases h)
                                      (fun X hXTrans hApp => by
                                        have hXMatch :
                                            __smtx_typeof (__eo_to_smt X) =
                                              __eo_to_smt_type (__eo_typeof X) :=
                                          TranslationProofs.eo_to_smt_typeof_matches_translation
                                            X hXTrans
                                        unfold RuleProofs.eo_has_smt_translation
                                        change
                                          __smtx_typeof
                                              (SmtTerm.qdiv (__eo_to_smt X)
                                                (SmtTerm.Rational
                                                  (native_mk_rational 0 1))) ≠
                                            SmtType.None
                                        change __eo_typeof__at_div_by_zero (__eo_typeof X) ≠
                                          Term.Stuck at hApp
                                        have hArgReal :=
                                          eo_typeof_at_div_by_zero_arg_real_of_ne_stuck hApp
                                        have hSmtArg :
                                            __smtx_typeof (__eo_to_smt X) = SmtType.Real := by
                                          rw [hXMatch, hArgReal]
                                          rfl
                                        have hRatTy :
                                            __smtx_typeof
                                                (SmtTerm.Rational
                                                  (native_mk_rational 0 1)) =
                                              SmtType.Real := by
                                          unfold __smtx_typeof
                                          rfl
                                        rw [typeof_qdiv_eq, hSmtArg, hRatTy]
                                        simp [__smtx_typeof_arith_overload_op_2_ret])
                                      (fun hATrans hATy =>
                                        hRec
                                          (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                          (by simp)
                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                · by_cases hBvnot :
                                    f = Term.UOp UserOp.bvnot
                                  · subst f
                                    exact
                                      substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                        UserOp.bvnot a xs ts bvs hXsEnv hBvsEnv hTs
                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                        hFTrans hTy
                                        (fun h => bvnot_arg_has_smt_translation_of_has_smt_translation h)
                                        (fun X hApp => by
                                          change __eo_typeof_bvnot (__eo_typeof X) ≠
                                            Term.Stuck at hApp
                                          rcases eo_typeof_bvnot_arg_bitvec_of_ne_stuck hApp with
                                            ⟨w, hArg⟩
                                          rw [hArg]
                                          intro h
                                          cases h)
                                        (fun X hXTrans hApp => by
                                          unfold RuleProofs.eo_has_smt_translation
                                          change
                                            __smtx_typeof
                                                (SmtTerm.bvnot (__eo_to_smt X)) ≠
                                              SmtType.None
                                          change __eo_typeof_bvnot (__eo_typeof X) ≠
                                            Term.Stuck at hApp
                                          rcases eo_typeof_bvnot_arg_bitvec_of_ne_stuck hApp with
                                            ⟨w, hArgEo⟩
                                          rcases
                                              smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                hXTrans hArgEo with
                                            ⟨n, hSmtArg⟩
                                          rw [smt_typeof_bvnot_eq, hSmtArg]
                                          simp [__smtx_typeof_bv_op_1])
                                        (fun hATrans hATy =>
                                          hRec
                                            (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                            (by simp)
                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                  · by_cases hBvneg :
                                      f = Term.UOp UserOp.bvneg
                                    · subst f
                                      exact
                                        substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                          UserOp.bvneg a xs ts bvs hXsEnv hBvsEnv hTs
                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                          hFTrans hTy
                                          (fun h => bvneg_arg_has_smt_translation_of_has_smt_translation h)
                                          (fun X hApp => by
                                            change __eo_typeof_bvnot (__eo_typeof X) ≠
                                              Term.Stuck at hApp
                                            rcases eo_typeof_bvnot_arg_bitvec_of_ne_stuck hApp with
                                              ⟨w, hArg⟩
                                            rw [hArg]
                                            intro h
                                            cases h)
                                          (fun X hXTrans hApp => by
                                            unfold RuleProofs.eo_has_smt_translation
                                            change
                                              __smtx_typeof
                                                  (SmtTerm.bvneg (__eo_to_smt X)) ≠
                                                SmtType.None
                                            change __eo_typeof_bvnot (__eo_typeof X) ≠
                                              Term.Stuck at hApp
                                            rcases eo_typeof_bvnot_arg_bitvec_of_ne_stuck hApp with
                                              ⟨w, hArgEo⟩
                                            rcases
                                                smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                  hXTrans hArgEo with
                                              ⟨n, hSmtArg⟩
                                            rw [smt_typeof_bvneg_eq, hSmtArg]
                                            simp [__smtx_typeof_bv_op_1])
                                          (fun hATrans hATy =>
                                            hRec
                                              (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                              (by simp)
                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                    · by_cases hBvnego :
                                        f = Term.UOp UserOp.bvnego
                                      · subst f
                                        exact
                                          substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                            UserOp.bvnego a xs ts bvs hXsEnv hBvsEnv hTs
                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                            hFTrans hTy
                                            (fun h => bvnego_arg_has_smt_translation_of_has_smt_translation h)
                                            (fun X hApp => by
                                              change __eo_typeof_bvnego (__eo_typeof X) ≠
                                                Term.Stuck at hApp
                                              rcases eo_typeof_bvnego_arg_bitvec_of_ne_stuck hApp with
                                                ⟨w, hArg⟩
                                              rw [hArg]
                                              intro h
                                              cases h)
                                            (fun X hXTrans hApp => by
                                              unfold RuleProofs.eo_has_smt_translation
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.bvnego (__eo_to_smt X)) ≠
                                                  SmtType.None
                                              change __eo_typeof_bvnego (__eo_typeof X) ≠
                                                Term.Stuck at hApp
                                              rcases eo_typeof_bvnego_arg_bitvec_of_ne_stuck hApp with
                                                ⟨w, hArgEo⟩
                                              rcases
                                                  smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                    hXTrans hArgEo with
                                                ⟨n, hSmtArg⟩
                                              rw [smt_typeof_bvnego_eq, hSmtArg]
                                              simp [__smtx_typeof_bv_op_1_ret])
                                            (fun hATrans hATy =>
                                              hRec
                                                (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                (by simp)
                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                      · by_cases hPurify :
                                          f = Term.UOp UserOp._at_purify
                                        · subst f
                                          exact
                                            substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                              UserOp._at_purify a xs ts bvs hXsEnv hBvsEnv hTs
                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                              hFTrans hTy
                                              (fun h => purify_arg_has_smt_translation_of_has_smt_translation h)
                                              (fun X hApp => by
                                                change __eo_typeof__at_purify (__eo_typeof X) ≠
                                                  Term.Stuck at hApp
                                                simpa [eo_typeof_purify_eq] using hApp)
                                              (fun X hXTrans hApp => by
                                                unfold RuleProofs.eo_has_smt_translation
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm._at_purify (__eo_to_smt X)) ≠
                                                    SmtType.None
                                                rw [__smtx_typeof.eq_11]
                                                simpa [RuleProofs.eo_has_smt_translation] using hXTrans)
                                              (fun hATrans hATy =>
                                                hRec
                                                  (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                  (by simp)
                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                        · by_cases hStrLen :
                                            f = Term.UOp UserOp.str_len
                                          · subst f
                                            exact
                                              substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                UserOp.str_len a xs ts bvs hXsEnv hBvsEnv hTs
                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                hFTrans hTy
                                                (fun h => str_len_arg_has_smt_translation_of_has_smt_translation h)
                                                (fun X hApp => by
                                                  change __eo_typeof_str_len (__eo_typeof X) ≠
                                                    Term.Stuck at hApp
                                                  rcases eo_typeof_str_len_arg_seq_of_ne_stuck hApp with
                                                    ⟨V, hArg⟩
                                                  rw [hArg]
                                                  intro h
                                                  cases h)
                                                (fun X hXTrans hApp => by
                                                  unfold RuleProofs.eo_has_smt_translation
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.str_len (__eo_to_smt X)) ≠
                                                      SmtType.None
                                                  change __eo_typeof_str_len (__eo_typeof X) ≠
                                                    Term.Stuck at hApp
                                                  rcases eo_typeof_str_len_arg_seq_of_ne_stuck hApp with
                                                    ⟨V, hArgEo⟩
                                                  rcases
                                                      smt_typeof_eo_to_smt_seq_of_typeof_seq
                                                        hXTrans hArgEo with
                                                    ⟨T, hSmtArg⟩
                                                  rw [typeof_str_len_eq, hSmtArg]
                                                  simp [__smtx_typeof_seq_op_1_ret])
                                                (fun hATrans hATy =>
                                                  hRec
                                                    (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                    (by simp)
                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                          · by_cases hStrRev :
                                              f = Term.UOp UserOp.str_rev
                                            · subst f
                                              exact
                                                substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                  UserOp.str_rev a xs ts bvs hXsEnv hBvsEnv hTs
                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                  hFTrans hTy
                                                  (fun h => str_rev_arg_has_smt_translation_of_has_smt_translation h)
                                                  (fun X hApp => by
                                                    change __eo_typeof_str_rev (__eo_typeof X) ≠
                                                      Term.Stuck at hApp
                                                    rcases eo_typeof_str_rev_arg_seq_of_ne_stuck hApp with
                                                      ⟨V, hArg⟩
                                                    rw [hArg]
                                                    intro h
                                                    cases h)
                                                  (fun X hXTrans hApp => by
                                                    unfold RuleProofs.eo_has_smt_translation
                                                    change
                                                      __smtx_typeof
                                                          (SmtTerm.str_rev (__eo_to_smt X)) ≠
                                                        SmtType.None
                                                    change __eo_typeof_str_rev (__eo_typeof X) ≠
                                                      Term.Stuck at hApp
                                                    rcases eo_typeof_str_rev_arg_seq_of_ne_stuck hApp with
                                                      ⟨V, hArgEo⟩
                                                    rcases
                                                        smt_typeof_eo_to_smt_seq_of_typeof_seq
                                                          hXTrans hArgEo with
                                                      ⟨T, hSmtArg⟩
                                                    rw [typeof_str_rev_eq, hSmtArg]
                                                    simp [__smtx_typeof_seq_op_1])
                                                  (fun hATrans hATy =>
                                                    hRec
                                                      (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                      (by simp)
                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                            · by_cases hStrToInt :
                                                f = Term.UOp UserOp.str_to_int
                                              · subst f
                                                exact
                                                  substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                    UserOp.str_to_int a xs ts bvs hXsEnv hBvsEnv hTs
                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                    hFTrans hTy
                                                    (fun h => str_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                    (fun X hApp => by
                                                      change __eo_typeof_str_to_code (__eo_typeof X) ≠
                                                        Term.Stuck at hApp
                                                      rw [eo_typeof_str_to_code_arg_seq_char_of_ne_stuck hApp]
                                                      intro h
                                                      cases h)
                                                    (fun X hXTrans hApp => by
                                                      unfold RuleProofs.eo_has_smt_translation
                                                      change
                                                        __smtx_typeof
                                                            (SmtTerm.str_to_int (__eo_to_smt X)) ≠
                                                          SmtType.None
                                                      change __eo_typeof_str_to_code (__eo_typeof X) ≠
                                                        Term.Stuck at hApp
                                                      have hArgEo :=
                                                        eo_typeof_str_to_code_arg_seq_char_of_ne_stuck hApp
                                                      have hSmtArg :=
                                                        smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                          hXTrans hArgEo
                                                      rw [typeof_str_to_int_eq, hSmtArg]
                                                      simp [native_ite, native_Teq])
                                                    (fun hATrans hATy =>
                                                      hRec
                                                        (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                        (by simp)
                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                              · by_cases hStrToRe :
                                                  f = Term.UOp UserOp.str_to_re
                                                · subst f
                                                  exact
                                                    substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                      UserOp.str_to_re a xs ts bvs hXsEnv hBvsEnv hTs
                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                      hFTrans hTy
                                                      (fun h => str_to_re_arg_has_smt_translation_of_has_smt_translation h)
                                                      (fun X hApp => by
                                                        change __eo_typeof_str_to_re (__eo_typeof X) ≠
                                                          Term.Stuck at hApp
                                                        rw [eo_typeof_str_to_re_arg_seq_char_of_ne_stuck hApp]
                                                        intro h
                                                        cases h)
                                                      (fun X hXTrans hApp => by
                                                        unfold RuleProofs.eo_has_smt_translation
                                                        change
                                                          __smtx_typeof
                                                              (SmtTerm.str_to_re (__eo_to_smt X)) ≠
                                                            SmtType.None
                                                        change __eo_typeof_str_to_re (__eo_typeof X) ≠
                                                          Term.Stuck at hApp
                                                        have hArgEo :=
                                                          eo_typeof_str_to_re_arg_seq_char_of_ne_stuck hApp
                                                        have hSmtArg :=
                                                          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                            hXTrans hArgEo
                                                        rw [typeof_str_to_re_eq, hSmtArg]
                                                        simp [native_ite, native_Teq])
                                                      (fun hATrans hATy =>
                                                        hRec
                                                          (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                          (by simp)
                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                · by_cases hReMult :
                                                    f = Term.UOp UserOp.re_mult
                                                  · subst f
                                                    exact
                                                      substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                        UserOp.re_mult a xs ts bvs hXsEnv hBvsEnv hTs
                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                        hFTrans hTy
                                                        (fun h => re_mult_arg_has_smt_translation_of_has_smt_translation h)
                                                        (fun X hApp => by
                                                          change __eo_typeof_re_mult (__eo_typeof X) ≠
                                                            Term.Stuck at hApp
                                                          rw [eo_typeof_re_mult_arg_reglan_of_ne_stuck hApp]
                                                          intro h
                                                          cases h)
                                                        (fun X hXTrans hApp => by
                                                          unfold RuleProofs.eo_has_smt_translation
                                                          change
                                                            __smtx_typeof
                                                                (SmtTerm.re_mult (__eo_to_smt X)) ≠
                                                              SmtType.None
                                                          change __eo_typeof_re_mult (__eo_typeof X) ≠
                                                            Term.Stuck at hApp
                                                          have hArgEo :=
                                                            eo_typeof_re_mult_arg_reglan_of_ne_stuck hApp
                                                          have hSmtArg :=
                                                            smt_typeof_eo_to_smt_reglan_of_typeof_reglan
                                                              hXTrans hArgEo
                                                          rw [typeof_re_mult_eq, hSmtArg]
                                                          simp [native_ite, native_Teq])
                                                        (fun hATrans hATy =>
                                                          hRec
                                                            (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                            (by simp)
                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                  · by_cases hStrToLower :
                                                      f = Term.UOp UserOp.str_to_lower
                                                    · subst f
                                                      exact
                                                        substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                          UserOp.str_to_lower a xs ts bvs hXsEnv hBvsEnv hTs
                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                          hFTrans hTy
                                                          (fun h => str_to_lower_arg_has_smt_translation_of_has_smt_translation h)
                                                          (fun X hApp => by
                                                            change __eo_typeof_str_to_lower (__eo_typeof X) ≠
                                                              Term.Stuck at hApp
                                                            rw [eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck hApp]
                                                            intro h
                                                            cases h)
                                                          (fun X hXTrans hApp => by
                                                            unfold RuleProofs.eo_has_smt_translation
                                                            change
                                                              __smtx_typeof
                                                                  (SmtTerm.str_to_lower (__eo_to_smt X)) ≠
                                                                SmtType.None
                                                            change __eo_typeof_str_to_lower (__eo_typeof X) ≠
                                                              Term.Stuck at hApp
                                                            have hArgEo :=
                                                              eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck hApp
                                                            have hSmtArg :=
                                                              smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                hXTrans hArgEo
                                                            rw [typeof_str_to_lower_eq, hSmtArg]
                                                            simp [native_ite, native_Teq])
                                                          (fun hATrans hATy =>
                                                            hRec
                                                              (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                              (by simp)
                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                    · by_cases hStrToUpper :
                                                        f = Term.UOp UserOp.str_to_upper
                                                      · subst f
                                                        exact
                                                          substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                            UserOp.str_to_upper a xs ts bvs hXsEnv hBvsEnv hTs
                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                            hFTrans hTy
                                                            (fun h => str_to_upper_arg_has_smt_translation_of_has_smt_translation h)
                                                            (fun X hApp => by
                                                              change __eo_typeof_str_to_lower (__eo_typeof X) ≠
                                                                Term.Stuck at hApp
                                                              rw [eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck hApp]
                                                              intro h
                                                              cases h)
                                                            (fun X hXTrans hApp => by
                                                              unfold RuleProofs.eo_has_smt_translation
                                                              change
                                                                __smtx_typeof
                                                                    (SmtTerm.str_to_upper (__eo_to_smt X)) ≠
                                                                  SmtType.None
                                                              change __eo_typeof_str_to_lower (__eo_typeof X) ≠
                                                                Term.Stuck at hApp
                                                              have hArgEo :=
                                                                eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck hApp
                                                              have hSmtArg :=
                                                                smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                  hXTrans hArgEo
                                                              rw [typeof_str_to_upper_eq, hSmtArg]
                                                              simp [native_ite, native_Teq])
                                                            (fun hATrans hATy =>
                                                              hRec
                                                                (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                (by simp)
                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                      · by_cases hStrToCode :
                                                          f = Term.UOp UserOp.str_to_code
                                                        · subst f
                                                          exact
                                                            substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                              UserOp.str_to_code a xs ts bvs hXsEnv hBvsEnv hTs
                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                              hFTrans hTy
                                                              (fun h => str_to_code_arg_has_smt_translation_of_has_smt_translation h)
                                                              (fun X hApp => by
                                                                change __eo_typeof_str_to_code (__eo_typeof X) ≠
                                                                  Term.Stuck at hApp
                                                                rw [eo_typeof_str_to_code_arg_seq_char_of_ne_stuck hApp]
                                                                intro h
                                                                cases h)
                                                              (fun X hXTrans hApp => by
                                                                unfold RuleProofs.eo_has_smt_translation
                                                                change
                                                                  __smtx_typeof
                                                                      (SmtTerm.str_to_code (__eo_to_smt X)) ≠
                                                                    SmtType.None
                                                                change __eo_typeof_str_to_code (__eo_typeof X) ≠
                                                                  Term.Stuck at hApp
                                                                have hArgEo :=
                                                                  eo_typeof_str_to_code_arg_seq_char_of_ne_stuck hApp
                                                                have hSmtArg :=
                                                                  smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                    hXTrans hArgEo
                                                                rw [typeof_str_to_code_eq, hSmtArg]
                                                                simp [native_ite, native_Teq])
                                                              (fun hATrans hATy =>
                                                                hRec
                                                                  (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                  (by simp)
                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                        · by_cases hStrFromCode :
                                                            f = Term.UOp UserOp.str_from_code
                                                          · subst f
                                                            exact
                                                              substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                                UserOp.str_from_code a xs ts bvs hXsEnv hBvsEnv hTs
                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                hFTrans hTy
                                                                (fun h => str_from_code_arg_has_smt_translation_of_has_smt_translation h)
                                                                (fun X hApp => by
                                                                  change __eo_typeof_str_from_code (__eo_typeof X) ≠
                                                                    Term.Stuck at hApp
                                                                  rw [eo_typeof_str_from_code_arg_int_of_ne_stuck hApp]
                                                                  intro h
                                                                  cases h)
                                                                (fun X hXTrans hApp => by
                                                                  unfold RuleProofs.eo_has_smt_translation
                                                                  change
                                                                    __smtx_typeof
                                                                        (SmtTerm.str_from_code (__eo_to_smt X)) ≠
                                                                      SmtType.None
                                                                  change __eo_typeof_str_from_code (__eo_typeof X) ≠
                                                                    Term.Stuck at hApp
                                                                  have hArgEo :=
                                                                    eo_typeof_str_from_code_arg_int_of_ne_stuck hApp
                                                                  have hSmtArg :=
                                                                    smt_typeof_eo_to_smt_int_of_typeof_int
                                                                      hXTrans hArgEo
                                                                  rw [typeof_str_from_code_eq, hSmtArg]
                                                                  simp [native_ite, native_Teq])
                                                                (fun hATrans hATy =>
                                                                  hRec
                                                                    (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                    (by simp)
                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                          · by_cases hStrIsDigit :
                                                              f = Term.UOp UserOp.str_is_digit
                                                            · subst f
                                                              exact
                                                                substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                                  UserOp.str_is_digit a xs ts bvs hXsEnv hBvsEnv hTs
                                                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                  hFTrans hTy
                                                                  (fun h => str_is_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                                  (fun X hApp => by
                                                                    change __eo_typeof_str_is_digit (__eo_typeof X) ≠
                                                                      Term.Stuck at hApp
                                                                    rw [eo_typeof_str_is_digit_arg_seq_char_of_ne_stuck hApp]
                                                                    intro h
                                                                    cases h)
                                                                  (fun X hXTrans hApp => by
                                                                    unfold RuleProofs.eo_has_smt_translation
                                                                    change
                                                                      __smtx_typeof
                                                                          (SmtTerm.str_is_digit (__eo_to_smt X)) ≠
                                                                        SmtType.None
                                                                    change __eo_typeof_str_is_digit (__eo_typeof X) ≠
                                                                      Term.Stuck at hApp
                                                                    have hArgEo :=
                                                                      eo_typeof_str_is_digit_arg_seq_char_of_ne_stuck hApp
                                                                    have hSmtArg :=
                                                                      smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                        hXTrans hArgEo
                                                                    rw [typeof_str_is_digit_eq, hSmtArg]
                                                                    simp [native_ite, native_Teq])
                                                                  (fun hATrans hATy =>
                                                                    hRec
                                                                      (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                      (by simp)
                                                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                            · by_cases hStrFromInt :
                                                                f = Term.UOp UserOp.str_from_int
                                                              · subst f
                                                                exact
                                                                  substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                                    UserOp.str_from_int a xs ts bvs hXsEnv hBvsEnv hTs
                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                    hFTrans hTy
                                                                    (fun h => str_from_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                    (fun X hApp => by
                                                                      change __eo_typeof_str_from_code (__eo_typeof X) ≠
                                                                        Term.Stuck at hApp
                                                                      rw [eo_typeof_str_from_code_arg_int_of_ne_stuck hApp]
                                                                      intro h
                                                                      cases h)
                                                                    (fun X hXTrans hApp => by
                                                                      unfold RuleProofs.eo_has_smt_translation
                                                                      change
                                                                        __smtx_typeof
                                                                            (SmtTerm.str_from_int (__eo_to_smt X)) ≠
                                                                          SmtType.None
                                                                      change __eo_typeof_str_from_code (__eo_typeof X) ≠
                                                                        Term.Stuck at hApp
                                                                      have hArgEo :=
                                                                        eo_typeof_str_from_code_arg_int_of_ne_stuck hApp
                                                                      have hSmtArg :=
                                                                        smt_typeof_eo_to_smt_int_of_typeof_int
                                                                          hXTrans hArgEo
                                                                      rw [typeof_str_from_int_eq, hSmtArg]
                                                                      simp [native_ite, native_Teq])
                                                                    (fun hATrans hATy =>
                                                                      hRec
                                                                        (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                        (by simp)
                                                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                              · by_cases hRePlus :
                                                                  f = Term.UOp UserOp.re_plus
                                                                · subst f
                                                                  exact
                                                                    substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                                      UserOp.re_plus a xs ts bvs hXsEnv hBvsEnv hTs
                                                                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                      hFTrans hTy
                                                                      (fun h => re_plus_arg_has_smt_translation_of_has_smt_translation h)
                                                                      (fun X hApp => by
                                                                        change __eo_typeof_re_mult (__eo_typeof X) ≠
                                                                          Term.Stuck at hApp
                                                                        rw [eo_typeof_re_mult_arg_reglan_of_ne_stuck hApp]
                                                                        intro h
                                                                        cases h)
                                                                      (fun X hXTrans hApp => by
                                                                        unfold RuleProofs.eo_has_smt_translation
                                                                        change
                                                                          __smtx_typeof
                                                                              (SmtTerm.re_plus (__eo_to_smt X)) ≠
                                                                            SmtType.None
                                                                        change __eo_typeof_re_mult (__eo_typeof X) ≠
                                                                          Term.Stuck at hApp
                                                                        have hArgEo :=
                                                                          eo_typeof_re_mult_arg_reglan_of_ne_stuck hApp
                                                                        have hSmtArg :=
                                                                          smt_typeof_eo_to_smt_reglan_of_typeof_reglan
                                                                            hXTrans hArgEo
                                                                        rw [typeof_re_plus_eq, hSmtArg]
                                                                        simp [native_ite, native_Teq])
                                                                      (fun hATrans hATy =>
                                                                        hRec
                                                                          (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                          (by simp)
                                                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                · by_cases hReOpt :
                                                                    f = Term.UOp UserOp.re_opt
                                                                  · subst f
                                                                    exact
                                                                      substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                                        UserOp.re_opt a xs ts bvs hXsEnv hBvsEnv hTs
                                                                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                        hFTrans hTy
                                                                        (fun h => re_opt_arg_has_smt_translation_of_has_smt_translation h)
                                                                        (fun X hApp => by
                                                                          change __eo_typeof_re_mult (__eo_typeof X) ≠
                                                                            Term.Stuck at hApp
                                                                          rw [eo_typeof_re_mult_arg_reglan_of_ne_stuck hApp]
                                                                          intro h
                                                                          cases h)
                                                                        (fun X hXTrans hApp => by
                                                                          unfold RuleProofs.eo_has_smt_translation
                                                                          change
                                                                            __smtx_typeof
                                                                                (SmtTerm.re_opt (__eo_to_smt X)) ≠
                                                                              SmtType.None
                                                                          change __eo_typeof_re_mult (__eo_typeof X) ≠
                                                                            Term.Stuck at hApp
                                                                          have hArgEo :=
                                                                            eo_typeof_re_mult_arg_reglan_of_ne_stuck hApp
                                                                          have hSmtArg :=
                                                                            smt_typeof_eo_to_smt_reglan_of_typeof_reglan
                                                                              hXTrans hArgEo
                                                                          rw [typeof_re_opt_eq, hSmtArg]
                                                                          simp [native_ite, native_Teq])
                                                                        (fun hATrans hATy =>
                                                                          hRec
                                                                            (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                            (by simp)
                                                                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                  · by_cases hReComp :
                                                                      f = Term.UOp UserOp.re_comp
                                                                    · subst f
                                                                      exact
                                                                        substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                                          UserOp.re_comp a xs ts bvs hXsEnv hBvsEnv hTs
                                                                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                          hFTrans hTy
                                                                          (fun h => re_comp_arg_has_smt_translation_of_has_smt_translation h)
                                                                          (fun X hApp => by
                                                                            change __eo_typeof_re_mult (__eo_typeof X) ≠
                                                                              Term.Stuck at hApp
                                                                            rw [eo_typeof_re_mult_arg_reglan_of_ne_stuck hApp]
                                                                            intro h
                                                                            cases h)
                                                                          (fun X hXTrans hApp => by
                                                                            unfold RuleProofs.eo_has_smt_translation
                                                                            change
                                                                              __smtx_typeof
                                                                                  (SmtTerm.re_comp (__eo_to_smt X)) ≠
                                                                                SmtType.None
                                                                            change __eo_typeof_re_mult (__eo_typeof X) ≠
                                                                              Term.Stuck at hApp
                                                                            have hArgEo :=
                                                                              eo_typeof_re_mult_arg_reglan_of_ne_stuck hApp
                                                                            have hSmtArg :=
                                                                              smt_typeof_eo_to_smt_reglan_of_typeof_reglan
                                                                                hXTrans hArgEo
                                                                            rw [typeof_re_comp_eq, hSmtArg]
                                                                            simp [native_ite, native_Teq])
                                                                          (fun hATrans hATy =>
                                                                            hRec
                                                                              (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                              (by simp)
                                                                              hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                    · by_cases hUbvToInt :
                                                                        f = Term.UOp UserOp.ubv_to_int
                                                                      · subst f
                                                                        exact
                                                                          substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                                            UserOp.ubv_to_int a xs ts bvs hXsEnv hBvsEnv hTs
                                                                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                            hFTrans hTy
                                                                            (fun h => ubv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                            (fun X hApp => by
                                                                              change __eo_typeof__at_bvsize (__eo_typeof X) ≠
                                                                                Term.Stuck at hApp
                                                                              rcases eo_typeof_bvsize_arg_bitvec_of_ne_stuck hApp with
                                                                                ⟨w, hArg⟩
                                                                              rw [hArg]
                                                                              intro h
                                                                              cases h)
                                                                            (fun X hXTrans hApp => by
                                                                              unfold RuleProofs.eo_has_smt_translation
                                                                              change
                                                                                __smtx_typeof
                                                                                    (SmtTerm.ubv_to_int (__eo_to_smt X)) ≠
                                                                                  SmtType.None
                                                                              change __eo_typeof__at_bvsize (__eo_typeof X) ≠
                                                                                Term.Stuck at hApp
                                                                              rcases eo_typeof_bvsize_arg_bitvec_of_ne_stuck hApp with
                                                                                ⟨w, hArgEo⟩
                                                                              rcases
                                                                                  smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                                    hXTrans hArgEo with
                                                                                ⟨n, hSmtArg⟩
                                                                              rw [smt_typeof_ubv_to_int_eq, hSmtArg]
                                                                              simp [__smtx_typeof_bv_op_1_ret])
                                                                            (fun hATrans hATy =>
                                                                              hRec
                                                                                (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                                (by simp)
                                                                                hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                      · by_cases hSbvToInt :
                                                                          f = Term.UOp UserOp.sbv_to_int
                                                                        · subst f
                                                                          exact
                                                                            substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                                              UserOp.sbv_to_int a xs ts bvs hXsEnv hBvsEnv hTs
                                                                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                              hFTrans hTy
                                                                              (fun h => sbv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                              (fun X hApp => by
                                                                                change __eo_typeof__at_bvsize (__eo_typeof X) ≠
                                                                                  Term.Stuck at hApp
                                                                                rcases eo_typeof_bvsize_arg_bitvec_of_ne_stuck hApp with
                                                                                  ⟨w, hArg⟩
                                                                                rw [hArg]
                                                                                intro h
                                                                                cases h)
                                                                              (fun X hXTrans hApp => by
                                                                                unfold RuleProofs.eo_has_smt_translation
                                                                                change
                                                                                  __smtx_typeof
                                                                                      (SmtTerm.sbv_to_int (__eo_to_smt X)) ≠
                                                                                    SmtType.None
                                                                                change __eo_typeof__at_bvsize (__eo_typeof X) ≠
                                                                                  Term.Stuck at hApp
                                                                                rcases eo_typeof_bvsize_arg_bitvec_of_ne_stuck hApp with
                                                                                  ⟨w, hArgEo⟩
                                                                                rcases
                                                                                    smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                                      hXTrans hArgEo with
                                                                                  ⟨n, hSmtArg⟩
                                                                                rw [smt_typeof_sbv_to_int_eq, hSmtArg]
                                                                                simp [__smtx_typeof_bv_op_1_ret])
                                                                              (fun hATrans hATy =>
                                                                                hRec
                                                                                  (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                                  (by simp)
                                                                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                        · by_cases hStringsStoiNonDigit :
                                                                            f = Term.UOp UserOp._at_strings_stoi_non_digit
                                                                          · subst f
                                                                            exact
                                                                              substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                                                                                UserOp._at_strings_stoi_non_digit a xs ts bvs hXsEnv hBvsEnv hTs
                                                                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                hFTrans hTy
                                                                                (fun h => strings_stoi_non_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                                                (fun X hApp => by
                                                                                  change __eo_typeof_str_to_code (__eo_typeof X) ≠
                                                                                    Term.Stuck at hApp
                                                                                  rw [eo_typeof_str_to_code_arg_seq_char_of_ne_stuck hApp]
                                                                                  intro h
                                                                                  cases h)
                                                                                (fun X hXTrans hApp => by
                                                                                  unfold RuleProofs.eo_has_smt_translation
                                                                                  change
                                                                                    __smtx_typeof
                                                                                        (SmtTerm.str_indexof_re (__eo_to_smt X)
                                                                                          (SmtTerm.re_comp
                                                                                            (SmtTerm.re_range
                                                                                              (SmtTerm.String (native_string_lit "0"))
                                                                                              (SmtTerm.String (native_string_lit "9"))))
                                                                                          (SmtTerm.Numeral 0)) ≠
                                                                                      SmtType.None
                                                                                  change __eo_typeof_str_to_code (__eo_typeof X) ≠
                                                                                    Term.Stuck at hApp
                                                                                  have hArgEo :=
                                                                                    eo_typeof_str_to_code_arg_seq_char_of_ne_stuck hApp
                                                                                  have hSmtArg :=
                                                                                    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                                      hXTrans hArgEo
                                                                                  have hZeroCharTy :
                                                                                      __smtx_typeof
                                                                                          (SmtTerm.String (native_string_lit "0")) =
                                                                                        SmtType.Seq SmtType.Char := by
                                                                                    rw [__smtx_typeof.eq_4]
                                                                                    simp [native_string_lit, native_string_valid,
                                                                                      native_char_valid, native_ite]
                                                                                  have hNineCharTy :
                                                                                      __smtx_typeof
                                                                                          (SmtTerm.String (native_string_lit "9")) =
                                                                                        SmtType.Seq SmtType.Char := by
                                                                                    rw [__smtx_typeof.eq_4]
                                                                                    simp [native_string_lit, native_string_valid,
                                                                                      native_char_valid, native_ite]
                                                                                  rw [typeof_str_indexof_re_eq, typeof_re_comp_eq,
                                                                                    typeof_re_range_eq, hSmtArg,
                                                                                    hZeroCharTy, hNineCharTy,
                                                                                    __smtx_typeof.eq_2]
                                                                                  simp [native_ite, native_Teq])
                                                                                (fun hATrans hATy =>
                                                                                  hRec
                                                                                    (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                                                                    (by simp)
                                                                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                                                          · sorry
      case Var name S =>
          exact
            substitute_simul_var_any_has_smt_translation_of_typeof_ne_stuck
              name S xs ts bvs hXsEnv hBvsEnv hFTrans hTs hTy
      case Stuck =>
          exact False.elim
            ((RuleProofs.term_ne_stuck_of_has_smt_translation Term.Stuck hFTrans) rfl)
      all_goals
        exact
          substitute_simul_atom_has_smt_translation_of_typeof_ne_stuck
            _ xs ts bvs hXsEnv hBvsEnv hTs
            (by intro f a h; cases h)
            (by intro s S h; cases h)
            (by intro h; cases h)
            hFTrans hTy

/-- General substitution-result translatability, under an arbitrary
bound-variable accumulator. -/
theorem substitute_simul_has_smt_translation_of_typeof_ne_stuck
    (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts bvs) ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ts bvs) :=
  substitute_simul_has_smt_translation_of_typeof_ne_stuck_lt
    (sizeOf F + 1) F xs ts bvs (by omega)
    hXsEnv hBvsEnv hFTrans hTs hActuals hTy

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
    (hActuals : SubstActualsHaveSmtTypes xs ts)
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
  cases F with
  | Apply f a =>
      exact
        substitute_simul_has_smt_translation_of_typeof_ne_stuck
          (Term.Apply f a) xs ts Term.__eo_List_nil
          (EoVarEnvPerm.of_exact hXsEnv)
          (EoVarEnvPerm.of_exact EoVarEnv.nil)
          hBodyTrans hTs hActuals
          (by
            intro hStuck
            rw [hStuck] at hTy
            cases hTy)
  | Var name S =>
      exact
        substitute_simul_var_any_has_smt_translation_of_typeof_bool
          name S xs ts Term.__eo_List_nil
          (EoVarEnvPerm.of_exact hXsEnv)
          (EoVarEnvPerm.of_exact EoVarEnv.nil)
          hBodyTrans hTs hTy
  | Stuck =>
      exact False.elim
        ((RuleProofs.term_ne_stuck_of_has_smt_translation Term.Stuck hBodyTrans) rfl)
  | UOp op =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.UOp op) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | UOp1 op x =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.UOp1 op x) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | UOp2 op x y =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.UOp2 op x y) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | UOp3 op x y z =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.UOp3 op x y z) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | __eo_List =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          Term.__eo_List xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | __eo_List_nil =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          Term.__eo_List_nil xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | __eo_List_cons =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          Term.__eo_List_cons xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | Bool =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          Term.Bool xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | Boolean b =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.Boolean b) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | Numeral n =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.Numeral n) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | Rational r =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.Rational r) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | String s =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.String s) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | Binary w n =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.Binary w n) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | «Type» =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          Term.Type xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | FunType =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          Term.FunType xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | DatatypeType s d =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.DatatypeType s d) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | DatatypeTypeRef s =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.DatatypeTypeRef s) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | DtcAppType T U =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.DtcAppType T U) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | DtCons s d i =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.DtCons s d i) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | DtSel s d i j =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.DtSel s d i j) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | USort i =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.USort i) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy
  | UConst i T =>
      exact
        substitute_simul_atom_has_smt_translation_of_typeof_bool_nil
          (Term.UConst i T) xs ts
          (EoVarEnvPerm.of_exact hXsEnv) hTs
          (by intro f a h; cases h)
          (by intro s S h; cases h)
          (by intro h; cases h)
          hBodyTrans hTy

/--
Typing preservation for the instantiate substitution result, packaged as SMT
Boolean-typedness.
-/
theorem substitute_simul_has_bool_type_of_typeof_bool
    (F xs ts : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
        Term.Bool) :
    RuleProofs.eo_has_bool_type
      (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) :=
  RuleProofs.eo_typeof_bool_implies_has_bool_type
    (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)
    (substitute_simul_has_smt_translation_of_typeof_bool F xs ts
      hForall hTs hActuals hTy)
    hTy

/-- Different-body congruence for the existential evaluator: if for every
witness value the two (distinct) bodies evaluate equally in the pushed models,
then the existentials evaluate equally. Generalises
`native_eval_texists_eq_of_body_eval_eq` (same body) and is what the
substitution case needs (`toSmt (subst a)` vs `toSmt a`). -/
theorem native_eval_texists_eq_of_body_eval_eq_diff
    {M N : SmtModel} {s : native_String} {T : SmtType} {bodyM bodyN : SmtTerm}
    (hBody : ∀ v : SmtValue,
      __smtx_model_eval (native_model_push M s T v) bodyM =
        __smtx_model_eval (native_model_push N s T v) bodyN) :
    native_eval_texists M s T bodyM = native_eval_texists N s T bodyN := by
  classical
  let PM : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) bodyM = SmtValue.Boolean true
  let PN : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push N s T v) bodyN = SmtValue.Boolean true
  change (if _ : PM then SmtValue.Boolean true else SmtValue.Boolean false) =
    (if _ : PN then SmtValue.Boolean true else SmtValue.Boolean false)
  have hIff : PM ↔ PN := by
    constructor
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [hBody v] using hEval⟩
    · intro h
      rcases h with ⟨v, hTy, hCanon, hEval⟩
      exact ⟨v, hTy, hCanon, by simpa [← hBody v] using hEval⟩
  by_cases hM : PM
  · have hN : PN := hIff.mp hM
    simp [hM, hN]
  · have hN : ¬ PN := fun h => hM (hIff.mpr h)
    simp [hM, hN]

/-- Reusable reduction for a **unary special-head application** in the
substitution-evaluation induction. Given that the head's substitution is the
bare operator (`hHeadSub`, from `substitute_simul_rec_uop_eq_self`), argument
translatability extraction (`hArgExtract`), the SMT constructor's evaluation
congruence (`hCong`), and the argument IH provider (`hRecArg`), the whole
application reduces to the argument IH. Each concrete unary head (`not`,
`to_real`, …) instantiates this with its constructor and arg-extraction lemma. -/
theorem substFalse_eval_unary_op
    (op : UserOp) (a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean false : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFTrans : eoHasSmtTranslation (Term.Apply (Term.UOp op) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {t : Term},
        eoHasSmtTranslation (Term.Apply (Term.UOp op) t) → eoHasSmtTranslation t)
    (hCong :
      ∀ X Y : Term,
        __smtx_model_eval M (__eo_to_smt X) = __smtx_model_eval N (__eo_to_smt Y) →
          __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.UOp op) X)) =
            __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) Y)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.UOp op) a) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Apply (Term.UOp op) a)) := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.UOp op) a xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hApplyEq
  have hMkNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNeStuck
  have hATrans : eoHasSmtTranslation a := hArgExtract hFTrans
  have hSubstApplyTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) := by
    rw [← hMk, ← hSubstEq]; exact hSubstTrans
  have hSubstATrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) :=
    hArgExtract hSubstApplyTrans
  rw [hSubstEq, hMk]
  exact hCong _ _ (hRecArg hATrans hSubstATrans)

/-- Reusable reduction for a **binary special-head application**
`(Apply (Apply (UOp op) x1) a)` in the substitution-evaluation induction.
Analogous to `substFalse_eval_unary_op`, but recurses on both subterms. -/
theorem substFalse_eval_binary_op
    (op : UserOp) (x1 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean false : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x1) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {s t : Term},
        eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) s) t) →
          eoHasSmtTranslation s ∧ eoHasSmtTranslation t)
    (hCong :
      ∀ X1 Y1 X2 Y2 : Term,
        __smtx_model_eval M (__eo_to_smt X1) = __smtx_model_eval N (__eo_to_smt Y1) →
        __smtx_model_eval M (__eo_to_smt X2) = __smtx_model_eval N (__eo_to_smt Y2) →
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) X1) X2)) =
            __smtx_model_eval N
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) Y1) Y2)))
    (hRecArg1 :
      eoHasSmtTranslation x1 →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x1))
    (hRecArg2 :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) a)) := by
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.UOp op) x1 xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.Apply (Term.UOp op) x1) a xs ss bvs hisr hxs hss hbvs
        hNotBinderOuter
    rw [hEq, hSubstHead]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by rw [← hInnerMk]; exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hArgsTrans := hArgExtract hFTrans
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) := by
    rw [← hResultEq]; exact hSubstTrans
  have hSubstArgsTrans := hArgExtract hSubstAppTrans
  rw [hResultEq]
  exact hCong _ _ _ _
    (hRecArg1 hArgsTrans.1 hSubstArgsTrans.1)
    (hRecArg2 hArgsTrans.2 hSubstArgsTrans.2)

theorem substFalse_eval_binary_op_with_app_trans
    (op : UserOp) (x1 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean false : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x1) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {s t : Term},
        eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) s) t) →
          eoHasSmtTranslation s ∧ eoHasSmtTranslation t)
    (hCong :
      ∀ X1 Y1 X2 Y2 : Term,
        eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) X1) X2) →
        eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) Y1) Y2) →
        __smtx_model_eval M (__eo_to_smt X1) = __smtx_model_eval N (__eo_to_smt Y1) →
        __smtx_model_eval M (__eo_to_smt X2) = __smtx_model_eval N (__eo_to_smt Y2) →
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) X1) X2)) =
            __smtx_model_eval N
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) Y1) Y2)))
    (hRecArg1 :
      eoHasSmtTranslation x1 →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x1))
    (hRecArg2 :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) a)) := by
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.UOp op) x1 xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.Apply (Term.UOp op) x1) a xs ss bvs hisr hxs hss hbvs
        hNotBinderOuter
    rw [hEq, hSubstHead]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠ Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by rw [← hInnerMk]; exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x1) a) xs ss bvs =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hOuterMk]
  have hArgsTrans := hArgExtract hFTrans
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) := by
    rw [← hResultEq]; exact hSubstTrans
  have hSubstArgsTrans := hArgExtract hSubstAppTrans
  rw [hResultEq]
  exact hCong _ _ _ _ hSubstAppTrans hFTrans
    (hRecArg1 hArgsTrans.1 hSubstArgsTrans.1)
    (hRecArg2 hArgsTrans.2 hSubstArgsTrans.2)

/-- Reusable reduction for a **ternary special-head application**
`(Apply (Apply (Apply (UOp op) x1) x2) a)` in the substitution-evaluation
induction. -/
theorem substFalse_eval_ternary_op
    (op : UserOp) (x1 x2 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean false : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.UOp op) x1) x2 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hArgExtract :
      ∀ {r s t : Term},
        eoHasSmtTranslation
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) r) s) t) →
          eoHasSmtTranslation r ∧ eoHasSmtTranslation s ∧
            eoHasSmtTranslation t)
    (hCong :
      ∀ X1 Y1 X2 Y2 X3 Y3 : Term,
        __smtx_model_eval M (__eo_to_smt X1) =
          __smtx_model_eval N (__eo_to_smt Y1) →
        __smtx_model_eval M (__eo_to_smt X2) =
          __smtx_model_eval N (__eo_to_smt Y2) →
        __smtx_model_eval M (__eo_to_smt X3) =
          __smtx_model_eval N (__eo_to_smt Y3) →
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) X1) X2) X3)) =
            __smtx_model_eval N
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) Y1) Y2) Y3)))
    (hRecArg1 :
      eoHasSmtTranslation x1 →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x1))
    (hRecArg2 :
      eoHasSmtTranslation x2 →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt x2))
    (hRecArg3 :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)) := by
  have hArgsTrans := hArgExtract hFTrans
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.UOp op) x1 xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hNotBinderMiddle :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    exact term_not_eo_list_cons_of_has_smt_translation hArgsTrans.1 v vs rfl
  have hSubstMid :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.Apply (Term.UOp op) x1) x2 xs ss bvs hisr hxs hss hbvs
        hNotBinderMiddle
    rw [hEq, hSubstHead]
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstMid]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMidNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMidNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hMidMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hMidNeStuck)
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hMidMk, ← hInnerMk]
      exact hOuterNeStuck)
  have hResultEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hMidMk, hOuterMk]
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) := by
    rw [← hResultEq]; exact hSubstTrans
  have hSubstArgsTrans := hArgExtract hSubstAppTrans
  rw [hResultEq]
  exact hCong _ _ _ _ _ _
    (hRecArg1 hArgsTrans.1 hSubstArgsTrans.1)
    (hRecArg2 hArgsTrans.2.1 hSubstArgsTrans.2.1)
    (hRecArg3 hArgsTrans.2.2 hSubstArgsTrans.2.2)

theorem smtx_model_eval_apply_cross_eq_of_eval_eq
    {M N : SmtModel} (hGlobals : model_agrees_on_globals M N)
    {F F' X X' : SmtTerm}
    (hEvalF : generic_apply_eval F X)
    (hEvalF' : generic_apply_eval F' X')
    (hF :
      __smtx_model_eval M F =
        __smtx_model_eval N F')
    (hX :
      __smtx_model_eval M X =
        __smtx_model_eval N X') :
    __smtx_model_eval M (SmtTerm.Apply F X) =
      __smtx_model_eval N (SmtTerm.Apply F' X') := by
  unfold generic_apply_eval at hEvalF hEvalF'
  rw [hEvalF M, hEvalF' N, hF, hX]
  exact smtx_model_eval_apply_eq_of_globals hGlobals _ _

theorem eo_to_smt_apply_apply_apply_uop_generic_of_not_smt_triop
    {op : UserOp} {x y z : Term}
    (hIte : op ≠ UserOp.ite)
    (hStore : op ≠ UserOp.store)
    (hBvite : op ≠ UserOp.bvite)
    (hStrSubstr : op ≠ UserOp.str_substr)
    (hStrIndexof : op ≠ UserOp.str_indexof)
    (hStrUpdate : op ≠ UserOp.str_update)
    (hStrReplace : op ≠ UserOp.str_replace)
    (hStrReplaceAll : op ≠ UserOp.str_replace_all)
    (hStrReplaceRe : op ≠ UserOp.str_replace_re)
    (hStrReplaceReAll : op ≠ UserOp.str_replace_re_all)
    (hStrIndexofRe : op ≠ UserOp.str_indexof_re)
    (hStrIndexofReSplit : op ≠ UserOp.str_indexof_re_split) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) =
      SmtTerm.Apply
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y))
        (__eo_to_smt z) := by
  cases op <;> try rfl
  case ite => exact False.elim (hIte rfl)
  case store => exact False.elim (hStore rfl)
  case bvite => exact False.elim (hBvite rfl)
  case str_substr => exact False.elim (hStrSubstr rfl)
  case str_indexof => exact False.elim (hStrIndexof rfl)
  case str_update => exact False.elim (hStrUpdate rfl)
  case str_replace => exact False.elim (hStrReplace rfl)
  case str_replace_all => exact False.elim (hStrReplaceAll rfl)
  case str_replace_re => exact False.elim (hStrReplaceRe rfl)
  case str_replace_re_all => exact False.elim (hStrReplaceReAll rfl)
  case str_indexof_re => exact False.elim (hStrIndexofRe rfl)
  case str_indexof_re_split => exact False.elim (hStrIndexofReSplit rfl)

theorem substFalse_eval_ternary_uop_generic_apply
    (op : UserOp) (x1 x2 a xs ss bvs : Term) {M N : SmtModel}
    (hisr : (Term.Boolean false : Term) ≠ Term.Stuck)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.UOp op) x1) x2 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hOrigTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a) =
        SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2))
          (__eo_to_smt a))
    (hSubstTranslate :
      __eo_to_smt
          (Term.Apply
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
              (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) =
        SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
              (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs)))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)))
    (hFTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a))
    (hSubstTrans :
      eoHasSmtTranslation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs))
    (hHeadSub :
      __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ss bvs =
        Term.UOp op)
    (hGlobals : model_agrees_on_globals M N)
    (hRecHead :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x1) x2) →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false)
                (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs)) =
          __smtx_model_eval N
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2)))
    (hRecArg :
      eoHasSmtTranslation a →
        eoHasSmtTranslation
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) →
        __smtx_model_eval M
            (__eo_to_smt
              (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) =
          __smtx_model_eval N (__eo_to_smt a)) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
            xs ss bvs)) =
      __smtx_model_eval N
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)) := by
  have hOrigTy :
      generic_apply_type
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2))
        (__eo_to_smt a) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hOrigNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2))
          (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hOrigTranslate]
    exact hFTrans
  rcases apply_args_have_smt_translation_of_non_none hOrigTy hOrigNN with
    ⟨hHeadTrans, hATrans⟩
  have hSubstInner :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) x1) xs ss bvs =
        __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.UOp op) x1 xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [hHeadSub] using hEq
  have hNotBinderMiddle :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x1 ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    by_cases hForall : op = UserOp.forall
    · subst op
      exact false_of_apply_apply_apply_forall_has_smt_translation hFTrans
    · by_cases hExists : op = UserOp.exists
      · subst op
        exact false_of_apply_apply_apply_exists_has_smt_translation hFTrans
      · exact
          apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
            hForall hExists hHeadTrans v vs rfl
  have hSubstHead :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.Apply (Term.UOp op) x1) x2 xs ss bvs hisr hxs hss hbvs
        hNotBinderMiddle
    rw [hEq, hSubstInner]
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) := by
    have hEq :=
      SubstituteSupport.substitute_simul_rec_apply (Term.Boolean false)
        (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a xs ss bvs
        hisr hxs hss hbvs hNotBinderOuter
    rw [hEq, hSubstHead]
  have hOuterNeStuck :
      __eo_mk_apply
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
        Term.Stuck := by
    rw [← hSubstEq]
    exact RuleProofs.term_ne_stuck_of_has_smt_translation _ hSubstTrans
  have hMidNeStuck :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNeStuck
  have hInnerNeStuck :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMidNeStuck
  have hInnerMk :
      __eo_mk_apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) =
        Term.Apply (Term.UOp op)
          (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ hInnerNeStuck
  have hMidMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hInnerMk]
      exact hMidNeStuck)
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck _ _ (by
      rw [← hMidMk, ← hInnerMk]
      exact hOuterNeStuck)
  have hHeadResultEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x1) x2) xs ss bvs =
        Term.Apply
          (Term.Apply (Term.UOp op)
            (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs) := by
    rw [hSubstHead, hInnerMk, hMidMk]
  have hResultEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x1) x2) a)
          xs ss bvs =
        Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) := by
    rw [hSubstEq, hInnerMk, hMidMk, hOuterMk]
  have hSubstTy :
      generic_apply_type
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs)))
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) :=
    generic_apply_type_of_non_special_head_closed _ _
      (by
        intro s d i j hSel
        exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
      (by
        intro s d i hTester
        exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester)
  have hSubstAppTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp op)
              (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
            (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) := by
    rw [← hResultEq]
    exact hSubstTrans
  have hSubstNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
              (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs)))
          (__eo_to_smt
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs))) := by
    unfold term_has_non_none_type
    rw [← hSubstTranslate]
    exact hSubstAppTrans
  rcases apply_args_have_smt_translation_of_non_none hSubstTy hSubstNN with
    ⟨hSubstHeadTrans, hSubstATrans⟩
  have hHeadEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp op)
                (__substitute_simul_rec (Term.Boolean false) x1 xs ss bvs))
              (__substitute_simul_rec (Term.Boolean false) x2 xs ss bvs))) =
        __smtx_model_eval N
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x1) x2)) := by
    simpa [hHeadResultEq] using
      hRecHead hHeadTrans
        (by
          rw [hHeadResultEq]
          exact hSubstHeadTrans)
  have hArgEval := hRecArg hATrans hSubstATrans
  rw [hResultEq, hOrigTranslate, hSubstTranslate]
  exact
    smtx_model_eval_apply_cross_eq_of_eval_eq hGlobals
      (generic_apply_eval_of_non_datatype_head
        (by
          intro s d i j hSel
          exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
        (by
          intro s d i hTester
          exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
      (generic_apply_eval_of_non_datatype_head
        (by
          intro s d i j hSel
          exact TranslationProofs.eo_to_smt_apply_ne_dt_sel _ _ s d i j hSel)
        (by
          intro s d i hTester
          exact TranslationProofs.eo_to_smt_apply_ne_dt_tester _ _ s d i hTester))
      hHeadEval hArgEval

/--
General substitution–evaluation induction (substitution mode, `isr = false`),
generalised over the bound-variable accumulator `bvs` and an arbitrary model
`N` realising the substitution.

Evaluating the translation of `subst false F xs ss bvs` in `M` coincides with
evaluating the translation of `F` in any model `N` related to `M` by
`SubstFalseRel M N xs ss bvs` (variables bound by `bvs` or unmapped by `xs` are
interpreted identically; a free mapped variable is assigned by `N` the value of
its substitute evaluated in `M`).

Proved by well-founded recursion on `F`. The **variable**, **atom**, and
**`Stuck`** cases are discharged here by `SubstituteSupport.substFalse_eval_var`
/ `substFalse_eval_atom` and the translation hypotheses. The **application**
case (both the non-binder heads — which reduce, per SMT constructor, to the
subterm IHs via the evaluator's compositionality — and the binder/quantifier
case, which descends under the binder via `SubstituteSupport.substFalseRel_push`
and the capture-avoidance guard) remains: it mirrors the head-shape dispatch of
`smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped_lt`
(`Cpc/Proofs/Closed/ContainsAtomicTermListFree.lean`), but with the substitution
applied on the `M` side. -/
theorem substFalse_eval_gen_lt
    (n : Nat) (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    {M N : SmtModel}
    (hLt : sizeOf F < n)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSsTrans : EoListAllHaveSmtTranslation ss)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hSubstTrans : RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ss bvs))
    (hRel : SubstituteSupport.SubstFalseRel M N xs ss bvs) :
    __smtx_model_eval M
        (__eo_to_smt (__substitute_simul_rec (Term.Boolean false) F xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt F) := by
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSsTrans
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  cases n with
  | zero => omega
  | succ n =>
      let hRec :
          ∀ {G bvs' : Term} {bvsVars' : List EoVarKey} {M' N' : SmtModel},
            sizeOf G < sizeOf F ->
            EoVarEnvPerm bvs' bvsVars' ->
            RuleProofs.eo_has_smt_translation G ->
            RuleProofs.eo_has_smt_translation
              (__substitute_simul_rec (Term.Boolean false) G xs ss bvs') ->
            SubstituteSupport.SubstFalseRel M' N' xs ss bvs' ->
            __smtx_model_eval M'
                (__eo_to_smt
                  (__substitute_simul_rec (Term.Boolean false) G xs ss bvs')) =
              __smtx_model_eval N' (__eo_to_smt G) :=
        fun {G bvs' bvsVars' M' N'} hGLt hBvsEnv' hGTrans hGSubstTrans hRel' =>
          substFalse_eval_gen_lt n G xs ss bvs' (by omega)
            hXsEnv hBvsEnv' hSsTrans hGTrans hGSubstTrans hRel'
      cases F
      case Apply f a =>
          by_cases hBinder :
              ∃ q v vs,
                f =
                  Term.Apply q
                    (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
          · -- binder / quantifier: descends under the binder via
            -- `substFalseRel_push` (its `hNoCollide` is dischargeable from
            -- `__eo_to_smt_type` injectivity; see the file header) and the
            -- capture-avoidance guard, then the body IH.
            sorry
          · -- The argument IH provider, shared by every non-binder head: the
            -- substitution keeps the operator head fixed, so each head reduces
            -- to the subterm IHs via `substFalse_eval_unary_op`.
            have hRecArg :
                ∀ {b : Term},
                  sizeOf b < sizeOf (Term.Apply f a) →
                  eoHasSmtTranslation b →
                  eoHasSmtTranslation
                    (__substitute_simul_rec (Term.Boolean false) b xs ss bvs) →
                  __smtx_model_eval M
                      (__eo_to_smt
                        (__substitute_simul_rec (Term.Boolean false) b xs ss bvs)) =
                    __smtx_model_eval N (__eo_to_smt b) :=
              fun {b} hb ht hst => hRec hb hBvsEnv ht hst hRel
            by_cases hNot : f = Term.UOp UserOp.not
            · subst f
              exact substFalse_eval_unary_op UserOp.not a xs ss bvs
                hisr hxs hss hbvs hFTrans hSubstTrans
                (substitute_simul_rec_uop_eq_self UserOp.not xs ss bvs
                  hXsEnv hBvsEnv hSsTrans)
                (fun {t} h => not_arg_has_smt_translation_of_has_smt_translation h)
                (fun X Y h => by
                  show __smtx_model_eval M (SmtTerm.not (__eo_to_smt X)) =
                    __smtx_model_eval N (SmtTerm.not (__eo_to_smt Y))
                  simp only [__smtx_model_eval]; rw [h])
                (fun ht hst => hRecArg (by simp; try omega) ht hst)
            · by_cases hToReal : f = Term.UOp UserOp.to_real
              · subst f
                exact substFalse_eval_unary_op UserOp.to_real a xs ss bvs
                  hisr hxs hss hbvs hFTrans hSubstTrans
                  (substitute_simul_rec_uop_eq_self UserOp.to_real xs ss bvs
                    hXsEnv hBvsEnv hSsTrans)
                  (fun {t} h => to_real_arg_has_smt_translation_of_has_smt_translation h)
                  (fun X Y h => by
                    show __smtx_model_eval M (SmtTerm.to_real (__eo_to_smt X)) =
                      __smtx_model_eval N (SmtTerm.to_real (__eo_to_smt Y))
                    simp only [__smtx_model_eval]; rw [h])
                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
              · by_cases hToInt : f = Term.UOp UserOp.to_int
                · subst f
                  exact substFalse_eval_unary_op UserOp.to_int a xs ss bvs
                    hisr hxs hss hbvs hFTrans hSubstTrans
                    (substitute_simul_rec_uop_eq_self UserOp.to_int xs ss bvs
                      hXsEnv hBvsEnv hSsTrans)
                    (fun {t} h => to_int_arg_has_smt_translation_of_has_smt_translation h)
                    (fun X Y h => by
                      show __smtx_model_eval M (SmtTerm.to_int (__eo_to_smt X)) =
                        __smtx_model_eval N (SmtTerm.to_int (__eo_to_smt Y))
                      simp only [__smtx_model_eval]; rw [h])
                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                · by_cases hIsInt : f = Term.UOp UserOp.is_int
                  · subst f
                    exact substFalse_eval_unary_op UserOp.is_int a xs ss bvs
                      hisr hxs hss hbvs hFTrans hSubstTrans
                      (substitute_simul_rec_uop_eq_self UserOp.is_int xs ss bvs
                        hXsEnv hBvsEnv hSsTrans)
                      (fun {t} h => is_int_arg_has_smt_translation_of_has_smt_translation h)
                      (fun X Y h => by
                        show __smtx_model_eval M (SmtTerm.is_int (__eo_to_smt X)) =
                          __smtx_model_eval N (SmtTerm.is_int (__eo_to_smt Y))
                        simp only [__smtx_model_eval]; rw [h])
                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                  · by_cases hAbs : f = Term.UOp UserOp.abs
                    · subst f
                      exact substFalse_eval_unary_op UserOp.abs a xs ss bvs
                        hisr hxs hss hbvs hFTrans hSubstTrans
                        (substitute_simul_rec_uop_eq_self UserOp.abs xs ss bvs
                          hXsEnv hBvsEnv hSsTrans)
                        (fun {t} h => abs_arg_has_smt_translation_of_has_smt_translation h)
                        (fun X Y h => by
                          show __smtx_model_eval M (SmtTerm.abs (__eo_to_smt X)) =
                            __smtx_model_eval N (SmtTerm.abs (__eo_to_smt Y))
                          simp only [__smtx_model_eval]; rw [h])
                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                    · by_cases hUneg : f = Term.UOp UserOp.__eoo_neg_2
                      · subst f
                        exact substFalse_eval_unary_op UserOp.__eoo_neg_2 a xs ss bvs
                          hisr hxs hss hbvs hFTrans hSubstTrans
                          (substitute_simul_rec_uop_eq_self UserOp.__eoo_neg_2 xs ss bvs
                            hXsEnv hBvsEnv hSsTrans)
                          (fun {t} h => uneg_arg_has_smt_translation_of_has_smt_translation h)
                          (fun X Y h => by
                            show __smtx_model_eval M (SmtTerm.uneg (__eo_to_smt X)) =
                              __smtx_model_eval N (SmtTerm.uneg (__eo_to_smt Y))
                            simp only [__smtx_model_eval]; rw [h])
                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                      · by_cases hPow2 : f = Term.UOp UserOp.int_pow2
                        · subst f
                          exact substFalse_eval_unary_op UserOp.int_pow2 a xs ss bvs
                            hisr hxs hss hbvs hFTrans hSubstTrans
                            (substitute_simul_rec_uop_eq_self UserOp.int_pow2 xs ss bvs
                              hXsEnv hBvsEnv hSsTrans)
                            (fun {t} h => int_pow2_arg_has_smt_translation_of_has_smt_translation h)
                            (fun X Y h => by
                              show __smtx_model_eval M (SmtTerm.int_pow2 (__eo_to_smt X)) =
                                __smtx_model_eval N (SmtTerm.int_pow2 (__eo_to_smt Y))
                              simp only [__smtx_model_eval]; rw [h])
                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                        · by_cases hLog2 : f = Term.UOp UserOp.int_log2
                          · subst f
                            exact substFalse_eval_unary_op UserOp.int_log2 a xs ss bvs
                              hisr hxs hss hbvs hFTrans hSubstTrans
                              (substitute_simul_rec_uop_eq_self UserOp.int_log2 xs ss bvs
                                hXsEnv hBvsEnv hSsTrans)
                              (fun {t} h => int_log2_arg_has_smt_translation_of_has_smt_translation h)
                              (fun X Y h => by
                                show __smtx_model_eval M (SmtTerm.int_log2 (__eo_to_smt X)) =
                                  __smtx_model_eval N (SmtTerm.int_log2 (__eo_to_smt Y))
                                simp only [__smtx_model_eval]; rw [h])
                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                          · by_cases hPurify : f = Term.UOp UserOp._at_purify
                            · subst f
                              exact substFalse_eval_unary_op UserOp._at_purify a xs ss bvs
                                hisr hxs hss hbvs hFTrans hSubstTrans
                                (substitute_simul_rec_uop_eq_self UserOp._at_purify xs ss bvs
                                  hXsEnv hBvsEnv hSsTrans)
                                (fun {t} h => purify_arg_has_smt_translation_of_has_smt_translation h)
                                (fun X Y h => by
                                  show __smtx_model_eval M (SmtTerm._at_purify (__eo_to_smt X)) =
                                    __smtx_model_eval N (SmtTerm._at_purify (__eo_to_smt Y))
                                  simp only [__smtx_model_eval]; rw [h])
                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                            · by_cases hIntIspow2 : f = Term.UOp UserOp.int_ispow2
                              · subst f
                                exact substFalse_eval_unary_op UserOp.int_ispow2 a xs ss bvs
                                  hisr hxs hss hbvs hFTrans hSubstTrans
                                  (substitute_simul_rec_uop_eq_self UserOp.int_ispow2 xs ss bvs
                                    hXsEnv hBvsEnv hSsTrans)
                                  (fun {t} h => int_ispow2_arg_has_smt_translation_of_has_smt_translation h)
                                  (fun X Y h => by
                                    show __smtx_model_eval M
                                        (SmtTerm.and (SmtTerm.geq (__eo_to_smt X) (SmtTerm.Numeral 0))
                                          (SmtTerm.eq (__eo_to_smt X)
                                            (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt X))))) =
                                      __smtx_model_eval N
                                        (SmtTerm.and (SmtTerm.geq (__eo_to_smt Y) (SmtTerm.Numeral 0))
                                          (SmtTerm.eq (__eo_to_smt Y)
                                            (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt Y)))))
                                    simp [__smtx_model_eval, h])
                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                              · by_cases hBvnot : f = Term.UOp UserOp.bvnot
                                · subst f
                                  exact substFalse_eval_unary_op UserOp.bvnot a xs ss bvs
                                    hisr hxs hss hbvs hFTrans hSubstTrans
                                    (substitute_simul_rec_uop_eq_self UserOp.bvnot xs ss bvs
                                      hXsEnv hBvsEnv hSsTrans)
                                    (fun {t} h => bvnot_arg_has_smt_translation_of_has_smt_translation h)
                                    (fun X Y h => by
                                      show __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt X)) =
                                        __smtx_model_eval N (SmtTerm.bvnot (__eo_to_smt Y))
                                      simp only [__smtx_model_eval]; rw [h])
                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                · by_cases hBvneg : f = Term.UOp UserOp.bvneg
                                  · subst f
                                    exact substFalse_eval_unary_op UserOp.bvneg a xs ss bvs
                                      hisr hxs hss hbvs hFTrans hSubstTrans
                                      (substitute_simul_rec_uop_eq_self UserOp.bvneg xs ss bvs
                                        hXsEnv hBvsEnv hSsTrans)
                                      (fun {t} h => bvneg_arg_has_smt_translation_of_has_smt_translation h)
                                      (fun X Y h => by
                                        show __smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt X)) =
                                          __smtx_model_eval N (SmtTerm.bvneg (__eo_to_smt Y))
                                        simp only [__smtx_model_eval]; rw [h])
                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                  · by_cases hBvnego : f = Term.UOp UserOp.bvnego
                                    · subst f
                                      exact substFalse_eval_unary_op UserOp.bvnego a xs ss bvs
                                        hisr hxs hss hbvs hFTrans hSubstTrans
                                        (substitute_simul_rec_uop_eq_self UserOp.bvnego xs ss bvs
                                          hXsEnv hBvsEnv hSsTrans)
                                        (fun {t} h => bvnego_arg_has_smt_translation_of_has_smt_translation h)
                                        (fun X Y h => by
                                          show __smtx_model_eval M (SmtTerm.bvnego (__eo_to_smt X)) =
                                            __smtx_model_eval N (SmtTerm.bvnego (__eo_to_smt Y))
                                          simp only [__smtx_model_eval]; rw [h])
                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                    · by_cases hStrLen : f = Term.UOp UserOp.str_len
                                      · subst f
                                        exact substFalse_eval_unary_op UserOp.str_len a xs ss bvs
                                          hisr hxs hss hbvs hFTrans hSubstTrans
                                          (substitute_simul_rec_uop_eq_self UserOp.str_len xs ss bvs
                                            hXsEnv hBvsEnv hSsTrans)
                                          (fun {t} h => str_len_arg_has_smt_translation_of_has_smt_translation h)
                                          (fun X Y h => by
                                            show __smtx_model_eval M (SmtTerm.str_len (__eo_to_smt X)) =
                                              __smtx_model_eval N (SmtTerm.str_len (__eo_to_smt Y))
                                            simp only [__smtx_model_eval]; rw [h])
                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                      · by_cases hStrRev : f = Term.UOp UserOp.str_rev
                                        · subst f
                                          exact substFalse_eval_unary_op UserOp.str_rev a xs ss bvs
                                            hisr hxs hss hbvs hFTrans hSubstTrans
                                            (substitute_simul_rec_uop_eq_self UserOp.str_rev xs ss bvs
                                              hXsEnv hBvsEnv hSsTrans)
                                            (fun {t} h => str_rev_arg_has_smt_translation_of_has_smt_translation h)
                                            (fun X Y h => by
                                              show __smtx_model_eval M (SmtTerm.str_rev (__eo_to_smt X)) =
                                                __smtx_model_eval N (SmtTerm.str_rev (__eo_to_smt Y))
                                              simp only [__smtx_model_eval]; rw [h])
                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                        · by_cases hStrToInt : f = Term.UOp UserOp.str_to_int
                                          · subst f
                                            exact substFalse_eval_unary_op UserOp.str_to_int a xs ss bvs
                                              hisr hxs hss hbvs hFTrans hSubstTrans
                                              (substitute_simul_rec_uop_eq_self UserOp.str_to_int xs ss bvs
                                                hXsEnv hBvsEnv hSsTrans)
                                              (fun {t} h => str_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                              (fun X Y h => by
                                                show __smtx_model_eval M (SmtTerm.str_to_int (__eo_to_smt X)) =
                                                  __smtx_model_eval N (SmtTerm.str_to_int (__eo_to_smt Y))
                                                simp only [__smtx_model_eval]; rw [h])
                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                          · by_cases hStrToRe : f = Term.UOp UserOp.str_to_re
                                            · subst f
                                              exact substFalse_eval_unary_op UserOp.str_to_re a xs ss bvs
                                                hisr hxs hss hbvs hFTrans hSubstTrans
                                                (substitute_simul_rec_uop_eq_self UserOp.str_to_re xs ss bvs
                                                  hXsEnv hBvsEnv hSsTrans)
                                                (fun {t} h => str_to_re_arg_has_smt_translation_of_has_smt_translation h)
                                                (fun X Y h => by
                                                  show __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt X)) =
                                                    __smtx_model_eval N (SmtTerm.str_to_re (__eo_to_smt Y))
                                                  simp only [__smtx_model_eval]; rw [h])
                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                            · by_cases hReMult : f = Term.UOp UserOp.re_mult
                                              · subst f
                                                exact substFalse_eval_unary_op UserOp.re_mult a xs ss bvs
                                                  hisr hxs hss hbvs hFTrans hSubstTrans
                                                  (substitute_simul_rec_uop_eq_self UserOp.re_mult xs ss bvs
                                                    hXsEnv hBvsEnv hSsTrans)
                                                  (fun {t} h => re_mult_arg_has_smt_translation_of_has_smt_translation h)
                                                  (fun X Y h => by
                                                    show __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt X)) =
                                                      __smtx_model_eval N (SmtTerm.re_mult (__eo_to_smt Y))
                                                    simp only [__smtx_model_eval]; rw [h])
                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                              · by_cases hSeqUnit : f = Term.UOp UserOp.seq_unit
                                                · subst f
                                                  exact substFalse_eval_unary_op UserOp.seq_unit a xs ss bvs
                                                    hisr hxs hss hbvs hFTrans hSubstTrans
                                                    (substitute_simul_rec_uop_eq_self UserOp.seq_unit xs ss bvs
                                                      hXsEnv hBvsEnv hSsTrans)
                                                    (fun {t} h => seq_unit_arg_has_smt_translation_of_has_smt_translation h)
                                                    (fun X Y h => by
                                                      show __smtx_model_eval M (SmtTerm.seq_unit (__eo_to_smt X)) =
                                                        __smtx_model_eval N (SmtTerm.seq_unit (__eo_to_smt Y))
                                                      simp only [__smtx_model_eval]; rw [h])
                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                · by_cases hSetSingleton : f = Term.UOp UserOp.set_singleton
                                                  · subst f
                                                    exact substFalse_eval_unary_op UserOp.set_singleton a xs ss bvs
                                                      hisr hxs hss hbvs hFTrans hSubstTrans
                                                      (substitute_simul_rec_uop_eq_self UserOp.set_singleton xs ss bvs
                                                        hXsEnv hBvsEnv hSsTrans)
                                                      (fun {t} h => set_singleton_arg_has_smt_translation_of_has_smt_translation h)
                                                      (fun X Y h => by
                                                        show __smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt X)) =
                                                          __smtx_model_eval N (SmtTerm.set_singleton (__eo_to_smt Y))
                                                        simp only [__smtx_model_eval]; rw [h])
                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                  · by_cases hStrToLower : f = Term.UOp UserOp.str_to_lower
                                                    · subst f
                                                      exact substFalse_eval_unary_op UserOp.str_to_lower a xs ss bvs
                                                        hisr hxs hss hbvs hFTrans hSubstTrans
                                                        (substitute_simul_rec_uop_eq_self UserOp.str_to_lower xs ss bvs
                                                          hXsEnv hBvsEnv hSsTrans)
                                                        (fun {t} h => str_to_lower_arg_has_smt_translation_of_has_smt_translation h)
                                                        (fun X Y h => by
                                                          show __smtx_model_eval M (SmtTerm.str_to_lower (__eo_to_smt X)) =
                                                            __smtx_model_eval N (SmtTerm.str_to_lower (__eo_to_smt Y))
                                                          simp only [__smtx_model_eval]; rw [h])
                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                    · by_cases hStrToUpper : f = Term.UOp UserOp.str_to_upper
                                                      · subst f
                                                        exact substFalse_eval_unary_op UserOp.str_to_upper a xs ss bvs
                                                          hisr hxs hss hbvs hFTrans hSubstTrans
                                                          (substitute_simul_rec_uop_eq_self UserOp.str_to_upper xs ss bvs
                                                            hXsEnv hBvsEnv hSsTrans)
                                                          (fun {t} h => str_to_upper_arg_has_smt_translation_of_has_smt_translation h)
                                                          (fun X Y h => by
                                                            show __smtx_model_eval M (SmtTerm.str_to_upper (__eo_to_smt X)) =
                                                              __smtx_model_eval N (SmtTerm.str_to_upper (__eo_to_smt Y))
                                                            simp only [__smtx_model_eval]; rw [h])
                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                      · by_cases hStrToCode : f = Term.UOp UserOp.str_to_code
                                                        · subst f
                                                          exact substFalse_eval_unary_op UserOp.str_to_code a xs ss bvs
                                                            hisr hxs hss hbvs hFTrans hSubstTrans
                                                            (substitute_simul_rec_uop_eq_self UserOp.str_to_code xs ss bvs
                                                              hXsEnv hBvsEnv hSsTrans)
                                                            (fun {t} h => str_to_code_arg_has_smt_translation_of_has_smt_translation h)
                                                            (fun X Y h => by
                                                              show __smtx_model_eval M (SmtTerm.str_to_code (__eo_to_smt X)) =
                                                                __smtx_model_eval N (SmtTerm.str_to_code (__eo_to_smt Y))
                                                              simp only [__smtx_model_eval]; rw [h])
                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                        · by_cases hStrFromCode : f = Term.UOp UserOp.str_from_code
                                                          · subst f
                                                            exact substFalse_eval_unary_op UserOp.str_from_code a xs ss bvs
                                                              hisr hxs hss hbvs hFTrans hSubstTrans
                                                              (substitute_simul_rec_uop_eq_self UserOp.str_from_code xs ss bvs
                                                                hXsEnv hBvsEnv hSsTrans)
                                                              (fun {t} h => str_from_code_arg_has_smt_translation_of_has_smt_translation h)
                                                              (fun X Y h => by
                                                                show __smtx_model_eval M (SmtTerm.str_from_code (__eo_to_smt X)) =
                                                                  __smtx_model_eval N (SmtTerm.str_from_code (__eo_to_smt Y))
                                                                simp only [__smtx_model_eval]; rw [h])
                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                          · by_cases hStrIsDigit : f = Term.UOp UserOp.str_is_digit
                                                            · subst f
                                                              exact substFalse_eval_unary_op UserOp.str_is_digit a xs ss bvs
                                                                hisr hxs hss hbvs hFTrans hSubstTrans
                                                                (substitute_simul_rec_uop_eq_self UserOp.str_is_digit xs ss bvs
                                                                  hXsEnv hBvsEnv hSsTrans)
                                                                (fun {t} h => str_is_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                                (fun X Y h => by
                                                                  show __smtx_model_eval M (SmtTerm.str_is_digit (__eo_to_smt X)) =
                                                                    __smtx_model_eval N (SmtTerm.str_is_digit (__eo_to_smt Y))
                                                                  simp only [__smtx_model_eval]; rw [h])
                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                            · by_cases hStrFromInt : f = Term.UOp UserOp.str_from_int
                                                              · subst f
                                                                exact substFalse_eval_unary_op UserOp.str_from_int a xs ss bvs
                                                                  hisr hxs hss hbvs hFTrans hSubstTrans
                                                                  (substitute_simul_rec_uop_eq_self UserOp.str_from_int xs ss bvs
                                                                    hXsEnv hBvsEnv hSsTrans)
                                                                  (fun {t} h => str_from_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                  (fun X Y h => by
                                                                    show __smtx_model_eval M (SmtTerm.str_from_int (__eo_to_smt X)) =
                                                                      __smtx_model_eval N (SmtTerm.str_from_int (__eo_to_smt Y))
                                                                    simp only [__smtx_model_eval]; rw [h])
                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                              · by_cases hRePlus : f = Term.UOp UserOp.re_plus
                                                                · subst f
                                                                  exact substFalse_eval_unary_op UserOp.re_plus a xs ss bvs
                                                                    hisr hxs hss hbvs hFTrans hSubstTrans
                                                                    (substitute_simul_rec_uop_eq_self UserOp.re_plus xs ss bvs
                                                                      hXsEnv hBvsEnv hSsTrans)
                                                                    (fun {t} h => re_plus_arg_has_smt_translation_of_has_smt_translation h)
                                                                    (fun X Y h => by
                                                                      show __smtx_model_eval M (SmtTerm.re_plus (__eo_to_smt X)) =
                                                                        __smtx_model_eval N (SmtTerm.re_plus (__eo_to_smt Y))
                                                                      simp only [__smtx_model_eval]; rw [h])
                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                · by_cases hReOpt : f = Term.UOp UserOp.re_opt
                                                                  · subst f
                                                                    exact substFalse_eval_unary_op UserOp.re_opt a xs ss bvs
                                                                      hisr hxs hss hbvs hFTrans hSubstTrans
                                                                      (substitute_simul_rec_uop_eq_self UserOp.re_opt xs ss bvs
                                                                        hXsEnv hBvsEnv hSsTrans)
                                                                      (fun {t} h => re_opt_arg_has_smt_translation_of_has_smt_translation h)
                                                                      (fun X Y h => by
                                                                        show __smtx_model_eval M (SmtTerm.re_opt (__eo_to_smt X)) =
                                                                          __smtx_model_eval N (SmtTerm.re_opt (__eo_to_smt Y))
                                                                        simp only [__smtx_model_eval]; rw [h])
                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                  · by_cases hReComp : f = Term.UOp UserOp.re_comp
                                                                    · subst f
                                                                      exact substFalse_eval_unary_op UserOp.re_comp a xs ss bvs
                                                                        hisr hxs hss hbvs hFTrans hSubstTrans
                                                                        (substitute_simul_rec_uop_eq_self UserOp.re_comp xs ss bvs
                                                                          hXsEnv hBvsEnv hSsTrans)
                                                                        (fun {t} h => re_comp_arg_has_smt_translation_of_has_smt_translation h)
                                                                        (fun X Y h => by
                                                                          show __smtx_model_eval M (SmtTerm.re_comp (__eo_to_smt X)) =
                                                                            __smtx_model_eval N (SmtTerm.re_comp (__eo_to_smt Y))
                                                                          simp only [__smtx_model_eval]; rw [h])
                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                    · by_cases hUbvToInt : f = Term.UOp UserOp.ubv_to_int
                                                                      · subst f
                                                                        exact substFalse_eval_unary_op UserOp.ubv_to_int a xs ss bvs
                                                                          hisr hxs hss hbvs hFTrans hSubstTrans
                                                                          (substitute_simul_rec_uop_eq_self UserOp.ubv_to_int xs ss bvs
                                                                            hXsEnv hBvsEnv hSsTrans)
                                                                          (fun {t} h => ubv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                          (fun X Y h => by
                                                                            show __smtx_model_eval M (SmtTerm.ubv_to_int (__eo_to_smt X)) =
                                                                              __smtx_model_eval N (SmtTerm.ubv_to_int (__eo_to_smt Y))
                                                                            simp only [__smtx_model_eval]; rw [h])
                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                      · by_cases hSbvToInt : f = Term.UOp UserOp.sbv_to_int
                                                                        · subst f
                                                                          exact substFalse_eval_unary_op UserOp.sbv_to_int a xs ss bvs
                                                                            hisr hxs hss hbvs hFTrans hSubstTrans
                                                                            (substitute_simul_rec_uop_eq_self UserOp.sbv_to_int xs ss bvs
                                                                              hXsEnv hBvsEnv hSsTrans)
                                                                            (fun {t} h => sbv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                            (fun X Y h => by
                                                                              show __smtx_model_eval M (SmtTerm.sbv_to_int (__eo_to_smt X)) =
                                                                                __smtx_model_eval N (SmtTerm.sbv_to_int (__eo_to_smt Y))
                                                                              simp only [__smtx_model_eval]; rw [h])
                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                        · by_cases hStringsStoiNonDigit : f = Term.UOp UserOp._at_strings_stoi_non_digit
                                                                          · subst f
                                                                            exact substFalse_eval_unary_op UserOp._at_strings_stoi_non_digit a xs ss bvs
                                                                              hisr hxs hss hbvs hFTrans hSubstTrans
                                                                              (substitute_simul_rec_uop_eq_self UserOp._at_strings_stoi_non_digit xs ss bvs
                                                                                hXsEnv hBvsEnv hSsTrans)
                                                                              (fun {t} h => strings_stoi_non_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                                              (fun X Y h => by
                                                                                show __smtx_model_eval M
                                                                                    (SmtTerm.str_indexof_re (__eo_to_smt X)
                                                                                      (SmtTerm.re_comp
                                                                                        (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
                                                                                          (SmtTerm.String (native_string_lit "9"))))
                                                                                      (SmtTerm.Numeral 0)) =
                                                                                  __smtx_model_eval N
                                                                                    (SmtTerm.str_indexof_re (__eo_to_smt Y)
                                                                                      (SmtTerm.re_comp
                                                                                        (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
                                                                                          (SmtTerm.String (native_string_lit "9"))))
                                                                                      (SmtTerm.Numeral 0))
                                                                                simp [__smtx_model_eval, h])
                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                          · by_cases hIntDivByZero : f = Term.UOp UserOp._at_int_div_by_zero
                                                                            · subst f
                                                                              exact substFalse_eval_unary_op UserOp._at_int_div_by_zero a xs ss bvs
                                                                                hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                (substitute_simul_rec_uop_eq_self UserOp._at_int_div_by_zero xs ss bvs
                                                                                  hXsEnv hBvsEnv hSsTrans)
                                                                                (fun {t} h => int_div_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                                                (fun X Y h => by
                                                                                  show __smtx_model_eval M (SmtTerm.div (__eo_to_smt X) (SmtTerm.Numeral 0)) =
                                                                                    __smtx_model_eval N (SmtTerm.div (__eo_to_smt Y) (SmtTerm.Numeral 0))
                                                                                  simp [__smtx_model_eval, h,
                                                                                    smtx_model_eval_apply_eq_of_globals hRel.globals,
                                                                                    hRel.globals.1])
                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                            · by_cases hModByZero : f = Term.UOp UserOp._at_mod_by_zero
                                                                              · subst f
                                                                                exact substFalse_eval_unary_op UserOp._at_mod_by_zero a xs ss bvs
                                                                                  hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                  (substitute_simul_rec_uop_eq_self UserOp._at_mod_by_zero xs ss bvs
                                                                                    hXsEnv hBvsEnv hSsTrans)
                                                                                  (fun {t} h => mod_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                                                  (fun X Y h => by
                                                                                    show __smtx_model_eval M (SmtTerm.mod (__eo_to_smt X) (SmtTerm.Numeral 0)) =
                                                                                      __smtx_model_eval N (SmtTerm.mod (__eo_to_smt Y) (SmtTerm.Numeral 0))
                                                                                    simp [__smtx_model_eval, h,
                                                                                      smtx_model_eval_apply_eq_of_globals hRel.globals,
                                                                                      hRel.globals.1])
                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                              · by_cases hQdivByZero : f = Term.UOp UserOp._at_div_by_zero
                                                                                · subst f
                                                                                  exact substFalse_eval_unary_op UserOp._at_div_by_zero a xs ss bvs
                                                                                    hisr hxs hss hbvs hFTrans hSubstTrans
                                                                                    (substitute_simul_rec_uop_eq_self UserOp._at_div_by_zero xs ss bvs
                                                                                      hXsEnv hBvsEnv hSsTrans)
                                                                                    (fun {t} h => qdiv_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                                                    (fun X Y h => by
                                                                                      show __smtx_model_eval M
                                                                                          (SmtTerm.qdiv (__eo_to_smt X)
                                                                                            (SmtTerm.Rational (native_mk_rational 0 1))) =
                                                                                        __smtx_model_eval N
                                                                                          (SmtTerm.qdiv (__eo_to_smt Y)
                                                                                            (SmtTerm.Rational (native_mk_rational 0 1)))
                                                                                      simp [__smtx_model_eval, h,
                                                                                        smtx_model_eval_apply_eq_of_globals hRel.globals,
                                                                                        hRel.globals.1])
                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                · -- `f` is not one of the handled unary heads: dispatch on its
                                                                                  -- structure for binary heads (`Apply (UOp op) x1`).
                                                                                  cases f with
                              | Apply g x1 =>
                                  cases g with
                                  | UOp op =>
                                      -- Binary special heads `(Apply (Apply (UOp op) x1) a)`; dispatch on `op`.
                                      -- (div/mod and other model-global-dependent ops are left for later.)
                                      by_cases h_and : op = UserOp.and
                                      · subst op
                                        exact substFalse_eval_binary_op UserOp.and x1 a xs ss bvs
                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                          hFTrans hSubstTrans
                                          (substitute_simul_rec_uop_eq_self UserOp.and xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                          (fun {s t} h => and_args_have_smt_translation_of_has_smt_translation h)
                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                            show __smtx_model_eval M (SmtTerm.and (__eo_to_smt X1) (__eo_to_smt X2)) =
                                              __smtx_model_eval N (SmtTerm.and (__eo_to_smt Y1) (__eo_to_smt Y2))
                                            simp only [__smtx_model_eval]; rw [h1, h2])
                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                      ·
                                        by_cases h_or : op = UserOp.or
                                        · subst op
                                          exact substFalse_eval_binary_op UserOp.or x1 a xs ss bvs
                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                            hFTrans hSubstTrans
                                            (substitute_simul_rec_uop_eq_self UserOp.or xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                            (fun {s t} h => or_args_have_smt_translation_of_has_smt_translation h)
                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                              show __smtx_model_eval M (SmtTerm.or (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                __smtx_model_eval N (SmtTerm.or (__eo_to_smt Y1) (__eo_to_smt Y2))
                                              simp only [__smtx_model_eval]; rw [h1, h2])
                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                        ·
                                          by_cases h_imp : op = UserOp.imp
                                          · subst op
                                            exact substFalse_eval_binary_op UserOp.imp x1 a xs ss bvs
                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                              hFTrans hSubstTrans
                                              (substitute_simul_rec_uop_eq_self UserOp.imp xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                              (fun {s t} h => imp_args_have_smt_translation_of_has_smt_translation h)
                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                show __smtx_model_eval M (SmtTerm.imp (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                  __smtx_model_eval N (SmtTerm.imp (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                simp only [__smtx_model_eval]; rw [h1, h2])
                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                          ·
                                            by_cases h_xor : op = UserOp.xor
                                            · subst op
                                              exact substFalse_eval_binary_op UserOp.xor x1 a xs ss bvs
                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                hFTrans hSubstTrans
                                                (substitute_simul_rec_uop_eq_self UserOp.xor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                (fun {s t} h => xor_args_have_smt_translation_of_has_smt_translation h)
                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                  show __smtx_model_eval M (SmtTerm.xor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                    __smtx_model_eval N (SmtTerm.xor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                  simp only [__smtx_model_eval]; rw [h1, h2])
                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                            ·
                                              by_cases h_eq : op = UserOp.eq
                                              · subst op
                                                exact substFalse_eval_binary_op UserOp.eq x1 a xs ss bvs
                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                  hFTrans hSubstTrans
                                                  (substitute_simul_rec_uop_eq_self UserOp.eq xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                  (fun {s t} h => eq_args_have_smt_translation_of_has_smt_translation h)
                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                    show __smtx_model_eval M (SmtTerm.eq (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                      __smtx_model_eval N (SmtTerm.eq (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                    simp only [__smtx_model_eval]; rw [h1, h2])
                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                              ·
                                                by_cases h_plus : op = UserOp.plus
                                                · subst op
                                                  exact substFalse_eval_binary_op UserOp.plus x1 a xs ss bvs
                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                    hFTrans hSubstTrans
                                                    (substitute_simul_rec_uop_eq_self UserOp.plus xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                    (fun {s t} h => plus_args_have_smt_translation_of_has_smt_translation h)
                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                      show __smtx_model_eval M (SmtTerm.plus (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                        __smtx_model_eval N (SmtTerm.plus (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                      simp only [__smtx_model_eval]; rw [h1, h2])
                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                ·
                                                  by_cases h_neg : op = UserOp.neg
                                                  · subst op
                                                    exact substFalse_eval_binary_op UserOp.neg x1 a xs ss bvs
                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                      hFTrans hSubstTrans
                                                      (substitute_simul_rec_uop_eq_self UserOp.neg xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                      (fun {s t} h => neg_args_have_smt_translation_of_has_smt_translation h)
                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                        show __smtx_model_eval M (SmtTerm.neg (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                          __smtx_model_eval N (SmtTerm.neg (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                        simp only [__smtx_model_eval]; rw [h1, h2])
                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                  ·
                                                    by_cases h_mult : op = UserOp.mult
                                                    · subst op
                                                      exact substFalse_eval_binary_op UserOp.mult x1 a xs ss bvs
                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                        hFTrans hSubstTrans
                                                        (substitute_simul_rec_uop_eq_self UserOp.mult xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                        (fun {s t} h => mult_args_have_smt_translation_of_has_smt_translation h)
                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                          show __smtx_model_eval M (SmtTerm.mult (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                            __smtx_model_eval N (SmtTerm.mult (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                          simp only [__smtx_model_eval]; rw [h1, h2])
                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                    ·
                                                      by_cases h_lt : op = UserOp.lt
                                                      · subst op
                                                        exact substFalse_eval_binary_op UserOp.lt x1 a xs ss bvs
                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                          hFTrans hSubstTrans
                                                          (substitute_simul_rec_uop_eq_self UserOp.lt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                          (fun {s t} h => lt_args_have_smt_translation_of_has_smt_translation h)
                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                            show __smtx_model_eval M (SmtTerm.lt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                              __smtx_model_eval N (SmtTerm.lt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                            simp only [__smtx_model_eval]; rw [h1, h2])
                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                      ·
                                                        by_cases h_leq : op = UserOp.leq
                                                        · subst op
                                                          exact substFalse_eval_binary_op UserOp.leq x1 a xs ss bvs
                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                            hFTrans hSubstTrans
                                                            (substitute_simul_rec_uop_eq_self UserOp.leq xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                            (fun {s t} h => leq_args_have_smt_translation_of_has_smt_translation h)
                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                              show __smtx_model_eval M (SmtTerm.leq (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                __smtx_model_eval N (SmtTerm.leq (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                              simp only [__smtx_model_eval]; rw [h1, h2])
                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                        ·
                                                          by_cases h_gt : op = UserOp.gt
                                                          · subst op
                                                            exact substFalse_eval_binary_op UserOp.gt x1 a xs ss bvs
                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                              hFTrans hSubstTrans
                                                              (substitute_simul_rec_uop_eq_self UserOp.gt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                              (fun {s t} h => gt_args_have_smt_translation_of_has_smt_translation h)
                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                show __smtx_model_eval M (SmtTerm.gt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                  __smtx_model_eval N (SmtTerm.gt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                simp only [__smtx_model_eval]; rw [h1, h2])
                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                          ·
                                                            by_cases h_geq : op = UserOp.geq
                                                            · subst op
                                                              exact substFalse_eval_binary_op UserOp.geq x1 a xs ss bvs
                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                hFTrans hSubstTrans
                                                                (substitute_simul_rec_uop_eq_self UserOp.geq xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                (fun {s t} h => geq_args_have_smt_translation_of_has_smt_translation h)
                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                  show __smtx_model_eval M (SmtTerm.geq (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                    __smtx_model_eval N (SmtTerm.geq (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                  simp only [__smtx_model_eval]; rw [h1, h2])
                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                            · by_cases h_div : op = UserOp.div
                                                              · subst op
                                                                exact substFalse_eval_binary_op UserOp.div x1 a xs ss bvs
                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                  hFTrans hSubstTrans
                                                                  (substitute_simul_rec_uop_eq_self UserOp.div xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                  (fun {s t} h => div_args_have_smt_translation_of_has_smt_translation h)
                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                    show __smtx_model_eval M (SmtTerm.div (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                      __smtx_model_eval N (SmtTerm.div (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                    simp only [__smtx_model_eval]
                                                                    rw [h1, h2, smtx_model_eval_apply_eq_of_globals hRel.globals,
                                                                      hRel.globals.1])
                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                              · by_cases h_mod : op = UserOp.mod
                                                                · subst op
                                                                  exact substFalse_eval_binary_op UserOp.mod x1 a xs ss bvs
                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                    hFTrans hSubstTrans
                                                                    (substitute_simul_rec_uop_eq_self UserOp.mod xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                    (fun {s t} h => mod_args_have_smt_translation_of_has_smt_translation h)
                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                      show __smtx_model_eval M (SmtTerm.mod (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                        __smtx_model_eval N (SmtTerm.mod (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                      simp only [__smtx_model_eval]
                                                                      rw [h1, h2, smtx_model_eval_apply_eq_of_globals hRel.globals,
                                                                        hRel.globals.1])
                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                ·
                                                                  by_cases h_select : op = UserOp.select
                                                                  · subst op
                                                                    exact substFalse_eval_binary_op UserOp.select x1 a xs ss bvs
                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                      hFTrans hSubstTrans
                                                                      (substitute_simul_rec_uop_eq_self UserOp.select xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                      (fun {s t} h => select_args_have_smt_translation_of_has_smt_translation h)
                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                        show __smtx_model_eval M (SmtTerm.select (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                          __smtx_model_eval N (SmtTerm.select (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                        simp only [__smtx_model_eval]; rw [h1, h2])
                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                  ·
                                                                    by_cases h_divisible : op = UserOp.divisible
                                                                    · subst op
                                                                      exact substFalse_eval_binary_op UserOp.divisible x1 a xs ss bvs
                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                        hFTrans hSubstTrans
                                                                        (substitute_simul_rec_uop_eq_self UserOp.divisible xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                        (fun {s t} h => divisible_args_have_smt_translation_of_has_smt_translation h)
                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                          show __smtx_model_eval M (SmtTerm.divisible (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                            __smtx_model_eval N (SmtTerm.divisible (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                          simp only [__smtx_model_eval]; rw [h1, h2])
                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                    ·
                                                                      by_cases h_div_total : op = UserOp.div_total
                                                                      · subst op
                                                                        exact substFalse_eval_binary_op UserOp.div_total x1 a xs ss bvs
                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                          hFTrans hSubstTrans
                                                                          (substitute_simul_rec_uop_eq_self UserOp.div_total xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                          (fun {s t} h => div_total_args_have_smt_translation_of_has_smt_translation h)
                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                            show __smtx_model_eval M (SmtTerm.div_total (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                              __smtx_model_eval N (SmtTerm.div_total (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                            simp only [__smtx_model_eval]; rw [h1, h2])
                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                      ·
                                                                        by_cases h_mod_total : op = UserOp.mod_total
                                                                        · subst op
                                                                          exact substFalse_eval_binary_op UserOp.mod_total x1 a xs ss bvs
                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                            hFTrans hSubstTrans
                                                                            (substitute_simul_rec_uop_eq_self UserOp.mod_total xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                            (fun {s t} h => mod_total_args_have_smt_translation_of_has_smt_translation h)
                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                              show __smtx_model_eval M (SmtTerm.mod_total (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                __smtx_model_eval N (SmtTerm.mod_total (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                              simp only [__smtx_model_eval]; rw [h1, h2])
                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                        ·
                                                                          by_cases h_multmult_total : op = UserOp.multmult_total
                                                                          · subst op
                                                                            exact substFalse_eval_binary_op UserOp.multmult_total x1 a xs ss bvs
                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                              hFTrans hSubstTrans
                                                                              (substitute_simul_rec_uop_eq_self UserOp.multmult_total xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                              (fun {s t} h => multmult_total_args_have_smt_translation_of_has_smt_translation h)
                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                show __smtx_model_eval M (SmtTerm.multmult_total (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                  __smtx_model_eval N (SmtTerm.multmult_total (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                simp only [__smtx_model_eval]; rw [h1, h2])
                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                          · by_cases h_multmult : op = UserOp.multmult
                                                                            · subst op
                                                                              exact substFalse_eval_binary_op UserOp.multmult x1 a xs ss bvs
                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                hFTrans hSubstTrans
                                                                                (substitute_simul_rec_uop_eq_self UserOp.multmult xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                (fun {s t} h => multmult_args_have_smt_translation_of_has_smt_translation h)
                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                  show __smtx_model_eval M (SmtTerm.multmult (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                    __smtx_model_eval N (SmtTerm.multmult (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                  simp only [__smtx_model_eval]
                                                                                  rw [h1, h2, smtx_model_eval_apply_eq_of_globals hRel.globals,
                                                                                    hRel.globals.1])
                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                            · by_cases h_qdiv_total : op = UserOp.qdiv_total
                                                                              · subst op
                                                                                exact substFalse_eval_binary_op UserOp.qdiv_total x1 a xs ss bvs
                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                  hFTrans hSubstTrans
                                                                                  (substitute_simul_rec_uop_eq_self UserOp.qdiv_total xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                  (fun {s t} h => qdiv_total_args_have_smt_translation_of_has_smt_translation h)
                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                    show __smtx_model_eval M (SmtTerm.qdiv_total (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                      __smtx_model_eval N (SmtTerm.qdiv_total (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                    simp only [__smtx_model_eval]
                                                                                    rw [h1, h2])
                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                              · by_cases h_qdiv : op = UserOp.qdiv
                                                                                · subst op
                                                                                  exact substFalse_eval_binary_op UserOp.qdiv x1 a xs ss bvs
                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                    hFTrans hSubstTrans
                                                                                    (substitute_simul_rec_uop_eq_self UserOp.qdiv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                    (fun {s t} h => qdiv_args_have_smt_translation_of_has_smt_translation h)
                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                      show __smtx_model_eval M (SmtTerm.qdiv (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                        __smtx_model_eval N (SmtTerm.qdiv (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                      simp only [__smtx_model_eval]
                                                                                      rw [h1, h2, smtx_model_eval_apply_eq_of_globals hRel.globals,
                                                                                        hRel.globals.1])
                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                · by_cases h_concat : op = UserOp.concat
                                                                                  · subst op
                                                                                    exact substFalse_eval_binary_op UserOp.concat x1 a xs ss bvs
                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                      hFTrans hSubstTrans
                                                                                      (substitute_simul_rec_uop_eq_self UserOp.concat xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                      (fun {s t} h =>
                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                          (eoOp := UserOp.concat) (smtOp := SmtTerm.concat)
                                                                                          (by rfl) bv_concat_args_have_smt_translation_of_non_none h)
                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                        show __smtx_model_eval M (SmtTerm.concat (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                          __smtx_model_eval N (SmtTerm.concat (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                        simp only [__smtx_model_eval]
                                                                                        rw [h1, h2])
                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                  · by_cases h_bvand : op = UserOp.bvand
                                                                                    · subst op
                                                                                      exact substFalse_eval_binary_op UserOp.bvand x1 a xs ss bvs
                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                        hFTrans hSubstTrans
                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvand xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                        (fun {s t} h =>
                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                            (eoOp := UserOp.bvand) (smtOp := SmtTerm.bvand)
                                                                                            (by rfl)
                                                                                            (fun hNN =>
                                                                                              bv_binop_args_have_smt_translation_of_non_none
                                                                                                (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                            h)
                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                          show __smtx_model_eval M (SmtTerm.bvand (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                            __smtx_model_eval N (SmtTerm.bvand (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                          simp only [__smtx_model_eval]
                                                                                          rw [h1, h2])
                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                    · by_cases h_bvor : op = UserOp.bvor
                                                                                      · subst op
                                                                                        exact substFalse_eval_binary_op UserOp.bvor x1 a xs ss bvs
                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                          hFTrans hSubstTrans
                                                                                          (substitute_simul_rec_uop_eq_self UserOp.bvor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                          (fun {s t} h =>
                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                              (eoOp := UserOp.bvor) (smtOp := SmtTerm.bvor)
                                                                                              (by rfl)
                                                                                              (fun hNN =>
                                                                                                bv_binop_args_have_smt_translation_of_non_none
                                                                                                  (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                              h)
                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                            show __smtx_model_eval M (SmtTerm.bvor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                              __smtx_model_eval N (SmtTerm.bvor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                            simp only [__smtx_model_eval]
                                                                                            rw [h1, h2])
                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                      · by_cases h_bvnand : op = UserOp.bvnand
                                                                                        · subst op
                                                                                          exact substFalse_eval_binary_op UserOp.bvnand x1 a xs ss bvs
                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                            hFTrans hSubstTrans
                                                                                            (substitute_simul_rec_uop_eq_self UserOp.bvnand xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                            (fun {s t} h =>
                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                (eoOp := UserOp.bvnand) (smtOp := SmtTerm.bvnand)
                                                                                                (by rfl)
                                                                                                (fun hNN =>
                                                                                                  bv_binop_args_have_smt_translation_of_non_none
                                                                                                    (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                h)
                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                              show __smtx_model_eval M (SmtTerm.bvnand (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                __smtx_model_eval N (SmtTerm.bvnand (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                              simp only [__smtx_model_eval]
                                                                                              rw [h1, h2])
                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                        · by_cases h_bvnor : op = UserOp.bvnor
                                                                                          · subst op
                                                                                            exact substFalse_eval_binary_op UserOp.bvnor x1 a xs ss bvs
                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                              hFTrans hSubstTrans
                                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvnor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                              (fun {s t} h =>
                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                  (eoOp := UserOp.bvnor) (smtOp := SmtTerm.bvnor)
                                                                                                  (by rfl)
                                                                                                  (fun hNN =>
                                                                                                    bv_binop_args_have_smt_translation_of_non_none
                                                                                                      (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                  h)
                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                show __smtx_model_eval M (SmtTerm.bvnor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                  __smtx_model_eval N (SmtTerm.bvnor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                simp only [__smtx_model_eval]
                                                                                                rw [h1, h2])
                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                          · by_cases h_bvxor : op = UserOp.bvxor
                                                                                            · subst op
                                                                                              exact substFalse_eval_binary_op UserOp.bvxor x1 a xs ss bvs
                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                hFTrans hSubstTrans
                                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvxor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                (fun {s t} h =>
                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                    (eoOp := UserOp.bvxor) (smtOp := SmtTerm.bvxor)
                                                                                                    (by rfl)
                                                                                                    (fun hNN =>
                                                                                                      bv_binop_args_have_smt_translation_of_non_none
                                                                                                        (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                    h)
                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                  show __smtx_model_eval M (SmtTerm.bvxor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                    __smtx_model_eval N (SmtTerm.bvxor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                  simp only [__smtx_model_eval]
                                                                                                  rw [h1, h2])
                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                            · by_cases h_bvxnor : op = UserOp.bvxnor
                                                                                              · subst op
                                                                                                exact substFalse_eval_binary_op UserOp.bvxnor x1 a xs ss bvs
                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                  hFTrans hSubstTrans
                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.bvxnor xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                  (fun {s t} h =>
                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                      (eoOp := UserOp.bvxnor) (smtOp := SmtTerm.bvxnor)
                                                                                                      (by rfl)
                                                                                                      (fun hNN =>
                                                                                                        bv_binop_args_have_smt_translation_of_non_none
                                                                                                          (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                      h)
                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                    show __smtx_model_eval M (SmtTerm.bvxnor (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                      __smtx_model_eval N (SmtTerm.bvxnor (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                    simp only [__smtx_model_eval]
                                                                                                    rw [h1, h2])
                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                              · by_cases h_bvcomp : op = UserOp.bvcomp
                                                                                                · subst op
                                                                                                  exact substFalse_eval_binary_op UserOp.bvcomp x1 a xs ss bvs
                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                    hFTrans hSubstTrans
                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.bvcomp xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                    (fun {s t} h =>
                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                        (eoOp := UserOp.bvcomp) (smtOp := SmtTerm.bvcomp)
                                                                                                        (by rfl)
                                                                                                        (fun hNN =>
                                                                                                          bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                            (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                        h)
                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                      show __smtx_model_eval M (SmtTerm.bvcomp (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                        __smtx_model_eval N (SmtTerm.bvcomp (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                      simp only [__smtx_model_eval]
                                                                                                      rw [h1, h2])
                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                · by_cases h_bvadd : op = UserOp.bvadd
                                                                                                  · subst op
                                                                                                    exact substFalse_eval_binary_op UserOp.bvadd x1 a xs ss bvs
                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                      hFTrans hSubstTrans
                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.bvadd xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                      (fun {s t} h =>
                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                          (eoOp := UserOp.bvadd) (smtOp := SmtTerm.bvadd)
                                                                                                          (by rfl)
                                                                                                          (fun hNN =>
                                                                                                            bv_binop_args_have_smt_translation_of_non_none
                                                                                                              (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                          h)
                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                        show __smtx_model_eval M (SmtTerm.bvadd (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                          __smtx_model_eval N (SmtTerm.bvadd (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                        simp only [__smtx_model_eval]
                                                                                                        rw [h1, h2])
                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                  · by_cases h_bvmul : op = UserOp.bvmul
                                                                                                    · subst op
                                                                                                      exact substFalse_eval_binary_op UserOp.bvmul x1 a xs ss bvs
                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                        hFTrans hSubstTrans
                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvmul xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                        (fun {s t} h =>
                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                            (eoOp := UserOp.bvmul) (smtOp := SmtTerm.bvmul)
                                                                                                            (by rfl)
                                                                                                            (fun hNN =>
                                                                                                              bv_binop_args_have_smt_translation_of_non_none
                                                                                                                (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                            h)
                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                          show __smtx_model_eval M (SmtTerm.bvmul (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                            __smtx_model_eval N (SmtTerm.bvmul (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                          simp only [__smtx_model_eval]
                                                                                                          rw [h1, h2])
                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                    · by_cases h_bvudiv : op = UserOp.bvudiv
                                                                                                      · subst op
                                                                                                        exact substFalse_eval_binary_op UserOp.bvudiv x1 a xs ss bvs
                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                          hFTrans hSubstTrans
                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.bvudiv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                          (fun {s t} h =>
                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                              (eoOp := UserOp.bvudiv) (smtOp := SmtTerm.bvudiv)
                                                                                                              (by rfl)
                                                                                                              (fun hNN =>
                                                                                                                bv_binop_args_have_smt_translation_of_non_none
                                                                                                                  (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                              h)
                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                            show __smtx_model_eval M (SmtTerm.bvudiv (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                              __smtx_model_eval N (SmtTerm.bvudiv (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                            simp only [__smtx_model_eval]
                                                                                                            rw [h1, h2])
                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                      · by_cases h_bvurem : op = UserOp.bvurem
                                                                                                        · subst op
                                                                                                          exact substFalse_eval_binary_op UserOp.bvurem x1 a xs ss bvs
                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                            hFTrans hSubstTrans
                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.bvurem xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                            (fun {s t} h =>
                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                (eoOp := UserOp.bvurem) (smtOp := SmtTerm.bvurem)
                                                                                                                (by rfl)
                                                                                                                (fun hNN =>
                                                                                                                  bv_binop_args_have_smt_translation_of_non_none
                                                                                                                    (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                h)
                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                              show __smtx_model_eval M (SmtTerm.bvurem (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                __smtx_model_eval N (SmtTerm.bvurem (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                              simp only [__smtx_model_eval]
                                                                                                              rw [h1, h2])
                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                        · by_cases h_bvsub : op = UserOp.bvsub
                                                                                                          · subst op
                                                                                                            exact substFalse_eval_binary_op UserOp.bvsub x1 a xs ss bvs
                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                              hFTrans hSubstTrans
                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvsub xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                              (fun {s t} h =>
                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                  (eoOp := UserOp.bvsub) (smtOp := SmtTerm.bvsub)
                                                                                                                  (by rfl)
                                                                                                                  (fun hNN =>
                                                                                                                    bv_binop_args_have_smt_translation_of_non_none
                                                                                                                      (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                  h)
                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                show __smtx_model_eval M (SmtTerm.bvsub (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                  __smtx_model_eval N (SmtTerm.bvsub (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                simp only [__smtx_model_eval]
                                                                                                                rw [h1, h2])
                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                          · by_cases h_bvsdiv : op = UserOp.bvsdiv
                                                                                                            · subst op
                                                                                                              exact substFalse_eval_binary_op UserOp.bvsdiv x1 a xs ss bvs
                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                hFTrans hSubstTrans
                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvsdiv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                (fun {s t} h =>
                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                    (eoOp := UserOp.bvsdiv) (smtOp := SmtTerm.bvsdiv)
                                                                                                                    (by rfl)
                                                                                                                    (fun hNN =>
                                                                                                                      bv_binop_args_have_smt_translation_of_non_none
                                                                                                                        (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                    h)
                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                  show __smtx_model_eval M (SmtTerm.bvsdiv (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                    __smtx_model_eval N (SmtTerm.bvsdiv (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                  rw [h1, h2])
                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                            · by_cases h_bvsrem : op = UserOp.bvsrem
                                                                                                              · subst op
                                                                                                                exact substFalse_eval_binary_op UserOp.bvsrem x1 a xs ss bvs
                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                  hFTrans hSubstTrans
                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.bvsrem xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                  (fun {s t} h =>
                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                      (eoOp := UserOp.bvsrem) (smtOp := SmtTerm.bvsrem)
                                                                                                                      (by rfl)
                                                                                                                      (fun hNN =>
                                                                                                                        bv_binop_args_have_smt_translation_of_non_none
                                                                                                                          (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                      h)
                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                    show __smtx_model_eval M (SmtTerm.bvsrem (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                      __smtx_model_eval N (SmtTerm.bvsrem (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                    rw [h1, h2])
                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                              · by_cases h_bvsmod : op = UserOp.bvsmod
                                                                                                                · subst op
                                                                                                                  exact substFalse_eval_binary_op UserOp.bvsmod x1 a xs ss bvs
                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                    hFTrans hSubstTrans
                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.bvsmod xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                    (fun {s t} h =>
                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                        (eoOp := UserOp.bvsmod) (smtOp := SmtTerm.bvsmod)
                                                                                                                        (by rfl)
                                                                                                                        (fun hNN =>
                                                                                                                          bv_binop_args_have_smt_translation_of_non_none
                                                                                                                            (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                        h)
                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                      show __smtx_model_eval M (SmtTerm.bvsmod (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                        __smtx_model_eval N (SmtTerm.bvsmod (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                      rw [h1, h2])
                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                · by_cases h_bvshl : op = UserOp.bvshl
                                                                                                                  · subst op
                                                                                                                    exact substFalse_eval_binary_op UserOp.bvshl x1 a xs ss bvs
                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                      hFTrans hSubstTrans
                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.bvshl xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                      (fun {s t} h =>
                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                          (eoOp := UserOp.bvshl) (smtOp := SmtTerm.bvshl)
                                                                                                                          (by rfl)
                                                                                                                          (fun hNN =>
                                                                                                                            bv_binop_args_have_smt_translation_of_non_none
                                                                                                                              (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                          h)
                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                        show __smtx_model_eval M (SmtTerm.bvshl (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                          __smtx_model_eval N (SmtTerm.bvshl (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                        rw [h1, h2])
                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                  · by_cases h_bvlshr : op = UserOp.bvlshr
                                                                                                                    · subst op
                                                                                                                      exact substFalse_eval_binary_op UserOp.bvlshr x1 a xs ss bvs
                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                        hFTrans hSubstTrans
                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvlshr xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                        (fun {s t} h =>
                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                            (eoOp := UserOp.bvlshr) (smtOp := SmtTerm.bvlshr)
                                                                                                                            (by rfl)
                                                                                                                            (fun hNN =>
                                                                                                                              bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                            h)
                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                          show __smtx_model_eval M (SmtTerm.bvlshr (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                            __smtx_model_eval N (SmtTerm.bvlshr (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                          rw [h1, h2])
                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                    · by_cases h_bvashr : op = UserOp.bvashr
                                                                                                                      · subst op
                                                                                                                        exact substFalse_eval_binary_op UserOp.bvashr x1 a xs ss bvs
                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                          hFTrans hSubstTrans
                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.bvashr xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                          (fun {s t} h =>
                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                              (eoOp := UserOp.bvashr) (smtOp := SmtTerm.bvashr)
                                                                                                                              (by rfl)
                                                                                                                              (fun hNN =>
                                                                                                                                bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                  (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                              h)
                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                            show __smtx_model_eval M (SmtTerm.bvashr (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                              __smtx_model_eval N (SmtTerm.bvashr (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                            rw [h1, h2])
                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                      · by_cases h_bvult : op = UserOp.bvult
                                                                                                                        · subst op
                                                                                                                          exact substFalse_eval_binary_op UserOp.bvult x1 a xs ss bvs
                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                            hFTrans hSubstTrans
                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.bvult xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                            (fun {s t} h =>
                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                (eoOp := UserOp.bvult) (smtOp := SmtTerm.bvult)
                                                                                                                                (by rfl)
                                                                                                                                (fun hNN =>
                                                                                                                                  bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                    (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                h)
                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                              show __smtx_model_eval M (SmtTerm.bvult (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                __smtx_model_eval N (SmtTerm.bvult (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                              rw [h1, h2])
                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                        · by_cases h_bvule : op = UserOp.bvule
                                                                                                                          · subst op
                                                                                                                            exact substFalse_eval_binary_op UserOp.bvule x1 a xs ss bvs
                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                              hFTrans hSubstTrans
                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvule xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                              (fun {s t} h =>
                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                  (eoOp := UserOp.bvule) (smtOp := SmtTerm.bvule)
                                                                                                                                  (by rfl)
                                                                                                                                  (fun hNN =>
                                                                                                                                    bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                      (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                  h)
                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                show __smtx_model_eval M (SmtTerm.bvule (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                  __smtx_model_eval N (SmtTerm.bvule (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                rw [h1, h2])
                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                          · by_cases h_bvugt : op = UserOp.bvugt
                                                                                                                            · subst op
                                                                                                                              exact substFalse_eval_binary_op UserOp.bvugt x1 a xs ss bvs
                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                hFTrans hSubstTrans
                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvugt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                (fun {s t} h =>
                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                    (eoOp := UserOp.bvugt) (smtOp := SmtTerm.bvugt)
                                                                                                                                    (by rfl)
                                                                                                                                    (fun hNN =>
                                                                                                                                      bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                        (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                    h)
                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                  show __smtx_model_eval M (SmtTerm.bvugt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                    __smtx_model_eval N (SmtTerm.bvugt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                  rw [h1, h2])
                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                            · by_cases h_bvuge : op = UserOp.bvuge
                                                                                                                              · subst op
                                                                                                                                exact substFalse_eval_binary_op UserOp.bvuge x1 a xs ss bvs
                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.bvuge xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                  (fun {s t} h =>
                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                      (eoOp := UserOp.bvuge) (smtOp := SmtTerm.bvuge)
                                                                                                                                      (by rfl)
                                                                                                                                      (fun hNN =>
                                                                                                                                        bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                          (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                      h)
                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                    show __smtx_model_eval M (SmtTerm.bvuge (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                      __smtx_model_eval N (SmtTerm.bvuge (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                    rw [h1, h2])
                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                              · by_cases h_bvslt : op = UserOp.bvslt
                                                                                                                                · subst op
                                                                                                                                  exact substFalse_eval_binary_op UserOp.bvslt x1 a xs ss bvs
                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.bvslt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                    (fun {s t} h =>
                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                        (eoOp := UserOp.bvslt) (smtOp := SmtTerm.bvslt)
                                                                                                                                        (by rfl)
                                                                                                                                        (fun hNN =>
                                                                                                                                          bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                            (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                        h)
                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                      show __smtx_model_eval M (SmtTerm.bvslt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                        __smtx_model_eval N (SmtTerm.bvslt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                      rw [h1, h2])
                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                · by_cases h_bvsle : op = UserOp.bvsle
                                                                                                                                  · subst op
                                                                                                                                    exact substFalse_eval_binary_op UserOp.bvsle x1 a xs ss bvs
                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.bvsle xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                      (fun {s t} h =>
                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                          (eoOp := UserOp.bvsle) (smtOp := SmtTerm.bvsle)
                                                                                                                                          (by rfl)
                                                                                                                                          (fun hNN =>
                                                                                                                                            bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                              (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                          h)
                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                        show __smtx_model_eval M (SmtTerm.bvsle (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                          __smtx_model_eval N (SmtTerm.bvsle (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                        rw [h1, h2])
                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                  · by_cases h_bvsgt : op = UserOp.bvsgt
                                                                                                                                    · subst op
                                                                                                                                      exact substFalse_eval_binary_op UserOp.bvsgt x1 a xs ss bvs
                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvsgt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                        (fun {s t} h =>
                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                            (eoOp := UserOp.bvsgt) (smtOp := SmtTerm.bvsgt)
                                                                                                                                            (by rfl)
                                                                                                                                            (fun hNN =>
                                                                                                                                              bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                            h)
                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                          show __smtx_model_eval M (SmtTerm.bvsgt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                            __smtx_model_eval N (SmtTerm.bvsgt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                          rw [h1, h2])
                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                    · by_cases h_bvsge : op = UserOp.bvsge
                                                                                                                                      · subst op
                                                                                                                                        exact substFalse_eval_binary_op UserOp.bvsge x1 a xs ss bvs
                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.bvsge xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                          (fun {s t} h =>
                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                              (eoOp := UserOp.bvsge) (smtOp := SmtTerm.bvsge)
                                                                                                                                              (by rfl)
                                                                                                                                              (fun hNN =>
                                                                                                                                                bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                  (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                              h)
                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                            show __smtx_model_eval M (SmtTerm.bvsge (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                              __smtx_model_eval N (SmtTerm.bvsge (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                            rw [h1, h2])
                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                      · by_cases h_bvuaddo : op = UserOp.bvuaddo
                                                                                                                                        · subst op
                                                                                                                                          exact substFalse_eval_binary_op UserOp.bvuaddo x1 a xs ss bvs
                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.bvuaddo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                            (fun {s t} h =>
                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                (eoOp := UserOp.bvuaddo) (smtOp := SmtTerm.bvuaddo)
                                                                                                                                                (by rfl)
                                                                                                                                                (fun hNN =>
                                                                                                                                                  bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                    (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                h)
                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                              show __smtx_model_eval M (SmtTerm.bvuaddo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                __smtx_model_eval N (SmtTerm.bvuaddo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                              rw [h1, h2])
                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                        · by_cases h_bvsaddo : op = UserOp.bvsaddo
                                                                                                                                          · subst op
                                                                                                                                            exact substFalse_eval_binary_op UserOp.bvsaddo x1 a xs ss bvs
                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.bvsaddo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                              (fun {s t} h =>
                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                  (eoOp := UserOp.bvsaddo) (smtOp := SmtTerm.bvsaddo)
                                                                                                                                                  (by rfl)
                                                                                                                                                  (fun hNN =>
                                                                                                                                                    bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                      (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                  h)
                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                show __smtx_model_eval M (SmtTerm.bvsaddo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                  __smtx_model_eval N (SmtTerm.bvsaddo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                rw [h1, h2])
                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                          · by_cases h_bvumulo : op = UserOp.bvumulo
                                                                                                                                            · subst op
                                                                                                                                              exact substFalse_eval_binary_op UserOp.bvumulo x1 a xs ss bvs
                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.bvumulo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                (fun {s t} h =>
                                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                    (eoOp := UserOp.bvumulo) (smtOp := SmtTerm.bvumulo)
                                                                                                                                                    (by rfl)
                                                                                                                                                    (fun hNN =>
                                                                                                                                                      bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                        (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                    h)
                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                  show __smtx_model_eval M (SmtTerm.bvumulo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                    __smtx_model_eval N (SmtTerm.bvumulo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                  rw [h1, h2])
                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                            · by_cases h_bvsmulo : op = UserOp.bvsmulo
                                                                                                                                              · subst op
                                                                                                                                                exact substFalse_eval_binary_op UserOp.bvsmulo x1 a xs ss bvs
                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.bvsmulo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                  (fun {s t} h =>
                                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                      (eoOp := UserOp.bvsmulo) (smtOp := SmtTerm.bvsmulo)
                                                                                                                                                      (by rfl)
                                                                                                                                                      (fun hNN =>
                                                                                                                                                        bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                          (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                      h)
                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                    show __smtx_model_eval M (SmtTerm.bvsmulo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                      __smtx_model_eval N (SmtTerm.bvsmulo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                    rw [h1, h2])
                                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                              · by_cases h_bvusubo : op = UserOp.bvusubo
                                                                                                                                                · subst op
                                                                                                                                                  exact substFalse_eval_binary_op UserOp.bvusubo x1 a xs ss bvs
                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.bvusubo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                        (eoOp := UserOp.bvusubo) (smtOp := SmtTerm.bvusubo)
                                                                                                                                                        (by rfl)
                                                                                                                                                        (fun hNN =>
                                                                                                                                                          bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                            (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                        h)
                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                      show __smtx_model_eval M (SmtTerm.bvusubo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                        __smtx_model_eval N (SmtTerm.bvusubo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                      rw [h1, h2])
                                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                · by_cases h_bvssubo : op = UserOp.bvssubo
                                                                                                                                                  · subst op
                                                                                                                                                    exact substFalse_eval_binary_op UserOp.bvssubo x1 a xs ss bvs
                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.bvssubo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                          (eoOp := UserOp.bvssubo) (smtOp := SmtTerm.bvssubo)
                                                                                                                                                          (by rfl)
                                                                                                                                                          (fun hNN =>
                                                                                                                                                            bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                              (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                          h)
                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                        show __smtx_model_eval M (SmtTerm.bvssubo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                          __smtx_model_eval N (SmtTerm.bvssubo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                        rw [h1, h2])
                                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                  · by_cases h_bvsdivo : op = UserOp.bvsdivo
                                                                                                                                                    · subst op
                                                                                                                                                      exact substFalse_eval_binary_op UserOp.bvsdivo x1 a xs ss bvs
                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.bvsdivo xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                            (eoOp := UserOp.bvsdivo) (smtOp := SmtTerm.bvsdivo)
                                                                                                                                                            (by rfl)
                                                                                                                                                            (fun hNN =>
                                                                                                                                                              bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                (by rw [__smtx_typeof.eq_def]) hNN)
                                                                                                                                                            h)
                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                          show __smtx_model_eval M (SmtTerm.bvsdivo (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                            __smtx_model_eval N (SmtTerm.bvsdivo (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                          rw [h1, h2])
                                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                    · by_cases h_bvultbv : op = UserOp.bvultbv
                                                                                                                                                      · subst op
                                                                                                                                                        exact substFalse_eval_binary_op UserOp.bvultbv x1 a xs ss bvs
                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.bvultbv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                          (fun {s t} h => bvultbv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                            show __smtx_model_eval M
                                                                                                                                                                (SmtTerm.ite (SmtTerm.bvult (__eo_to_smt X1) (__eo_to_smt X2))
                                                                                                                                                                  (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
                                                                                                                                                              __smtx_model_eval N
                                                                                                                                                                (SmtTerm.ite (SmtTerm.bvult (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                  (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                            rw [h1, h2])
                                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                      · by_cases h_bvsltbv : op = UserOp.bvsltbv
                                                                                                                                                        · subst op
                                                                                                                                                          exact substFalse_eval_binary_op UserOp.bvsltbv x1 a xs ss bvs
                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.bvsltbv xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                            (fun {s t} h => bvsltbv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                              show __smtx_model_eval M
                                                                                                                                                                  (SmtTerm.ite (SmtTerm.bvslt (__eo_to_smt X1) (__eo_to_smt X2))
                                                                                                                                                                    (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0)) =
                                                                                                                                                                __smtx_model_eval N
                                                                                                                                                                  (SmtTerm.ite (SmtTerm.bvslt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                    (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                              rw [h1, h2])
                                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                        · by_cases h_from_bools : op = UserOp._at_from_bools
                                                                                                                                                          · subst op
                                                                                                                                                            exact substFalse_eval_binary_op UserOp._at_from_bools x1 a xs ss bvs
                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp._at_from_bools xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                              (fun {s t} h => from_bools_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                show __smtx_model_eval M
                                                                                                                                                                    (SmtTerm.concat
                                                                                                                                                                      (SmtTerm.ite (__eo_to_smt X1)
                                                                                                                                                                        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
                                                                                                                                                                      (__eo_to_smt X2)) =
                                                                                                                                                                  __smtx_model_eval N
                                                                                                                                                                    (SmtTerm.concat
                                                                                                                                                                      (SmtTerm.ite (__eo_to_smt Y1)
                                                                                                                                                                        (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
                                                                                                                                                                      (__eo_to_smt Y2))
                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                rw [h1, h2])
                                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                          · by_cases h_strings_deq_diff : op = UserOp._at_strings_deq_diff
                                                                                                                                                            · subst op
                                                                                                                                                              exact substFalse_eval_binary_op UserOp._at_strings_deq_diff x1 a xs ss bvs
                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp._at_strings_deq_diff xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                (fun {s t} h => strings_deq_diff_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                  show __smtx_model_eval M (SmtTerm.seq_diff (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                    __smtx_model_eval N (SmtTerm.seq_diff (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                                  rw [h1, h2])
                                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                            · by_cases h_strings_stoi_result : op = UserOp._at_strings_stoi_result
                                                                                                                                                              · subst op
                                                                                                                                                                exact substFalse_eval_binary_op UserOp._at_strings_stoi_result x1 a xs ss bvs
                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp._at_strings_stoi_result xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                  (fun {s t} h => strings_stoi_result_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                    show __smtx_model_eval M
                                                                                                                                                                        (SmtTerm.str_to_int
                                                                                                                                                                          (SmtTerm.str_substr (__eo_to_smt X1)
                                                                                                                                                                            (SmtTerm.Numeral 0) (__eo_to_smt X2))) =
                                                                                                                                                                      __smtx_model_eval N
                                                                                                                                                                        (SmtTerm.str_to_int
                                                                                                                                                                          (SmtTerm.str_substr (__eo_to_smt Y1)
                                                                                                                                                                            (SmtTerm.Numeral 0) (__eo_to_smt Y2)))
                                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                                    rw [h1, h2])
                                                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                              · by_cases h_str_concat : op = UserOp.str_concat
                                                                                                                                                                · subst op
                                                                                                                                                                  exact substFalse_eval_binary_op UserOp.str_concat x1 a xs ss bvs
                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.str_concat xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                        (eoOp := UserOp.str_concat) (smtOp := SmtTerm.str_concat)
                                                                                                                                                                        (by rfl)
                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                          seq_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                            (typeof_str_concat_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                        h)
                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                      show __smtx_model_eval M (SmtTerm.str_concat (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                        __smtx_model_eval N (SmtTerm.str_concat (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                                      rw [h1, h2])
                                                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                · by_cases h_str_contains : op = UserOp.str_contains
                                                                                                                                                                  · subst op
                                                                                                                                                                    exact substFalse_eval_binary_op UserOp.str_contains x1 a xs ss bvs
                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.str_contains xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                          (eoOp := UserOp.str_contains) (smtOp := SmtTerm.str_contains)
                                                                                                                                                                          (by rfl)
                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                            seq_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                              (ret := SmtType.Bool)
                                                                                                                                                                              (typeof_str_contains_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                          h)
                                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                        show __smtx_model_eval M (SmtTerm.str_contains (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                          __smtx_model_eval N (SmtTerm.str_contains (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                                        rw [h1, h2])
                                                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                  · by_cases h_str_at : op = UserOp.str_at
                                                                                                                                                                    · subst op
                                                                                                                                                                      exact substFalse_eval_binary_op UserOp.str_at x1 a xs ss bvs
                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.str_at xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                            (eoOp := UserOp.str_at) (smtOp := SmtTerm.str_at)
                                                                                                                                                                            (by rfl) str_at_args_have_smt_translation_of_non_none h)
                                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                          show __smtx_model_eval M (SmtTerm.str_at (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                            __smtx_model_eval N (SmtTerm.str_at (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                                          rw [h1, h2])
                                                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                    · by_cases h_str_prefixof : op = UserOp.str_prefixof
                                                                                                                                                                      · subst op
                                                                                                                                                                        exact substFalse_eval_binary_op UserOp.str_prefixof x1 a xs ss bvs
                                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.str_prefixof xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                          (fun {s t} h =>
                                                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                              (eoOp := UserOp.str_prefixof) (smtOp := SmtTerm.str_prefixof)
                                                                                                                                                                              (by rfl)
                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                  (ret := SmtType.Bool)
                                                                                                                                                                                  (typeof_str_prefixof_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                              h)
                                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                            show __smtx_model_eval M (SmtTerm.str_prefixof (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                              __smtx_model_eval N (SmtTerm.str_prefixof (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                                            rw [h1, h2])
                                                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                      · by_cases h_str_suffixof : op = UserOp.str_suffixof
                                                                                                                                                                        · subst op
                                                                                                                                                                          exact substFalse_eval_binary_op UserOp.str_suffixof x1 a xs ss bvs
                                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.str_suffixof xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                            (fun {s t} h =>
                                                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                (eoOp := UserOp.str_suffixof) (smtOp := SmtTerm.str_suffixof)
                                                                                                                                                                                (by rfl)
                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                  seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                    (ret := SmtType.Bool)
                                                                                                                                                                                    (typeof_str_suffixof_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                h)
                                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                              show __smtx_model_eval M (SmtTerm.str_suffixof (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                __smtx_model_eval N (SmtTerm.str_suffixof (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                                              rw [h1, h2])
                                                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                        · by_cases h_str_lt : op = UserOp.str_lt
                                                                                                                                                                          · subst op
                                                                                                                                                                            exact substFalse_eval_binary_op UserOp.str_lt x1 a xs ss bvs
                                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.str_lt xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                              (fun {s t} h =>
                                                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                  (eoOp := UserOp.str_lt) (smtOp := SmtTerm.str_lt)
                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                    seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                      (ret := SmtType.Bool)
                                                                                                                                                                                      (typeof_str_lt_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                  h)
                                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                show __smtx_model_eval M (SmtTerm.str_lt (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                  __smtx_model_eval N (SmtTerm.str_lt (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                                rw [h1, h2])
                                                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                          · by_cases h_str_leq : op = UserOp.str_leq
                                                                                                                                                                            · subst op
                                                                                                                                                                              exact substFalse_eval_binary_op UserOp.str_leq x1 a xs ss bvs
                                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.str_leq xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                (fun {s t} h =>
                                                                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                    (eoOp := UserOp.str_leq) (smtOp := SmtTerm.str_leq)
                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                      seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                        (ret := SmtType.Bool)
                                                                                                                                                                                        (typeof_str_leq_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                    h)
                                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                  show __smtx_model_eval M (SmtTerm.str_leq (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                    __smtx_model_eval N (SmtTerm.str_leq (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                                                  rw [h1, h2])
                                                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                            · by_cases h_re_range : op = UserOp.re_range
                                                                                                                                                                              · subst op
                                                                                                                                                                                exact substFalse_eval_binary_op UserOp.re_range x1 a xs ss bvs
                                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.re_range xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                  (fun {s t} h =>
                                                                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                      (eoOp := UserOp.re_range) (smtOp := SmtTerm.re_range)
                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                        seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                          (ret := SmtType.RegLan)
                                                                                                                                                                                          (typeof_re_range_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                      h)
                                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                    show __smtx_model_eval M (SmtTerm.re_range (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                      __smtx_model_eval N (SmtTerm.re_range (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                                                    rw [h1, h2])
                                                                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                              · by_cases h_re_concat : op = UserOp.re_concat
                                                                                                                                                                                · subst op
                                                                                                                                                                                  exact substFalse_eval_binary_op UserOp.re_concat x1 a xs ss bvs
                                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.re_concat xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                        (eoOp := UserOp.re_concat) (smtOp := SmtTerm.re_concat)
                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                          reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                            (typeof_re_concat_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                        h)
                                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                      show __smtx_model_eval M (SmtTerm.re_concat (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                        __smtx_model_eval N (SmtTerm.re_concat (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                                                      rw [h1, h2])
                                                                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                · by_cases h_re_inter : op = UserOp.re_inter
                                                                                                                                                                                  · subst op
                                                                                                                                                                                    exact substFalse_eval_binary_op UserOp.re_inter x1 a xs ss bvs
                                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.re_inter xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                          (eoOp := UserOp.re_inter) (smtOp := SmtTerm.re_inter)
                                                                                                                                                                                          (by rfl)
                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                            reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                              (typeof_re_inter_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                          h)
                                                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                        show __smtx_model_eval M (SmtTerm.re_inter (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                          __smtx_model_eval N (SmtTerm.re_inter (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                                                        rw [h1, h2])
                                                                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                  · by_cases h_re_union : op = UserOp.re_union
                                                                                                                                                                                    · subst op
                                                                                                                                                                                      exact substFalse_eval_binary_op UserOp.re_union x1 a xs ss bvs
                                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.re_union xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                            (eoOp := UserOp.re_union) (smtOp := SmtTerm.re_union)
                                                                                                                                                                                            (by rfl)
                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                              reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                (typeof_re_union_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                            h)
                                                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                          show __smtx_model_eval M (SmtTerm.re_union (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                            __smtx_model_eval N (SmtTerm.re_union (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                                                          rw [h1, h2])
                                                                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                    · by_cases h_re_diff : op = UserOp.re_diff
                                                                                                                                                                                      · subst op
                                                                                                                                                                                        exact substFalse_eval_binary_op UserOp.re_diff x1 a xs ss bvs
                                                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp.re_diff xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                          (fun {s t} h =>
                                                                                                                                                                                            apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                              (eoOp := UserOp.re_diff) (smtOp := SmtTerm.re_diff)
                                                                                                                                                                                              (by rfl)
                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                  (typeof_re_diff_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                              h)
                                                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                            show __smtx_model_eval M (SmtTerm.re_diff (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                              __smtx_model_eval N (SmtTerm.re_diff (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                            simp only [__smtx_model_eval]
                                                                                                                                                                                            rw [h1, h2])
                                                                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                      · by_cases h_str_in_re : op = UserOp.str_in_re
                                                                                                                                                                                        · subst op
                                                                                                                                                                                          exact substFalse_eval_binary_op UserOp.str_in_re x1 a xs ss bvs
                                                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp.str_in_re xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                            (fun {s t} h =>
                                                                                                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                (eoOp := UserOp.str_in_re) (smtOp := SmtTerm.str_in_re)
                                                                                                                                                                                                (by rfl)
                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                  seq_char_reglan_args_have_smt_translation_of_non_none
                                                                                                                                                                                                    (ret := SmtType.Bool)
                                                                                                                                                                                                    (typeof_str_in_re_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                h)
                                                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                              show __smtx_model_eval M (SmtTerm.str_in_re (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                __smtx_model_eval N (SmtTerm.str_in_re (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                              simp only [__smtx_model_eval]
                                                                                                                                                                                              rw [h1, h2])
                                                                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                        · by_cases h_seq_nth : op = UserOp.seq_nth
                                                                                                                                                                                          · subst op
                                                                                                                                                                                            exact substFalse_eval_binary_op UserOp.seq_nth x1 a xs ss bvs
                                                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp.seq_nth xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                              (fun {s t} h =>
                                                                                                                                                                                                apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                  (eoOp := UserOp.seq_nth) (smtOp := SmtTerm.seq_nth)
                                                                                                                                                                                                  (by rfl) seq_nth_args_have_smt_translation_of_non_none h)
                                                                                                                                                                                              (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                show __smtx_model_eval M (SmtTerm.seq_nth (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                  __smtx_model_eval N (SmtTerm.seq_nth (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                simp only [__smtx_model_eval]
                                                                                                                                                                                                rw [h1, h2, smtx_seq_nth_eq_of_globals hRel.globals])
                                                                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                          · by_cases h_set_union : op = UserOp.set_union
                                                                                                                                                                                            · subst op
                                                                                                                                                                                              exact substFalse_eval_binary_op UserOp.set_union x1 a xs ss bvs
                                                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp.set_union xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                (fun {s t} h =>
                                                                                                                                                                                                  apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                    (eoOp := UserOp.set_union) (smtOp := SmtTerm.set_union)
                                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                      set_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                        (typeof_set_union_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                    h)
                                                                                                                                                                                                (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                  show __smtx_model_eval M (SmtTerm.set_union (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                    __smtx_model_eval N (SmtTerm.set_union (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                  simp only [__smtx_model_eval]
                                                                                                                                                                                                  rw [h1, h2])
                                                                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                            · by_cases h_set_inter : op = UserOp.set_inter
                                                                                                                                                                                              · subst op
                                                                                                                                                                                                exact substFalse_eval_binary_op UserOp.set_inter x1 a xs ss bvs
                                                                                                                                                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                  hFTrans hSubstTrans
                                                                                                                                                                                                  (substitute_simul_rec_uop_eq_self UserOp.set_inter xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                  (fun {s t} h =>
                                                                                                                                                                                                    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                      (eoOp := UserOp.set_inter) (smtOp := SmtTerm.set_inter)
                                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                                        set_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                          (typeof_set_inter_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                      h)
                                                                                                                                                                                                  (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                    show __smtx_model_eval M (SmtTerm.set_inter (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                      __smtx_model_eval N (SmtTerm.set_inter (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                    simp only [__smtx_model_eval]
                                                                                                                                                                                                    rw [h1, h2])
                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                              · by_cases h_set_minus : op = UserOp.set_minus
                                                                                                                                                                                                · subst op
                                                                                                                                                                                                  exact substFalse_eval_binary_op UserOp.set_minus x1 a xs ss bvs
                                                                                                                                                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                    hFTrans hSubstTrans
                                                                                                                                                                                                    (substitute_simul_rec_uop_eq_self UserOp.set_minus xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                    (fun {s t} h =>
                                                                                                                                                                                                      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                        (eoOp := UserOp.set_minus) (smtOp := SmtTerm.set_minus)
                                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                                          set_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                            (typeof_set_minus_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                        h)
                                                                                                                                                                                                    (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                      show __smtx_model_eval M (SmtTerm.set_minus (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                        __smtx_model_eval N (SmtTerm.set_minus (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                      simp only [__smtx_model_eval]
                                                                                                                                                                                                      rw [h1, h2])
                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                · by_cases h_set_member : op = UserOp.set_member
                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                    exact substFalse_eval_binary_op UserOp.set_member x1 a xs ss bvs
                                                                                                                                                                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                      hFTrans hSubstTrans
                                                                                                                                                                                                      (substitute_simul_rec_uop_eq_self UserOp.set_member xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                      (fun {s t} h =>
                                                                                                                                                                                                        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                          (eoOp := UserOp.set_member) (smtOp := SmtTerm.set_member)
                                                                                                                                                                                                          (by rfl) set_member_args_have_smt_translation_of_non_none h)
                                                                                                                                                                                                      (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                        show __smtx_model_eval M (SmtTerm.set_member (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                          __smtx_model_eval N (SmtTerm.set_member (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                        simp only [__smtx_model_eval]
                                                                                                                                                                                                        rw [h1, h2])
                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                  · by_cases h_set_subset : op = UserOp.set_subset
                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                      exact substFalse_eval_binary_op UserOp.set_subset x1 a xs ss bvs
                                                                                                                                                                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                        hFTrans hSubstTrans
                                                                                                                                                                                                        (substitute_simul_rec_uop_eq_self UserOp.set_subset xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                        (fun {s t} h =>
                                                                                                                                                                                                          apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                                                                                                            (eoOp := UserOp.set_subset) (smtOp := SmtTerm.set_subset)
                                                                                                                                                                                                            (by rfl)
                                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                                              set_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                (ret := SmtType.Bool)
                                                                                                                                                                                                                (typeof_set_subset_eq (__eo_to_smt s) (__eo_to_smt t)) hNN)
                                                                                                                                                                                                            h)
                                                                                                                                                                                                        (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                          show __smtx_model_eval M (SmtTerm.set_subset (__eo_to_smt X1) (__eo_to_smt X2)) =
                                                                                                                                                                                                            __smtx_model_eval N (SmtTerm.set_subset (__eo_to_smt Y1) (__eo_to_smt Y2))
                                                                                                                                                                                                          simp only [__smtx_model_eval]
                                                                                                                                                                                                          rw [h1, h2])
                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                    · by_cases h_strings_itos_result : op = UserOp._at_strings_itos_result
                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                        exact substFalse_eval_binary_op UserOp._at_strings_itos_result x1 a xs ss bvs
                                                                                                                                                                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                          hFTrans hSubstTrans
                                                                                                                                                                                                          (substitute_simul_rec_uop_eq_self UserOp._at_strings_itos_result xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                          (fun {s t} h => strings_itos_result_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                          (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                            show __smtx_model_eval M
                                                                                                                                                                                                                (SmtTerm.mod (__eo_to_smt X1)
                                                                                                                                                                                                                  (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt X2))) =
                                                                                                                                                                                                              __smtx_model_eval N
                                                                                                                                                                                                                (SmtTerm.mod (__eo_to_smt Y1)
                                                                                                                                                                                                                  (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt Y2)))
                                                                                                                                                                                                            simp [__smtx_model_eval, h1, h2,
                                                                                                                                                                                                              smtx_model_eval_apply_eq_of_globals hRel.globals,
                                                                                                                                                                                                              hRel.globals.1])
                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                      · by_cases h_strings_num_occur : op = UserOp._at_strings_num_occur
                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                          exact substFalse_eval_binary_op UserOp._at_strings_num_occur x1 a xs ss bvs
                                                                                                                                                                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                            hFTrans hSubstTrans
                                                                                                                                                                                                            (substitute_simul_rec_uop_eq_self UserOp._at_strings_num_occur xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                            (fun {s t} h => strings_num_occur_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                            (fun X1 Y1 X2 Y2 h1 h2 => by
                                                                                                                                                                                                              show __smtx_model_eval M
                                                                                                                                                                                                                  (SmtTerm.div
                                                                                                                                                                                                                    (SmtTerm.neg
                                                                                                                                                                                                                      (SmtTerm.str_len (__eo_to_smt X1))
                                                                                                                                                                                                                      (SmtTerm.str_len
                                                                                                                                                                                                                        (SmtTerm.str_replace_all (__eo_to_smt X1) (__eo_to_smt X2)
                                                                                                                                                                                                                          (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
                                                                                                                                                                                                                    (SmtTerm.str_len (__eo_to_smt X2))) =
                                                                                                                                                                                                                __smtx_model_eval N
                                                                                                                                                                                                                  (SmtTerm.div
                                                                                                                                                                                                                    (SmtTerm.neg
                                                                                                                                                                                                                      (SmtTerm.str_len (__eo_to_smt Y1))
                                                                                                                                                                                                                      (SmtTerm.str_len
                                                                                                                                                                                                                        (SmtTerm.str_replace_all (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                                                                                                                                                                          (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
                                                                                                                                                                                                                    (SmtTerm.str_len (__eo_to_smt Y2)))
                                                                                                                                                                                                              simp [__smtx_model_eval, h1, h2,
                                                                                                                                                                                                                smtx_model_eval_apply_eq_of_globals hRel.globals,
                                                                                                                                                                                                                hRel.globals.1])
                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                        · by_cases h_array_deq_diff : op = UserOp._at_array_deq_diff
                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                            exact substFalse_eval_binary_op_with_app_trans UserOp._at_array_deq_diff x1 a xs ss bvs
                                                                                                                                                                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                              hFTrans hSubstTrans
                                                                                                                                                                                                              (substitute_simul_rec_uop_eq_self UserOp._at_array_deq_diff xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                              (fun {s t} h => array_deq_diff_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                              (fun X1 Y1 X2 Y2 hSubApp hOrigApp h1 h2 => by
                                                                                                                                                                                                                unfold eoHasSmtTranslation at hSubApp hOrigApp
                                                                                                                                                                                                                change
                                                                                                                                                                                                                    __smtx_model_eval M
                                                                                                                                                                                                                        (__eo_to_smt_array_deq_diff (__eo_to_smt X1)
                                                                                                                                                                                                                          (__smtx_typeof (__eo_to_smt X1))
                                                                                                                                                                                                                          (__eo_to_smt X2)
                                                                                                                                                                                                                          (__smtx_typeof (__eo_to_smt X2))) =
                                                                                                                                                                                                                      __smtx_model_eval N
                                                                                                                                                                                                                        (__eo_to_smt_array_deq_diff (__eo_to_smt Y1)
                                                                                                                                                                                                                          (__smtx_typeof (__eo_to_smt Y1))
                                                                                                                                                                                                                          (__eo_to_smt Y2)
                                                                                                                                                                                                                          (__smtx_typeof (__eo_to_smt Y2)))
                                                                                                                                                                                                                change
                                                                                                                                                                                                                    __smtx_typeof
                                                                                                                                                                                                                        (__eo_to_smt_array_deq_diff (__eo_to_smt X1)
                                                                                                                                                                                                                          (__smtx_typeof (__eo_to_smt X1))
                                                                                                                                                                                                                          (__eo_to_smt X2)
                                                                                                                                                                                                                          (__smtx_typeof (__eo_to_smt X2))) ≠
                                                                                                                                                                                                                      SmtType.None at hSubApp
                                                                                                                                                                                                                change
                                                                                                                                                                                                                    __smtx_typeof
                                                                                                                                                                                                                        (__eo_to_smt_array_deq_diff (__eo_to_smt Y1)
                                                                                                                                                                                                                          (__smtx_typeof (__eo_to_smt Y1))
                                                                                                                                                                                                                          (__eo_to_smt Y2)
                                                                                                                                                                                                                          (__smtx_typeof (__eo_to_smt Y2))) ≠
                                                                                                                                                                                                                      SmtType.None at hOrigApp
                                                                                                                                                                                                                cases hX1Ty : __smtx_typeof (__eo_to_smt X1) <;>
                                                                                                                                                                                                                  cases hX2Ty : __smtx_typeof (__eo_to_smt X2) <;>
                                                                                                                                                                                                                  simp [__eo_to_smt_array_deq_diff, hX1Ty, hX2Ty,
                                                                                                                                                                                                                    TranslationProofs.smtx_typeof_none] at hSubApp ⊢
                                                                                                                                                                                                                case Map.Map A B C D =>
                                                                                                                                                                                                                  cases hY1Ty : __smtx_typeof (__eo_to_smt Y1) <;>
                                                                                                                                                                                                                    cases hY2Ty : __smtx_typeof (__eo_to_smt Y2) <;>
                                                                                                                                                                                                                    simp [__eo_to_smt_array_deq_diff, hY1Ty, hY2Ty,
                                                                                                                                                                                                                      TranslationProofs.smtx_typeof_none] at hOrigApp ⊢
                                                                                                                                                                                                                  case Map.Map A' B' C' D' =>
                                                                                                                                                                                                                    simp [__smtx_model_eval, h1, h2])
                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                          · by_cases h_sets_deq_diff : op = UserOp._at_sets_deq_diff
                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                              exact substFalse_eval_binary_op_with_app_trans UserOp._at_sets_deq_diff x1 a xs ss bvs
                                                                                                                                                                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                hFTrans hSubstTrans
                                                                                                                                                                                                                (substitute_simul_rec_uop_eq_self UserOp._at_sets_deq_diff xs ss bvs hXsEnv hBvsEnv hSsTrans)
                                                                                                                                                                                                                (fun {s t} h => sets_deq_diff_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                (fun X1 Y1 X2 Y2 hSubApp hOrigApp h1 h2 => by
                                                                                                                                                                                                                  unfold eoHasSmtTranslation at hSubApp hOrigApp
                                                                                                                                                                                                                  change
                                                                                                                                                                                                                      __smtx_model_eval M
                                                                                                                                                                                                                          (__eo_to_smt_sets_deq_diff (__eo_to_smt X1)
                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt X1))
                                                                                                                                                                                                                            (__eo_to_smt X2)
                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt X2))) =
                                                                                                                                                                                                                        __smtx_model_eval N
                                                                                                                                                                                                                          (__eo_to_smt_sets_deq_diff (__eo_to_smt Y1)
                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt Y1))
                                                                                                                                                                                                                            (__eo_to_smt Y2)
                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt Y2)))
                                                                                                                                                                                                                  change
                                                                                                                                                                                                                      __smtx_typeof
                                                                                                                                                                                                                          (__eo_to_smt_sets_deq_diff (__eo_to_smt X1)
                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt X1))
                                                                                                                                                                                                                            (__eo_to_smt X2)
                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt X2))) ≠
                                                                                                                                                                                                                        SmtType.None at hSubApp
                                                                                                                                                                                                                  change
                                                                                                                                                                                                                      __smtx_typeof
                                                                                                                                                                                                                          (__eo_to_smt_sets_deq_diff (__eo_to_smt Y1)
                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt Y1))
                                                                                                                                                                                                                            (__eo_to_smt Y2)
                                                                                                                                                                                                                            (__smtx_typeof (__eo_to_smt Y2))) ≠
                                                                                                                                                                                                                        SmtType.None at hOrigApp
                                                                                                                                                                                                                  cases hX1Ty : __smtx_typeof (__eo_to_smt X1) <;>
                                                                                                                                                                                                                    cases hX2Ty : __smtx_typeof (__eo_to_smt X2) <;>
                                                                                                                                                                                                                    simp [__eo_to_smt_sets_deq_diff, hX1Ty, hX2Ty,
                                                                                                                                                                                                                      TranslationProofs.smtx_typeof_none] at hSubApp ⊢
                                                                                                                                                                                                                  case Set.Set A B =>
                                                                                                                                                                                                                    cases hY1Ty : __smtx_typeof (__eo_to_smt Y1) <;>
                                                                                                                                                                                                                      cases hY2Ty : __smtx_typeof (__eo_to_smt Y2) <;>
                                                                                                                                                                                                                      simp [__eo_to_smt_sets_deq_diff, hY1Ty, hY2Ty,
                                                                                                                                                                                                                        TranslationProofs.smtx_typeof_none] at hOrigApp ⊢
                                                                                                                                                                                                                    case Set.Set A' B' =>
                                                                                                                                                                                                                      simp [__smtx_model_eval, h1, h2])
                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                                                                                                                                                            · by_cases h_forall : op = UserOp.forall
                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                exact
                                                                                                                                                                                                                  false_of_forall_non_list_has_smt_translation
                                                                                                                                                                                                                    (by
                                                                                                                                                                                                                      intro v vs hEq
                                                                                                                                                                                                                      exact hBinder ⟨Term.UOp UserOp.forall, v, vs, by rw [hEq]⟩)
                                                                                                                                                                                                                    hFTrans
                                                                                                                                                                                                              · by_cases h_exists : op = UserOp.exists
                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                  exact
                                                                                                                                                                                                                    false_of_exists_non_list_has_smt_translation
                                                                                                                                                                                                                      (by
                                                                                                                                                                                                                        intro v vs hEq
                                                                                                                                                                                                                        exact hBinder ⟨Term.UOp UserOp.exists, v, vs, by rw [hEq]⟩)
                                                                                                                                                                                                                      hFTrans
                                                                                                                                                                                                                · sorry
                                  | Apply h x0 =>
                                      cases h with
                                      | UOp op =>
                                          by_cases h_ite : op = UserOp.ite
                                          · subst op
                                            exact substFalse_eval_ternary_op UserOp.ite x0 x1 a xs ss bvs
                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                              hFTrans hSubstTrans
                                              (substitute_simul_rec_uop_eq_self UserOp.ite xs ss bvs
                                                hXsEnv hBvsEnv hSsTrans)
                                              (fun {c x y} h => ite_args_have_smt_translation_of_has_smt_translation h)
                                              (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                show __smtx_model_eval M
                                                    (SmtTerm.ite (__eo_to_smt X1) (__eo_to_smt X2) (__eo_to_smt X3)) =
                                                  __smtx_model_eval N
                                                    (SmtTerm.ite (__eo_to_smt Y1) (__eo_to_smt Y2) (__eo_to_smt Y3))
                                                simp only [__smtx_model_eval]
                                                rw [h1, h2, h3])
                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                          · by_cases h_store : op = UserOp.store
                                            · subst op
                                              exact substFalse_eval_ternary_op UserOp.store x0 x1 a xs ss bvs
                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                hFTrans hSubstTrans
                                                (substitute_simul_rec_uop_eq_self UserOp.store xs ss bvs
                                                  hXsEnv hBvsEnv hSsTrans)
                                                (fun {x y z} h => store_args_have_smt_translation_of_has_smt_translation h)
                                                (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                  show __smtx_model_eval M
                                                      (SmtTerm.store (__eo_to_smt X1) (__eo_to_smt X2) (__eo_to_smt X3)) =
                                                    __smtx_model_eval N
                                                      (SmtTerm.store (__eo_to_smt Y1) (__eo_to_smt Y2) (__eo_to_smt Y3))
                                                  simp only [__smtx_model_eval]
                                                  rw [h1, h2, h3])
                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                            · by_cases h_bvite : op = UserOp.bvite
                                              · subst op
                                                exact substFalse_eval_ternary_op UserOp.bvite x0 x1 a xs ss bvs
                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                  hFTrans hSubstTrans
                                                  (substitute_simul_rec_uop_eq_self UserOp.bvite xs ss bvs
                                                    hXsEnv hBvsEnv hSsTrans)
                                                  (fun {x y z} h => bvite_args_have_smt_translation_of_has_smt_translation h)
                                                  (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                    show __smtx_model_eval M
                                                        (SmtTerm.ite
                                                          (SmtTerm.eq (__eo_to_smt X1) (SmtTerm.Binary 1 1))
                                                          (__eo_to_smt X2) (__eo_to_smt X3)) =
                                                      __smtx_model_eval N
                                                        (SmtTerm.ite
                                                          (SmtTerm.eq (__eo_to_smt Y1) (SmtTerm.Binary 1 1))
                                                          (__eo_to_smt Y2) (__eo_to_smt Y3))
                                                    simp only [__smtx_model_eval]
                                                    rw [h1, h2, h3])
                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                              · by_cases h_str_substr : op = UserOp.str_substr
                                                · subst op
                                                  exact substFalse_eval_ternary_op UserOp.str_substr x0 x1 a xs ss bvs
                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                    hFTrans hSubstTrans
                                                    (substitute_simul_rec_uop_eq_self UserOp.str_substr xs ss bvs
                                                      hXsEnv hBvsEnv hSsTrans)
                                                    (fun {x y z} h =>
                                                      apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                        (eoOp := UserOp.str_substr) (smtOp := SmtTerm.str_substr)
                                                        (by rfl) str_substr_args_have_smt_translation_of_non_none h)
                                                    (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                      show __smtx_model_eval M
                                                          (SmtTerm.str_substr (__eo_to_smt X1) (__eo_to_smt X2)
                                                            (__eo_to_smt X3)) =
                                                        __smtx_model_eval N
                                                          (SmtTerm.str_substr (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                            (__eo_to_smt Y3))
                                                      simp only [__smtx_model_eval]
                                                      rw [h1, h2, h3])
                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                · by_cases h_str_indexof : op = UserOp.str_indexof
                                                  · subst op
                                                    exact substFalse_eval_ternary_op UserOp.str_indexof x0 x1 a xs ss bvs
                                                      hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                      hFTrans hSubstTrans
                                                      (substitute_simul_rec_uop_eq_self UserOp.str_indexof xs ss bvs
                                                        hXsEnv hBvsEnv hSsTrans)
                                                      (fun {x y z} h =>
                                                        apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                          (eoOp := UserOp.str_indexof) (smtOp := SmtTerm.str_indexof)
                                                          (by rfl) str_indexof_args_have_smt_translation_of_non_none h)
                                                      (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                        show __smtx_model_eval M
                                                            (SmtTerm.str_indexof (__eo_to_smt X1) (__eo_to_smt X2)
                                                              (__eo_to_smt X3)) =
                                                          __smtx_model_eval N
                                                            (SmtTerm.str_indexof (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                              (__eo_to_smt Y3))
                                                        simp only [__smtx_model_eval]
                                                        rw [h1, h2, h3])
                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                      (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                  · by_cases h_str_update : op = UserOp.str_update
                                                    · subst op
                                                      exact substFalse_eval_ternary_op UserOp.str_update x0 x1 a xs ss bvs
                                                        hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                        hFTrans hSubstTrans
                                                        (substitute_simul_rec_uop_eq_self UserOp.str_update xs ss bvs
                                                          hXsEnv hBvsEnv hSsTrans)
                                                        (fun {x y z} h =>
                                                          apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                            (eoOp := UserOp.str_update) (smtOp := SmtTerm.str_update)
                                                            (by rfl) str_update_args_have_smt_translation_of_non_none h)
                                                        (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                          show __smtx_model_eval M
                                                              (SmtTerm.str_update (__eo_to_smt X1) (__eo_to_smt X2)
                                                                (__eo_to_smt X3)) =
                                                            __smtx_model_eval N
                                                              (SmtTerm.str_update (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                (__eo_to_smt Y3))
                                                          simp only [__smtx_model_eval]
                                                          rw [h1, h2, h3])
                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                        (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                    · by_cases h_str_replace : op = UserOp.str_replace
                                                      · subst op
                                                        exact substFalse_eval_ternary_op UserOp.str_replace x0 x1 a xs ss bvs
                                                          hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                          hFTrans hSubstTrans
                                                          (substitute_simul_rec_uop_eq_self UserOp.str_replace xs ss bvs
                                                            hXsEnv hBvsEnv hSsTrans)
                                                          (fun {x y z} h =>
                                                            apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                              (eoOp := UserOp.str_replace) (smtOp := SmtTerm.str_replace)
                                                              (by rfl)
                                                              (fun hNN =>
                                                                seq_triop_args_have_smt_translation_of_non_none
                                                                  (typeof_str_replace_eq (__eo_to_smt x) (__eo_to_smt y)
                                                                    (__eo_to_smt z)) hNN)
                                                              h)
                                                          (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                            show __smtx_model_eval M
                                                                (SmtTerm.str_replace (__eo_to_smt X1) (__eo_to_smt X2)
                                                                  (__eo_to_smt X3)) =
                                                              __smtx_model_eval N
                                                                (SmtTerm.str_replace (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                  (__eo_to_smt Y3))
                                                            simp only [__smtx_model_eval]
                                                            rw [h1, h2, h3])
                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                          (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                      · by_cases h_str_replace_all : op = UserOp.str_replace_all
                                                        · subst op
                                                          exact substFalse_eval_ternary_op UserOp.str_replace_all x0 x1 a xs ss bvs
                                                            hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                            hFTrans hSubstTrans
                                                            (substitute_simul_rec_uop_eq_self UserOp.str_replace_all xs ss bvs
                                                              hXsEnv hBvsEnv hSsTrans)
                                                            (fun {x y z} h =>
                                                              apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                (eoOp := UserOp.str_replace_all) (smtOp := SmtTerm.str_replace_all)
                                                                (by rfl)
                                                                (fun hNN =>
                                                                  seq_triop_args_have_smt_translation_of_non_none
                                                                    (typeof_str_replace_all_eq (__eo_to_smt x) (__eo_to_smt y)
                                                                      (__eo_to_smt z)) hNN)
                                                                h)
                                                            (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                              show __smtx_model_eval M
                                                                  (SmtTerm.str_replace_all (__eo_to_smt X1) (__eo_to_smt X2)
                                                                    (__eo_to_smt X3)) =
                                                                __smtx_model_eval N
                                                                  (SmtTerm.str_replace_all (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                    (__eo_to_smt Y3))
                                                              simp only [__smtx_model_eval]
                                                              rw [h1, h2, h3])
                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                            (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                        · by_cases h_str_replace_re : op = UserOp.str_replace_re
                                                          · subst op
                                                            exact substFalse_eval_ternary_op UserOp.str_replace_re x0 x1 a xs ss bvs
                                                              hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                              hFTrans hSubstTrans
                                                              (substitute_simul_rec_uop_eq_self UserOp.str_replace_re xs ss bvs
                                                                hXsEnv hBvsEnv hSsTrans)
                                                              (fun {x y z} h =>
                                                                apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                  (eoOp := UserOp.str_replace_re) (smtOp := SmtTerm.str_replace_re)
                                                                  (by rfl)
                                                                  (fun hNN =>
                                                                    str_replace_re_args_have_smt_translation_of_non_none
                                                                      (typeof_str_replace_re_eq (__eo_to_smt x) (__eo_to_smt y)
                                                                        (__eo_to_smt z)) hNN)
                                                                  h)
                                                              (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                show __smtx_model_eval M
                                                                    (SmtTerm.str_replace_re (__eo_to_smt X1) (__eo_to_smt X2)
                                                                      (__eo_to_smt X3)) =
                                                                  __smtx_model_eval N
                                                                    (SmtTerm.str_replace_re (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                      (__eo_to_smt Y3))
                                                                simp only [__smtx_model_eval]
                                                                rw [h1, h2, h3])
                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                              (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                          · by_cases h_str_replace_re_all : op = UserOp.str_replace_re_all
                                                            · subst op
                                                              exact substFalse_eval_ternary_op UserOp.str_replace_re_all x0 x1 a xs ss bvs
                                                                hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                hFTrans hSubstTrans
                                                                (substitute_simul_rec_uop_eq_self UserOp.str_replace_re_all xs ss bvs
                                                                  hXsEnv hBvsEnv hSsTrans)
                                                                (fun {x y z} h =>
                                                                  apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                    (eoOp := UserOp.str_replace_re_all) (smtOp := SmtTerm.str_replace_re_all)
                                                                    (by rfl)
                                                                    (fun hNN =>
                                                                      str_replace_re_args_have_smt_translation_of_non_none
                                                                        (typeof_str_replace_re_all_eq (__eo_to_smt x) (__eo_to_smt y)
                                                                          (__eo_to_smt z)) hNN)
                                                                    h)
                                                                (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                  show __smtx_model_eval M
                                                                      (SmtTerm.str_replace_re_all (__eo_to_smt X1) (__eo_to_smt X2)
                                                                        (__eo_to_smt X3)) =
                                                                    __smtx_model_eval N
                                                                      (SmtTerm.str_replace_re_all (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                        (__eo_to_smt Y3))
                                                                  simp only [__smtx_model_eval]
                                                                  rw [h1, h2, h3])
                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                            · by_cases h_str_indexof_re : op = UserOp.str_indexof_re
                                                              · subst op
                                                                exact substFalse_eval_ternary_op UserOp.str_indexof_re x0 x1 a xs ss bvs
                                                                  hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                  hFTrans hSubstTrans
                                                                  (substitute_simul_rec_uop_eq_self UserOp.str_indexof_re xs ss bvs
                                                                    hXsEnv hBvsEnv hSsTrans)
                                                                  (fun {x y z} h =>
                                                                    apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                      (eoOp := UserOp.str_indexof_re) (smtOp := SmtTerm.str_indexof_re)
                                                                      (by rfl) str_indexof_re_args_have_smt_translation_of_non_none h)
                                                                  (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                    show __smtx_model_eval M
                                                                        (SmtTerm.str_indexof_re (__eo_to_smt X1) (__eo_to_smt X2)
                                                                          (__eo_to_smt X3)) =
                                                                      __smtx_model_eval N
                                                                        (SmtTerm.str_indexof_re (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                          (__eo_to_smt Y3))
                                                                    simp only [__smtx_model_eval]
                                                                    rw [h1, h2, h3])
                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                  (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                              · by_cases h_str_indexof_re_split : op = UserOp.str_indexof_re_split
                                                                · subst op
                                                                  exact substFalse_eval_ternary_op UserOp.str_indexof_re_split x0 x1 a xs ss bvs
                                                                    hisr hxs hss hbvs (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                    hFTrans hSubstTrans
                                                                    (substitute_simul_rec_uop_eq_self UserOp.str_indexof_re_split xs ss bvs
                                                                      hXsEnv hBvsEnv hSsTrans)
                                                                    (fun {x y z} h =>
                                                                      apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
                                                                        (eoOp := UserOp.str_indexof_re_split) (smtOp := SmtTerm.str_indexof_re_split)
                                                                        (by rfl) str_indexof_re_split_args_have_smt_translation_of_non_none h)
                                                                    (fun X1 Y1 X2 Y2 X3 Y3 h1 h2 h3 => by
                                                                      show __smtx_model_eval M
                                                                          (SmtTerm.str_indexof_re_split (__eo_to_smt X1) (__eo_to_smt X2)
                                                                            (__eo_to_smt X3)) =
                                                                        __smtx_model_eval N
                                                                          (SmtTerm.str_indexof_re_split (__eo_to_smt Y1) (__eo_to_smt Y2)
                                                                            (__eo_to_smt Y3))
                                                                      simp only [__smtx_model_eval]
                                                                      rw [h1, h2, h3])
                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                · exact substFalse_eval_ternary_uop_generic_apply op x0 x1 a xs ss bvs
                                                                    hisr hxs hss hbvs
                                                                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                                                    (eo_to_smt_apply_apply_apply_uop_generic_of_not_smt_triop
                                                                      h_ite h_store h_bvite h_str_substr h_str_indexof
                                                                      h_str_update h_str_replace h_str_replace_all
                                                                      h_str_replace_re h_str_replace_re_all h_str_indexof_re
                                                                      h_str_indexof_re_split)
                                                                    (eo_to_smt_apply_apply_apply_uop_generic_of_not_smt_triop
                                                                      h_ite h_store h_bvite h_str_substr h_str_indexof
                                                                      h_str_update h_str_replace h_str_replace_all
                                                                      h_str_replace_re h_str_replace_re_all h_str_indexof_re
                                                                      h_str_indexof_re_split)
                                                                    hFTrans hSubstTrans
                                                                    (substitute_simul_rec_uop_eq_self op xs ss bvs
                                                                      hXsEnv hBvsEnv hSsTrans)
                                                                    hRel.globals
                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                                                    (fun ht hst => hRecArg (by simp; try omega) ht hst)
                                      | _ =>
                                          -- ternary / generic application head
                                          sorry
                                  | _ =>
                                      -- ternary / generic application head
                                      sorry
                              | _ =>
                                  -- remaining unary `UOp` heads and atom heads
                                  -- (generic application)
                                  sorry
      case Var name S =>
          by_cases hString : ∃ s, name = Term.String s
          · rcases hString with ⟨s, rfl⟩
            exact SubstituteSupport.substFalse_eval_var M N s S xs ss bvs
              hXsEnv hBvsEnv hss hRel
          · exact false_of_non_string_var_has_smt_translation
              (fun s hEq => hString ⟨s, hEq⟩) hFTrans
      case Stuck =>
          exact False.elim
            (RuleProofs.term_ne_stuck_of_has_smt_translation Term.Stuck hFTrans rfl)
      all_goals
          exact SubstituteSupport.substFalse_eval_atom M N _ xs ss bvs
            hxs hss hbvs
            (by intro f a h; cases h)
            (by intro s S h; cases h)
            (by intro h; cases h)
            hFTrans hSubstTrans hRel.globals

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

The general induction (over an arbitrary `bvs` accumulator and a model `N`
related by `SubstFalseRel`) is factored into `substFalse_eval_gen_lt`, whose
variable / atom / `Stuck` cases are proved; only its application case remains.
Reducing this top-level `bvs = nil` statement to that lemma additionally needs
the base relation `SubstFalseRel M (pushSubstModel M xs ts) xs ts nil` (the
mapped field of which relates `pushSubstModel`'s push order to `assoc_nil_nth`
by `find`-index, and needs binder-key distinctness — the same collision subtlety
as `substFalseRel_push`'s `hNoCollide`).

Side hypotheses still to be threaded through from the rule context:
* `F` has an SMT translation and is `Bool`-typed under the binders;
* `ts` is a translatable value list matching `xs` (`__is_instantiation`).
-/
theorem substitute_simul_eval
    (M : SmtModel) (hM : model_total_typed M)
    (F xs ts : Term) :
    __smtx_model_eval M
        (__eo_to_smt (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil)) =
      __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) := by
  sorry

/--
The checker's `__is_instantiation xs ts = true` guard exactly reflects the
predicate `SubstActualsHaveSmtTypes`: it certifies that `ts` matches `xs` in
length and that each actual `tᵢ` has EO type equal to the binder type `Tᵢ`.
Combined with elementwise translatability of `ts` and well-formedness of the
binder SMT types, this yields the well-typed-actuals record the substitution
soundness lemmas consume. -/
theorem substActualsHaveSmtTypes_of_is_instantiation
    {xs ts : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hIsInst : __is_instantiation xs ts = Term.Boolean true) :
    SubstActualsHaveSmtTypes xs ts := by
  induction hEnv generalizing ts with
  | nil => exact SubstActualsHaveSmtTypes.nil ts
  | cons hTail ih =>
      rename_i s T env tailVars
      cases ts with
      | Apply f ts' =>
          cases f with
          | Apply g t =>
              cases g with
              | __eo_List_cons =>
                  rcases hTs with ⟨hHeadTrans, hTailTrans⟩
                  have hReq :
                      __is_instantiation
                          (Term.Apply (Term.Apply Term.__eo_List_cons
                            (Term.Var (Term.String s) T)) env)
                          (Term.Apply (Term.Apply Term.__eo_List_cons t) ts') =
                        __eo_requires (__eo_typeof t) T
                          (__is_instantiation env ts') := rfl
                  rw [hReq] at hIsInst
                  have hNeStuck :
                      __eo_requires (__eo_typeof t) T
                          (__is_instantiation env ts') ≠ Term.Stuck := by
                    rw [hIsInst]; decide
                  have hTypeofT : __eo_typeof t = T :=
                    instantiate_eo_requires_arg_eq_of_ne_stuck hNeStuck
                  have hTailInst :
                      __is_instantiation env ts' = Term.Boolean true := by
                    rw [← instantiate_eo_requires_result_eq_of_ne_stuck hNeStuck]
                    exact hIsInst
                  have hMatch :
                      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type T := by
                    rw [TranslationProofs.eo_to_smt_typeof_matches_translation t
                      hHeadTrans, hTypeofT]
                  exact SubstActualsHaveSmtTypes.cons
                    (hWf s T (List.Mem.head _))
                    hHeadTrans hMatch
                    (ih (fun s' T' hMem => hWf s' T' (List.Mem.tail _ hMem))
                      hTailTrans hTailInst)
              | _ => simp [EoListAllHaveSmtTranslation] at hTs
          | _ => simp [EoListAllHaveSmtTranslation] at hTs
      | __eo_List_nil =>
          have hStuck :
              __is_instantiation
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  Term.__eo_List_nil = Term.Stuck := rfl
          rw [hStuck] at hIsInst
          cases hIsInst
      | _ => simp [EoListAllHaveSmtTranslation] at hTs

/--
From `(forall xs F)` true in `M` and well-typed instantiation terms `ts`, the
body `F` is true under the substitution model `pushSubstModel M xs ts`. The
well-typedness of the actuals (`SubstActualsHaveSmtTypes`) is exactly what the
checker's `__is_instantiation` guard certifies; see
`substActualsHaveSmtTypes_of_is_instantiation`. -/
theorem instantiate_body_true
    (M : SmtModel) (hM : model_total_typed M)
    (xs F ts : Term)
    (hPrem : eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) true)
    (hWf : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hActuals : SubstActualsHaveSmtTypes xs ts) :
    __smtx_model_eval (pushSubstModel M xs ts) (__eo_to_smt F) = SmtValue.Boolean true :=
  instantiate_body_true_of_smt_typed_actuals M hM xs F ts hPrem hWf hActuals

/--
A non-`Stuck` result of `__eo_prog_instantiate` forces the premise to be a
`forall` and pins the conclusion to the substituted body. -/
theorem prog_instantiate_shape
    (ts prem : Term)
    (hNe : __eo_prog_instantiate ts (Proof.pf prem) ≠ Term.Stuck) :
    ∃ xs F,
      prem = Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F ∧
      __is_instantiation xs ts = Term.Boolean true ∧
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
                  -- `__eo_prog_instantiate` wraps the substitution in a
                  -- `__is_instantiation` capture/type guard; a non-`Stuck`
                  -- result forces that guard, collapsing `requires` to the
                  -- substitution itself, and pins `__is_instantiation` to `true`.
                  have hProgEq :
                      __eo_prog_instantiate ts
                          (Proof.pf
                            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) =
                        __eo_requires (__is_instantiation xs ts) (Term.Boolean true)
                          (__substitute_simul_rec (Term.Boolean false) F xs ts
                            Term.__eo_List_nil) := by
                    cases ts <;> first | rfl | exact absurd rfl hNe
                  rw [hProgEq] at hNe
                  refine ⟨xs, F, rfl, ?_, ?_⟩
                  · exact instantiate_eo_requires_arg_eq_of_ne_stuck hNe
                  · rw [hProgEq]
                    exact instantiate_eo_requires_result_eq_of_ne_stuck hNe
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
    (hActuals : SubstActualsHaveSmtTypes xs ts)
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
    exact instantiate_body_true M hM xs F ts hPrem hWf hActuals
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
                  obtain ⟨xs, F, hPremShape, hIsInst, hResEq⟩ :=
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
                  -- The binder list reflects an EO variable environment with
                  -- well-formed SMT types, and the `__is_instantiation` guard
                  -- certifies the actuals are correctly typed against it.
                  obtain ⟨binderVars, hXsEnv⟩ :=
                    InstantiateRule.forall_binders_env_of_has_smt_translation xs F hWf
                  have hBinderWf :
                      ∀ s T, (s, T) ∈ binderVars ->
                        __smtx_type_wf (__eo_to_smt_type T) = true :=
                    InstantiateRule.forall_binder_types_wf_of_has_smt_translation
                      hWf hXsEnv
                  have hActuals : InstantiateRule.SubstActualsHaveSmtTypes xs a1 :=
                    InstantiateRule.substActualsHaveSmtTypes_of_is_instantiation
                      hXsEnv hBinderWf hActualsTrans hIsInst
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
                      F xs a1 hWf hActualsTrans hActuals hSubstTypeof
                  refine ⟨?_, ?_⟩
                  · -- facts_of_true
                    intro hEvid
                    have hPremTrue : eo_interprets M prem true :=
                      hEvid prem (by simp [prem, premiseTermList])
                    rw [hPremShape] at hPremTrue
                    change eo_interprets M (__eo_prog_instantiate a1 (Proof.pf prem)) true
                    rw [hResEq]
                    exact InstantiateRule.instantiate_sound M hM xs F a1
                      hPremTrue hWf hActuals hResBool
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
