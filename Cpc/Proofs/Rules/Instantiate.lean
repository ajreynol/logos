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
                            · -- `f` is not a special unary head: dispatch on its
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
                                                                            · sorry
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
