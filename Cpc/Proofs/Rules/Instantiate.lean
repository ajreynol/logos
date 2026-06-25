import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Closed.ContainsAtomicTermListFree

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
   lemma for the case breakdown and the `bvs`-generalisation it needs.

3. **`instantiate_body_true`** (`sorry`) — from `forall xs F` true and the
   well-typedness of `ts`, the body is true under `pushSubstModel M xs ts`. This
   unfolds the `forall = not (exists … not)` encoding (`Cpc/Spec.lean:411`,
   `native_eval_texists`, `Cpc/SmtModel.lean:580`) and instantiates the universal
   at the specific assignment `pushSubstModel M xs ts`.

4. **`prog_instantiate_shape`** (`sorry`) — a non-`Stuck` result forces the
   premise to be `forall xs F` and pins the conclusion to the substitution.

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
  sorry

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
  sorry

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
  sorry

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
                  -- The result is Bool-typed (transport hResultTy along hResEq).
                  have hResBool :
                      RuleProofs.eo_has_bool_type
                        (__substitute_simul_rec (Term.Boolean false) F xs a1 Term.__eo_List_nil) := by
                    sorry
                  -- The premise (the forall) has an SMT translation.
                  have hWf :
                      RuleProofs.eo_has_smt_translation
                        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) := by
                    sorry
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
