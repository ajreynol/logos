import Cpc.Proofs.Closed.ContainsAtomicTermListFree

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
# Substitution utilities — `__substitute_simul_rec`

`__substitute_simul_rec isr t xs ss bvs` (`Cpc/Logos.lean:2298`) performs a
simultaneous substitution `[xs ↦ ss]` into `t`, with `bvs` the accumulator of
locally bound variables. The leading flag `isr` ("is rename") selects between two
genuinely different operations, and **only the quantifier case depends on it**:

* **`isr = false` — capture-avoiding substitution** (used by `instantiate`,
  `skolemize`). At a binder `(q (v::vs) a)` the binder list is kept verbatim and
  its variables are pushed onto `bvs`, so they *shadow* the substitution inside
  the body `a`.

* **`isr = true` — uniform renaming** (used by `alpha_equiv`). At a binder the
  substitution is applied to the binder list *itself*, and the bound variables
  are **not** added to `bvs`. Soundness here is alpha-equivalence (`t = subst t`),
  a different statement from the substitution semantics.

The variable / application / atom / `Stuck` cases thread `isr` through unchanged,
so their unfolding lemmas are shared. This file establishes the definitional
unfolding lemmas; semantic (model-evaluation) lemmas build on top in sibling
files, split by mode.

Naming: `substitute_simul_rec_*` for shared structural lemmas;
`substFalse_*` / `substTrue_*` for the mode-specific quantifier lemmas.
-/

namespace SubstituteSupport

/-- `(v :: vs)` as an EO cons-list term, the binder-list shape. -/
private abbrev consTerm (v vs : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons v) vs

/-! ## `Stuck` propagation (mode-independent)

Only the `isr = Stuck` case is definitional; the others require the earlier
arguments to be resolved first, so they are not stated here (the structural
lemmas below take `≠ Stuck` hypotheses directly). -/

@[simp] theorem substitute_simul_rec_stuck_isr (t xs ss bvs : Term) :
    __substitute_simul_rec Term.Stuck t xs ss bvs = Term.Stuck := by
  simp [__substitute_simul_rec]

/-! ## Variable case (mode-independent)

A variable is kept if it is locally bound (`bvs`); otherwise it is looked up in
`xs` and replaced by the associated `ss` entry, or kept if absent. -/
theorem substitute_simul_rec_var
    (isr s S xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck) :
    __substitute_simul_rec isr (Term.Var s S) xs ss bvs =
      __eo_ite (__eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var s S)))
        (__eo_ite (__eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var s S)))
          (Term.Var s S)
          (__assoc_nil_nth Term.__eo_List_cons ss
            (__eo_list_find Term.__eo_List_cons xs (Term.Var s S))))
        (Term.Var s S) := by
  simp [__substitute_simul_rec]

/-! ### Variable outcomes

`substitute_simul_rec_var` exposes the raw nested `__eo_ite`. The three lemmas
below resolve it into the three semantic outcomes, keyed on whether the variable
is locally bound (`bvs`) and whether it is mapped by `xs`. These are what the
model-evaluation variable case consumes.

`__eo_is_neg (__eo_list_find _ l x)` is `Boolean true` exactly when `x ∉ l`
(`__eo_list_find` returns `-1` when absent, a non-negative index otherwise). -/

/-- Variable locally bound (`x ∈ bvs`): kept verbatim. -/
theorem substitute_simul_rec_var_bound
    (isr s S xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hBound :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var s S)) =
        Term.Boolean false) :
    __substitute_simul_rec isr (Term.Var s S) xs ss bvs = Term.Var s S := by
  rw [substitute_simul_rec_var isr s S xs ss bvs hisr hxs hss hbvs, hBound]
  simp [__eo_ite, native_ite, native_teq]

/-- Variable free (`x ∉ bvs`) and unmapped (`x ∉ xs`): kept verbatim. -/
theorem substitute_simul_rec_var_unmapped
    (isr s S xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFree :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var s S)) =
        Term.Boolean true)
    (hUnmapped :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var s S)) =
        Term.Boolean true) :
    __substitute_simul_rec isr (Term.Var s S) xs ss bvs = Term.Var s S := by
  rw [substitute_simul_rec_var isr s S xs ss bvs hisr hxs hss hbvs, hFree, hUnmapped]
  simp [__eo_ite, native_ite, native_teq]

/-- Variable free (`x ∉ bvs`) and mapped (`x ∈ xs`): replaced by the associated
`ss` entry at the found index. -/
theorem substitute_simul_rec_var_mapped
    (isr s S xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hFree :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var s S)) =
        Term.Boolean true)
    (hMapped :
      __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var s S)) =
        Term.Boolean false) :
    __substitute_simul_rec isr (Term.Var s S) xs ss bvs =
      __assoc_nil_nth Term.__eo_List_cons ss
        (__eo_list_find Term.__eo_List_cons xs (Term.Var s S)) := by
  rw [substitute_simul_rec_var isr s S xs ss bvs hisr hxs hss hbvs, hFree, hMapped]
  simp [__eo_ite, native_ite, native_teq]

/-! ## Application case, non-binder (mode-independent)

Reached for `Apply f a` whose head `f` is *not* of binder shape
`Apply q (v :: vs)`. The substitution distributes over the application. -/
theorem substitute_simul_rec_apply
    (isr f a xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotBinder : ∀ q v vs, f ≠ Term.Apply q (consTerm v vs)) :
    __substitute_simul_rec isr (Term.Apply f a) xs ss bvs =
      __eo_mk_apply
        (__substitute_simul_rec isr f xs ss bvs)
        (__substitute_simul_rec isr a xs ss bvs) := by
  simp [__substitute_simul_rec]

/-! ## Atom case (mode-independent)

A non-`Apply`, non-`Var`, non-`Stuck` term (constants, `UOp`, …) must be ground:
the result requires `__is_closed_rec` and returns the term unchanged. -/
theorem substitute_simul_rec_atom
    (isr x xs ss bvs : Term)
    (hisr : isr ≠ Term.Stuck) (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck)
    (hNotApply : ∀ f a, x ≠ Term.Apply f a)
    (hNotVar : ∀ s S, x ≠ Term.Var s S)
    (hNotStuck : x ≠ Term.Stuck) :
    __substitute_simul_rec isr x xs ss bvs =
      __eo_requires (__is_closed_rec x Term.__eo_List_nil) (Term.Boolean true) x := by
  cases x <;>
    simp_all [__substitute_simul_rec]

/-! ## Quantifier case — mode-specific

At a binder `(q (v::vs) a)` the capture-avoidance side condition
`__contains_atomic_term_list_free_rec ss (v::vs) nil = false` is required; then
the two modes diverge. -/

/-- **Substitution mode** (`isr = false`): binder list kept, bound vars pushed
onto `bvs`, body substituted under the extended `bvs`. -/
theorem substFalse_quant
    (q v vs a xs ss bvs : Term)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q (consTerm v vs)) a) xs ss bvs =
      __eo_requires
        (__contains_atomic_term_list_free_rec ss (consTerm v vs) Term.__eo_List_nil)
        (Term.Boolean false)
        (__eo_mk_apply (Term.Apply q (consTerm v vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss
            (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) := by
  simp [__substitute_simul_rec, consTerm, __eo_ite, native_ite, native_teq]

/-- **Rename mode** (`isr = true`): substitution applied to the binder list too,
bound vars *not* pushed, body substituted under the unchanged `bvs`. -/
theorem substTrue_quant
    (q v vs a xs ss bvs : Term)
    (hxs : xs ≠ Term.Stuck) (hss : ss ≠ Term.Stuck) (hbvs : bvs ≠ Term.Stuck) :
    __substitute_simul_rec (Term.Boolean true)
        (Term.Apply (Term.Apply q (consTerm v vs)) a) xs ss bvs =
      __eo_requires
        (__contains_atomic_term_list_free_rec ss (consTerm v vs) Term.__eo_List_nil)
        (Term.Boolean false)
        (__eo_mk_apply
          (__eo_mk_apply q
            (__substitute_simul_rec (Term.Boolean true) (consTerm v vs) xs ss bvs))
          (__substitute_simul_rec (Term.Boolean true) a xs ss bvs)) := by
  simp [__substitute_simul_rec, consTerm, __eo_ite, native_ite, native_teq]

/-! ## Substitution-mode semantics (`isr = false`)

The model-evaluation lemma: evaluating the translation of `subst false F xs ss bvs`
in `M` equals evaluating `toSmt F` in a model `N` that realises the substitution
`[xs ↦ ss]` (off the bound `bvs`). The relation `SubstFalseRel` packages exactly
the per-variable obligations the variable case needs; the induction on `F`
threads it through, re-establishing it under each binder via the
capture-avoidance side condition. -/

/-- Evaluating an EO variable reduces to the model's variable lookup. -/
theorem eval_eo_var (M : SmtModel) (s : native_String) (T : Term) :
    __smtx_model_eval M (__eo_to_smt (Term.Var (Term.String s) T)) =
      native_model_var_lookup M s (__eo_to_smt_type T) := by
  rw [__smtx_model_eval.eq_def]
  rfl

/--
Model relation realising a simultaneous substitution `[xs ↦ ss]` off the bound
variables `bvs`, in substitution mode.

* `agree` — variables that are bound (`is_neg (find bvs x) = false`) or unmapped
  (`is_neg (find xs x) = true`) are interpreted identically by `M` and `N`.
* `mapped` — a free, mapped variable `x` is assigned by `N` the value of its
  substitute `ss[find xs x]` evaluated in the ambient model `M`.

This is the substitution analogue of `model_agrees_except_on_eo_env`. -/
structure SubstFalseRel (M N : SmtModel) (xs ss bvs : Term) : Prop where
  globals : model_agrees_on_globals M N
  agree :
    ∀ (s : native_String) (T : Term),
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s) T)) =
          Term.Boolean false ∨
        __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) =
          Term.Boolean true ->
      native_model_var_lookup M s (__eo_to_smt_type T) =
        native_model_var_lookup N s (__eo_to_smt_type T)
  mapped :
    ∀ (s : native_String) (T : Term),
      __eo_is_neg (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s) T)) =
          Term.Boolean true ->
      __eo_is_neg (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) =
          Term.Boolean false ->
      native_model_var_lookup N s (__eo_to_smt_type T) =
        __smtx_model_eval M
          (__eo_to_smt
            (__assoc_nil_nth Term.__eo_List_cons ss
              (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T))))

/--
**Variable case** of the substitution-mode evaluation lemma.

Given proper var-list reflections for `xs` and `bvs`, the substituted variable
evaluated in `M` matches the variable evaluated in the substitution model `N`.
Splits on membership (bound / mapped / unmapped) and discharges each via the
corresponding variable-outcome lemma and a field of `SubstFalseRel`. -/
theorem substFalse_eval_var
    (M N : SmtModel) (s : native_String) (T xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars) (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hss : ss ≠ Term.Stuck)
    (hRel : SubstFalseRel M N xs ss bvs) :
    __smtx_model_eval M
        (__eo_to_smt
          (__substitute_simul_rec (Term.Boolean false) (Term.Var (Term.String s) T) xs ss bvs)) =
      __smtx_model_eval N (__eo_to_smt (Term.Var (Term.String s) T)) := by
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  rw [eval_eo_var N s T]
  rcases hBvsEnv with ⟨bvExact, hBvExact, hBvEquiv⟩
  by_cases hBound : (s, T) ∈ bvExact
  · -- bound: kept; M and N agree
    have hb : __eo_is_neg
        (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s) T)) =
        Term.Boolean false := hBvExact.find_neg_false_of_mem hBound
    rw [substitute_simul_rec_var_bound (Term.Boolean false) (Term.String s) T xs ss bvs
      hisr hxs hss hbvs hb, eval_eo_var M s T]
    exact hRel.agree s T (Or.inl hb)
  · have hbTrue : __eo_is_neg
        (__eo_list_find Term.__eo_List_cons bvs (Term.Var (Term.String s) T)) =
        Term.Boolean true := hBvExact.find_neg_true_of_not_mem hBound
    rcases hXsEnv with ⟨xsExact, hXsExact, hXsEquiv⟩
    by_cases hMapped : (s, T) ∈ xsExact
    · -- free and mapped: replaced by ss entry
      have hx : __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) =
          Term.Boolean false := hXsExact.find_neg_false_of_mem hMapped
      rw [substitute_simul_rec_var_mapped (Term.Boolean false) (Term.String s) T xs ss bvs
        hisr hxs hss hbvs hbTrue hx]
      exact (hRel.mapped s T hbTrue hx).symm
    · -- free and unmapped: kept; M and N agree
      have hx : __eo_is_neg
          (__eo_list_find Term.__eo_List_cons xs (Term.Var (Term.String s) T)) =
          Term.Boolean true := hXsExact.find_neg_true_of_not_mem hMapped
      rw [substitute_simul_rec_var_unmapped (Term.Boolean false) (Term.String s) T xs ss bvs
        hisr hxs hss hbvs hbTrue hx, eval_eo_var M s T]
      exact hRel.agree s T (Or.inr hx)

end SubstituteSupport
