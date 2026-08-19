module

public import Cpc.Api
import all Cpc.Api
public import Cpc.Proofs.Assumptions
import all Cpc.Proofs.Assumptions

@[expose] public section

/-!
# The checks in `Cpc/Api.lean` are the components of `correct___eo_is_refutation`

`Cpc/Api.lean` computes four things from the parser's output; this module proves
that each one means what its name claims, against the definitions the soundness
proof actually uses.

| computed in `Cpc/Api.lean`                 | proved here to give              |
| ------------------------------------------ | -------------------------------- |
| `logos_check_refutation assums cmds`        | `eo_is_refutation F cmds`        |
| `logos_check_translatableAssumptionList`    | `TranslatableAssumptionList F`   |
| `logos_check_cmdListTranslationOk`          | `CmdListTranslationOk cmds`      |

throughout with `F = logos_assumption_term assums`.  `Cpc/ApiCorrect.lean` feeds
these into `correct___eo_is_refutation`.

The last section goes the other way, and reads the conclusion of that theorem
back as a statement about the parser's assumption list rather than about the
`and`-chain built from it.

Only the direction soundness needs is proved -- a check that returned `true` too
rarely would only reject proofs the theorem would not have covered anyway.

This module deliberately does not import the checker correctness proof, so that
it stays cheap enough to build in CI.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The refutation check computes `eo_is_refutation`

`__eo_invoke_assume_list` walks an `and`-chain and pushes each conjunct with the
guard `(and (is_bool_type A) (is_closed A))`.  `logos_check_refutation` folds
`logos_invoke_input_assume` over the parser's list instead, which applies the
same guard in the same order with no stack growth.  These lemmas prove the two
agree, so that the executable's check is literally the theorem's hypothesis.
-/

/-- Generalized over the accumulator, so the induction goes through. -/
private theorem invoke_assume_list_foldl (assums : List Term) :
    ∀ (rest : Term) (S : CState),
      __eo_invoke_assume_list S (assums.foldl logos_assumption_chain_step rest)
        = assums.foldl logos_invoke_input_assume (__eo_invoke_assume_list S rest) := by
  induction assums with
  | nil => intro rest S; rfl
  | cons A assums ih =>
    intro rest S
    rw [List.foldl_cons, ih, List.foldl_cons]
    congr 1

/--
Folding the guarded push over the parser's assumptions builds exactly the state
`__eo_invoke_assume_list` builds from the corresponding `and`-chain.
-/
theorem invoke_assume_list_eq_fold (assums : List Term) :
    __eo_invoke_assume_list CState.nil (logos_assumption_term assums)
      = assums.foldl logos_invoke_input_assume logos_init_state := by
  simpa [logos_assumption_term, logos_init_state, __eo_invoke_assume_list]
    using invoke_assume_list_foldl assums (Term.Boolean true) CState.nil

/-- The executable's refutation check is the generated `__eo_checker_is_refutation`. -/
theorem logos_check_refutation_eq_checker (assums : List Term) (cmds : CCmdList) :
    logos_check_refutation assums cmds
      = __eo_checker_is_refutation (logos_assumption_term assums) cmds := by
  simp [logos_check_refutation, __eo_checker_is_refutation, invoke_assume_list_eq_fold]

/-- `logos_check_refutation` returning `true` is `eo_is_refutation` on the same data. -/
theorem eo_is_refutation_of_check (assums : List Term) (cmds : CCmdList)
    (h : logos_check_refutation assums cmds = true) :
    eo_is_refutation (logos_assumption_term assums) cmds :=
  eo_is_refutation.intro _ _ (by rwa [logos_check_refutation_eq_checker] at h)

/-! ## The two translation side conditions

Both checks are `decide` of the predicate the theorem uses, so the only thing
left to prove is that checking the parser's *list* of assumptions gives
`TranslatableAssumptionList` of the `and`-chain built from it.
-/

/-- Generalized over the accumulator, mirroring `invoke_assume_list_foldl`. -/
private theorem translatableAssumptionList_foldl (assums : List Term) :
    ∀ rest : Term,
      logos_check_translatableAssumptionList assums = true ->
      TranslatableAssumptionList rest ->
      TranslatableAssumptionList (assums.foldl logos_assumption_chain_step rest) := by
  induction assums with
  | nil => intro rest _ hrest; exact hrest
  | cons A assums ih =>
    intro rest h hrest
    simp only [logos_check_translatableAssumptionList, List.all_cons, Bool.and_eq_true,
      decide_eq_true_eq] at h
    exact ih _ (by simpa [logos_check_translatableAssumptionList] using h.2)
      (TranslatableAssumptionList.step A rest h.1 hrest)

/--
`logos_check_translatableAssumptionList` gives the first hypothesis of
`correct___eo_is_refutation` for the term the executable uses as `F`.
-/
theorem translatableAssumptionList_of_check (assums : List Term)
    (h : logos_check_translatableAssumptionList assums = true) :
    TranslatableAssumptionList (logos_assumption_term assums) :=
  translatableAssumptionList_foldl assums (Term.Boolean true) h TranslatableAssumptionList.base

/--
`logos_check_cmdListTranslationOk` gives the second hypothesis of
`correct___eo_is_refutation`; it is `decide` of that hypothesis.
-/
theorem cmdListTranslationOk_of_check (cmds : CCmdList)
    (h : logos_check_cmdListTranslationOk cmds = true) : CmdListTranslationOk cmds :=
  of_decide_eq_true h

/-! ## The verdict -/

/-- `correct` means all three checks returned `true`. -/
theorem checks_of_verdict_correct (assums : List Term) (cmds : CCmdList)
    (h : logos_verdict assums cmds = Verdict.correct) :
    logos_check_refutation assums cmds = true ∧
      logos_check_translatableAssumptionList assums = true ∧
        logos_check_cmdListTranslationOk cmds = true := by
  unfold logos_verdict at h
  cases hRef : logos_check_refutation assums cmds <;>
    cases hAssums : logos_check_translatableAssumptionList assums <;>
      cases hCmds : logos_check_cmdListTranslationOk cmds <;>
        simp_all

/--
What the executable computes on a file it could parse: the verdict of the
parser's output.  This is the step `Main.lean` performs by hand, so that it can
report *why* an accepted proof is `unsupported`.
-/
theorem logos_check_proof_of_parse (input : String) (assums : List Term) (cmds : CCmdList)
    (h : parseProof input = Except.ok (assums, cmds)) :
    logos_check_proof input = Except.ok (logos_verdict assums cmds) := by
  simp [logos_check_proof, h]

/-! ## Reading the conclusion back as a statement about the assumption list

`correct___eo_is_refutation` concludes `eo_satisfiability F false` for the
`and`-chain `F`.  Unfolded, that says every total typed model evaluates the chain
to `false`; the lemmas here turn it into the statement that every such model
makes one of the parser's assumptions false, which is what
`Cpc/ApiCorrect.lean` states.
-/

/-- `__smtx_model_eval_and` is `false` only if one of its arguments is. -/
private theorem eval_and_eq_false (x y : SmtValue)
    (h : __smtx_model_eval_and x y = SmtValue.Boolean false) :
    x = SmtValue.Boolean false ∨ y = SmtValue.Boolean false := by
  fun_cases __smtx_model_eval_and x y <;> simp_all [__smtx_model_eval_and, native_and]
  rename_i x1 _
  cases x1 <;> simp_all

/-- Generalized over the accumulator, so the induction goes through. -/
private theorem exists_false_assumption_foldl (M : SmtModel) (assums : List Term) :
    ∀ rest : Term,
      __smtx_model_eval M (__eo_to_smt (assums.foldl logos_assumption_chain_step rest))
          = SmtValue.Boolean false ->
      (∃ A ∈ assums, __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false)
        ∨ __smtx_model_eval M (__eo_to_smt rest) = SmtValue.Boolean false := by
  induction assums with
  | nil => intro rest h; exact Or.inr h
  | cons A assums ih =>
    intro rest h
    rw [List.foldl_cons] at h
    rcases ih (logos_assumption_chain_step rest A) h with hA | hStep
    · rcases hA with ⟨B, hB, hBval⟩
      exact Or.inl ⟨B, List.mem_cons_of_mem A hB, hBval⟩
    · have hAnd : __smtx_model_eval_and (__smtx_model_eval M (__eo_to_smt A))
          (__smtx_model_eval M (__eo_to_smt rest)) = SmtValue.Boolean false := by
        simpa [logos_assumption_chain_step, __eo_to_smt, __smtx_model_eval] using hStep
      rcases eval_and_eq_false _ _ hAnd with hA | hRest
      · exact Or.inl ⟨A, List.mem_cons_self, hA⟩
      · exact Or.inr hRest

/--
If the conjunction of the assumptions is false in a model, then one of the
assumptions is false in it.
-/
theorem exists_false_assumption (M : SmtModel) (assums : List Term)
    (h : __smtx_model_eval M (__eo_to_smt (logos_assumption_term assums))
      = SmtValue.Boolean false) :
    ∃ A ∈ assums, __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean false := by
  rcases exists_false_assumption_foldl M assums (Term.Boolean true) h with hA | hTrue
  · exact hA
  · simp [__eo_to_smt, __smtx_model_eval] at hTrue

end Eo
