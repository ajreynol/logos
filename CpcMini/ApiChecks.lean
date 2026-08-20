module

public import CpcMini.Api
import all CpcMini.Api
public import CpcMini.Proofs.Assumptions
import all CpcMini.Proofs.Assumptions

@[expose] public section

/-!
# The checks in `CpcMini/Api.lean` are the components of `correct___eo_is_refutation`

The CpcMini counterpart of `Cpc/ApiChecks.lean`: each check of `CpcMini/Api.lean`
is proved to give the component of the theorem it stands for.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The refutation check computes `eo_is_refutation` -/

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
Folding the guarded push over a proof's assumptions builds exactly the state
`__eo_invoke_assume_list` builds from the corresponding `and`-chain.
-/
theorem invoke_assume_list_eq_fold (assums : List Term) :
    __eo_invoke_assume_list CState.nil (logos_assumption_term assums)
      = assums.foldl logos_invoke_input_assume logos_init_state := by
  simpa [logos_assumption_term, logos_init_state, __eo_invoke_assume_list]
    using invoke_assume_list_foldl assums (Term.Boolean true) CState.nil

/-- The refutation check is the generated `__eo_checker_is_refutation`. -/
theorem logos_check_refutation_eq_checker (assums : List Term) (cmds : CCmdList) :
    logos_check_refutation assums cmds
      = __eo_checker_is_refutation (logos_assumption_term assums) cmds := by
  simp [logos_check_refutation, __eo_checker_is_refutation, invoke_assume_list_eq_fold]

/-- `logos_check_refutation` returning `true` is `eo_is_refutation` on the same data. -/
theorem eo_is_refutation_of_check (assums : List Term) (cmds : CCmdList)
    (h : logos_check_refutation assums cmds = true) :
    eo_is_refutation (logos_assumption_term assums) cmds :=
  eo_is_refutation.intro _ _ (by rwa [logos_check_refutation_eq_checker] at h)

/-! ## The two translation side conditions -/

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
`correct___eo_is_refutation` for the term `logos_verdict` uses as `F`.
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

end Eo
