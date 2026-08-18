module

public import Cpc.Api
import all Cpc.Api

@[expose] public section

/-!
# The runtime checks discharge the hypotheses of `correct___eo_is_refutation`

`Cpc/Api.lean` computes four things from the parser's output; this module proves
that each one means what its name claims, against the definitions the soundness
proof actually uses.

| computed in `Cpc/Api.lean`                 | proved here to imply             |
| ------------------------------------------ | -------------------------------- |
| `logos_check_refutation assums cmds`        | `eo_is_refutation F cmds`        |
| `logos_check_translatableAssumptionList`    | `TranslatableAssumptionList F`   |
| `logos_check_cmdListTranslationOk`          | `CmdListTranslationOk cmds`      |

throughout with `F = logos_assumption_term assums`.  `Cpc/ApiCorrect.lean` feeds
these into `correct___eo_is_refutation`.

Only the `check = true -> predicate` direction is proved, which is the direction
soundness needs.  It is also what keeps the `Bool` mirrors in `Cpc/Api.lean`
honest as `Cpc/Proofs/Assumptions.lean` evolves: a mirror that checked less than
its predicate would break `cmdTranslationOk_of_check` below, whereas a mirror
that checks more can only reject proofs the theorem would not have covered.

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
      __eo_invoke_assume_list S
          (assums.foldl (fun rest A => Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest) rest)
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

/-! ## The mirrors decide the translation side conditions -/

/-- `eoHasSmtTranslationB` decides `eoHasSmtTranslation`. -/
theorem eoHasSmtTranslation_of_check {t : Term} (h : eoHasSmtTranslationB t = true) :
    eoHasSmtTranslation t := by
  simp [eoHasSmtTranslationB, bne_iff_ne] at h
  simpa [eoHasSmtTranslation] using h

/-- `eoListAllHaveSmtTranslationB` decides `EoListAllHaveSmtTranslation`. -/
theorem eoListAllHaveSmtTranslation_of_check :
    ∀ t : Term, eoListAllHaveSmtTranslationB t = true -> EoListAllHaveSmtTranslation t := by
  intro t
  fun_induction eoListAllHaveSmtTranslationB t <;>
    simp_all [EoListAllHaveSmtTranslation, eoHasSmtTranslation_of_check]

/-- `argTranslationOkMaskedB` decides `argTranslationOkMasked`. -/
theorem argTranslationOkMasked_of_check :
    ∀ (k : ArgTranslationKind) (t : Term),
      argTranslationOkMaskedB k t = true -> argTranslationOkMasked k t := by
  intro k t
  cases k <;>
    simp_all [argTranslationOkMaskedB, argTranslationOkMasked, eoHasSmtTranslation_of_check,
      eoListAllHaveSmtTranslation_of_check]

/-- `cArgListTranslationOkB` decides `cArgListTranslationOk`. -/
theorem cArgListTranslationOk_of_check :
    ∀ args : CArgList, cArgListTranslationOkB args = true -> cArgListTranslationOk args := by
  intro args
  induction args with
  | nil => intro _; simp [cArgListTranslationOk]
  | cons a args ih =>
    intro h
    simp only [cArgListTranslationOkB, Bool.and_eq_true] at h
    exact ⟨eoHasSmtTranslation_of_check h.1, ih h.2⟩

/-- `cArgListTranslationOkMaskB` decides `cArgListTranslationOkMask`. -/
theorem cArgListTranslationOkMask_of_check :
    ∀ (mask : List ArgTranslationKind) (args : CArgList),
      cArgListTranslationOkMaskB mask args = true -> cArgListTranslationOkMask mask args := by
  intro mask args
  fun_induction cArgListTranslationOkMaskB mask args <;>
    simp_all [cArgListTranslationOkMask, argTranslationOkMasked_of_check]

/--
`cmdTranslationOkB` decides `cmdTranslationOk`.

This is the lemma that pins the two case lists together: if a rule gains a mask
in `Cpc/Proofs/Assumptions.lean` and the mirror in `Cpc/Api.lean` is not updated
to match, the mirror falls through to `cArgListTranslationOkB` and this proof
stops going through.
-/
theorem cmdTranslationOk_of_check :
    ∀ c : CCmd, cmdTranslationOkB c = true -> cmdTranslationOk c := by
  intro c
  fun_cases cmdTranslationOkB c <;>
    simp_all [cmdTranslationOk, cArgListTranslationOk_of_check,
      cArgListTranslationOkMask_of_check, eoHasSmtTranslation_of_check]

/-! ## The two top-level checks -/

/-- Generalized over the accumulator, mirroring `invoke_assume_list_foldl`. -/
private theorem translatableAssumptionList_foldl (assums : List Term) :
    ∀ rest : Term,
      logos_check_translatableAssumptionList assums = true ->
      TranslatableAssumptionList rest ->
      TranslatableAssumptionList
        (assums.foldl (fun rest A => Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest) rest) := by
  induction assums with
  | nil => intro rest _ hrest; exact hrest
  | cons A assums ih =>
    intro rest h hrest
    simp only [logos_check_translatableAssumptionList, Bool.and_eq_true] at h
    exact ih _ h.2 (TranslatableAssumptionList.step A rest (eoHasSmtTranslation_of_check h.1) hrest)

/--
`logos_check_translatableAssumptionList` decides the first hypothesis of
`correct___eo_is_refutation` for the term the executable uses as `F`.
-/
theorem translatableAssumptionList_of_check (assums : List Term)
    (h : logos_check_translatableAssumptionList assums = true) :
    TranslatableAssumptionList (logos_assumption_term assums) :=
  translatableAssumptionList_foldl assums (Term.Boolean true) h TranslatableAssumptionList.base

/--
`logos_check_cmdListTranslationOk` decides the second hypothesis of
`correct___eo_is_refutation`.
-/
theorem cmdListTranslationOk_of_check :
    ∀ cmds : CCmdList, logos_check_cmdListTranslationOk cmds = true -> CmdListTranslationOk cmds := by
  intro cmds
  induction cmds with
  | nil => intro _; exact CmdListTranslationOk.nil
  | cons c cmds ih =>
    intro h
    simp only [logos_check_cmdListTranslationOk, Bool.and_eq_true] at h
    exact CmdListTranslationOk.cons c cmds (cmdTranslationOk_of_check c h.1) (ih h.2)

end Eo
