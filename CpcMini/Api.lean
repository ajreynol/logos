module

public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.Spec
import all CpcMini.Spec
public import CpcMini.Proofs.Assumptions
import all CpcMini.Proofs.Assumptions

@[expose] public section

/-!
# The verdict CpcMini computes for a proof

The CpcMini counterpart of `Cpc/Api.lean`; see that file for the full account.
CpcMini is the small calculus the proofs are developed and tested against; it
has no parser and no executable of its own, so this file stops at
`logos_verdict` — the three checks run on a proof that is already in hand — and
`CpcMini/ApiCorrect.lean` is stated about that.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The assumptions of a proof, as one formula -/

/-- One link of the assumption chain: `A` conjoined onto the assumptions already read. -/
def logos_assumption_chain_step (rest A : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest

/--
The conjunction of a proof's assumptions, i.e. the term the correctness theorem
is about.

`__eo_invoke_assume_list` pushes the head of an `and`-chain last, and premises
are numbered against a stack whose first assumption is at the bottom, so the
chain lists the assumptions in reverse order.  See `Cpc/Api.lean` for the long
version.
-/
def logos_assumption_term (assums : List Term) : Term :=
  assums.foldl logos_assumption_chain_step (Term.Boolean true)

/--
Push one input assumption with the guard `__eo_invoke_assume_list` applies: the
assumption must be Boolean-typed and closed, or the state goes `Stuck`.  This is
*not* `logos_invoke_assume` (`CpcMini/Logos.lean`), which pushes without the
guard; `checkerTypeInvariant` and `StableAssumptionList` both depend on it.
-/
def logos_invoke_input_assume (s : CState) (A : Term) : CState :=
  __eo_push_input_assume_check (__eo_and (__eo_is_bool_type A) (__eo_is_closed A)) A s

/-! ## The three checks -/

/--
Logos runs `cmds` from the proof's assumptions and ends in a closed state that
has proven `false`; equal to `__eo_checker_is_refutation (logos_assumption_term
assums) cmds` by `logos_check_refutation_eq_checker` in `CpcMini/ApiChecks.lean`.
-/
def logos_check_refutation (assums : List Term) (cmds : CCmdList) : Bool :=
  __eo_state_is_refutation
    (__eo_invoke_cmd_list (assums.foldl logos_invoke_input_assume logos_init_state) cmds)

/--
Every assumption has an SMT-LIB translation.  `translatableAssumptionList_of_check`
(`CpcMini/ApiChecks.lean`) turns this into `TranslatableAssumptionList
(logos_assumption_term assums)`.
-/
def logos_check_translatableAssumptionList (assums : List Term) : Bool :=
  assums.all fun A => decide (eoHasSmtTranslation A)

/-- `CmdListTranslationOk cmds`, decided by the instance in `CpcMini/Proofs/Assumptions.lean`. -/
def logos_check_cmdListTranslationOk (cmds : CCmdList) : Bool :=
  decide (CmdListTranslationOk cmds)

/-! ## The verdict -/

/-- What Logos reports about a proof. -/
inductive Verdict where
  /-- The proof's assumptions are unsatisfiable, by `correct___logos_verdict`. -/
  | correct
  /-- Logos does not accept the proof as a refutation. -/
  | incorrect
  /-- Logos accepts the proof, but a side condition of the theorem fails on it. -/
  | incomplete
deriving DecidableEq, Repr, Inhabited

/-- The verdict for a proof: `correct` exactly when all three checks pass. -/
def logos_verdict (assums : List Term) (cmds : CCmdList) : Verdict :=
  if !logos_check_refutation assums cmds then Verdict.incorrect
  else if !logos_check_translatableAssumptionList assums then Verdict.incomplete
  else if !logos_check_cmdListTranslationOk cmds then Verdict.incomplete
  else Verdict.correct

end Eo
