module

public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.Spec
import all CpcMini.Spec
public import CpcMini.Parser
import all CpcMini.Parser
public import CpcMini.Proofs.Assumptions
import all CpcMini.Proofs.Assumptions

@[expose] public section

/-!
# What the `logos-mini` executable computes

The CpcMini counterpart of `Cpc/Api.lean`; see that file for the full account.
`logos_check_proof` is the whole of what `MainMini.lean` does with a proof file,
and `CpcMini/ApiCorrect.lean` is stated about it.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The assumptions the parser produced, as one formula -/

/-- One link of the assumption chain: `A` conjoined onto the assumptions already read. -/
def logos_assumption_chain_step (rest A : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest

/--
The conjunction of the parser's assumptions, i.e. the term the correctness
theorem is about.

`__eo_invoke_assume_list` pushes the head of an `and`-chain last, and the parser
numbers premises against a stack whose first assumption is at the bottom, so the
chain lists the assumptions in reverse file order.  See `Cpc/Api.lean` for the
long version.
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
Logos runs `cmds` from the parser's assumptions and ends in a closed state that
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

/-- What the executable reports about a proof file. -/
inductive Verdict where
  /-- The proof's assumptions are unsatisfiable, by `correct___logos_check_proof`. -/
  | correct
  /-- Logos does not accept the proof as a refutation. -/
  | incorrect
  /-- Logos accepts the proof, but a side condition of the theorem fails on it. -/
  | incomplete
deriving DecidableEq, Repr, Inhabited

/-- The verdict for a parsed proof: `correct` exactly when all three checks pass. -/
def logos_verdict (assums : List Term) (cmds : CCmdList) : Verdict :=
  if !logos_check_refutation assums cmds then Verdict.incorrect
  else if !logos_check_translatableAssumptionList assums then Verdict.incomplete
  else if !logos_check_cmdListTranslationOk cmds then Verdict.incomplete
  else Verdict.correct

/-- Parse a proof file and report its verdict: everything `MainMini.lean` does. -/
def logos_check_proof (input : String) : Except String Verdict :=
  match parseProof input with
  | Except.ok (assums, cmds) => Except.ok (logos_verdict assums cmds)
  | Except.error e => Except.error e

/-! ## Diagnostics

Used only to report why a proof fell outside the fragment the specification
covers; they have no role in the correctness statement.
-/

/-- The first assumption with no SMT-LIB translation, with its position in file order. -/
def logos_untranslatable_assumption (assums : List Term) : Option (Nat × Term) :=
  go 0 assums
where
  go : Nat -> List Term -> Option (Nat × Term)
    | _, [] => none
    | i, A :: assums => if eoHasSmtTranslation A then go (i + 1) assums else some (i, A)

/--
The first command whose arguments fail their translation side condition, with its
position in file order among the proof-stack commands.
-/
def logos_untranslatable_cmd (cmds : CCmdList) : Option (Nat × CCmd) :=
  go 0 cmds
where
  go : Nat -> CCmdList -> Option (Nat × CCmd)
    | _, CCmdList.nil => none
    | i, CCmdList.cons c cmds => if cmdTranslationOk c then go (i + 1) cmds else some (i, c)

end Eo
