module

public import CpcMini.Logos
import all CpcMini.Logos
public import CpcMini.Spec
import all CpcMini.Spec

@[expose] public section

/-!
# The entry point that the `logos-mini` executable runs

This is the CpcMini counterpart of `Cpc/Api.lean`; see that file for the full
account of the correspondence.  It computes everything the soundness theorem
`correct___eo_is_refutation` of `CpcMini/Proofs/Checker.lean` needs:

| hypothesis of the theorem       | computed by                                |
| ------------------------------- | ------------------------------------------ |
| the term `F`                    | `logos_assumption_term assums`             |
| `eo_is_refutation F pf`         | `logos_check_refutation assums cmds`       |
| `TranslatableAssumptionList F`  | `logos_check_translatableAssumptionList`   |
| `CmdListTranslationOk pf`       | `logos_check_cmdListTranslationOk`         |

`CpcMini/ApiChecks.lean` proves each check implies its hypothesis and
`CpcMini/ApiCorrect.lean` assembles them into `correct___logos_check_refutation`,
a theorem about the expression `MainMini.lean` evaluates.

Unlike CPC, the CpcMini calculus gives no rule a per-argument translation mask,
so `cmdTranslationOkB` below has one case per command shape and this module does
not need `CpcMini/Proofs/Assumptions.lean`.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The refutation check -/

/--
The assumption term `F` of `correct___eo_is_refutation`, built from the parser's
assumptions in file order.

`__eo_invoke_assume_list` pushes the head of an `and`-chain last, and the parser
numbers premises against a stack whose first assumption is at the bottom, so the
chain lists the assumptions in reverse file order.  See `Cpc/Api.lean` for the
long version.
-/
def logos_assumption_term (assums : List Term) : Term :=
  assums.foldl
    (fun rest A => Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest)
    (Term.Boolean true)

/--
Push one input assumption with the guard `__eo_invoke_assume_list` applies: the
assumption must be Boolean-typed and closed, or the state goes `Stuck`.  This is
*not* `logos_invoke_assume` (`CpcMini/Logos.lean`), which pushes without the
guard; `checkerTypeInvariant` and `StableAssumptionList` both depend on it.
-/
def logos_invoke_input_assume (s : CState) (A : Term) : CState :=
  __eo_push_input_assume_check (__eo_and (__eo_is_bool_type A) (__eo_is_closed A)) A s

/--
The refutation check the executable runs; equal to
`__eo_checker_is_refutation (logos_assumption_term assums) cmds` by
`logos_check_refutation_eq_checker` in `CpcMini/ApiChecks.lean`.
-/
def logos_check_refutation (assums : List Term) (cmds : CCmdList) : native_Bool :=
  __eo_state_is_refutation
    (__eo_invoke_cmd_list (assums.foldl logos_invoke_input_assume logos_init_state) cmds)

/-! ## The translation side conditions

`Bool` mirrors of the predicates of `CpcMini/Proofs/Assumptions.lean`;
`CpcMini/ApiChecks.lean` proves `mirror = true -> predicate`.
-/

/-- Mirror of `eoHasSmtTranslation`. -/
def eoHasSmtTranslationB (t : Term) : Bool :=
  __smtx_typeof (__eo_to_smt t) != SmtType.None

/-- Mirror of `cArgListTranslationOk`. -/
def cArgListTranslationOkB : CArgList -> Bool
  | CArgList.nil => true
  | CArgList.cons a args => eoHasSmtTranslationB a && cArgListTranslationOkB args

/-- Mirror of `cmdTranslationOk`, case for case. -/
def cmdTranslationOkB : CCmd -> Bool
  | CCmd.assume_push A => eoHasSmtTranslationB A
  | CCmd.step _ args _ => cArgListTranslationOkB args
  | _ => true

/--
Decides `TranslatableAssumptionList (logos_assumption_term assums)`, the first
hypothesis of `correct___eo_is_refutation`.
-/
def logos_check_translatableAssumptionList : List Term -> Bool
  | [] => true
  | A :: assums => eoHasSmtTranslationB A && logos_check_translatableAssumptionList assums

/-- Decides `CmdListTranslationOk cmds`, the second hypothesis of `correct___eo_is_refutation`. -/
def logos_check_cmdListTranslationOk : CCmdList -> Bool
  | CCmdList.nil => true
  | CCmdList.cons c cmds => cmdTranslationOkB c && logos_check_cmdListTranslationOk cmds

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
    | i, A :: assums => if eoHasSmtTranslationB A then go (i + 1) assums else some (i, A)

/--
The first command whose arguments fail their translation side condition, with its
position in file order among the proof-stack commands.
-/
def logos_untranslatable_cmd (cmds : CCmdList) : Option (Nat × CCmd) :=
  go 0 cmds
where
  go : Nat -> CCmdList -> Option (Nat × CCmd)
    | _, CCmdList.nil => none
    | i, CCmdList.cons c cmds => if cmdTranslationOkB c then go (i + 1) cmds else some (i, c)

end Eo
