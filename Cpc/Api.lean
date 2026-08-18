module

public import Cpc.Logos
import all Cpc.Logos
public import Cpc.Spec
import all Cpc.Spec
public import Cpc.Proofs.Assumptions
import all Cpc.Proofs.Assumptions

@[expose] public section

/-!
# The entry point that the `logos` executable runs

This module is the bridge between the parser -- `Cpc/Parser.lean`, which turns a
proof file into a `List Term` of assumptions and a `CCmdList` of commands -- and
the soundness theorem `correct___eo_is_refutation` of `Cpc/Proofs/Checker.lean`:

```
theorem correct___eo_is_refutation (F : Term) (pf : CCmdList) :
  TranslatableAssumptionList F ->
  CmdListTranslationOk pf ->
  (eo_is_refutation F pf) ->
  eo_satisfiability F false
```

Everything that theorem needs is computed here, so that the `correct` printed by
the executable means the theorem's conclusion and nothing weaker.  Each of its
three hypotheses has one runtime counterpart:

| hypothesis of the theorem       | computed by                                |
| ------------------------------- | ------------------------------------------ |
| the term `F`                    | `logos_assumption_term assums`             |
| `eo_is_refutation F pf`         | `logos_check_refutation assums cmds`       |
| `TranslatableAssumptionList F`  | `logos_check_translatableAssumptionList`   |
| `CmdListTranslationOk pf`       | `logos_check_cmdListTranslationOk`         |

Nothing in this file is trusted.  `Cpc/ApiChecks.lean` proves that each check
implies the hypothesis it stands for, and `Cpc/ApiCorrect.lean` assembles those
into `correct___logos_check_refutation`, a theorem stated about the very
expression `Main.lean` evaluates.

The definitions here are deliberately *not* in `Cpc/Logos.lean`: that file is
generated from the calculus, and its `logos_invoke_assume` pushes an input
assumption without the well-formedness guard that `__eo_invoke_assume_list`
applies (see `logos_invoke_input_assume` below).  The Lean-native front end
(`MainNative.lean`, and the `#eval` scripts cvc5 emits for it) still goes
through the generated API and so is not yet covered by
`correct___logos_check_refutation`.
-/

open SmtEval
open Smtm

namespace Eo

/-! ## The refutation check

`eo_is_refutation F pf` holds when `__eo_checker_is_refutation F pf` is `true`,
i.e. when running `pf` from the state `__eo_invoke_assume_list CState.nil F`
ends in a closed state that has proven `false`.  The two definitions below
compute that state from the parser's output instead of from an `and`-chain, and
`Cpc/ApiChecks.lean` proves the two agree.
-/

/--
The assumption term `F` of `correct___eo_is_refutation`, built from the
assumptions the parser produced in file order.

The order is not the obvious one.  `__eo_invoke_assume_list` consumes an
`and`-chain by pushing its head *last*, so the head of the chain ends up on top
of the proof stack.  The parser numbers premises against a stack whose *first*
assumption is at the bottom (`registerStep` and `parsePremise` in
`Logos/Parser.lean`), so the chain that matches the parser's numbering lists the
assumptions in reverse file order: for assumptions `A1 ... An` this builds

    (and An (and A(n-1) ... (and A1 true) ... ))

which `__eo_invoke_assume_list` pushes as `A1` first and `An` on top.  Building
the chain the other way round cannot silently accept a bad proof -- premise
indices then resolve to the wrong stack entries and the checker rejects -- but
it would make the theorem talk about a different `F`.
-/
def logos_assumption_term (assums : List Term) : Term :=
  assums.foldl
    (fun rest A => Term.Apply (Term.Apply (Term.UOp UserOp.and) A) rest)
    (Term.Boolean true)

/--
Push one input assumption, applying the well-formedness guard that
`__eo_invoke_assume_list` applies to each element of the `and`-chain: the
assumption must be Boolean-typed and closed, or the state goes `Stuck`.

This is deliberately *not* `logos_invoke_assume` (`Cpc/Logos.lean`), which
pushes an input assumption with no guard at all.  The guard is not cosmetic:
`__eo_typeof A = Term.Bool` for `assume` entries is what `checkerTypeInvariant`
requires (`Cpc/Proofs/CheckerCore.lean`), and closedness is what yields
`StableAssumptionList`, so dropping it puts the run outside the reach of the
soundness proof.  Folding this function over the parser's assumption list is
equal to `__eo_invoke_assume_list CState.nil (logos_assumption_term assums)` --
that is `invoke_assume_list_eq_fold` in `Cpc/ApiChecks.lean` -- with the
difference that a fold needs no stack, while `__eo_invoke_assume_list` recurses
once per assumption.
-/
def logos_invoke_input_assume (s : CState) (A : Term) : CState :=
  __eo_push_input_assume_check (__eo_and (__eo_is_bool_type A) (__eo_is_closed A)) A s

/--
The refutation check the executable runs.  `logos_check_refutation_eq_checker`
(`Cpc/ApiChecks.lean`) proves

    logos_check_refutation assums cmds
      = __eo_checker_is_refutation (logos_assumption_term assums) cmds

so this returning `true` is exactly `eo_is_refutation (logos_assumption_term assums) cmds`.
-/
def logos_check_refutation (assums : List Term) (cmds : CCmdList) : native_Bool :=
  __eo_state_is_refutation
    (__eo_invoke_cmd_list (assums.foldl logos_invoke_input_assume logos_init_state) cmds)

/-! ## The translation side conditions

`correct___eo_is_refutation` also assumes `TranslatableAssumptionList F` and
`CmdListTranslationOk pf`: the rule proofs only interpret an EO term through
`__eo_to_smt`, so terms with no SMT-LIB counterpart are excluded.  Those
predicates (`Cpc/Proofs/Assumptions.lean`) are decidable, and the functions
below decide them.

Each `...B` function is a `Bool` mirror of the predicate of the same name, and
`Cpc/ApiChecks.lean` proves `mirror = true -> predicate`.  That direction is the
one that matters, and it also keeps the mirrors honest: a mirror that checked
*less* than its predicate would fail to compile there, while a mirror that
checks *more* only ever rejects proofs the theorem would not have covered.
-/

/-- Mirror of `eoHasSmtTranslation`. -/
def eoHasSmtTranslationB (t : Term) : Bool :=
  __smtx_typeof (__eo_to_smt t) != SmtType.None

/-- Mirror of `EoListAllHaveSmtTranslation`. -/
def eoListAllHaveSmtTranslationB : Term -> Bool
  | Term.__eo_List_nil => true
  | Term.Apply (Term.Apply Term.__eo_List_cons t) ts =>
      eoHasSmtTranslationB t && eoListAllHaveSmtTranslationB ts
  | _ => false

/-- Mirror of `argTranslationOkMasked`. -/
def argTranslationOkMaskedB : ArgTranslationKind -> Term -> Bool
  | ArgTranslationKind.term, t => eoHasSmtTranslationB t
  | ArgTranslationKind.list, t => eoListAllHaveSmtTranslationB t
  | ArgTranslationKind.type, t => __smtx_type_wf (__eo_to_smt_type t)
  | ArgTranslationKind.wfTerm, t =>
      eoHasSmtTranslationB t && __smtx_type_wf (__smtx_typeof (__eo_to_smt t))
  | ArgTranslationKind.wfElem, t =>
      __smtx_type_wf_component (__smtx_typeof (__eo_to_smt t))

/-- Mirror of `cArgListTranslationOk`. -/
def cArgListTranslationOkB : CArgList -> Bool
  | CArgList.nil => true
  | CArgList.cons a args => eoHasSmtTranslationB a && cArgListTranslationOkB args

/-- Mirror of `cArgListTranslationOkMask`. -/
def cArgListTranslationOkMaskB : List ArgTranslationKind -> CArgList -> Bool
  | [], CArgList.nil => true
  | kind :: mask, CArgList.cons a args =>
      argTranslationOkMaskedB kind a && cArgListTranslationOkMaskB mask args
  | _, _ => false

/--
Mirror of `cmdTranslationOk`, case for case.  When a rule is given a mask in
`Cpc/Proofs/Assumptions.lean` it gets the same mask here; every other rule falls
back to `cArgListTranslationOkB` on its arguments.
-/
def cmdTranslationOkB : CCmd -> Bool
  | CCmd.assume_push A => eoHasSmtTranslationB A
  | CCmd.step CRule.chain_resolution args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.list, ArgTranslationKind.list] args
  | CCmd.step CRule.chain_m_resolution args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.list,
        ArgTranslationKind.list] args
  | CCmd.step CRule.instantiate args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.list] args
  | CCmd.step CRule.alpha_equiv args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.list,
        ArgTranslationKind.list] args
  | CCmd.step CRule.distinct_binary_elim args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.wfTerm, ArgTranslationKind.term] args
  | CCmd.step CRule.exists_string_length args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.type, ArgTranslationKind.term,
        ArgTranslationKind.term] args
  | CCmd.step CRule.sets_eq_singleton_emp args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_member_emp args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_inter_emp1 args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_inter_emp2 args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_minus_emp1 args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_minus_emp2 args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_union_emp1 args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_union_emp2 args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_minus_self args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.sets_is_empty_elim args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_empty_range args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_empty_start args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_empty_start_neg args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_substr_start_geq_len args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.str_concat_unify_base args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_concat_unify_base_rev args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_contains_char args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.str_len_eq_zero_concat_rec args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_len_eq_zero_base args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.type] args
  | CCmd.step CRule.str_indexof_self args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.str_substr_char_start_eq_len args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.term,
        ArgTranslationKind.type] args
  | CCmd.step CRule.sets_member_singleton args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.term, ArgTranslationKind.wfElem] args
  | CCmd.step CRule.sets_choose_singleton args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.wfElem] args
  | CCmd.step CRule.seq_len_unit args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.wfElem] args
  | CCmd.step CRule.seq_rev_unit args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.wfElem] args
  | CCmd.step CRule.seq_nth_unit args _ =>
      cArgListTranslationOkMaskB [ArgTranslationKind.wfElem] args
  | CCmd.step _ args _ => cArgListTranslationOkB args
  | _ => true

/--
Decides `TranslatableAssumptionList (logos_assumption_term assums)`, the first
hypothesis of `correct___eo_is_refutation`.  Written as a fold over the parser's
list rather than over the `and`-chain, so it needs no stack.
-/
def logos_check_translatableAssumptionList : List Term -> Bool
  | [] => true
  | A :: assums => eoHasSmtTranslationB A && logos_check_translatableAssumptionList assums

/-- Decides `CmdListTranslationOk cmds`, the second hypothesis of `correct___eo_is_refutation`. -/
def logos_check_cmdListTranslationOk : CCmdList -> Bool
  | CCmdList.nil => true
  | CCmdList.cons c cmds => cmdTranslationOkB c && logos_check_cmdListTranslationOk cmds

/-! ## Diagnostics

Used only to report *why* a proof fell outside the fragment the specification
covers, once one of the two checks above has already returned `false`.  They have
no role in the correctness statement.
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
