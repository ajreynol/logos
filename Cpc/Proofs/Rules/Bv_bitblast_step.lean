module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
This rule was previously unsound for two independent reasons, both now fixed
in the corresponding definitions in `Cpc.Logos`.

First, `__bv_bitblast_ult` accepted an `orEqual` argument but did not use it,
so the `bvule` branch (and the recursive magnitude comparison in the multi-bit
`bvsle` branch) implemented strict unsigned comparison and gave a wrong answer
on equal operands.  `__bv_bitblast_ult` now seeds `__bv_bitblast_ult_rec` from
`orEqual`: the seed is one comparison step applied to the least-significant bit
with prior result `orEqual`, so equal operands reduce to `orEqual` (`true` for
`bvule`/`bvsle`, `false` for `bvult`/`bvslt`).  With `orEqual = false` the seed
reduces to the original strict seed, so `bvult`/`bvslt` are unchanged.

Second, the bitwise, addition, and multiplication fold helpers expect their
right operand to be a right-nested operator spine ending in the operator's
identity.  Their fallback case returned the accumulated left operand, silently
dropping the terminal operand.  A well-typed plain binary application is also
admitted by the rule theorem, and there the right operand was dropped, giving
a wrong bit-blasting.  The fallbacks now guard with `__eo_requires` that the
terminal operand is the operator's nil (`__eo_is_list_nil`); a non-identity
terminal (e.g. the right operand of a plain binary application) yields
`Term.Stuck`, so `__eo_prog_bv_bitblast_step` produces a non-`Bool` result and
the rule theorem's well-typedness hypothesis excludes the case.

The `private def`s below exercise all affected paths and now evaluate either to
a valid instance (`bvule`) or to `Term.Stuck` (the three fold helpers), rather
than to an unsound equality.  The soundness proof is still outstanding.
-/

private abbrev bitblastCounterApp2 (op x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private def bitblastCounterBit (b : Bool) : Term :=
  bitblastCounterApp2 (Term.UOp UserOp._at_from_bools)
    (Term.Boolean b) (Term.Binary 0 0)

private def bitblastCounterResult (expr : Term) : Term :=
  __eo_prog_bv_bitblast_step
    (bitblastCounterApp2 (Term.UOp UserOp.eq) expr
      (__bv_mk_bitblast_step expr))

private def bitblastUleCounterResult : Term :=
  let zero := bitblastCounterBit false
  bitblastCounterResult
    (bitblastCounterApp2 (Term.UOp UserOp.bvule) zero zero)

private def bitblastAndCounterResult : Term :=
  bitblastCounterResult
    (bitblastCounterApp2 (Term.UOp UserOp.bvand)
      (bitblastCounterBit true) (bitblastCounterBit false))

private def bitblastAddCounterResult : Term :=
  bitblastCounterResult
    (bitblastCounterApp2 (Term.UOp UserOp.bvadd)
      (bitblastCounterBit true) (bitblastCounterBit true))

private def bitblastMulCounterResult : Term :=
  bitblastCounterResult
    (bitblastCounterApp2 (Term.UOp UserOp.bvmul)
      (bitblastCounterBit true) (bitblastCounterBit false))

public theorem cmd_step_bv_bitblast_step_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_bitblast_step args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_bitblast_step args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_bitblast_step args premises) :=
by
  sorry
