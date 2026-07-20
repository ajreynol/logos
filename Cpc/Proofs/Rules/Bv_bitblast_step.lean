module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Logos
import all Cpc.SmtModel
import all Cpc.Proofs.Common
import all Cpc.Proofs.Assumptions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
This rule is currently unsound for two independent reasons.

First, `__bv_bitblast_ult` accepts an `orEqual` argument but does not use it.
Consequently, the `bvule` branch implements strict unsigned comparison.  The
same omission reaches the recursive magnitude comparison in the multi-bit
`bvsle` branch.  Equal operands therefore give a counterexample.

Second, the bitwise, addition, and multiplication helpers expect their right
operand to be a right-nested operator list ending in the operator's identity.
Their fallback case returns the accumulated left operand.  A well-typed plain
binary application is also admitted by the rule theorem, however, and its
right operand is then silently dropped.  The closed examples below exercise
all three affected fold helpers.

The comparison helper should incorporate `orEqual` into its least-significant
bit seed (or start the recurrence from `orEqual`).  The fold helpers should
either process a final bit-vector operand or the rule must require the
canonical right-spine representation.  The proof remains unfinished until
these cases are fixed or excluded by the rule specification.
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
