module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
This rule is currently unsound because `x1i` and `y1i` are used both as
integer prefixes and as arguments of `int_to_bv`, but the premises do not
constrain them to the unsigned range of their prefix widths.  In particular,
`int_log2 (-1) = 0`, so the leading-zero bound treats a negative prefix as
having only one significant bit, while `int_to_bv n (-1)` is `n` one bits.

For the closed example below, each operand has width 65.  The first prefix is
`int_to_bv 64 (-1)`, the second operand is one, and the bound permits
extracting bits 64 through 3 as zero.  Their product is instead `2^65 - 2`,
so that extract is nonzero.

A sound version should require each prefix integer `i` to satisfy
`0 <= i < 2^in` before using `int_log2 i` to count leading zeros (or compute
the bound from the wrapped bit-vector prefix itself).  The proof remains
unfinished until that range condition is represented by the specification.
-/

private abbrev extractLeadingCounterApp1 (op x : Term) : Term :=
  Term.Apply op x

private abbrev extractLeadingCounterApp2 (op x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private abbrev extractLeadingCounterApp3 (op x y z : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply op x) y) z

private def extractLeadingCounterHigh : Term := Term.Numeral 64
private def extractLeadingCounterLow : Term := Term.Numeral 3
private def extractLeadingCounterXi : Term := Term.Numeral (-1)
private def extractLeadingCounterXin : Term := Term.Numeral 64
private def extractLeadingCounterX : Term := Term.Binary 1 0
private def extractLeadingCounterYi : Term := Term.Numeral 0
private def extractLeadingCounterYin : Term := Term.Numeral 64
private def extractLeadingCounterY : Term := Term.Binary 1 1
private def extractLeadingCounterW : Term := Term.Numeral 62

private def extractLeadingCounterP1 : Term :=
  extractLeadingCounterApp2 (Term.UOp UserOp.eq)
    (extractLeadingCounterApp2 (Term.UOp UserOp.gt)
      (extractLeadingCounterApp2 (Term.UOp UserOp.plus)
        extractLeadingCounterXin
        (extractLeadingCounterApp2 (Term.UOp UserOp.plus)
          (extractLeadingCounterApp1 (Term.UOp UserOp._at_bvsize)
            extractLeadingCounterX)
          (Term.Numeral 0)))
      (Term.Numeral 64))
    (Term.Boolean true)

private def extractLeadingCounterZeros (i n : Term) : Term :=
  extractLeadingCounterApp3 (Term.UOp UserOp.ite)
    (extractLeadingCounterApp2 (Term.UOp UserOp.eq) i (Term.Numeral 0))
    n
    (extractLeadingCounterApp2 (Term.UOp UserOp.neg) n
      (extractLeadingCounterApp2 (Term.UOp UserOp.plus) (Term.Numeral 1)
        (extractLeadingCounterApp2 (Term.UOp UserOp.plus)
          (extractLeadingCounterApp1 (Term.UOp UserOp.int_log2) i)
          (Term.Numeral 0))))

private def extractLeadingCounterP2 : Term :=
  extractLeadingCounterApp2 (Term.UOp UserOp.eq)
    (extractLeadingCounterApp2 (Term.UOp UserOp.leq)
      (extractLeadingCounterApp2 (Term.UOp UserOp.neg)
        (extractLeadingCounterApp2 (Term.UOp UserOp.mult) (Term.Numeral 2)
          (extractLeadingCounterApp2 (Term.UOp UserOp.mult)
            (extractLeadingCounterApp2 (Term.UOp UserOp.plus)
              extractLeadingCounterXin
              (extractLeadingCounterApp2 (Term.UOp UserOp.plus)
                (extractLeadingCounterApp1 (Term.UOp UserOp._at_bvsize)
                  extractLeadingCounterX)
                (Term.Numeral 0)))
            (Term.Numeral 1)))
        (extractLeadingCounterApp2 (Term.UOp UserOp.plus)
          (extractLeadingCounterZeros extractLeadingCounterXi
            extractLeadingCounterXin)
          (extractLeadingCounterApp2 (Term.UOp UserOp.plus)
            (extractLeadingCounterZeros extractLeadingCounterYi
              extractLeadingCounterYin)
            (Term.Numeral 0))))
      extractLeadingCounterLow)
    (Term.Boolean true)

private def extractLeadingCounterP3 : Term :=
  extractLeadingCounterApp2 (Term.UOp UserOp.eq) extractLeadingCounterW
    (extractLeadingCounterApp2 (Term.UOp UserOp.plus) (Term.Numeral 1)
      (extractLeadingCounterApp2 (Term.UOp UserOp.plus)
        (extractLeadingCounterApp2 (Term.UOp UserOp.neg)
          extractLeadingCounterHigh extractLeadingCounterLow)
        (Term.Numeral 0)))

private def extractLeadingCounterResult : Term :=
  __eo_prog_bv_extract_mult_leading_bit
    extractLeadingCounterHigh extractLeadingCounterLow
    extractLeadingCounterXi extractLeadingCounterXin extractLeadingCounterX
    extractLeadingCounterYi extractLeadingCounterYin extractLeadingCounterY
    extractLeadingCounterW
    (Proof.pf extractLeadingCounterP1)
    (Proof.pf extractLeadingCounterP2)
    (Proof.pf extractLeadingCounterP3)

/-- A mechanically checked closed counterexample to the current rule. -/
private theorem bv_extract_mult_leading_bit_closed_counterexample
    (M : SmtModel) :
    __eo_typeof extractLeadingCounterP1 = Term.Bool ∧
      __eo_typeof extractLeadingCounterP2 = Term.Bool ∧
      __eo_typeof extractLeadingCounterP3 = Term.Bool ∧
      __eo_typeof extractLeadingCounterResult = Term.Bool ∧
      __smtx_model_eval M (__eo_to_smt extractLeadingCounterP1) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M (__eo_to_smt extractLeadingCounterP2) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M (__eo_to_smt extractLeadingCounterP3) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M (__eo_to_smt extractLeadingCounterResult) =
        SmtValue.Boolean false := by
  refine ⟨by native_decide, by native_decide, by native_decide,
    by native_decide, rfl, rfl, rfl, rfl⟩

public theorem cmd_step_bv_extract_mult_leading_bit_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_extract_mult_leading_bit args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_extract_mult_leading_bit args premises) :=
by
  sorry
