module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
This rule is currently unsound because `n` and `m` are not constrained to
make the extended product wide enough to avoid signed overflow.  For example,
take width-four constants `x = #b0111`, `y = #b1111`, and `a = #b0010`, with
`n = m = 0` and `tn = an = 4`.  Both size premises hold.  On the left, the
two products are both `#b1110`, so the strict signed comparison is false.  On
the right, `x != y`, `a != 0`, `y bvslt x`, and `a bvsgt 0` all hold, so the
right side is true.

A sound version must constrain the extension amounts so multiplication cannot
overflow (or account for overflow explicitly).  The proof remains unfinished
until that condition is represented by the rule specification.
-/

private abbrev counterApp1 (op x : Term) : Term := Term.Apply op x
private abbrev counterApp2 (op x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private def bvMultSltMult1CounterX : Term := Term.Binary 4 7
private def bvMultSltMult1CounterY : Term := Term.Binary 4 15
private def bvMultSltMult1CounterA : Term := Term.Binary 4 2

private def bvMultSltMult1CounterSizePrem (x : Term) : Term :=
  counterApp2 (Term.UOp UserOp.eq) (Term.Numeral 4)
    (counterApp1 (Term.UOp UserOp._at_bvsize) x)

private def bvMultSltMult1CounterResult : Term :=
  __eo_prog_bv_mult_slt_mult_1
    bvMultSltMult1CounterX bvMultSltMult1CounterY bvMultSltMult1CounterA
    (Term.Numeral 0) (Term.Numeral 0) (Term.Numeral 4) (Term.Numeral 4)
    (Proof.pf (bvMultSltMult1CounterSizePrem bvMultSltMult1CounterX))
    (Proof.pf (bvMultSltMult1CounterSizePrem bvMultSltMult1CounterA))

private def bvMultSltMult1CounterExpected : Term :=
  let eqOp := Term.UOp UserOp.eq
  let andOp := Term.UOp UserOp.and
  let notOp := Term.UOp UserOp.not
  let mulOp := Term.UOp UserOp.bvmul
  let sltOp := Term.UOp UserOp.bvslt
  let sgtOp := Term.UOp UserOp.bvsgt
  let subOp := Term.UOp UserOp.bvsub
  let sx0 := Term.UOp1 UserOp1.sign_extend (Term.Numeral 0)
  let zero :=
    counterApp1 (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 4))
      (Term.Numeral 0)
  let one := Term.Binary 4 1
  let lhs :=
    counterApp2 sltOp
      (counterApp2 mulOp (counterApp1 sx0 bvMultSltMult1CounterY)
        (counterApp2 mulOp (counterApp1 sx0 bvMultSltMult1CounterA) one))
      (counterApp2 mulOp (counterApp1 sx0 bvMultSltMult1CounterX)
        (counterApp2 mulOp (counterApp1 sx0 bvMultSltMult1CounterA) one))
  let rhs :=
    counterApp2 andOp
      (counterApp1 notOp
        (counterApp2 eqOp
          (counterApp2 subOp bvMultSltMult1CounterY bvMultSltMult1CounterX)
          zero))
      (counterApp2 andOp
        (counterApp1 notOp
          (counterApp2 eqOp bvMultSltMult1CounterA zero))
        (counterApp2 andOp
          (counterApp2 eqOp
            (counterApp2 sltOp bvMultSltMult1CounterY bvMultSltMult1CounterX)
            (counterApp2 sgtOp bvMultSltMult1CounterA zero))
          (Term.Boolean true)))
  counterApp2 eqOp lhs rhs

/-- A mechanically checked closed counterexample to the current rule. -/
private theorem bv_mult_slt_mult_1_closed_counterexample (M : SmtModel) :
    __eo_typeof (bvMultSltMult1CounterSizePrem bvMultSltMult1CounterX) =
        Term.Bool ∧
      __eo_typeof (bvMultSltMult1CounterSizePrem bvMultSltMult1CounterA) =
        Term.Bool ∧
      __eo_typeof bvMultSltMult1CounterResult = Term.Bool ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvMultSltMult1CounterSizePrem bvMultSltMult1CounterX)) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvMultSltMult1CounterSizePrem bvMultSltMult1CounterA)) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M (__eo_to_smt bvMultSltMult1CounterResult) =
        SmtValue.Boolean false := by
  have hShape :
      bvMultSltMult1CounterResult = bvMultSltMult1CounterExpected := by
    native_decide
  refine ⟨by native_decide, by native_decide, by native_decide,
    rfl, rfl, ?_⟩
  rw [hShape]
  simp [bvMultSltMult1CounterExpected, counterApp1, counterApp2,
    bvMultSltMult1CounterX, bvMultSltMult1CounterY, bvMultSltMult1CounterA,
    __smtx_model_eval.eq_def]

public theorem cmd_step_bv_mult_slt_mult_1_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_mult_slt_mult_1 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_mult_slt_mult_1 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_mult_slt_mult_1 args premises) :=
by
  sorry
