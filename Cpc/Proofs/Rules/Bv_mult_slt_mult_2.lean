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
take width-four constants `x = #b0111`, `y = #b0001`, and `a = #b0100`, with
`n = m = 0` and `tn = an = 4`.  Both size premises hold.  On the left,
`y * a = #b0100` while `x * a = #b1100`, so the strict signed comparison is
false (`4` is not less than `-4`).  On the right, `x != y`, `a != 0`,
`y bvult x`, and `a bvsgt 0` all hold, so the right side is true.

A sound version must constrain the extension amounts so multiplication cannot
overflow (or account for overflow explicitly).  The proof remains unfinished
until that condition is represented by the rule specification.
-/

private abbrev counterApp1 (op x : Term) : Term := Term.Apply op x
private abbrev counterApp2 (op x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private def bvMultSltMult2CounterX : Term := Term.Binary 4 7
private def bvMultSltMult2CounterY : Term := Term.Binary 4 1
private def bvMultSltMult2CounterA : Term := Term.Binary 4 4

private def bvMultSltMult2CounterSizePrem (x : Term) : Term :=
  counterApp2 (Term.UOp UserOp.eq) (Term.Numeral 4)
    (counterApp1 (Term.UOp UserOp._at_bvsize) x)

private def bvMultSltMult2CounterResult : Term :=
  __eo_prog_bv_mult_slt_mult_2
    bvMultSltMult2CounterX bvMultSltMult2CounterY bvMultSltMult2CounterA
    (Term.Numeral 0) (Term.Numeral 0) (Term.Numeral 4) (Term.Numeral 4)
    (Proof.pf (bvMultSltMult2CounterSizePrem bvMultSltMult2CounterX))
    (Proof.pf (bvMultSltMult2CounterSizePrem bvMultSltMult2CounterA))

private def bvMultSltMult2CounterExpected : Term :=
  let eqOp := Term.UOp UserOp.eq
  let andOp := Term.UOp UserOp.and
  let notOp := Term.UOp UserOp.not
  let mulOp := Term.UOp UserOp.bvmul
  let sltOp := Term.UOp UserOp.bvslt
  let ultOp := Term.UOp UserOp.bvult
  let sgtOp := Term.UOp UserOp.bvsgt
  let subOp := Term.UOp UserOp.bvsub
  let zx0 := Term.UOp1 UserOp1.zero_extend (Term.Numeral 0)
  let sx0 := Term.UOp1 UserOp1.sign_extend (Term.Numeral 0)
  let zero :=
    counterApp1 (Term.UOp1 UserOp1.int_to_bv (Term.Numeral 4))
      (Term.Numeral 0)
  let one := Term.Binary 4 1
  let lhs :=
    counterApp2 sltOp
      (counterApp2 mulOp (counterApp1 zx0 bvMultSltMult2CounterY)
        (counterApp2 mulOp (counterApp1 sx0 bvMultSltMult2CounterA) one))
      (counterApp2 mulOp (counterApp1 zx0 bvMultSltMult2CounterX)
        (counterApp2 mulOp (counterApp1 sx0 bvMultSltMult2CounterA) one))
  let rhs :=
    counterApp2 andOp
      (counterApp1 notOp
        (counterApp2 eqOp
          (counterApp2 subOp bvMultSltMult2CounterY bvMultSltMult2CounterX)
          zero))
      (counterApp2 andOp
        (counterApp1 notOp
          (counterApp2 eqOp bvMultSltMult2CounterA zero))
        (counterApp2 andOp
          (counterApp2 eqOp
            (counterApp2 ultOp bvMultSltMult2CounterY bvMultSltMult2CounterX)
            (counterApp2 sgtOp bvMultSltMult2CounterA zero))
          (Term.Boolean true)))
  counterApp2 eqOp lhs rhs

/-- A mechanically checked closed counterexample to the current rule. -/
private theorem bv_mult_slt_mult_2_closed_counterexample (M : SmtModel) :
    __eo_typeof (bvMultSltMult2CounterSizePrem bvMultSltMult2CounterX) =
        Term.Bool ∧
      __eo_typeof (bvMultSltMult2CounterSizePrem bvMultSltMult2CounterA) =
        Term.Bool ∧
      __eo_typeof bvMultSltMult2CounterResult = Term.Bool ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvMultSltMult2CounterSizePrem bvMultSltMult2CounterX)) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M
          (__eo_to_smt
            (bvMultSltMult2CounterSizePrem bvMultSltMult2CounterA)) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M (__eo_to_smt bvMultSltMult2CounterResult) =
        SmtValue.Boolean false := by
  have hShape :
      bvMultSltMult2CounterResult = bvMultSltMult2CounterExpected := by
    native_decide
  refine ⟨by native_decide, by native_decide, by native_decide,
    rfl, rfl, ?_⟩
  rw [hShape]
  simp [bvMultSltMult2CounterExpected, counterApp1, counterApp2,
    bvMultSltMult2CounterX, bvMultSltMult2CounterY, bvMultSltMult2CounterA,
    __smtx_model_eval.eq_def]

public theorem cmd_step_bv_mult_slt_mult_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_mult_slt_mult_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_mult_slt_mult_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_mult_slt_mult_2 args premises) :=
by
  sorry
