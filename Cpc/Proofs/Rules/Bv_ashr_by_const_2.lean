module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
This rule is currently unsound because its premises constrain the integer
`amount`, while `bvashr` uses `int_to_bv sz amount` and therefore sees the
amount modulo `2^sz`.  For example, take `x = #b01`, `amount = 4`, `sz = 2`,
`nm = 1`, and `rn = 2`.  All three premises hold, but the encoded amount is
`int_to_bv 2 4 = #b00`, so the left side is `#b01 bvashr #b00 = #b01` while
the right side repeats the zero sign bit twice and is `#b00`.

A sound version must prevent this wraparound (for example, by requiring
`amount < 2^sz`) or handle wrapped amounts explicitly.  The proof remains
unfinished until the rule specification is corrected.
-/

private abbrev counterApp1 (op x : Term) : Term := Term.Apply op x
private abbrev counterApp2 (op x y : Term) : Term :=
  Term.Apply (Term.Apply op x) y

private def bvAshrByConst2CounterX : Term := Term.Binary 2 1
private def bvAshrByConst2CounterAmount : Term := Term.Numeral 4
private def bvAshrByConst2CounterSize : Term := Term.Numeral 2
private def bvAshrByConst2CounterNm : Term := Term.Numeral 1
private def bvAshrByConst2CounterRn : Term := Term.Numeral 2

private def bvAshrByConst2CounterP1 : Term :=
  counterApp2 (Term.UOp UserOp.eq)
    (counterApp2 (Term.UOp UserOp.geq) bvAshrByConst2CounterAmount
      (counterApp1 (Term.UOp UserOp._at_bvsize) bvAshrByConst2CounterX))
    (Term.Boolean true)

private def bvAshrByConst2CounterP2 : Term :=
  counterApp2 (Term.UOp UserOp.eq) bvAshrByConst2CounterNm
    (counterApp2 (Term.UOp UserOp.neg)
      (counterApp1 (Term.UOp UserOp._at_bvsize) bvAshrByConst2CounterX)
      (Term.Numeral 1))

private def bvAshrByConst2CounterP3 : Term :=
  counterApp2 (Term.UOp UserOp.eq) bvAshrByConst2CounterRn
    (counterApp1 (Term.UOp UserOp._at_bvsize) bvAshrByConst2CounterX)

private def bvAshrByConst2CounterResult : Term :=
  __eo_prog_bv_ashr_by_const_2 bvAshrByConst2CounterX
    bvAshrByConst2CounterAmount bvAshrByConst2CounterSize
    bvAshrByConst2CounterNm bvAshrByConst2CounterRn
    (Proof.pf bvAshrByConst2CounterP1)
    (Proof.pf bvAshrByConst2CounterP2)
    (Proof.pf bvAshrByConst2CounterP3)

private def bvAshrByConst2CounterExpected : Term :=
  counterApp2 (Term.UOp UserOp.eq)
    (counterApp2 (Term.UOp UserOp.bvashr) bvAshrByConst2CounterX
      (counterApp1
        (Term.UOp1 UserOp1.int_to_bv bvAshrByConst2CounterSize)
        bvAshrByConst2CounterAmount))
    (counterApp1 (Term.UOp1 UserOp1.repeat bvAshrByConst2CounterRn)
      (counterApp1
        (Term.UOp2 UserOp2.extract bvAshrByConst2CounterNm
          bvAshrByConst2CounterNm)
        bvAshrByConst2CounterX))

/-- A mechanically checked closed counterexample to the current rule. -/
private theorem bv_ashr_by_const_2_closed_counterexample (M : SmtModel) :
    __eo_typeof bvAshrByConst2CounterP1 = Term.Bool ∧
      __eo_typeof bvAshrByConst2CounterP2 = Term.Bool ∧
      __eo_typeof bvAshrByConst2CounterP3 = Term.Bool ∧
      __eo_typeof bvAshrByConst2CounterResult = Term.Bool ∧
      __smtx_model_eval M (__eo_to_smt bvAshrByConst2CounterP1) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M (__eo_to_smt bvAshrByConst2CounterP2) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M (__eo_to_smt bvAshrByConst2CounterP3) =
        SmtValue.Boolean true ∧
      __smtx_model_eval M (__eo_to_smt bvAshrByConst2CounterResult) =
        SmtValue.Boolean false := by
  have hShape :
      bvAshrByConst2CounterResult = bvAshrByConst2CounterExpected := by
    native_decide
  refine ⟨by native_decide, by native_decide, by native_decide,
    by native_decide, rfl, rfl, rfl, ?_⟩
  rw [hShape]
  simp [bvAshrByConst2CounterExpected, counterApp1, counterApp2,
    bvAshrByConst2CounterX, bvAshrByConst2CounterAmount,
    bvAshrByConst2CounterSize, bvAshrByConst2CounterNm,
    bvAshrByConst2CounterRn, __smtx_model_eval.eq_def]

public theorem cmd_step_bv_ashr_by_const_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ashr_by_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ashr_by_const_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ashr_by_const_2 args premises) :=
by
  sorry
