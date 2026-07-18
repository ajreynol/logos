import Cpc.Proofs.RuleSupport.Support

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

theorem cmd_step_bv_ashr_by_const_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_ashr_by_const_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_ashr_by_const_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_ashr_by_const_2 args premises) :=
by
  sorry
