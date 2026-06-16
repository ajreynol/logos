import Cpc.Proofs.RuleSupport.ReConcatNullableSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
Semantic soundness of this rule is fully established by
`RuleProofs.nullable2_eval_rel` in `ReConcatNullableSupport`: in any model in
which the conclusion is well typed, `xs · r · Σ* · ys` and `xs · Σ* · ys`
(with `r` nullable) denote the same language.  What remains is the mechanical
wrapper (argument/premise case-split, premise-shape recovery, typing extraction).
-/
theorem cmd_step_re_concat_star_nullable2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_concat_star_nullable2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_concat_star_nullable2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_concat_star_nullable2 args premises) :=
by
  sorry
