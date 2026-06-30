import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
BLOCKED (framework gap, not a proof-difficulty gap).

This rule's conclusion is
  eq (int_to_bv w (ubv_to_int t)) (concat (@bv 0 n) (concat t (Binary 0 0)))
where the zero-extension amount `n = w - bvsize t` is supplied as an argument and
constrained to be positive only by the *premise* `gt w (bvsize t) = true`.

`StepRuleProperties.has_smt_translation` is an UNCONDITIONAL obligation: it must show
`__smtx_typeof (__eo_to_smt P) ≠ None` given only `cmdTranslationOk`,
`AllHaveBoolType (premiseTermList …)`, and `__eo_typeof P = Term.Bool`. It does NOT
receive premise truth (only `facts_of_true` does, via `RulePremiseEvidence`).

Root cause: the EO and SMT typings of `@bv` diverge.
  • `__eo_typeof__at_bv` (Cpc/Logos.lean:8504) returns `BitVec w` for ANY width `w`,
    with no `w ≥ 0` guard — unlike `int_to_bv`/`extract`/`repeat`, which all guard
    `w > -1`.
  • The SMT side translates a negative-width `@bv` to `None`.
Machine-checked: `__eo_typeof (@bv 0 (-1)) = BitVec (Numeral (-1))` (not Stuck), but
`__smtx_typeof (__eo_to_smt (@bv 0 (-1))) = None`. So for `n = -1` (i.e. `w < bvsize t`)
every theorem hypothesis holds while `has_smt_translation P` is false — a genuine
counterexample.

Fix requires a spec/framework change (out of scope for a rule proof): e.g. add a
`w > -1` guard to `__eo_typeof__at_bv`, after which `__eo_typeof P = Bool` forces
`n ≥ 0` and the rule becomes provable exactly like `Uf_bv2nat_int2bv`. A WIP proof
that closes everything EXCEPT this `n ≥ 0` obligation is preserved in the session
scratchpad.
-/
theorem cmd_step_uf_bv2nat_int2bv_extend_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv_extend args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extend args premises) :=
by
  sorry
