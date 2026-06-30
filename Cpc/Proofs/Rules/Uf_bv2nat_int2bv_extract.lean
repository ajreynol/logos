import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-
BLOCKED (framework gap, not a proof-difficulty gap). The sibling
`Uf_bv2nat_int2bv_extend` is now provable after `_at_bv` was tightened, but
this extract rule still has a separate EO/SMT typing mismatch.

This rule's conclusion is
  eq (int_to_bv w (ubv_to_int t)) (extract wm 0 t)
with `wm = w - 1` (premise) and `w < bvsize t` (premise). The degenerate boundary
`w = 0`, i.e. `wm = -1`, is the problem.

`StepRuleProperties.has_smt_translation` must show `__smtx_typeof (__eo_to_smt P) ≠ None`
UNCONDITIONALLY (no premise truth available). Root cause: EO and SMT extract typings
diverge.
  • `__eo_typeof_extract` (Cpc/Logos.lean) guards only `lo > -1` and `width > hi`, so
    `extract[-1:0]` is admitted as a 0-width `BitVec 0`.
  • `__smtx_typeof_extract` (Cpc/SmtModel.lean) ALSO requires `lo ≤ hi`, so
    `extract[-1:0]` translates to `None`.
Machine-checked counterexample (`w = 0`, `wm = -1`, `t = Binary 5 3`):
  `__eo_typeof P = Term.Bool` ✓, both premises have Bool type ✓, args translate ✓,
  but `__smtx_typeof (__eo_to_smt P) = None` ✗  (LHS `int_to_bv 0 …` → `BitVec 0`;
  RHS `extract[-1:0] t` → `None`; so the `eq` is `None`).

Fix requires a spec change (out of scope): tighten `__eo_typeof_extract` to also
require `lo ≤ hi` (matching the SMT side), after which `__eo_typeof P = Bool` forces
`0 ≤ wm` and the rule becomes provable (the `native_binary_extract` identity and the
rest of the proof are routine). A WIP proof that closes everything EXCEPT the `0 ≤ wm`
obligation is preserved in the session scratchpad.
-/
theorem cmd_step_uf_bv2nat_int2bv_extract_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.uf_bv2nat_int2bv_extract args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.uf_bv2nat_int2bv_extract args premises) :=
by
  sorry
