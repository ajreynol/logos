import CpcMini.Proofs.CheckerCore
import CpcMini.Proofs.Rules.Support
import CpcMini.Proofs.Rules.Scope
import CpcMini.Proofs.Rules.Contra
import CpcMini.Proofs.Rules.Refl
import CpcMini.Proofs.Rules.Symm
import CpcMini.Proofs.Rules.Trans

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/- Central expansion point for plain `step` rules.

   To add a new rule handled by `__eo_cmd_step_proven`, add its matching
   pattern here and dispatch to the arity helper matching the rule shape.
   The preservation theorems below then pick the new rule up automatically. -/
theorem cmd_step_proven_facts_of_invariants
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (_hNotStuck : s ≠ CState.Stuck)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTruthInvariant M s ->
  checkerTypeInvariant s ->
  checkerTranslationInvariant s ->
  cmdTranslationOk (CCmd.step r args premises) ->
  __eo_cmd_step_proven s r args premises ≠ Term.Stuck ->
  CmdStepFacts M s (__eo_cmd_step_proven s r args premises)
:=
by
  intro hs hsTy hsTrans hCmdTrans hProg
  have hPremisesBool : AllHaveBoolType (premiseTermList s premises) :=
    premiseTermList_has_bool_type s premises hsTy hsTrans
  cases r with
  | scope =>
      exact False.elim (hProg (by simp [__eo_cmd_step_proven]))
  | contra =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_contra_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | refl =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_refl_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | symm =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_symm_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg
  | trans =>
      exact cmd_step_facts_of_rule_properties M s premises hs <|
        cmd_step_trans_properties M hM s args premises
          (by simpa using hCmdTrans) hPremisesBool hProg

/-
Central expansion point for `step_pop` rules.

If `__eo_cmd_step_pop_proven` grows more supported rules, add a matching
branch below and route it to the rule-specific helper.
-/
theorem cmd_step_pop_proven_facts_of_invariants
    (root tail : CState) (A : Term)
    (r : CRule) (args : CArgList) (premises : CIndexList) :
  checkerTypeInvariant root ->
  checkerTranslationInvariant root ->
  checkerTypeInvariant (CState.cons (CStateObj.assume_push A) tail) ->
  checkerTranslationInvariant (CState.cons (CStateObj.assume_push A) tail) ->
  __eo_cmd_step_pop_proven root r args A premises ≠ Term.Stuck ->
  CmdStepPopFacts root tail A (__eo_cmd_step_pop_proven root r args A premises)
:=
by
  intro hsRootTy hsRootTrans hsCurTy hsCurTrans hProg
  have hATy : __eo_typeof A = Term.Bool :=
    (checkerTypeInvariant_head_assume_push A tail hsCurTy).2
  have hATrans : RuleProofs.eo_has_smt_translation A :=
    checkerTranslationInvariant_head_assume_push A tail hsCurTrans
  have hPremisesTrans : AllHaveSmtTranslation (premiseTermList root premises) :=
    premiseTermList_has_smt_translation root premises hsRootTrans
  have hPremisesTy : AllTypeofBool (premiseTermList root premises) :=
    premiseTermList_has_typeof_bool root premises hsRootTy
  cases r with
  | scope =>
      exact cmd_step_pop_facts_of_rule_properties root tail A premises <|
        cmd_step_pop_scope_properties A root args premises
          hATrans hATy hPremisesTrans hPremisesTy hProg
  | contra =>
      exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
  | refl =>
      exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
  | symm =>
      exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
  | trans =>
      exact False.elim (hProg (by simp [__eo_cmd_step_pop_proven]))
