module

public import Cpc.Proofs.RuleSupport.BvBitblastSupport
import all Cpc.Proofs.RuleSupport.BvBitblastSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-!
This rule was previously unsound for two independent reasons, both now fixed
in the corresponding definitions in `Cpc.Logos`.

First, `__bv_bitblast_ult` accepted an `orEqual` argument but did not use it,
so the `bvule` branch (and the recursive magnitude comparison in the multi-bit
`bvsle` branch) implemented strict unsigned comparison and gave a wrong answer
on equal operands.  `__bv_bitblast_ult` now seeds `__bv_bitblast_ult_rec` from
`orEqual`: the seed is one comparison step applied to the least-significant bit
with prior result `orEqual`, so equal operands reduce to `orEqual` (`true` for
`bvule`/`bvsle`, `false` for `bvult`/`bvslt`).  With `orEqual = false` the seed
reduces to the original strict seed, so `bvult`/`bvslt` are unchanged.

Second, the bitwise, addition, and multiplication fold helpers expect their
right operand to be a right-nested operator spine ending in the operator's
identity.  Their fallback case returned the accumulated left operand, silently
dropping the terminal operand.  Those fallbacks now reject a non-identity
terminal.  The rule also no longer relies on the unverified fold, division, and
shift circuits: those branches use `__bv_bitblast_reify`, which represents the
result uniformly as a little-endian list of `@bit` predicates.  Specialized
circuits are retained for the operations proved directly below.

The `private def`s below exercise the affected paths.  The theorem at the end
proves the resulting step sound for every total typed SMT model.
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

private theorem bv_bitblast_requires_left_ne
    {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases y <;> cases z <;>
    simp_all [__eo_requires, native_ite, native_teq, native_not]

private theorem bv_bitblast_step_shape
    (A : Term)
    (h : __eo_prog_bv_bitblast_step A ≠ Term.Stuck) :
    ∃ lhs rhs,
      A = Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs := by
  unfold __eo_prog_bv_bitblast_step at h
  split at h <;> simp_all

public theorem cmd_step_bv_bitblast_step_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_bitblast_step args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_bitblast_step args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_bitblast_step args premises) :=
by
  intro hCmdTrans _hPremBool hResultTy
  have hProgNe :
      __eo_cmd_step_proven s CRule.bv_bitblast_step args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProgNe
      exact False.elim (hProgNe rfl)
  | cons A argsTail =>
      cases argsTail with
      | cons A2 argsRest =>
          change Term.Stuck ≠ Term.Stuck at hProgNe
          exact False.elim (hProgNe rfl)
      | nil =>
          cases premises with
          | cons n rest =>
              change Term.Stuck ≠ Term.Stuck at hProgNe
              exact False.elim (hProgNe rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation A := by
                simpa [RuleProofs.eo_has_smt_translation,
                  eoHasSmtTranslation, cmdTranslationOk,
                  cArgListTranslationOk] using hCmdTrans.1
              change
                StepRuleProperties M [] (__eo_prog_bv_bitblast_step A)
              change
                __eo_typeof (__eo_prog_bv_bitblast_step A) =
                  Term.Bool at hResultTy
              have hProgNe' :
                  __eo_prog_bv_bitblast_step A ≠ Term.Stuck := by
                simpa using hProgNe
              rcases bv_bitblast_step_shape A hProgNe' with
                ⟨lhs, rhs, hShape⟩
              subst A
              let expanded := __bv_mk_bitblast_step lhs
              let orig :=
                Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
              have hReqNe :
                  __eo_requires expanded rhs orig ≠ Term.Stuck := by
                simpa [__eo_prog_bv_bitblast_step, expanded, orig] using
                  hProgNe'
              have hExpandedEq : expanded = rhs :=
                support_eo_requires_cond_eq_of_non_stuck hReqNe
              have hExpandedNe : expanded ≠ Term.Stuck :=
                bv_bitblast_requires_left_ne hReqNe
              have hRhsNe : rhs ≠ Term.Stuck := by
                rw [← hExpandedEq]
                exact hExpandedNe
              have hProgEq :
                  __eo_prog_bv_bitblast_step
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) =
                    orig := by
                rw [__eo_prog_bv_bitblast_step.eq_1]
                change __eo_requires expanded rhs orig = orig
                simp [__eo_requires, hExpandedEq, hRhsNe, native_ite,
                  native_teq, native_not, SmtEval.native_not]
              have hOrigTy : __eo_typeof orig = Term.Bool := by
                simpa [hProgEq, orig] using hResultTy
              have hOrigBool : RuleProofs.eo_has_bool_type orig :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  orig hATrans hOrigTy
              rcases
                  RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                    lhs rhs hOrigBool with
                ⟨_hSameTy, hRepNN⟩
              have hEval :
                  __smtx_model_eval M (__eo_to_smt expanded) =
                    __smtx_model_eval M (__eo_to_smt lhs) := by
                simpa [expanded] using
                  BvBitblast.eval_bv_mk_bitblast_step
                    M hM lhs hExpandedNe hRepNN
              have hRelExpanded :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt expanded))
                    (__smtx_model_eval M (__eo_to_smt lhs)) := by
                rw [hEval]
                exact RuleProofs.smt_value_rel_refl _
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt lhs))
                    (__smtx_model_eval M (__eo_to_smt rhs)) := by
                rw [← hExpandedEq]
                exact
                  RuleProofs.smt_value_rel_symm _ _ hRelExpanded
              have hFact :
                  eo_interprets M
                    (__eo_prog_bv_bitblast_step orig) true := by
                rw [hProgEq]
                exact RuleProofs.eo_interprets_eq_of_rel
                  M lhs rhs hOrigBool hRel
              exact
                { facts_of_true := by
                    intro _premisesTrue
                    simpa [orig] using hFact
                  has_smt_translation := by
                    rw [hProgEq]
                    exact
                      RuleProofs.eo_has_smt_translation_of_has_bool_type
                        orig hOrigBool }
