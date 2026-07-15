import Cpc.Proofs.RuleSupport.BvXorSimplifySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem cmd_step_bv_xor_simplify_2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.bv_xor_simplify_2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.bv_xor_simplify_2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.bv_xor_simplify_2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.bv_xor_simplify_2 args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
                  | nil =>
                      cases premises with
                      | cons _ _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | nil =>
                          have hArgs :
                              ∃ width : native_Nat,
                                __smtx_typeof (__eo_to_smt a1) =
                                    SmtType.BitVec width ∧
                                  __smtx_typeof (__eo_to_smt a2) =
                                    SmtType.BitVec width ∧
                                  __smtx_typeof (__eo_to_smt a3) =
                                    SmtType.BitVec width ∧
                                  __smtx_typeof (__eo_to_smt a4) =
                                    SmtType.BitVec width := by
                            simpa [cmdTranslationOk,
                              bvXorSimplifyArgsTranslationOk] using hCmdTrans
                          rcases hArgs with
                            ⟨width, hA1Ty, hA2Ty, hA3Ty, hA4Ty⟩
                          change __eo_typeof
                              (__eo_prog_bv_xor_simplify_2 a1 a2 a3 a4) =
                            Term.Bool at hResultTy
                          have hProgEq :=
                            BvXorSimplifySupport.program2_eq_term
                              a1 a2 a3 a4 width
                              hA1Ty hA2Ty hA3Ty hA4Ty hResultTy
                          change StepRuleProperties M []
                            (__eo_prog_bv_xor_simplify_2 a1 a2 a3 a4)
                          rw [hProgEq]
                          refine ⟨?_, ?_⟩
                          · intro _hTrue
                            exact BvXorSimplifySupport.facts_term2 M hM
                              a1 a2 a3 a4 width
                              hA1Ty hA2Ty hA3Ty hA4Ty hResultTy
                          · exact
                              RuleProofs.eo_has_smt_translation_of_has_bool_type _
                                (BvXorSimplifySupport.typed_term2
                                  a1 a2 a3 a4 width
                                  hA1Ty hA2Ty hA3Ty hA4Ty hResultTy)
