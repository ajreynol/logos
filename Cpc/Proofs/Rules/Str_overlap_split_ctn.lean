import Cpc.Proofs.RuleSupport.StrOverlapSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem cmd_step_str_overlap_split_ctn_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_split_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_overlap_split_ctn args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_split_ctn args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_overlap_split_ctn args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil => exact absurd rfl hProg
  | cons a1 args =>
      cases args with
      | cons _ _ => exact absurd rfl hProg
      | nil =>
          cases premises with
          | cons _ _ => exact absurd rfl hProg
          | nil =>
              change StepRuleProperties M [] (__eo_prog_str_overlap_split_ctn a1)
              change __eo_prog_str_overlap_split_ctn a1 ≠ Term.Stuck at hProg
              unfold __eo_prog_str_overlap_split_ctn at hProg ⊢
              split at hProg
              · rename_i t c sw emp d lvt2 lvd2 lvs2 lvd3
                have h1 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ hProg
                have h2 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h1
                have h3 := RuleProofs.eo_requires_result_ne_stuck_of_ne_stuck _ _ _ h2
                have hemp : __str_is_empty emp = Term.Boolean true :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h1
                have hgt1 :
                    __eo_gt (__str_value_len c)
                        (__str_overlap_rec (__str_flatten (__str_nary_intro c))
                          (__str_flatten (__str_nary_intro d))) = Term.Boolean false :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h2
                have hgt2 :
                    __eo_gt (__str_value_len d)
                        (__str_overlap_rec (__str_flatten (__str_nary_intro d))
                          (__str_flatten (__str_nary_intro c))) = Term.Boolean false :=
                  RuleProofs.eo_requires_eq_of_ne_stuck _ _ _ h3
                rw [RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ hProg,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h1,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h2,
                  RuleProofs.eo_requires_result_eq_of_ne_stuck _ _ _ h3]
                sorry
              all_goals exact absurd rfl hProg
