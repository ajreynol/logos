import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinarySetHelpers

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open TypedListSubstitutionSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

namespace SubstitutePreservationSupport

theorem eo_typeof_sets_deq_diff_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_sets_deq_diff A B ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Set) T ∧
      B = Term.Apply (Term.UOp UserOp.Set) T := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | Set =>
              cases B with
              | Apply g m =>
                  cases g with
                  | UOp opB =>
                      cases opB with
                      | Set =>
                          have hReq :
                              __eo_requires (__eo_eq n m)
                                  (Term.Boolean true) n ≠
                                Term.Stuck := by
                            simpa [__eo_typeof__at_sets_deq_diff] using h
                          have hm : m = n :=
                            support_eq_of_eo_eq_true n m
                              (support_eo_requires_cond_eq_of_non_stuck hReq)
                          exact ⟨n, rfl, by rw [hm]⟩
                      | _ =>
                          simp [__eo_typeof__at_sets_deq_diff] at h
                  | _ =>
                      simp [__eo_typeof__at_sets_deq_diff] at h
              | _ =>
                  simp [__eo_typeof__at_sets_deq_diff] at h
          | _ =>
              simp [__eo_typeof__at_sets_deq_diff] at h
      | _ =>
          simp [__eo_typeof__at_sets_deq_diff] at h
  | _ =>
      simp [__eo_typeof__at_sets_deq_diff] at h

theorem eo_typeof_sets_deq_diff_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_sets_deq_diff A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_sets_deq_diff_arg_types_of_ne_stuck h with
    ⟨T, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_sets_deq_diff_non_none_of_eo_typeof_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof__at_sets_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt_sets_deq_diff (__eo_to_smt X)
          (__smtx_typeof (__eo_to_smt X)) (__eo_to_smt Y)
          (__smtx_typeof (__eo_to_smt Y))) ≠ SmtType.None := by
  rcases eo_typeof_sets_deq_diff_arg_types_of_ne_stuck hApp with
    ⟨T, hXTy, hYTy⟩
  have hXSmt :=
    smt_typeof_eo_to_smt_set_of_typeof_set hXTrans hXTy
  have hYSmt :=
    smt_typeof_eo_to_smt_set_of_typeof_set hYTrans hYTy
  have hElemNN :
      __eo_to_smt_type T ≠ SmtType.None :=
    smt_typeof_eo_to_smt_set_elem_ne_none_of_typeof_set hXTrans hXTy
  rw [hXSmt, hYSmt]
  change
    __smtx_typeof (SmtTerm.map_diff (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None
  rw [typeof_map_diff_eq, hXSmt, hYSmt]
  simp [__smtx_typeof_map_diff, native_ite, native_Teq, hElemNN]

theorem eo_typeof_strings_deq_diff_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_strings_deq_diff A B ≠ Term.Stuck) :
    ∃ T, A = Term.Apply (Term.UOp UserOp.Seq) T ∧
      B = Term.Apply (Term.UOp UserOp.Seq) T := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | Seq =>
              cases B with
              | Apply g m =>
                  cases g with
                  | UOp opB =>
                      cases opB with
                      | Seq =>
                          have hReq :
                              __eo_requires (__eo_eq n m)
                                  (Term.Boolean true)
                                  (Term.UOp UserOp.Int) ≠
                                Term.Stuck := by
                            simpa [__eo_typeof__at_strings_deq_diff] using h
                          have hm : m = n :=
                            support_eq_of_eo_eq_true n m
                              (support_eo_requires_cond_eq_of_non_stuck hReq)
                          exact ⟨n, rfl, by rw [hm]⟩
                      | _ =>
                          simp [__eo_typeof__at_strings_deq_diff] at h
                  | _ =>
                      simp [__eo_typeof__at_strings_deq_diff] at h
              | _ =>
                  simp [__eo_typeof__at_strings_deq_diff] at h
          | _ =>
              simp [__eo_typeof__at_strings_deq_diff] at h
      | _ =>
          simp [__eo_typeof__at_strings_deq_diff] at h
  | _ =>
      simp [__eo_typeof__at_strings_deq_diff] at h

theorem eo_typeof_strings_deq_diff_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_strings_deq_diff A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_strings_deq_diff_arg_types_of_ne_stuck h with
    ⟨T, hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_strings_deq_diff_non_none_of_eo_typeof_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof__at_strings_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.seq_diff (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  rcases eo_typeof_strings_deq_diff_arg_types_of_ne_stuck hApp with
    ⟨T, hXTy, hYTy⟩
  have hXSmt :
      __smtx_typeof (__eo_to_smt X) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
    have hMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
    rw [hXTy] at hMatch
    exact hMatch
  have hYSmt :
      __smtx_typeof (__eo_to_smt Y) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
    have hMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
    rw [hYTy] at hMatch
    exact hMatch
  have hSeqNN :
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) ≠
        SmtType.None := by
    intro hNone
    have hXNN :
        __smtx_typeof (__eo_to_smt X) ≠ SmtType.None := by
      simpa [RuleProofs.eo_has_smt_translation] using hXTrans
    exact hXNN (by simpa [hXSmt] using hNone)
  rw [typeof_seq_diff_eq, hXSmt, hYSmt]
  exact
    smt_seq_binop_ret_non_none_of_eo_seq_type_non_none
      hSeqNN (by simp)

end SubstitutePreservationSupport
