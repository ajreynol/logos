module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryStringComparisonHelpers
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryStringComparisonHelpers

public section

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

theorem eo_typeof_re_range_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_re_range A B ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
      B = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | Seq =>
              cases n with
              | UOp innerA =>
                  cases innerA with
                  | Char =>
                      cases B with
                      | Apply g m =>
                          cases g with
                          | UOp opB =>
                              cases opB with
                              | Seq =>
                                  cases m with
                                  | UOp innerB =>
                                      cases innerB with
                                      | Char =>
                                          exact ⟨rfl, rfl⟩
                                      | _ =>
                                          simp [__eo_typeof_re_range] at h
                                  | _ =>
                                      simp [__eo_typeof_re_range] at h
                              | _ =>
                                  simp [__eo_typeof_re_range] at h
                          | _ =>
                              simp [__eo_typeof_re_range] at h
                      | _ =>
                          simp [__eo_typeof_re_range] at h
                  | _ =>
                      simp [__eo_typeof_re_range] at h
              | _ =>
                  simp [__eo_typeof_re_range] at h
          | _ =>
              simp [__eo_typeof_re_range] at h
      | _ =>
          simp [__eo_typeof_re_range] at h
  | _ =>
      simp [__eo_typeof_re_range] at h

theorem eo_typeof_re_range_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_re_range A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_re_range_arg_types_of_ne_stuck h with ⟨hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_re_range_non_none_of_eo_typeof_re_range_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_re_range (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.re_range (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  rcases eo_typeof_re_range_arg_types_of_ne_stuck hApp with
    ⟨hXTy, hYTy⟩
  have hXSmt :=
    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hXTrans hXTy
  have hYSmt :=
    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hYTrans hYTy
  rw [typeof_re_range_eq, hXSmt, hYSmt]
  simp [native_ite, native_Teq]

theorem eo_typeof_re_concat_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_re_concat A B ≠ Term.Stuck) :
    A = Term.UOp UserOp.RegLan ∧ B = Term.UOp UserOp.RegLan := by
  cases A <;> cases B <;> simp [__eo_typeof_re_concat] at h ⊢
  case UOp.UOp opA opB =>
    cases opA <;> cases opB <;> simp [__eo_typeof_re_concat] at h ⊢

theorem eo_typeof_re_concat_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_re_concat A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_re_concat_arg_types_of_ne_stuck h with ⟨hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_reglan_binop_non_none_of_eo_typeof_re_concat_ne_stuck
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          native_ite (native_Teq (__smtx_typeof X) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof Y) SmtType.RegLan)
              SmtType.RegLan SmtType.None)
            SmtType.None)
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_re_concat (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof (smtOp (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hXSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_re_concat_arg_types_of_ne_stuck hApp with
    ⟨hXTy, hYTy⟩
  rw [hSmtType, hXSmt, hYSmt, hXTy, hYTy]
  simp [native_ite, native_Teq]

theorem eo_typeof_str_in_re_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_in_re A B ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
      B = Term.UOp UserOp.RegLan := by
  cases A with
  | Apply f n =>
      cases f with
      | UOp opA =>
          cases opA with
          | Seq =>
              cases n with
              | UOp innerA =>
                  cases innerA with
                  | Char =>
                      cases B with
                      | UOp opB =>
                          cases opB with
                          | RegLan =>
                              exact ⟨rfl, rfl⟩
                          | _ =>
                              simp [__eo_typeof_str_in_re] at h
                      | _ =>
                          simp [__eo_typeof_str_in_re] at h
                  | _ =>
                      simp [__eo_typeof_str_in_re] at h
              | _ =>
                  simp [__eo_typeof_str_in_re] at h
          | _ =>
              simp [__eo_typeof_str_in_re] at h
      | _ =>
          simp [__eo_typeof_str_in_re] at h
  | _ =>
      simp [__eo_typeof_str_in_re] at h

theorem eo_typeof_str_in_re_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_in_re A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_str_in_re_arg_types_of_ne_stuck h with
    ⟨hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_str_in_re_non_none_of_eo_typeof_str_in_re_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_str_in_re (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.str_in_re (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  have hYSmt :=
    TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
  rcases eo_typeof_str_in_re_arg_types_of_ne_stuck hApp with
    ⟨hXTy, hYTy⟩
  have hXSmt :=
    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hXTrans hXTy
  rw [typeof_str_in_re_eq, hXSmt, hYSmt, hYTy]
  simp [native_ite, native_Teq]

end SubstitutePreservationSupport
