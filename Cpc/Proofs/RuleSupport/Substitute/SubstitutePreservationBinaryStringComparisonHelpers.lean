module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryStringConversionHelpers
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryStringConversionHelpers

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

theorem eo_typeof_str_lt_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_lt A B ≠ Term.Stuck) :
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
                                          simp [__eo_typeof_str_lt] at h
                                  | _ =>
                                      simp [__eo_typeof_str_lt] at h
                              | _ =>
                                  simp [__eo_typeof_str_lt] at h
                          | _ =>
                              simp [__eo_typeof_str_lt] at h
                      | _ =>
                          simp [__eo_typeof_str_lt] at h
                  | _ =>
                      simp [__eo_typeof_str_lt] at h
              | _ =>
                  simp [__eo_typeof_str_lt] at h
          | _ =>
              simp [__eo_typeof_str_lt] at h
      | _ =>
          simp [__eo_typeof_str_lt] at h
  | _ =>
      simp [__eo_typeof_str_lt] at h

theorem eo_typeof_str_lt_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof_str_lt A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_str_lt_arg_types_of_ne_stuck h with ⟨hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_seq_char_bool_binop_non_none_of_eo_typeof_str_lt_ne_stuck
    (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          native_ite
            (native_Teq (__smtx_typeof X) (SmtType.Seq SmtType.Char))
            (native_ite
              (native_Teq (__smtx_typeof Y) (SmtType.Seq SmtType.Char))
              SmtType.Bool SmtType.None)
            SmtType.None)
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_str_lt (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof (smtOp (__eo_to_smt X) (__eo_to_smt Y)) ≠
      SmtType.None := by
  rcases eo_typeof_str_lt_arg_types_of_ne_stuck hApp with
    ⟨hXTy, hYTy⟩
  have hXSmt :=
    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hXTrans hXTy
  have hYSmt :=
    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hYTrans hYTy
  rw [hSmtType, hXSmt, hYSmt]
  simp [native_ite, native_Teq]

end SubstitutePreservationSupport
