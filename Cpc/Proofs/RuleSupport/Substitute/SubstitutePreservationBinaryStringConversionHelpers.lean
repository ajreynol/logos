import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryStringDiffHelpers

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

theorem eo_typeof_strings_stoi_result_arg_types_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_strings_stoi_result A B ≠ Term.Stuck) :
    A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) ∧
      B = Term.UOp UserOp.Int := by
  cases A <;> cases B <;>
    simp [__eo_typeof__at_strings_stoi_result] at h ⊢
  case Apply.UOp f arg opB =>
    cases f <;> cases opB <;>
      simp [__eo_typeof__at_strings_stoi_result] at h ⊢
    case UOp.Int opInner =>
      cases opInner <;>
        simp [__eo_typeof__at_strings_stoi_result] at h ⊢
      case Seq =>
        cases arg <;>
          simp [__eo_typeof__at_strings_stoi_result] at h ⊢
        case UOp inner =>
          cases inner <;>
            simp [__eo_typeof__at_strings_stoi_result] at h ⊢

theorem eo_typeof_strings_stoi_result_args_not_stuck_of_ne_stuck
    {A B : Term}
    (h : __eo_typeof__at_strings_stoi_result A B ≠ Term.Stuck) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  rcases eo_typeof_strings_stoi_result_arg_types_of_ne_stuck h with
    ⟨hA, hB⟩
  constructor
  · intro hStuck
    rw [hA] at hStuck
    cases hStuck
  · intro hStuck
    rw [hB] at hStuck
    cases hStuck

theorem smt_strings_stoi_result_non_none_of_eo_typeof_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof__at_strings_stoi_result (__eo_typeof X) (__eo_typeof Y) ≠
        Term.Stuck) :
    __smtx_typeof
        (SmtTerm.str_to_int
          (SmtTerm.str_substr (__eo_to_smt X) (SmtTerm.Numeral 0)
            (__eo_to_smt Y))) ≠
      SmtType.None := by
  rcases eo_typeof_strings_stoi_result_arg_types_of_ne_stuck hApp with
    ⟨hXTy, hYTy⟩
  have hXSmt :=
    smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char hXTrans hXTy
  have hYSmt : __smtx_typeof (__eo_to_smt Y) = SmtType.Int := by
    have hMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation Y hYTrans
    rw [hYTy] at hMatch
    exact hMatch
  have hSubTy :
      __smtx_typeof
          (SmtTerm.str_substr (__eo_to_smt X) (SmtTerm.Numeral 0)
            (__eo_to_smt Y)) =
        SmtType.Seq SmtType.Char := by
    have hZero :
        __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
      rw [__smtx_typeof.eq_2]
    rw [typeof_str_substr_eq, hXSmt, hYSmt, hZero]
    simp [__smtx_typeof_str_substr]
  rw [typeof_str_to_int_eq, hSubTy]
  simp [native_ite, native_Teq]

theorem smt_strings_itos_result_non_none_of_eo_typeof_ne_stuck
    (X Y : Term)
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hYTrans : RuleProofs.eo_has_smt_translation Y)
    (hApp :
      __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠ Term.Stuck) :
    __smtx_typeof
        (SmtTerm.ite
          (SmtTerm.eq (__eo_to_smt Y) (SmtTerm.Numeral 0))
          (SmtTerm.Numeral 0)
          (SmtTerm.str_to_int
            (SmtTerm.str_substr
              (SmtTerm.str_from_int (__eo_to_smt X))
              (SmtTerm.Numeral 0) (__eo_to_smt Y)))) ≠
      SmtType.None := by
  have hArgTy :=
    eo_typeof_div_arg_types_of_ne_stuck hApp
  have hXSmt :=
    smt_typeof_eo_to_smt_int_of_typeof_int hXTrans hArgTy.1
  have hYSmt :=
    smt_typeof_eo_to_smt_int_of_typeof_int hYTrans hArgTy.2
  have hZero :
      __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
    rw [__smtx_typeof.eq_2]
  have hFromInt :
      __smtx_typeof
          (SmtTerm.str_from_int (__eo_to_smt X)) =
        SmtType.Seq SmtType.Char := by
    rw [typeof_str_from_int_eq, hXSmt]
    simp [native_ite, native_Teq]
  have hSubstr :
      __smtx_typeof
          (SmtTerm.str_substr
            (SmtTerm.str_from_int (__eo_to_smt X))
            (SmtTerm.Numeral 0) (__eo_to_smt Y)) =
        SmtType.Seq SmtType.Char := by
    rw [typeof_str_substr_eq, hFromInt, hZero, hYSmt]
    simp [__smtx_typeof_str_substr, native_ite, native_Teq]
  have hParsed :
      __smtx_typeof
          (SmtTerm.str_to_int
            (SmtTerm.str_substr
              (SmtTerm.str_from_int (__eo_to_smt X))
              (SmtTerm.Numeral 0) (__eo_to_smt Y))) =
        SmtType.Int := by
    rw [typeof_str_to_int_eq, hSubstr]
    simp [native_ite, native_Teq]
  have hCond :
      __smtx_typeof
          (SmtTerm.eq (__eo_to_smt Y) (SmtTerm.Numeral 0)) =
        SmtType.Bool := by
    rw [typeof_eq_eq, hYSmt, hZero]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite, native_Teq]
  rw [typeof_ite_eq, hCond, hZero, hParsed]
  simp [__smtx_typeof_ite, native_ite, native_Teq]

theorem smt_strings_num_occur_typeof_congr
    {X₁ X₂ Y₁ Y₂ : SmtTerm}
    (hX : __smtx_typeof X₁ = __smtx_typeof X₂)
    (hY : __smtx_typeof Y₁ = __smtx_typeof Y₂) :
    __smtx_typeof
        (SmtTerm.div
          (SmtTerm.neg (SmtTerm.str_len X₁)
            (SmtTerm.str_len
              (SmtTerm.str_replace_all X₁ Y₁
                (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
          (SmtTerm.str_len Y₁)) =
      __smtx_typeof
        (SmtTerm.div
          (SmtTerm.neg (SmtTerm.str_len X₂)
            (SmtTerm.str_len
              (SmtTerm.str_replace_all X₂ Y₂
                (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
          (SmtTerm.str_len Y₂)) := by
  simp [typeof_div_eq, typeof_neg_eq, typeof_str_len_eq,
    typeof_str_replace_all_eq, hX, hY]

end SubstitutePreservationSupport
