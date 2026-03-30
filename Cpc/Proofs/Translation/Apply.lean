import Cpc.Proofs.Translation.Quantifiers
import Cpc.Proofs.Translation.Special
import Cpc.Proofs.Translation.Inversions
import Cpc.Proofs.Translation.Heads
import Cpc.Proofs.TypePreservation

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof
attribute [local reducible] __eo_to_smt

namespace TranslationProofs

theorem eo_to_smt_typeof_matches_translation_apply
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  cases f <;> intro hNonNone
  case Var s T =>
    sorry
  case DtCons s d i =>
    sorry
  case DtSel s d i j =>
    sorry
  case UConst i T =>
    sorry
  case Apply f y =>
    sorry
  case not =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.not x) =
          SmtTerm.Apply SmtTerm.not (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.not (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
      unfold term_has_non_none_type at hApplyNN
      cases h : __smtx_typeof (__eo_to_smt x) <;>
        simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at hApplyNN
      simp
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Bool := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Bool := eo_to_smt_type_eq_bool hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) = SmtType.Bool := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
          SmtType.Bool SmtType.None) = SmtType.Bool
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_not_of_bool x hxEo).symm
  case _at_purify y =>
    sorry
  case to_real =>
    sorry
  case to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.to_int x) =
          SmtTerm.Apply SmtTerm.to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
      real_arg_of_non_none (op := SmtTerm.to_int) (t := __eo_to_smt x) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.to_int x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_to_int_of_real x hxEo).symm
  case is_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.is_int x) =
          SmtTerm.Apply SmtTerm.is_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.is_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
      real_arg_of_non_none (op := SmtTerm.is_int) (t := __eo_to_smt x) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.is_int x)) = SmtType.Bool := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
          SmtType.Bool SmtType.None) = SmtType.Bool
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_is_int_of_real x hxEo).symm
  case abs =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.abs x) =
          SmtTerm.Apply SmtTerm.abs (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.abs (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_arg_of_non_none (t := __eo_to_smt x) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.abs x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_abs_of_int x hxEo).symm
  case int_pow2 =>
    sorry
  case int_log2 =>
    sorry
  case int_ispow2 =>
    sorry
  case _at_int_div_by_zero =>
    sorry
  case _at_mod_by_zero =>
    sorry
  case _at_array_deq_diff x1 x2 =>
    sorry
  case _at_bvsize =>
    sorry
  case bvnot =>
    sorry
  case bvneg =>
    sorry
  case bvredand =>
    sorry
  case bvredor =>
    sorry
  case str_len =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_len x) =
          SmtTerm.Apply SmtTerm.str_len (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_len (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgExists : ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
      unfold term_has_non_none_type at hApplyNN
      cases h : __smtx_typeof (__eo_to_smt x) with
      | Seq T =>
          exact ⟨T, rfl⟩
      | _ =>
          simp [__smtx_typeof, __smtx_typeof_seq_op_1_ret, h] at hApplyNN
    rcases hArgExists with ⟨T, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
      rw [← hXTyped]
      exact hArg
    rcases eo_to_smt_type_eq_seq hxSmt with ⟨V, hxEo, hV⟩
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len x)) = SmtType.Int := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_seq_op_1_ret, hArg]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_len_of_seq x V hxEo).symm
  case str_rev =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_rev x) =
          SmtTerm.Apply SmtTerm.str_rev (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_rev (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases seq_arg_of_non_none (op := SmtTerm.str_rev) rfl hApplyNN with ⟨T, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
      rw [← hXTyped]
      exact hArg
    rcases eo_to_smt_type_eq_seq hxSmt with ⟨V, hxEo, hV⟩
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_rev x)) = SmtType.Seq T := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_seq_op_1, hArg]
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_rev x)) =
          SmtType.Seq (__eo_to_smt_type V) :=
      eo_to_smt_type_typeof_apply_str_rev_of_seq x V hxEo
    rw [hV] at hEo
    exact hSmt.trans hEo.symm
  case str_to_lower =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_lower x) =
          SmtTerm.Apply SmtTerm.str_to_lower (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_lower (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_lower) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_lower x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          (SmtType.Seq SmtType.Char) SmtType.None) = SmtType.Seq SmtType.Char
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_lower_of_seq_char x hxEo).symm
  case str_to_upper =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_upper x) =
          SmtTerm.Apply SmtTerm.str_to_upper (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_upper (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_upper) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_upper x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          (SmtType.Seq SmtType.Char) SmtType.None) = SmtType.Seq SmtType.Char
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_upper_of_seq_char x hxEo).symm
  case str_to_code =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_code x) =
          SmtTerm.Apply SmtTerm.str_to_code (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_code (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_code) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_code x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_code_of_seq_char x hxEo).symm
  case str_from_code =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_from_code x) =
          SmtTerm.Apply SmtTerm.str_from_code (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_from_code (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := SmtTerm.str_from_code) (R := SmtType.Seq SmtType.Char) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_from_code x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (SmtType.Seq SmtType.Char) SmtType.None) = SmtType.Seq SmtType.Char
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_code_of_int x hxEo).symm
  case str_is_digit =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_is_digit x) =
          SmtTerm.Apply SmtTerm.str_is_digit (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_is_digit (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_is_digit) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_is_digit x)) = SmtType.Bool := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          SmtType.Bool SmtType.None) = SmtType.Bool
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_is_digit_of_seq_char x hxEo).symm
  case str_to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_int x) =
          SmtTerm.Apply SmtTerm.str_to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_int) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_int x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_int_of_seq_char x hxEo).symm
  case str_from_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_from_int x) =
          SmtTerm.Apply SmtTerm.str_from_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_from_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := SmtTerm.str_from_int) (R := SmtType.Seq SmtType.Char) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_from_int x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (SmtType.Seq SmtType.Char) SmtType.None) = SmtType.Seq SmtType.Char
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_int_of_int x hxEo).symm
  case _at_strings_stoi_non_digit =>
    sorry
  case str_to_re =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_re x) =
          SmtTerm.Apply SmtTerm.str_to_re (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_re (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_re) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_re x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_re_of_seq_char x hxEo).symm
  case re_mult =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_mult x) =
          SmtTerm.Apply SmtTerm.re_mult (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_mult (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_mult) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_mult x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_mult_of_reglan x hxEo).symm
  case re_plus =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_plus x) =
          SmtTerm.Apply SmtTerm.re_plus (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_plus (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_plus) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_plus x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_plus_of_reglan x hxEo).symm
  case re_opt =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_opt x) =
          SmtTerm.Apply SmtTerm.re_opt (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_opt (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_opt) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_opt x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_opt_of_reglan x hxEo).symm
  case re_comp =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_comp x) =
          SmtTerm.Apply SmtTerm.re_comp (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_comp (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_comp) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_comp x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_comp_of_reglan x hxEo).symm
  case seq_unit =>
    sorry
  case is =>
    sorry
  case set_empty T =>
    sorry
  case set_singleton =>
    sorry
  case set_is_empty =>
    sorry
  case set_is_singleton =>
    sorry
  case _at_sets_deq_diff x1 x2 =>
    sorry
  case _at_div_by_zero =>
    sorry
  case _at_quantifiers_skolemize x1 x2 =>
    sorry
  case ubv_to_int =>
    sorry
  case sbv_to_int =>
    sorry
  all_goals
    sorry

end TranslationProofs
