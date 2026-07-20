module

public import Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Cpc.Proofs.RuleSupport.ReInclusionSupport
import all Init.Data.Repr

open Eo
open SmtEval
open Smtm
open RuleProofs

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace StrInReFromIntDigRangeProof

abbrev zeroStr : native_String := native_string_lit "0"
abbrev nineStr : native_String := native_string_lit "9"

abbrev digitRange : native_RegLan :=
  native_re_range zeroStr nineStr

abbrev rangeTerm : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.re_range) (Term.String zeroStr))
    (Term.String nineStr)

private abbrev starRangeTerm : Term :=
  Term.Apply (Term.UOp UserOp.re_mult) rangeTerm

private abbrev lhs (n : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.str_in_re)
      (Term.Apply (Term.UOp UserOp.str_from_int) n))
    starRangeTerm

private abbrev concl (n : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (lhs n)) (Term.Boolean true)

private theorem native_char_is_digit_digitChar_lt10
    (n : Nat) (hn : n < 10) :
    native_char_is_digit (Char.toNat (Nat.digitChar n)) = true := by
  by_cases h0 : n = 0
  · subst n; native_decide
  by_cases h1 : n = 1
  · subst n; native_decide
  by_cases h2 : n = 2
  · subst n; native_decide
  by_cases h3 : n = 3
  · subst n; native_decide
  by_cases h4 : n = 4
  · subst n; native_decide
  by_cases h5 : n = 5
  · subst n; native_decide
  by_cases h6 : n = 6
  · subst n; native_decide
  by_cases h7 : n = 7
  · subst n; native_decide
  by_cases h8 : n = 8
  · subst n; native_decide
  by_cases h9 : n = 9
  · subst n; native_decide
  · have : False := by omega
    exact False.elim this

private theorem native_toDigitsCore_all_digits :
    ∀ fuel n ds,
      (ds.map Char.toNat).all native_char_is_digit = true ->
        ((Nat.toDigitsCore 10 fuel n ds).map Char.toNat).all
          native_char_is_digit = true
  | 0, _n, _ds, hds => by
      simpa [Nat.toDigitsCore.eq_1] using hds
  | fuel + 1, n, ds, hds => by
      rw [Nat.toDigitsCore.eq_2]
      by_cases hDiv : n / 10 = 0
      · rw [if_pos hDiv]
        have hDigit :=
          native_char_is_digit_digitChar_lt10 (n % 10) (Nat.mod_lt n (by decide))
        simpa [hDigit, hds]
      · rw [if_neg hDiv]
        have hDigit :=
          native_char_is_digit_digitChar_lt10 (n % 10) (Nat.mod_lt n (by decide))
        exact native_toDigitsCore_all_digits fuel (n / 10)
          ((Nat.digitChar (n % 10)) :: ds) (by
            simpa [hDigit, hds])

private theorem native_string_lit_nat_toString_all_digits
    (n : Nat) :
    (native_string_lit (toString n)).all native_char_is_digit = true := by
  unfold native_string_lit
  rw [show (toString n).toList = Nat.toDigits 10 n by
    rw [show (toString n) = n.repr by rfl]
    unfold Nat.repr
    rw [String.toList_ofList]]
  rw [Nat.toDigits.eq_1]
  exact native_toDigitsCore_all_digits (n + 1) n [] (by simp)

theorem native_str_from_int_all_digits
    (i : native_Int) :
    (native_str_from_int i).all native_char_is_digit = true := by
  cases i with
  | ofNat n =>
      unfold native_str_from_int
      have hNot : ¬ ((Int.ofNat n) < 0) := by
        exact Int.not_lt_of_ge (Int.natCast_nonneg n)
      rw [if_neg hNot]
      exact native_string_lit_nat_toString_all_digits n
  | negSucc n =>
      unfold native_str_from_int
      have hNeg : (Int.negSucc n) < 0 := by
        exact Int.negSucc_lt_zero n
      rw [if_pos hNeg]
      simp [native_string_lit]

theorem native_char_valid_of_digit
    (c : native_Char)
    (hDigit : native_char_is_digit c = true) :
    native_char_valid c = true := by
  have hBounds : 48 ≤ c ∧ c ≤ 57 := by
    unfold native_char_is_digit at hDigit
    simpa [Bool.and_eq_true] using hDigit
  unfold native_char_valid
  have h57 : 57 < 196608 := by native_decide
  exact decide_eq_true (Nat.lt_of_le_of_lt hBounds.2 h57)

theorem native_digit_bounds
    (c : native_Char)
    (hDigit : native_char_is_digit c = true) :
    48 ≤ c ∧ c ≤ 57 := by
  unfold native_char_is_digit at hDigit
  simpa [Bool.and_eq_true] using hDigit

theorem nativeListInRe_digit_range_singleton
    (c : native_Char)
    (hDigit : native_char_is_digit c = true) :
    _root_.nativeListInRe [c] digitRange = true := by
  have hValid : native_char_valid c = true :=
    native_char_valid_of_digit c hDigit
  have hBounds := native_digit_bounds c hDigit
  have hLoValid : native_char_valid 48 = true := by native_decide
  have hHiValid : native_char_valid 57 = true := by native_decide
  simp [digitRange, zeroStr, nineStr, native_re_range, native_string_lit,
    _root_.nativeListInRe, native_re_deriv, native_re_nullable, hValid, hLoValid,
    hHiValid, hBounds.1, hBounds.2]

theorem native_str_in_re_digit_range_singleton
    (c : native_Char)
    (hDigit : native_char_is_digit c = true) :
    native_str_in_re [c] digitRange = true := by
  have hValidChar : native_char_valid c = true :=
    native_char_valid_of_digit c hDigit
  have hValidString : native_string_valid [c] = true := by
    simpa [native_string_valid, hValidChar]
  have hList := nativeListInRe_digit_range_singleton c hDigit
  simpa [native_str_in_re, hValidString, _root_.nativeListInRe] using hList

theorem nativeListInRe_digit_star_of_all_digits
    (xs : native_String)
    (hDigits : xs.all native_char_is_digit = true) :
    _root_.nativeListInRe xs (native_re_mult digitRange) = true := by
  induction xs with
  | nil =>
      simpa [native_re_mult] using
        RuleProofs.nativeListInRe_nil_mk_star digitRange
  | cons c cs ih =>
      have hParts :
          native_char_is_digit c = true ∧
            cs.all native_char_is_digit = true := by
        simpa [Bool.and_eq_true] using hDigits
      have hCValid : native_string_valid [c] = true := by
        have hValidChar := native_char_valid_of_digit c hParts.1
        simpa [native_string_valid, hValidChar]
      have hCBase : native_str_in_re [c] digitRange = true :=
        native_str_in_re_digit_range_singleton c hParts.1
      have hCStarStr :
          native_str_in_re [c] (native_re_mult digitRange) = true :=
        RuleProofs.native_includes_star_self digitRange [c] hCValid hCBase
      have hCStar :
          _root_.nativeListInRe [c] (native_re_mk_star digitRange) = true := by
        simpa [native_str_in_re, hCValid, native_re_mult, _root_.nativeListInRe]
          using hCStarStr
      have hCsStar :
          _root_.nativeListInRe cs (native_re_mk_star digitRange) = true := by
        simpa [native_re_mult] using ih hParts.2
      have hAppend :=
        RuleProofs.nativeListInRe_mk_star_append [c] cs digitRange
          hCStar hCsStar
      simpa [native_re_mult] using hAppend

theorem eo_typeof_str_in_re_reglan_eq_seq_char_of_ne_stuck (T : Term)
    (h : __eo_typeof_str_in_re T (Term.UOp UserOp.RegLan) ≠ Term.Stuck) :
    T = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  cases T with
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> simp [__eo_typeof_str_in_re] at h ⊢
          case Seq =>
            cases x with
            | UOp opx =>
                cases opx <;> simp [__eo_typeof_str_in_re] at h ⊢
            | _ => simp [__eo_typeof_str_in_re] at h
      | _ => simp [__eo_typeof_str_in_re] at h
  | _ => simp [__eo_typeof_str_in_re] at h

theorem eo_typeof_str_from_code_eq_seq_char_arg_int
    (T : Term)
    (h : __eo_typeof_str_from_code T =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    T = Term.UOp UserOp.Int := by
  have hNe : __eo_typeof_str_from_code T ≠ Term.Stuck := by
    rw [h]
    native_decide
  cases T <;> simp [__eo_typeof_str_from_code] at hNe ⊢
  case UOp op =>
    cases op <;> simp [__eo_typeof_str_from_code] at hNe ⊢

theorem smtx_typeof_of_eo_int
    (n : Term)
    (hTrans : RuleProofs.eo_has_smt_translation n)
    (hTy : __eo_typeof n = Term.UOp UserOp.Int) :
    __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  have hTyRaw :
      __smtx_typeof (__eo_to_smt n) = __eo_to_smt_type (__eo_typeof n) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation n hTrans
  rw [hTy] at hTyRaw
  simpa using hTyRaw

private theorem smtx_typeof_zero_string :
    __smtx_typeof (SmtTerm.String zeroStr) = SmtType.Seq SmtType.Char := by
  native_decide

private theorem smtx_typeof_nine_string :
    __smtx_typeof (SmtTerm.String nineStr) = SmtType.Seq SmtType.Char := by
  native_decide

theorem smtx_typeof_digit_range :
    __smtx_typeof
        (SmtTerm.re_range (SmtTerm.String zeroStr) (SmtTerm.String nineStr)) =
      SmtType.RegLan := by
  rw [typeof_re_range_eq]
  simp [smtx_typeof_zero_string, smtx_typeof_nine_string, native_ite,
    native_Teq]

theorem smtx_eval_str_from_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_from_int x) =
      __smtx_model_eval_str_from_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_re_mult_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.re_mult x) =
      __smtx_model_eval_re_mult (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_str_in_re_term_eq
    (M : SmtModel) (x r : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_in_re x r) =
      __smtx_model_eval_str_in_re
        (__smtx_model_eval M x) (__smtx_model_eval M r) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem smtx_eval_digit_range
    (M : SmtModel) :
    __smtx_model_eval M
        (SmtTerm.re_range (SmtTerm.String zeroStr) (SmtTerm.String nineStr)) =
      SmtValue.RegLan digitRange := by
  simp [__smtx_model_eval, __smtx_model_eval_re_range,
    RuleProofs.native_unpack_string_pack_string, digitRange, zeroStr, nineStr]

end StrInReFromIntDigRangeProof
