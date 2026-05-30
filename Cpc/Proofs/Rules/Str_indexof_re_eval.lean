import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.RegexSupport
import Cpc.Proofs.Rules.Str_in_re_eval

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  simp [__eo_requires, native_ite, native_teq] at h
  exact h.1

private theorem eo_requires_result_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq] at h'
  rcases h' with ⟨hxy, hxOk, _hz⟩
  subst y
  simp [__eo_requires, native_ite, native_teq, hxOk]

private theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h
  have h' := h
  simp [__eo_requires, native_ite, native_teq] at h'
  rcases h' with ⟨_hxy, hxOk, _hz⟩
  intro hx
  subst x
  simp [hx, native_not] at hxOk

private theorem eo_ite_cond_eq_true_or_false_of_ne_stuck (c t e : Term) :
    __eo_ite c t e ≠ Term.Stuck ->
    c = Term.Boolean true ∨ c = Term.Boolean false := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢

private theorem native_unpack_seq_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | x :: xs => by
      simp [native_pack_seq, native_unpack_seq, native_unpack_seq_pack_seq T xs]

private theorem map_native_ssm_char_of_value_char :
    ∀ s : native_String,
      List.map (native_ssm_char_of_value ∘ SmtValue.Char) s = s
  | [] => rfl
  | c :: cs => by
      simpa [Function.comp_def, native_ssm_char_of_value] using
        map_native_ssm_char_of_value_char cs

private theorem native_unpack_string_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp [native_unpack_string, native_pack_string, native_unpack_seq_pack_seq,
    map_native_ssm_char_of_value_char]

private theorem native_string_valid_of_smtx_typeof_eo_string
    (s : native_String)
    (hTy : __smtx_typeof (__eo_to_smt (Term.String s)) =
      SmtType.Seq SmtType.Char) :
    native_string_valid s = true := by
  change __smtx_typeof (SmtTerm.String s) = SmtType.Seq SmtType.Char at hTy
  unfold __smtx_typeof at hTy
  cases hValid : native_string_valid s
  · simp [native_ite, hValid] at hTy
  · rfl

private def str_indexof_re_eval_match_regex (r : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
    (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
      (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))

private def str_indexof_re_eval_match_test (tail : Term) (r : Term) : Term :=
  __str_eval_str_in_re_rec (__str_flatten (__str_nary_intro tail))
    (str_indexof_re_eval_match_regex r)

private def str_indexof_re_eval_first_match_term (tail : Term) (r : Term) : Term :=
  __str_first_match_rec (__str_flatten (__str_nary_intro tail)) r
    (str_indexof_re_eval_match_regex r) (Term.Numeral 0)

private def str_indexof_re_eval_idx_term (tail : Term) (r : Term) : Term :=
  let matchTerm :=
    __eo_requires (__eo_is_str tail) (Term.Boolean true)
      (str_indexof_re_eval_first_match_term tail r)
  __pair_first matchTerm

private def str_indexof_re_eval_tail_search_side (tail : Term) (r : Term)
    (ni : native_Int) : Term :=
  let idxTerm := str_indexof_re_eval_idx_term tail r
  __eo_ite (__eo_eq idxTerm (Term.Numeral (-1 : native_Int)))
    (Term.Numeral (-1 : native_Int))
    (__eo_add (Term.Numeral ni) idxTerm)

private def str_indexof_re_eval_search_side (str : native_String) (r : Term)
    (ni : native_Int) : Term :=
  let lenTerm := __eo_len (Term.String str)
  let tail := __eo_extract (Term.String str) (Term.Numeral ni) lenTerm
  str_indexof_re_eval_tail_search_side tail r ni

private def str_indexof_re_eval_side (str : native_String) (r : Term)
    (ni : native_Int) : Term :=
  let lenTerm := __eo_len (Term.String str)
  __eo_ite (__eo_or (__eo_gt (Term.Numeral ni) lenTerm)
      (__eo_is_neg (Term.Numeral ni)))
    (Term.Numeral (-1 : native_Int))
    (str_indexof_re_eval_search_side str r ni)

private theorem eq_operands_same_smt_type_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTrans
  have hEqNN : term_has_non_none_type (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) ≠
      SmtType.None
    exact hTrans
  have hEqTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) = SmtType.Bool :=
    Smtm.eq_term_typeof_of_non_none hEqNN
  rw [Smtm.typeof_eq_eq] at hEqTy
  exact RuleProofs.smtx_typeof_eq_bool_iff
    (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y)) |>.mp hEqTy

private theorem eq_operands_have_smt_translation_of_eq_has_smt_translation
    (x y : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
    RuleProofs.eo_has_smt_translation x ∧
      RuleProofs.eo_has_smt_translation y := by
  intro hTrans
  rcases eq_operands_same_smt_type_of_eq_has_smt_translation x y hTrans with
    ⟨hTy, hNonNone⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation] using hNonNone
  · simpa [RuleProofs.eo_has_smt_translation, hTy] using hNonNone

private theorem str_indexof_re_args_smt_types_of_has_translation
    (s r n : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) r) n) ->
    __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt n) = SmtType.Int := by
  intro hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.str_indexof_re (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt n)) := by
    unfold term_has_non_none_type
    change __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) s) r) n)) ≠
      SmtType.None
    exact hTrans
  exact str_indexof_re_args_of_non_none hNN

private theorem native_re_find_idx_aux_offset
    (r : native_RegLan) :
    ∀ (xs : native_String) (start : Nat),
      native_re_find_idx_aux r xs start =
        match native_re_find_idx_aux r xs 0 with
        | some (idx, len) => some (start + idx, len)
        | none => none
  | xs, start => by
      induction xs generalizing start with
      | nil =>
          rw [native_re_find_idx_aux.eq_def, native_re_find_idx_aux.eq_def]
          cases native_re_prefix_match_len? r [] <;> simp
      | cons c cs ih =>
          rw [native_re_find_idx_aux.eq_def, native_re_find_idx_aux.eq_def]
          cases native_re_prefix_match_len? r (c :: cs) with
          | none =>
              simp
              rw [ih (start + 1), ih 1]
              cases hTail : native_re_find_idx_aux r cs 0 <;> simp
              case some p =>
                cases p
                omega
          | some n =>
              simp

private theorem native_string_valid_drop
    (s : native_String) (n : Nat)
    (h : native_string_valid s = true) :
    native_string_valid (s.drop n) = true := by
  simp [native_string_valid] at h ⊢
  intro c hc
  exact h c (List.mem_of_mem_drop hc)

private theorem native_re_prefix_match_len_go_isSome_eq_str_in_re_concat_all
    (r : native_RegLan) :
    ∀ (xs : native_String) (n : Nat), native_string_valid xs = true ->
      (match native_re_prefix_match_len?.go r xs n with
      | some _ => true
      | none => false) =
        native_str_in_re xs (native_re_concat r native_re_all)
  | [], n, hValid => by
      rw [native_re_prefix_match_len?.go.eq_1]
      cases hNull : native_re_nullable r <;>
        simp [hNull, native_str_in_re, hValid, native_re_concat,
          native_re_nullable_mk_concat, native_re_all, native_re_nullable]
  | c :: cs, n, hValid => by
      have hParts : native_char_valid c = true ∧ native_string_valid cs = true := by
        simpa [native_string_valid] using hValid
      rcases hParts with ⟨hc, hcs⟩
      rw [native_re_prefix_match_len?.go.eq_2]
      by_cases hNullTrue : native_re_nullable r = true
      · simp [hNullTrue]
        have hEmpty : native_str_in_re ([] : native_String) r = true := by
          change native_re_nullable r = true
          exact hNullTrue
        have hAll : native_str_in_re (c :: cs) native_re_all = true :=
          native_str_in_re_re_all (c :: cs) hValid
        have hIntro :=
          native_str_in_re_re_concat_intro ([] : native_String) (c :: cs) r
            native_re_all hEmpty hAll
        simpa using hIntro
      · have hNullFalse : native_re_nullable r = false := by
          cases h : native_re_nullable r <;> simp [h] at hNullTrue ⊢
        simp [hNullFalse, hc]
        rw [native_re_prefix_match_len_go_isSome_eq_str_in_re_concat_all
          (native_re_deriv c r) cs (n + 1) hcs]
        simp only [native_str_in_re, hValid, hcs, native_re_concat]
        change
          nativeListInRe cs (native_re_mk_concat (native_re_deriv c r) native_re_all) =
            nativeListInRe cs (native_re_deriv c (native_re_mk_concat r native_re_all))
        rw [nativeListInRe_deriv_mk_concat cs c r native_re_all]
        simp [hNullFalse, nativeListInRe_mk_union, nativeListInRe_empty]

private theorem native_re_prefix_match_len_isSome_eq_str_in_re_concat_all
    (r : native_RegLan) (xs : native_String)
    (hValid : native_string_valid xs = true) :
    (match native_re_prefix_match_len? r xs with
    | some _ => true
    | none => false) =
      native_str_in_re xs (native_re_concat r native_re_all) := by
  rw [native_re_prefix_match_len?.eq_1]
  exact native_re_prefix_match_len_go_isSome_eq_str_in_re_concat_all r xs 0 hValid

private theorem smtx_typeof_eo_string_of_native_valid
    (s : native_String)
    (hValid : native_string_valid s = true) :
    __smtx_typeof (__eo_to_smt (Term.String s)) =
      SmtType.Seq SmtType.Char := by
  change __smtx_typeof (SmtTerm.String s) = SmtType.Seq SmtType.Char
  unfold __smtx_typeof
  simp [hValid, native_ite]

private theorem str_indexof_re_eval_match_regex_typeof
    (r : Term)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (str_indexof_re_eval_match_regex r)) =
      SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_concat (__eo_to_smt r)
        (SmtTerm.re_concat SmtTerm.re_all
          (SmtTerm.str_to_re (SmtTerm.String [])))) = SmtType.RegLan
  rw [typeof_re_concat_eq, typeof_re_concat_eq, typeof_str_to_re_eq]
  rw [__smtx_typeof.eq_105, __smtx_typeof.eq_4]
  simp [hRTy, native_ite, native_Teq]
  rfl

private theorem str_indexof_re_eval_match_regex_model_eval
    (M : SmtModel) (r : Term) (rv : native_RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv) :
    __smtx_model_eval M (__eo_to_smt (str_indexof_re_eval_match_regex r)) =
      SmtValue.RegLan (native_re_concat rv native_re_all) := by
  change __smtx_model_eval M
      (SmtTerm.re_concat (__eo_to_smt r)
        (SmtTerm.re_concat SmtTerm.re_all
          (SmtTerm.str_to_re (SmtTerm.String [])))) =
    SmtValue.RegLan (native_re_concat rv native_re_all)
  simp [str_indexof_re_eval_match_regex, __smtx_model_eval,
    __smtx_model_eval_re_concat, __smtx_model_eval_str_to_re, hREval,
    native_unpack_string_pack_string, native_re_concat, native_str_to_re,
    native_re_of_list, native_re_mk_concat]
  change native_re_concat rv (native_re_concat native_re_all SmtRegLan.epsilon) =
    native_re_concat rv native_re_all
  rw [show native_re_concat native_re_all SmtRegLan.epsilon = native_re_all by rfl]

private theorem str_indexof_re_eval_match_test_eq_of_bool
    (M : SmtModel) (hM : model_total_typed M)
    (tail : native_String) (r : Term) (rv : native_RegLan)
    (hTailValid : native_string_valid tail = true)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hBool :
      str_indexof_re_eval_match_test (Term.String tail) r = Term.Boolean true ∨
        str_indexof_re_eval_match_test (Term.String tail) r = Term.Boolean false) :
    str_indexof_re_eval_match_test (Term.String tail) r =
      Term.Boolean
        (match native_re_prefix_match_len? rv tail with
        | some _ => true
        | none => false) := by
  let test := str_indexof_re_eval_match_test (Term.String tail) r
  have hTailTy : __smtx_typeof (__eo_to_smt (Term.String tail)) =
      SmtType.Seq SmtType.Char :=
    smtx_typeof_eo_string_of_native_valid tail hTailValid
  have hMatchTy :
      __smtx_typeof (__eo_to_smt (str_indexof_re_eval_match_regex r)) =
        SmtType.RegLan :=
    str_indexof_re_eval_match_regex_typeof r hRTy
  have hMatchEval :
      __smtx_model_eval M (__eo_to_smt (str_indexof_re_eval_match_regex r)) =
        SmtValue.RegLan (native_re_concat rv native_re_all) :=
    str_indexof_re_eval_match_regex_model_eval M r rv hREval
  have hTestEval :
      __smtx_model_eval M (__eo_to_smt test) =
        SmtValue.Boolean
          (native_str_in_re tail (native_re_concat rv native_re_all)) := by
    exact smtx_model_eval_str_in_re_eval_side M hM tail
      (str_indexof_re_eval_match_regex r) test
      (native_re_concat rv native_re_all) hTailTy hMatchTy hMatchEval
      (by rfl) (by
        cases hBool with
        | inl h =>
            have ht : test = Term.Boolean true := by
              simpa [test] using h
            rw [ht]
            simp
        | inr h =>
            have ht : test = Term.Boolean false := by
              simpa [test] using h
            rw [ht]
            simp)
  have hPrefix :=
    native_re_prefix_match_len_isSome_eq_str_in_re_concat_all rv tail hTailValid
  cases hBool with
  | inl hTrue =>
      have ht : test = Term.Boolean true := by
        simpa [test] using hTrue
      rw [ht] at hTestEval
      change __smtx_model_eval M (SmtTerm.Boolean true) =
          SmtValue.Boolean (native_str_in_re tail (native_re_concat rv native_re_all))
        at hTestEval
      rw [__smtx_model_eval.eq_1] at hTestEval
      injection hTestEval with hNative
      rw [← hPrefix] at hNative
      rw [hTrue]
      rw [← hNative]
  | inr hFalse =>
      have ht : test = Term.Boolean false := by
        simpa [test] using hFalse
      rw [ht] at hTestEval
      change __smtx_model_eval M (SmtTerm.Boolean false) =
          SmtValue.Boolean (native_str_in_re tail (native_re_concat rv native_re_all))
        at hTestEval
      rw [__smtx_model_eval.eq_1] at hTestEval
      injection hTestEval with hNative
      rw [← hPrefix] at hNative
      rw [hFalse]
      rw [← hNative]

private theorem str_indexof_re_eval_idx_ne_stuck_of_search_ne
    (tail r : Term) (offset : native_Int) :
    str_indexof_re_eval_tail_search_side tail r offset ≠ Term.Stuck ->
      str_indexof_re_eval_idx_term tail r ≠ Term.Stuck := by
  intro hSearch hIdx
  simp [str_indexof_re_eval_tail_search_side, hIdx, __eo_eq, __eo_ite,
    native_ite, native_teq] at hSearch

private theorem native_str_substr_to_end
    (s : native_String) (i : native_Int)
    (hNonneg : 0 <= i)
    (hLe : Int.toNat i <= s.length) :
    native_str_substr s i
        (native_zplus (native_zplus (native_str_len s) (native_zneg i)) 1) =
      s.drop (Int.toNat i) := by
  unfold native_str_substr
  by_cases hEnd : Int.toNat i = s.length
  · have hiEqLen : i = (s.length : Int) := by
      calc
        i = (Int.toNat i : Int) := (Int.toNat_of_nonneg hNonneg).symm
        _ = (s.length : Int) := by rw [hEnd]
    simp [native_str_len, native_zplus, native_zneg, hiEqLen]
  · have hLtNat : Int.toNat i < s.length := by omega
    have hLtLen : i < (s.length : Int) := by
      rw [← Int.toNat_of_nonneg hNonneg]
      exact Int.ofNat_lt.mpr hLtNat
    have hNotGeLen : ¬ (s.length : Int) <= i := Int.not_le_of_gt hLtLen
    have hLenSubNotLe : ¬ (s.length : Int) + -i + 1 <= 0 := by omega
    have hMinToNat :
        (min (native_zplus (native_zplus (native_str_len s) (native_zneg i)) 1)
            (native_str_len s - i)).toNat = s.length - Int.toNat i := by
      have hLeMin : native_str_len s - i <=
          native_zplus (native_zplus (native_str_len s) (native_zneg i)) 1 := by
        change (s.length : Int) - i <= (s.length : Int) + -i + 1
        omega
      have hSubEq :
          native_str_len s - i = Int.ofNat (s.length - Int.toNat i) := by
        rw [native_str_len, ← Int.toNat_of_nonneg hNonneg]
        exact (Int.ofNat_sub hLe).symm
      rw [Int.min_eq_right hLeMin, hSubEq]
      simp
    have hMinToNat' :
        (min (Int.ofNat s.length + -i + 1) (Int.ofNat s.length - i)).toNat =
          s.length - Int.toNat i := by
      simpa [native_str_len, native_zplus, native_zneg] using hMinToNat
    have hTake :
        (s.drop (Int.toNat i)).take (s.length - Int.toNat i) =
          s.drop (Int.toNat i) := by
      apply List.take_of_length_le
      rw [List.length_drop]
      exact Nat.le_refl _
    have hNotNeg : ¬ i < 0 := Int.not_lt_of_ge hNonneg
    simp [native_str_len, native_zplus, native_zneg, hNotNeg, hLenSubNotLe,
      hNotGeLen]
    change
      List.take
          ((min (Int.ofNat s.length + -i + 1) (Int.ofNat s.length - i)).toNat)
          (List.drop (Int.toNat i) s) =
        List.drop (Int.toNat i) s
    rw [hMinToNat']
    exact hTake

private theorem str_indexof_re_eval_idx_term_eq
    (M : SmtModel) (hM : model_total_typed M)
    (tail : native_String) (r : Term) (offset : native_Int)
    (rv : native_RegLan)
    (hTailValid : native_string_valid tail = true)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSearchNe :
      str_indexof_re_eval_tail_search_side (Term.String tail) r offset ≠
        Term.Stuck) :
    str_indexof_re_eval_idx_term (Term.String tail) r =
      Term.Numeral
        (match native_re_find_idx_aux rv tail 0 with
        | some (idx, _) => Int.ofNat idx
        | none => -1) := by
  cases tail with
  | nil =>
      have hIdxNe :
          str_indexof_re_eval_idx_term (Term.String []) r ≠ Term.Stuck :=
        str_indexof_re_eval_idx_ne_stuck_of_search_ne (Term.String []) r offset
          hSearchNe
      let test := str_indexof_re_eval_match_test (Term.String []) r
      let second :=
        __eo_add (Term.Numeral 0)
          (__str_first_match_rec_smallest (Term.String []) r (Term.Numeral 0))
      let thenTerm :=
        __eo_mk_apply
          (Term.Apply (Term.UOp UserOp._at__at_pair) (Term.Numeral 0))
          second
      let elseTerm :=
        Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_pair)
            (Term.Numeral (-1 : native_Int)))
          (Term.Numeral (-1 : native_Int))
      have hFirstNe :
          __eo_ite test thenTerm elseTerm ≠ Term.Stuck := by
        intro hFirst
        have hIdxStuck :
            str_indexof_re_eval_idx_term (Term.String []) r = Term.Stuck := by
          simp [str_indexof_re_eval_idx_term, str_indexof_re_eval_first_match_term,
            str_indexof_re_eval_match_test, test, thenTerm, elseTerm,
            __str_first_match_rec, __str_flatten, __str_nary_intro,
            __eo_requires, __eo_is_str, __eo_is_str_internal, native_ite,
            native_teq, native_not, SmtEval.native_and, hFirst]
        exact hIdxNe hIdxStuck
      have hBool := eo_ite_cond_eq_true_or_false_of_ne_stuck test thenTerm
        elseTerm hFirstNe
      have hTestEq :=
        str_indexof_re_eval_match_test_eq_of_bool M hM [] r rv hTailValid
          hRTy hREval (by simpa [test] using hBool)
      cases hPref : native_re_prefix_match_len? rv [] with
      | none =>
          have hFind :
              native_re_find_idx_aux rv [] 0 = none := by
            rw [native_re_find_idx_aux.eq_def]
            simp [hPref]
          simp [str_indexof_re_eval_idx_term, str_indexof_re_eval_first_match_term,
            str_indexof_re_eval_match_test, hTestEq, hPref, hFind,
            __str_first_match_rec, __str_flatten, __str_nary_intro,
            __eo_requires, __eo_is_str, __eo_is_str_internal, __eo_ite,
            native_ite, native_teq, native_not, SmtEval.native_and]
      | some len =>
          have hFind :
              native_re_find_idx_aux rv [] 0 = some (0, len) := by
            rw [native_re_find_idx_aux.eq_def]
            simp [hPref]
          have hSecondNe : second ≠ Term.Stuck := by
            intro hSecond
            have hIdxStuck :
                str_indexof_re_eval_idx_term (Term.String []) r = Term.Stuck := by
              simp [str_indexof_re_eval_idx_term,
                str_indexof_re_eval_first_match_term,
                str_indexof_re_eval_match_test, hTestEq, hPref, second,
                thenTerm, elseTerm, hSecond, __str_first_match_rec,
                __str_flatten, __str_nary_intro, __eo_requires, __eo_is_str,
                __eo_is_str_internal, __eo_ite, __eo_mk_apply, native_ite,
                native_teq, native_not, SmtEval.native_and]
            exact hIdxNe hIdxStuck
          simp [str_indexof_re_eval_idx_term, str_indexof_re_eval_first_match_term,
            str_indexof_re_eval_match_test, hTestEq, hPref, hFind, second,
            thenTerm, elseTerm, hSecondNe, __str_first_match_rec,
            __str_flatten, __str_nary_intro, __eo_requires, __eo_is_str,
            __eo_is_str_internal, __eo_ite, __eo_mk_apply, native_ite,
            native_teq, native_not, SmtEval.native_and]
  | cons c cs =>
      sorry

private theorem str_indexof_re_eval_tail_search_side_aux_model_eval
    (M : SmtModel) (hM : model_total_typed M)
    (tail : native_String) (r : Term) (offset : native_Int)
    (rv : native_RegLan)
    (hTailValid : native_string_valid tail = true)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hOffsetNonneg : 0 <= offset)
    (hSearchNe :
      str_indexof_re_eval_tail_search_side (Term.String tail) r offset ≠
        Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (str_indexof_re_eval_tail_search_side (Term.String tail) r offset)) =
      SmtValue.Numeral
        (match native_re_find_idx_aux rv tail 0 with
        | some (idx, _) => offset + Int.ofNat idx
        | none => -1) := by
  have hIdxEq :=
    str_indexof_re_eval_idx_term_eq M hM tail r offset rv hTailValid hRTy hREval
      hSearchNe
  cases hFind : native_re_find_idx_aux rv tail 0 with
  | none =>
      simp [str_indexof_re_eval_tail_search_side,
        hIdxEq, hFind, __eo_eq, __eo_ite, native_ite, native_teq]
      change __smtx_model_eval M (SmtTerm.Numeral (-1)) =
        SmtValue.Numeral (-1)
      rw [__smtx_model_eval.eq_2]
  | some p =>
      cases p with
      | mk idx len =>
          have hIdxNe : Term.Numeral (Int.ofNat idx) ≠
              Term.Numeral (-1 : native_Int) := by
            intro h
            simp at h
          simp [str_indexof_re_eval_tail_search_side,
            hIdxEq, hFind, __eo_eq, __eo_ite, __eo_add, native_ite,
            native_teq, hIdxNe]
          change __smtx_model_eval M
              (SmtTerm.Numeral (offset + Int.ofNat idx)) =
            SmtValue.Numeral (offset + Int.ofNat idx)
          rw [__smtx_model_eval.eq_2]

private theorem str_indexof_re_eval_tail_search_side_model_eval_of_aux
    (M : SmtModel) (hM : model_total_typed M)
    (tail : native_String) (r : Term) (offset : native_Int)
    (rv : native_RegLan)
    (hTailValid : native_string_valid tail = true)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hOffsetNonneg : 0 <= offset)
    (hSearchNe :
      str_indexof_re_eval_tail_search_side (Term.String tail) r offset ≠
        Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (str_indexof_re_eval_tail_search_side (Term.String tail) r offset)) =
      SmtValue.Numeral
        (match native_re_find_idx_aux rv tail (Int.toNat offset) with
        | some (idx, _) => Int.ofNat idx
        | none => -1) := by
  have hRelative :=
    str_indexof_re_eval_tail_search_side_aux_model_eval M hM tail r offset rv
      hTailValid hRTy hREval hOffsetNonneg hSearchNe
  rw [hRelative]
  rw [native_re_find_idx_aux_offset rv tail (Int.toNat offset)]
  cases hFind : native_re_find_idx_aux rv tail 0 with
  | none =>
      simp [hFind]
  | some p =>
      cases p with
      | mk idx len =>
          have hOffsetEq : (Int.toNat offset : Int) = offset :=
            Int.toNat_of_nonneg hOffsetNonneg
          simp [hFind, hOffsetEq]

private theorem str_indexof_re_eval_tail_search_side_model_eval
    (M : SmtModel) (hM : model_total_typed M)
    (str : native_String) (r : Term) (ni : native_Int) (rv : native_RegLan)
    (hSTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hNiNonneg : 0 <= ni)
    (hStartLe : Int.toNat ni <= str.length)
    (hSearchNe :
      str_indexof_re_eval_tail_search_side (Term.String (str.drop (Int.toNat ni)))
        r ni ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt
          (str_indexof_re_eval_tail_search_side
            (Term.String (str.drop (Int.toNat ni))) r ni)) =
      SmtValue.Numeral
        (match native_re_find_idx_from rv str (Int.toNat ni) with
        | some (idx, _) => Int.ofNat idx
        | none => -1) := by
  have hValid : native_string_valid str = true :=
    native_string_valid_of_smtx_typeof_eo_string str hSTy
  have hTailValid : native_string_valid (str.drop (Int.toNat ni)) = true :=
    native_string_valid_drop str (Int.toNat ni) hValid
  have hAux :=
    str_indexof_re_eval_tail_search_side_model_eval_of_aux M hM
      (str.drop (Int.toNat ni)) r ni rv hTailValid hRTy hREval hNiNonneg
      hSearchNe
  simpa [native_re_find_idx_from] using hAux

private theorem str_indexof_re_eval_search_side_model_eval
    (M : SmtModel) (hM : model_total_typed M)
    (str : native_String) (r : Term) (ni : native_Int) (rv : native_RegLan)
    (hSTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hNiNonneg : 0 <= ni)
    (hStartLe : Int.toNat ni <= str.length)
    (hSearchNe : str_indexof_re_eval_search_side str r ni ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (str_indexof_re_eval_search_side str r ni)) =
      SmtValue.Numeral
        (match native_re_find_idx_from rv str (Int.toNat ni) with
        | some (idx, _) => Int.ofNat idx
        | none => -1) := by
  have hTailEq :
      __eo_extract (Term.String str) (Term.Numeral ni) (__eo_len (Term.String str)) =
        Term.String (str.drop (Int.toNat ni)) := by
    simp only [__eo_extract, __eo_len]
    rw [native_str_substr_to_end str ni hNiNonneg hStartLe]
  have hTailSearchNe :
      str_indexof_re_eval_tail_search_side (Term.String (str.drop (Int.toNat ni)))
        r ni ≠ Term.Stuck := by
    simpa [str_indexof_re_eval_search_side, hTailEq] using hSearchNe
  have hTailEval :=
    str_indexof_re_eval_tail_search_side_model_eval M hM str r ni rv hSTy
      hRTy hREval hNiNonneg hStartLe hTailSearchNe
  simpa [str_indexof_re_eval_search_side, hTailEq] using hTailEval

private theorem str_indexof_re_eval_in_bounds_side_model_eval
    (M : SmtModel) (hM : model_total_typed M)
    (str : native_String) (r : Term) (ni : native_Int) (rv : native_RegLan)
    (hSTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hNiNonneg : 0 <= ni)
    (hStartLe : Int.toNat ni <= str.length)
    (hSideNe : str_indexof_re_eval_side str r ni ≠ Term.Stuck) :
    __smtx_model_eval M (__eo_to_smt (str_indexof_re_eval_side str r ni)) =
      SmtValue.Numeral
        (match native_re_find_idx_from rv str (Int.toNat ni) with
        | some (idx, _) => Int.ofNat idx
        | none => -1) := by
  have hNiLeLen : ni <= Int.ofNat str.length := by
    have hLe : (Int.toNat ni : Int) <= Int.ofNat str.length :=
      Int.ofNat_le.mpr hStartLe
    rw [Int.toNat_of_nonneg hNiNonneg] at hLe
    exact hLe
  have hGtBool : native_zlt (native_str_len str) ni = false := by
    have hLenLe : ni <= (str.length : Int) := by
      simpa using hNiLeLen
    by_cases h : (str.length : Int) < ni
    · omega
    · simp [native_str_len, native_zlt, h]
  have hNegBool : native_zlt ni 0 = false := by
    by_cases h : ni < 0
    · exact False.elim ((Int.not_lt_of_ge hNiNonneg) h)
    · simp [native_zlt, h]
  have hSearchNe : str_indexof_re_eval_search_side str r ni ≠ Term.Stuck := by
    simpa [str_indexof_re_eval_side, __eo_len, __eo_gt, __eo_is_neg,
      __eo_or, __eo_ite, native_ite, native_teq, native_or, hGtBool,
      hNegBool] using hSideNe
  have hSearchEval :=
    str_indexof_re_eval_search_side_model_eval M hM str r ni rv hSTy hRTy
      hREval hNiNonneg hStartLe hSearchNe
  simpa [str_indexof_re_eval_side, __eo_len, __eo_gt, __eo_is_neg, __eo_or,
    __eo_ite, native_ite, native_teq, native_or, hGtBool, hNegBool] using
      hSearchEval

private theorem str_indexof_re_eval_concrete_side_model_eval
    (M : SmtModel) (hM : model_total_typed M)
    (str : native_String) (r : Term) (ni : native_Int) (rv : native_RegLan)
    (hSTy : __smtx_typeof (__eo_to_smt (Term.String str)) =
      SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSideNe : str_indexof_re_eval_side str r ni ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt (str_indexof_re_eval_side str r ni)) =
      SmtValue.Numeral (native_str_indexof_re str rv ni) := by
  by_cases hNeg : ni < 0
  · have hNegBool : native_zlt ni 0 = true := by
      simp [native_zlt, hNeg]
    simp [str_indexof_re_eval_side, str_indexof_re_eval_match_regex,
      __eo_len, __eo_extract, __eo_gt, __eo_is_neg, __eo_or, __eo_ite,
      native_ite, native_teq, native_or, hNegBool, native_str_indexof_re, hNeg]
    change __smtx_model_eval M (SmtTerm.Numeral (-1)) = SmtValue.Numeral (-1)
    rw [__smtx_model_eval.eq_2]
  · by_cases hPastEnd : Int.ofNat str.length < ni
    · have hGtBool : native_zlt (native_str_len str) ni = true := by
        simpa [native_str_len, native_zlt] using hPastEnd
      have hNegBool : native_zlt ni 0 = false := by
        simp [native_zlt, hNeg]
      have hStartNotLe : ¬ Int.toNat ni <= str.length := by
        intro hStartLe
        have hNiNonneg : 0 <= ni := Int.not_lt.mp hNeg
        have hNiEq : Int.ofNat (Int.toNat ni) = ni :=
          Int.toNat_of_nonneg hNiNonneg
        have hLe : (Int.toNat ni : Int) <= (str.length : Int) := by
          exact_mod_cast hStartLe
        change Int.ofNat (Int.toNat ni) <= Int.ofNat str.length at hLe
        rw [hNiEq] at hLe
        omega
      simp [str_indexof_re_eval_side, str_indexof_re_eval_match_regex,
        __eo_len, __eo_extract, __eo_gt, __eo_is_neg, __eo_or, __eo_ite,
        native_ite, native_teq, native_or, hGtBool, hNegBool,
        native_str_indexof_re, hNeg, hStartNotLe]
      change __smtx_model_eval M (SmtTerm.Numeral (-1)) = SmtValue.Numeral (-1)
      rw [__smtx_model_eval.eq_2]
    · have hNiNonneg : 0 <= ni := Int.not_lt.mp hNeg
      have hNiLeLen : ni <= Int.ofNat str.length := Int.not_lt.mp hPastEnd
      have hStartLe : Int.toNat ni <= str.length := by
        exact Int.toNat_le.mpr hNiLeLen
      have hValid : native_string_valid str = true :=
        native_string_valid_of_smtx_typeof_eo_string str hSTy
      have hSideEval :=
        str_indexof_re_eval_in_bounds_side_model_eval M hM str r ni rv hSTy
          hRTy hREval hNiNonneg hStartLe hSideNe
      simpa [native_str_indexof_re, hNeg, hValid, hStartLe] using hSideEval

private theorem str_indexof_re_eval_side_model_eval
    (M : SmtModel) (hM : model_total_typed M)
    (s r n m : Term)
    (hEqTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m))
    (hProgNe :
      __eo_prog_str_indexof_re_eval
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m) ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n)) =
      __smtx_model_eval M (__eo_to_smt m) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n
  let body := Term.Apply (Term.Apply Term.eq lhs) m
  let lenTerm := __eo_len s
  let tail := __eo_extract s n lenTerm
  let matchTerm :=
    __eo_requires (__eo_is_str tail) (Term.Boolean true)
      (__str_first_match_rec (__str_flatten (__str_nary_intro tail)) r
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (Term.Numeral 0))
  let idxTerm := __pair_first matchTerm
  let side :=
    __eo_ite (__eo_or (__eo_gt n lenTerm) (__eo_is_neg n))
      (Term.Numeral (-1 : native_Int))
      (__eo_ite (__eo_eq idxTerm (Term.Numeral (-1 : native_Int)))
        (Term.Numeral (-1 : native_Int))
        (__eo_add n idxTerm))
  change __eo_requires side m body ≠ Term.Stuck at hProgNe
  have hSideEq : side = m :=
    eo_requires_eq_of_ne_stuck side m body hProgNe
  have hSideNe : side ≠ Term.Stuck :=
    eo_requires_left_ne_stuck_of_ne_stuck side m body hProgNe
  have hEqOperands :=
    eq_operands_have_smt_translation_of_eq_has_smt_translation lhs m hEqTrans
  have hArgTypes :=
    str_indexof_re_args_smt_types_of_has_translation s r n hEqOperands.1
  have hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan := hArgTypes.2.1
  have hREvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt r)) =
        SmtType.RegLan := by
    simpa [hRTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt r) (by
        unfold term_has_non_none_type
        rw [hRTy]
        simp)
  rcases reglan_value_canonical hREvalTy with ⟨rv, hREval⟩
  cases s <;> first
  | case Binary w bv =>
      have hBad := hArgTypes.1
      change __smtx_typeof (SmtTerm.Binary w bv) = SmtType.Seq SmtType.Char at hBad
      cases hCond :
          native_and (native_zleq 0 w)
            (native_zeq bv (native_mod_total bv (native_int_pow2 w))) <;>
        simp [__smtx_typeof, native_ite, hCond] at hBad
  | case String str =>
      cases n <;> first
      | case Numeral ni =>
      have hConcreteSideNe : str_indexof_re_eval_side str r ni ≠ Term.Stuck := by
        simpa [str_indexof_re_eval_side, str_indexof_re_eval_match_regex,
          side, lenTerm, tail, matchTerm, idxTerm] using hSideNe
      have hSideEval :=
        str_indexof_re_eval_concrete_side_model_eval M hM str r ni rv
          hArgTypes.1 hRTy hREval hConcreteSideNe
      have hLhsEval :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.Apply Term.str_indexof_re (Term.String str)) r)
                  (Term.Numeral ni))) =
            SmtValue.Numeral (native_str_indexof_re str rv ni) := by
        change __smtx_model_eval M
            (SmtTerm.str_indexof_re (SmtTerm.String str) (__eo_to_smt r)
              (SmtTerm.Numeral ni)) =
          SmtValue.Numeral (native_str_indexof_re str rv ni)
        simp [__smtx_model_eval, hREval, __smtx_model_eval_str_indexof_re,
          native_unpack_string_pack_string]
      rw [← hSideEq, hLhsEval]
      simpa [str_indexof_re_eval_side, str_indexof_re_eval_match_regex,
        side, lenTerm, tail, matchTerm, idxTerm] using hSideEval.symm
      | (change side ≠ Term.Stuck at hSideNe
         simp [lenTerm, tail, matchTerm, idxTerm, side, __eo_len, __eo_extract,
           __eo_gt, __eo_is_neg, __eo_or, __eo_ite, __eo_requires, native_ite,
           native_teq, native_not, SmtEval.native_not] at hSideNe)
  | (change side ≠ Term.Stuck at hSideNe
     simp [lenTerm, tail, matchTerm, idxTerm, side, __eo_len, __eo_extract,
       __eo_gt, __eo_is_neg, __eo_or, __eo_ite, __eo_requires, native_ite,
       native_teq, native_not, SmtEval.native_not] at hSideNe)

private theorem str_indexof_re_eval_valid_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s r n m : Term)
    (hArgTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m))
    (hProgNe :
      __eo_prog_str_indexof_re_eval
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m) ≠ Term.Stuck)
    (hProgTy :
      __eo_typeof
        (__eo_prog_str_indexof_re_eval
          (Term.Apply
            (Term.Apply Term.eq
              (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
            m)) =
        Term.Bool) :
    StepRuleProperties M []
      (__eo_prog_str_indexof_re_eval
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n))
          m)) := by
  let lhs := Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re s) r) n
  let body := Term.Apply (Term.Apply Term.eq lhs) m
  let lenTerm := __eo_len s
  let tail := __eo_extract s n lenTerm
  let matchTerm :=
    __eo_requires (__eo_is_str tail) (Term.Boolean true)
      (__str_first_match_rec (__str_flatten (__str_nary_intro tail)) r
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) (Term.UOp UserOp.re_all))
            (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))
        (Term.Numeral 0))
  let idxTerm := __pair_first matchTerm
  let side :=
    __eo_ite (__eo_or (__eo_gt n lenTerm) (__eo_is_neg n))
      (Term.Numeral (-1 : native_Int))
      (__eo_ite (__eo_eq idxTerm (Term.Numeral (-1 : native_Int)))
        (Term.Numeral (-1 : native_Int))
        (__eo_add n idxTerm))
  have hReqEq : __eo_requires side m body = body := by
    change __eo_requires side m body ≠ Term.Stuck at hProgNe
    exact eo_requires_result_eq_of_ne_stuck side m body hProgNe
  have hBodyTy : __eo_typeof body = Term.Bool := by
    change __eo_typeof (__eo_requires side m body) = Term.Bool at hProgTy
    rw [hReqEq] at hProgTy
    exact hProgTy
  change StepRuleProperties M [] (__eo_requires side m body)
  rw [hReqEq]
  have hBool : RuleProofs.eo_has_bool_type body :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type body hArgTrans hBodyTy
  refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type body hBool⟩
  intro _hPremises
  exact RuleProofs.eo_interprets_eq_of_rel M lhs m hBool <| by
    have hEval :=
      str_indexof_re_eval_side_model_eval M hM s r n m hArgTrans hProgNe
    rw [hEval]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt m))

end RuleProofs

theorem cmd_step_str_indexof_re_eval_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_indexof_re_eval args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_indexof_re_eval args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_indexof_re_eval args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.str_indexof_re_eval args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
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
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              cases a1 with
              | Apply eqApp m =>
                  cases eqApp with
                  | Apply eqOp lhs =>
                      cases eqOp with
                      | UOp eqOpName =>
                          cases eqOpName with
                          | eq =>
                              cases lhs with
                              | Apply idxApp n =>
                                  cases idxApp with
                                  | Apply idxApp2 r =>
                                      cases idxApp2 with
                                      | Apply idxOp sArg =>
                                          cases idxOp with
                                          | UOp idxOpName =>
                                              cases idxOpName with
                                              | str_indexof_re =>
                                                  have hProps :=
                                                    RuleProofs.str_indexof_re_eval_valid_properties
                                                      M hM sArg r n m (by
                                                        simpa using hA1Trans) (by
                                                        change
                                                          __eo_prog_str_indexof_re_eval
                                                            (Term.Apply
                                                              (Term.Apply Term.eq
                                                                (Term.Apply
                                                                  (Term.Apply
                                                                    (Term.Apply Term.str_indexof_re
                                                                      sArg) r) n))
                                                              m) ≠
                                                            Term.Stuck at hProg
                                                        exact hProg) (by
                                                        change
                                                          __eo_typeof
                                                            (__eo_prog_str_indexof_re_eval
                                                              (Term.Apply
                                                                (Term.Apply Term.eq
                                                                  (Term.Apply
                                                                    (Term.Apply
                                                                      (Term.Apply Term.str_indexof_re
                                                                        sArg) r) n))
                                                                m)) =
                                                            Term.Bool at hResultTy
                                                        exact hResultTy)
                                                  change StepRuleProperties M []
                                                    (__eo_prog_str_indexof_re_eval
                                                      (Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply
                                                            (Term.Apply
                                                              (Term.Apply Term.str_indexof_re
                                                                sArg) r) n))
                                                        m))
                                                  simpa [premiseTermList] using hProps
                                              | _ =>
                                                  change Term.Stuck ≠ Term.Stuck at hProg
                                                  exact False.elim (hProg rfl)
                                          | _ =>
                                              change Term.Stuck ≠ Term.Stuck at hProg
                                              exact False.elim (hProg rfl)
                                      | _ =>
                                          change Term.Stuck ≠ Term.Stuck at hProg
                                          exact False.elim (hProg rfl)
                                  | _ =>
                                      change Term.Stuck ≠ Term.Stuck at hProg
                                      exact False.elim (hProg rfl)
                              | _ =>
                                  change Term.Stuck ≠ Term.Stuck at hProg
                                  exact False.elim (hProg rfl)
                          | _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                      | _ =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
