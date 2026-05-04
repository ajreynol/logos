import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.TypePreservation.Helpers
import Cpc.Proofs.TypePreservation.SeqStringRegex

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev mkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev mkConcat (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y

private abbrev mkPair (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) x) y

private abbrev concatEqNormalize (rev x : Term) : Term :=
  __eo_ite rev (__eo_list_rev (Term.UOp UserOp.str_concat) x) x

private abbrev concatEqStrip (rev s t : Term) : Term :=
  __str_strip_prefix (concatEqNormalize rev (__str_nary_intro s))
    (concatEqNormalize rev (__str_nary_intro t))

private abbrev concatEqLhs (rev s t : Term) : Term :=
  __str_nary_elim (concatEqNormalize rev (__pair_first (concatEqStrip rev s t)))

private abbrev concatEqRhs (rev s t : Term) : Term :=
  __str_nary_elim (concatEqNormalize rev (__pair_second (concatEqStrip rev s t)))

private theorem seq_ne_none (T : SmtType) : SmtType.Seq T ≠ SmtType.None := by
  intro h
  cases h

private theorem smtx_model_eval_str_concat_term_eq (M : SmtModel) (x y : Term) :
    __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
      __smtx_model_eval_str_concat (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  rw [show __eo_to_smt (mkConcat x y) =
      SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y) by
    rfl]
  rw [__smtx_model_eval.eq_79]

private theorem str_concat_args_of_non_none (x y : Term) :
    __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None ->
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  intro h
  have h' :
      term_has_non_none_type (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) := by
    simpa [term_has_non_none_type, mkConcat] using h
  exact seq_binop_args_of_non_none (op := SmtTerm.str_concat)
    (typeof_str_concat_eq (__eo_to_smt x) (__eo_to_smt y)) h'

private theorem smt_typeof_str_concat_of_seq (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T := by
  change __smtx_typeof (SmtTerm.str_concat (__eo_to_smt x) (__eo_to_smt y)) =
    SmtType.Seq T
  rw [typeof_str_concat_eq (__eo_to_smt x) (__eo_to_smt y)]
  simp [__smtx_typeof_seq_op_2, native_ite, native_Teq, hxTy, hyTy]

private theorem str_concat_args_of_seq_type (x y : Term) (T : SmtType)
    (hTy : __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  have hNN :
      __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
    rw [hTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none x y hNN with ⟨U, hxTyU, hyTyU⟩
  have hConcatTyU :
      __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq x y U hxTyU hyTyU
  have hUT : U = T := by
    have hSeq : SmtType.Seq U = SmtType.Seq T := by
      rw [← hConcatTyU, hTy]
    injection hSeq
  constructor
  · simpa [hUT] using hxTyU
  · simpa [hUT] using hyTyU

private theorem smt_typeof_str_concat_seq_of_non_none (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T := by
  rcases str_concat_args_of_non_none x y hNN with ⟨T, hxTy, hyTy⟩
  exact ⟨T, smt_typeof_str_concat_of_seq x y T hxTy hyTy⟩

private theorem str_nary_intro_concat_eq (x y : Term) :
    __str_nary_intro (mkConcat x y) = mkConcat x y := by
  rfl

private theorem str_nary_intro_concat_has_smt_translation
    (x y : Term)
    (hNN : __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro (mkConcat x y))) ≠
      SmtType.None := by
  simpa [str_nary_intro_concat_eq] using hNN

private theorem concatEq_seq_pack_of_both_concat
    (sHead sTail tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail))) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat sHead sTail))) ≠
        SmtType.None ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat tHead tTail))) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat sHead sTail) (mkConcat tHead tTail) hPremBool with
    ⟨hSame, hLeftNN⟩
  rcases smt_typeof_str_concat_seq_of_non_none sHead sTail hLeftNN with
    ⟨T, hLeftTy⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt (mkConcat tHead tTail)) ≠
        SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  exact ⟨T, hLeftTy,
    str_nary_intro_concat_has_smt_translation sHead sTail hLeftNN,
    str_nary_intro_concat_has_smt_translation tHead tTail hRightNN⟩

private theorem concatEq_seq_pack_of_left_concat
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat sHead sTail))) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat sHead sTail) t hPremBool with
    ⟨_, hLeftNN⟩
  rcases smt_typeof_str_concat_seq_of_non_none sHead sTail hLeftNN with
    ⟨T, hLeftTy⟩
  exact ⟨T, hLeftTy,
    str_nary_intro_concat_has_smt_translation sHead sTail hLeftNN,
    hIntroTNN⟩

private theorem concatEq_seq_pack_of_right_concat
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat tHead tTail))) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s (mkConcat tHead tTail) hPremBool with
    ⟨hSame, hLeftNN⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt (mkConcat tHead tTail)) ≠
        SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases smt_typeof_str_concat_seq_of_non_none tHead tTail hRightNN with
    ⟨T, hRightTy⟩
  have hLeftTy :
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [hSame, hRightTy]
  exact ⟨T, hLeftTy, hIntroSNN,
    str_nary_intro_concat_has_smt_translation tHead tTail hRightNN⟩

private theorem concatEq_seq_pack_of_left_concat_intro_eq_self
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroEq : __str_nary_intro t = t) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat sHead sTail))) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat sHead sTail) t hPremBool with
    ⟨hSame, hLeftNN⟩
  have hRightNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
    simpa [hIntroEq] using hRightNN
  exact concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
    hIntroTNN

private theorem concatEq_seq_pack_of_right_concat_intro_eq_self
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroEq : __str_nary_intro s = s) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat tHead tTail))) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s (mkConcat tHead tTail) hPremBool with
    ⟨_hSame, hLeftNN⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None := by
    simpa [hIntroEq] using hLeftNN
  exact concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
    hIntroSNN

private theorem eq_bool_seq_of_left_concat
    (sHead sTail t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t)) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat sHead sTail) t hPremBool with
    ⟨hSame, hLeftNN⟩
  rcases smt_typeof_str_concat_seq_of_non_none sHead sTail hLeftNN with
    ⟨T, hLeftTy⟩
  exact ⟨T, hLeftTy, by rw [← hSame, hLeftTy]⟩

private theorem eq_bool_seq_of_right_concat
    (s tHead tTail : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail))) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (mkConcat tHead tTail)) =
        SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s (mkConcat tHead tTail) hPremBool with
    ⟨hSame, hLeftNN⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt (mkConcat tHead tTail)) ≠
        SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases smt_typeof_str_concat_seq_of_non_none tHead tTail hRightNN with
    ⟨T, hRightTy⟩
  exact ⟨T, by rw [hSame, hRightTy], hRightTy⟩

private theorem eq_bool_right_seq_of_left_seq (x y : Term) (T : SmtType)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x y))
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hBool with
    ⟨hSame, _⟩
  rw [← hSame, hxTy]

private theorem eq_bool_left_seq_of_right_seq (x y : Term) (T : SmtType)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x y))
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hBool with
    ⟨hSame, _⟩
  rw [hSame, hyTy]

private theorem eval_seq_empty_of_type (M : SmtModel) (A : Term) (T : SmtType) :
    __eo_to_smt_type A = SmtType.Seq T ->
    __smtx_model_eval M (__eo_to_smt (__seq_empty A)) =
      SmtValue.Seq (SmtSeq.empty T) := by
  intro hA
  by_cases hSpecial : A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst hSpecial
    simp [__eo_to_smt_type, __smtx_typeof_guard] at hA
    cases hA
    change __smtx_model_eval M (SmtTerm.String "") =
      SmtValue.Seq (SmtSeq.empty SmtType.Char)
    rw [__smtx_model_eval.eq_4]
    simp [native_pack_string, __smtx_ssm_char_values_of_string, native_pack_seq]
  · by_cases hStuck : A = Term.Stuck
    · subst hStuck
      simp [__eo_to_smt_type] at hA
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault]
      rw [show __eo_to_smt (Term.seq_empty A) =
          __eo_to_smt_seq_empty (__eo_to_smt_type A) by
        rfl]
      rw [hA]
      change __smtx_model_eval M (SmtTerm.seq_empty T) =
        SmtValue.Seq (SmtSeq.empty T)
      rw [__smtx_model_eval.eq_77]

private theorem eval_seq_empty_typeof (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  exact eval_seq_empty_of_type M (__eo_typeof x) T hA

private theorem smt_typeof_seq_empty_of_type (A : Term) (T : SmtType) :
    __eo_to_smt_type A = SmtType.Seq T ->
    __smtx_typeof (__eo_to_smt (__seq_empty A)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (__seq_empty A)) = SmtType.Seq T := by
  intro hA hEmptyNN
  by_cases hSpecial : A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst hSpecial
    simp [__eo_to_smt_type, __smtx_typeof_guard] at hA
    cases hA
    change __smtx_typeof (SmtTerm.String "") = SmtType.Seq SmtType.Char
    rw [__smtx_typeof.eq_4]
  · by_cases hStuck : A = Term.Stuck
    · subst hStuck
      simp [__eo_to_smt_type] at hA
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault] at hEmptyNN
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) ≠
        SmtType.None at hEmptyNN
      rw [hA] at hEmptyNN
      change __smtx_typeof (SmtTerm.seq_empty T) ≠ SmtType.None at hEmptyNN
      rw [hDefault]
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
        SmtType.Seq T
      rw [hA]
      exact TranslationProofs.smtx_typeof_seq_empty_of_non_none T hEmptyNN

private theorem smt_typeof_seq_empty_seq_of_non_none (A : Term)
    (hEmptyNN : __smtx_typeof (__eo_to_smt (__seq_empty A)) ≠
      SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt (__seq_empty A)) = SmtType.Seq T := by
  by_cases hSpecial :
      A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst A
    exact ⟨SmtType.Char, by
      change __smtx_typeof (SmtTerm.String "") =
        SmtType.Seq SmtType.Char
      rw [__smtx_typeof.eq_4]⟩
  · by_cases hStuck : A = Term.Stuck
    · subst A
      have hNone : __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.None := by
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
      exact False.elim (hEmptyNN (by simpa [__seq_empty] using hNone))
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault] at hEmptyNN ⊢
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) ≠
        SmtType.None at hEmptyNN
      change ∃ T,
        __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
          SmtType.Seq T
      cases hA : __eo_to_smt_type A <;>
        simp [__eo_to_smt_seq_empty, hA] at hEmptyNN ⊢
      rename_i T
      exact ⟨T, TranslationProofs.smtx_typeof_seq_empty_of_non_none T
        (by simpa [__eo_to_smt_seq_empty, hA] using hEmptyNN)⟩

private theorem eo_to_smt_type_seq_of_seq_empty_non_none (A : Term)
    (hEmptyNN : __smtx_typeof (__eo_to_smt (__seq_empty A)) ≠
      SmtType.None) :
    ∃ T,
      __eo_to_smt_type A = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__seq_empty A)) =
          SmtType.Seq T := by
  by_cases hSpecial :
      A = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · subst A
    exact ⟨SmtType.Char, by
      have hNe : SmtType.Char ≠ SmtType.None := by
        intro h
        cases h
      simp [__eo_to_smt_type, __smtx_typeof_guard, native_Teq, native_ite,
        hNe],
      by
        change __smtx_typeof (SmtTerm.String "") =
          SmtType.Seq SmtType.Char
        rw [__smtx_typeof.eq_4]⟩
  · by_cases hStuck : A = Term.Stuck
    · subst A
      have hNone : __smtx_typeof (__eo_to_smt Term.Stuck) = SmtType.None := by
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
      exact False.elim (hEmptyNN (by simpa [__seq_empty] using hNone))
    · have hDefault : __seq_empty A = Term.seq_empty A := by
        cases A <;> simp [__seq_empty] at hStuck hSpecial ⊢
      rw [hDefault] at hEmptyNN ⊢
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) ≠
        SmtType.None at hEmptyNN
      change ∃ T,
        __eo_to_smt_type A = SmtType.Seq T ∧
          __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
            SmtType.Seq T
      cases hA : __eo_to_smt_type A <;>
        simp [__eo_to_smt_seq_empty, hA] at hEmptyNN
      rename_i T
      exact ⟨T, rfl,
        TranslationProofs.smtx_typeof_seq_empty_of_non_none T
          (by simpa [__eo_to_smt_seq_empty, hA] using hEmptyNN)⟩

private theorem smt_typeof_seq_of_seq_empty_typeof_non_none
    (x : Term)
    (hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None) :
    ∃ T,
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
          SmtType.Seq T := by
  rcases eo_to_smt_type_seq_of_seq_empty_non_none (__eo_typeof x)
      hEmptyNN with ⟨T, hType, hEmptyTy⟩
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hXNN
  exact ⟨T, by rw [hTypeMatch, hType], hEmptyTy⟩

private theorem smt_typeof_eq_seq_empty_seq_of_non_none
    (x A : Term)
    (hEq : x = __seq_empty A)
    (hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  subst x
  exact smt_typeof_seq_empty_seq_of_non_none A hXNN

private theorem smt_typeof_seq_empty_typeof (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch := TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  exact smt_typeof_seq_empty_of_type (__eo_typeof x) T hA hEmptyNN

private theorem seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hTInh : type_inhabited T)
    (hTWf : __smtx_type_wf T = true) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
      SmtType.None := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  by_cases hSpecial :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · rw [hSpecial]
    change __smtx_typeof (SmtTerm.String "") ≠ SmtType.None
    rw [__smtx_typeof.eq_4]
    exact seq_ne_none SmtType.Char
  · by_cases hStuck : __eo_typeof x = Term.Stuck
    · rw [hStuck] at hA
      simp [__eo_to_smt_type] at hA
    · have hDefault :
          __seq_empty (__eo_typeof x) = Term.seq_empty (__eo_typeof x) := by
        cases hTy : __eo_typeof x <;>
          simp [__seq_empty, hTy] at hStuck hSpecial ⊢
        case Apply f a =>
          cases f <;> simp at hSpecial ⊢
          case UOp op =>
            cases op <;> simp at hSpecial ⊢
            case Seq =>
              cases a <;> simp at hSpecial ⊢
              case UOp op' =>
                cases op' <;> simp at hSpecial ⊢
      rw [hDefault]
      change
        __smtx_typeof (__eo_to_smt_seq_empty
          (__eo_to_smt_type (__eo_typeof x))) ≠ SmtType.None
      rw [hA]
      change __smtx_typeof (SmtTerm.seq_empty T) ≠ SmtType.None
      have hInh : native_inhabited_type T = true :=
        (smtx_inhabited_type_eq_true_iff T).2 hTInh
      simp [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, hInh,
        hTWf]

private theorem eq_of_eo_eq_true_local (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem eo_eq_true_left_concat_right_not_concat_false
    (sHead sTail t : Term)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hHead : __eo_eq (mkConcat sHead sTail) t = Term.Boolean true) :
    False := by
  have hT : t = mkConcat sHead sTail :=
    eq_of_eo_eq_true_local (mkConcat sHead sTail) t hHead
  exact hTNotConcat ⟨sHead, sTail, hT⟩

private theorem eo_eq_true_left_not_concat_right_concat_false
    (s tHead tTail : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hHead : __eo_eq s (mkConcat tHead tTail) = Term.Boolean true) :
    False := by
  have hT : mkConcat tHead tTail = s :=
    eq_of_eo_eq_true_local s (mkConcat tHead tTail) hHead
  exact hSNotConcat ⟨tHead, tTail, hT.symm⟩

private theorem eo_eq_self_true_of_ne_stuck (x : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem eo_eq_cases_of_ne_stuck (x y : Term)
    (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_eq x y = Term.Boolean true ∨
      __eo_eq x y = Term.Boolean false := by
  by_cases hxy : y = x
  · subst y
    exact Or.inl (eo_eq_self_true_of_ne_stuck x hx)
  · right
    cases x <;> cases y <;>
      simp [__eo_eq, native_teq] at hx hy hxy ⊢
    all_goals assumption

private theorem eo_eq_cases_of_has_bool_type (x y : Term)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x y)) :
    __eo_eq x y = Term.Boolean true ∨
      __eo_eq x y = Term.Boolean false := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y
      hBool with ⟨hSame, hXNN⟩
  have hYNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    rw [← hSame]
    exact hXNN
  exact eo_eq_cases_of_ne_stuck x y
    (RuleProofs.term_ne_stuck_of_has_smt_translation x hXNN)
    (RuleProofs.term_ne_stuck_of_has_smt_translation y hYNN)

private theorem eo_ite_true (x y : Term) :
    __eo_ite (Term.Boolean true) x y = x := by
  rfl

private theorem eo_ite_false (x y : Term) :
    __eo_ite (Term.Boolean false) x y = y := by
  rfl

private theorem eo_ite_cases_of_ne_stuck (c x y : Term) :
    __eo_ite c x y ≠ Term.Stuck ->
    c = Term.Boolean true ∨ c = Term.Boolean false := by
  intro h
  by_cases hTrue : native_teq c (Term.Boolean true) = true
  · left
    simpa [native_teq] using hTrue
  · by_cases hFalse : native_teq c (Term.Boolean false) = true
    · right
      simpa [native_teq] using hFalse
    · simp [__eo_ite, hTrue, hFalse, SmtEval.native_ite] at h

private theorem eo_requires_self_eq_of_ne_stuck (x z : Term)
    (hx : x ≠ Term.Stuck) :
    __eo_requires x x z = z := by
  simp [__eo_requires, hx, native_teq, SmtEval.native_ite, SmtEval.native_not]

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  by_cases hxy : native_teq x y = true
  · by_cases hxOk : native_not (native_teq x Term.Stuck) = true
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite]
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite] at h
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

private theorem eo_requires_left_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h hStuck
  subst x
  simp [__eo_requires, native_teq, SmtEval.native_ite, SmtEval.native_not] at h

private theorem eo_requires_result_ne_stuck_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    z ≠ Term.Stuck := by
  intro h
  rw [← eo_requires_eq_result_of_ne_stuck x y z h]
  exact h

private theorem eo_is_ok_ne_stuck_of_true (x : Term) :
    __eo_is_ok x = Term.Boolean true ->
    x ≠ Term.Stuck := by
  intro h hx
  subst x
  simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at h

private theorem eo_is_ok_true_of_ne_stuck (x : Term) :
    x ≠ Term.Stuck ->
    __eo_is_ok x = Term.Boolean true := by
  intro hNe
  cases x <;> simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at hNe ⊢

private theorem eo_get_nil_rec_ne_stuck_of_is_list_true (f x : Term) :
    __eo_is_list f x = Term.Boolean true ->
    __eo_get_nil_rec f x ≠ Term.Stuck := by
  intro h
  have hOk : __eo_is_ok (__eo_get_nil_rec f x) = Term.Boolean true := by
    cases f <;> cases x <;>
      simp [__eo_is_list] at h ⊢ <;> exact h
  exact eo_is_ok_ne_stuck_of_true (__eo_get_nil_rec f x) hOk

private theorem eo_is_list_true_of_get_nil_rec_ne_stuck (f x : Term) :
    __eo_get_nil_rec f x ≠ Term.Stuck ->
    __eo_is_list f x = Term.Boolean true := by
  intro hRec
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst f
    simp [__eo_get_nil_rec] at hRec
  have hX : x ≠ Term.Stuck := by
    intro hX
    subst x
    simp [__eo_get_nil_rec] at hRec
  simp [__eo_is_list, eo_is_ok_true_of_ne_stuck (__eo_get_nil_rec f x) hRec]

private theorem eo_is_list_cons_head_eq_of_true (f g x y : Term) :
    __eo_is_list f (Term.Apply (Term.Apply g x) y) = Term.Boolean true ->
    g = f := by
  intro h
  have hRec :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f
      (Term.Apply (Term.Apply g x) y) h
  have hReq :
      __eo_requires f g (__eo_get_nil_rec f y) ≠ Term.Stuck := by
    cases f <;> simp [__eo_get_nil_rec] at hRec ⊢ <;> exact hRec
  exact (eo_requires_eq_of_ne_stuck f g (__eo_get_nil_rec f y) hReq).symm

private theorem eo_is_list_tail_true_of_cons_self (f x y : Term) :
    __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true ->
    __eo_is_list f y = Term.Boolean true := by
  intro h
  have hRec :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f
      (Term.Apply (Term.Apply f x) y) h
  have hReq :
      __eo_requires f f (__eo_get_nil_rec f y) ≠ Term.Stuck := by
    cases f <;> simp [__eo_get_nil_rec] at hRec ⊢ <;> exact hRec
  have hTail : __eo_get_nil_rec f y ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck f f (__eo_get_nil_rec f y) hReq
  exact eo_is_list_true_of_get_nil_rec_ne_stuck f y hTail

private theorem eo_get_nil_rec_cons_self_eq_of_tail_list (f x y : Term)
    (hF : f ≠ Term.Stuck)
    (hTail : __eo_is_list f y = Term.Boolean true) :
    __eo_get_nil_rec f (Term.Apply (Term.Apply f x) y) =
      __eo_get_nil_rec f y := by
  cases f <;> simp [__eo_get_nil_rec] at hF ⊢
  all_goals
    simp [__eo_requires, native_teq, native_ite, SmtEval.native_ite,
      SmtEval.native_not]

set_option linter.unusedSimpArgs false in
private theorem eo_get_nil_rec_str_concat_eq_of_nil_true (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil = nil := by
  cases nil <;>
    simp [__eo_get_nil_rec, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq, __eo_requires, native_ite, SmtEval.native_ite,
      SmtEval.native_not] at hNil ⊢
  case String s =>
    subst s
    simp [__eo_get_nil_rec, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq, __eo_requires, native_ite, SmtEval.native_ite,
      SmtEval.native_not]

set_option linter.unusedSimpArgs false in
private theorem eo_list_rev_str_concat_nil_eq_of_nil_true (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_list_rev (Term.UOp UserOp.str_concat) nil = nil := by
  cases nil <;>
    simp [__eo_list_rev, __eo_is_list, __eo_get_nil_rec,
      __eo_list_rev_rec, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_is_ok, __eo_eq, native_teq, __eo_requires, native_ite,
      SmtEval.native_ite, SmtEval.native_not] at hNil ⊢
  case String s =>
    subst s
    simp [__eo_list_rev, __eo_is_list, __eo_get_nil_rec, __eo_list_rev_rec,
      __eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_is_ok, __eo_eq,
      native_teq, __eo_requires, native_ite, SmtEval.native_ite,
      SmtEval.native_not]

set_option linter.unusedSimpArgs false in
private theorem eo_list_rev_rec_str_concat_nil_eq_of_nil_true
    (nil acc : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_list_rev_rec nil acc = acc := by
  cases nil <;>
    simp [__eo_list_rev_rec, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq] at hNil
  case String s =>
    subst s
    cases acc <;> rfl
  case seq_empty A =>
    cases acc <;> rfl

set_option linter.unusedSimpArgs false in
private theorem eo_is_list_str_concat_nil_true_of_nil_true (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true := by
  cases nil <;>
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __eo_is_ok, __eo_eq, native_teq,
      __eo_requires, native_ite, SmtEval.native_ite, SmtEval.native_not] at hNil ⊢
  case String s =>
    subst s
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __eo_is_ok, __eo_eq, native_teq,
      __eo_requires, native_ite, SmtEval.native_ite, SmtEval.native_not]

private theorem eo_is_list_cons_self_true_of_tail_list (f x y : Term)
    (hF : f ≠ Term.Stuck)
    (hTail : __eo_is_list f y = Term.Boolean true) :
    __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true := by
  have hRec : __eo_get_nil_rec f y ≠ Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f y hTail
  have hGet :
      __eo_get_nil_rec f (Term.Apply (Term.Apply f x) y) ≠ Term.Stuck := by
    rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTail]
    exact hRec
  exact eo_is_list_true_of_get_nil_rec_ne_stuck f
    (Term.Apply (Term.Apply f x) y) hGet

private theorem eo_list_rev_is_list_true_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    __eo_is_list f a = Term.Boolean true := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
        (__eo_list_rev_rec a (__eo_get_nil_rec f a)) ≠ Term.Stuck := by
    simpa [__eo_list_rev] using h
  exact eo_requires_eq_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
    (__eo_list_rev_rec a (__eo_get_nil_rec f a)) hReq

private theorem eo_list_rev_rec_ne_stuck_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    __eo_list_rev_rec a (__eo_get_nil_rec f a) ≠ Term.Stuck := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
        (__eo_list_rev_rec a (__eo_get_nil_rec f a)) ≠ Term.Stuck := by
    simpa [__eo_list_rev] using h
  exact eo_requires_result_ne_stuck_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
    (__eo_list_rev_rec a (__eo_get_nil_rec f a)) hReq

private theorem eo_list_rev_eq_rec_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    __eo_list_rev f a = __eo_list_rev_rec a (__eo_get_nil_rec f a) := by
  intro h
  have hReq :
      __eo_requires (__eo_is_list f a) (Term.Boolean true)
        (__eo_list_rev_rec a (__eo_get_nil_rec f a)) ≠ Term.Stuck := by
    simpa [__eo_list_rev] using h
  simpa [__eo_list_rev] using
    eo_requires_eq_result_of_ne_stuck (__eo_is_list f a) (Term.Boolean true)
      (__eo_list_rev_rec a (__eo_get_nil_rec f a)) hReq

private theorem eo_list_rev_arg_ne_stuck_of_ne_stuck (f a : Term) :
    __eo_list_rev f a ≠ Term.Stuck ->
    a ≠ Term.Stuck := by
  intro h ha
  subst a
  cases f <;>
    simp [__eo_list_rev, __eo_is_list, __eo_requires, native_ite, native_teq] at h

private theorem eo_list_rev_rec_cons (f x y acc : Term)
    (hAcc : acc ≠ Term.Stuck) :
    __eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc =
      __eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc) := by
  cases acc <;> simp [__eo_list_rev_rec] at hAcc ⊢

private theorem eo_list_rev_cons_eq_of_tail_list (f x y : Term)
    (hF : f ≠ Term.Stuck)
    (hTail : __eo_is_list f y = Term.Boolean true) :
    __eo_list_rev f (Term.Apply (Term.Apply f x) y) =
      __eo_list_rev_rec y (Term.Apply (Term.Apply f x)
        (__eo_get_nil_rec f y)) := by
  have hRec : __eo_get_nil_rec f y ≠ Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f y hTail
  have hConsList :
      __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list f x y hF hTail
  rw [__eo_list_rev]
  rw [hConsList]
  rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
    (__eo_list_rev_rec (Term.Apply (Term.Apply f x) y)
      (__eo_get_nil_rec f (Term.Apply (Term.Apply f x) y))) (by decide)]
  rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTail]
  exact eo_list_rev_rec_cons f x y (__eo_get_nil_rec f y) hRec

private theorem eo_list_rev_cons_tail_list_of_ne_stuck (f x y : Term)
    (hRev : __eo_list_rev f (Term.Apply (Term.Apply f x) y) ≠
      Term.Stuck) :
    __eo_is_list f y = Term.Boolean true := by
  have hList :
      __eo_is_list f (Term.Apply (Term.Apply f x) y) = Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck f (Term.Apply (Term.Apply f x) y)
      hRev
  exact eo_is_list_tail_true_of_cons_self f x y hList

private theorem eo_list_rev_cons_eq_of_ne_stuck (f x y : Term)
    (hRev : __eo_list_rev f (Term.Apply (Term.Apply f x) y) ≠
      Term.Stuck) :
    __eo_list_rev f (Term.Apply (Term.Apply f x) y) =
      __eo_list_rev_rec y (Term.Apply (Term.Apply f x)
        (__eo_get_nil_rec f y)) := by
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst f
    simp [__eo_list_rev, __eo_is_list, __eo_requires, native_teq,
      native_ite, SmtEval.native_ite] at hRev
  have hTail := eo_list_rev_cons_tail_list_of_ne_stuck f x y hRev
  exact eo_list_rev_cons_eq_of_tail_list f x y hF hTail

private theorem eo_list_rev_str_concat_cons_eq_of_ne_stuck (x y : Term)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat x y) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat x y) =
      __eo_list_rev_rec y
        (mkConcat x (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y)) := by
  exact eo_list_rev_cons_eq_of_ne_stuck (Term.UOp UserOp.str_concat) x y hRev

set_option linter.unusedSimpArgs false in
private theorem eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck
    (head nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
      mkConcat head nil := by
  rw [eo_list_rev_str_concat_cons_eq_of_ne_stuck head nil hRev]
  rw [eo_get_nil_rec_str_concat_eq_of_nil_true nil hNil]
  cases nil <;>
    simp [__eo_list_rev_rec, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq] at hNil ⊢

private theorem eo_list_rev_str_concat_cons_cons_nil_eq_of_ne_stuck
    (head mid nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hRev :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat head (mkConcat mid nil)) ≠ Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (mkConcat head (mkConcat mid nil)) =
      mkConcat mid (mkConcat head nil) := by
  rw [eo_list_rev_str_concat_cons_eq_of_ne_stuck head (mkConcat mid nil) hRev]
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil hNil
  rw [eo_get_nil_rec_cons_self_eq_of_tail_list
    (Term.UOp UserOp.str_concat) mid nil (by decide) hNilList]
  rw [eo_get_nil_rec_str_concat_eq_of_nil_true nil hNil]
  have hAcc : mkConcat head nil ≠ Term.Stuck := by
    intro h
    cases h
  rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) mid nil
    (mkConcat head nil) hAcc]
  rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true nil
    (mkConcat mid (mkConcat head nil)) hNil]

private theorem eo_list_rev_rec_cons_ne_stuck_of_ne_stuck (f x y acc : Term) :
    __eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc ≠ Term.Stuck ->
    __eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc) ≠ Term.Stuck := by
  intro h
  have hAcc : acc ≠ Term.Stuck := by
    intro hAcc
    subst acc
    simp [__eo_list_rev_rec] at h
  simpa [eo_list_rev_rec_cons f x y acc hAcc] using h

private theorem eo_list_rev_rec_acc_ne_stuck_of_ne_stuck (a acc : Term) :
    __eo_list_rev_rec a acc ≠ Term.Stuck ->
    acc ≠ Term.Stuck := by
  intro h hAcc
  subst acc
  cases a <;> simp [__eo_list_rev_rec] at h

private theorem eo_list_rev_rec_is_list_true_of_lists (f a acc : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f acc = Term.Boolean true ->
    __eo_list_rev_rec a acc ≠ Term.Stuck ->
    __eo_is_list f (__eo_list_rev_rec a acc) = Term.Boolean true := by
  induction a, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      intro hListA hListAcc hRev
      simp [__eo_list_rev_rec] at hRev
  | case2 a hA =>
      intro hListA hListAcc hRev
      simp [__eo_list_rev_rec] at hRev
  | case3 g x y acc hAcc ih =>
      intro hListA hListAcc hRev
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hListA
      subst g
      have hF : f ≠ Term.Stuck := by
        intro hF
        subst f
        simp [__eo_is_list] at hListA
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hListA
      have hNewAccList :
          __eo_is_list f (Term.Apply (Term.Apply f x) acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list f x acc hF hListAcc
      have hTailRev :
          __eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc) ≠
            Term.Stuck := by
        simpa [__eo_list_rev_rec] using hRev
      simpa [__eo_list_rev_rec] using
        ih hTailList hNewAccList hTailRev
  | case4 nil acc hNil hAcc hNot =>
      intro hListA hListAcc hRev
      simpa [__eo_list_rev_rec] using hListAcc

private theorem eo_get_nil_rec_is_list_true_of_is_list_true (f a : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f (__eo_get_nil_rec f a) = Term.Boolean true := by
  induction f, a using __eo_get_nil_rec.induct with
  | case1 a =>
      intro hList
      simp [__eo_is_list] at hList
  | case2 f hF =>
      intro hList
      simp [__eo_is_list] at hList
  | case3 f g x y hF ih =>
      intro hList
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTailList]
      exact ih hTailList
  | case4 f nil hF hNil hNot =>
      intro hList
      have hGet : __eo_get_nil_rec f nil ≠ Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true f nil hList
      have hReq :
          __eo_requires (__eo_is_list_nil f nil) (Term.Boolean true) nil ≠
            Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hGetEq :
          __eo_get_nil_rec f nil = nil := by
        simpa [__eo_get_nil_rec] using
          eo_requires_eq_result_of_ne_stuck
            (__eo_is_list_nil f nil) (Term.Boolean true) nil hReq
      rw [hGetEq]
      exact hList

private theorem eo_is_list_nil_get_nil_rec_of_is_list_true (f a : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list_nil f (__eo_get_nil_rec f a) = Term.Boolean true := by
  induction f, a using __eo_get_nil_rec.induct with
  | case1 a =>
      intro hList
      simp [__eo_is_list] at hList
  | case2 f hF =>
      intro hList
      simp [__eo_is_list] at hList
  | case3 f g x y hF ih =>
      intro hList
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      rw [eo_get_nil_rec_cons_self_eq_of_tail_list f x y hF hTailList]
      exact ih hTailList
  | case4 f nil hF hNil hNot =>
      intro hList
      have hGet : __eo_get_nil_rec f nil ≠ Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true f nil hList
      have hReq :
          __eo_requires (__eo_is_list_nil f nil) (Term.Boolean true) nil ≠
            Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hNilTrue :
          __eo_is_list_nil f nil = Term.Boolean true :=
        eo_requires_eq_of_ne_stuck (__eo_is_list_nil f nil)
          (Term.Boolean true) nil hReq
      have hGetEq :
          __eo_get_nil_rec f nil = nil := by
        simpa [__eo_get_nil_rec] using
          eo_requires_eq_result_of_ne_stuck
            (__eo_is_list_nil f nil) (Term.Boolean true) nil hReq
      rw [hGetEq]
      exact hNilTrue

private theorem eo_list_rev_result_is_list_true_of_ne_stuck (f a : Term)
    (hRev : __eo_list_rev f a ≠ Term.Stuck) :
    __eo_is_list f (__eo_list_rev f a) = Term.Boolean true := by
  have hList : __eo_is_list f a = Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck f a hRev
  have hGetList :
      __eo_is_list f (__eo_get_nil_rec f a) = Term.Boolean true :=
    eo_get_nil_rec_is_list_true_of_is_list_true f a hList
  have hRec :
      __eo_list_rev_rec a (__eo_get_nil_rec f a) ≠ Term.Stuck :=
    eo_list_rev_rec_ne_stuck_of_ne_stuck f a hRev
  rw [eo_list_rev_eq_rec_of_ne_stuck f a hRev]
  exact eo_list_rev_rec_is_list_true_of_lists f a (__eo_get_nil_rec f a)
    hList hGetList hRec

private theorem eo_list_rev_rec_ne_stuck_of_list (f a acc : Term) :
    __eo_is_list f a = Term.Boolean true ->
    acc ≠ Term.Stuck ->
    __eo_list_rev_rec a acc ≠ Term.Stuck := by
  induction a, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      intro hList hAcc
      cases f <;> simp [__eo_is_list] at hList
  | case2 a hA =>
      intro hList hAcc
      exact False.elim (hAcc rfl)
  | case3 g x y acc hAcc ih =>
      intro hList hAccNonStuck
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      have hNewAcc :
          Term.Apply (Term.Apply f x) acc ≠ Term.Stuck := by
        intro h
        cases h
      simpa [__eo_list_rev_rec] using ih hTailList hNewAcc
  | case4 nil acc hNil hAcc hNot =>
      intro hList hAccNonStuck
      simpa [__eo_list_rev_rec] using hAccNonStuck

private theorem eo_list_rev_ne_stuck_of_is_list_true (f a : Term)
    (hList : __eo_is_list f a = Term.Boolean true) :
    __eo_list_rev f a ≠ Term.Stuck := by
  have hGet : __eo_get_nil_rec f a ≠ Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true f a hList
  have hRec :
      __eo_list_rev_rec a (__eo_get_nil_rec f a) ≠ Term.Stuck :=
    eo_list_rev_rec_ne_stuck_of_list f a (__eo_get_nil_rec f a) hList hGet
  rw [__eo_list_rev, hList]
  rw [eo_requires_self_eq_of_ne_stuck (Term.Boolean true)
    (__eo_list_rev_rec a (__eo_get_nil_rec f a)) (by decide)]
  exact hRec

set_option linter.unusedSimpArgs false in
private theorem eo_list_concat_rec_str_concat_nil_eq_of_nil_true
    (nil z : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true) :
    __eo_list_concat_rec nil z = z := by
  cases nil <;>
    simp [__eo_list_concat_rec, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __eo_eq, native_teq] at hNil ⊢
  case String s =>
    subst s
    cases z <;> rfl
  case seq_empty A =>
    cases z <;> rfl

private theorem eo_list_concat_rec_cons_eq_of_tail_ne_stuck
    (f head tail z : Term)
    (hTail : __eo_list_concat_rec tail z ≠ Term.Stuck) :
    __eo_list_concat_rec (Term.Apply (Term.Apply f head) tail) z =
      Term.Apply (Term.Apply f head) (__eo_list_concat_rec tail z) := by
  have hLeft :
      __eo_list_concat_rec (Term.Apply (Term.Apply f head) tail) z =
        __eo_mk_apply (Term.Apply f head) (__eo_list_concat_rec tail z) := by
    cases z <;> try rfl
    case Stuck =>
      cases tail <;> simp [__eo_list_concat_rec] at hTail
  rw [hLeft]
  cases hRec : __eo_list_concat_rec tail z <;>
    simp [__eo_mk_apply, hRec] at hTail ⊢

private theorem eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
    (head tail z : Term)
    (hTail : __eo_list_concat_rec tail z ≠ Term.Stuck) :
    __eo_list_concat_rec (mkConcat head tail) z =
      mkConcat head (__eo_list_concat_rec tail z) := by
  exact eo_list_concat_rec_cons_eq_of_tail_ne_stuck
    (Term.UOp UserOp.str_concat) head tail z hTail

private theorem eo_list_concat_rec_ne_stuck_of_list (f a z : Term) :
    __eo_is_list f a = Term.Boolean true ->
    z ≠ Term.Stuck ->
    __eo_list_concat_rec a z ≠ Term.Stuck := by
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro hList hZ
      cases f <;> simp [__eo_is_list] at hList
  | case2 a hA =>
      intro hList hZ
      exact False.elim (hZ rfl)
  | case3 g x y z hZ ih =>
      intro hList hZNonStuck
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        ih hTailList hZNonStuck
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck f x y z hTailConcat]
      intro h
      cases h
  | case4 nil z hNil hZ hNot =>
      intro hList hZNonStuck
      simpa [__eo_list_concat_rec] using hZNonStuck

private theorem eo_list_concat_rec_is_list_true_of_lists (f a z : Term) :
    __eo_is_list f a = Term.Boolean true ->
    __eo_is_list f z = Term.Boolean true ->
    __eo_is_list f (__eo_list_concat_rec a z) = Term.Boolean true := by
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro hListA hListZ
      cases f <;> simp [__eo_is_list] at hListA
  | case2 a hA =>
      intro hListA hListZ
      cases f <;> simp [__eo_is_list] at hListZ
  | case3 g x y z hZ ih =>
      intro hListA hListZ
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hListA
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hListA
      have hZNonStuck : z ≠ Term.Stuck := by
        intro hz
        subst z
        cases f <;> simp [__eo_is_list] at hListZ
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list f y z hTailList hZNonStuck
      rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck f x y z hTailConcat]
      exact eo_is_list_cons_self_true_of_tail_list f x
        (__eo_list_concat_rec y z)
        (by
          intro hF
          subst f
          simp [__eo_is_list] at hListA)
        (ih hTailList hListZ)
  | case4 nil z hNil hZ hNot =>
      intro hListA hListZ
      simpa [__eo_list_concat_rec] using hListZ

private theorem smt_typeof_list_concat_rec_str_concat_of_seq_aux
    (f a z : Term) :
    f = Term.UOp UserOp.str_concat ->
    ∀ T : SmtType,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt z) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
        SmtType.Seq T := by
  intro hf
  induction a, z using __eo_list_concat_rec.induct with
  | case1 z =>
      intro T hList haTy hzTy
      subst f
      simp [__eo_is_list] at hList
  | case2 a hA =>
      intro T hList haTy hzTy
      change __smtx_typeof SmtTerm.None = SmtType.Seq T at hzTy
      rw [TranslationProofs.smtx_typeof_none] at hzTy
      cases hzTy
  | case3 g x y z hZ ih =>
      intro T hList haTy hzTy
      subst f
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hList
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [haTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with
        ⟨U, hxTy, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTy hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, haTy]
        injection hSeq
      have hxTyT : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        simpa [hUT] using hxTy
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hZNonStuck : z ≠ Term.Stuck := by
        intro hz
        subst z
        change __smtx_typeof SmtTerm.None = SmtType.Seq T at hzTy
        rw [TranslationProofs.smtx_typeof_none] at hzTy
        cases hzTy
      have hTailConcat :
          __eo_list_concat_rec y z ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.str_concat)
          y z hTailList hZNonStuck
      have hTailTy :
          __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y z)) =
            SmtType.Seq T :=
        ih T hTailList hyTy hzTy
      rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck x y z
        hTailConcat]
      exact smt_typeof_str_concat_of_seq x (__eo_list_concat_rec y z) T
        hxTyT hTailTy
  | case4 nil z hNil hZ hNot =>
      intro T hList haTy hzTy
      simpa [__eo_list_concat_rec] using hzTy

private theorem smt_typeof_list_concat_rec_str_concat_of_seq
    (a z : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__eo_list_concat_rec a z)) =
      SmtType.Seq T :=
  smt_typeof_list_concat_rec_str_concat_of_seq_aux
    (Term.UOp UserOp.str_concat) a z rfl T hList haTy hzTy

private theorem eo_list_rev_rec_list_concat_rec_singleton_eq
    (tail acc head nil : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc = Term.Boolean true) :
    __eo_list_rev_rec tail
        (__eo_list_concat_rec acc (mkConcat head nil)) =
      __eo_list_concat_rec (__eo_list_rev_rec tail acc)
        (mkConcat head nil) := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hTailList
      have hAccNonStuck : acc ≠ Term.Stuck := by
        intro h
        subst acc
        simp [__eo_is_list] at hAccList
      have hSingletonNonStuck : mkConcat head nil ≠ Term.Stuck := by
        intro h
        cases h
      have hAccSnocNonStuck :
          __eo_list_concat_rec acc (mkConcat head nil) ≠ Term.Stuck :=
        eo_list_concat_rec_ne_stuck_of_list
          (Term.UOp UserOp.str_concat) acc (mkConcat head nil)
          hAccList hSingletonNonStuck
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat x acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.str_concat) x acc (by decide) hAccList
      have hConsAccSnoc :
          mkConcat x (__eo_list_concat_rec acc (mkConcat head nil)) =
            __eo_list_concat_rec (mkConcat x acc) (mkConcat head nil) := by
        exact (eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
          x acc (mkConcat head nil) hAccSnocNonStuck).symm
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) x y
        (__eo_list_concat_rec acc (mkConcat head nil)) hAccSnocNonStuck]
      change __eo_list_rev_rec y
          (mkConcat x (__eo_list_concat_rec acc (mkConcat head nil))) =
        __eo_list_concat_rec
          (__eo_list_rev_rec (mkConcat x y) acc) (mkConcat head nil)
      rw [hConsAccSnoc]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) x y acc
        hAccNonStuck]
      exact ih hTailTailList hConsAccList
  | case4 tail acc hTail hAcc hNot =>
      have hGet : __eo_get_nil_rec (Term.UOp UserOp.str_concat) tail ≠
          Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) tail hTailList
      have hReq :
          __eo_requires
              (__eo_is_list_nil (Term.UOp UserOp.str_concat) tail)
              (Term.Boolean true) tail ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hTailNil :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) tail =
            Term.Boolean true :=
        eo_requires_eq_of_ne_stuck
          (__eo_is_list_nil (Term.UOp UserOp.str_concat) tail)
          (Term.Boolean true) tail hReq
      rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true tail
        (__eo_list_concat_rec acc (mkConcat head nil)) hTailNil]
      rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true tail acc hTailNil]

private theorem eo_get_nil_rec_list_rev_rec_eq
    (tail acc : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc = Term.Boolean true) :
    __eo_get_nil_rec (Term.UOp UserOp.str_concat)
        (__eo_list_rev_rec tail acc) =
      __eo_get_nil_rec (Term.UOp UserOp.str_concat) acc := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hTailList
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat x acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.str_concat) x acc (by decide) hAccList
      simpa [__eo_list_rev_rec] using ih hTailTailList hConsAccList
  | case4 nil acc hNil hAcc hNot =>
      simpa [__eo_list_rev_rec]

private theorem eo_list_rev_rec_rev_rec_get_nil_eq
    (tail acc : Term)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hAccList :
      __eo_is_list (Term.UOp UserOp.str_concat) acc = Term.Boolean true) :
    __eo_list_rev_rec (__eo_list_rev_rec tail acc)
        (__eo_get_nil_rec (Term.UOp UserOp.str_concat) tail) =
      __eo_list_rev_rec acc tail := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      simp [__eo_is_list] at hAccList
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hTailList
      have hAccNonStuck : acc ≠ Term.Stuck := by
        intro h
        subst acc
        simp [__eo_is_list] at hAccList
      have hTailNonStuck : y ≠ Term.Stuck := by
        intro h
        subst y
        simp [__eo_is_list] at hTailTailList
      have hConsAccList :
          __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat x acc) =
            Term.Boolean true :=
        eo_is_list_cons_self_true_of_tail_list
          (Term.UOp UserOp.str_concat) x acc (by decide) hAccList
      have hGetEq :
          __eo_get_nil_rec (Term.UOp UserOp.str_concat)
              (mkConcat x y) =
            __eo_get_nil_rec (Term.UOp UserOp.str_concat) y :=
        eo_get_nil_rec_cons_self_eq_of_tail_list
          (Term.UOp UserOp.str_concat) x y (by decide) hTailTailList
      rw [hGetEq]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) x y acc
        hAccNonStuck]
      rw [ih hTailTailList hConsAccList]
      rw [eo_list_rev_rec_cons (Term.UOp UserOp.str_concat) x acc y
        hTailNonStuck]
  | case4 nil acc hNil hAcc hNot =>
      have hGet : __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil ≠
          Term.Stuck :=
        eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) nil hTailList
      have hReq :
          __eo_requires
              (__eo_is_list_nil (Term.UOp UserOp.str_concat) nil)
              (Term.Boolean true) nil ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hNilTrue :
          __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
            Term.Boolean true :=
        eo_requires_eq_of_ne_stuck
          (__eo_is_list_nil (Term.UOp UserOp.str_concat) nil)
          (Term.Boolean true) nil hReq
      have hGetEq :
          __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil = nil :=
        eo_get_nil_rec_str_concat_eq_of_nil_true nil hNilTrue
      rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true nil acc hNilTrue]
      rw [hGetEq]

private theorem eo_list_rev_list_rev_str_concat_eq_of_list_true
    (a : Term)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) a) = a := by
  let nil := __eo_get_nil_rec (Term.UOp UserOp.str_concat) a
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true := by
    simpa [nil] using
      eo_get_nil_rec_is_list_true_of_is_list_true
        (Term.UOp UserOp.str_concat) a hList
  have hNilNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true := by
    simpa [nil] using
      eo_is_list_nil_get_nil_rec_of_is_list_true
        (Term.UOp UserOp.str_concat) a hList
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) a =
        __eo_list_rev_rec a nil := by
    simpa [nil] using
      eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.str_concat) a hRev
  have hRevRecNonStuck :
      __eo_list_rev_rec a nil ≠ Term.Stuck := by
    simpa [hRevEq] using hRev
  have hRevRecList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_rev_rec a nil) = Term.Boolean true :=
    eo_list_rev_rec_is_list_true_of_lists (Term.UOp UserOp.str_concat)
      a nil hList hNilList hRevRecNonStuck
  have hRevRev :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) ≠ Term.Stuck := by
    rw [hRevEq]
    exact eo_list_rev_ne_stuck_of_is_list_true
      (Term.UOp UserOp.str_concat) (__eo_list_rev_rec a nil) hRevRecList
  have hGetRev :
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) = nil := by
    rw [hRevEq]
    calc
      __eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (__eo_list_rev_rec a nil) =
        __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil := by
          exact eo_get_nil_rec_list_rev_rec_eq a nil hList hNilList
      _ = nil :=
        eo_get_nil_rec_str_concat_eq_of_nil_true nil hNilNil
  have hRevRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) =
        __eo_list_rev_rec (__eo_list_rev (Term.UOp UserOp.str_concat) a)
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a)) :=
    eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) a) hRevRev
  rw [hRevRevEq, hGetRev, hRevEq]
  rw [eo_list_rev_rec_rev_rec_get_nil_eq a nil hList hNilList]
  rw [eo_list_rev_rec_str_concat_nil_eq_of_nil_true nil a hNilNil]

private theorem smt_typeof_get_nil_rec_str_concat_of_seq_aux (f a : Term) :
    f = Term.UOp UserOp.str_concat ->
    ∀ T : SmtType,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __eo_get_nil_rec f a ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__eo_get_nil_rec f a)) = SmtType.Seq T := by
  intro hf
  induction f, a using __eo_get_nil_rec.induct with
  | case1 a =>
      intro T hList haTy hGet
      cases hf
  | case2 f hF =>
      intro T hList haTy hGet
      simp [__eo_get_nil_rec] at hGet
  | case3 f g x y hF ih =>
      intro T hList haTy hGet
      have hg : g = f :=
        eo_is_list_cons_head_eq_of_true f g x y hList
      subst g
      have hTailList : __eo_is_list f y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self f x y hList
      have hReq :
          __eo_requires f f (__eo_get_nil_rec f y) ≠ Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      have hTailGet : __eo_get_nil_rec f y ≠ Term.Stuck :=
        eo_requires_result_ne_stuck_of_ne_stuck f f (__eo_get_nil_rec f y) hReq
      subst f
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [haTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with ⟨U, hxTy, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTy hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, haTy]
        injection hSeq
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hIH := ih rfl T hTailList hyTy hTailGet
      simpa [__eo_get_nil_rec,
        eo_requires_eq_result_of_ne_stuck (Term.UOp UserOp.str_concat)
          (Term.UOp UserOp.str_concat)
          (__eo_get_nil_rec (Term.UOp UserOp.str_concat) y) hReq] using hIH
  | case4 f nil hF hNil hNot =>
      intro T hList haTy hGet
      have hReq :
          __eo_requires (__eo_is_list_nil f nil) (Term.Boolean true) nil ≠
            Term.Stuck := by
        simpa [__eo_get_nil_rec] using hGet
      simpa [__eo_get_nil_rec,
        eo_requires_eq_result_of_ne_stuck
          (__eo_is_list_nil f nil) (Term.Boolean true) nil hReq] using haTy

private theorem smt_typeof_get_nil_rec_str_concat_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hGet :
      __eo_get_nil_rec (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a)) =
      SmtType.Seq T :=
  smt_typeof_get_nil_rec_str_concat_of_seq_aux
    (Term.UOp UserOp.str_concat) a rfl T hList haTy hGet

private theorem smt_typeof_list_rev_eq_rec_of_ne_stuck (f a : Term)
    (hRev : __eo_list_rev f a ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_list_rev f a)) =
      __smtx_typeof
        (__eo_to_smt (__eo_list_rev_rec a (__eo_get_nil_rec f a))) := by
  rw [eo_list_rev_eq_rec_of_ne_stuck f a hRev]

private theorem smt_typeof_list_rev_rec_cons_eq
    (f x y acc : Term) (hAcc : acc ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_rev_rec (Term.Apply (Term.Apply f x) y) acc)) =
      __smtx_typeof
        (__eo_to_smt (__eo_list_rev_rec y (Term.Apply (Term.Apply f x) acc))) := by
  rw [eo_list_rev_rec_cons f x y acc hAcc]

private theorem smt_typeof_list_rev_rec_str_concat_of_seq_aux
    (f a acc : Term) :
    f = Term.UOp UserOp.str_concat ->
    ∀ T : SmtType,
      __eo_is_list f a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T ->
      __eo_list_rev_rec a acc ≠ Term.Stuck ->
      __smtx_typeof (__eo_to_smt (__eo_list_rev_rec a acc)) =
        SmtType.Seq T := by
  intro hf
  induction a, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      intro T hList haTy hAccTy hRev
      simp [__eo_list_rev_rec] at hRev
  | case2 a hA =>
      intro T hList haTy hAccTy hRev
      simp [__eo_list_rev_rec] at hRev
  | case3 g x y acc hAcc ih =>
      intro T hList haTy hAccTy hRev
      subst f
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hList
      subst g
      have hTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) x y
          hList
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [haTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with
        ⟨U, hxTy, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTy hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, haTy]
        injection hSeq
      have hxTyT : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        simpa [hUT] using hxTy
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hNewAccTy :
          __smtx_typeof (__eo_to_smt (mkConcat x acc)) = SmtType.Seq T :=
        smt_typeof_str_concat_of_seq x acc T hxTyT hAccTy
      have hTailRev :
          __eo_list_rev_rec y (mkConcat x acc) ≠ Term.Stuck := by
        simpa [__eo_list_rev_rec] using hRev
      have hIH := ih T hTailList hyTy hNewAccTy hTailRev
      simpa [__eo_list_rev_rec] using hIH
  | case4 nil acc hNil hAcc hNot =>
      intro T hList haTy hAccTy hRev
      simpa [__eo_list_rev_rec] using hAccTy

private theorem smt_typeof_list_rev_rec_str_concat_of_seq
    (a acc : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T)
    (hRev : __eo_list_rev_rec a acc ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__eo_list_rev_rec a acc)) = SmtType.Seq T :=
  smt_typeof_list_rev_rec_str_concat_of_seq_aux
    (Term.UOp UserOp.str_concat) a acc rfl T hList haTy hAccTy hRev

private theorem smt_typeof_list_rev_str_concat_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.str_concat) a)) =
      SmtType.Seq T := by
  have hGet : __eo_get_nil_rec (Term.UOp UserOp.str_concat) a ≠
      Term.Stuck :=
    eo_get_nil_rec_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat) a
      hList
  have hGetTy :
      __smtx_typeof
          (__eo_to_smt (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a)) =
        SmtType.Seq T :=
    smt_typeof_get_nil_rec_str_concat_of_seq a T hList haTy hGet
  have hRec :
      __eo_list_rev_rec a (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a) ≠
        Term.Stuck :=
    eo_list_rev_rec_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat) a hRev
  rw [smt_typeof_list_rev_eq_rec_of_ne_stuck
    (Term.UOp UserOp.str_concat) a hRev]
  exact smt_typeof_list_rev_rec_str_concat_of_seq a
    (__eo_get_nil_rec (Term.UOp UserOp.str_concat) a) T hList haTy hGetTy hRec

private theorem eo_list_rev_list_rev_ne_stuck_of_ne_stuck (f a : Term)
    (hRev : __eo_list_rev f a ≠ Term.Stuck) :
    __eo_list_rev f (__eo_list_rev f a) ≠ Term.Stuck := by
  exact eo_list_rev_ne_stuck_of_is_list_true f (__eo_list_rev f a)
    (eo_list_rev_result_is_list_true_of_ne_stuck f a hRev)

private theorem smt_typeof_list_rev_list_rev_str_concat_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a))) =
      SmtType.Seq T := by
  have hRevTy :
      __smtx_typeof
          (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.str_concat) a)) =
        SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq a T hList haTy hRev
  have hRevList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) =
        Term.Boolean true :=
    eo_list_rev_result_is_list_true_of_ne_stuck
      (Term.UOp UserOp.str_concat) a hRev
  have hRevRev :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__eo_list_rev (Term.UOp UserOp.str_concat) a) ≠
        Term.Stuck :=
    eo_list_rev_list_rev_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.str_concat) a hRev
  exact smt_typeof_list_rev_str_concat_of_seq
    (__eo_list_rev (Term.UOp UserOp.str_concat) a) T hRevList hRevTy
    hRevRev

private theorem eo_mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem eo_mk_apply_fun_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    f ≠ Term.Stuck := by
  intro hf
  subst f
  simp [__eo_mk_apply] at h

private theorem eo_mk_apply_arg_ne_stuck_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

private theorem eo_ite_then_ne_stuck_of_ne_stuck (c x y : Term)
    (h : __eo_ite c x y ≠ Term.Stuck)
    (hc : c = Term.Boolean true) :
    x ≠ Term.Stuck := by
  subst c
  simpa [eo_ite_true] using h

private theorem eo_ite_else_ne_stuck_of_ne_stuck (c x y : Term)
    (h : __eo_ite c x y ≠ Term.Stuck)
    (hc : c = Term.Boolean false) :
    y ≠ Term.Stuck := by
  subst c
  simpa [eo_ite_false] using h

private theorem str_nary_intro_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_nary_intro x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_nary_intro] at h

private theorem str_nary_elim_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __str_nary_elim x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_nary_elim] at h

private theorem term_ne_stuck_of_smt_type_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hxTy
  rw [TranslationProofs.smtx_typeof_none] at hxTy
  cases hxTy

private theorem seq_empty_ne_stuck_of_ne_stuck (A : Term)
    (hA : A ≠ Term.Stuck) :
    __seq_empty A ≠ Term.Stuck := by
  cases A with
  | Stuck =>
      exact False.elim (hA rfl)
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__seq_empty]
          case Seq =>
            cases x with
            | UOp op' =>
                cases op' <;> simp
            | _ =>
                simp
      | _ =>
          simp [__seq_empty]
  | _ =>
      simp [__seq_empty]

private theorem seq_empty_typeof_ne_stuck_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __seq_empty (__eo_typeof x) ≠ Term.Stuck := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  have hTypeNonStuck : __eo_typeof x ≠ Term.Stuck := by
    intro hType
    rw [hType] at hA
    simp [__eo_to_smt_type] at hA
  exact seq_empty_ne_stuck_of_ne_stuck (__eo_typeof x) hTypeNonStuck

private theorem eo_eq_seq_empty_typeof_ne_stuck_of_smt_type_seq
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    ∃ b, __eo_eq y (__seq_empty (__eo_typeof x)) = Term.Boolean b := by
  have hyNonStuck : y ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq y T hyTy
  have hEmptyNonStuck :
      __seq_empty (__eo_typeof x) ≠ Term.Stuck :=
    seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy
  cases y <;> simp [__eo_eq] at hyNonStuck ⊢
  all_goals
    cases hEmpty : __seq_empty (__eo_typeof x) <;>
      simp [__eo_eq, hEmpty] at hEmptyNonStuck ⊢

private theorem str_nary_elim_str_concat_cons_ne_stuck_of_seq
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T) :
    __str_nary_elim (mkConcat x y) ≠ Term.Stuck := by
  have hxNonStuck : x ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq x T hxTy
  rcases eo_eq_seq_empty_typeof_ne_stuck_of_smt_type_seq x y T hxTy hyTy with
    ⟨b, hb⟩
  rw [show __str_nary_elim (mkConcat x y) =
      __eo_ite (__eo_eq y (__seq_empty (__eo_typeof x))) x
        (mkConcat x y) by
    rfl]
  rw [hb]
  cases b
  · rw [eo_ite_false]
    intro h
    cases h
  · rw [eo_ite_true]
    exact hxNonStuck

private theorem str_nary_elim_str_nary_intro_default_ne_stuck_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElimDefault :
      __str_nary_elim x =
        __eo_requires x (__seq_empty (__eo_typeof x)) x)
    (hIntroNN :
      __smtx_typeof
          (__eo_to_smt
            (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
              (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
                (__seq_empty (__eo_typeof x))))) ≠ SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __str_nary_elim
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x)))) ≠ Term.Stuck := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · have hxNonStuck : x ≠ Term.Stuck :=
      term_ne_stuck_of_smt_type_seq x T hxTy
    have hEmptyEq : __seq_empty (__eo_typeof x) = x :=
      eq_of_eo_eq_true_local x (__seq_empty (__eo_typeof x)) hCond
    rw [hCond, eo_ite_true]
    rw [hElimDefault, hEmptyEq]
    rw [eo_requires_self_eq_of_ne_stuck x x hxNonStuck]
    exact hxNonStuck
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    have hConcatNN :
        __smtx_typeof
            (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))) ≠
          SmtType.None := by
      simpa [hCond, eo_ite_false, hApplyEq] using hIntroNN
    rcases str_concat_args_of_non_none x (__seq_empty (__eo_typeof x))
        hConcatNN with ⟨U, hxTyU, hEmptyTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hxTyU, hxTy]
      injection hSeq
    have hEmptyTy :
        __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
          SmtType.Seq T := by
      simpa [hUT] using hEmptyTyU
    rw [hCond, eo_ite_false, hApplyEq]
    exact str_nary_elim_str_concat_cons_ne_stuck_of_seq x
      (__seq_empty (__eo_typeof x)) T hxTy hEmptyTy

private theorem str_nary_elim_list_rev_rec_ne_stuck_of_seq
    (tail acc : Term) (T : SmtType)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T)
    (hAccElim : __str_nary_elim acc ≠ Term.Stuck)
    (hRev : __eo_list_rev_rec tail acc ≠ Term.Stuck) :
    __str_nary_elim (__eo_list_rev_rec tail acc) ≠ Term.Stuck := by
  induction tail, acc using __eo_list_rev_rec.induct with
  | case1 acc =>
      simp [__eo_is_list] at hTailList
  | case2 tail hTail =>
      change __smtx_typeof SmtTerm.None = SmtType.Seq T at hAccTy
      rw [TranslationProofs.smtx_typeof_none] at hAccTy
      cases hAccTy
  | case3 g x y acc hAcc ih =>
      have hg : g = Term.UOp UserOp.str_concat :=
        eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat) g x y
          hTailList
      subst g
      have hTailTailList :
          __eo_is_list (Term.UOp UserOp.str_concat) y =
            Term.Boolean true :=
        eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
          x y hTailList
      have hConcatNN :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
        rw [hTailTy]
        exact seq_ne_none T
      rcases str_concat_args_of_non_none x y hConcatNN with
        ⟨U, hxTyU, hyTyU⟩
      have hConcatTyU :
          __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
        smt_typeof_str_concat_of_seq x y U hxTyU hyTyU
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hConcatTyU, hTailTy]
        injection hSeq
      have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        simpa [hUT] using hxTyU
      have hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
        simpa [hUT] using hyTyU
      have hNewAccTy :
          __smtx_typeof (__eo_to_smt (mkConcat x acc)) = SmtType.Seq T :=
        smt_typeof_str_concat_of_seq x acc T hxTy hAccTy
      have hNewAccElim :
          __str_nary_elim (mkConcat x acc) ≠ Term.Stuck :=
        str_nary_elim_str_concat_cons_ne_stuck_of_seq x acc T hxTy
          hAccTy
      have hTailRev :
          __eo_list_rev_rec y (mkConcat x acc) ≠ Term.Stuck := by
        simpa [__eo_list_rev_rec] using hRev
      simpa [__eo_list_rev_rec] using
        ih hTailTailList hyTy hNewAccTy hNewAccElim hTailRev
  | case4 nil acc hNil hAcc hNot =>
      simpa [__eo_list_rev_rec] using hAccElim

private theorem str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq
    (head tail : Term) (T : SmtType)
    (hConsTy : __smtx_typeof (__eo_to_smt (mkConcat head tail)) =
      SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
        Term.Stuck) :
    __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat head tail)) ≠ Term.Stuck := by
  rcases str_concat_args_of_seq_type head tail T hConsTy with
    ⟨hHeadTy, hTailTy⟩
  have hConsList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (mkConcat head tail) hRevCons
  have hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true :=
    eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat) head
      tail hConsList
  let nil := __eo_get_nil_rec (Term.UOp UserOp.str_concat) tail
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_get_nil_rec_str_concat_of_seq tail T hTailList hTailTy
        (eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) tail hTailList)
  have hAccTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hAccElim : __str_nary_elim (mkConcat head nil) ≠ Term.Stuck :=
    str_nary_elim_str_concat_cons_ne_stuck_of_seq head nil T hHeadTy
      hNilTy
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        __eo_list_rev_rec tail (mkConcat head nil) := by
    simpa [nil] using
      eo_list_rev_str_concat_cons_eq_of_ne_stuck head tail hRevCons
  have hRevRec :
      __eo_list_rev_rec tail (mkConcat head nil) ≠ Term.Stuck := by
    simpa [hRevEq] using hRevCons
  simpa [hRevEq, nil] using
    str_nary_elim_list_rev_rec_ne_stuck_of_seq tail (mkConcat head nil)
      T hTailList hTailTy hAccTy hAccElim hRevRec

private theorem str_nary_elim_str_nary_intro_ne_stuck_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck := by
  cases x with
  | Stuck =>
      simp [__str_nary_intro] at hIntro
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                rcases str_concat_args_of_seq_type t a T hxTy with
                  ⟨htTy, haTy⟩
                simpa [__str_nary_intro] using
                  str_nary_elim_str_concat_cons_ne_stuck_of_seq t a T
                    htTy haTy
              · change __str_nary_elim (__str_nary_intro
                    (Term.Apply (Term.Apply (Term.UOp op) t) a)) ≠
                    Term.Stuck
                simp [__str_nary_intro, hop] at hIntroNN hIntro ⊢
                exact str_nary_elim_str_nary_intro_default_ne_stuck_of_seq
                  (Term.Apply (Term.Apply (Term.UOp op) t) a) T hxTy
                  (by simp [__str_nary_elim, hop]) hIntroNN hIntro
          | _ =>
              simp [__str_nary_intro] at hIntroNN hIntro ⊢
              exact str_nary_elim_str_nary_intro_default_ne_stuck_of_seq
                _ T hxTy (by simp [__str_nary_elim]) hIntroNN hIntro
      | _ =>
          simp [__str_nary_intro] at hIntroNN hIntro ⊢
          exact str_nary_elim_str_nary_intro_default_ne_stuck_of_seq
            _ T hxTy (by simp [__str_nary_elim]) hIntroNN hIntro
  | _ =>
      simp [__str_nary_intro] at hIntroNN hIntro ⊢
      exact str_nary_elim_str_nary_intro_default_ne_stuck_of_seq
        _ T hxTy (by simp [__str_nary_elim]) hIntroNN hIntro

private theorem pair_first_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __pair_first x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__pair_first] at h

private theorem pair_second_arg_ne_stuck_of_ne_stuck (x : Term)
    (h : __pair_second x ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__pair_second] at h

private theorem str_strip_prefix_left_ne_stuck_of_ne_stuck (x y : Term)
    (h : __str_strip_prefix x y ≠ Term.Stuck) :
    x ≠ Term.Stuck := by
  intro hx
  subst x
  simp [__str_strip_prefix] at h

private theorem str_strip_prefix_right_ne_stuck_of_ne_stuck (x y : Term)
    (h : __str_strip_prefix x y ≠ Term.Stuck) :
    y ≠ Term.Stuck := by
  intro hy
  subst y
  cases x <;> simp [__str_strip_prefix] at h

private theorem eo_prog_concat_eq_eq_of_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) =
      mkEq (concatEqLhs rev s t) (concatEqRhs rev s t) := by
  have hRev : rev ≠ Term.Stuck := by
    intro h
    subst rev
    simp [__eo_prog_concat_eq] at hProg
  have hProg' :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
          (concatEqRhs rev s t) ≠ Term.Stuck := by
    cases rev <;>
      simp [__eo_prog_concat_eq, concatEqLhs, concatEqRhs, concatEqStrip,
        concatEqNormalize] at hRev hProg ⊢
    all_goals first | exact hProg | contradiction
  have hInner :
      __eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) ≠
        Term.Stuck := by
    exact eo_mk_apply_fun_ne_stuck_of_ne_stuck
        (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
        (concatEqRhs rev s t) hProg'
  have hInnerEq :
      __eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) =
        Term.Apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp UserOp.eq)
      (concatEqLhs rev s t) hInner
  have hOuterEq :
      __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) =
        Term.Apply (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
          (concatEqRhs rev s t) := by
    cases rev <;>
      simp [__eo_prog_concat_eq, concatEqLhs, concatEqRhs, concatEqStrip,
        concatEqNormalize] at hRev hProg' ⊢
    all_goals first
      | exact eo_mk_apply_eq_apply_of_ne_stuck _ _ hProg'
      | contradiction
  rw [hOuterEq, hInnerEq]

private theorem eo_prog_concat_eq_mk_apply_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
      (concatEqRhs rev s t) ≠ Term.Stuck := by
  have hRev : rev ≠ Term.Stuck := by
    intro h
    subst rev
    simp [__eo_prog_concat_eq] at hProg
  cases rev <;>
    simp [__eo_prog_concat_eq, concatEqLhs, concatEqRhs, concatEqStrip,
      concatEqNormalize] at hRev hProg ⊢
  all_goals first | exact hProg | contradiction

private theorem concatEqLhs_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqLhs rev s t ≠ Term.Stuck := by
  have hApply := eo_prog_concat_eq_mk_apply_ne_stuck rev s t hProg
  have hInner :
      __eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t) ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck
      (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
      (concatEqRhs rev s t) hApply
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.eq)
    (concatEqLhs rev s t) hInner

private theorem concatEqRhs_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqRhs rev s t ≠ Term.Stuck := by
  have hApply := eo_prog_concat_eq_mk_apply_ne_stuck rev s t hProg
  exact eo_mk_apply_arg_ne_stuck_of_ne_stuck
    (__eo_mk_apply (Term.UOp UserOp.eq) (concatEqLhs rev s t))
    (concatEqRhs rev s t) hApply

private theorem concatEq_rev_cases_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    rev = Term.Boolean true ∨ rev = Term.Boolean false := by
  have hLhs := concatEqLhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  have hNorm :
      concatEqNormalize rev (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
    str_nary_elim_arg_ne_stuck_of_ne_stuck
      (concatEqNormalize rev (__pair_first (concatEqStrip rev s t))) hLhs
  exact eo_ite_cases_of_ne_stuck rev
    (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first (concatEqStrip rev s t)))
    (__pair_first (concatEqStrip rev s t)) hNorm

private theorem concatEqStrip_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqStrip rev s t ≠ Term.Stuck := by
  have hLhs := concatEqLhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  have hNorm :
      concatEqNormalize rev (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
    str_nary_elim_arg_ne_stuck_of_ne_stuck
      (concatEqNormalize rev (__pair_first (concatEqStrip rev s t))) hLhs
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevFirst :
        __eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first (concatEqStrip rev s t)))
        (__pair_first (concatEqStrip rev s t)) hNorm hRev
    have hFirst : __pair_first (concatEqStrip rev s t) ≠ Term.Stuck :=
      eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip rev s t)) hRevFirst
    exact pair_first_arg_ne_stuck_of_ne_stuck (concatEqStrip rev s t) hFirst
  · have hFirst : __pair_first (concatEqStrip rev s t) ≠ Term.Stuck :=
      eo_ite_else_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first (concatEqStrip rev s t)))
        (__pair_first (concatEqStrip rev s t)) hNorm hRev
    exact pair_first_arg_ne_stuck_of_ne_stuck (concatEqStrip rev s t) hFirst

private theorem concatEqNormalize_first_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__pair_first (concatEqStrip rev s t)) ≠
      Term.Stuck := by
  have hLhs := concatEqLhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_nary_elim_arg_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__pair_first (concatEqStrip rev s t))) hLhs

private theorem concatEqNormalize_second_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__pair_second (concatEqStrip rev s t)) ≠
      Term.Stuck := by
  have hRhs := concatEqRhs_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_nary_elim_arg_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__pair_second (concatEqStrip rev s t))) hRhs

private theorem concatEqStrip_first_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __pair_first (concatEqStrip rev s t) ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_first_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevFirst :
        __eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first (concatEqStrip rev s t)) ≠ Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first (concatEqStrip rev s t)))
        (__pair_first (concatEqStrip rev s t)) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_first (concatEqStrip rev s t)) hRevFirst
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip rev s t)))
      (__pair_first (concatEqStrip rev s t)) hNorm hRev

private theorem concatEqStrip_second_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __pair_second (concatEqStrip rev s t) ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_second_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevSecond :
        __eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_second (concatEqStrip rev s t)) ≠ Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_second (concatEqStrip rev s t)))
        (__pair_second (concatEqStrip rev s t)) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_second (concatEqStrip rev s t)) hRevSecond
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_second (concatEqStrip rev s t)))
      (__pair_second (concatEqStrip rev s t)) hNorm hRev

private theorem concatEqNormalize_left_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__str_nary_intro s) ≠ Term.Stuck := by
  have hStrip := concatEqStrip_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_strip_prefix_left_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__str_nary_intro s))
    (concatEqNormalize rev (__str_nary_intro t)) hStrip

private theorem concatEqNormalize_right_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    concatEqNormalize rev (__str_nary_intro t) ≠ Term.Stuck := by
  have hStrip := concatEqStrip_ne_stuck_of_prog_ne_stuck rev s t hProg
  exact str_strip_prefix_right_ne_stuck_of_ne_stuck
    (concatEqNormalize rev (__str_nary_intro s))
    (concatEqNormalize rev (__str_nary_intro t)) hStrip

private theorem str_nary_intro_left_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __str_nary_intro s ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_left_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevIntro :
        __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
          Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__str_nary_intro s) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevIntro
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
      (__str_nary_intro s) hNorm hRev

private theorem str_nary_intro_right_ne_stuck_of_prog_ne_stuck (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck) :
    __str_nary_intro t ≠ Term.Stuck := by
  have hNorm := concatEqNormalize_right_ne_stuck_of_prog_ne_stuck rev s t hProg
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · have hRevIntro :
        __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
          Term.Stuck :=
      eo_ite_then_ne_stuck_of_ne_stuck rev
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
        (__str_nary_intro t) hNorm hRev
    exact eo_list_rev_arg_ne_stuck_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevIntro
  · exact eo_ite_else_ne_stuck_of_ne_stuck rev
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))
      (__str_nary_intro t) hNorm hRev

private theorem eo_prog_concat_eq_premise_eq_shape_of_ne_stuck (rev x1 : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf x1) ≠ Term.Stuck) :
    ∃ s t, x1 = mkEq s t := by
  cases x1 with
  | Apply f t =>
      cases f with
      | Apply g s =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  exact ⟨s, t, rfl⟩
              | _ =>
                  cases rev <;> simp [__eo_prog_concat_eq] at hProg
          | _ =>
              cases rev <;> simp [__eo_prog_concat_eq] at hProg
      | _ =>
          cases rev <;> simp [__eo_prog_concat_eq] at hProg
  | _ =>
      cases rev <;> simp [__eo_prog_concat_eq] at hProg

private theorem pair_first_pair (x y : Term) :
    __pair_first (mkPair x y) = x := by
  rfl

private theorem pair_second_pair (x y : Term) :
    __pair_second (mkPair x y) = y := by
  rfl

private theorem concatEqNormalize_false (x : Term) :
    concatEqNormalize (Term.Boolean false) x = x := by
  rfl

private theorem concatEqNormalize_true (x : Term) :
    concatEqNormalize (Term.Boolean true) x =
      __eo_list_rev (Term.UOp UserOp.str_concat) x := by
  rfl

private theorem concatEqStrip_false (s t : Term) :
    concatEqStrip (Term.Boolean false) s t =
      __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) := by
  rfl

private theorem concatEqStrip_true (s t : Term) :
    concatEqStrip (Term.Boolean true) s t =
      __str_strip_prefix
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)) := by
  rfl

private theorem concatEqLhs_false (s t : Term) :
    concatEqLhs (Term.Boolean false) s t =
      __str_nary_elim
        (__pair_first (__str_strip_prefix (__str_nary_intro s) (__str_nary_intro t))) := by
  rfl

private theorem concatEqRhs_false (s t : Term) :
    concatEqRhs (Term.Boolean false) s t =
      __str_nary_elim
        (__pair_second (__str_strip_prefix (__str_nary_intro s) (__str_nary_intro t))) := by
  rfl

private theorem concatEqLhs_true (s t : Term) :
    concatEqLhs (Term.Boolean true) s t =
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_first
            (__str_strip_prefix
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))))) := by
  rfl

private theorem concatEqRhs_true (s t : Term) :
    concatEqRhs (Term.Boolean true) s t =
      __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__pair_second
            (__str_strip_prefix
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
              (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t))))) := by
  rfl

private theorem concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_left_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_right_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_rev_first_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip (Term.Boolean true) s t)) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_first_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_rev_second_ne_stuck_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
        (__pair_second (concatEqStrip (Term.Boolean true) s t)) ≠
      Term.Stuck := by
  simpa [concatEqNormalize_true] using
    concatEqNormalize_second_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg

private theorem concatEq_true_intro_left_is_list_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
      Term.Boolean true := by
  exact eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
    (__str_nary_intro s)
    (concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg)

private theorem concatEq_true_intro_right_is_list_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
      Term.Boolean true := by
  exact eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
    (__str_nary_intro t)
    (concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg)

private theorem concatEq_true_strip_first_is_list_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__pair_first (concatEqStrip (Term.Boolean true) s t)) =
      Term.Boolean true := by
  exact eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
    (__pair_first (concatEqStrip (Term.Boolean true) s t))
    (concatEq_true_rev_first_ne_stuck_of_prog_ne_stuck s t hProg)

private theorem concatEq_true_strip_second_is_list_of_prog_ne_stuck
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__pair_second (concatEqStrip (Term.Boolean true) s t)) =
      Term.Boolean true := by
  exact eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
    (__pair_second (concatEqStrip (Term.Boolean true) s t))
    (concatEq_true_rev_second_ne_stuck_of_prog_ne_stuck s t hProg)

private theorem eo_interprets_strip_prefix_pair_of_eq
    (M : SmtModel) (x y : Term)
    (hXY : eo_interprets M (mkEq x y) true)
    (hStrip : __str_strip_prefix x y = mkPair x y) :
    eo_interprets M
      (mkEq (__pair_first (__str_strip_prefix x y))
        (__pair_second (__str_strip_prefix x y))) true := by
  rw [hStrip]
  simpa [mkPair, pair_first_pair, pair_second_pair] using hXY

private theorem eo_interprets_eq_symm_local
    (M : SmtModel) (x y : Term)
    (hXY : eo_interprets M (mkEq x y) true) :
    eo_interprets M (mkEq y x) true := by
  have hBool : RuleProofs.eo_has_bool_type (mkEq y x) :=
    RuleProofs.eo_has_bool_type_eq_symm x y
      (RuleProofs.eo_has_bool_type_of_interprets_true M (mkEq x y) hXY)
  exact RuleProofs.eo_interprets_eq_of_rel M y x hBool
    (RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))
      (RuleProofs.eo_interprets_eq_rel M x y hXY))

private theorem eo_interprets_eq_self_of_has_bool_type
    (M : SmtModel) (x : Term)
    (hBool : RuleProofs.eo_has_bool_type (mkEq x x)) :
    eo_interprets M (mkEq x x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M x x hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt x)))

private theorem str_strip_prefix_left_not_str_concat
    (x y : Term)
    (hx : x ≠ Term.Stuck)
    (hy : y ≠ Term.Stuck)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __str_strip_prefix x y = mkPair x y := by
  cases x with
  | Stuck =>
      exact False.elim (hx rfl)
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                exact False.elim (hNotConcat ⟨t, a, rfl⟩)
              · cases y <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
                  mkPair, hop] at hy ⊢
          | _ =>
              cases y <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
                mkPair] at hy ⊢
      | _ =>
          cases y <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
            mkPair] at hy ⊢
  | _ =>
      cases y <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
        mkPair] at hy ⊢

private theorem str_strip_prefix_right_not_str_concat
    (x y : Term)
    (hx : x ≠ Term.Stuck)
    (hy : y ≠ Term.Stuck)
    (hNotConcat : ¬ ∃ head tail : Term, y = mkConcat head tail) :
    __str_strip_prefix x y = mkPair x y := by
  cases y with
  | Stuck =>
      exact False.elim (hy rfl)
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                exact False.elim (hNotConcat ⟨t, a, rfl⟩)
              · cases x <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
                  mkPair, hop] at hx ⊢
          | _ =>
              cases x <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
                mkPair] at hx ⊢
      | _ =>
          cases x <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
            mkPair] at hx ⊢
  | _ =>
      cases x <;> simp [__str_strip_prefix, __eo_l_1___str_strip_prefix,
        mkPair] at hx ⊢

private theorem str_strip_prefix_concat_of_eo_eq_true
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean true) :
    __str_strip_prefix (mkConcat t t2) (mkConcat u s2) =
      __str_strip_prefix t2 s2 := by
  change __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
    (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      __str_strip_prefix t2 s2
  rw [h, eo_ite_true]

private theorem str_strip_prefix_tail_ne_stuck_of_concat_eo_eq_true
    (t u t2 s2 : Term)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (h : __eo_eq t u = Term.Boolean true) :
    __str_strip_prefix t2 s2 ≠ Term.Stuck := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 h] at hStrip
  exact hStrip

private theorem str_strip_prefix_concat_of_eo_eq_false
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean false) :
    __str_strip_prefix (mkConcat t t2) (mkConcat u s2) =
      mkPair (mkConcat t t2) (mkConcat u s2) := by
  change __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
    (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      mkPair (mkConcat t t2) (mkConcat u s2)
  rw [h, eo_ite_false]
  simp [__eo_l_1___str_strip_prefix, mkPair]

private theorem pair_first_str_strip_prefix_concat_of_eo_eq_true
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean true) :
    __pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      __pair_first (__str_strip_prefix t2 s2) := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 h]

private theorem pair_second_str_strip_prefix_concat_of_eo_eq_true
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean true) :
    __pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      __pair_second (__str_strip_prefix t2 s2) := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 h]

private theorem pair_first_str_strip_prefix_concat_of_eo_eq_false
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean false) :
    __pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      mkConcat t t2 := by
  rw [str_strip_prefix_concat_of_eo_eq_false t u t2 s2 h]
  rfl

private theorem pair_second_str_strip_prefix_concat_of_eo_eq_false
    (t u t2 s2 : Term)
    (h : __eo_eq t u = Term.Boolean false) :
    __pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)) =
      mkConcat u s2 := by
  rw [str_strip_prefix_concat_of_eo_eq_false t u t2 s2 h]
  rfl

private theorem eo_interprets_str_strip_prefix_concat_false
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean false)
    (hXY : eo_interprets M (mkEq (mkConcat t t2) (mkConcat u s2)) true) :
    eo_interprets M
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))) true := by
  exact eo_interprets_strip_prefix_pair_of_eq M (mkConcat t t2) (mkConcat u s2)
    hXY (str_strip_prefix_concat_of_eo_eq_false t u t2 s2 hCond)

private theorem eo_interprets_str_strip_prefix_concat_true_of_tail
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean true)
    (hTail : eo_interprets M
      (mkEq (__pair_first (__str_strip_prefix t2 s2))
        (__pair_second (__str_strip_prefix t2 s2))) true) :
    eo_interprets M
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))) true := by
  rw [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond]
  exact hTail

private theorem eo_interprets_rev_strip_prefix_concat_true_of_tail
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean true)
    (hTail :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2)))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))) true := by
  rw [pair_first_str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond]
  rw [pair_second_str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond]
  exact hTail

private theorem eo_interprets_rev_strip_prefix_concat_false_of_eq
    (M : SmtModel) (t u t2 s2 : Term)
    (hCond : __eo_eq t u = Term.Boolean false)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second
              (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))))) true := by
  rw [pair_first_str_strip_prefix_concat_of_eo_eq_false t u t2 s2 hCond]
  rw [pair_second_str_strip_prefix_concat_of_eo_eq_false t u t2 s2 hCond]
  exact hXY

private theorem pair_first_str_strip_prefix_self_eq_pair_second (x : Term)
    (hStrip : __str_strip_prefix x x ≠ Term.Stuck) :
    __pair_first (__str_strip_prefix x x) =
      __pair_second (__str_strip_prefix x x) := by
  fun_cases __str_strip_prefix x x
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2
    subst_vars
    have hIte :
        __eo_ite (__eo_eq t t) (__str_strip_prefix t2 t2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat t t2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t t) (__str_strip_prefix t2 t2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat t t2)) hIte with
      hCond | hCond
    · have hTailNonStuck : __str_strip_prefix t2 t2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      rw [hCond, eo_ite_true]
      exact pair_first_str_strip_prefix_self_eq_pair_second t2 hTailNonStuck
    · cases t <;> simp [__eo_eq, native_teq] at hCond
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair,
      pair_second_pair]
termination_by sizeOf x
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem eo_interprets_rev_str_strip_prefix_result
    (M : SmtModel) (x y : Term)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) x))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) y))) true)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))))) true := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    have hIte :
        __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
      hCond | hCond
    · have hTailEq :=
        hCancel t u t2 s2 hStrip hCond hXY
      have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      exact eo_interprets_rev_strip_prefix_concat_true_of_tail M t u t2 s2
        hCond
        (eo_interprets_rev_str_strip_prefix_result M t2 s2 hTailEq
          hTailNonStuck hCancel)
    · exact eo_interprets_rev_strip_prefix_concat_false_of_eq M t u t2 s2
        hCond hXY
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair,
      pair_second_pair] using hXY
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem eo_interprets_concat_eq_true_from_rev_strip
    (M : SmtModel) (s t : Term)
    (hRevStrip :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) true := by
  let revS := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)
  let revT := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)
  let strip := __str_strip_prefix revS revT
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)) ≠
      Term.Stuck
    simpa [concatEqStrip_true] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinal :=
    eo_interprets_rev_str_strip_prefix_result M revS revT
      (by
        simpa [revS, revT] using hRevStrip)
      hStripNonStuck hCancel
  simpa [revS, revT, strip, concatEqLhs_true, concatEqRhs_true,
    concatEqStrip_true] using hFinal

private theorem eo_interprets_rev_str_strip_prefix_result_with_final
    (M : SmtModel) (x y : Term)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) x))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) y))) true)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))) ≠ Term.Stuck)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))))) true := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    have hIte :
        __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
      hCond | hCond
    · have hTailFinalLeft :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck := by
        simpa [pair_first_str_strip_prefix_concat_of_eo_eq_true
            t u t2 s2 hCond] using hFinalLeft
      have hTailFinalRight :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck := by
        simpa [pair_second_str_strip_prefix_concat_of_eo_eq_true
            t u t2 s2 hCond] using hFinalRight
      have hTailEq :=
        hCancel t u t2 s2 hStrip hCond hTailFinalLeft hTailFinalRight hXY
      have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      exact eo_interprets_rev_strip_prefix_concat_true_of_tail M t u t2 s2
        hCond
        (eo_interprets_rev_str_strip_prefix_result_with_final M t2 s2
          hTailEq hTailNonStuck hTailFinalLeft hTailFinalRight hCancel)
    · exact eo_interprets_rev_strip_prefix_concat_false_of_eq M t u t2 s2
        hCond hXY
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair,
      pair_second_pair] using hXY
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem eo_interprets_concat_eq_true_from_rev_strip_with_final
    (M : SmtModel) (s t : Term)
    (hRevStrip :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) true := by
  let revS := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)
  let revT := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)
  let strip := __str_strip_prefix revS revT
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)) ≠
      Term.Stuck
    simpa [concatEqStrip_true] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first strip)) ≠ Term.Stuck := by
    simpa [revS, revT, strip, concatEqLhs_true, concatEqStrip_true] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second strip)) ≠ Term.Stuck := by
    simpa [revS, revT, strip, concatEqRhs_true, concatEqStrip_true] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinal :=
    eo_interprets_rev_str_strip_prefix_result_with_final M revS revT
      (by
        simpa [revS, revT] using hRevStrip)
      hStripNonStuck hFinalLeft hFinalRight hCancel
  simpa [revS, revT, strip, concatEqLhs_true, concatEqRhs_true,
    concatEqStrip_true] using hFinal

private theorem eo_interprets_rev_str_strip_prefix_result_with_final_seq
    (M : SmtModel) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) x))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) y))) true)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))) ≠ Term.Stuck)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix x y))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix x y))))) true := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    rcases str_concat_args_of_seq_type t t2 T hxTy with
      ⟨_htTy, ht2Ty⟩
    rcases str_concat_args_of_seq_type u s2 T hyTy with
      ⟨_huTy, hs2Ty⟩
    have hIte :
        __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
      hCond | hCond
    · have hTailFinalLeft :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck := by
        simpa [pair_first_str_strip_prefix_concat_of_eo_eq_true
            t u t2 s2 hCond] using hFinalLeft
      have hTailFinalRight :
          __str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck := by
        simpa [pair_second_str_strip_prefix_concat_of_eo_eq_true
            t u t2 s2 hCond] using hFinalRight
      have hTailEq :=
        hCancel t u t2 s2 hStrip hCond hxTy hyTy hTailFinalLeft
          hTailFinalRight hXY
      have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      exact eo_interprets_rev_strip_prefix_concat_true_of_tail M t u t2 s2
        hCond
        (eo_interprets_rev_str_strip_prefix_result_with_final_seq M t2 s2
          T ht2Ty hs2Ty hTailEq hTailNonStuck hTailFinalLeft
          hTailFinalRight hCancel)
    · exact eo_interprets_rev_strip_prefix_concat_false_of_eq M t u t2 s2
        hCond hXY
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair,
      pair_second_pair] using hXY
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem eo_interprets_double_rev_intros_of_self
    (M : SmtModel) (s t : Term)
    (hS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          s) true)
    (hT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          t) true)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  let ds :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)))
  let dt :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)))
  have hTdt : eo_interprets M (mkEq t dt) true :=
    eo_interprets_eq_symm_local M dt t (by simpa [dt] using hT)
  have hDsT : eo_interprets M (mkEq ds t) true :=
    RuleProofs.eo_interprets_eq_trans M ds s t
      (by simpa [ds] using hS) hST
  have hDsDt : eo_interprets M (mkEq ds dt) true :=
    RuleProofs.eo_interprets_eq_trans M ds t dt hDsT hTdt
  simpa [ds, dt] using hDsDt

private theorem smt_seq_rel_pack_append_cancel (T : SmtType) :
    ∀ xs ys zs : List SmtValue,
      RuleProofs.smt_seq_rel
          (native_pack_seq T (xs ++ ys)) (native_pack_seq T (xs ++ zs)) ->
      RuleProofs.smt_seq_rel (native_pack_seq T ys) (native_pack_seq T zs)
  | [], _, _, h => h
  | _ :: xs, ys, zs, h => by
      apply smt_seq_rel_pack_append_cancel T xs ys zs
      unfold RuleProofs.smt_seq_rel at h ⊢
      simpa [native_pack_seq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_and, RuleProofs.smtx_model_eval_eq_refl] using h

private theorem smt_seq_rel_pack_length_eq (T U : SmtType) :
    ∀ xs ys : List SmtValue,
      RuleProofs.smt_seq_rel (native_pack_seq T xs) (native_pack_seq U ys) ->
      xs.length = ys.length
  | [], [], _ => rfl
  | [], _ :: _, h => by
      unfold RuleProofs.smt_seq_rel at h
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq] at h
  | _ :: _, [], h => by
      unfold RuleProofs.smt_seq_rel at h
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq] at h
  | _ :: xs, _ :: ys, h => by
      have ht : RuleProofs.smt_seq_rel (native_pack_seq T xs) (native_pack_seq U ys) := by
        unfold RuleProofs.smt_seq_rel at h ⊢
        simp [native_pack_seq, __smtx_model_eval_eq, native_veq,
          SmtEval.native_and] at h ⊢
        exact h.2
      exact congrArg Nat.succ (smt_seq_rel_pack_length_eq T U xs ys ht)

private theorem smt_seq_rel_pack_append_right (T : SmtType) :
    ∀ xs ys zs : List SmtValue,
      RuleProofs.smt_seq_rel (native_pack_seq T xs) (native_pack_seq T ys) ->
      RuleProofs.smt_seq_rel
        (native_pack_seq T (xs ++ zs)) (native_pack_seq T (ys ++ zs))
  | [], [], zs, _ => by
      exact RuleProofs.smt_seq_rel_refl (native_pack_seq T zs)
  | [], _ :: ys, zs, h => by
      unfold RuleProofs.smt_seq_rel at h
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq] at h
  | _ :: xs, [], zs, h => by
      unfold RuleProofs.smt_seq_rel at h
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq] at h
  | x :: xs, y :: ys, zs, h => by
      have ht :
          RuleProofs.smt_seq_rel (native_pack_seq T xs)
            (native_pack_seq T ys) := by
        unfold RuleProofs.smt_seq_rel at h ⊢
        simp [native_pack_seq, __smtx_model_eval_eq, native_veq,
          SmtEval.native_and] at h ⊢
        exact h.2
      unfold RuleProofs.smt_seq_rel at h ⊢
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_and] at h ⊢
      exact ⟨h.1, smt_seq_rel_pack_append_right T xs ys zs ht⟩

private theorem smt_seq_rel_pack_append_left (T : SmtType)
    (xs ys zs : List SmtValue)
    (h : RuleProofs.smt_seq_rel (native_pack_seq T ys) (native_pack_seq T zs)) :
    RuleProofs.smt_seq_rel
      (native_pack_seq T (xs ++ ys)) (native_pack_seq T (xs ++ zs)) := by
  induction xs with
  | nil => exact h
  | cons x xs ih =>
      unfold RuleProofs.smt_seq_rel at ih ⊢
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_and, RuleProofs.smtx_model_eval_eq_refl, ih]

private theorem smt_seq_rel_pack_append_right_cancel (T : SmtType) :
    ∀ ys zs xs : List SmtValue,
      RuleProofs.smt_seq_rel
          (native_pack_seq T (ys ++ xs)) (native_pack_seq T (zs ++ xs)) ->
      RuleProofs.smt_seq_rel (native_pack_seq T ys) (native_pack_seq T zs)
  | [], [], _, _ => by
      unfold RuleProofs.smt_seq_rel
      simp [native_pack_seq, __smtx_model_eval_eq]
  | [], z :: zs, xs, h => by
      have hLen := smt_seq_rel_pack_length_eq T T xs ((z :: zs) ++ xs) h
      simp at hLen
      omega
  | y :: ys, [], xs, h => by
      have hLen := smt_seq_rel_pack_length_eq T T ((y :: ys) ++ xs) xs h
      simp at hLen
      omega
  | _ :: ys, _ :: zs, xs, h => by
      have ht :
          RuleProofs.smt_seq_rel
            (native_pack_seq T (ys ++ xs)) (native_pack_seq T (zs ++ xs)) := by
        unfold RuleProofs.smt_seq_rel at h ⊢
        simp [native_pack_seq, __smtx_model_eval_eq, native_veq,
          SmtEval.native_and] at h ⊢
        exact h.2
      unfold RuleProofs.smt_seq_rel at h ⊢
      simp [native_pack_seq, __smtx_model_eval_eq, native_veq,
        SmtEval.native_and] at h ⊢
      exact ⟨h.1, smt_seq_rel_pack_append_right_cancel T ys zs xs ht⟩

private theorem smt_seq_rel_pack_unpack (T : SmtType) :
    (s : SmtSeq) -> RuleProofs.smt_seq_rel s (native_pack_seq T (native_unpack_seq s))
  | SmtSeq.empty _ => by
      unfold RuleProofs.smt_seq_rel
      simp [native_unpack_seq, native_pack_seq, __smtx_model_eval_eq]
  | SmtSeq.cons v vs => by
      have ih := smt_seq_rel_pack_unpack T vs
      unfold RuleProofs.smt_seq_rel at ih ⊢
      simp [native_unpack_seq, native_pack_seq, __smtx_model_eval_eq,
        native_veq, SmtEval.native_and, RuleProofs.smtx_model_eval_eq_refl, ih]

private theorem native_unpack_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq, native_unpack_pack_seq T xs]

private theorem elem_typeof_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue,
      __smtx_elem_typeof_seq_value (native_pack_seq T xs) = T
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, __smtx_elem_typeof_seq_value,
        elem_typeof_pack_seq T xs]

private theorem smt_value_rel_str_concat_nil_empty
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt nil))
      (SmtValue.Seq (SmtSeq.empty T)) := by
  cases nil <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_str_concat, __eo_eq,
      native_teq] at hNil
  case String s =>
      subst s
      change __smtx_typeof (SmtTerm.String "") = SmtType.Seq T at hNilTy
      rw [__smtx_typeof.eq_4] at hNilTy
      injection hNilTy with hT
      subst T
      unfold RuleProofs.smt_value_rel
      change __smtx_model_eval_eq
        (__smtx_model_eval M (SmtTerm.String ""))
        (SmtValue.Seq (SmtSeq.empty SmtType.Char)) = SmtValue.Boolean true
      rw [__smtx_model_eval.eq_4]
      simp [native_pack_string, __smtx_ssm_char_values_of_string,
        native_pack_seq, __smtx_model_eval_eq]
  case seq_empty A =>
      change __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type A)) =
        SmtType.Seq T at hNilTy
      change RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt_seq_empty (__eo_to_smt_type A)))
        (SmtValue.Seq (SmtSeq.empty T))
      cases hA : __eo_to_smt_type A with
      | Seq U =>
          rw [hA] at hNilTy
          simp [__eo_to_smt_seq_empty] at hNilTy ⊢
          have hNN : __smtx_typeof (SmtTerm.seq_empty U) ≠ SmtType.None := by
            rw [hNilTy]
            intro h
            cases h
          have hTyU := TranslationProofs.smtx_typeof_seq_empty_of_non_none U hNN
          have hUT : U = T := by
            rw [hTyU] at hNilTy
            injection hNilTy
          subst T
          rw [__smtx_model_eval.eq_77]
          unfold RuleProofs.smt_value_rel
          simp [__smtx_model_eval_eq]
      | _ =>
          rw [hA] at hNilTy
          simp [__eo_to_smt_seq_empty, TranslationProofs.smtx_typeof_none] at hNilTy

private theorem smt_value_rel_str_concat_right_empty
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hEmpty := eval_seq_empty_typeof M x T hxTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hEmpty]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ []))) (SmtValue.Seq sx) =
      SmtValue.Boolean true
  rw [List.append_nil, hsxElem]
  change RuleProofs.smt_seq_rel (native_pack_seq T (native_unpack_seq sx)) sx
  exact RuleProofs.smt_seq_rel_symm sx (native_pack_seq T (native_unpack_seq sx))
    (smt_seq_rel_pack_unpack T sx)

private theorem smt_value_rel_str_concat_left_empty
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat (__seq_empty (__eo_typeof x)) x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hEmpty := eval_seq_empty_typeof M x T hxTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, hxEval, hEmpty]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value (SmtSeq.empty T))
      ([] ++ native_unpack_seq sx))) (SmtValue.Seq sx) =
      SmtValue.Boolean true
  simp [__smtx_elem_typeof_seq_value]
  change RuleProofs.smt_seq_rel (native_pack_seq T (native_unpack_seq sx)) sx
  exact RuleProofs.smt_seq_rel_symm sx (native_pack_seq T (native_unpack_seq sx))
    (smt_seq_rel_pack_unpack T sx)

private theorem smt_value_rel_str_concat_list_nil_left_empty
    (M : SmtModel) (hM : model_total_typed M) (nil x : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat nil x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hNilValTy := smt_model_eval_preserves_type M hM (__eo_to_smt nil)
    (SmtType.Seq T) hNilTy (seq_ne_none T) (type_inhabited_seq T)
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hNilValTy with ⟨snil, hNilEval⟩
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  have hNilRel := smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy
  unfold RuleProofs.smt_value_rel at hNilRel ⊢
  rw [hNilEval] at hNilRel
  cases snil with
  | cons v vs =>
      simp [__smtx_model_eval_eq, native_veq] at hNilRel
  | empty U =>
      have hUT : U = T := by
        have hTy : __smtx_typeof_value (SmtValue.Seq (SmtSeq.empty U)) =
            SmtType.Seq T := by
          simpa [hNilEval] using hNilValTy
        simp [__smtx_typeof_value, __smtx_typeof_seq_value] at hTy
        exact hTy
      subst T
      rw [smtx_model_eval_str_concat_term_eq, hNilEval, hxEval]
      change __smtx_model_eval_eq
        (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value
          (SmtSeq.empty U)) ([] ++ native_unpack_seq sx)))
        (SmtValue.Seq sx) = SmtValue.Boolean true
      simp [__smtx_elem_typeof_seq_value]
      change RuleProofs.smt_seq_rel (native_pack_seq U (native_unpack_seq sx)) sx
      exact RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq U (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack U sx)

private theorem smt_value_rel_str_concat_list_nil_right_empty
    (M : SmtModel) (hM : model_total_typed M) (x nil : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hNilValTy := smt_model_eval_preserves_type M hM (__eo_to_smt nil)
    (SmtType.Seq T) hNilTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hNilValTy with ⟨snil, hNilEval⟩
  have hNilRel := smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy
  unfold RuleProofs.smt_value_rel at hNilRel ⊢
  rw [hNilEval] at hNilRel
  cases snil with
  | cons v vs =>
      simp [__smtx_model_eval_eq, native_veq] at hNilRel
  | empty U =>
      have hUT : U = T := by
        have hTy : __smtx_typeof_value (SmtValue.Seq (SmtSeq.empty U)) =
            SmtType.Seq T := by
          simpa [hNilEval] using hNilValTy
        simp [__smtx_typeof_value, __smtx_typeof_seq_value] at hTy
        exact hTy
      subst T
      rw [smtx_model_eval_str_concat_term_eq, hxEval, hNilEval]
      change __smtx_model_eval_eq
        (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_unpack_seq sx ++ []))) (SmtValue.Seq sx) =
          SmtValue.Boolean true
      rw [List.append_nil]
      have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq U := by
        simpa [hxEval, __smtx_typeof_value] using hxValTy
      have hsxElem : __smtx_elem_typeof_seq_value sx = U :=
        elem_typeof_seq_value_of_typeof_seq_value hsxTy
      rw [hsxElem]
      change RuleProofs.smt_seq_rel (native_pack_seq U (native_unpack_seq sx)) sx
      exact RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq U (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack U sx)

private theorem smt_value_rel_str_concat_left_of_rel_empty
    (M : SmtModel) (hM : model_total_typed M) (empty x : Term) (T : SmtType)
    (hEmptyTy : __smtx_typeof (__eo_to_smt empty) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt empty))
      (SmtValue.Seq (SmtSeq.empty T))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat empty x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hEmptyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt empty)
    (SmtType.Seq T) hEmptyTy (seq_ne_none T) (type_inhabited_seq T)
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hEmptyValTy with ⟨sempty, hEmptyEval⟩
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  unfold RuleProofs.smt_value_rel at hEmptyRel ⊢
  rw [hEmptyEval] at hEmptyRel
  cases sempty with
  | cons v vs =>
      simp [__smtx_model_eval_eq, native_veq] at hEmptyRel
  | empty U =>
      have hUT : U = T := by
        have hTy : __smtx_typeof_value (SmtValue.Seq (SmtSeq.empty U)) =
            SmtType.Seq T := by
          simpa [hEmptyEval] using hEmptyValTy
        simp [__smtx_typeof_value, __smtx_typeof_seq_value] at hTy
        exact hTy
      subst T
      rw [smtx_model_eval_str_concat_term_eq, hEmptyEval, hxEval]
      change __smtx_model_eval_eq
        (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value
          (SmtSeq.empty U)) ([] ++ native_unpack_seq sx)))
        (SmtValue.Seq sx) = SmtValue.Boolean true
      simp [__smtx_elem_typeof_seq_value]
      change RuleProofs.smt_seq_rel (native_pack_seq U (native_unpack_seq sx)) sx
      exact RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq U (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack U sx)

private theorem smt_value_rel_str_concat_right_of_rel_empty
    (M : SmtModel) (hM : model_total_typed M) (x empty : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyTy : __smtx_typeof (__eo_to_smt empty) = SmtType.Seq T)
    (hEmptyRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt empty))
      (SmtValue.Seq (SmtSeq.empty T))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x empty)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hEmptyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt empty)
    (SmtType.Seq T) hEmptyTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hEmptyValTy with ⟨sempty, hEmptyEval⟩
  unfold RuleProofs.smt_value_rel at hEmptyRel ⊢
  rw [hEmptyEval] at hEmptyRel
  cases sempty with
  | cons v vs =>
      simp [__smtx_model_eval_eq, native_veq] at hEmptyRel
  | empty U =>
      have hUT : U = T := by
        have hTy : __smtx_typeof_value (SmtValue.Seq (SmtSeq.empty U)) =
            SmtType.Seq T := by
          simpa [hEmptyEval] using hEmptyValTy
        simp [__smtx_typeof_value, __smtx_typeof_seq_value] at hTy
        exact hTy
      subst T
      rw [smtx_model_eval_str_concat_term_eq, hxEval, hEmptyEval]
      change __smtx_model_eval_eq
        (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
          (native_unpack_seq sx ++ []))) (SmtValue.Seq sx) =
          SmtValue.Boolean true
      rw [List.append_nil]
      have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq U := by
        simpa [hxEval, __smtx_typeof_value] using hxValTy
      have hsxElem : __smtx_elem_typeof_seq_value sx = U :=
        elem_typeof_seq_value_of_typeof_seq_value hsxTy
      rw [hsxElem]
      change RuleProofs.smt_seq_rel (native_pack_seq U (native_unpack_seq sx)) sx
      exact RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq U (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack U sx)

private theorem smt_value_rel_str_concat_left_congr
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hxy : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat y z))) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z)
    (SmtType.Seq T) hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hxySeq : RuleProofs.smt_seq_rel sx sy := by
    unfold RuleProofs.smt_value_rel at hxy
    unfold RuleProofs.smt_seq_rel
    simpa [hxEval, hyEval] using hxy
  have hPackXY :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sx))
        (native_pack_seq T (native_unpack_seq sy)) :=
    RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sx)) sx
      (native_pack_seq T (native_unpack_seq sy))
      (RuleProofs.smt_seq_rel_symm sx
        (native_pack_seq T (native_unpack_seq sx))
        (smt_seq_rel_pack_unpack T sx))
      (RuleProofs.smt_seq_rel_trans sx sy
        (native_pack_seq T (native_unpack_seq sy)) hxySeq
        (smt_seq_rel_pack_unpack T sy))
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
  rw [hxEval, hyEval, hzEval]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sz)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sz))) =
      SmtValue.Boolean true
  rw [hsxElem, hsyElem]
  exact smt_seq_rel_pack_append_right T
    (native_unpack_seq sx) (native_unpack_seq sy) (native_unpack_seq sz)
    hPackXY

private theorem smt_value_rel_str_concat_right_congr
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hyz : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x y)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x z))) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z)
    (SmtType.Seq T) hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hyzSeq : RuleProofs.smt_seq_rel sy sz := by
    unfold RuleProofs.smt_value_rel at hyz
    unfold RuleProofs.smt_seq_rel
    simpa [hyEval, hzEval] using hyz
  have hPackYZ :
      RuleProofs.smt_seq_rel
        (native_pack_seq T (native_unpack_seq sy))
        (native_pack_seq T (native_unpack_seq sz)) :=
    RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sy)) sy
      (native_pack_seq T (native_unpack_seq sz))
      (RuleProofs.smt_seq_rel_symm sy
        (native_pack_seq T (native_unpack_seq sy))
        (smt_seq_rel_pack_unpack T sy))
      (RuleProofs.smt_seq_rel_trans sy sz
        (native_pack_seq T (native_unpack_seq sz)) hyzSeq
        (smt_seq_rel_pack_unpack T sz))
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq]
  rw [hxEval, hyEval, hzEval]
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sy)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sz))) =
      SmtValue.Boolean true
  rw [hsxElem]
  exact smt_seq_rel_pack_append_left T (native_unpack_seq sx)
    (native_unpack_seq sy) (native_unpack_seq sz) hPackYZ

private theorem smt_value_rel_str_concat_assoc
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat (mkConcat x y) z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (mkConcat y z)))) := by
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x)
    (SmtType.Seq T) hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y)
    (SmtType.Seq T) hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z)
    (SmtType.Seq T) hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, __smtx_typeof_value] using hxValTy
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hsxElem : __smtx_elem_typeof_seq_value sx = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsxTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  unfold RuleProofs.smt_value_rel
  rw [smtx_model_eval_str_concat_term_eq M (mkConcat x y) z]
  rw [smtx_model_eval_str_concat_term_eq M x y]
  rw [smtx_model_eval_str_concat_term_eq M x (mkConcat y z)]
  rw [smtx_model_eval_str_concat_term_eq M y z]
  rw [hxEval, hyEval, hzEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat,
    native_unpack_pack_seq, elem_typeof_pack_seq, hsxElem, hsyElem,
    List.append_assoc, RuleProofs.smtx_model_eval_eq_refl]

private theorem eo_interprets_str_concat_assoc
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    eo_interprets M
      (mkEq (mkConcat (mkConcat x y) z) (mkConcat x (mkConcat y z)))
      true := by
  have hXYTy : __smtx_typeof (__eo_to_smt (mkConcat x y)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x y T hxTy hyTy
  have hYZTy : __smtx_typeof (__eo_to_smt (mkConcat y z)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y z T hyTy hzTy
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat (mkConcat x y) z)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (mkConcat x y) z T hXYTy hzTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat x (mkConcat y z))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x (mkConcat y z) T hxTy hYZTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat (mkConcat x y) z) (mkConcat x (mkConcat y z))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat (mkConcat x y) z) (mkConcat x (mkConcat y z)) hBool
    (smt_value_rel_str_concat_assoc M hM x y z T hxTy hyTy hzTy)

private theorem eo_interprets_str_concat_assoc_symm
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    eo_interprets M
      (mkEq (mkConcat x (mkConcat y z)) (mkConcat (mkConcat x y) z))
      true := by
  have hXYTy : __smtx_typeof (__eo_to_smt (mkConcat x y)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x y T hxTy hyTy
  have hYZTy : __smtx_typeof (__eo_to_smt (mkConcat y z)) =
      SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y z T hyTy hzTy
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat x (mkConcat y z))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x (mkConcat y z) T hxTy hYZTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat (mkConcat x y) z)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (mkConcat x y) z T hXYTy hzTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x (mkConcat y z)) (mkConcat (mkConcat x y) z)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat x (mkConcat y z)) (mkConcat (mkConcat x y) z) hBool
    (RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt (mkConcat (mkConcat x y) z)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x (mkConcat y z))))
      (smt_value_rel_str_concat_assoc M hM x y z T hxTy hyTy hzTy))

private theorem eo_interprets_str_concat_left_congr_of_seq
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hXY : eo_interprets M (mkEq x y) true) :
    eo_interprets M (mkEq (mkConcat x z) (mkConcat y z)) true := by
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat x z)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x z T hxTy hzTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat y z)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq y z T hyTy hzTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x z) (mkConcat y z)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M (mkConcat x z)
    (mkConcat y z) hBool
    (smt_value_rel_str_concat_left_congr M hM x y z T hxTy hyTy hzTy
      (RuleProofs.eo_interprets_eq_rel M x y hXY))

private theorem eo_interprets_str_concat_right_congr_of_seq
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hYZ : eo_interprets M (mkEq y z) true) :
    eo_interprets M (mkEq (mkConcat x y) (mkConcat x z)) true := by
  have hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x y T hxTy hyTy
  have hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat x z)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x z T hxTy hzTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x y) (mkConcat x z)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hLeftTy, hRightTy]
    · rw [hLeftTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M (mkConcat x y)
    (mkConcat x z) hBool
    (smt_value_rel_str_concat_right_congr M hM x y z T hxTy hyTy hzTy
      (RuleProofs.eo_interprets_eq_rel M y z hYZ))

private theorem smt_value_rel_list_concat_rec_str_concat
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ a z T,
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true ->
      __smtx_typeof (__eo_to_smt a) = SmtType.Seq T ->
      __smtx_typeof (__eo_to_smt z) = SmtType.Seq T ->
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)))
        (__smtx_model_eval M (__eo_to_smt (mkConcat a z)))
  | a, z, T, hList, haTy, hzTy => by
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z =>
          simp [__eo_is_list] at hList
      | case2 a hA =>
          change __smtx_typeof SmtTerm.None = SmtType.Seq T at hzTy
          rw [TranslationProofs.smtx_typeof_none] at hzTy
          cases hzTy
      | case3 g x y z hZ ih =>
          have hg : g = Term.UOp UserOp.str_concat :=
            eo_is_list_cons_head_eq_of_true (Term.UOp UserOp.str_concat)
              g x y hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.str_concat) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self (Term.UOp UserOp.str_concat)
              x y hList
          have hConcatNN :
              __smtx_typeof (__eo_to_smt (mkConcat x y)) ≠ SmtType.None := by
            rw [haTy]
            exact seq_ne_none T
          rcases str_concat_args_of_non_none x y hConcatNN with
            ⟨U, hxTy, hyTyU⟩
          have hConcatTyU :
              __smtx_typeof (__eo_to_smt (mkConcat x y)) = SmtType.Seq U :=
            smt_typeof_str_concat_of_seq x y U hxTy hyTyU
          have hUT : U = T := by
            have hSeq : SmtType.Seq U = SmtType.Seq T := by
              rw [← hConcatTyU, haTy]
            injection hSeq
          have hxTyT :
              __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
            simpa [hUT] using hxTy
          have hyTy :
              __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
            simpa [hUT] using hyTyU
          have hZNonStuck : z ≠ Term.Stuck := by
            intro hz
            subst z
            change __smtx_typeof SmtTerm.None = SmtType.Seq T at hzTy
            rw [TranslationProofs.smtx_typeof_none] at hzTy
            cases hzTy
          have hTailConcat :
              __eo_list_concat_rec y z ≠ Term.Stuck :=
            eo_list_concat_rec_ne_stuck_of_list (Term.UOp UserOp.str_concat)
              y z hTailList hZNonStuck
          have hTailRel :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (__eo_list_concat_rec y z)))
                (__smtx_model_eval M (__eo_to_smt (mkConcat y z))) :=
            ih hTailList hyTy hzTy
          have hTailConcatTy :
              __smtx_typeof (__eo_to_smt (__eo_list_concat_rec y z)) =
                SmtType.Seq T :=
            smt_typeof_list_concat_rec_str_concat_of_seq y z T hTailList
              hyTy hzTy
          have hYZTy :
              __smtx_typeof (__eo_to_smt (mkConcat y z)) = SmtType.Seq T :=
            smt_typeof_str_concat_of_seq y z T hyTy hzTy
          rw [eo_list_concat_rec_str_concat_cons_eq_of_tail_ne_stuck
            x y z hTailConcat]
          have hCongr :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkConcat x (__eo_list_concat_rec y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkConcat x (mkConcat y z)))) :=
            smt_value_rel_str_concat_right_congr M hM x
              (__eo_list_concat_rec y z) (mkConcat y z) T
              hxTyT hTailConcatTy hYZTy hTailRel
          have hAssoc :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkConcat x (mkConcat y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkConcat (mkConcat x y) z))) :=
            RuleProofs.smt_value_rel_symm
              (__smtx_model_eval M
                (__eo_to_smt (mkConcat (mkConcat x y) z)))
              (__smtx_model_eval M
                (__eo_to_smt (mkConcat x (mkConcat y z))))
              (smt_value_rel_str_concat_assoc M hM x y z T
                hxTyT hyTy hzTy)
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat x (__eo_list_concat_rec y z))))
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat x (mkConcat y z))))
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat (mkConcat x y) z)))
            hCongr hAssoc
      | case4 nil z hNil hZ hNot =>
          have hGet :
              __eo_get_nil_rec (Term.UOp UserOp.str_concat) nil ≠
                Term.Stuck :=
            eo_get_nil_rec_ne_stuck_of_is_list_true
              (Term.UOp UserOp.str_concat) nil hList
          have hReq :
              __eo_requires
                  (__eo_is_list_nil (Term.UOp UserOp.str_concat) nil)
                  (Term.Boolean true) nil ≠ Term.Stuck := by
            simpa [__eo_get_nil_rec] using hGet
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
                Term.Boolean true :=
            eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.str_concat) nil)
              (Term.Boolean true) nil hReq
          rw [eo_list_concat_rec_str_concat_nil_eq_of_nil_true
            nil z hNilTrue]
          exact RuleProofs.smt_value_rel_symm
            (__smtx_model_eval M (__eo_to_smt (mkConcat nil z)))
            (__smtx_model_eval M (__eo_to_smt z))
            (smt_value_rel_str_concat_list_nil_left_empty M hM
              nil z T hNilTrue haTy hzTy)

private theorem smt_value_rel_str_nary_intro_ite
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (mkConcat x (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (mkConcat x (__seq_empty (__eo_typeof x))))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (mkConcat x (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x))
  · rw [hCond, eo_ite_false]
    exact smt_value_rel_str_concat_right_empty M hM x T hxTy

private theorem smt_value_rel_str_nary_intro_default
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x))))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x))
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    rw [hCond, eo_ite_false, hApplyEq]
    exact smt_value_rel_str_concat_right_empty M hM x T hxTy

private theorem smt_value_rel_str_nary_intro
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  cases x with
  | Stuck =>
      simp [__str_nary_intro] at hIntro
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simp [__str_nary_intro]
                exact RuleProofs.smt_value_rel_refl
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (Term.Apply
                        (Term.Apply (Term.UOp UserOp.str_concat) t) a)))
              · change RuleProofs.smt_value_rel
                  (__smtx_model_eval M (__eo_to_smt (__str_nary_intro
                    (Term.Apply (Term.Apply (Term.UOp op) t) a))))
                  (__smtx_model_eval M (__eo_to_smt
                    (Term.Apply (Term.Apply (Term.UOp op) t) a)))
                simp [__str_nary_intro, hop] at hIntro ⊢
                exact smt_value_rel_str_nary_intro_default M hM
                  (Term.Apply (Term.Apply (Term.UOp op) t) a) T hxTy hIntro
          | _ =>
              simp [__str_nary_intro] at hIntro ⊢
              exact smt_value_rel_str_nary_intro_default M hM
                _ T hxTy hIntro
      | _ =>
          simp [__str_nary_intro] at hIntro ⊢
          exact smt_value_rel_str_nary_intro_default M hM
            _ T hxTy hIntro
  | _ =>
      simp [__str_nary_intro] at hIntro ⊢
      exact smt_value_rel_str_nary_intro_default M hM _ T hxTy hIntro

private theorem smt_typeof_str_nary_intro_default_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x))))) ≠ SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))))) = SmtType.Seq T := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact hxTy
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    have hApplyNN :
        __smtx_typeof
          (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))) ≠
            SmtType.None := by
      simpa [hCond, eo_ite_false, hApplyEq] using hIntroNN
    rcases str_concat_args_of_non_none x (__seq_empty (__eo_typeof x)) hApplyNN with
      ⟨U, hxTyU, hEmptyTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hxTyU, hxTy]
      injection hSeq
    have hEmptyTy :
        __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
          SmtType.Seq T := by
      simpa [hUT] using hEmptyTyU
    rw [hCond, eo_ite_false, hApplyEq]
    exact smt_typeof_str_concat_of_seq x (__seq_empty (__eo_typeof x)) T
      hxTy hEmptyTy

private theorem smt_typeof_str_nary_intro_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN : __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
      SmtType.None) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T := by
  have hIntro : __str_nary_intro x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation (__str_nary_intro x) hIntroNN
  cases x with
  | Stuck =>
      simp [__str_nary_intro] at hIntro
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simpa [__str_nary_intro] using hxTy
              · change __smtx_typeof
                    (__eo_to_smt (__str_nary_intro
                      (Term.Apply (Term.Apply (Term.UOp op) t) a))) =
                    SmtType.Seq T
                simp [__str_nary_intro, hop] at hIntroNN hIntro ⊢
                exact smt_typeof_str_nary_intro_default_of_seq
                  (Term.Apply (Term.Apply (Term.UOp op) t) a) T hxTy hIntroNN
                  hIntro
          | _ =>
              simp [__str_nary_intro] at hIntroNN hIntro ⊢
              exact smt_typeof_str_nary_intro_default_of_seq _ T hxTy
                hIntroNN hIntro
      | _ =>
          simp [__str_nary_intro] at hIntroNN hIntro ⊢
          exact smt_typeof_str_nary_intro_default_of_seq _ T hxTy hIntroNN hIntro
  | _ =>
      simp [__str_nary_intro] at hIntroNN hIntro ⊢
      exact smt_typeof_str_nary_intro_default_of_seq _ T hxTy hIntroNN hIntro

private theorem smt_typeof_str_nary_intro_default_of_seq_ne_stuck
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x))))) ≠ SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))))) = SmtType.Seq T := by
  exact smt_typeof_str_nary_intro_default_of_seq x T hxTy hIntroNN hIntro

private theorem smt_typeof_str_nary_intro_of_seq_ne_stuck
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN : __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
      SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T := by
  exact smt_typeof_str_nary_intro_of_seq x T hxTy hIntroNN

private theorem smt_typeof_str_nary_intro_default_of_seq_empty_typeof
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))))) = SmtType.Seq T := by
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x))) hIntro with hCond | hCond
  · rw [hCond, eo_ite_true]
    exact hxTy
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntro
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x)) =
            mkConcat x (__seq_empty (__eo_typeof x)) :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x)
        (__seq_empty (__eo_typeof x)) hApplyNonStuck
    have hEmptyTy :
        __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
          SmtType.Seq T :=
      smt_typeof_seq_empty_typeof x T hxTy hEmptyNN
    rw [hCond, eo_ite_false, hApplyEq]
    exact smt_typeof_str_concat_of_seq x (__seq_empty (__eo_typeof x))
      T hxTy hEmptyTy

private theorem smt_typeof_str_nary_intro_of_seq_empty_typeof
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T := by
  cases x with
  | Stuck =>
      simp [__str_nary_intro] at hIntro
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simpa [__str_nary_intro] using hxTy
              · change __smtx_typeof
                    (__eo_to_smt (__str_nary_intro
                      (Term.Apply (Term.Apply (Term.UOp op) t) a))) =
                    SmtType.Seq T
                simp [__str_nary_intro, hop] at hIntro ⊢
                exact smt_typeof_str_nary_intro_default_of_seq_empty_typeof
                  (Term.Apply (Term.Apply (Term.UOp op) t) a) T hxTy
                  hEmptyNN hIntro
          | _ =>
              simp [__str_nary_intro] at hIntro ⊢
              exact smt_typeof_str_nary_intro_default_of_seq_empty_typeof
                _ T hxTy hEmptyNN hIntro
      | _ =>
          simp [__str_nary_intro] at hIntro ⊢
          exact smt_typeof_str_nary_intro_default_of_seq_empty_typeof
            _ T hxTy hEmptyNN hIntro
  | _ =>
      simp [__str_nary_intro] at hIntro ⊢
      exact smt_typeof_str_nary_intro_default_of_seq_empty_typeof
        _ T hxTy hEmptyNN hIntro

private theorem str_nary_intro_has_smt_translation_of_seq_empty_typeof
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hEmptyNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None := by
  rw [smt_typeof_str_nary_intro_of_seq_empty_typeof x T hxTy hEmptyNN
    hIntro]
  exact seq_ne_none T

private theorem eo_interprets_concat_eq_true_from_rev_strip_with_final_seq
    (M : SmtModel) (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None)
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hRevStrip :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) true := by
  let revS := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)
  let revT := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)
  let strip := __str_strip_prefix revS revT
  have hIntroS : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroT : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck s T hsTy hIntroSNN
      hIntroS
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck t T htTy hIntroTNN
      hIntroT
  have hRevSNonStuck : revS ≠ Term.Stuck := by
    simpa [revS] using
      concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevTNonStuck : revT ≠ Term.Stuck := by
    simpa [revT] using
      concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hIntroSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevSNonStuck
  have hIntroTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevTNonStuck
  have hRevSTy : __smtx_typeof (__eo_to_smt revS) = SmtType.Seq T := by
    simpa [revS] using
      smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro s) T
        hIntroSList hIntroSTy hRevSNonStuck
  have hRevTTy : __smtx_typeof (__eo_to_smt revT) = SmtType.Seq T := by
    simpa [revT] using
      smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro t) T
        hIntroTList hIntroTTy hRevTNonStuck
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)) ≠
      Term.Stuck
    simpa [concatEqStrip_true] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first strip)) ≠ Term.Stuck := by
    simpa [revS, revT, strip, concatEqLhs_true, concatEqStrip_true] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second strip)) ≠ Term.Stuck := by
    simpa [revS, revT, strip, concatEqRhs_true, concatEqStrip_true] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hFinal :=
    eo_interprets_rev_str_strip_prefix_result_with_final_seq M revS revT
      T hRevSTy hRevTTy
      (by
        simpa [revS, revT] using hRevStrip)
      hStripNonStuck hFinalLeft hFinalRight hCancel
  simpa [revS, revT, strip, concatEqLhs_true, concatEqRhs_true,
    concatEqStrip_true] using hFinal

private theorem concatEq_seq_pack_of_left_concat_empty_typeof
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt (mkConcat sHead sTail)) =
        SmtType.Seq T ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat sHead sTail))) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases eq_bool_seq_of_left_concat sHead sTail t hPremBool with
    ⟨T, hLeftTy, hRightTy⟩
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof t T hRightTy
      hEmptyTNN hIntroT
  exact concatEq_seq_pack_of_left_concat sHead sTail t hPremBool hIntroTNN

private theorem concatEq_seq_pack_of_right_concat_empty_typeof
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof
          (__eo_to_smt (__str_nary_intro (mkConcat tHead tTail))) ≠
        SmtType.None := by
  rcases eq_bool_seq_of_right_concat s tHead tTail hPremBool with
    ⟨T, hLeftTy, _⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof s T hLeftTy
      hEmptySNN hIntroS
  exact concatEq_seq_pack_of_right_concat s tHead tTail hPremBool hIntroSNN

private theorem smt_typeof_double_rev_str_nary_intro_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x)))) =
      SmtType.Seq T := by
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck x T hxTy hIntroNN hIntro
  have hIntroList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro x) hRevIntro
  exact smt_typeof_list_rev_list_rev_str_concat_of_seq (__str_nary_intro x)
    T hIntroList hIntroTy hRevIntro

private theorem smt_value_rel_str_nary_elim_concat_ite
    (M : SmtModel) (hM : model_total_typed M) (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) ≠
        Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))))
      (__smtx_model_eval M (__eo_to_smt (mkConcat t ss))) := by
  have hConcatNN : __smtx_typeof (__eo_to_smt (mkConcat t ss)) ≠ SmtType.None := by
    rw [hConcatTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none t ss hConcatNN with ⟨U, htTy, hssTy⟩
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) hElim with
    hCond | hCond
  · have hEmptyEq := eq_of_eo_eq_true_local ss (__seq_empty (__eo_typeof t)) hCond
    have hssEq : ss = __seq_empty (__eo_typeof t) := hEmptyEq.symm
    subst ss
    rw [hCond, eo_ite_true]
    exact RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt (mkConcat t (__seq_empty (__eo_typeof t)))))
      (__smtx_model_eval M (__eo_to_smt t))
      (smt_value_rel_str_concat_right_empty M hM t U htTy)
  · rw [hCond, eo_ite_false]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (mkConcat t ss)))

private theorem smt_value_rel_str_nary_elim_requires
    (M : SmtModel) (t : Term)
    (hElim : __eo_requires t (__seq_empty (__eo_typeof t)) t ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (__eo_requires t (__seq_empty (__eo_typeof t)) t)))
      (__smtx_model_eval M (__eo_to_smt t)) := by
  rw [eo_requires_eq_result_of_ne_stuck t (__seq_empty (__eo_typeof t)) t hElim]
  exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt t))

private theorem smt_value_rel_str_nary_elim
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  cases x with
  | Stuck =>
      simp [__str_nary_elim] at hElim
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simp [__str_nary_elim] at hElim ⊢
                exact smt_value_rel_str_nary_elim_concat_ite M hM t a T hxTy hElim
              · simp [__str_nary_elim, hop] at hElim ⊢
                exact smt_value_rel_str_nary_elim_requires M _ hElim
          | _ =>
              simp [__str_nary_elim] at hElim ⊢
              exact smt_value_rel_str_nary_elim_requires M _ hElim
      | _ =>
          simp [__str_nary_elim] at hElim ⊢
          exact smt_value_rel_str_nary_elim_requires M _ hElim
  | _ =>
      simp [__str_nary_elim] at hElim ⊢
      exact smt_value_rel_str_nary_elim_requires M _ hElim

private theorem smt_value_rel_str_nary_elim_list_nil_empty
    (M : SmtModel) (hM : model_total_typed M) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hElim : __str_nary_elim nil ≠ Term.Stuck) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim nil)))
      (SmtValue.Seq (SmtSeq.empty T)) := by
  exact RuleProofs.smt_value_rel_trans
    (__smtx_model_eval M (__eo_to_smt (__str_nary_elim nil)))
    (__smtx_model_eval M (__eo_to_smt nil))
    (SmtValue.Seq (SmtSeq.empty T))
    (smt_value_rel_str_nary_elim M hM nil T hNilTy hElim)
    (smt_value_rel_str_concat_nil_empty M nil T hNil hNilTy)

private theorem smt_typeof_str_nary_elim_concat_of_seq (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElimNN :
      __smtx_typeof (__eo_to_smt
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
          (mkConcat t ss))) ≠ SmtType.None)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss))) = SmtType.Seq T := by
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) ≠ SmtType.None := by
    rw [hConcatTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none t ss hConcatNN with ⟨U, htTyU, hssTyU⟩
  have hConcatTyU :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq t ss U htTyU hssTyU
  have hUT : U = T := by
    have hSeq : SmtType.Seq U = SmtType.Seq T := by
      rw [← hConcatTyU, hConcatTy]
    injection hSeq
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    simpa [hUT] using htTyU
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) hElim with
    hCond | hCond
  · rw [hCond, eo_ite_true]
    exact htTy
  · rw [hCond, eo_ite_false]
    exact hConcatTy

private theorem smt_typeof_str_nary_elim_requires_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __eo_requires x (__seq_empty (__eo_typeof x)) x ≠ Term.Stuck) :
    __smtx_typeof
      (__eo_to_smt (__eo_requires x (__seq_empty (__eo_typeof x)) x)) =
        SmtType.Seq T := by
  rw [eo_requires_eq_result_of_ne_stuck x (__seq_empty (__eo_typeof x)) x hElim]
  exact hxTy

private theorem smt_typeof_str_nary_elim_concat_of_seq_ne_stuck
    (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss) ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt
      (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t
        (mkConcat t ss))) = SmtType.Seq T := by
  have hConcatNN :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) ≠ SmtType.None := by
    rw [hConcatTy]
    exact seq_ne_none T
  rcases str_concat_args_of_non_none t ss hConcatNN with ⟨U, htTyU, hssTyU⟩
  have hConcatTyU :
      __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq U :=
    smt_typeof_str_concat_of_seq t ss U htTyU hssTyU
  have hUT : U = T := by
    have hSeq : SmtType.Seq U = SmtType.Seq T := by
      rw [← hConcatTyU, hConcatTy]
    injection hSeq
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    simpa [hUT] using htTyU
  rcases eo_ite_cases_of_ne_stuck
      (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) hElim with
    hCond | hCond
  · rw [hCond, eo_ite_true]
    exact htTy
  · rw [hCond, eo_ite_false]
    exact hConcatTy

private theorem smt_typeof_str_nary_elim_of_seq (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElimNN : __smtx_typeof (__eo_to_smt (__str_nary_elim x)) ≠
      SmtType.None) :
    __smtx_typeof (__eo_to_smt (__str_nary_elim x)) = SmtType.Seq T := by
  have hElim : __str_nary_elim x ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation (__str_nary_elim x) hElimNN
  cases x with
  | Stuck =>
      simp [__str_nary_elim] at hElim
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simp [__str_nary_elim] at hElimNN hElim ⊢
                exact smt_typeof_str_nary_elim_concat_of_seq t a T hxTy
                  hElimNN hElim
              · simp [__str_nary_elim, hop] at hElimNN hElim ⊢
                exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
          | _ =>
              simp [__str_nary_elim] at hElimNN hElim ⊢
              exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
      | _ =>
          simp [__str_nary_elim] at hElimNN hElim ⊢
          exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
  | _ =>
      simp [__str_nary_elim] at hElimNN hElim ⊢
      exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim

private theorem smt_typeof_str_nary_elim_of_seq_ne_stuck
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_elim x)) = SmtType.Seq T := by
  cases x with
  | Stuck =>
      simp [__str_nary_elim] at hElim
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                simp [__str_nary_elim] at hElim ⊢
                exact smt_typeof_str_nary_elim_concat_of_seq_ne_stuck
                  t a T hxTy hElim
              · simp [__str_nary_elim, hop] at hElim ⊢
                exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
          | _ =>
              simp [__str_nary_elim] at hElim ⊢
              exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
      | _ =>
          simp [__str_nary_elim] at hElim ⊢
          exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim
  | _ =>
      simp [__str_nary_elim] at hElim ⊢
      exact smt_typeof_str_nary_elim_requires_of_seq _ T hxTy hElim

private theorem smt_typeof_str_nary_elim_list_rev_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck)
    (hElim :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) a) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) a))) =
      SmtType.Seq T := by
  have hRevTy :
      __smtx_typeof
          (__eo_to_smt (__eo_list_rev (Term.UOp UserOp.str_concat) a)) =
        SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq a T hList haTy hRev
  exact smt_typeof_str_nary_elim_of_seq_ne_stuck
    (__eo_list_rev (Term.UOp UserOp.str_concat) a) T hRevTy hElim

private theorem smt_typeof_str_nary_elim_list_rev_list_rev_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck)
    (hElim :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a)) ≠
        Term.Stuck) :
    __smtx_typeof
        (__eo_to_smt
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) a)))) =
      SmtType.Seq T := by
  have hRevRevTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat) a))) =
        SmtType.Seq T :=
    smt_typeof_list_rev_list_rev_str_concat_of_seq a T hList haTy hRev
  exact smt_typeof_str_nary_elim_of_seq_ne_stuck
    (__eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) a)) T hRevRevTy hElim

private theorem eo_has_bool_type_rev_elim_eq_of_seq
    (x y : Term) (T : SmtType)
    (hxList :
      __eo_is_list (Term.UOp UserOp.str_concat) x = Term.Boolean true)
    (hyList :
      __eo_is_list (Term.UOp UserOp.str_concat) y = Term.Boolean true)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hxRev : __eo_list_rev (Term.UOp UserOp.str_concat) x ≠ Term.Stuck)
    (hyRev : __eo_list_rev (Term.UOp UserOp.str_concat) y ≠ Term.Stuck)
    (hxElim :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) x) ≠
        Term.Stuck)
    (hyElim :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) y) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) x))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) y))) := by
  have hxElimTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) x))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_of_seq x T hxList hxTy hxRev hxElim
  have hyElimTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) y))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_of_seq y T hyList hyTy hyRev hyElim
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hxElimTy, hyElimTy]
  · rw [hxElimTy]
    exact seq_ne_none T

private theorem eo_has_bool_type_double_rev_elim_eq_of_seq
    (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck)
    (hElimRevRev :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a)) ≠
        Term.Stuck)
    (hElimA : __str_nary_elim a ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a)))
        (__str_nary_elim a)) := by
  have hLeftTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__eo_list_rev (Term.UOp UserOp.str_concat) a)))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_list_rev_of_seq a T hList haTy
      hRev hElimRevRev
  have hRightTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim a)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck a T haTy hElimA
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hLeftTy, hRightTy]
  · rw [hLeftTy]
    exact seq_ne_none T

private theorem eo_interprets_double_rev_elim_eq_of_list
    (M : SmtModel) (a : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hRev : __eo_list_rev (Term.UOp UserOp.str_concat) a ≠ Term.Stuck)
    (hElimA : __str_nary_elim a ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) a)))
        (__str_nary_elim a)) true := by
  have hRevRevEq :=
    eo_list_rev_list_rev_str_concat_eq_of_list_true a hList hRev
  rw [hRevRevEq]
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim a)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck a T haTy hElimA
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim a) (__str_nary_elim a)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · rw [hElimTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim a) (__str_nary_elim a) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim a))))

private theorem eo_interprets_double_rev_intro_elim_eq_of_str_concat
    (M : SmtModel) (head tail : Term) (T : SmtType)
    (hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head tail)) = SmtType.Seq T)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_nary_intro (mkConcat head tail)) ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro (mkConcat head tail)))))
        (__str_nary_elim (__str_nary_intro (mkConcat head tail)))) true := by
  rcases str_concat_args_of_seq_type head tail T hConsTy with
    ⟨hHeadTy, hTailTy⟩
  have hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
        Term.Stuck := by
    simpa [__str_nary_intro] using hRevIntro
  have hConsList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (mkConcat head tail) hRevCons
  have hElimCons : __str_nary_elim (mkConcat head tail) ≠ Term.Stuck :=
    str_nary_elim_str_concat_cons_ne_stuck_of_seq head tail T hHeadTy
      hTailTy
  simpa [__str_nary_intro] using
    eo_interprets_double_rev_elim_eq_of_list M (mkConcat head tail) T
      hConsList hConsTy hRevCons hElimCons

private theorem eo_has_bool_type_double_rev_intro_elim_eq_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck)
    (hElimRevRev :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))) ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) := by
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck x T hxTy hIntroNN hIntro
  have hElimIntro :
      __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq x T hxTy hIntroNN
      hIntro
  have hIntroList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro x) hRevIntro
  exact eo_has_bool_type_double_rev_elim_eq_of_seq
    (__str_nary_intro x) T hIntroList hIntroTy hRevIntro hElimRevRev
    hElimIntro

private theorem eo_has_bool_type_rev_cons_snoc_of_seq
    (head tail : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
        Term.Stuck)
    (hRevTail :
      __eo_list_rev (Term.UOp UserOp.str_concat) tail ≠ Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)) ≠
        Term.Stuck)
    (hElimTail :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)))
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
          head)) := by
  have hConsList :
      __eo_is_list (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        Term.Boolean true :=
    eo_is_list_cons_self_true_of_tail_list
      (Term.UOp UserOp.str_concat) head tail (by decide) hTailList
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head tail)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head tail T hHeadTy hTailTy
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (mkConcat head tail)))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_of_seq (mkConcat head tail) T
      hConsList hConsTy hRevCons hElimCons
  have hTailElimTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) tail))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_list_rev_of_seq tail T hTailList hTailTy
      hRevTail hElimTail
  have hRhsTy :
      __smtx_typeof
          (__eo_to_smt
            (mkConcat
              (__str_nary_elim
                (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
              head)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq
      (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
      head T hTailElimTy hHeadTy
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hLhsTy, hRhsTy]
  · rw [hLhsTy]
    exact seq_ne_none T

private theorem eo_has_bool_type_str_concat_list_nil_left_empty_of_seq
    (nil x : Term) (T : SmtType)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (mkEq (mkConcat nil x) x) := by
  have hConcatTy :
      __smtx_typeof (__eo_to_smt (mkConcat nil x)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq nil x T hNilTy hxTy
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hConcatTy, hxTy]
  · rw [hConcatTy]
    exact seq_ne_none T

private theorem eo_has_bool_type_str_concat_list_nil_right_empty_of_seq
    (x nil : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T) :
    RuleProofs.eo_has_bool_type (mkEq (mkConcat x nil) x) := by
  have hConcatTy :
      __smtx_typeof (__eo_to_smt (mkConcat x nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq x nil T hxTy hNilTy
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hConcatTy, hxTy]
  · rw [hConcatTy]
    exact seq_ne_none T

private theorem eo_has_bool_type_str_nary_elim_eq_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type (mkEq (__str_nary_elim x) x) := by
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim x)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck x T hxTy hElim
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · rw [hElimTy, hxTy]
  · rw [hElimTy]
    exact seq_ne_none T

private theorem eo_interprets_str_nary_elim_rev_rec_nil_eq
    (M : SmtModel) (nil acc : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hAccTy : __smtx_typeof (__eo_to_smt acc) = SmtType.Seq T)
    (hElimAcc : __str_nary_elim acc ≠ Term.Stuck) :
    eo_interprets M
      (mkEq (__str_nary_elim (__eo_list_rev_rec nil acc))
        (__str_nary_elim acc)) true := by
  have hRecEq :
      __eo_list_rev_rec nil acc = acc :=
    eo_list_rev_rec_str_concat_nil_eq_of_nil_true nil acc hNil
  rw [hRecEq]
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim acc)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck acc T hAccTy hElimAcc
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim acc) (__str_nary_elim acc)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · rw [hElimTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim acc) (__str_nary_elim acc) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim acc))))

private theorem eo_interprets_rev_cons_snoc_of_list_nil
    (M : SmtModel) (hM : model_total_typed M) (head nil : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
        Term.Stuck)
    (hRevNil :
      __eo_list_rev (Term.UOp UserOp.str_concat) nil ≠ Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)) ≠
        Term.Stuck)
    (hElimNil :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) nil) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) nil))
          head)) true := by
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true :=
    eo_is_list_str_concat_nil_true_of_nil_true nil hNil
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil)))
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) nil))
          head)) :=
    eo_has_bool_type_rev_cons_snoc_of_seq head nil T hHeadTy hNilList
      hNilTy hRevCons hRevNil hElimCons hElimNil
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
        mkConcat head nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck head nil hNil hRevCons
  have hRevNilEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) nil = nil :=
    eo_list_rev_str_concat_nil_eq_of_nil_true nil hNil
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hElimCons' : __str_nary_elim (mkConcat head nil) ≠ Term.Stuck := by
    simpa [hRevConsEq] using hElimCons
  have hElimNil' : __str_nary_elim nil ≠ Term.Stuck := by
    simpa [hRevNilEq] using hElimNil
  let lhs :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil))
  let rhs :=
    mkConcat
      (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) nil))
      head
  have hLhsToCons : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil))) := by
    subst lhs
    rw [hRevConsEq]
    exact smt_value_rel_str_nary_elim M hM (mkConcat head nil) T
      hConsTy hElimCons'
  have hConsToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) :=
    smt_value_rel_str_concat_list_nil_right_empty M hM head nil T
      hHeadTy hNil hNilTy
  have hLhsToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt head)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt (mkConcat head nil)))
      (__smtx_model_eval M (__eo_to_smt head)) hLhsToCons hConsToHead
  have hElimNilTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim nil)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck nil T hNilTy hElimNil'
  have hElimNilEmpty : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim nil)))
      (SmtValue.Seq (SmtSeq.empty T)) :=
    smt_value_rel_str_nary_elim_list_nil_empty M hM nil T hNil hNilTy
      hElimNil'
  have hRhsToHead : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt rhs))
      (__smtx_model_eval M (__eo_to_smt head)) := by
    subst rhs
    rw [hRevNilEq]
    exact smt_value_rel_str_concat_left_of_rel_empty M hM
      (__str_nary_elim nil) head T hElimNilTy hHeadTy hElimNilEmpty
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt rhs)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt lhs))
      (__smtx_model_eval M (__eo_to_smt head))
      (__smtx_model_eval M (__eo_to_smt rhs)) hLhsToHead
      (RuleProofs.smt_value_rel_symm
        (__smtx_model_eval M (__eo_to_smt rhs))
        (__smtx_model_eval M (__eo_to_smt head)) hRhsToHead)
  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool hRel

private theorem eo_interprets_str_concat_right_empty_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat x (__seq_empty (__eo_typeof x))) x)) :
    eo_interprets M (mkEq (mkConcat x (__seq_empty (__eo_typeof x))) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat x (__seq_empty (__eo_typeof x))) x hBool
    (smt_value_rel_str_concat_right_empty M hM x T hxTy)

private theorem eo_interprets_str_concat_left_empty_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (mkConcat (__seq_empty (__eo_typeof x)) x) x)) :
    eo_interprets M (mkEq (mkConcat (__seq_empty (__eo_typeof x)) x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (mkConcat (__seq_empty (__eo_typeof x)) x) x hBool
    (smt_value_rel_str_concat_left_empty M hM x T hxTy)

private theorem eo_interprets_str_concat_list_nil_left_empty_of_bool
    (M : SmtModel) (hM : model_total_typed M) (nil x : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat nil x) x)) :
    eo_interprets M (mkEq (mkConcat nil x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (mkConcat nil x) x hBool
    (smt_value_rel_str_concat_list_nil_left_empty M hM nil x T
      hNil hNilTy hxTy)

private theorem eo_interprets_str_concat_list_nil_right_empty_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x nil : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat x nil) x)) :
    eo_interprets M (mkEq (mkConcat x nil) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (mkConcat x nil) x hBool
    (smt_value_rel_str_concat_list_nil_right_empty M hM x nil T
      hxTy hNil hNilTy)

private theorem eo_interprets_str_nary_intro_ite_eq_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro :
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (mkConcat x (__seq_empty (__eo_typeof x))) ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (mkConcat x (__seq_empty (__eo_typeof x))))
        x)) :
    eo_interprets M
      (mkEq
        (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (mkConcat x (__seq_empty (__eo_typeof x))))
        x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
      (mkConcat x (__seq_empty (__eo_typeof x)))) x hBool
    (smt_value_rel_str_nary_intro_ite M hM x T hxTy hIntro)

private theorem eo_interprets_str_nary_elim_concat_ite_eq_of_bool
    (M : SmtModel) (hM : model_total_typed M) (t ss : Term) (T : SmtType)
    (hConcatTy : __smtx_typeof (__eo_to_smt (mkConcat t ss)) = SmtType.Seq T)
    (hElim :
      __eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss) ≠
        Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))
        (mkConcat t ss))) :
    eo_interprets M
      (mkEq
        (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))
        (mkConcat t ss)) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__eo_ite (__eo_eq ss (__seq_empty (__eo_typeof t))) t (mkConcat t ss))
    (mkConcat t ss) hBool
    (smt_value_rel_str_nary_elim_concat_ite M hM t ss T hConcatTy hElim)

private theorem eo_interprets_str_nary_elim_requires_eq_of_bool
    (M : SmtModel) (t : Term)
    (hElim : __eo_requires t (__seq_empty (__eo_typeof t)) t ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__eo_requires t (__seq_empty (__eo_typeof t)) t) t)) :
    eo_interprets M
      (mkEq (__eo_requires t (__seq_empty (__eo_typeof t)) t) t) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__eo_requires t (__seq_empty (__eo_typeof t)) t) t hBool
    (smt_value_rel_str_nary_elim_requires M t hElim)

private theorem eo_interprets_str_nary_intro_eq_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (__str_nary_intro x) x)) :
    eo_interprets M (mkEq (__str_nary_intro x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (__str_nary_intro x) x hBool
    (smt_value_rel_str_nary_intro M hM x T hxTy hIntro)

private theorem eo_interprets_str_nary_elim_eq_of_bool
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hElim : __str_nary_elim x ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type (mkEq (__str_nary_elim x) x)) :
    eo_interprets M (mkEq (__str_nary_elim x) x) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (__str_nary_elim x) x hBool
    (smt_value_rel_str_nary_elim M hM x T hxTy hElim)

private theorem eo_interprets_str_nary_elim_intro_eq_of_seq
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hElimIntro : __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck) :
    eo_interprets M (mkEq (__str_nary_elim (__str_nary_intro x)) x)
      true := by
  have hIntroTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq_ne_stuck x T hxTy hIntroNN hIntro
  have hElimIntroTy :
      __smtx_typeof
          (__eo_to_smt (__str_nary_elim (__str_nary_intro x))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (__str_nary_intro x) T
      hIntroTy hElimIntro
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__str_nary_intro x)) x) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimIntroTy, hxTy]
    · rw [hElimIntroTy]
      exact seq_ne_none T
  have hElimRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__str_nary_elim (__str_nary_intro x))))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x))) :=
    smt_value_rel_str_nary_elim M hM (__str_nary_intro x) T
      hIntroTy hElimIntro
  have hIntroRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
        (__smtx_model_eval M (__eo_to_smt x)) :=
    smt_value_rel_str_nary_intro M hM x T hxTy hIntro
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim (__str_nary_intro x)) x hBool
    (RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M
        (__eo_to_smt (__str_nary_elim (__str_nary_intro x))))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt x)) hElimRel hIntroRel)

private theorem eo_interprets_str_nary_elim_intro_eq_of_seq_ne_stuck
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    eo_interprets M (mkEq (__str_nary_elim (__str_nary_intro x)) x)
      true := by
  exact eo_interprets_str_nary_elim_intro_eq_of_seq M hM x T hxTy
    hIntroNN hIntro
    (str_nary_elim_str_nary_intro_ne_stuck_of_seq x T hxTy
      hIntroNN hIntro)

private theorem eo_interprets_double_rev_intro_elim_eq_of_rel
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck)
    (hElimRevRev :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))) ≠ Term.Stuck)
    (hRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro x)))))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  let revrev :=
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x))
  let intro := __str_nary_intro x
  have hIntroTy :
      __smtx_typeof (__eo_to_smt intro) = SmtType.Seq T := by
    simpa [intro] using
      smt_typeof_str_nary_intro_of_seq_ne_stuck x T hxTy hIntroNN hIntro
  have hRevRevTy :
      __smtx_typeof (__eo_to_smt revrev) = SmtType.Seq T := by
    simpa [revrev, intro] using
      smt_typeof_double_rev_str_nary_intro_of_seq x T hxTy hIntroNN
        hIntro hRevIntro
  have hElimIntro : __str_nary_elim intro ≠ Term.Stuck := by
    simpa [intro] using
      str_nary_elim_str_nary_intro_ne_stuck_of_seq x T hxTy hIntroNN
        hIntro
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim revrev) (__str_nary_elim intro)) := by
    simpa [revrev, intro] using
      eo_has_bool_type_double_rev_intro_elim_eq_of_seq x T hxTy hIntroNN
        hIntro hRevIntro hElimRevRev
  have hLeftRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim revrev)))
        (__smtx_model_eval M (__eo_to_smt revrev)) :=
    smt_value_rel_str_nary_elim M hM revrev T hRevRevTy
      (by simpa [revrev] using hElimRevRev)
  have hRightRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro)))
        (__smtx_model_eval M (__eo_to_smt intro)) :=
    smt_value_rel_str_nary_elim M hM intro T hIntroTy hElimIntro
  have hAllRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim revrev)))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim revrev)))
      (__smtx_model_eval M (__eo_to_smt revrev))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro)))
      hLeftRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt revrev))
        (__smtx_model_eval M (__eo_to_smt intro))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro)))
        (by simpa [revrev, intro] using hRel)
        (RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim intro)))
          (__smtx_model_eval M (__eo_to_smt intro)) hRightRel))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim revrev) (__str_nary_elim intro) hBool hAllRel

private theorem eo_interprets_double_rev_elim_eq_of_cons_nil
    (M : SmtModel) (head nil : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat head nil))))
        (__str_nary_elim (mkConcat head nil))) true := by
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head nil) =
        mkConcat head nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck head nil hNil hRevCons
  have hConsTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hElimCons :
      __str_nary_elim (mkConcat head nil) ≠ Term.Stuck :=
    str_nary_elim_str_concat_cons_ne_stuck_of_seq head nil T hHeadTy
      hNilTy
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (mkConcat head nil))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (mkConcat head nil) T
      hConsTy hElimCons
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (mkConcat head nil))
        (__str_nary_elim (mkConcat head nil))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · rw [hElimTy]
      exact seq_ne_none T
  rw [hRevEq, hRevEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim (mkConcat head nil))
    (__str_nary_elim (mkConcat head nil)) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim (mkConcat head nil)))))

private theorem eo_is_list_nil_str_concat_seq_empty_of_ne_stuck
    (A : Term) (hEmpty : __seq_empty A ≠ Term.Stuck) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
      (__seq_empty A) = Term.Boolean true := by
  cases A <;>
    simp [__seq_empty, __eo_is_list_nil, __eo_is_list_nil_str_concat,
      __eo_eq, native_teq] at hEmpty ⊢
  case Apply f a =>
    cases f with
    | UOp op =>
        cases op <;> try rfl
        case Seq =>
          cases a <;> try rfl
          case UOp op =>
            cases op <;> try rfl
    | _ =>
        rfl

private theorem eo_is_list_nil_str_concat_seq_empty_typeof_of_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
      (__seq_empty (__eo_typeof x)) = Term.Boolean true := by
  exact eo_is_list_nil_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
    (seq_empty_typeof_ne_stuck_of_smt_type_seq x T hxTy)

private theorem eo_interprets_double_rev_elim_eq_of_nil
    (M : SmtModel) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hElimNil : __str_nary_elim nil ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat) nil)))
        (__str_nary_elim nil)) true := by
  have hRevEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) nil = nil :=
    eo_list_rev_str_concat_nil_eq_of_nil_true nil hNil
  have hElimTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim nil)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck nil T hNilTy hElimNil
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim nil) (__str_nary_elim nil)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · rw [hElimTy]
      exact seq_ne_none T
  rw [hRevEq, hRevEq]
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim nil) (__str_nary_elim nil) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim nil))))

private theorem eo_interprets_double_rev_intro_elim_eq_of_default
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck)
    (hDefault :
      __str_nary_intro x =
        __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            (__seq_empty (__eo_typeof x)))) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  let empty := __seq_empty (__eo_typeof x)
  have hEmptyNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
        Term.Boolean true := by
    simpa [empty] using
      eo_is_list_nil_str_concat_seq_empty_typeof_of_seq x T hxTy
  have hIntroIte :
      __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) ≠ Term.Stuck := by
    simpa [empty, hDefault] using hIntro
  rcases eo_ite_cases_of_ne_stuck (__eo_eq x empty) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)
      hIntroIte with hCond | hCond
  · have hEmptyEq : empty = x :=
      eq_of_eo_eq_true_local x empty hCond
    have hIntroEq : __str_nary_intro x = x := by
      rw [hDefault]
      simpa [empty, hCond, eo_ite_true]
    have hXNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) x =
          Term.Boolean true := by
      simpa [hEmptyEq] using hEmptyNil
    have hElimIntro :
        __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck :=
      str_nary_elim_str_nary_intro_ne_stuck_of_seq x T hxTy hIntroNN
        hIntro
    have hElimX : __str_nary_elim x ≠ Term.Stuck := by
      simpa [hIntroEq] using hElimIntro
    simpa [hIntroEq] using
      eo_interprets_double_rev_elim_eq_of_nil M x T hXNil hxTy hElimX
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntroIte
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty = mkConcat x empty :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hIntroEq : __str_nary_intro x = mkConcat x empty := by
      rw [hDefault]
      simpa [empty, hCond, eo_ite_false, hApplyEq]
    have hConcatNN :
        __smtx_typeof (__eo_to_smt (mkConcat x empty)) ≠ SmtType.None := by
      simpa [hIntroEq] using hIntroNN
    rcases str_concat_args_of_non_none x empty hConcatNN with
      ⟨U, hxTyU, hEmptyTyU⟩
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hxTyU, hxTy]
      injection hSeq
    have hEmptyTy :
        __smtx_typeof (__eo_to_smt empty) = SmtType.Seq T := by
      simpa [hUT] using hEmptyTyU
    simpa [hIntroEq, empty] using
      eo_interprets_double_rev_elim_eq_of_cons_nil M x empty T hxTy
        hEmptyNil hEmptyTy
        (by simpa [hIntroEq, empty] using hRevIntro)

private theorem str_nary_intro_eq_default_of_not_str_concat (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __str_nary_intro x =
      __eo_ite (__eo_eq x (__seq_empty (__eo_typeof x))) x
        (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          (__seq_empty (__eo_typeof x))) := by
  cases x with
  | Stuck =>
      rfl
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                exact False.elim (hNotConcat ⟨t, a, rfl⟩)
              · simp [__str_nary_intro, hop]
          | _ =>
              simp [__str_nary_intro]
      | _ =>
          simp [__str_nary_intro]
  | _ =>
      simp [__str_nary_intro]

private theorem str_nary_elim_eq_default_of_not_str_concat (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    __str_nary_elim x =
      __eo_requires x (__seq_empty (__eo_typeof x)) x := by
  cases x with
  | Stuck =>
      rfl
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp op =>
              by_cases hop : op = UserOp.str_concat
              · subst op
                exact False.elim (hNotConcat ⟨t, a, rfl⟩)
              · simp [__str_nary_elim, hop]
          | _ =>
              simp [__str_nary_elim]
      | _ =>
          simp [__str_nary_elim]
  | _ =>
      simp [__str_nary_elim]

private theorem str_nary_elim_str_nary_intro_eq_of_not_str_concat
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_elim (__str_nary_intro x) = x := by
  let empty := __seq_empty (__eo_typeof x)
  have hIntroDefault :
      __str_nary_intro x =
        __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) := by
    simpa [empty] using
      str_nary_intro_eq_default_of_not_str_concat x hNotConcat
  have hElimDefault :
      __str_nary_elim x = __eo_requires x empty x := by
    simpa [empty] using
      str_nary_elim_eq_default_of_not_str_concat x hNotConcat
  have hIntroIte :
      __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) ≠ Term.Stuck := by
    simpa [hIntroDefault] using hIntro
  rcases eo_ite_cases_of_ne_stuck (__eo_eq x empty) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)
      hIntroIte with hCond | hCond
  · have hEmptyEq : empty = x :=
      eq_of_eo_eq_true_local x empty hCond
    have hxNonStuck : x ≠ Term.Stuck :=
      str_nary_intro_arg_ne_stuck_of_ne_stuck x hIntro
    have hIntroEq : __str_nary_intro x = x := by
      rw [hIntroDefault]
      simpa [hCond, eo_ite_true]
    rw [hIntroEq, hElimDefault, hEmptyEq]
    exact eo_requires_self_eq_of_ne_stuck x x hxNonStuck
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntroIte
    have hEmptyNonStuck : empty ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty = mkConcat x empty :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hIntroEq : __str_nary_intro x = mkConcat x empty := by
      rw [hIntroDefault]
      simpa [hCond, eo_ite_false, hApplyEq]
    have hEmptyEqTrue : __eo_eq empty empty = Term.Boolean true :=
      eo_eq_self_true_of_ne_stuck empty hEmptyNonStuck
    rw [hIntroEq]
    change __eo_ite (__eo_eq empty empty) x (mkConcat x empty) = x
    rw [hEmptyEqTrue, eo_ite_true]

private theorem str_nary_intro_not_str_concat_cases
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_intro x = x ∨
      ∃ empty,
        __str_nary_intro x = mkConcat x empty ∧
          __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
            Term.Boolean true := by
  let empty := __seq_empty (__eo_typeof x)
  have hIntroDefault :
      __str_nary_intro x =
        __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) := by
    simpa [empty] using
      str_nary_intro_eq_default_of_not_str_concat x hNotConcat
  have hIntroIte :
      __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) ≠ Term.Stuck := by
    simpa [hIntroDefault] using hIntro
  rcases eo_ite_cases_of_ne_stuck (__eo_eq x empty) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)
      hIntroIte with hCond | hCond
  · left
    rw [hIntroDefault]
    simp [hCond, eo_ite_true]
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntroIte
    have hEmptyNonStuck : empty ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty = mkConcat x empty :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hIntroEq : __str_nary_intro x = mkConcat x empty := by
      rw [hIntroDefault]
      simpa [hCond, eo_ite_false, hApplyEq]
    have hEmptyNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
        (by simpa [empty] using hEmptyNonStuck)
    exact Or.inr ⟨empty, hIntroEq, hEmptyNil⟩

private theorem str_nary_intro_not_str_concat_cases_typeof_empty
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_intro x = x ∨
      __str_nary_intro x = mkConcat x (__seq_empty (__eo_typeof x)) ∧
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
            (__seq_empty (__eo_typeof x)) =
          Term.Boolean true := by
  let empty := __seq_empty (__eo_typeof x)
  have hIntroDefault :
      __str_nary_intro x =
        __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) := by
    simpa [empty] using
      str_nary_intro_eq_default_of_not_str_concat x hNotConcat
  have hIntroIte :
      __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) ≠ Term.Stuck := by
    simpa [hIntroDefault] using hIntro
  rcases eo_ite_cases_of_ne_stuck (__eo_eq x empty) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)
      hIntroIte with hCond | hCond
  · left
    rw [hIntroDefault]
    simp [hCond, eo_ite_true]
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntroIte
    have hEmptyNonStuck : empty ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty = mkConcat x empty :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hIntroEq : __str_nary_intro x = mkConcat x empty := by
      rw [hIntroDefault]
      simpa [hCond, eo_ite_false, hApplyEq]
    have hEmptyNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
        (by simpa [empty] using hEmptyNonStuck)
    right
    exact ⟨by simpa [empty] using hIntroEq,
      by simpa [empty] using hEmptyNil⟩

private theorem str_nary_intro_not_str_concat_cases_eq_empty
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    (__str_nary_intro x = x ∧
        x = __seq_empty (__eo_typeof x)) ∨
      __str_nary_intro x = mkConcat x (__seq_empty (__eo_typeof x)) ∧
        __eo_is_list_nil (Term.UOp UserOp.str_concat)
            (__seq_empty (__eo_typeof x)) =
          Term.Boolean true := by
  let empty := __seq_empty (__eo_typeof x)
  have hIntroDefault :
      __str_nary_intro x =
        __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) := by
    simpa [empty] using
      str_nary_intro_eq_default_of_not_str_concat x hNotConcat
  have hIntroIte :
      __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) ≠ Term.Stuck := by
    simpa [hIntroDefault] using hIntro
  rcases eo_ite_cases_of_ne_stuck (__eo_eq x empty) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)
      hIntroIte with hCond | hCond
  · have hEmptyEq : empty = x :=
      eq_of_eo_eq_true_local x empty hCond
    left
    refine ⟨?_, ?_⟩
    · rw [hIntroDefault]
      simp [hCond, eo_ite_true]
    · exact hEmptyEq.symm
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntroIte
    have hEmptyNonStuck : empty ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty = mkConcat x empty :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hIntroEq : __str_nary_intro x = mkConcat x empty := by
      rw [hIntroDefault]
      simpa [hCond, eo_ite_false, hApplyEq]
    have hEmptyNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
        (by simpa [empty] using hEmptyNonStuck)
    right
    exact ⟨by simpa [empty] using hIntroEq,
      by simpa [empty] using hEmptyNil⟩

private theorem str_nary_intro_not_str_concat_eq_self_or_empty_typeof_of_seq_wf
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hTInh : type_inhabited T)
    (hTWf : __smtx_type_wf T = true)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_intro x = x ∨
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None := by
  rcases str_nary_intro_not_str_concat_cases_typeof_empty x hNotConcat
      hIntro with hIntroEq | _hIntroConcat
  · exact Or.inl hIntroEq
  · exact Or.inr
      (seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf x T
        hxTy hTInh hTWf)

private theorem str_nary_intro_not_str_concat_eq_self_or_has_smt_translation_of_seq_wf
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hTInh : type_inhabited T)
    (hTWf : __smtx_type_wf T = true)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __str_nary_intro x = x ∨
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
        SmtType.None := by
  rcases
      str_nary_intro_not_str_concat_eq_self_or_empty_typeof_of_seq_wf
        x T hxTy hTInh hTWf hNotConcat hIntro with
    hIntroEq | hEmptyNN
  · exact Or.inl hIntroEq
  · exact Or.inr
      (str_nary_intro_has_smt_translation_of_seq_empty_typeof x T hxTy
        hEmptyNN hIntro)

private theorem str_nary_intro_has_smt_translation_of_seq_wf
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hTInh : type_inhabited T)
    (hTWf : __smtx_type_wf T = true)
    (hIntro : __str_nary_intro x ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠
      SmtType.None := by
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, hX⟩
    subst x
    have hNN :
        __smtx_typeof (__eo_to_smt (mkConcat head tail)) ≠
          SmtType.None := by
      rw [hxTy]
      exact seq_ne_none T
    simpa [__str_nary_intro] using hNN
  · rcases
      str_nary_intro_not_str_concat_eq_self_or_has_smt_translation_of_seq_wf
        x T hxTy hTInh hTWf hConcat hIntro with
      hIntroEq | hIntroNN
    · rw [hIntroEq, hxTy]
      exact seq_ne_none T
    · exact hIntroNN

private theorem concatEq_seq_pack_of_seq_wf
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hTInh : type_inhabited T)
    (hTWf : __smtx_type_wf T = true)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck) :
    ∃ U,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq U ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact ⟨T, hsTy,
    str_nary_intro_has_smt_translation_of_seq_wf s T hsTy hTInh hTWf
      hIntroS,
    str_nary_intro_has_smt_translation_of_seq_wf t T htTy hTInh hTWf
      hIntroT⟩

private theorem smt_typeof_seq_of_not_str_concat_intro_eq_self
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hIntroEq : __str_nary_intro x = x)
    (hXNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  rcases str_nary_intro_not_str_concat_cases_eq_empty x hNotConcat
      hIntro with ⟨_hIntroEq, hEmptyEq⟩ | ⟨hIntroConcat, _hEmptyNil⟩
  · exact smt_typeof_eq_seq_empty_seq_of_non_none x (__eo_typeof x)
      hEmptyEq hXNN
  · have hxConcat : x = mkConcat x (__seq_empty (__eo_typeof x)) :=
      hIntroEq.symm.trans hIntroConcat
    exact False.elim (hNotConcat
      ⟨x, __seq_empty (__eo_typeof x), hxConcat⟩)

private theorem concatEq_seq_pack_of_not_concat_intros_eq_self
    (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroSEq : __str_nary_intro s = s)
    (hIntroTEq : __str_nary_intro t = t) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
      hPremBool with ⟨hSame, hSNN⟩
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSame]
    exact hSNN
  rcases smt_typeof_seq_of_not_str_concat_intro_eq_self s hSNotConcat
      hIntroS hIntroSEq hSNN with ⟨T, hsTy⟩
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None := by
    simpa [hIntroSEq] using hSNN
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
    simpa [hIntroTEq] using hTNN
  exact ⟨T, hsTy, hIntroSNN, hIntroTNN⟩

private theorem concatEq_seq_pack_of_not_concat_left_intro_eq_self_right_empty_typeof
    (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroSEq : __str_nary_intro s = s)
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
      hPremBool with ⟨hSame, hSNN⟩
  rcases smt_typeof_seq_of_not_str_concat_intro_eq_self s hSNotConcat
      hIntroS hIntroSEq hSNN with ⟨T, hsTy⟩
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    rw [← hSame, hsTy]
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None := by
    simpa [hIntroSEq] using hSNN
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof t T htTy
      hEmptyTNN hIntroT
  exact ⟨T, hsTy, hIntroSNN, hIntroTNN⟩

private theorem concatEq_seq_pack_of_not_concat_right_intro_eq_self_left_empty_typeof
    (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hIntroTEq : __str_nary_intro t = t)
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
      hPremBool with ⟨hSame, hSNN⟩
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSame]
    exact hSNN
  rcases smt_typeof_seq_of_not_str_concat_intro_eq_self t hTNotConcat
      hIntroT hIntroTEq hTNN with ⟨T, htTy⟩
  have hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := by
    rw [hSame, htTy]
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof s T hsTy
      hEmptySNN hIntroS
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
    simpa [hIntroTEq] using hTNN
  exact ⟨T, hsTy, hIntroSNN, hIntroTNN⟩

private theorem concatEq_seq_pack_of_empty_typeof_intros
    (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck) :
    ∃ T,
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None ∧
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t
      hPremBool with ⟨hSame, hSNN⟩
  rcases smt_typeof_seq_of_seq_empty_typeof_non_none s hSNN
      hEmptySNN with ⟨T, hsTy, _hEmptySTy⟩
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    rw [← hSame, hsTy]
  have hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof s T hsTy
      hEmptySNN hIntroS
  have hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None :=
    str_nary_intro_has_smt_translation_of_seq_empty_typeof t T htTy
      hEmptyTNN hIntroT
  exact ⟨T, hsTy, hIntroSNN, hIntroTNN⟩

private theorem str_nary_intro_not_str_concat_smt_cases
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None) :
    (__smtx_typeof (__eo_to_smt x) ≠ SmtType.None) ∨
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None := by
  rcases str_nary_intro_not_str_concat_cases_typeof_empty x hNotConcat
      hIntro with hIntroEq | ⟨hIntroEq, _hEmptyNil⟩
  · left
    simpa [hIntroEq] using hIntroNN
  · right
    have hConcatNN :
        __smtx_typeof
            (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))) ≠
          SmtType.None := by
      simpa [hIntroEq] using hIntroNN
    rcases str_concat_args_of_non_none x (__seq_empty (__eo_typeof x))
        hConcatNN with
      ⟨_T, _hxTy, hEmptyTy⟩
    rw [hEmptyTy]
    exact seq_ne_none _T

private theorem str_nary_intro_not_str_concat_eq_or_empty_smt
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None) :
    __str_nary_intro x = x ∨
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) ≠
        SmtType.None := by
  rcases str_nary_intro_not_str_concat_cases_typeof_empty x hNotConcat
      hIntro with hIntroEq | ⟨hIntroEq, _hEmptyNil⟩
  · exact Or.inl hIntroEq
  · right
    have hConcatNN :
        __smtx_typeof
            (__eo_to_smt (mkConcat x (__seq_empty (__eo_typeof x)))) ≠
          SmtType.None := by
      simpa [hIntroEq] using hIntroNN
    rcases str_concat_args_of_non_none x (__seq_empty (__eo_typeof x))
        hConcatNN with
      ⟨_T, _hxTy, hEmptyTy⟩
    rw [hEmptyTy]
    exact seq_ne_none _T

private theorem eo_list_rev_str_nary_intro_eq_of_not_str_concat
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) =
      __str_nary_intro x := by
  let empty := __seq_empty (__eo_typeof x)
  have hIntroDefault :
      __str_nary_intro x =
        __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) := by
    simpa [empty] using
      str_nary_intro_eq_default_of_not_str_concat x hNotConcat
  have hIntroIte :
      __eo_ite (__eo_eq x empty) x
          (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
            empty) ≠ Term.Stuck := by
    simpa [hIntroDefault] using hIntro
  rcases eo_ite_cases_of_ne_stuck (__eo_eq x empty) x
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) empty)
      hIntroIte with hCond | hCond
  · have hEmptyEq : empty = x :=
      eq_of_eo_eq_true_local x empty hCond
    have hxNonStuck : x ≠ Term.Stuck :=
      str_nary_intro_arg_ne_stuck_of_ne_stuck x hIntro
    have hIntroEq : __str_nary_intro x = x := by
      rw [hIntroDefault]
      simpa [hCond, eo_ite_true]
    have hEmptyNonStuck : empty ≠ Term.Stuck := by
      simpa [hEmptyEq] using hxNonStuck
    have hEmptyEq' : __seq_empty (__eo_typeof x) = x := by
      simpa [empty] using hEmptyEq
    have hXNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) x =
          Term.Boolean true := by
      simpa [hEmptyEq'] using
        eo_is_list_nil_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
          (by simpa [empty] using hEmptyNonStuck)
    rw [hIntroEq]
    exact eo_list_rev_str_concat_nil_eq_of_nil_true x hXNil
  · have hApplyNonStuck :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty ≠ Term.Stuck := by
      simpa [hCond, eo_ite_false] using hIntroIte
    have hEmptyNonStuck : empty ≠ Term.Stuck :=
      eo_mk_apply_arg_ne_stuck_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hApplyEq :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x)
          empty = mkConcat x empty :=
      eo_mk_apply_eq_apply_of_ne_stuck
        (Term.Apply (Term.UOp UserOp.str_concat) x) empty hApplyNonStuck
    have hIntroEq : __str_nary_intro x = mkConcat x empty := by
      rw [hIntroDefault]
      simpa [hCond, eo_ite_false, hApplyEq]
    have hEmptyNil :
        __eo_is_list_nil (Term.UOp UserOp.str_concat) empty =
          Term.Boolean true :=
      eo_is_list_nil_str_concat_seq_empty_of_ne_stuck (__eo_typeof x)
        (by simpa [empty] using hEmptyNonStuck)
    rw [hIntroEq]
    exact eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck x empty
      hEmptyNil (by simpa [hIntroEq] using hRevIntro)

private theorem eo_list_rev_list_rev_str_nary_intro_eq_of_not_str_concat
    (x : Term)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    __eo_list_rev (Term.UOp UserOp.str_concat)
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x)) =
      __str_nary_intro x := by
  have hRevEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat x hNotConcat hIntro
      hRevIntro
  rw [hRevEq]
  exact hRevEq

private theorem eo_interprets_double_rev_intro_elim_eq_of_not_str_concat_smt
    (M : SmtModel) (x : Term)
    (hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  have hRevRevEq :=
    eo_list_rev_list_rev_str_nary_intro_eq_of_not_str_concat x
      hNotConcat hIntro hRevIntro
  have hElimIntroEq :
      __str_nary_elim (__str_nary_intro x) = x :=
    str_nary_elim_str_nary_intro_eq_of_not_str_concat x hNotConcat
      hIntro
  rw [hRevRevEq]
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__str_nary_intro x))
        (__str_nary_elim (__str_nary_intro x))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · simpa [hElimIntroEq] using hxNN
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim (__str_nary_intro x))
    (__str_nary_elim (__str_nary_intro x)) hBool
    (RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M
        (__eo_to_smt (__str_nary_elim (__str_nary_intro x)))))

private theorem eo_interprets_double_rev_intro_elim_eq_of_not_str_concat
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck)
    (hNotConcat : ¬ ∃ head tail : Term, x = mkConcat head tail) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  exact eo_interprets_double_rev_intro_elim_eq_of_default M x T hxTy
    hIntroNN hIntro hRevIntro
    (str_nary_intro_eq_default_of_not_str_concat x hNotConcat)

private theorem eo_interprets_double_rev_intro_elim_eq_of_seq_cases
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        (__str_nary_elim (__str_nary_intro x))) true := by
  by_cases hConcat : ∃ head tail : Term, x = mkConcat head tail
  · rcases hConcat with ⟨head, tail, hX⟩
    subst x
    exact eo_interprets_double_rev_intro_elim_eq_of_str_concat M head
      tail T hxTy hRevIntro
  · exact eo_interprets_double_rev_intro_elim_eq_of_not_str_concat M x T
      hxTy hIntroNN hIntro hRevIntro hConcat

private theorem eo_interprets_double_rev_intro_elim_eq_of_str_concat_nil
    (M : SmtModel) (head nil : Term) (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevIntro :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_nary_intro (mkConcat head nil)) ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro (mkConcat head nil)))))
        (__str_nary_elim (__str_nary_intro (mkConcat head nil)))) true := by
  simpa [__str_nary_intro] using
    eo_interprets_double_rev_elim_eq_of_cons_nil M head nil T hHeadTy
      hNil hNilTy (by simpa [__str_nary_intro] using hRevIntro)

private theorem eo_interprets_double_rev_intro_self_of_elim_intro
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hIntroNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro x)) ≠ SmtType.None)
    (hIntro : __str_nary_intro x ≠ Term.Stuck)
    (hElimIntro : __str_nary_elim (__str_nary_intro x) ≠ Term.Stuck)
    (hDoubleToIntro :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro x))))
          (__str_nary_elim (__str_nary_intro x))) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro x))))
        x) true := by
  exact RuleProofs.eo_interprets_eq_trans M
    (__str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro x))))
    (__str_nary_elim (__str_nary_intro x)) x hDoubleToIntro
    (eo_interprets_str_nary_elim_intro_eq_of_seq M hM x T hxTy
      hIntroNN hIntro hElimIntro)

private theorem eo_interprets_double_rev_intros_of_elim_intros
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None)
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hElimIntroS : __str_nary_elim (__str_nary_intro s) ≠ Term.Stuck)
    (hElimIntroT : __str_nary_elim (__str_nary_intro t) ≠ Term.Stuck)
    (hDoubleS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim (__str_nary_intro s))) true)
    (hDoubleT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim (__str_nary_intro t))) true)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  have hSelfS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          s) true :=
    eo_interprets_double_rev_intro_self_of_elim_intro M hM s T hsTy
      hIntroSNN hIntroS hElimIntroS hDoubleS
  have hSelfT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          t) true :=
    eo_interprets_double_rev_intro_self_of_elim_intro M hM t T htTy
      hIntroTNN hIntroT hElimIntroT hDoubleT
  exact eo_interprets_double_rev_intros_of_self M s t hSelfS hSelfT hST

private theorem eo_interprets_double_rev_intros_of_prog_elim_intros
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None)
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hDoubleS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim (__str_nary_intro s))) true)
    (hDoubleT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim (__str_nary_intro t))) true)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  have hIntroS : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroT : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hElimIntroS : __str_nary_elim (__str_nary_intro s) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq s T hsTy hIntroSNN
      hIntroS
  have hElimIntroT : __str_nary_elim (__str_nary_intro t) ≠ Term.Stuck :=
    str_nary_elim_str_nary_intro_ne_stuck_of_seq t T htTy hIntroTNN
      hIntroT
  exact eo_interprets_double_rev_intros_of_elim_intros M hM s t T
    hsTy htTy hIntroSNN hIntroTNN hIntroS hIntroT hElimIntroS
    hElimIntroT hDoubleS hDoubleT hST

private theorem eo_interprets_double_rev_intros_of_prog_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None)
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  have hIntroS : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroT : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hRevS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hDoubleS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim (__str_nary_intro s))) true :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M s T hsTy
      hIntroSNN hIntroS hRevS
  have hDoubleT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim (__str_nary_intro t))) true :=
    eo_interprets_double_rev_intro_elim_eq_of_seq_cases M t T htTy
      hIntroTNN hIntroT hRevT
  exact eo_interprets_double_rev_intros_of_prog_elim_intros M hM
    s t T hsTy htTy hIntroSNN hIntroTNN hProg hDoubleS hDoubleT hST

private theorem eo_interprets_double_rev_intros_of_prog_not_str_concat
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None)
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  have hIntroS : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroT : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hRevS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hDoubleS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim (__str_nary_intro s))) true :=
    eo_interprets_double_rev_intro_elim_eq_of_not_str_concat M s T
      hsTy hIntroSNN hIntroS hRevS hSNotConcat
  have hDoubleT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim (__str_nary_intro t))) true :=
    eo_interprets_double_rev_intro_elim_eq_of_not_str_concat M t T
      htTy hIntroTNN hIntroT hRevT hTNotConcat
  exact eo_interprets_double_rev_intros_of_prog_elim_intros M hM
    s t T hsTy htTy hIntroSNN hIntroTNN hProg hDoubleS hDoubleT hST

private theorem eo_interprets_double_rev_intros_of_prog_not_str_concat_smt
    (M : SmtModel) (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hST : eo_interprets M (mkEq s t) true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro s))))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__str_nary_intro t)))))
      true := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s t hPremBool with ⟨hSame, hSNN⟩
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hSame]
    exact hSNN
  have hIntroS : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroT : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hRevS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck :=
    concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hDoubleS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim (__str_nary_intro s))) true :=
    eo_interprets_double_rev_intro_elim_eq_of_not_str_concat_smt M s
      hSNN hSNotConcat hIntroS hRevS
  have hDoubleT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          (__str_nary_elim (__str_nary_intro t))) true :=
    eo_interprets_double_rev_intro_elim_eq_of_not_str_concat_smt M t
      hTNN hTNotConcat hIntroT hRevT
  have hElimIntroS :
      __str_nary_elim (__str_nary_intro s) = s :=
    str_nary_elim_str_nary_intro_eq_of_not_str_concat s hSNotConcat
      hIntroS
  have hElimIntroT :
      __str_nary_elim (__str_nary_intro t) = t :=
    str_nary_elim_str_nary_intro_eq_of_not_str_concat t hTNotConcat
      hIntroT
  have hSelfS :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          s) true := by
    simpa [hElimIntroS] using hDoubleS
  have hSelfT :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t))))
          t) true := by
    simpa [hElimIntroT] using hDoubleT
  exact eo_interprets_double_rev_intros_of_self M s t hSelfS hSelfT hST

private theorem str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) =
      mkPair (__str_nary_intro s) (__str_nary_intro t) := by
  rcases str_nary_intro_not_str_concat_cases s hSNotConcat hIntroS with
    hIntroSEq | ⟨emptyS, hIntroSEq, hEmptySNil⟩
  · rw [hIntroSEq]
    exact str_strip_prefix_left_not_str_concat s (__str_nary_intro t)
      (str_nary_intro_arg_ne_stuck_of_ne_stuck s hIntroS)
      hIntroT hSNotConcat
  · rcases str_nary_intro_not_str_concat_cases t hTNotConcat hIntroT with
      hIntroTEq | ⟨emptyT, hIntroTEq, hEmptyTNil⟩
    · rw [hIntroSEq, hIntroTEq]
      exact str_strip_prefix_right_not_str_concat (mkConcat s emptyS) t
        (by simpa [hIntroSEq] using hIntroS)
        (str_nary_intro_arg_ne_stuck_of_ne_stuck t hIntroT)
        hTNotConcat
    · rw [hIntroSEq, hIntroTEq]
      exact str_strip_prefix_concat_of_eo_eq_false s t emptyS emptyT
        hHead

private theorem concatEq_false_lhs_eq_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    concatEqLhs (Term.Boolean false) s t = s := by
  have hStrip :=
    str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
      s t hSNotConcat hTNotConcat hIntroS hIntroT hHead
  rw [concatEqLhs_false, hStrip]
  simp [mkPair, pair_first_pair,
    str_nary_elim_str_nary_intro_eq_of_not_str_concat s hSNotConcat
      hIntroS]

private theorem concatEq_false_rhs_eq_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    concatEqRhs (Term.Boolean false) s t = t := by
  have hStrip :=
    str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
      s t hSNotConcat hTNotConcat hIntroS hIntroT hHead
  rw [concatEqRhs_false, hStrip]
  simp [mkPair, pair_second_pair,
    str_nary_elim_str_nary_intro_eq_of_not_str_concat t hTNotConcat
      hIntroT]

private theorem concatEq_true_lhs_eq_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hRevS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck)
    (hRevT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    concatEqLhs (Term.Boolean true) s t = s := by
  have hRevSEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat s hSNotConcat
      hIntroS hRevS
  have hRevTEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat t hTNotConcat
      hIntroT hRevT
  have hStrip :=
    str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
      s t hSNotConcat hTNotConcat hIntroS hIntroT hHead
  rw [concatEqLhs_true, hRevSEq, hRevTEq, hStrip]
  simp [mkPair, pair_first_pair, hRevSEq,
    str_nary_elim_str_nary_intro_eq_of_not_str_concat s hSNotConcat
      hIntroS]

private theorem concatEq_true_rhs_eq_of_not_str_concat_eo_eq_false
    (s t : Term)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hRevS :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s) ≠
        Term.Stuck)
    (hRevT :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean false) :
    concatEqRhs (Term.Boolean true) s t = t := by
  have hRevSEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat s hSNotConcat
      hIntroS hRevS
  have hRevTEq :=
    eo_list_rev_str_nary_intro_eq_of_not_str_concat t hTNotConcat
      hIntroT hRevT
  have hStrip :=
    str_strip_prefix_str_nary_intro_of_not_str_concat_eo_eq_false
      s t hSNotConcat hTNotConcat hIntroS hIntroT hHead
  rw [concatEqRhs_true, hRevSEq, hRevTEq, hStrip]
  simp [mkPair, pair_second_pair, hRevTEq,
    str_nary_elim_str_nary_intro_eq_of_not_str_concat t hTNotConcat
      hIntroT]

private theorem concatEq_false_lhs_eq_rhs_of_eo_eq_true
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    concatEqLhs (Term.Boolean false) s t =
      concatEqRhs (Term.Boolean false) s t := by
  have hTS : t = s := eq_of_eo_eq_true_local s t hHead
  subst t
  have hStrip :
      __str_strip_prefix (__str_nary_intro s) (__str_nary_intro s) ≠
        Term.Stuck := by
    simpa [concatEqStrip_false] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s s hProg
  have hPair :=
    pair_first_str_strip_prefix_self_eq_pair_second
      (__str_nary_intro s) hStrip
  rw [concatEqLhs_false, concatEqRhs_false, hPair]

private theorem concatEq_true_lhs_eq_rhs_of_eo_eq_true
    (s t : Term)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    concatEqLhs (Term.Boolean true) s t =
      concatEqRhs (Term.Boolean true) s t := by
  have hTS : t = s := eq_of_eo_eq_true_local s t hHead
  subst t
  let revS := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)
  have hStrip : __str_strip_prefix revS revS ≠ Term.Stuck := by
    change
      __str_strip_prefix
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s))
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)) ≠
        Term.Stuck
    simpa [revS, concatEqStrip_true] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s s hProg
  have hPair := pair_first_str_strip_prefix_self_eq_pair_second revS hStrip
  rw [concatEqLhs_true, concatEqRhs_true]
  simp [revS, hPair]

private theorem eo_interprets_str_nary_elim_list_nil_empty_of_bool
    (M : SmtModel) (hM : model_total_typed M) (nil : Term) (T : SmtType)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hElim : __str_nary_elim nil ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim nil) nil)) :
    eo_interprets M (mkEq (__str_nary_elim nil) nil) true := by
  exact RuleProofs.eo_interprets_eq_of_rel M (__str_nary_elim nil) nil hBool
    (smt_value_rel_str_nary_elim M hM nil T hNilTy hElim)

private theorem eo_interprets_str_nary_elim_list_concat_rec_singleton
    (M : SmtModel) (hM : model_total_typed M)
    (a head nil : Term) (T : SmtType)
    (hList :
      __eo_is_list (Term.UOp UserOp.str_concat) a = Term.Boolean true)
    (haTy : __smtx_typeof (__eo_to_smt a) = SmtType.Seq T)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hElimConcat :
      __str_nary_elim
          (__eo_list_concat_rec a (mkConcat head nil)) ≠ Term.Stuck)
    (hElimA : __str_nary_elim a ≠ Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_concat_rec a (mkConcat head nil)))
        (mkConcat (__str_nary_elim a) head)) true := by
  have hZTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hConcatTy :
      __smtx_typeof
          (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil))) =
        SmtType.Seq T :=
    smt_typeof_list_concat_rec_str_concat_of_seq a (mkConcat head nil) T
      hList haTy hZTy
  have hElimConcatTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_concat_rec a (mkConcat head nil)))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (__eo_list_concat_rec a (mkConcat head nil)) T hConcatTy hElimConcat
  have hElimATy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim a)) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck a T haTy hElimA
  have hElimAHeadTy :
      __smtx_typeof (__eo_to_smt (mkConcat (__str_nary_elim a) head)) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq (__str_nary_elim a) head T
      hElimATy hHeadTy
  have hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_concat_rec a (mkConcat head nil)))
        (mkConcat (__str_nary_elim a) head)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimConcatTy, hElimAHeadTy]
    · rw [hElimConcatTy]
      exact seq_ne_none T
  have hLeftRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_concat_rec a (mkConcat head nil)))))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil)))) :=
    smt_value_rel_str_nary_elim M hM
      (__eo_list_concat_rec a (mkConcat head nil)) T hConcatTy hElimConcat
  have hConcatRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat a (mkConcat head nil)))) :=
    smt_value_rel_list_concat_rec_str_concat M hM a (mkConcat head nil) T
      hList haTy hZTy
  have hAElimRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim a))) :=
    RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim a)))
      (__smtx_model_eval M (__eo_to_smt a))
      (smt_value_rel_str_nary_elim M hM a T haTy hElimA)
  have hLeftCongr :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat a (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat (__str_nary_elim a)
            (mkConcat head nil)))) :=
    smt_value_rel_str_concat_left_congr M hM a (__str_nary_elim a)
      (mkConcat head nil) T haTy hElimATy hZTy hAElimRel
  have hAssoc :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (__str_nary_elim a) (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (mkConcat (__str_nary_elim a) head) nil))) :=
    RuleProofs.smt_value_rel_symm
      (__smtx_model_eval M
        (__eo_to_smt
          (mkConcat (mkConcat (__str_nary_elim a) head) nil)))
      (__smtx_model_eval M
        (__eo_to_smt (mkConcat (__str_nary_elim a) (mkConcat head nil))))
      (smt_value_rel_str_concat_assoc M hM (__str_nary_elim a) head nil T
        hElimATy hHeadTy hNilTy)
  have hRightNil :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (mkConcat (mkConcat (__str_nary_elim a) head) nil)))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat (__str_nary_elim a) head))) :=
    smt_value_rel_str_concat_list_nil_right_empty M hM
      (mkConcat (__str_nary_elim a) head) nil T hElimAHeadTy hNil hNilTy
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (__str_nary_elim
            (__eo_list_concat_rec a (mkConcat head nil)))))
      (__smtx_model_eval M
        (__eo_to_smt (mkConcat (__str_nary_elim a) head))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M
        (__eo_to_smt
          (__str_nary_elim
            (__eo_list_concat_rec a (mkConcat head nil)))))
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil))))
      (__smtx_model_eval M
        (__eo_to_smt (mkConcat (__str_nary_elim a) head))) hLeftRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_concat_rec a (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat a (mkConcat head nil))))
        (__smtx_model_eval M
          (__eo_to_smt (mkConcat (__str_nary_elim a) head))) hConcatRel
        (RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M
            (__eo_to_smt (mkConcat a (mkConcat head nil))))
          (__smtx_model_eval M
            (__eo_to_smt (mkConcat (__str_nary_elim a)
              (mkConcat head nil))))
          (__smtx_model_eval M
            (__eo_to_smt (mkConcat (__str_nary_elim a) head))) hLeftCongr
          (RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat (__str_nary_elim a)
                (mkConcat head nil))))
            (__smtx_model_eval M
              (__eo_to_smt
                (mkConcat (mkConcat (__str_nary_elim a) head) nil)))
            (__smtx_model_eval M
              (__eo_to_smt (mkConcat (__str_nary_elim a) head)))
            hAssoc hRightNil)))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim (__eo_list_concat_rec a (mkConcat head nil)))
    (mkConcat (__str_nary_elim a) head) hBool hRel

private theorem eo_interprets_rev_cons_snoc_of_seq
    (M : SmtModel) (hM : model_total_typed M) (head tail : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hTailList :
      __eo_is_list (Term.UOp UserOp.str_concat) tail = Term.Boolean true)
    (hTailTy : __smtx_typeof (__eo_to_smt tail) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) ≠
        Term.Stuck)
    (hRevTail :
      __eo_list_rev (Term.UOp UserOp.str_concat) tail ≠ Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)) ≠
        Term.Stuck)
    (hElimTail :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail)))
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) tail))
          head)) true := by
  let nil := __eo_get_nil_rec (Term.UOp UserOp.str_concat) tail
  have hGet : nil ≠ Term.Stuck := by
    simpa [nil] using
      eo_get_nil_rec_ne_stuck_of_is_list_true
        (Term.UOp UserOp.str_concat) tail hTailList
  have hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil =
        Term.Boolean true := by
    simpa [nil] using
      eo_is_list_nil_get_nil_rec_of_is_list_true
        (Term.UOp UserOp.str_concat) tail hTailList
  have hNilList :
      __eo_is_list (Term.UOp UserOp.str_concat) nil = Term.Boolean true := by
    simpa [nil] using
      eo_get_nil_rec_is_list_true_of_is_list_true
        (Term.UOp UserOp.str_concat) tail hTailList
  have hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T := by
    simpa [nil] using
      smt_typeof_get_nil_rec_str_concat_of_seq tail T hTailList hTailTy
        (eo_get_nil_rec_ne_stuck_of_is_list_true
          (Term.UOp UserOp.str_concat) tail hTailList)
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        __eo_list_rev_rec tail (mkConcat head nil) := by
    simpa [nil] using
      eo_list_rev_str_concat_cons_eq_of_ne_stuck head tail hRevCons
  have hNilConcat :
      __eo_list_concat_rec nil (mkConcat head nil) = mkConcat head nil :=
    eo_list_concat_rec_str_concat_nil_eq_of_nil_true nil (mkConcat head nil)
      hNil
  have hRevConsConcatEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat head tail) =
        __eo_list_concat_rec (__eo_list_rev_rec tail nil)
          (mkConcat head nil) := by
    rw [hRevConsEq]
    calc
      __eo_list_rev_rec tail (mkConcat head nil) =
          __eo_list_rev_rec tail
            (__eo_list_concat_rec nil (mkConcat head nil)) := by
        rw [hNilConcat]
      _ = __eo_list_concat_rec (__eo_list_rev_rec tail nil)
            (mkConcat head nil) :=
        eo_list_rev_rec_list_concat_rec_singleton_eq tail nil head nil
          hTailList hNilList
  have hRevTailEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) tail =
        __eo_list_rev_rec tail nil := by
    simpa [nil] using
      eo_list_rev_eq_rec_of_ne_stuck (Term.UOp UserOp.str_concat) tail
        hRevTail
  have hRevTailRecNonStuck :
      __eo_list_rev_rec tail nil ≠ Term.Stuck := by
    simpa [hRevTailEq] using hRevTail
  have hRevTailRecList :
      __eo_is_list (Term.UOp UserOp.str_concat)
          (__eo_list_rev_rec tail nil) = Term.Boolean true :=
    eo_list_rev_rec_is_list_true_of_lists (Term.UOp UserOp.str_concat)
      tail nil hTailList hNilList hRevTailRecNonStuck
  have hRevTailRecTy :
      __smtx_typeof (__eo_to_smt (__eo_list_rev_rec tail nil)) =
        SmtType.Seq T :=
    smt_typeof_list_rev_rec_str_concat_of_seq tail nil T hTailList
      hTailTy hNilTy hRevTailRecNonStuck
  have hElimRec :
      __str_nary_elim (__eo_list_rev_rec tail nil) ≠ Term.Stuck := by
    simpa [hRevTailEq] using hElimTail
  have hElimConcat :
      __str_nary_elim
          (__eo_list_concat_rec (__eo_list_rev_rec tail nil)
            (mkConcat head nil)) ≠ Term.Stuck := by
    simpa [hRevConsConcatEq] using hElimCons
  have hCore :=
    eo_interprets_str_nary_elim_list_concat_rec_singleton M hM
      (__eo_list_rev_rec tail nil) head nil T hRevTailRecList
      hRevTailRecTy hHeadTy hNil hNilTy hElimConcat hElimRec
  simpa [hRevConsConcatEq, hRevTailEq] using hCore

private theorem eo_interprets_rev_cons_snoc_of_cons_nil
    (M : SmtModel) (hM : model_total_typed M) (head mid nil : Term)
    (T : SmtType)
    (hHeadTy : __smtx_typeof (__eo_to_smt head) = SmtType.Seq T)
    (hMidTy : __smtx_typeof (__eo_to_smt mid) = SmtType.Seq T)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) nil = Term.Boolean true)
    (hNilTy : __smtx_typeof (__eo_to_smt nil) = SmtType.Seq T)
    (hRevCons :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat head (mkConcat mid nil)) ≠ Term.Stuck)
    (hRevTail :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil) ≠
        Term.Stuck)
    (hElimCons :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat head (mkConcat mid nil))) ≠ Term.Stuck)
    (hElimTail :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil)) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (mkConcat head (mkConcat mid nil))))
        (mkConcat
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil)))
          head)) true := by
  have hRevConsEq :
      __eo_list_rev (Term.UOp UserOp.str_concat)
          (mkConcat head (mkConcat mid nil)) =
        mkConcat mid (mkConcat head nil) :=
    eo_list_rev_str_concat_cons_cons_nil_eq_of_ne_stuck head mid nil hNil
      hRevCons
  have hRevTailEq :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil) =
        mkConcat mid nil :=
    eo_list_rev_str_concat_cons_nil_eq_of_ne_stuck mid nil hNil hRevTail
  have hHeadNilTy :
      __smtx_typeof (__eo_to_smt (mkConcat head nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq head nil T hHeadTy hNilTy
  have hTailTy :
      __smtx_typeof (__eo_to_smt (mkConcat mid nil)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq mid nil T hMidTy hNilTy
  have hCons2Ty :
      __smtx_typeof (__eo_to_smt (mkConcat mid (mkConcat head nil))) =
        SmtType.Seq T :=
    smt_typeof_str_concat_of_seq mid (mkConcat head nil) T hMidTy
      hHeadNilTy
  have hMidHeadTy :
      __smtx_typeof (__eo_to_smt (mkConcat mid head)) = SmtType.Seq T :=
    smt_typeof_str_concat_of_seq mid head T hMidTy hHeadTy
  have hElimCons' :
      __str_nary_elim (mkConcat mid (mkConcat head nil)) ≠ Term.Stuck := by
    simpa [hRevConsEq] using hElimCons
  have hElimTail' :
      __str_nary_elim (mkConcat mid nil) ≠ Term.Stuck := by
    simpa [hRevTailEq] using hElimTail
  have hElimTailTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (mkConcat mid nil))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (mkConcat mid nil) T
      hTailTy hElimTail'
  let lhs :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat)
        (mkConcat head (mkConcat mid nil)))
  let rhs :=
    mkConcat
      (__str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat mid nil)))
      head
  let midHead := mkConcat mid head
  have hLhsToCons2 :
      eo_interprets M
        (mkEq lhs (mkConcat mid (mkConcat head nil))) true := by
    subst lhs
    rw [hRevConsEq]
    exact eo_interprets_str_nary_elim_eq_of_bool M hM
      (mkConcat mid (mkConcat head nil)) T hCons2Ty hElimCons'
      (eo_has_bool_type_str_nary_elim_eq_of_seq
        (mkConcat mid (mkConcat head nil)) T hCons2Ty hElimCons')
  have hAssoc :
      eo_interprets M
        (mkEq (mkConcat mid (mkConcat head nil))
          (mkConcat (mkConcat mid head) nil)) true :=
    eo_interprets_str_concat_assoc_symm M hM mid head nil T hMidTy
      hHeadTy hNilTy
  have hRightNil :
      eo_interprets M
        (mkEq (mkConcat (mkConcat mid head) nil) midHead) true := by
    subst midHead
    exact eo_interprets_str_concat_list_nil_right_empty_of_bool M hM
      (mkConcat mid head) nil T hMidHeadTy hNil hNilTy
      (eo_has_bool_type_str_concat_list_nil_right_empty_of_seq
        (mkConcat mid head) nil T hMidHeadTy hNilTy)
  have hLhsToMidHead :
      eo_interprets M (mkEq lhs midHead) true :=
    RuleProofs.eo_interprets_eq_trans M lhs
      (mkConcat mid (mkConcat head nil)) midHead hLhsToCons2
      (RuleProofs.eo_interprets_eq_trans M
        (mkConcat mid (mkConcat head nil))
        (mkConcat (mkConcat mid head) nil) midHead hAssoc hRightNil)
  have hElimTailToTail :
      eo_interprets M
        (mkEq (__str_nary_elim (mkConcat mid nil)) (mkConcat mid nil)) true :=
    eo_interprets_str_nary_elim_eq_of_bool M hM (mkConcat mid nil) T
      hTailTy hElimTail'
      (eo_has_bool_type_str_nary_elim_eq_of_seq (mkConcat mid nil) T
        hTailTy hElimTail')
  have hTailToMid :
      eo_interprets M (mkEq (mkConcat mid nil) mid) true :=
    eo_interprets_str_concat_list_nil_right_empty_of_bool M hM mid nil T
      hMidTy hNil hNilTy
      (eo_has_bool_type_str_concat_list_nil_right_empty_of_seq mid nil T
        hMidTy hNilTy)
  have hElimTailToMid :
      eo_interprets M (mkEq (__str_nary_elim (mkConcat mid nil)) mid) true :=
    RuleProofs.eo_interprets_eq_trans M (__str_nary_elim (mkConcat mid nil))
      (mkConcat mid nil) mid hElimTailToTail hTailToMid
  have hRhsToMidHead :
      eo_interprets M (mkEq rhs midHead) true := by
    subst rhs
    rw [hRevTailEq]
    subst midHead
    exact eo_interprets_str_concat_left_congr_of_seq M hM
      (__str_nary_elim (mkConcat mid nil)) mid head T hElimTailTy
      hMidTy hHeadTy hElimTailToMid
  have hMidHeadToRhs : eo_interprets M (mkEq midHead rhs) true :=
    eo_interprets_eq_symm_local M rhs midHead hRhsToMidHead
  have hGoal : eo_interprets M (mkEq lhs rhs) true :=
    RuleProofs.eo_interprets_eq_trans M lhs midHead rhs hLhsToMidHead
      hMidHeadToRhs
  simpa [lhs, rhs] using hGoal

private theorem eo_interprets_str_nary_intro_congr_of_seq
    (M : SmtModel) (hM : model_total_typed M) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hIntroX : __str_nary_intro x ≠ Term.Stuck)
    (hIntroY : __str_nary_intro y ≠ Term.Stuck)
    (hXY : eo_interprets M (mkEq x y) true)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_intro x) (__str_nary_intro y))) :
    eo_interprets M (mkEq (__str_nary_intro x) (__str_nary_intro y)) true := by
  have hXRel := smt_value_rel_str_nary_intro M hM x T hxTy hIntroX
  have hYRel := smt_value_rel_str_nary_intro M hM y T hyTy hIntroY
  have hXYRel := RuleProofs.eo_interprets_eq_rel M x y hXY
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro x)))
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y))) hXRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y))) hXYRel
        (RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_intro y)))
          (__smtx_model_eval M (__eo_to_smt y)) hYRel))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_intro x) (__str_nary_intro y) hBool hRel

private theorem eo_interprets_str_nary_elim_congr_of_seq
    (M : SmtModel) (hM : model_total_typed M) (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hElimX : __str_nary_elim x ≠ Term.Stuck)
    (hElimY : __str_nary_elim y ≠ Term.Stuck)
    (hXY : eo_interprets M (mkEq x y) true)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim x) (__str_nary_elim y))) :
    eo_interprets M (mkEq (__str_nary_elim x) (__str_nary_elim y)) true := by
  have hXRel := smt_value_rel_str_nary_elim M hM x T hxTy hElimX
  have hYRel := smt_value_rel_str_nary_elim M hM y T hyTy hElimY
  have hXYRel := RuleProofs.eo_interprets_eq_rel M x y hXY
  have hRel : RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim x)))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y))) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim x)))
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y))) hXRel
      (RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))
        (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y))) hXYRel
        (RuleProofs.smt_value_rel_symm
          (__smtx_model_eval M (__eo_to_smt (__str_nary_elim y)))
          (__smtx_model_eval M (__eo_to_smt y)) hYRel))
  exact RuleProofs.eo_interprets_eq_of_rel M
    (__str_nary_elim x) (__str_nary_elim y) hBool hRel

private theorem smt_seq_rel_concat_left_cancel (T : SmtType) (sx sy sz : SmtSeq) :
    RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sz)) ->
    RuleProofs.smt_seq_rel sy sz := by
  intro h
  have hTail := smt_seq_rel_pack_append_cancel T (native_unpack_seq sx)
    (native_unpack_seq sy) (native_unpack_seq sz) h
  exact RuleProofs.smt_seq_rel_trans sy (native_pack_seq T (native_unpack_seq sy)) sz
    (smt_seq_rel_pack_unpack T sy)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sz)) sz hTail
      (RuleProofs.smt_seq_rel_symm sz (native_pack_seq T (native_unpack_seq sz))
        (smt_seq_rel_pack_unpack T sz)))

private theorem smt_seq_rel_concat_right_cancel (T : SmtType) (sx sy sz : SmtSeq) :
    RuleProofs.smt_seq_rel
      (native_pack_seq T (native_unpack_seq sy ++ native_unpack_seq sx))
      (native_pack_seq T (native_unpack_seq sz ++ native_unpack_seq sx)) ->
    RuleProofs.smt_seq_rel sy sz := by
  intro h
  have hTail := smt_seq_rel_pack_append_right_cancel T (native_unpack_seq sy)
    (native_unpack_seq sz) (native_unpack_seq sx) h
  exact RuleProofs.smt_seq_rel_trans sy (native_pack_seq T (native_unpack_seq sy)) sz
    (smt_seq_rel_pack_unpack T sy)
    (RuleProofs.smt_seq_rel_trans
      (native_pack_seq T (native_unpack_seq sy))
      (native_pack_seq T (native_unpack_seq sz)) sz hTail
      (RuleProofs.smt_seq_rel_symm sz (native_pack_seq T (native_unpack_seq sz))
        (smt_seq_rel_pack_unpack T sz)))

private theorem smt_value_rel_str_concat_left_cancel
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat x y)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat x z))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y) (SmtType.Seq T)
    hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z) (SmtType.Seq T)
    hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hyEval, hzEval] at hRel
  rw [hyEval, hzEval]
  change RuleProofs.smt_seq_rel sy sz
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sy)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sx)
      (native_unpack_seq sx ++ native_unpack_seq sz))) =
      SmtValue.Boolean true at hRel
  exact smt_seq_rel_concat_left_cancel (__smtx_elem_typeof_seq_value sx) sx sy sz hRel

private theorem smt_value_rel_str_concat_right_cancel
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkConcat y x)))
      (__smtx_model_eval M (__eo_to_smt (mkConcat z x))) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z)) := by
  intro hRel
  have hxValTy := smt_model_eval_preserves_type M hM (__eo_to_smt x) (SmtType.Seq T)
    hxTy (seq_ne_none T) (type_inhabited_seq T)
  have hyValTy := smt_model_eval_preserves_type M hM (__eo_to_smt y) (SmtType.Seq T)
    hyTy (seq_ne_none T) (type_inhabited_seq T)
  have hzValTy := smt_model_eval_preserves_type M hM (__eo_to_smt z) (SmtType.Seq T)
    hzTy (seq_ne_none T) (type_inhabited_seq T)
  rcases seq_value_canonical hxValTy with ⟨sx, hxEval⟩
  rcases seq_value_canonical hyValTy with ⟨sy, hyEval⟩
  rcases seq_value_canonical hzValTy with ⟨sz, hzEval⟩
  have hsyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
    simpa [hyEval, __smtx_typeof_value] using hyValTy
  have hszTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
    simpa [hzEval, __smtx_typeof_value] using hzValTy
  have hsyElem : __smtx_elem_typeof_seq_value sy = T :=
    elem_typeof_seq_value_of_typeof_seq_value hsyTy
  have hszElem : __smtx_elem_typeof_seq_value sz = T :=
    elem_typeof_seq_value_of_typeof_seq_value hszTy
  unfold RuleProofs.smt_value_rel at hRel ⊢
  rw [smtx_model_eval_str_concat_term_eq, smtx_model_eval_str_concat_term_eq] at hRel
  rw [hxEval, hyEval, hzEval] at hRel
  change __smtx_model_eval_eq
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sy)
      (native_unpack_seq sy ++ native_unpack_seq sx)))
    (SmtValue.Seq (native_pack_seq (__smtx_elem_typeof_seq_value sz)
      (native_unpack_seq sz ++ native_unpack_seq sx))) =
      SmtValue.Boolean true at hRel
  rw [hsyElem, hszElem] at hRel
  rw [hyEval, hzEval]
  change RuleProofs.smt_seq_rel sy sz
  exact smt_seq_rel_concat_right_cancel T sx sy sz hRel

private theorem eo_interprets_str_concat_left_cancel
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) :
    eo_interprets M (mkEq (mkConcat x y) (mkConcat x z)) true ->
    eo_interprets M (mkEq y z) true := by
  intro h
  have hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat x y) (mkConcat x z)) :=
    RuleProofs.eo_has_bool_type_of_interprets_true M _ h
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat x y) (mkConcat x z) hBool with ⟨hSame, hLeftNN⟩
  rcases str_concat_args_of_non_none x y hLeftNN with ⟨T, hxTy, hyTy⟩
  have hRightNN : __smtx_typeof (__eo_to_smt (mkConcat x z)) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases str_concat_args_of_non_none x z hRightNN with ⟨U, hxTyU, hzTyU⟩
  have hUT : U = T := by
    have hSeq : SmtType.Seq T = SmtType.Seq U := by
      rw [← hxTy, ← hxTyU]
    injection hSeq with hTU
    exact hTU.symm
  have hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    simpa [hUT] using hzTyU
  have hRel := RuleProofs.eo_interprets_eq_rel M (mkConcat x y) (mkConcat x z) h
  have hTailRel := smt_value_rel_str_concat_left_cancel M hM x y z T hxTy hyTy hzTy hRel
  have hYZBool : RuleProofs.eo_has_bool_type (mkEq y z) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hyTy, hzTy]
    · rw [hyTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M y z hYZBool hTailRel

private theorem eo_interprets_str_concat_tails_of_head_eo_eq_true
    (M : SmtModel) (hM : model_total_typed M) (t u t2 s2 : Term)
    (hHead : __eo_eq t u = Term.Boolean true) :
    eo_interprets M (mkEq (mkConcat t t2) (mkConcat u s2)) true ->
    eo_interprets M (mkEq t2 s2) true := by
  intro h
  have hUT : u = t := eq_of_eo_eq_true_local t u hHead
  subst u
  exact eo_interprets_str_concat_left_cancel M hM t t2 s2 h

private theorem eo_interprets_str_strip_prefix_concat_step
    (M : SmtModel) (hM : model_total_typed M) (t u t2 s2 : Term)
    (hXY : eo_interprets M (mkEq (mkConcat t t2) (mkConcat u s2)) true)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hTail :
      eo_interprets M (mkEq t2 s2) true ->
      __str_strip_prefix t2 s2 ≠ Term.Stuck ->
      RuleProofs.eo_has_bool_type
        (mkEq (__pair_first (__str_strip_prefix t2 s2))
          (__pair_second (__str_strip_prefix t2 s2))) ->
      eo_interprets M
        (mkEq (__pair_first (__str_strip_prefix t2 s2))
          (__pair_second (__str_strip_prefix t2 s2))) true)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2))))) :
    eo_interprets M
      (mkEq
        (__pair_first (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))
        (__pair_second (__str_strip_prefix (mkConcat t t2) (mkConcat u s2)))) true := by
  have hIte :
      __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
        Term.Stuck := by
    simpa [__str_strip_prefix] using hStrip
  rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
      (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
    hCond | hCond
  · have hTailEq :=
      eo_interprets_str_concat_tails_of_head_eo_eq_true M hM t u t2 s2 hCond hXY
    have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
      simpa [hCond, eo_ite_true] using hIte
    have hTailBool : RuleProofs.eo_has_bool_type
        (mkEq (__pair_first (__str_strip_prefix t2 s2))
          (__pair_second (__str_strip_prefix t2 s2))) := by
      simpa [str_strip_prefix_concat_of_eo_eq_true t u t2 s2 hCond] using hBool
    exact eo_interprets_str_strip_prefix_concat_true_of_tail M t u t2 s2 hCond
      (hTail hTailEq hTailNonStuck hTailBool)
  · exact eo_interprets_str_strip_prefix_concat_false M t u t2 s2 hCond hXY

private theorem eo_interprets_str_strip_prefix_result
    (M : SmtModel) (hM : model_total_typed M) (x y : Term)
    (hXY : eo_interprets M (mkEq x y) true)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck)
    (hBool : RuleProofs.eo_has_bool_type
      (mkEq (__pair_first (__str_strip_prefix x y))
        (__pair_second (__str_strip_prefix x y)))) :
    eo_interprets M
      (mkEq (__pair_first (__str_strip_prefix x y))
        (__pair_second (__str_strip_prefix x y))) true := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    exact eo_interprets_str_strip_prefix_concat_step M hM t u t2 s2
      hXY hStrip
      (eo_interprets_str_strip_prefix_result M hM t2 s2) hBool
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair, pair_second_pair]
      using hXY
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem str_strip_prefix_result_types_of_seq
    (x y : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hyTy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hStrip : __str_strip_prefix x y ≠ Term.Stuck) :
    __smtx_typeof (__eo_to_smt (__pair_first (__str_strip_prefix x y))) =
        SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt (__pair_second (__str_strip_prefix x y))) =
        SmtType.Seq T := by
  fun_cases __str_strip_prefix x y
  · simp [__str_strip_prefix] at hStrip
  · simp [__str_strip_prefix] at hStrip
  · rename_i t t2 u s2
    subst_vars
    have hLeftNN :
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) ≠ SmtType.None := by
      rw [hxTy]
      exact seq_ne_none T
    have hRightNN :
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) ≠ SmtType.None := by
      rw [hyTy]
      exact seq_ne_none T
    rcases str_concat_args_of_non_none t t2 hLeftNN with ⟨U, htTy, ht2TyU⟩
    rcases str_concat_args_of_non_none u s2 hRightNN with ⟨V, huTy, hs2TyV⟩
    have hLeftTyU :
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq U :=
      smt_typeof_str_concat_of_seq t t2 U htTy ht2TyU
    have hRightTyV :
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq V :=
      smt_typeof_str_concat_of_seq u s2 V huTy hs2TyV
    have hUT : U = T := by
      have hSeq : SmtType.Seq U = SmtType.Seq T := by
        rw [← hLeftTyU, hxTy]
      injection hSeq
    have hVT : V = T := by
      have hSeq : SmtType.Seq V = SmtType.Seq T := by
        rw [← hRightTyV, hyTy]
      injection hSeq
    have ht2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T := by
      simpa [hUT] using ht2TyU
    have hs2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T := by
      simpa [hVT] using hs2TyV
    have hIte :
        __eo_ite (__eo_eq t u) (__str_strip_prefix t2 s2)
          (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) ≠
          Term.Stuck := by
      simpa [__str_strip_prefix] using hStrip
    rcases eo_ite_cases_of_ne_stuck (__eo_eq t u) (__str_strip_prefix t2 s2)
        (__eo_l_1___str_strip_prefix (mkConcat t t2) (mkConcat u s2)) hIte with
      hCond | hCond
    · have hTailNonStuck : __str_strip_prefix t2 s2 ≠ Term.Stuck := by
        simpa [hCond, eo_ite_true] using hIte
      rw [hCond, eo_ite_true]
      exact str_strip_prefix_result_types_of_seq t2 s2 T ht2Ty hs2Ty hTailNonStuck
    · rw [hCond, eo_ite_false]
      simpa [mkPair, pair_first_pair, pair_second_pair] using And.intro hxTy hyTy
  · simpa [__eo_l_1___str_strip_prefix, mkPair, pair_first_pair, pair_second_pair]
      using And.intro hxTy hyTy
termination_by sizeOf x + sizeOf y
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem concatEq_false_has_bool_type_of_seq
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) := by
  let strip := __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t)
  have hIntroSNonStuck :
      __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroTNonStuck :
      __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq s T hsTy hIntroSNN
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq t T htTy hIntroTNN
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) ≠
      Term.Stuck
    simpa [concatEqStrip_false] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hStripTypes :
      __smtx_typeof (__eo_to_smt (__pair_first strip)) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__pair_second strip)) = SmtType.Seq T :=
    str_strip_prefix_result_types_of_seq (__str_nary_intro s) (__str_nary_intro t)
      T hIntroSTy hIntroTTy hStripNonStuck
  have hElimFirstNonStuck :
      __str_nary_elim (__pair_first strip) ≠ Term.Stuck := by
    simpa [strip, concatEqLhs_false] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hElimSecondNonStuck :
      __str_nary_elim (__pair_second strip) ≠ Term.Stuck := by
    simpa [strip, concatEqRhs_false] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hElimFirstTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_first strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (__pair_first strip) T
      hStripTypes.1 hElimFirstNonStuck
  have hElimSecondTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_second strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck (__pair_second strip) T
      hStripTypes.2 hElimSecondNonStuck
  have hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__pair_first strip))
        (__str_nary_elim (__pair_second strip))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimFirstTy, hElimSecondTy]
    · rw [hElimFirstTy]
      exact seq_ne_none T
  simpa [strip, concatEqLhs_false, concatEqRhs_false] using hFinalBool

private theorem eo_interprets_concat_eq_false_of_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hPrem : eo_interprets M (mkEq s t) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t))) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) true := by
  let strip := __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t)
  have hIntroSNonStuck :
      __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroTNonStuck :
      __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq s T hsTy hIntroSNN
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq t T htTy hIntroTNN
  have hIntroBool : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_intro s) (__str_nary_intro t)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hIntroSTy, hIntroTTy]
    · rw [hIntroSTy]
      exact seq_ne_none T
  have hIntroEq : eo_interprets M
      (mkEq (__str_nary_intro s) (__str_nary_intro t)) true :=
    eo_interprets_str_nary_intro_congr_of_seq M hM s t T
      hsTy htTy hIntroSNonStuck hIntroTNonStuck hPrem hIntroBool
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix (__str_nary_intro s) (__str_nary_intro t) ≠
      Term.Stuck
    simpa [concatEqStrip_false] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hStripTypes :
      __smtx_typeof (__eo_to_smt (__pair_first strip)) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__pair_second strip)) = SmtType.Seq T :=
    str_strip_prefix_result_types_of_seq (__str_nary_intro s) (__str_nary_intro t)
      T hIntroSTy hIntroTTy hStripNonStuck
  have hStripBool : RuleProofs.eo_has_bool_type
      (mkEq (__pair_first strip) (__pair_second strip)) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hStripTypes.1, hStripTypes.2]
    · rw [hStripTypes.1]
      exact seq_ne_none T
  have hStripEq : eo_interprets M
      (mkEq (__pair_first strip) (__pair_second strip)) true :=
    eo_interprets_str_strip_prefix_result M hM
      (__str_nary_intro s) (__str_nary_intro t) hIntroEq hStripNonStuck
      hStripBool
  have hElimFirstNonStuck :
      __str_nary_elim (__pair_first strip) ≠ Term.Stuck := by
    simpa [strip, concatEqLhs_false] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  have hElimSecondNonStuck :
      __str_nary_elim (__pair_second strip) ≠ Term.Stuck := by
    simpa [strip, concatEqRhs_false] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean false) s t hProg
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (concatEqLhs (Term.Boolean false) s t)
      (concatEqRhs (Term.Boolean false) s t) hFinalBool with
    ⟨hFinalSame, hFinalLeftNN⟩
  have hElimFirstNN :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_first strip))) ≠
        SmtType.None := by
    simpa [strip, concatEqLhs_false] using hFinalLeftNN
  have hElimSecondNN :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_second strip))) ≠
        SmtType.None := by
    have hRightNN :
        __smtx_typeof (__eo_to_smt (concatEqRhs (Term.Boolean false) s t)) ≠
          SmtType.None := by
      rw [← hFinalSame]
      exact hFinalLeftNN
    simpa [strip, concatEqRhs_false] using hRightNN
  have hElimFirstTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_first strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq (__pair_first strip) T
      hStripTypes.1 hElimFirstNN
  have hElimSecondTy :
      __smtx_typeof (__eo_to_smt (__str_nary_elim (__pair_second strip))) =
        SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq (__pair_second strip) T
      hStripTypes.2 hElimSecondNN
  have hFinalBool' : RuleProofs.eo_has_bool_type
      (mkEq (__str_nary_elim (__pair_first strip))
        (__str_nary_elim (__pair_second strip))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimFirstTy, hElimSecondTy]
    · rw [hElimFirstTy]
      exact seq_ne_none T
  have hFinal :=
    eo_interprets_str_nary_elim_congr_of_seq M hM
      (__pair_first strip) (__pair_second strip) T
      hStripTypes.1 hStripTypes.2 hElimFirstNonStuck hElimSecondNonStuck
      hStripEq hFinalBool'
  simpa [strip, concatEqLhs_false, concatEqRhs_false] using hFinal

private theorem eo_interprets_concat_eq_false_of_seq'
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hPrem : eo_interprets M (mkEq s t) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    eo_interprets M
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) true := by
  have hFinalBool :=
    concatEq_false_has_bool_type_of_seq s t T hsTy htTy hIntroSNN hIntroTNN
      hProg
  exact eo_interprets_concat_eq_false_of_seq M hM s t T hsTy htTy
    hIntroSNN hIntroTNN hPrem hProg hFinalBool

private theorem concatEq_true_has_bool_type_of_seq
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) := by
  let revS := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro s)
  let revT := __eo_list_rev (Term.UOp UserOp.str_concat) (__str_nary_intro t)
  let strip := __str_strip_prefix revS revT
  have hIntroSNonStuck : __str_nary_intro s ≠ Term.Stuck :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroTNonStuck : __str_nary_intro t ≠ Term.Stuck :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t
      hProg
  have hIntroSTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq s T hsTy hIntroSNN
  have hIntroTTy :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) = SmtType.Seq T :=
    smt_typeof_str_nary_intro_of_seq t T htTy hIntroTNN
  have hRevSNonStuck : revS ≠ Term.Stuck := by
    simpa [revS] using
      concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevTNonStuck : revT ≠ Term.Stuck := by
    simpa [revT] using
      concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hIntroSList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro s) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro s) hRevSNonStuck
  have hIntroTList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__str_nary_intro t) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__str_nary_intro t) hRevTNonStuck
  have hRevSTy : __smtx_typeof (__eo_to_smt revS) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro s) T
      hIntroSList hIntroSTy hRevSNonStuck
  have hRevTTy : __smtx_typeof (__eo_to_smt revT) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__str_nary_intro t) T
      hIntroTList hIntroTTy hRevTNonStuck
  have hStripNonStuck : strip ≠ Term.Stuck := by
    change __str_strip_prefix revS revT ≠ Term.Stuck
    simpa [strip, revS, revT, concatEqStrip_true] using
      concatEqStrip_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hStripTypes :
      __smtx_typeof (__eo_to_smt (__pair_first strip)) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt (__pair_second strip)) = SmtType.Seq T :=
    str_strip_prefix_result_types_of_seq revS revT T hRevSTy hRevTTy
      hStripNonStuck
  have hFirstRevNonStuck :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first strip) ≠
        Term.Stuck := by
    simpa [strip, concatEqStrip_true] using
      concatEq_true_rev_first_ne_stuck_of_prog_ne_stuck s t hProg
  have hSecondRevNonStuck :
      __eo_list_rev (Term.UOp UserOp.str_concat) (__pair_second strip) ≠
        Term.Stuck := by
    simpa [strip, concatEqStrip_true] using
      concatEq_true_rev_second_ne_stuck_of_prog_ne_stuck s t hProg
  have hFirstList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__pair_first strip) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_first strip) hFirstRevNonStuck
  have hSecondList :
      __eo_is_list (Term.UOp UserOp.str_concat) (__pair_second strip) =
        Term.Boolean true :=
    eo_list_rev_is_list_true_of_ne_stuck (Term.UOp UserOp.str_concat)
      (__pair_second strip) hSecondRevNonStuck
  have hFirstRevTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first strip))) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__pair_first strip) T hFirstList
      hStripTypes.1 hFirstRevNonStuck
  have hSecondRevTy :
      __smtx_typeof
          (__eo_to_smt
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second strip))) = SmtType.Seq T :=
    smt_typeof_list_rev_str_concat_of_seq (__pair_second strip) T hSecondList
      hStripTypes.2 hSecondRevNonStuck
  have hElimFirstNonStuck :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first strip)) ≠ Term.Stuck := by
    simpa [strip, concatEqLhs_true] using
      concatEqLhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hElimSecondNonStuck :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second strip)) ≠ Term.Stuck := by
    simpa [strip, concatEqRhs_true] using
      concatEqRhs_ne_stuck_of_prog_ne_stuck (Term.Boolean true) s t hProg
  have hElimFirstTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_first strip)))) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first strip)) T
      hFirstRevTy hElimFirstNonStuck
  have hElimSecondTy :
      __smtx_typeof
          (__eo_to_smt
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__pair_second strip)))) = SmtType.Seq T :=
    smt_typeof_str_nary_elim_of_seq_ne_stuck
      (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_second strip)) T
      hSecondRevTy hElimSecondNonStuck
  have hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (__pair_first strip)))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second strip)))) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hElimFirstTy, hElimSecondTy]
    · rw [hElimFirstTy]
      exact seq_ne_none T
  simpa [strip, revS, revT, concatEqLhs_true, concatEqRhs_true] using
    hFinalBool

private theorem concatEq_true_has_bool_type_of_left_seq
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact concatEq_true_has_bool_type_of_seq s t T hsTy htTy hIntroSNN
    hIntroTNN hProg

private theorem concatEq_has_bool_type_of_left_seq
    (rev s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠
      Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs rev s t) (concatEqRhs rev s t)) := by
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · subst rev
    exact concatEq_true_has_bool_type_of_left_seq s t T hPremBool hsTy
      hIntroSNN hIntroTNN hProg
  · subst rev
    have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
      eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
    exact concatEq_false_has_bool_type_of_seq s t T hsTy htTy
      hIntroSNN hIntroTNN hProg

private theorem eo_interprets_str_concat_right_cancel
    (M : SmtModel) (hM : model_total_typed M) (x y z : Term) :
    eo_interprets M (mkEq (mkConcat y x) (mkConcat z x)) true ->
    eo_interprets M (mkEq y z) true := by
  intro h
  have hBool : RuleProofs.eo_has_bool_type (mkEq (mkConcat y x) (mkConcat z x)) :=
    RuleProofs.eo_has_bool_type_of_interprets_true M _ h
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (mkConcat y x) (mkConcat z x) hBool with ⟨hSame, hLeftNN⟩
  rcases str_concat_args_of_non_none y x hLeftNN with ⟨T, hyTy, hxTy⟩
  have hRightNN : __smtx_typeof (__eo_to_smt (mkConcat z x)) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  rcases str_concat_args_of_non_none z x hRightNN with ⟨U, hzTyU, hxTyU⟩
  have hUT : U = T := by
    have hSeq : SmtType.Seq T = SmtType.Seq U := by
      rw [← hxTy, ← hxTyU]
    injection hSeq with hTU
    exact hTU.symm
  have hzTy : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T := by
    simpa [hUT] using hzTyU
  have hRel := RuleProofs.eo_interprets_eq_rel M (mkConcat y x) (mkConcat z x) h
  have hTailRel := smt_value_rel_str_concat_right_cancel M hM x y z T hxTy hyTy hzTy hRel
  have hYZBool : RuleProofs.eo_has_bool_type (mkEq y z) := by
    apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rw [hyTy, hzTy]
    · rw [hyTy]
      exact seq_ne_none T
  exact RuleProofs.eo_interprets_eq_of_rel M y z hYZBool hTailRel

private theorem eo_interprets_str_concat_heads_of_tail_eo_eq_true
    (M : SmtModel) (hM : model_total_typed M) (t u t2 s2 : Term)
    (hTail : __eo_eq t u = Term.Boolean true) :
    eo_interprets M (mkEq (mkConcat t2 t) (mkConcat s2 u)) true ->
    eo_interprets M (mkEq t2 s2) true := by
  intro h
  have hUT : u = t := eq_of_eo_eq_true_local t u hTail
  subst u
  exact eo_interprets_str_concat_right_cancel M hM t t2 s2 h

private theorem eo_interprets_rev_tails_of_head_eo_eq_true
    (M : SmtModel) (hM : model_total_typed M) (t u t2 s2 : Term)
    (hHead : __eo_eq t u = Term.Boolean true) :
    eo_interprets M
      (mkEq
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2)) t)
        (mkConcat
          (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)) u))
      true ->
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  exact eo_interprets_str_concat_heads_of_tail_eo_eq_true M hM t u
    (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
    (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)) hHead

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_snoc
    (M : SmtModel) (hM : model_total_typed M) (t u t2 s2 : Term)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftSnoc :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            t)) true)
    (hRightSnoc :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2)))
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))
            u)) true)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  let left :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2))
  let right :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))
  let leftSnoc :=
    mkConcat
      (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2)) t
  let rightSnoc :=
    mkConcat
      (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)) u
  have hLeftSymm : eo_interprets M (mkEq leftSnoc left) true :=
    eo_interprets_eq_symm_local M left leftSnoc hLeftSnoc
  have hLeftRight : eo_interprets M (mkEq leftSnoc right) true :=
    RuleProofs.eo_interprets_eq_trans M leftSnoc left right hLeftSymm hXY
  have hSnocEq : eo_interprets M (mkEq leftSnoc rightSnoc) true :=
    RuleProofs.eo_interprets_eq_trans M leftSnoc right rightSnoc
      hLeftRight hRightSnoc
  exact eo_interprets_rev_tails_of_head_eo_eq_true M hM t u t2 s2 hHead
    hSnocEq

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_seq
    (M : SmtModel) (hM : model_total_typed M)
    (t u t2 s2 : Term) (T : SmtType)
    (hHead : __eo_eq t u = Term.Boolean true)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (huTy : __smtx_typeof (__eo_to_smt u) = SmtType.Seq T)
    (ht2List :
      __eo_is_list (Term.UOp UserOp.str_concat) t2 = Term.Boolean true)
    (hs2List :
      __eo_is_list (Term.UOp UserOp.str_concat) s2 = Term.Boolean true)
    (ht2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hs2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T)
    (hRevLeft :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2) ≠
        Term.Stuck)
    (hRevRight :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2) ≠
        Term.Stuck)
    (hRevTailLeft :
      __eo_list_rev (Term.UOp UserOp.str_concat) t2 ≠ Term.Stuck)
    (hRevTailRight :
      __eo_list_rev (Term.UOp UserOp.str_concat) s2 ≠ Term.Stuck)
    (hElimLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)) ≠
        Term.Stuck)
    (hElimRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2)) ≠
        Term.Stuck)
    (hElimTailLeft :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2) ≠
        Term.Stuck)
    (hElimTailRight :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2) ≠
        Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  have hLeftSnoc :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            t)) true :=
    eo_interprets_rev_cons_snoc_of_seq M hM t t2 T htTy ht2List
      ht2Ty hRevLeft hRevTailLeft hElimLeft hElimTailLeft
  have hRightSnoc :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2)))
          (mkConcat
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))
            u)) true :=
    eo_interprets_rev_cons_snoc_of_seq M hM u s2 T huTy hs2List
      hs2Ty hRevRight hRevTailRight hElimRight hElimTailRight
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_snoc M hM
    t u t2 s2 hHead hLeftSnoc hRightSnoc hXY

private theorem rev_elim_cons_operands_ne_stuck_of_interprets
    (M : SmtModel) (t u t2 s2 : Term)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)) ≠
      Term.Stuck ∧
    __str_nary_elim
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2)) ≠
      Term.Stuck ∧
    __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2) ≠
      Term.Stuck ∧
    __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2) ≠
      Term.Stuck := by
  let left :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2))
  let right :=
    __str_nary_elim
      (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))
  have hBool : RuleProofs.eo_has_bool_type (mkEq left right) := by
    simpa [left, right] using
      RuleProofs.eo_has_bool_type_of_interprets_true M _ hXY
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type left right
      hBool with ⟨hSame, hLeftNN⟩
  have hRightNN :
      __smtx_typeof (__eo_to_smt right) ≠ SmtType.None := by
    rw [← hSame]
    exact hLeftNN
  have hLeft : left ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation left hLeftNN
  have hRight : right ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation right hRightNN
  have hRevLeft :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2) ≠
        Term.Stuck := by
    simpa [left] using
      str_nary_elim_arg_ne_stuck_of_ne_stuck
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2))
        hLeft
  have hRevRight :
      __eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2) ≠
        Term.Stuck := by
    simpa [right] using
      str_nary_elim_arg_ne_stuck_of_ne_stuck
        (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))
        hRight
  exact ⟨by simpa [left] using hLeft, by simpa [right] using hRight,
    hRevLeft, hRevRight⟩

private theorem rev_elim_cons_tail_lists_of_interprets
    (M : SmtModel) (t u t2 s2 : Term)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    __eo_is_list (Term.UOp UserOp.str_concat) t2 = Term.Boolean true ∧
    __eo_is_list (Term.UOp UserOp.str_concat) s2 = Term.Boolean true ∧
    __eo_list_rev (Term.UOp UserOp.str_concat) t2 ≠ Term.Stuck ∧
    __eo_list_rev (Term.UOp UserOp.str_concat) s2 ≠ Term.Stuck := by
  rcases rev_elim_cons_operands_ne_stuck_of_interprets M t u t2 s2 hXY with
    ⟨_, _, hRevLeft, hRevRight⟩
  have ht2List :
      __eo_is_list (Term.UOp UserOp.str_concat) t2 = Term.Boolean true :=
    eo_list_rev_cons_tail_list_of_ne_stuck
      (Term.UOp UserOp.str_concat) t t2 hRevLeft
  have hs2List :
      __eo_is_list (Term.UOp UserOp.str_concat) s2 = Term.Boolean true :=
    eo_list_rev_cons_tail_list_of_ne_stuck
      (Term.UOp UserOp.str_concat) u s2 hRevRight
  exact ⟨ht2List, hs2List,
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat) t2
      ht2List,
    eo_list_rev_ne_stuck_of_is_list_true (Term.UOp UserOp.str_concat) s2
      hs2List⟩

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq
    (M : SmtModel) (hM : model_total_typed M)
    (t u t2 s2 : Term) (T : SmtType)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hElimTailLeft :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2) ≠
        Term.Stuck)
    (hElimTailRight :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2) ≠
        Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  rcases str_concat_args_of_seq_type t t2 T hLeftTy with
    ⟨htTy, ht2Ty⟩
  rcases str_concat_args_of_seq_type u s2 T hRightTy with
    ⟨huTy, hs2Ty⟩
  rcases rev_elim_cons_operands_ne_stuck_of_interprets M t u t2 s2 hXY with
    ⟨hElimLeft, hElimRight, hRevLeft, hRevRight⟩
  rcases rev_elim_cons_tail_lists_of_interprets M t u t2 s2 hXY with
    ⟨ht2List, hs2List, hRevTailLeft, hRevTailRight⟩
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_seq M hM
    t u t2 s2 T hHead htTy huTy ht2List hs2List ht2Ty hs2Ty
    hRevLeft hRevRight hRevTailLeft hRevTailRight hElimLeft hElimRight
    hElimTailLeft hElimTailRight hXY

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip
    (M : SmtModel) (hM : model_total_typed M)
    (t u t2 s2 : Term) (T : SmtType)
    (_hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hElimTailLeft :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2) ≠
        Term.Stuck)
    (hElimTailRight :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2) ≠
        Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq M hM
    t u t2 s2 T hHead hLeftTy hRightTy hElimTailLeft
    hElimTailRight hXY

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_pair
    (M : SmtModel) (hM : model_total_typed M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hTailStrip : __str_strip_prefix t2 s2 = mkPair t2 s2)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  have hElimTailLeft :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2) ≠
        Term.Stuck := by
    simpa [hTailStrip, mkPair, pair_first_pair] using hFinalLeft
  have hElimTailRight :
      __str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2) ≠
        Term.Stuck := by
    simpa [hTailStrip, mkPair, pair_second_pair] using hFinalRight
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip M hM
    t u t2 s2 T hStrip hHead hLeftTy hRightTy hElimTailLeft
    hElimTailRight hXY

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_false
    (M : SmtModel) (hM : model_total_typed M)
    (t u a aTail b bTail : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t (mkConcat a aTail))
          (mkConcat u (mkConcat b bTail)) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t (mkConcat a aTail))) =
        SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u (mkConcat b bTail))) =
        SmtType.Seq T)
    (hTailHead : __eo_eq a b = Term.Boolean false)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first
              (__str_strip_prefix (mkConcat a aTail) (mkConcat b bTail)))) ≠
        Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second
              (__str_strip_prefix (mkConcat a aTail) (mkConcat b bTail)))) ≠
        Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat t (mkConcat a aTail))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat u (mkConcat b bTail)))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat a aTail)))
        (__str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat b bTail))))
      true := by
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_pair
    M hM t u (mkConcat a aTail) (mkConcat b bTail) T hStrip hHead
    hLeftTy hRightTy
    (str_strip_prefix_concat_of_eo_eq_false a b aTail bTail hTailHead)
    hFinalLeft hFinalRight hXY

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_left_not_concat
    (M : SmtModel) (hM : model_total_typed M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hT2NotConcat : ¬ ∃ head tail : Term, t2 = mkConcat head tail)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  have hTailStrip : __str_strip_prefix t2 s2 ≠ Term.Stuck :=
    str_strip_prefix_tail_ne_stuck_of_concat_eo_eq_true t u t2 s2
      hStrip hHead
  have ht2 : t2 ≠ Term.Stuck :=
    str_strip_prefix_left_ne_stuck_of_ne_stuck t2 s2 hTailStrip
  have hs2 : s2 ≠ Term.Stuck :=
    str_strip_prefix_right_ne_stuck_of_ne_stuck t2 s2 hTailStrip
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_pair
    M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy
    (str_strip_prefix_left_not_str_concat t2 s2 ht2 hs2 hT2NotConcat)
    hFinalLeft hFinalRight hXY

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_right_not_concat
    (M : SmtModel) (hM : model_total_typed M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hS2NotConcat : ¬ ∃ head tail : Term, s2 = mkConcat head tail)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  have hTailStrip : __str_strip_prefix t2 s2 ≠ Term.Stuck :=
    str_strip_prefix_tail_ne_stuck_of_concat_eo_eq_true t u t2 s2
      hStrip hHead
  have ht2 : t2 ≠ Term.Stuck :=
    str_strip_prefix_left_ne_stuck_of_ne_stuck t2 s2 hTailStrip
  have hs2 : s2 ≠ Term.Stuck :=
    str_strip_prefix_right_ne_stuck_of_ne_stuck t2 s2 hTailStrip
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_pair
    M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy
    (str_strip_prefix_right_not_str_concat t2 s2 ht2 hs2 hS2NotConcat)
    hFinalLeft hFinalRight hXY

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_stop
    (M : SmtModel) (hM : model_total_typed M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hTailStop :
      (¬ ∃ head tail : Term, t2 = mkConcat head tail) ∨
        (¬ ∃ head tail : Term, s2 = mkConcat head tail) ∨
        ∃ a aTail b bTail : Term,
          t2 = mkConcat a aTail ∧
          s2 = mkConcat b bTail ∧
          __eo_eq a b = Term.Boolean false)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  rcases hTailStop with hT2NotConcat | hTailStop
  · exact
      eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_left_not_concat
        M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy
        hT2NotConcat hFinalLeft hFinalRight hXY
  rcases hTailStop with hS2NotConcat | hTailFalse
  · exact
      eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_right_not_concat
        M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy
        hS2NotConcat hFinalLeft hFinalRight hXY
  rcases hTailFalse with
    ⟨a, aTail, b, bTail, hT2, hS2, hTailHead⟩
  subst t2
  subst s2
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_false
    M hM t u a aTail b bTail T hStrip hHead hLeftTy hRightTy
    hTailHead hFinalLeft hFinalRight hXY

private theorem concat_tail_stop_or_head_true_of_seq_type
    (t2 s2 : Term) (T : SmtType)
    (ht2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hs2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T) :
    ((¬ ∃ head tail : Term, t2 = mkConcat head tail) ∨
      (¬ ∃ head tail : Term, s2 = mkConcat head tail) ∨
      ∃ a aTail b bTail : Term,
        t2 = mkConcat a aTail ∧
        s2 = mkConcat b bTail ∧
        __eo_eq a b = Term.Boolean false) ∨
      ∃ a aTail b bTail : Term,
        t2 = mkConcat a aTail ∧
        s2 = mkConcat b bTail ∧
        __eo_eq a b = Term.Boolean true := by
  by_cases hT2Concat : ∃ head tail : Term, t2 = mkConcat head tail
  · rcases hT2Concat with ⟨a, aTail, hT2⟩
    by_cases hS2Concat : ∃ head tail : Term, s2 = mkConcat head tail
    · rcases hS2Concat with ⟨b, bTail, hS2⟩
      subst t2
      subst s2
      rcases str_concat_args_of_seq_type a aTail T ht2Ty with
        ⟨haTy, _haTailTy⟩
      rcases str_concat_args_of_seq_type b bTail T hs2Ty with
        ⟨hbTy, _hbTailTy⟩
      rcases eo_eq_cases_of_ne_stuck a b
          (term_ne_stuck_of_smt_type_seq a T haTy)
          (term_ne_stuck_of_smt_type_seq b T hbTy) with
        hHead | hHead
      · exact Or.inr ⟨a, aTail, b, bTail, rfl, rfl, hHead⟩
      · exact Or.inl (Or.inr (Or.inr
          ⟨a, aTail, b, bTail, rfl, rfl, hHead⟩))
    · exact Or.inl (Or.inr (Or.inl hS2Concat))
  · exact Or.inl (Or.inl hT2Concat)

private theorem concat_tail_stop_of_no_head_true_of_seq_type
    (t2 s2 : Term) (T : SmtType)
    (ht2Ty : __smtx_typeof (__eo_to_smt t2) = SmtType.Seq T)
    (hs2Ty : __smtx_typeof (__eo_to_smt s2) = SmtType.Seq T)
    (hNoHeadTrue :
      ¬ ∃ a aTail b bTail : Term,
        t2 = mkConcat a aTail ∧
        s2 = mkConcat b bTail ∧
        __eo_eq a b = Term.Boolean true) :
    (¬ ∃ head tail : Term, t2 = mkConcat head tail) ∨
      (¬ ∃ head tail : Term, s2 = mkConcat head tail) ∨
      ∃ a aTail b bTail : Term,
        t2 = mkConcat a aTail ∧
        s2 = mkConcat b bTail ∧
        __eo_eq a b = Term.Boolean false := by
  rcases concat_tail_stop_or_head_true_of_seq_type t2 s2 T ht2Ty hs2Ty with
    hStop | hHeadTrue
  · exact hStop
  · exact False.elim (hNoHeadTrue hHeadTrue)

private theorem eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_with_final
    (M : SmtModel) (hM : model_total_typed M)
    (t u t2 s2 : Term) (T : SmtType)
    (hStrip :
      __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck)
    (hHead : __eo_eq t u = Term.Boolean true)
    (hLeftTy :
      __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T)
    (hRightTy :
      __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T)
    (hFinalLeft :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hFinalRight :
      __str_nary_elim
          (__eo_list_rev (Term.UOp UserOp.str_concat)
            (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck)
    (hXY :
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
        true) :
    eo_interprets M
      (mkEq
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
        (__str_nary_elim (__eo_list_rev (Term.UOp UserOp.str_concat) s2)))
      true := by
  rcases str_concat_args_of_seq_type t t2 T hLeftTy with
    ⟨_htTy, ht2Ty⟩
  rcases str_concat_args_of_seq_type u s2 T hRightTy with
    ⟨_huTy, hs2Ty⟩
  rcases concat_tail_stop_or_head_true_of_seq_type t2 s2 T ht2Ty hs2Ty with
    hTailStop | hTailHeadTrue
  · exact
      eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_stop
        M hM t u t2 s2 T hStrip hHead hLeftTy hRightTy hTailStop
        hFinalLeft hFinalRight hXY
  · rcases hTailHeadTrue with
      ⟨a, aTail, b, bTail, hT2, hS2, _hTailHead⟩
    subst t2
    subst s2
    rcases rev_elim_cons_tail_lists_of_interprets
        M t u (mkConcat a aTail) (mkConcat b bTail) hXY with
      ⟨_hTailLeftList, _hTailRightList, hRevTailLeft,
        hRevTailRight⟩
    have hElimTailLeft :
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat a aTail)) ≠ Term.Stuck :=
      str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq a aTail T
        ht2Ty hRevTailLeft
    have hElimTailRight :
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (mkConcat b bTail)) ≠ Term.Stuck :=
      str_nary_elim_list_rev_str_concat_cons_ne_stuck_of_seq b bTail T
        hs2Ty hRevTailRight
    exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip
      M hM t u (mkConcat a aTail) (mkConcat b bTail) T hStrip hHead
      hLeftTy hRightTy hElimTailLeft hElimTailRight hXY

private theorem eo_typeof_eq_operands_same_of_bool (x y : Term)
    (hTy : __eo_typeof (mkEq x y) = Term.Bool) :
    __eo_typeof x = __eo_typeof y ∧
      __eo_typeof x ≠ Term.Stuck ∧
      __eo_typeof y ≠ Term.Stuck := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at hTy
  by_cases hx : __eo_typeof x = Term.Stuck
  · simp [hx, __eo_typeof_eq] at hTy
  by_cases hy : __eo_typeof y = Term.Stuck
  · simp [hy, __eo_typeof_eq] at hTy
  have hReq :
      __eo_requires (__eo_eq (__eo_typeof x) (__eo_typeof y))
        (Term.Boolean true) Term.Bool = Term.Bool := by
    simpa [hx, hy, __eo_typeof_eq] using hTy
  have hReqNonStuck :
      __eo_requires (__eo_eq (__eo_typeof x) (__eo_typeof y))
        (Term.Boolean true) Term.Bool ≠ Term.Stuck := by
    rw [hReq]
    intro h
    cases h
  have hEq :
      __eo_eq (__eo_typeof x) (__eo_typeof y) = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck
      (__eo_eq (__eo_typeof x) (__eo_typeof y))
      (Term.Boolean true) Term.Bool hReqNonStuck
  have hSame : __eo_typeof x = __eo_typeof y :=
    (eq_of_eo_eq_true_local (__eo_typeof x) (__eo_typeof y) hEq).symm
  exact ⟨hSame, hx, hy⟩

private theorem concatEq_result_operands_same_eo_type (rev s t : Term)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck)
    (hTy :
      __eo_typeof (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) =
        Term.Bool) :
    __eo_typeof (concatEqLhs rev s t) = __eo_typeof (concatEqRhs rev s t) ∧
      __eo_typeof (concatEqLhs rev s t) ≠ Term.Stuck ∧
      __eo_typeof (concatEqRhs rev s t) ≠ Term.Stuck := by
  have hProgEq := eo_prog_concat_eq_eq_of_ne_stuck rev s t hProg
  have hOutTy :
      __eo_typeof (mkEq (concatEqLhs rev s t) (concatEqRhs rev s t)) =
        Term.Bool := by
    simpa [hProgEq] using hTy
  exact eo_typeof_eq_operands_same_of_bool
    (concatEqLhs rev s t) (concatEqRhs rev s t) hOutTy

private theorem step_concat_eq_false_of_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean false) s t hProg
  have hFinalBool :=
    concatEq_false_has_bool_type_of_seq s t T hsTy htTy hIntroSNN hIntroTNN
      hProg
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq]
    exact eo_interprets_concat_eq_false_of_seq' M hM s t T hsTy htTy
      hIntroSNN hIntroTNN hPrem hProg
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) hFinalBool

private theorem step_concat_eq_false_of_left_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_false_of_seq M hM s t T hsTy htTy
    hIntroSNN hIntroTNN hProg

private theorem step_concat_eq_false_of_left_concat
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean false)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
      hIntroTNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_false_of_left_seq M hM (mkConcat sHead sTail) t T
    hPremBool hLeftTy hIntroLeftNN hIntroRightNN hProg

private theorem step_concat_eq_false_of_right_concat
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean false)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
      hIntroSNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_false_of_left_seq M hM s (mkConcat tHead tTail) T
    hPremBool hLeftTy hIntroLeftNN hIntroRightNN hProg

private theorem step_concat_eq_false_of_left_concat_empty_typeof
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean false)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
      hPremBool hEmptyTNN hIntroT with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_false_of_left_seq M hM (mkConcat sHead sTail) t T
    hPremBool hLeftTy hIntroLeftNN hIntroRightNN hProg

private theorem step_concat_eq_false_of_right_concat_empty_typeof
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean false)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
      hPremBool hEmptySNN hIntroS with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_false_of_left_seq M hM s (mkConcat tHead tTail) T
    hPremBool hLeftTy hIntroLeftNN hIntroRightNN hProg

private theorem step_concat_eq_true_of_seq_from_rev_strip
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean true) s t hProg
  have hFinalBool :=
    concatEq_true_has_bool_type_of_seq s t T hsTy htTy hIntroSNN
      hIntroTNN hProg
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq]
    exact eo_interprets_concat_eq_true_from_rev_strip M s t
      (hRevStrip hPrem) hCancel hProg
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) hFinalBool

private theorem step_concat_eq_true_of_seq_from_rev_strip_with_final
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean true) s t hProg
  have hFinalBool :=
    concatEq_true_has_bool_type_of_seq s t T hsTy htTy hIntroSNN
      hIntroTNN hProg
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq]
    exact eo_interprets_concat_eq_true_from_rev_strip_with_final M s t
      (hRevStrip hPrem) hCancel hProg
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) hFinalBool

private theorem step_concat_eq_true_of_left_seq_from_rev_strip_with_final
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_true_of_seq_from_rev_strip_with_final M hM s t T
    hsTy htTy hIntroSNN hIntroTNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_left_concat_from_rev_strip_with_final
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
      hIntroTNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_right_concat_from_rev_strip_with_final
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s (mkConcat tHead tTail)) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
      hIntroSNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_both_concat_from_rev_strip_with_final
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)))
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail))
        true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail)
            (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail)
          (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
      hPremBool with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final M hM
    (mkConcat sHead sTail) (mkConcat tHead tTail) T hPremBool
    hLeftTy hIntroLeftNN hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_left_concat_empty_typeof_from_rev_strip_with_final
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
      hPremBool hEmptyTNN hIntroT with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_right_concat_empty_typeof_from_rev_strip_with_final
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hRevStrip :
      eo_interprets M (mkEq s (mkConcat tHead tTail)) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
      hPremBool hEmptySNN hIntroS with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_seq_from_rev_strip_with_final_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean true) s t hProg
  have hFinalBool :=
    concatEq_true_has_bool_type_of_seq s t T hsTy htTy hIntroSNN
      hIntroTNN hProg
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq]
    exact eo_interprets_concat_eq_true_from_rev_strip_with_final_seq
      M s t T hsTy htTy hIntroSNN hIntroTNN (hRevStrip hPrem)
      hCancel hProg
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) hFinalBool

private theorem step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_true_of_seq_from_rev_strip_with_final_seq M hM
    s t T hsTy htTy hIntroSNN hIntroTNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_seq_from_rev_strip_with_final_seq_tail_stop
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hTailStop :
      ∀ a b aTail bTail : Term,
        __str_strip_prefix (mkConcat a aTail) (mkConcat b bTail) ≠
          Term.Stuck ->
        __eo_eq a b = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat a aTail)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat b bTail)) = SmtType.Seq T ->
        (¬ ∃ head tail : Term, aTail = mkConcat head tail) ∨
          (¬ ∃ head tail : Term, bTail = mkConcat head tail) ∨
          ∃ aHead aRest bHead bRest : Term,
            aTail = mkConcat aHead aRest ∧
            bTail = mkConcat bHead bRest ∧
            __eo_eq aHead bHead = Term.Boolean false)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  refine step_concat_eq_true_of_seq_from_rev_strip_with_final_seq M hM
    s t T hsTy htTy hIntroSNN hIntroTNN hRevStrip ?_ hProg
  intro a b aTail bTail hStrip hHead hLeftTy hRightTy hFinalLeft
    hFinalRight hXY
  exact eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_tail_stop
    M hM a b aTail bTail T hStrip hHead hLeftTy hRightTy
    (hTailStop a b aTail bTail hStrip hHead hLeftTy hRightTy)
    hFinalLeft hFinalRight hXY

private theorem step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq_tail_stop
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hTailStop :
      ∀ a b aTail bTail : Term,
        __str_strip_prefix (mkConcat a aTail) (mkConcat b bTail) ≠
          Term.Stuck ->
        __eo_eq a b = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat a aTail)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat b bTail)) = SmtType.Seq T ->
        (¬ ∃ head tail : Term, aTail = mkConcat head tail) ∨
          (¬ ∃ head tail : Term, bTail = mkConcat head tail) ∨
          ∃ aHead aRest bHead bRest : Term,
            aTail = mkConcat aHead aRest ∧
            bTail = mkConcat bHead bRest ∧
            __eo_eq aHead bHead = Term.Boolean false)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_true_of_seq_from_rev_strip_with_final_seq_tail_stop
    M hM s t T hsTy htTy hIntroSNN hIntroTNN hRevStrip hTailStop hProg

private theorem step_concat_eq_true_of_seq_from_rev_strip_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  refine step_concat_eq_true_of_seq_from_rev_strip_with_final_seq M hM
    s t T hsTy htTy hIntroSNN hIntroTNN hRevStrip ?_ hProg
  intro a b aTail bTail hStrip hHead hLeftTy hRightTy hFinalLeft
    hFinalRight hXY
  exact
    eo_interprets_rev_tails_of_head_eo_eq_true_of_cons_seq_strip_with_final
      M hM a b aTail bTail T hStrip hHead hLeftTy hRightTy
      hFinalLeft hFinalRight hXY

private theorem step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_true_of_seq_from_rev_strip_with_final_seq_cancel
    M hM s t T hsTy htTy hIntroSNN hIntroTNN hRevStrip hProg

private theorem step_concat_eq_true_of_seq_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  refine step_concat_eq_true_of_seq_from_rev_strip_with_final_seq_cancel
    M hM s t T hsTy htTy hIntroSNN hIntroTNN ?_ hProg
  intro hPrem
  exact eo_interprets_double_rev_intros_of_prog_seq M hM s t T
    hsTy htTy hIntroSNN hIntroTNN hProg hPrem

private theorem step_concat_eq_true_of_left_seq_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_true_of_seq_with_final_seq_cancel M hM s t T
    hsTy htTy hIntroSNN hIntroTNN hProg

private theorem step_concat_eq_true_of_left_concat_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
      hIntroTNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_right_concat_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
      hIntroSNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_left_concat_intro_eq_self_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroEq : __str_nary_intro t = t)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat_intro_eq_self sHead sTail t
      hPremBool hIntroEq with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_right_concat_intro_eq_self_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroEq : __str_nary_intro s = s)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat_intro_eq_self s tHead tTail
      hPremBool hIntroEq with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_both_concat_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail)
            (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail)
          (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
      hPremBool with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    (mkConcat sHead sTail) (mkConcat tHead tTail) T hPremBool
    hLeftTy hIntroLeftNN hIntroRightNN hProg

private theorem step_concat_eq_true_of_left_concat_empty_typeof_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
      hPremBool hEmptyTNN hIntroT with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_right_concat_empty_typeof_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
      hPremBool hEmptySNN hIntroS with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_with_final_seq_cancel M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hProg

private theorem step_concat_eq_true_of_left_concat_from_rev_strip_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
      hIntroTNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq_cancel
    M hM (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hProg

private theorem step_concat_eq_true_of_right_concat_from_rev_strip_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s (mkConcat tHead tTail)) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
      hIntroSNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq_cancel
    M hM s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hProg

private theorem step_concat_eq_true_of_both_concat_from_rev_strip_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)))
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail))
        true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail)
            (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail)
          (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
      hPremBool with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq_cancel
    M hM (mkConcat sHead sTail) (mkConcat tHead tTail) T hPremBool
    hLeftTy hIntroLeftNN hIntroRightNN hRevStrip hProg

private theorem step_concat_eq_true_of_left_concat_empty_typeof_from_rev_strip_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
      hPremBool hEmptyTNN hIntroT with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq_cancel
    M hM (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hProg

private theorem step_concat_eq_true_of_right_concat_empty_typeof_from_rev_strip_with_final_seq_cancel
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hRevStrip :
      eo_interprets M (mkEq s (mkConcat tHead tTail)) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
      hPremBool hEmptySNN hIntroS with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq_cancel
    M hM s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hProg

private theorem step_concat_eq_true_of_left_concat_from_rev_strip_with_final_seq
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ T : SmtType, ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
      hIntroTNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip (hCancel T) hProg

private theorem step_concat_eq_true_of_right_concat_from_rev_strip_with_final_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s (mkConcat tHead tTail)) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hCancel :
      ∀ T : SmtType, ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
      hIntroSNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip (hCancel T) hProg

private theorem step_concat_eq_true_of_both_concat_from_rev_strip_with_final_seq
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)))
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail))
        true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hCancel :
      ∀ T : SmtType, ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail)
            (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail)
          (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
      hPremBool with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq M hM
    (mkConcat sHead sTail) (mkConcat tHead tTail) T hPremBool
    hLeftTy hIntroLeftNN hIntroRightNN hRevStrip (hCancel T) hProg

private theorem step_concat_eq_true_of_left_concat_empty_typeof_from_rev_strip_with_final_seq
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ T : SmtType, ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
      hPremBool hEmptyTNN hIntroT with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip (hCancel T) hProg

private theorem step_concat_eq_true_of_right_concat_empty_typeof_from_rev_strip_with_final_seq
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hRevStrip :
      eo_interprets M (mkEq s (mkConcat tHead tTail)) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hCancel :
      ∀ T : SmtType, ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        __smtx_typeof (__eo_to_smt (mkConcat t t2)) = SmtType.Seq T ->
        __smtx_typeof (__eo_to_smt (mkConcat u s2)) = SmtType.Seq T ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_first (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        __str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__pair_second (__str_strip_prefix t2 s2))) ≠ Term.Stuck ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
      hPremBool hEmptySNN hIntroS with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip_with_final_seq M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip (hCancel T) hProg

private theorem step_concat_eq_true_of_left_seq_from_rev_strip
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T :=
    eq_bool_right_seq_of_left_seq s t T hPremBool hsTy
  exact step_concat_eq_true_of_seq_from_rev_strip M hM s t T hsTy htTy
    hIntroSNN hIntroTNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_left_concat_from_rev_strip
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hIntroTNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
        SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
      hIntroTNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_right_concat_from_rev_strip
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hIntroSNN :
      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
        SmtType.None)
    (hRevStrip :
      eo_interprets M (mkEq s (mkConcat tHead tTail)) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
      hIntroSNN with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_both_concat_from_rev_strip
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type
        (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)))
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) (mkConcat tHead tTail))
        true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail)
            (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail)
          (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
      hPremBool with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip M hM
    (mkConcat sHead sTail) (mkConcat tHead tTail) T hPremBool
    hLeftTy hIntroLeftNN hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_left_concat_empty_typeof_from_rev_strip
    (M : SmtModel) (hM : model_total_typed M)
    (sHead sTail t : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq (mkConcat sHead sTail) t))
    (hEmptyTNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
        SmtType.None)
    (hIntroT : __str_nary_intro t ≠ Term.Stuck)
    (hRevStrip :
      eo_interprets M (mkEq (mkConcat sHead sTail) t) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat sHead sTail)))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro t)))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq (mkConcat sHead sTail) t)) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq (mkConcat sHead sTail) t]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq (mkConcat sHead sTail) t))) := by
  rcases concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
      hPremBool hEmptyTNN hIntroT with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip M hM
    (mkConcat sHead sTail) t T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_true_of_right_concat_empty_typeof_from_rev_strip
    (M : SmtModel) (hM : model_total_typed M)
    (s tHead tTail : Term)
    (hPremBool :
      RuleProofs.eo_has_bool_type (mkEq s (mkConcat tHead tTail)))
    (hEmptySNN :
      __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
        SmtType.None)
    (hIntroS : __str_nary_intro s ≠ Term.Stuck)
    (hRevStrip :
      eo_interprets M (mkEq s (mkConcat tHead tTail)) true ->
      eo_interprets M
        (mkEq
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro s))))
          (__str_nary_elim
            (__eo_list_rev (Term.UOp UserOp.str_concat)
              (__eo_list_rev (Term.UOp UserOp.str_concat)
                (__str_nary_intro (mkConcat tHead tTail))))))
        true)
    (hCancel :
      ∀ t u t2 s2 : Term,
        __str_strip_prefix (mkConcat t t2) (mkConcat u s2) ≠ Term.Stuck ->
        __eo_eq t u = Term.Boolean true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat t t2)))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) (mkConcat u s2))))
          true ->
        eo_interprets M
          (mkEq
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) t2))
            (__str_nary_elim
              (__eo_list_rev (Term.UOp UserOp.str_concat) s2))) true)
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true)
          (Proof.pf (mkEq s (mkConcat tHead tTail))) ≠ Term.Stuck) :
    StepRuleProperties M [mkEq s (mkConcat tHead tTail)]
      (__eo_prog_concat_eq (Term.Boolean true)
        (Proof.pf (mkEq s (mkConcat tHead tTail)))) := by
  rcases concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
      hPremBool hEmptySNN hIntroS with
    ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
  exact step_concat_eq_true_of_left_seq_from_rev_strip M hM
    s (mkConcat tHead tTail) T hPremBool hLeftTy hIntroLeftNN
    hIntroRightNN hRevStrip hCancel hProg

private theorem step_concat_eq_false_of_not_str_concat_eo_eq_false
    (M : SmtModel) (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hHead : __eo_eq s t = Term.Boolean false) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean false) s t hProg
  have hIntroS :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck
      (Term.Boolean false) s t hProg
  have hIntroT :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck
      (Term.Boolean false) s t hProg
  have hLhs :=
    concatEq_false_lhs_eq_of_not_str_concat_eo_eq_false s t
      hSNotConcat hTNotConcat hIntroS hIntroT hHead
  have hRhs :=
    concatEq_false_rhs_eq_of_not_str_concat_eo_eq_false s t
      hSNotConcat hTNotConcat hIntroS hIntroT hHead
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq, hLhs, hRhs]
    exact hPrem
  · rw [hProgEq, hLhs, hRhs]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq s t) hPremBool

private theorem step_concat_eq_true_of_not_str_concat_eo_eq_false
    (M : SmtModel) (s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hHead : __eo_eq s t = Term.Boolean false) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean true) s t hProg
  have hIntroS :=
    str_nary_intro_left_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg
  have hIntroT :=
    str_nary_intro_right_ne_stuck_of_prog_ne_stuck
      (Term.Boolean true) s t hProg
  have hRevS :=
    concatEq_true_rev_intro_left_ne_stuck_of_prog_ne_stuck s t hProg
  have hRevT :=
    concatEq_true_rev_intro_right_ne_stuck_of_prog_ne_stuck s t hProg
  have hLhs :=
    concatEq_true_lhs_eq_of_not_str_concat_eo_eq_false s t
      hSNotConcat hTNotConcat hIntroS hIntroT hRevS hRevT hHead
  have hRhs :=
    concatEq_true_rhs_eq_of_not_str_concat_eo_eq_false s t
      hSNotConcat hTNotConcat hIntroS hIntroT hRevS hRevT hHead
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    have hPrem : eo_interprets M (mkEq s t) true :=
      hPremisesTrue (mkEq s t) (by simp)
    rw [hProgEq, hLhs, hRhs]
    exact hPrem
  · rw [hProgEq, hLhs, hRhs]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq s t) hPremBool

private theorem step_concat_eq_of_not_str_concat_eo_eq_false
    (M : SmtModel) (rev s t : Term)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠
      Term.Stuck)
    (hSNotConcat : ¬ ∃ head tail : Term, s = mkConcat head tail)
    (hTNotConcat : ¬ ∃ head tail : Term, t = mkConcat head tail)
    (hHead : __eo_eq s t = Term.Boolean false) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) := by
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · subst rev
    exact step_concat_eq_true_of_not_str_concat_eo_eq_false M s t
      hPremBool hProg hSNotConcat hTNotConcat hHead
  · subst rev
    exact step_concat_eq_false_of_not_str_concat_eo_eq_false M s t
      hPremBool hProg hSNotConcat hTNotConcat hHead

private theorem step_concat_eq_false_of_eo_eq_true
    (M : SmtModel) (s t : Term)
    (hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean false) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean false) s t hProg
  have hOperands :=
    concatEq_false_lhs_eq_rhs_of_eo_eq_true s t hProg hHead
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    rw [hProgEq, hOperands]
    exact eo_interprets_eq_self_of_has_bool_type M
      (concatEqRhs (Term.Boolean false) s t)
      (by simpa [hOperands] using hFinalBool)
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean false) s t)
        (concatEqRhs (Term.Boolean false) s t)) hFinalBool

private theorem step_concat_eq_true_of_eo_eq_true
    (M : SmtModel) (s t : Term)
    (hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)))
    (hProg :
      __eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t)) ≠
        Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq (Term.Boolean true) (Proof.pf (mkEq s t))) := by
  have hProgEq :=
    eo_prog_concat_eq_eq_of_ne_stuck (Term.Boolean true) s t hProg
  have hOperands :=
    concatEq_true_lhs_eq_rhs_of_eo_eq_true s t hProg hHead
  refine ⟨?_, ?_⟩
  · intro hPremisesTrue
    rw [hProgEq, hOperands]
    exact eo_interprets_eq_self_of_has_bool_type M
      (concatEqRhs (Term.Boolean true) s t)
      (by simpa [hOperands] using hFinalBool)
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type
      (mkEq (concatEqLhs (Term.Boolean true) s t)
        (concatEqRhs (Term.Boolean true) s t)) hFinalBool

private theorem step_concat_eq_of_eo_eq_true
    (M : SmtModel) (rev s t : Term)
    (hFinalBool : RuleProofs.eo_has_bool_type
      (mkEq (concatEqLhs rev s t) (concatEqRhs rev s t)))
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠
      Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) := by
  rcases concatEq_rev_cases_of_prog_ne_stuck rev s t hProg with hRev | hRev
  · subst rev
    exact step_concat_eq_true_of_eo_eq_true M s t
      (by simpa using hFinalBool) hProg hHead
  · subst rev
    exact step_concat_eq_false_of_eo_eq_true M s t
      (by simpa using hFinalBool) hProg hHead

private theorem step_concat_eq_of_left_seq_eo_eq_true
    (M : SmtModel) (rev s t : Term) (T : SmtType)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T)
    (hIntroSNN : __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
      SmtType.None)
    (hIntroTNN : __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
      SmtType.None)
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠
      Term.Stuck)
    (hHead : __eo_eq s t = Term.Boolean true) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) := by
  exact step_concat_eq_of_eo_eq_true M rev s t
    (concatEq_has_bool_type_of_left_seq rev s t T hPremBool hsTy
      hIntroSNN hIntroTNN hProg)
    hProg hHead

private theorem step_concat_eq_core
    (M : SmtModel) (hM : model_total_typed M)
    (rev s t : Term)
    (hRevTrans : RuleProofs.eo_has_smt_translation rev)
    (hPremBool : RuleProofs.eo_has_bool_type (mkEq s t))
    (hProg : __eo_prog_concat_eq rev (Proof.pf (mkEq s t)) ≠ Term.Stuck)
    (hResultTy :
      __eo_typeof (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) =
        Term.Bool) :
    StepRuleProperties M [mkEq s t]
      (__eo_prog_concat_eq rev (Proof.pf (mkEq s t))) := by
  have hProgEq := eo_prog_concat_eq_eq_of_ne_stuck rev s t hProg
  have hRevCases := concatEq_rev_cases_of_prog_ne_stuck rev s t hProg
  have hOutEoTypes := concatEq_result_operands_same_eo_type rev s t hProg hResultTy
  by_cases hFalseSeq :
      rev = Term.Boolean false ∧
        ∃ T,
          __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
          __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠ SmtType.None ∧
          __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠ SmtType.None
  · rcases hFalseSeq with ⟨hRev, T, hsTy, hIntroSNN, hIntroTNN⟩
    subst rev
    exact step_concat_eq_false_of_left_seq M hM s t T hPremBool hsTy
      hIntroSNN hIntroTNN hProg
  · by_cases hTrueSeqHead :
        rev = Term.Boolean true ∧
          ∃ T,
            __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
            __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
              SmtType.None ∧
            __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
              SmtType.None ∧
            __eo_eq s t = Term.Boolean true
    · rcases hTrueSeqHead with
        ⟨hRev, T, hsTy, hIntroSNN, hIntroTNN, hHead⟩
      subst rev
      exact step_concat_eq_of_left_seq_eo_eq_true M (Term.Boolean true)
        s t T hPremBool hsTy hIntroSNN hIntroTNN hProg hHead
    · by_cases hNonConcatHead :
        (¬ ∃ head tail : Term, s = mkConcat head tail) ∧
          (¬ ∃ head tail : Term, t = mkConcat head tail) ∧
          __eo_eq s t = Term.Boolean false
      · rcases hNonConcatHead with ⟨hSNotConcat, hTNotConcat, hHead⟩
        exact step_concat_eq_of_not_str_concat_eo_eq_false M rev s t
          hPremBool hProg hSNotConcat hTNotConcat hHead
      · by_cases hTrueSeqNonConcat :
            rev = Term.Boolean true ∧
              ∃ T,
                __smtx_typeof (__eo_to_smt s) = SmtType.Seq T ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                  SmtType.None ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                  SmtType.None ∧
                (¬ ∃ head tail : Term, s = mkConcat head tail) ∧
                (¬ ∃ head tail : Term, t = mkConcat head tail)
        · rcases hTrueSeqNonConcat with
            ⟨hRev, T, hsTy, hIntroSNN, hIntroTNN, hSNotConcat,
              hTNotConcat⟩
          subst rev
          have hIntroS :=
            str_nary_intro_left_ne_stuck_of_prog_ne_stuck
              (Term.Boolean true) s t hProg
          have hIntroT :=
            str_nary_intro_right_ne_stuck_of_prog_ne_stuck
              (Term.Boolean true) s t hProg
          have hsNonStuck :=
            str_nary_intro_arg_ne_stuck_of_ne_stuck s hIntroS
          have htNonStuck :=
            str_nary_intro_arg_ne_stuck_of_ne_stuck t hIntroT
          rcases eo_eq_cases_of_ne_stuck s t hsNonStuck htNonStuck with
            hHead | hHead
          · exact False.elim
              (hTrueSeqHead
                ⟨rfl, T, hsTy, hIntroSNN, hIntroTNN, hHead⟩)
          · exact False.elim
              (hNonConcatHead ⟨hSNotConcat, hTNotConcat, hHead⟩)
        · -- Remaining core: the `rev = true` suffix-canceling branch, plus the
          -- side-condition proof that a successful `rev = false` step supplies the
          -- sequence/intro-translation package consumed above.
          have hNotFalseBothConcat :
              ¬ (rev = Term.Boolean false ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail)) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, ⟨tHead, tTail, hT⟩⟩
            subst rev
            subst s
            subst t
            have hPack :=
              concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
                hPremBool
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseLeftConcatWithRightIntro :
              ¬ (rev = Term.Boolean false ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hIntroTNN⟩
            subst rev
            subst s
            have hPack :=
              concatEq_seq_pack_of_left_concat sHead sTail t hPremBool
                hIntroTNN
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseLeftConcatWithRightIntroEqSelf :
              ¬ (rev = Term.Boolean false ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hIntroEq⟩
            subst rev
            subst s
            have hPack :=
              concatEq_seq_pack_of_left_concat_intro_eq_self sHead sTail t
                hPremBool hIntroEq
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseRightConcatWithLeftIntro :
              ¬ (rev = Term.Boolean false ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hIntroSNN⟩
            subst rev
            subst t
            have hPack :=
              concatEq_seq_pack_of_right_concat s tHead tTail hPremBool
                hIntroSNN
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseRightConcatWithLeftIntroEqSelf :
              ¬ (rev = Term.Boolean false ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hIntroEq⟩
            subst rev
            subst t
            have hPack :=
              concatEq_seq_pack_of_right_concat_intro_eq_self s tHead tTail
                hPremBool hIntroEq
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseLeftConcatWithRightEmpty :
              ¬ (rev = Term.Boolean false ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hEmptyTNN⟩
            subst rev
            subst s
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) (mkConcat sHead sTail) t hProg
            have hPack :=
              concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
                hPremBool hEmptyTNN hIntroT
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseRightConcatWithLeftEmpty :
              ¬ (rev = Term.Boolean false ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hEmptySNN⟩
            subst rev
            subst t
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s (mkConcat tHead tTail) hProg
            have hPack :=
              concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
                hPremBool hEmptySNN hIntroS
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseBothNotConcatIntroEqSelf :
              ¬ (rev = Term.Boolean false ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, _hTNotConcat, hIntroSEq,
                hIntroTEq⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hPack :=
              concatEq_seq_pack_of_not_concat_intros_eq_self s t
                hPremBool hSNotConcat hIntroS hIntroSEq hIntroTEq
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseBothNotConcatLeftIntroEqSelfRightEmpty :
              ¬ (rev = Term.Boolean false ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, _hTNotConcat, hIntroSEq,
                hEmptyTNN⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hPack :=
              concatEq_seq_pack_of_not_concat_left_intro_eq_self_right_empty_typeof
                s t hPremBool hSNotConcat hIntroS hIntroSEq hEmptyTNN
                hIntroT
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseBothNotConcatRightIntroEqSelfLeftEmpty :
              ¬ (rev = Term.Boolean false ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, _hSNotConcat, hTNotConcat, hEmptySNN,
                hIntroTEq⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hPack :=
              concatEq_seq_pack_of_not_concat_right_intro_eq_self_left_empty_typeof
                s t hPremBool hTNotConcat hIntroT hIntroTEq hEmptySNN
                hIntroS
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotFalseBothNotConcatEmptyTypeof :
              ¬ (rev = Term.Boolean false ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, _hSNotConcat, _hTNotConcat, hEmptySNN,
                hEmptyTNN⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean false) s t hProg
            have hPack :=
              concatEq_seq_pack_of_empty_typeof_intros s t hPremBool
                hEmptySNN hIntroS hEmptyTNN hIntroT
            exact hFalseSeq ⟨rfl, hPack⟩
          have hNotTrueBothConcatHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, ⟨tHead, tTail, hT⟩,
                hHead⟩
            subst rev
            subst s
            subst t
            rcases concatEq_seq_pack_of_both_concat sHead sTail tHead tTail
                hPremBool with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueBothNotConcatIntroEqSelf :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, hTNotConcat, hIntroSEq,
                hIntroTEq⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            rcases concatEq_seq_pack_of_not_concat_intros_eq_self s t
                hPremBool hSNotConcat hIntroS hIntroSEq hIntroTEq with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqNonConcat
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN,
                hSNotConcat, hTNotConcat⟩
          have hNotTrueBothNotConcatLeftIntroEqSelfRightEmpty :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, hTNotConcat, hIntroSEq,
                hEmptyTNN⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            rcases
                concatEq_seq_pack_of_not_concat_left_intro_eq_self_right_empty_typeof
                  s t hPremBool hSNotConcat hIntroS hIntroSEq
                  hEmptyTNN hIntroT with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqNonConcat
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN,
                hSNotConcat, hTNotConcat⟩
          have hNotTrueBothNotConcatRightIntroEqSelfLeftEmpty :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __str_nary_intro t = t) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, hTNotConcat, hEmptySNN,
                hIntroTEq⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            rcases
                concatEq_seq_pack_of_not_concat_right_intro_eq_self_left_empty_typeof
                  s t hPremBool hTNotConcat hIntroT hIntroTEq
                  hEmptySNN hIntroS with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqNonConcat
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN,
                hSNotConcat, hTNotConcat⟩
          have hNotTrueBothNotConcatEmptyTypeof :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None) := by
            intro h
            rcases h with
              ⟨hRev, hSNotConcat, hTNotConcat, hEmptySNN,
                hEmptyTNN⟩
            subst rev
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s t hProg
            rcases concatEq_seq_pack_of_empty_typeof_intros s t hPremBool
                hEmptySNN hIntroS hEmptyTNN hIntroT with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqNonConcat
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN,
                hSNotConcat, hTNotConcat⟩
          have hNotTrueLeftConcatWithRightIntroHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                  SmtType.None ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hIntroTNN, hHead⟩
            subst rev
            subst s
            rcases concatEq_seq_pack_of_left_concat sHead sTail t
                hPremBool hIntroTNN with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueLeftConcatWithRightIntroEqSelfHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __str_nary_intro t = t ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hIntroEq, hHead⟩
            subst rev
            subst s
            rcases concatEq_seq_pack_of_left_concat_intro_eq_self sHead
                sTail t hPremBool hIntroEq with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueRightConcatWithLeftIntroHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                  SmtType.None ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hIntroSNN, hHead⟩
            subst rev
            subst t
            rcases concatEq_seq_pack_of_right_concat s tHead tTail
                hPremBool hIntroSNN with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueRightConcatWithLeftIntroEqSelfHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __str_nary_intro s = s ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hIntroEq, hHead⟩
            subst rev
            subst t
            rcases concatEq_seq_pack_of_right_concat_intro_eq_self s tHead
                tTail hPremBool hIntroEq with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueLeftConcatWithRightEmptyHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof t))) ≠
                  SmtType.None ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨sHead, sTail, hS⟩, hEmptyTNN, hHead⟩
            subst rev
            subst s
            have hIntroT :
                __str_nary_intro t ≠ Term.Stuck :=
              str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) (mkConcat sHead sTail) t hProg
            rcases concatEq_seq_pack_of_left_concat_empty_typeof sHead sTail t
                hPremBool hEmptyTNN hIntroT with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueRightConcatWithLeftEmptyHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __smtx_typeof
                    (__eo_to_smt (__seq_empty (__eo_typeof s))) ≠
                  SmtType.None ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨hRev, ⟨tHead, tTail, hT⟩, hEmptySNN, hHead⟩
            subst rev
            subst t
            have hIntroS :
                __str_nary_intro s ≠ Term.Stuck :=
              str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                (Term.Boolean true) s (mkConcat tHead tTail) hProg
            rcases concatEq_seq_pack_of_right_concat_empty_typeof s tHead tTail
                hPremBool hEmptySNN hIntroS with
              ⟨T, hLeftTy, hIntroLeftNN, hIntroRightNN⟩
            exact hTrueSeqHead
              ⟨rfl, T, hLeftTy, hIntroLeftNN, hIntroRightNN, hHead⟩
          have hNotTrueLeftConcatRightNotConcatHead :
              ¬ (rev = Term.Boolean true ∧
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (¬ ∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨_hRev, ⟨sHead, sTail, hS⟩, hTNotConcat, hHead⟩
            subst s
            exact eo_eq_true_left_concat_right_not_concat_false
              sHead sTail t hTNotConcat hHead
          have hNotTrueRightConcatLeftNotConcatHead :
              ¬ (rev = Term.Boolean true ∧
                (¬ ∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                __eo_eq s t = Term.Boolean true) := by
            intro h
            rcases h with
              ⟨_hRev, hSNotConcat, ⟨tHead, tTail, hT⟩, hHead⟩
            subst t
            exact eo_eq_true_left_not_concat_right_concat_false
              s tHead tTail hSNotConcat hHead
          rcases hRevCases with hRev | hRev
          · subst rev
            by_cases hBothConcat :
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                  (∃ tHead tTail : Term, t = mkConcat tHead tTail)
            · rcases hBothConcat with
                ⟨⟨sHead, sTail, hS⟩, ⟨tHead, tTail, hT⟩⟩
              subst s
              subst t
              exact step_concat_eq_true_of_both_concat_with_final_seq_cancel
                M hM sHead sTail tHead tTail hPremBool hProg
            · by_cases hLeftConcatWithRightIntro :
                  (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                    __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                      SmtType.None
              · rcases hLeftConcatWithRightIntro with
                  ⟨⟨sHead, sTail, hS⟩, hIntroTNN⟩
                subst s
                exact
                  step_concat_eq_true_of_left_concat_with_final_seq_cancel
                    M hM sHead sTail t hPremBool hIntroTNN hProg
              · by_cases hRightConcatWithLeftIntro :
                    (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                        SmtType.None
                · rcases hRightConcatWithLeftIntro with
                    ⟨⟨tHead, tTail, hT⟩, hIntroSNN⟩
                  subst t
                  exact
                    step_concat_eq_true_of_right_concat_with_final_seq_cancel
                      M hM s tHead tTail hPremBool hIntroSNN hProg
                · by_cases hLeftConcatWithRightIntroEqSelf :
                      (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                        __str_nary_intro t = t
                  · rcases hLeftConcatWithRightIntroEqSelf with
                      ⟨⟨sHead, sTail, hS⟩, hIntroEq⟩
                    subst s
                    exact
                      step_concat_eq_true_of_left_concat_intro_eq_self_with_final_seq_cancel
                        M hM sHead sTail t hPremBool hIntroEq hProg
                  · by_cases hRightConcatWithLeftIntroEqSelf :
                        (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                          __str_nary_intro s = s
                    · rcases hRightConcatWithLeftIntroEqSelf with
                        ⟨⟨tHead, tTail, hT⟩, hIntroEq⟩
                      subst t
                      exact
                        step_concat_eq_true_of_right_concat_intro_eq_self_with_final_seq_cancel
                          M hM s tHead tTail hPremBool hIntroEq hProg
                    · by_cases hLeftConcatWithRightEmpty :
                          (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                            __smtx_typeof
                                (__eo_to_smt
                                  (__seq_empty (__eo_typeof t))) ≠
                              SmtType.None
                      · rcases hLeftConcatWithRightEmpty with
                          ⟨⟨sHead, sTail, hS⟩, hEmptyTNN⟩
                        subst s
                        have hIntroT :
                            __str_nary_intro t ≠ Term.Stuck :=
                          str_nary_intro_right_ne_stuck_of_prog_ne_stuck
                            (Term.Boolean true) (mkConcat sHead sTail) t
                            hProg
                        exact
                          step_concat_eq_true_of_left_concat_empty_typeof_with_final_seq_cancel
                            M hM sHead sTail t hPremBool hEmptyTNN hIntroT
                            hProg
                      · by_cases hRightConcatWithLeftEmpty :
                            (∃ tHead tTail : Term,
                              t = mkConcat tHead tTail) ∧
                              __smtx_typeof
                                  (__eo_to_smt
                                    (__seq_empty (__eo_typeof s))) ≠
                                SmtType.None
                        · rcases hRightConcatWithLeftEmpty with
                            ⟨⟨tHead, tTail, hT⟩, hEmptySNN⟩
                          subst t
                          have hIntroS :
                              __str_nary_intro s ≠ Term.Stuck :=
                            str_nary_intro_left_ne_stuck_of_prog_ne_stuck
                              (Term.Boolean true) s (mkConcat tHead tTail)
                              hProg
                          exact
                            step_concat_eq_true_of_right_concat_empty_typeof_with_final_seq_cancel
                              M hM s tHead tTail hPremBool hEmptySNN
                              hIntroS hProg
                        · by_cases hBothNotConcatIntroEqSelf :
                              (¬ ∃ sHead sTail : Term,
                                s = mkConcat sHead sTail) ∧
                                (¬ ∃ tHead tTail : Term,
                                  t = mkConcat tHead tTail) ∧
                                __str_nary_intro s = s ∧
                                __str_nary_intro t = t
                          · exact False.elim
                              (hNotTrueBothNotConcatIntroEqSelf
                                ⟨rfl, hBothNotConcatIntroEqSelf.1,
                                  hBothNotConcatIntroEqSelf.2.1,
                                  hBothNotConcatIntroEqSelf.2.2⟩)
                          · by_cases
                              hBothNotConcatLeftIntroEqSelfRightEmpty :
                                (¬ ∃ sHead sTail : Term,
                                  s = mkConcat sHead sTail) ∧
                                  (¬ ∃ tHead tTail : Term,
                                    t = mkConcat tHead tTail) ∧
                                  __str_nary_intro s = s ∧
                                  __smtx_typeof
                                      (__eo_to_smt
                                        (__seq_empty (__eo_typeof t))) ≠
                                    SmtType.None
                            · exact False.elim
                                (hNotTrueBothNotConcatLeftIntroEqSelfRightEmpty
                                  ⟨rfl,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.1,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.2.1,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.2.2⟩)
                            · by_cases
                                hBothNotConcatRightIntroEqSelfLeftEmpty :
                                  (¬ ∃ sHead sTail : Term,
                                    s = mkConcat sHead sTail) ∧
                                    (¬ ∃ tHead tTail : Term,
                                      t = mkConcat tHead tTail) ∧
                                    __smtx_typeof
                                        (__eo_to_smt
                                          (__seq_empty (__eo_typeof s))) ≠
                                      SmtType.None ∧
                                    __str_nary_intro t = t
                              · exact False.elim
                                  (hNotTrueBothNotConcatRightIntroEqSelfLeftEmpty
                                    ⟨rfl,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.1,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.2.1,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.2.2⟩)
                              · by_cases hBothNotConcatEmptyTypeof :
                                    (¬ ∃ sHead sTail : Term,
                                      s = mkConcat sHead sTail) ∧
                                      (¬ ∃ tHead tTail : Term,
                                        t = mkConcat tHead tTail) ∧
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__seq_empty (__eo_typeof s))) ≠
                                        SmtType.None ∧
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__seq_empty (__eo_typeof t))) ≠
                                        SmtType.None
                                · exact False.elim
                                    (hNotTrueBothNotConcatEmptyTypeof
                                      ⟨rfl, hBothNotConcatEmptyTypeof.1,
                                        hBothNotConcatEmptyTypeof.2.1,
                                        hBothNotConcatEmptyTypeof.2.2⟩)
                                · by_cases hBothNotConcatHeadFalse :
                                      (¬ ∃ sHead sTail : Term,
                                        s = mkConcat sHead sTail) ∧
                                        (¬ ∃ tHead tTail : Term,
                                          t = mkConcat tHead tTail) ∧
                                        __eo_eq s t = Term.Boolean false
                                  · exact False.elim
                                      (hNonConcatHead hBothNotConcatHeadFalse)
                                  · by_cases hLeftConcatRightNotConcatHead :
                                        (∃ sHead sTail : Term,
                                          s = mkConcat sHead sTail) ∧
                                          (¬ ∃ tHead tTail : Term,
                                            t = mkConcat tHead tTail) ∧
                                          __eo_eq s t = Term.Boolean true
                                    · exact False.elim
                                        (hNotTrueLeftConcatRightNotConcatHead
                                          ⟨rfl,
                                            hLeftConcatRightNotConcatHead.1,
                                            hLeftConcatRightNotConcatHead.2.1,
                                            hLeftConcatRightNotConcatHead.2.2⟩)
                                    · by_cases hRightConcatLeftNotConcatHead :
                                          (¬ ∃ sHead sTail : Term,
                                            s = mkConcat sHead sTail) ∧
                                            (∃ tHead tTail : Term,
                                              t = mkConcat tHead tTail) ∧
                                            __eo_eq s t = Term.Boolean true
                                      · exact False.elim
                                          (hNotTrueRightConcatLeftNotConcatHead
                                            ⟨rfl,
                                              hRightConcatLeftNotConcatHead.1,
                                              hRightConcatLeftNotConcatHead.2.1,
                                              hRightConcatLeftNotConcatHead.2.2⟩)
                                      -- Remaining corner: cancellation can expose
                                      -- generated seq.empty terms whose SMT
                                      -- translation needs inhabited/wf element
                                      -- type evidence.
                                      · sorry
          · subst rev
            by_cases hBothConcat :
                (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                  (∃ tHead tTail : Term, t = mkConcat tHead tTail)
            · exact False.elim
                (hNotFalseBothConcat ⟨rfl, hBothConcat.1, hBothConcat.2⟩)
            · by_cases hLeftConcatWithRightIntro :
                  (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                    __smtx_typeof (__eo_to_smt (__str_nary_intro t)) ≠
                      SmtType.None
              · exact False.elim
                  (hNotFalseLeftConcatWithRightIntro
                    ⟨rfl, hLeftConcatWithRightIntro.1,
                      hLeftConcatWithRightIntro.2⟩)
              · by_cases hRightConcatWithLeftIntro :
                    (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                      __smtx_typeof (__eo_to_smt (__str_nary_intro s)) ≠
                        SmtType.None
                · exact False.elim
                    (hNotFalseRightConcatWithLeftIntro
                      ⟨rfl, hRightConcatWithLeftIntro.1,
                        hRightConcatWithLeftIntro.2⟩)
                · by_cases hLeftConcatWithRightIntroEqSelf :
                      (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                        __str_nary_intro t = t
                  · exact False.elim
                      (hNotFalseLeftConcatWithRightIntroEqSelf
                        ⟨rfl, hLeftConcatWithRightIntroEqSelf.1,
                          hLeftConcatWithRightIntroEqSelf.2⟩)
                  · by_cases hRightConcatWithLeftIntroEqSelf :
                        (∃ tHead tTail : Term, t = mkConcat tHead tTail) ∧
                          __str_nary_intro s = s
                    · exact False.elim
                        (hNotFalseRightConcatWithLeftIntroEqSelf
                          ⟨rfl, hRightConcatWithLeftIntroEqSelf.1,
                            hRightConcatWithLeftIntroEqSelf.2⟩)
                    · by_cases hLeftConcatWithRightEmpty :
                          (∃ sHead sTail : Term, s = mkConcat sHead sTail) ∧
                            __smtx_typeof
                                (__eo_to_smt
                                  (__seq_empty (__eo_typeof t))) ≠
                              SmtType.None
                      · exact False.elim
                          (hNotFalseLeftConcatWithRightEmpty
                            ⟨rfl, hLeftConcatWithRightEmpty.1,
                              hLeftConcatWithRightEmpty.2⟩)
                      · by_cases hRightConcatWithLeftEmpty :
                            (∃ tHead tTail : Term,
                              t = mkConcat tHead tTail) ∧
                              __smtx_typeof
                                  (__eo_to_smt
                                    (__seq_empty (__eo_typeof s))) ≠
                                SmtType.None
                        · exact False.elim
                            (hNotFalseRightConcatWithLeftEmpty
                              ⟨rfl, hRightConcatWithLeftEmpty.1,
                                hRightConcatWithLeftEmpty.2⟩)
                        · by_cases hBothNotConcatIntroEqSelf :
                              (¬ ∃ sHead sTail : Term,
                                s = mkConcat sHead sTail) ∧
                                (¬ ∃ tHead tTail : Term,
                                  t = mkConcat tHead tTail) ∧
                                __str_nary_intro s = s ∧
                                __str_nary_intro t = t
                          · exact False.elim
                              (hNotFalseBothNotConcatIntroEqSelf
                                ⟨rfl, hBothNotConcatIntroEqSelf.1,
                                  hBothNotConcatIntroEqSelf.2.1,
                                  hBothNotConcatIntroEqSelf.2.2⟩)
                          · by_cases
                              hBothNotConcatLeftIntroEqSelfRightEmpty :
                                (¬ ∃ sHead sTail : Term,
                                  s = mkConcat sHead sTail) ∧
                                  (¬ ∃ tHead tTail : Term,
                                    t = mkConcat tHead tTail) ∧
                                  __str_nary_intro s = s ∧
                                  __smtx_typeof
                                      (__eo_to_smt
                                        (__seq_empty (__eo_typeof t))) ≠
                                    SmtType.None
                            · exact False.elim
                                (hNotFalseBothNotConcatLeftIntroEqSelfRightEmpty
                                  ⟨rfl,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.1,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.2.1,
                                    hBothNotConcatLeftIntroEqSelfRightEmpty.2.2⟩)
                            · by_cases
                                hBothNotConcatRightIntroEqSelfLeftEmpty :
                                  (¬ ∃ sHead sTail : Term,
                                    s = mkConcat sHead sTail) ∧
                                    (¬ ∃ tHead tTail : Term,
                                      t = mkConcat tHead tTail) ∧
                                    __smtx_typeof
                                        (__eo_to_smt
                                          (__seq_empty (__eo_typeof s))) ≠
                                      SmtType.None ∧
                                    __str_nary_intro t = t
                              · exact False.elim
                                  (hNotFalseBothNotConcatRightIntroEqSelfLeftEmpty
                                    ⟨rfl,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.1,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.2.1,
                                      hBothNotConcatRightIntroEqSelfLeftEmpty.2.2⟩)
                              · by_cases hBothNotConcatEmptyTypeof :
                                    (¬ ∃ sHead sTail : Term,
                                      s = mkConcat sHead sTail) ∧
                                      (¬ ∃ tHead tTail : Term,
                                        t = mkConcat tHead tTail) ∧
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__seq_empty (__eo_typeof s))) ≠
                                        SmtType.None ∧
                                      __smtx_typeof
                                          (__eo_to_smt
                                            (__seq_empty (__eo_typeof t))) ≠
                                        SmtType.None
                                · exact False.elim
                                    (hNotFalseBothNotConcatEmptyTypeof
                                      ⟨rfl, hBothNotConcatEmptyTypeof.1,
                                        hBothNotConcatEmptyTypeof.2.1,
                                        hBothNotConcatEmptyTypeof.2.2⟩)
                                · by_cases hBothNotConcatHeadFalse :
                                      (¬ ∃ sHead sTail : Term,
                                        s = mkConcat sHead sTail) ∧
                                        (¬ ∃ tHead tTail : Term,
                                          t = mkConcat tHead tTail) ∧
                                        __eo_eq s t = Term.Boolean false
                                  · exact False.elim
                                      (hNonConcatHead hBothNotConcatHeadFalse)
                                  -- Same remaining seq.empty translation corner
                                  -- for the non-reversed strip.
                                  · sorry

theorem cmd_step_concat_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.concat_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.concat_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.concat_eq args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.concat_eq args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons n1 premises =>
              cases premises with
              | nil =>
                  let X1 := __eo_state_proven_nth s n1
                  have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                    have hArgs : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                      simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                    exact hArgs.1
                  have hX1Bool : RuleProofs.eo_has_bool_type X1 :=
                    hPremisesBool X1 (by simp [X1, premiseTermList])
                  have hProgConcatEq :
                      __eo_prog_concat_eq a1 (Proof.pf X1) ≠ Term.Stuck := by
                    change __eo_prog_concat_eq a1
                      (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                    simpa [X1] using hProg
                  rcases eo_prog_concat_eq_premise_eq_shape_of_ne_stuck a1 X1
                      hProgConcatEq with ⟨lhs, rhs, hX1Eq⟩
                  have hStateEq :
                      __eo_state_proven_nth s n1 = mkEq lhs rhs := by
                    simpa [X1] using hX1Eq
                  have hPremEqBool : RuleProofs.eo_has_bool_type (mkEq lhs rhs) := by
                    simpa [X1, hStateEq] using hX1Bool
                  have hProgRule :
                      __eo_prog_concat_eq a1 (Proof.pf (mkEq lhs rhs)) ≠
                        Term.Stuck := by
                    simpa [X1, hStateEq] using hProgConcatEq
                  have hResultTyRule :
                      __eo_typeof
                        (__eo_prog_concat_eq a1 (Proof.pf (mkEq lhs rhs))) =
                        Term.Bool := by
                    change __eo_typeof
                      (__eo_prog_concat_eq a1
                        (Proof.pf (__eo_state_proven_nth s n1))) = Term.Bool at hResultTy
                    simpa [hStateEq] using hResultTy
                  change StepRuleProperties M [__eo_state_proven_nth s n1]
                    (__eo_prog_concat_eq a1
                      (Proof.pf (__eo_state_proven_nth s n1)))
                  rw [hStateEq]
                  exact step_concat_eq_core M hM a1 lhs rhs hA1Trans
                    hPremEqBool hProgRule hResultTyRule
              | cons _ _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
