import Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-- `seq.nth` at a natural index agrees with list `getD`. -/
private theorem sr_ssm_seq_nth_ofNat (d : SmtValue) :
    ∀ (s : SmtSeq) (j : Nat),
      __smtx_ssm_seq_nth s (Int.ofNat j) d =
        (native_unpack_seq s).getD j d
  | SmtSeq.empty T, j => by
      simp [__smtx_ssm_seq_nth, native_unpack_seq]
  | SmtSeq.cons v vs, 0 => by
      simp [__smtx_ssm_seq_nth, native_unpack_seq]
  | SmtSeq.cons v vs, (j + 1) => by
      have hidx :
          native_zplus (Int.ofNat (j + 1)) (native_zneg 1) =
            Int.ofNat j := by
        show Int.ofNat j + 1 + (-1) = Int.ofNat j
        omega
      have ih := sr_ssm_seq_nth_ofNat d vs j
      simp only [__smtx_ssm_seq_nth, hidx, ih, native_unpack_seq,
        List.getD_cons_succ]

/-- In bounds, the default supplied to `getD` is irrelevant. -/
private theorem sr_getD_lt_eq (d d' : SmtValue) (l : List SmtValue) (j : Nat)
    (h : j < l.length) : l.getD j d = l.getD j d' := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h, Option.getD_some, Option.getD_some]

/-- Split a list immediately around an in-bounds element. -/
private theorem sr_take_getD_drop_succ
    (d : SmtValue) (l : List SmtValue) (j : Nat) (h : j < l.length) :
    l.take j ++ [l.getD j d] ++ l.drop (j + 1) = l := by
  induction l generalizing j with
  | nil => simp at h
  | cons a l ih =>
      cases j with
      | zero => simp
      | succ j =>
          simp only [List.length_cons, Nat.succ_lt_succ_iff] at h
          simpa [List.take_succ_cons, List.getD_cons_succ,
            List.drop_succ_cons, Nat.succ_eq_add_one, Nat.add_assoc] using
            congrArg (fun xs => a :: xs) (ih j h)

/-- Unpacking a string immediately after packing it recovers its characters. -/
private theorem sr_native_unpack_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  simp only [native_unpack_string, native_pack_string,
    Smtm.native_unpack_pack_seq, List.map_map]
  induction s with
  | nil => rfl
  | cons c cs ih => simp [native_ssm_char_of_value, ih]

/-- A well-typed character sequence is exactly the packing of its string view. -/
private theorem sr_native_pack_unpack_string
    (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_string (native_unpack_string ss) = ss := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (native_ssm_char_of_value v)) =
        native_unpack_seq ss := by
    induction native_unpack_seq ss with
    | nil => rfl
    | cons v vs ih =>
        rcases hTyped with ⟨hv, hvs⟩
        rcases char_value_canonical hv with ⟨c, rfl, _hc⟩
        simpa [native_ssm_char_of_value] using ih hvs
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  unfold native_pack_string native_unpack_string
  simp only [List.map_map]
  change native_pack_seq SmtType.Char
      ((native_unpack_seq ss).map
        (fun v => SmtValue.Char (native_ssm_char_of_value v))) = ss
  rw [hMap]
  simpa [hElem] using native_pack_unpack_seq ss

/-- String extraction commutes with the sequence encoding used by SMT values. -/
private theorem sr_native_seq_extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_pack_seq SmtType.Char
        (native_seq_extract (native_unpack_seq (native_pack_string s)) i n) =
      native_pack_string (native_str_substr s i n) := by
  simp only [native_pack_string, native_seq_extract, native_str_substr,
    native_str_len, Smtm.native_unpack_pack_seq]
  by_cases h : (i < 0 ∨ n ≤ 0) ∨ Int.ofNat s.length ≤ i
  · simp [h]
  · simp [h, List.map_take, List.map_drop]

/-- An in-bounds, length-one substring is the indexed singleton. -/
private theorem sr_native_str_substr_one_nat (s : native_String) (j : Nat)
    (hj : j < s.length) :
    native_str_substr s (Int.ofNat j) 1 = [s[j]] := by
  have e1 : decide ((Int.ofNat j : native_Int) < 0) = false :=
    decide_eq_false (show ¬ ((j : Int) < 0) by omega)
  have e2 : decide ((1 : native_Int) ≤ 0) = false := by decide
  have h1 : (1 : Int) ≤ (s.length : Int) - (j : Int) := by omega
  have hmin : min (1 : native_Int) (Int.ofNat s.length - Int.ofNat j) = 1 :=
    Int.min_eq_left h1
  have htn : (Int.ofNat j : native_Int).toNat = j := rfl
  have htake :
      (min (1 : native_Int) (Int.ofNat s.length - Int.ofNat j)).toNat = 1 := by
    rw [hmin]
    exact Int.toNat_one
  simp only [native_str_substr, native_str_len]
  rw [e1, e2]
  simp only [Bool.false_or, decide_eq_true_eq]
  rw [if_neg (show ¬ Int.ofNat j ≥ Int.ofNat s.length by omega)]
  rw [htake, htn]
  have hDrop := congrArg (List.take 1) (List.drop_eq_getElem_cons hj)
  exact hDrop

/-- The code constraint generated for lowercasing matches the native operation. -/
private theorem sr_lower_code_at (s : native_String) (j : Nat)
    (hValid : native_string_valid s = true) (hj : j < s.length) :
    native_str_to_code
        (native_str_substr (native_str_to_lower s) (Int.ofNat j) 1) =
      if 65 ≤ native_str_to_code (native_str_substr s (Int.ofNat j) 1) &&
          native_str_to_code (native_str_substr s (Int.ofNat j) 1) ≤ 90 then
        native_str_to_code (native_str_substr s (Int.ofNat j) 1) + 32
      else native_str_to_code (native_str_substr s (Int.ofNat j) 1) := by
  have hc : native_char_valid s[j] = true := by
    rw [native_string_valid, List.all_eq_true] at hValid
    exact hValid s[j] (List.getElem_mem hj)
  have hjMap : j < (native_str_to_lower s).length := by
    simpa [native_str_to_lower] using hj
  rw [sr_native_str_substr_one_nat s j hj]
  rw [sr_native_str_substr_one_nat (native_str_to_lower s) j hjMap]
  simp only [native_str_to_lower, List.getElem_map]
  have hcLower := native_char_valid_to_lower hc
  have hCode : native_str_to_code [s[j]] = Int.ofNat s[j] := by
    simp [native_str_to_code, hc]
  have hLowerCode :
      native_str_to_code [native_char_to_lower s[j]] =
        Int.ofNat (native_char_to_lower s[j]) := by
    simp [native_str_to_code, hcLower]
  rw [hCode, hLowerCode]
  by_cases hRange : 65 ≤ s[j] ∧ s[j] ≤ 90
  · have hRangeInt : (65 : Int) ≤ Int.ofNat s[j] ∧ Int.ofNat s[j] ≤ 90 := by
      exact ⟨Int.ofNat_le.mpr hRange.1, Int.ofNat_le.mpr hRange.2⟩
    have hRangeBool :
        (decide ((65 : Int) ≤ Int.ofNat s[j]) &&
          decide (Int.ofNat s[j] ≤ 90)) = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hRangeInt
    rw [if_pos hRangeBool]
    simp [native_char_to_lower, hRange]
  · have hRangeInt : ¬ ((65 : Int) ≤ Int.ofNat s[j] ∧ Int.ofNat s[j] ≤ 90) := by
      intro h
      exact hRange ⟨Int.ofNat_le.mp h.1, Int.ofNat_le.mp h.2⟩
    have hRangeBool :
        (decide ((65 : Int) ≤ Int.ofNat s[j]) &&
          decide (Int.ofNat s[j] ≤ 90)) ≠ true := by
      simpa [Bool.and_eq_true] using hRangeInt
    rw [if_neg hRangeBool]
    simp [native_char_to_lower, hRange]

/-- The code constraint generated for uppercasing matches the native operation. -/
private theorem sr_upper_code_at (s : native_String) (j : Nat)
    (hValid : native_string_valid s = true) (hj : j < s.length) :
    native_str_to_code
        (native_str_substr (native_str_to_upper s) (Int.ofNat j) 1) =
      if 97 ≤ native_str_to_code (native_str_substr s (Int.ofNat j) 1) &&
          native_str_to_code (native_str_substr s (Int.ofNat j) 1) ≤ 122 then
        native_str_to_code (native_str_substr s (Int.ofNat j) 1) + (-32)
      else native_str_to_code (native_str_substr s (Int.ofNat j) 1) := by
  have hc : native_char_valid s[j] = true := by
    rw [native_string_valid, List.all_eq_true] at hValid
    exact hValid s[j] (List.getElem_mem hj)
  have hjMap : j < (native_str_to_upper s).length := by
    simpa [native_str_to_upper] using hj
  rw [sr_native_str_substr_one_nat s j hj]
  rw [sr_native_str_substr_one_nat (native_str_to_upper s) j hjMap]
  simp only [native_str_to_upper, List.getElem_map]
  have hcUpper := native_char_valid_to_upper hc
  have hCode : native_str_to_code [s[j]] = Int.ofNat s[j] := by
    simp [native_str_to_code, hc]
  have hUpperCode :
      native_str_to_code [native_char_to_upper s[j]] =
        Int.ofNat (native_char_to_upper s[j]) := by
    simp [native_str_to_code, hcUpper]
  rw [hCode, hUpperCode]
  by_cases hRange : 97 ≤ s[j] ∧ s[j] ≤ 122
  · have hRangeInt : (97 : Int) ≤ Int.ofNat s[j] ∧ Int.ofNat s[j] ≤ 122 := by
      exact ⟨Int.ofNat_le.mpr hRange.1, Int.ofNat_le.mpr hRange.2⟩
    have hRangeBool :
        (decide ((97 : Int) ≤ Int.ofNat s[j]) &&
          decide (Int.ofNat s[j] ≤ 122)) = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hRangeInt
    rw [if_pos hRangeBool]
    simp [native_char_to_upper, hRange]
    omega
  · have hRangeInt : ¬ ((97 : Int) ≤ Int.ofNat s[j] ∧ Int.ofNat s[j] ≤ 122) := by
      intro h
      exact hRange ⟨Int.ofNat_le.mp h.1, Int.ofNat_le.mp h.2⟩
    have hRangeBool :
        (decide ((97 : Int) ≤ Int.ofNat s[j]) &&
          decide (Int.ofNat s[j] ≤ 122)) ≠ true := by
      simpa [Bool.and_eq_true] using hRangeInt
    rw [if_neg hRangeBool]
    simp [native_char_to_upper, hRange]

private def sr_native_str_leq_bool (s t : native_String) : Bool :=
  native_or (decide (s = t)) (native_str_lt s t)

private theorem sr_native_str_substr_at_length (s : native_String) :
    native_str_substr s (Int.ofNat s.length) 1 = [] := by
  simp [native_str_substr, native_str_len]

private theorem sr_native_str_substr_zero_nat
    (s : native_String) (j : Nat) (hj : j ≤ s.length) :
    native_str_substr s 0 (Int.ofNat j) = s.take j := by
  simp [native_str_substr, native_str_len, hj]

private theorem sr_native_str_substr_cons_succ
    (a : native_Char) (s : native_String) (j : Nat) (hj : j ≤ s.length) :
    native_str_substr (a :: s) (Int.ofNat (j + 1)) 1 =
      native_str_substr s (Int.ofNat j) 1 := by
  by_cases hlt : j < s.length
  · rw [sr_native_str_substr_one_nat s j hlt]
    rw [sr_native_str_substr_one_nat (a :: s) (j + 1) (by simpa using hlt)]
    simp
  · have heq : j = s.length := by omega
    subst j
    rw [sr_native_str_substr_at_length s]
    rw [sr_native_str_substr_at_length (a :: s)]

/-- Unequal strings have a first lexicographically decisive position. -/
private theorem sr_native_str_leq_witness :
    ∀ (s t : native_String),
      native_string_valid s = true →
      native_string_valid t = true →
      s ≠ t →
      ∃ j : Nat,
        j ≤ s.length ∧ j ≤ t.length ∧
        s.take j = t.take j ∧
        (if sr_native_str_leq_bool s t = true then
          native_str_to_code (native_str_substr s (Int.ofNat j) 1) <
            native_str_to_code (native_str_substr t (Int.ofNat j) 1)
        else
          native_str_to_code (native_str_substr t (Int.ofNat j) 1) <
            native_str_to_code (native_str_substr s (Int.ofNat j) 1))
  | [], [], _hs, _ht, hne => False.elim (hne rfl)
  | [], b :: bs, _hs, ht, _hne => by
      have hb : native_char_valid b = true := by
        simpa [native_string_valid] using ht
      refine ⟨0, by simp, by simp, by simp, ?_⟩
      simp [sr_native_str_leq_bool, native_str_lt, native_or,
        native_str_substr, native_str_len, native_str_to_code, hb]
  | a :: as, [], hs, _ht, _hne => by
      have ha : native_char_valid a = true := by
        simpa [native_string_valid] using hs
      refine ⟨0, by simp, by simp, by simp, ?_⟩
      simp [sr_native_str_leq_bool, native_str_lt, native_or,
        native_str_substr, native_str_len, native_str_to_code, ha]
  | a :: as, b :: bs, hs, ht, hne => by
      have ha : native_char_valid a = true := by
        simpa [native_string_valid] using hs
      have hb : native_char_valid b = true := by
        simpa [native_string_valid] using ht
      have has : native_string_valid as = true := by
        simpa [native_string_valid] using hs
      have hbs : native_string_valid bs = true := by
        simpa [native_string_valid] using ht
      by_cases hab : a = b
      · subst b
        have hTailNe : as ≠ bs := by
          intro h
          exact hne (by rw [h])
        rcases sr_native_str_leq_witness as bs has hbs hTailNe with
          ⟨j, hjas, hjbs, hpre, hcmp⟩
        refine ⟨j + 1, by simpa using hjas, by simpa using hjbs, ?_, ?_⟩
        · simpa [List.take_succ_cons] using
            congrArg (fun xs => a :: xs) hpre
        · rw [sr_native_str_substr_cons_succ a as j hjas,
            sr_native_str_substr_cons_succ a bs j hjbs]
          simpa [sr_native_str_leq_bool, native_str_lt, native_or,
            List.cons_lt_cons_iff] using hcmp
      · refine ⟨0, by simp, by simp, by simp, ?_⟩
        rw [sr_native_str_substr_one_nat (a :: as) 0 (by simp),
          sr_native_str_substr_one_nat (b :: bs) 0 (by simp)]
        by_cases hlt : a < b
        · simp [sr_native_str_leq_bool, native_str_lt, native_or,
            List.cons_lt_cons_iff, hab, hlt, native_str_to_code, ha, hb]
        · have hba : b < a := by omega
          simp [sr_native_str_leq_bool, native_str_lt, native_or,
            List.cons_lt_cons_iff, hab, hlt, hba,
            native_str_to_code, ha, hb]

private abbrev srMkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private abbrev srMkAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y

private abbrev srPurify (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_purify) x

private abbrev stringReductionBody (s : Term) : Term :=
  __eo_mk_apply
    (__eo_mk_apply (Term.UOp UserOp.and) (__str_reduction_pred s))
    (srMkAnd (srMkEq s (srPurify s)) (Term.Boolean true))

/-- The purification marker is semantically the identity. -/
private theorem eo_interprets_purify_eq_self
    (M : SmtModel) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s) :
    eo_interprets M (srMkEq s (srPurify s)) true := by
  apply RuleProofs.eo_interprets_eq_of_rel M
  · apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    · rfl
    · exact hTrans
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt s))
      (__smtx_model_eval M (SmtTerm._at_purify (__eo_to_smt s)))
    simpa [__smtx_model_eval, __smtx_model_eval__at_purify] using
      RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt s))

/-- Once its generated predicate holds, the common string-reduction shell holds. -/
private theorem string_reduction_body_true
    (M : SmtModel) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s)
    (hPred : eo_interprets M (__str_reduction_pred s) true) :
    eo_interprets M (stringReductionBody s) true := by
  have hPredNe : __str_reduction_pred s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation _
      (RuleProofs.eo_has_smt_translation_of_has_bool_type _
        (RuleProofs.eo_has_bool_type_of_interprets_true M _ hPred))
  simp only [stringReductionBody, __eo_mk_apply, hPredNe]
  apply RuleProofs.eo_interprets_and_intro M
  · exact hPred
  · apply RuleProofs.eo_interprets_and_intro M
    · exact eo_interprets_purify_eq_self M s hTrans
    · exact RuleProofs.eo_interprets_true M

/-- Semantic obligations specific to the individual string-reduction cases. -/
private theorem string_reduction_pred_true
    (M : SmtModel) (hM : model_total_typed M) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s)
    (hClosed : __eo_is_closed s = Term.Boolean true)
    (hBodyTy : __eo_typeof (stringReductionBody s) = Term.Bool) :
    eo_interprets M (__str_reduction_pred s) true := by
  cases s <;>
    simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
  all_goals try
    (change Term.Stuck = Term.Bool at hBodyTy
     exact False.elim (Term.noConfusion hBodyTy))
  case Apply f x =>
    cases f <;> try
      simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
    all_goals try
      (change Term.Stuck = Term.Bool at hBodyTy
       exact False.elim (Term.noConfusion hBodyTy))
    case UOp op =>
      cases op <;> try
        simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
      all_goals try
        (change Term.Stuck = Term.Bool at hBodyTy
         exact False.elim (Term.noConfusion hBodyTy))
      case str_from_int => sorry
      case str_to_int => sorry
      case str_to_lower =>
        have hOrigNN :
            term_has_non_none_type
              (SmtTerm.str_to_lower (__eo_to_smt x)) := by
          simpa [RuleProofs.eo_has_smt_translation] using hTrans
        have hxTy :
            __smtx_typeof (__eo_to_smt x) =
              SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
            (typeof_str_to_lower_eq (__eo_to_smt x)) hOrigNN
        have hXNN : term_has_non_none_type (__eo_to_smt x) := by
          unfold term_has_non_none_type
          rw [hxTy]
          exact seq_ne_none SmtType.Char
        have hTWf :
            __smtx_type_wf (SmtType.Seq SmtType.Char) = true :=
          Smtm.smt_term_seq_type_wf_of_non_none
            (__eo_to_smt x) hXNN hxTy
        have hLowerTy :
            __smtx_typeof (SmtTerm.str_to_lower (__eo_to_smt x)) =
              SmtType.Seq SmtType.Char := by
          rw [typeof_str_to_lower_eq, hxTy]
          simp [native_ite, native_Teq]
        have hXValTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
              SmtType.Seq SmtType.Char := by
          simpa [hxTy] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt x) hXNN
        rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
        have hSxTy :
            __smtx_typeof_seq_value sx =
              SmtType.Seq SmtType.Char := by
          simpa [hXEval, __smtx_typeof_value] using hXValTy
        let w := native_unpack_string sx
        have hValid : native_string_valid w = true := by
          exact native_unpack_string_valid_of_typeof_seq_char hSxTy
        have hPack : native_pack_string w = sx :=
          sr_native_pack_unpack_string sx hSxTy
        have hXEvalString :
            __smtx_model_eval M (__eo_to_smt x) =
              SmtValue.Seq (native_pack_string w) := by
          rw [hPack]
          exact hXEval
        have hXClosed : __eo_is_closed x = Term.Boolean true := by
          simpa [__eo_is_closed, __eo_is_closed_rec, __eo_and,
            native_and] using hClosed
        let idxName := native_string_lit "@var.str_index"
        let idx := SmtTerm.Var idxName SmtType.Int
        let lowerS :=
          SmtTerm._at_purify (SmtTerm.str_to_lower (__eo_to_smt x))
        let lowerLen := SmtTerm.str_len lowerS
        let origCode := SmtTerm.str_to_code
          (SmtTerm.str_substr (__eo_to_smt x) idx (SmtTerm.Numeral 1))
        let lowerCode := SmtTerm.str_to_code
          (SmtTerm.str_substr lowerS idx (SmtTerm.Numeral 1))
        let isUpper := SmtTerm.and
          (SmtTerm.leq (SmtTerm.Numeral 65) origCode)
          (SmtTerm.and (SmtTerm.leq origCode (SmtTerm.Numeral 90))
            (SmtTerm.Boolean true))
        let expected := SmtTerm.ite isUpper
          (SmtTerm.plus origCode
            (SmtTerm.plus (SmtTerm.Numeral 32) (SmtTerm.Numeral 0)))
          origCode
        let qBody := SmtTerm.or
          (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
          (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx lowerLen))
            (SmtTerm.or (SmtTerm.eq lowerCode expected)
              (SmtTerm.Boolean false)))
        apply RuleProofs.eo_interprets_and_intro M
        · apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len lowerS)) = SmtType.Bool
            simp [lowerS, typeof_eq_eq, typeof_str_len_eq, hxTy,
              hLowerTy, __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq,
              __smtx_typeof, native_ite, native_Teq]
          · change __smtx_model_eval M
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len lowerS)) = SmtValue.Boolean true
            simp [lowerS, __smtx_model_eval, hXEvalString,
              __smtx_model_eval_str_len, __smtx_model_eval_str_to_lower,
              __smtx_model_eval__at_purify, __smtx_model_eval_eq,
              native_seq_len, native_str_to_lower,
              Smtm.native_unpack_pack_seq, sr_native_unpack_pack_string,
              native_veq]
        · apply RuleProofs.eo_interprets_and_intro M
          · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof
                  (SmtTerm.forall idxName SmtType.Int qBody) =
                    SmtType.Bool
              simp [qBody, expected, isUpper, lowerCode, origCode,
                lowerLen, lowerS, idx, smtx_typeof_forall_term_eq,
                typeof_or_eq, typeof_not_eq, typeof_geq_eq, typeof_lt_eq,
                typeof_eq_eq, typeof_str_len_eq, typeof_str_substr_eq,
                typeof_str_to_code_eq, typeof_leq_eq, typeof_and_eq,
                typeof_ite_eq, typeof_plus_eq, hxTy, hLowerTy,
                __smtx_typeof, __smtx_typeof_seq_op_1,
                __smtx_typeof_seq_op_1_ret, __smtx_typeof_str_substr,
                __smtx_typeof_arith_overload_op_2,
                __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_eq, __smtx_typeof_guard_wf,
                __smtx_typeof_guard, __smtx_typeof_ite, hTWf,
                native_ite, native_Teq]
            · change native_eval_tforall M idxName SmtType.Int qBody =
                SmtValue.Boolean true
              have hAll :
                  ∀ v : SmtValue,
                    __smtx_typeof_value v = SmtType.Int →
                    __smtx_value_canonical_bool v = true →
                    __smtx_model_eval
                        (native_model_push M idxName SmtType.Int v) qBody =
                      SmtValue.Boolean true := by
                intro v hvTy _hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hXEvalPush :
                    __smtx_model_eval Mk (__eo_to_smt x) =
                      SmtValue.Seq (native_pack_string w) := by
                  rw [← hXEvalString]
                  exact (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                by_cases hk0 : 0 ≤ k
                · by_cases hklt : k < Int.ofNat w.length
                  · let j := Int.toNat k
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hj : j < w.length := by
                      have h := hklt
                      rw [← hCast] at h
                      exact Int.ofNat_lt.mp h
                    have hCode := sr_lower_code_at w j hValid hj
                    rw [hCast] at hCode
                    simp [qBody, expected, isUpper, lowerCode, origCode,
                      lowerLen, lowerS, idx, Mk, __smtx_model_eval,
                      hXEvalPush, native_model_var_lookup, native_model_push,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_lt, __smtx_model_eval_eq,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_to_lower,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code,
                      __smtx_model_eval__at_purify,
                      __smtx_model_eval_and, __smtx_model_eval_ite,
                      __smtx_model_eval_plus, native_seq_len,
                      native_str_to_lower, native_zleq, native_zlt,
                      native_zplus, native_and, native_or, native_not,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_seq_extract_pack_string, hCode, hk0, hklt]
                  · simp [qBody, lowerLen, lowerS, idx, Mk,
                      __smtx_model_eval, hXEvalPush,
                      native_model_var_lookup, native_model_push,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_lt,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_to_lower,
                      __smtx_model_eval__at_purify, native_seq_len,
                      native_str_to_lower, native_zleq, native_zlt,
                      native_and, native_or, native_not,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string, hk0, hklt]
                · simp [qBody, idx, Mk, __smtx_model_eval,
                    native_model_var_lookup, native_model_push,
                    __smtx_model_eval_or, __smtx_model_eval_not,
                    __smtx_model_eval_geq, native_zleq, native_and,
                    native_or, native_not, hk0]
              simpa [native_eval_tforall, hAll]
          · exact RuleProofs.eo_interprets_true M
      case str_to_upper =>
        have hOrigNN :
            term_has_non_none_type
              (SmtTerm.str_to_upper (__eo_to_smt x)) := by
          simpa [RuleProofs.eo_has_smt_translation] using hTrans
        have hxTy :
            __smtx_typeof (__eo_to_smt x) =
              SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
            (typeof_str_to_upper_eq (__eo_to_smt x)) hOrigNN
        have hXNN : term_has_non_none_type (__eo_to_smt x) := by
          unfold term_has_non_none_type
          rw [hxTy]
          exact seq_ne_none SmtType.Char
        have hTWf :
            __smtx_type_wf (SmtType.Seq SmtType.Char) = true :=
          Smtm.smt_term_seq_type_wf_of_non_none
            (__eo_to_smt x) hXNN hxTy
        have hUpperTy :
            __smtx_typeof (SmtTerm.str_to_upper (__eo_to_smt x)) =
              SmtType.Seq SmtType.Char := by
          rw [typeof_str_to_upper_eq, hxTy]
          simp [native_ite, native_Teq]
        have hXValTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
              SmtType.Seq SmtType.Char := by
          simpa [hxTy] using
            smt_model_eval_preserves_type_of_non_none M hM
              (__eo_to_smt x) hXNN
        rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
        have hSxTy :
            __smtx_typeof_seq_value sx =
              SmtType.Seq SmtType.Char := by
          simpa [hXEval, __smtx_typeof_value] using hXValTy
        let w := native_unpack_string sx
        have hValid : native_string_valid w = true := by
          exact native_unpack_string_valid_of_typeof_seq_char hSxTy
        have hPack : native_pack_string w = sx :=
          sr_native_pack_unpack_string sx hSxTy
        have hXEvalString :
            __smtx_model_eval M (__eo_to_smt x) =
              SmtValue.Seq (native_pack_string w) := by
          rw [hPack]
          exact hXEval
        have hXClosed : __eo_is_closed x = Term.Boolean true := by
          simpa [__eo_is_closed, __eo_is_closed_rec, __eo_and,
            native_and] using hClosed
        let idxName := native_string_lit "@var.str_index"
        let idx := SmtTerm.Var idxName SmtType.Int
        let upperS :=
          SmtTerm._at_purify (SmtTerm.str_to_upper (__eo_to_smt x))
        let upperLen := SmtTerm.str_len upperS
        let origCode := SmtTerm.str_to_code
          (SmtTerm.str_substr (__eo_to_smt x) idx (SmtTerm.Numeral 1))
        let upperCode := SmtTerm.str_to_code
          (SmtTerm.str_substr upperS idx (SmtTerm.Numeral 1))
        let isLower := SmtTerm.and
          (SmtTerm.leq (SmtTerm.Numeral 97) origCode)
          (SmtTerm.and (SmtTerm.leq origCode (SmtTerm.Numeral 122))
            (SmtTerm.Boolean true))
        let expected := SmtTerm.ite isLower
          (SmtTerm.plus origCode
            (SmtTerm.plus (SmtTerm.Numeral (-32)) (SmtTerm.Numeral 0)))
          origCode
        let qBody := SmtTerm.or
          (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
          (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx upperLen))
            (SmtTerm.or (SmtTerm.eq upperCode expected)
              (SmtTerm.Boolean false)))
        apply RuleProofs.eo_interprets_and_intro M
        · apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len upperS)) = SmtType.Bool
            simp [upperS, typeof_eq_eq, typeof_str_len_eq, hxTy,
              hUpperTy, __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq,
              __smtx_typeof, native_ite, native_Teq]
          · change __smtx_model_eval M
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len upperS)) = SmtValue.Boolean true
            simp [upperS, __smtx_model_eval, hXEvalString,
              __smtx_model_eval_str_len, __smtx_model_eval_str_to_upper,
              __smtx_model_eval__at_purify, __smtx_model_eval_eq,
              native_seq_len, native_str_to_upper,
              Smtm.native_unpack_pack_seq, sr_native_unpack_pack_string,
              native_veq]
        · apply RuleProofs.eo_interprets_and_intro M
          · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof
                  (SmtTerm.forall idxName SmtType.Int qBody) =
                    SmtType.Bool
              simp [qBody, expected, isLower, upperCode, origCode,
                upperLen, upperS, idx, smtx_typeof_forall_term_eq,
                typeof_or_eq, typeof_not_eq, typeof_geq_eq, typeof_lt_eq,
                typeof_eq_eq, typeof_str_len_eq, typeof_str_substr_eq,
                typeof_str_to_code_eq, typeof_leq_eq, typeof_and_eq,
                typeof_ite_eq, typeof_plus_eq, hxTy, hUpperTy,
                __smtx_typeof, __smtx_typeof_seq_op_1,
                __smtx_typeof_seq_op_1_ret, __smtx_typeof_str_substr,
                __smtx_typeof_arith_overload_op_2,
                __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_eq, __smtx_typeof_guard_wf,
                __smtx_typeof_guard, __smtx_typeof_ite, hTWf,
                native_ite, native_Teq]
            · change native_eval_tforall M idxName SmtType.Int qBody =
                SmtValue.Boolean true
              have hAll :
                  ∀ v : SmtValue,
                    __smtx_typeof_value v = SmtType.Int →
                    __smtx_value_canonical_bool v = true →
                    __smtx_model_eval
                        (native_model_push M idxName SmtType.Int v) qBody =
                      SmtValue.Boolean true := by
                intro v hvTy _hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hXEvalPush :
                    __smtx_model_eval Mk (__eo_to_smt x) =
                      SmtValue.Seq (native_pack_string w) := by
                  rw [← hXEvalString]
                  exact (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                by_cases hk0 : 0 ≤ k
                · by_cases hklt : k < Int.ofNat w.length
                  · let j := Int.toNat k
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hj : j < w.length := by
                      have h := hklt
                      rw [← hCast] at h
                      exact Int.ofNat_lt.mp h
                    have hCode := sr_upper_code_at w j hValid hj
                    rw [hCast] at hCode
                    simp [qBody, expected, isLower, upperCode, origCode,
                      upperLen, upperS, idx, Mk, __smtx_model_eval,
                      hXEvalPush, native_model_var_lookup, native_model_push,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_lt, __smtx_model_eval_eq,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_to_upper,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code,
                      __smtx_model_eval__at_purify,
                      __smtx_model_eval_and, __smtx_model_eval_ite,
                      __smtx_model_eval_plus, native_seq_len,
                      native_str_to_upper, native_zleq, native_zlt,
                      native_zplus, native_and, native_or, native_not,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_seq_extract_pack_string, hCode, hk0, hklt]
                  · simp [qBody, upperLen, upperS, idx, Mk,
                      __smtx_model_eval, hXEvalPush,
                      native_model_var_lookup, native_model_push,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_lt,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_to_upper,
                      __smtx_model_eval__at_purify, native_seq_len,
                      native_str_to_upper, native_zleq, native_zlt,
                      native_and, native_or, native_not,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string, hk0, hklt]
                · simp [qBody, idx, Mk, __smtx_model_eval,
                    native_model_var_lookup, native_model_push,
                    __smtx_model_eval_or, __smtx_model_eval_not,
                    __smtx_model_eval_geq, native_zleq, native_and,
                    native_or, native_not, hk0]
              simpa [native_eval_tforall, hAll]
          · exact RuleProofs.eo_interprets_true M
      case str_rev =>
        have hOrigNN :
            term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt x)) := by
          simpa [RuleProofs.eo_has_smt_translation] using hTrans
        rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
            (typeof_str_rev_eq (__eo_to_smt x)) hOrigNN with ⟨T, hxTy⟩
        have hXNN : term_has_non_none_type (__eo_to_smt x) := by
          unfold term_has_non_none_type
          rw [hxTy]
          exact seq_ne_none T
        have hTWf : __smtx_type_wf (SmtType.Seq T) = true :=
          Smtm.smt_term_seq_type_wf_of_non_none (__eo_to_smt x) hXNN hxTy
        have hRevTy :
            __smtx_typeof (SmtTerm.str_rev (__eo_to_smt x)) =
              SmtType.Seq T := by
          rw [typeof_str_rev_eq, hxTy]
          simp [__smtx_typeof_seq_op_1, __smtx_typeof_guard_wf, hTWf,
            native_ite]
        have hXValTy :
            __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
              SmtType.Seq T := by
          simpa [hxTy] using
            smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hXNN
        rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
        have hSxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
          simpa [hXEval, __smtx_typeof_value] using hXValTy
        have hElemTy : __smtx_elem_typeof_seq_value sx = T :=
          elem_typeof_seq_value_of_typeof_seq_value hSxTy
        have hXClosed : __eo_is_closed x = Term.Boolean true := by
          simpa [__eo_is_closed, __eo_is_closed_rec, __eo_and,
            native_and] using hClosed
        let idxName := native_string_lit "@var.str_index"
        let idx := SmtTerm.Var idxName SmtType.Int
        let revS := SmtTerm._at_purify (SmtTerm.str_rev (__eo_to_smt x))
        let revLen := SmtTerm.str_len revS
        let mirrorStart := SmtTerm.neg (SmtTerm.str_len (__eo_to_smt x))
          (SmtTerm.plus idx
            (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)))
        let sliceEq := SmtTerm.eq
          (SmtTerm.str_substr revS idx (SmtTerm.Numeral 1))
          (SmtTerm.str_substr (__eo_to_smt x) mirrorStart
            (SmtTerm.Numeral 1))
        let qBody := SmtTerm.or
          (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
          (SmtTerm.or (SmtTerm.not (SmtTerm.lt idx revLen))
            (SmtTerm.or sliceEq (SmtTerm.Boolean false)))
        apply RuleProofs.eo_interprets_and_intro M
        · apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len
                    (SmtTerm._at_purify
                      (SmtTerm.str_rev (__eo_to_smt x))))) = SmtType.Bool
            simp [typeof_eq_eq, typeof_str_len_eq, hxTy, hRevTy,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq, native_ite,
              native_Teq, __smtx_typeof, __smtx_typeof_seq_op_1,
              __smtx_typeof_guard_wf, __smtx_typeof_guard, hTWf]
          · change __smtx_model_eval M
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len
                    (SmtTerm._at_purify
                      (SmtTerm.str_rev (__eo_to_smt x))))) =
                SmtValue.Boolean true
            simp [__smtx_model_eval, hXEval, __smtx_model_eval_str_len,
              __smtx_model_eval_str_rev, __smtx_model_eval__at_purify,
              __smtx_model_eval_eq, native_seq_len, native_seq_rev,
              Smtm.native_unpack_pack_seq, native_veq]
        · apply RuleProofs.eo_interprets_and_intro M
          · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof
                  (SmtTerm.forall idxName SmtType.Int qBody) = SmtType.Bool
              simp [qBody, sliceEq, mirrorStart, revLen, revS, idx,
                smtx_typeof_forall_term_eq, typeof_or_eq, typeof_not_eq,
                typeof_geq_eq, typeof_lt_eq, typeof_eq_eq,
                typeof_str_len_eq, typeof_str_substr_eq, typeof_neg_eq,
                typeof_plus_eq, hxTy, hRevTy, __smtx_typeof,
                __smtx_typeof_seq_op_1, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_str_substr, __smtx_typeof_arith_overload_op_2,
                __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
                __smtx_typeof_guard_wf, __smtx_typeof_guard, hTWf,
                native_ite, native_Teq]
            · change native_eval_tforall M idxName SmtType.Int qBody =
                SmtValue.Boolean true
              have hAll :
                  ∀ v : SmtValue,
                    __smtx_typeof_value v = SmtType.Int →
                    __smtx_value_canonical_bool v = true →
                    __smtx_model_eval
                        (native_model_push M idxName SmtType.Int v) qBody =
                      SmtValue.Boolean true := by
                intro v hvTy _hvCanonical
                rcases int_value_canonical hvTy with ⟨k, rfl⟩
                let Mk := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral k)
                have hXEvalPush :
                    __smtx_model_eval Mk (__eo_to_smt x) =
                      SmtValue.Seq sx := by
                  rw [← hXEval]
                  exact (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                simp [qBody, sliceEq, mirrorStart, revLen, revS, idx, Mk,
                  __smtx_model_eval, hXEvalPush, native_model_var_lookup,
                  native_model_push, __smtx_model_eval_or,
                  __smtx_model_eval_not, __smtx_model_eval_geq,
                  __smtx_model_eval_leq, __smtx_model_eval_lt,
                  __smtx_model_eval_eq, __smtx_model_eval_str_len,
                  __smtx_model_eval_str_rev, __smtx_model_eval_str_substr,
                  __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                  __smtx_model_eval__, native_seq_len, native_seq_rev,
                  native_zleq, native_zlt, native_zplus, native_zneg,
                  native_and, native_or, native_not,
                  Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                  hElemTy, native_veq]
              simpa [native_eval_tforall, hAll]
          · exact RuleProofs.eo_interprets_true M
    case Apply g y =>
      cases g <;> try
        simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
      all_goals try
        (change Term.Stuck = Term.Bool at hBodyTy
         exact False.elim (Term.noConfusion hBodyTy))
      case UOp op =>
        cases op <;> try
          simp [__str_reduction_pred, stringReductionBody, __eo_mk_apply] at hBodyTy ⊢
        all_goals try
          (change Term.Stuck = Term.Bool at hBodyTy
           exact False.elim (Term.noConfusion hBodyTy))
        case str_contains =>
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          have hOrigNN :
              term_has_non_none_type (SmtTerm.str_contains ty tx) := by
            simpa [ty, tx, RuleProofs.eo_has_smt_translation] using hTrans
          rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
              (R := SmtType.Bool) (typeof_str_contains_eq ty tx) hOrigNN with
            ⟨U, hyTy, hxTy⟩
          let idx := SmtTerm.str_indexof ty tx (SmtTerm.Numeral 0)
          let pfx := SmtTerm._at_purify
            (SmtTerm.str_substr ty (SmtTerm.Numeral 0) idx)
          let cut := SmtTerm.plus (SmtTerm.str_len pfx)
            (SmtTerm.plus (SmtTerm.str_len tx) (SmtTerm.Numeral 0))
          let suffixS := SmtTerm._at_purify
            (SmtTerm.str_substr ty cut (SmtTerm.neg (SmtTerm.str_len ty) cut))
          let pre := srPurify
            (Term.Apply
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_substr) y)
                (Term.Numeral 0))
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_indexof) y) x)
                (Term.Numeral 0)))
          have hPreTy :
              __smtx_typeof (__eo_to_smt pre) = SmtType.Seq U := by
            change __smtx_typeof pfx = SmtType.Seq U
            simp [pfx, idx, ty, tx, typeof_str_substr_eq,
              typeof_str_indexof_eq, hyTy, hxTy, __smtx_typeof,
              __smtx_typeof_str_indexof, __smtx_typeof_str_substr,
              native_ite, native_Teq]
          let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)
          have hNilNe : nil ≠ Term.Stuck := by
            exact nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre U hPreTy
          let nilS := __eo_to_smt nil
          have hNilTy : __smtx_typeof nilS = SmtType.Seq U := by
            simpa [nilS, nil] using
              smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre U hPreTy
          let rhs := SmtTerm.str_concat pfx
            (SmtTerm.str_concat tx (SmtTerm.str_concat suffixS nilS))
          let cond := SmtTerm.str_contains ty tx
          let formula := SmtTerm.ite cond (SmtTerm.eq ty rhs)
            (SmtTerm.not (SmtTerm.eq ty tx))
          simp only [hNilNe, __eo_mk_apply]
          apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof formula = SmtType.Bool
            simp [formula, cond, rhs, nilS, suffixS, cut, pfx, idx,
              ty, tx, typeof_ite_eq, typeof_str_contains_eq, typeof_eq_eq,
              typeof_not_eq, typeof_str_concat_eq, typeof_str_substr_eq,
              typeof_str_indexof_eq, typeof_str_len_eq, typeof_plus_eq,
              typeof_neg_eq, hyTy, hxTy, hNilTy, __smtx_typeof,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_seq_op_2,
              __smtx_typeof_str_indexof, __smtx_typeof_str_substr,
              __smtx_typeof_arith_overload_op_2,
              __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
              __smtx_typeof_guard, __smtx_typeof_ite, native_ite,
              native_Teq]
          · change __smtx_model_eval M formula = SmtValue.Boolean true
            rcases seq_eval_of_seq_type M hM y U
                (by simpa [ty] using hyTy) with ⟨sy, hYEval⟩
            rcases seq_eval_of_seq_type M hM x U
                (by simpa [tx] using hxTy) with ⟨sx, hXEval⟩
            let ys := native_unpack_seq sy
            let xs := native_unpack_seq sx
            let idxVal := native_seq_indexof ys xs 0
            have hYEvalTy :
                __smtx_typeof_value (__smtx_model_eval M ty) =
                  __smtx_typeof ty :=
              Smtm.smt_model_eval_preserves_type_of_non_none M hM ty
                (by simp [term_has_non_none_type, hyTy])
            have hSyTy :
                __smtx_typeof_seq_value sy = SmtType.Seq U := by
              simpa [ty, hYEval, hyTy] using hYEvalTy
            have hElemY : __smtx_elem_typeof_seq_value sy = U :=
              elem_typeof_seq_value_of_typeof_seq_value hSyTy
            have hNilEval :
                __smtx_model_eval M nilS =
                  SmtValue.Seq (SmtSeq.empty U) := by
              simpa [nilS, nil] using
                eval_nil_str_concat_typeof_of_smt_type_seq M pre U hPreTy
            by_cases hContains : native_seq_contains ys xs = true
            · have hIdxNonneg : 0 ≤ idxVal := by
                simpa [idxVal, native_seq_contains] using hContains
              have hSplit :
                  native_seq_extract ys 0 idxVal ++ xs ++
                      native_seq_extract ys
                        (idxVal + Int.ofNat xs.length)
                        (Int.ofNat ys.length -
                          (idxVal + Int.ofNat xs.length)) = ys :=
                native_seq_indexof_zero_decomp ys xs hIdxNonneg
              have hPrefixLen :
                  Int.ofNat (native_seq_extract ys 0 idxVal).length =
                    idxVal := by
                simpa [idxVal] using
                  native_seq_extract_prefix_length_of_indexof_nonneg
                    ys xs hIdxNonneg
              have hStartEq :
                  Int.ofNat (native_seq_extract ys 0 idxVal).length +
                      Int.ofNat xs.length =
                    idxVal + Int.ofNat xs.length := by
                rw [hPrefixLen]
              have hLenEq :
                  Int.ofNat ys.length +
                      -(Int.ofNat (native_seq_extract ys 0 idxVal).length +
                        Int.ofNat xs.length) =
                    Int.ofNat ys.length -
                      (idxVal + Int.ofNat xs.length) := by
                rw [hPrefixLen]
                simp [Int.sub_eq_add_neg]
              have hPackSy : native_pack_seq U ys = sy := by
                dsimp [ys]
                rw [← hElemY]
                exact native_pack_unpack_seq sy
              simp [formula, cond, rhs, nilS, suffixS, cut, pfx, idx,
                ty, tx, ys, xs, __smtx_model_eval, hYEval, hXEval,
                hNilEval, __smtx_model_eval_ite,
                __smtx_model_eval_str_contains, __smtx_model_eval_eq,
                __smtx_model_eval_str_concat,
                __smtx_model_eval_str_substr,
                __smtx_model_eval_str_indexof,
                __smtx_model_eval_str_len, __smtx_model_eval_plus,
                __smtx_model_eval__, __smtx_model_eval__at_purify,
                native_seq_concat, Smtm.native_unpack_pack_seq,
                elem_typeof_pack_seq, native_seq_len, hElemY, hContains,
                native_zplus, native_zneg, native_veq]
              apply Eq.trans hPackSy.symm
              apply congrArg (native_pack_seq U)
              dsimp [ys, xs, idxVal] at hSplit hStartEq hLenEq ⊢
              rw [hStartEq]
              simpa [native_unpack_seq, List.append_assoc,
                Int.sub_eq_add_neg] using hSplit.symm
            · have hContainsFalse : native_seq_contains ys xs = false := by
                cases h : native_seq_contains ys xs
                · rfl
                · exact False.elim (hContains (by simp [h]))
              have hSyNeSx : sy ≠ sx := by
                intro hEq
                have hLists : ys = xs := by simp [ys, xs, hEq]
                have hSelf := native_seq_contains_self xs
                have hFalseSelf : native_seq_contains xs xs = false := by
                  simpa [ys, xs, hLists] using hContainsFalse
                rw [hSelf] at hFalseSelf
                cases hFalseSelf
              have hValNe : SmtValue.Seq sy ≠ SmtValue.Seq sx := by
                intro hEq
                cases hEq
                exact hSyNeSx rfl
              have hEqFalse :
                  native_veq (SmtValue.Seq sy) (SmtValue.Seq sx) = false := by
                simp [native_veq, hValNe]
              simp [formula, cond, rhs, nilS, suffixS, cut, pfx, idx,
                ty, tx, ys, xs, __smtx_model_eval, hYEval, hXEval,
                __smtx_model_eval_ite, __smtx_model_eval_str_contains,
                __smtx_model_eval_eq, __smtx_model_eval_not, native_not,
                native_veq, hContainsFalse]
              exact hSyNeSx
        case seq_nth =>
          have hOrigNN :
              term_has_non_none_type
                (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x)) := by
            simpa [RuleProofs.eo_has_smt_translation] using hTrans
          rcases seq_nth_args_of_non_none hOrigNN with ⟨T, hyTy, hxTy⟩
          let pre := srPurify
            (Term.Apply
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) y)
                (Term.Numeral 0)) x)
          have hPreTy :
              __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
            change __smtx_typeof
                (SmtTerm._at_purify
                  (SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0)
                    (__eo_to_smt x))) = SmtType.Seq T
            simp [__smtx_typeof, typeof_str_substr_eq, hyTy, hxTy,
              __smtx_typeof_str_substr, native_ite, native_Teq]
          have hNilNe :
              __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre) ≠
                Term.Stuck :=
            nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T hPreTy
          have hNilNe' :
              __eo_nil (Term.UOp UserOp.str_concat)
                  (__eo_typeof
                    (srPurify
                      (Term.Apply
                        (Term.Apply
                          (Term.Apply (Term.UOp UserOp.str_substr) y)
                          (Term.Numeral 0)) x))) ≠
                Term.Stuck := by
            simpa [pre] using hNilNe
          simp only [hNilNe', __eo_mk_apply] at hBodyTy ⊢
          have hTWf : __smtx_type_wf T = true :=
            (smt_seq_component_wf_of_non_none_type (__eo_to_smt y) T hyTy).2
          have hYNN : term_has_non_none_type (__eo_to_smt y) := by
            unfold term_has_non_none_type
            rw [hyTy]
            exact seq_ne_none T
          have hSeqTWf : __smtx_type_wf (SmtType.Seq T) = true :=
            Smtm.smt_term_seq_type_wf_of_non_none (__eo_to_smt y) hYNN hyTy
          have hNthTy :
              __smtx_typeof
                  (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x)) = T := by
            rw [typeof_seq_nth_eq, hyTy, hxTy]
            simp [__smtx_typeof_seq_nth, __smtx_typeof_guard_wf, hTWf,
              native_ite]
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          let len := SmtTerm.str_len ty
          let next := SmtTerm.plus tx
            (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0))
          let remaining := SmtTerm.neg len next
          let preS := SmtTerm._at_purify
            (SmtTerm.str_substr ty (SmtTerm.Numeral 0) tx)
          let nthS := SmtTerm._at_purify (SmtTerm.seq_nth ty tx)
          let suffixS := SmtTerm._at_purify
            (SmtTerm.str_substr ty next remaining)
          let nilS := __eo_to_smt
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))
          let decomposition := SmtTerm.str_concat preS
            (SmtTerm.str_concat (SmtTerm.seq_unit nthS)
              (SmtTerm.str_concat suffixS nilS))
          let cond := SmtTerm.and (SmtTerm.geq tx (SmtTerm.Numeral 0))
            (SmtTerm.and (SmtTerm.gt len tx) (SmtTerm.Boolean true))
          let rhs := SmtTerm.and (SmtTerm.eq ty decomposition)
            (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) tx)
              (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len suffixS) remaining)
                (SmtTerm.Boolean true)))
          have hNilTy : __smtx_typeof nilS = SmtType.Seq T := by
            simpa [nilS, pre] using
              smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPreTy
          have hLenTy : __smtx_typeof len = SmtType.Int := by
            simp [len, ty, typeof_str_len_eq, hyTy,
              __smtx_typeof_seq_op_1_ret]
          have hNextTy : __smtx_typeof next = SmtType.Int := by
            simp [next, tx, hxTy, typeof_plus_eq,
              __smtx_typeof_arith_overload_op_2, __smtx_typeof]
          have hRemainingTy : __smtx_typeof remaining = SmtType.Int := by
            simp [remaining, hLenTy, hNextTy, typeof_neg_eq,
              __smtx_typeof_arith_overload_op_2]
          have hPreSTy : __smtx_typeof preS = SmtType.Seq T := by
            simpa [preS, ty, tx, pre] using hPreTy
          have hNthSTy : __smtx_typeof nthS = T := by
            simpa [nthS, ty, tx, __smtx_typeof] using hNthTy
          have hSuffixTy : __smtx_typeof suffixS = SmtType.Seq T := by
            change __smtx_typeof (SmtTerm.str_substr ty next remaining) =
              SmtType.Seq T
            simp [typeof_str_substr_eq, ty, hNextTy, hRemainingTy, hyTy,
              __smtx_typeof_str_substr]
          have hUnitTy :
              __smtx_typeof (SmtTerm.seq_unit nthS) = SmtType.Seq T := by
            rw [smtx_typeof_seq_unit_term_eq, hNthSTy]
            simp [__smtx_typeof_guard_wf, hSeqTWf, native_ite]
          have hDecompositionTy :
              __smtx_typeof decomposition = SmtType.Seq T := by
            simp [decomposition, typeof_str_concat_eq, hPreSTy, hUnitTy,
              hSuffixTy, hNilTy, __smtx_typeof_seq_op_2, native_ite,
              native_Teq]
          have hCondTy : __smtx_typeof cond = SmtType.Bool := by
            simp [cond, typeof_and_eq, typeof_geq_eq, typeof_gt_eq, hLenTy,
              tx, hxTy, __smtx_typeof_arith_overload_op_2_ret,
              __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
          have hRhsTy : __smtx_typeof rhs = SmtType.Bool := by
            simp [rhs, typeof_and_eq, typeof_eq_eq, typeof_str_len_eq, ty,
              tx, hyTy, hxTy, hDecompositionTy, hPreSTy, hSuffixTy,
              hRemainingTy, __smtx_typeof_seq_op_1_ret,
              __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
              __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
          apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof (SmtTerm.imp cond rhs) = SmtType.Bool
            simp [typeof_imp_eq, hCondTy, hRhsTy, __smtx_typeof_guard,
              native_ite, native_Teq]
          · change __smtx_model_eval M (SmtTerm.imp cond rhs) =
              SmtValue.Boolean true
            have hYValTy :
                __smtx_typeof_value (__smtx_model_eval M ty) =
                  SmtType.Seq T := by
              simpa [ty, hyTy] using
                smt_model_eval_preserves_type_of_non_none M hM
                  (__eo_to_smt y) hYNN
            rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
            have hXNN : term_has_non_none_type tx := by
              unfold term_has_non_none_type
              rw [show __smtx_typeof tx = SmtType.Int by simpa [tx] using hxTy]
              decide
            have hXValTy :
                __smtx_typeof_value (__smtx_model_eval M tx) =
                  SmtType.Int := by
              simpa [tx, hxTy] using
                smt_model_eval_preserves_type_of_non_none M hM
                  (__eo_to_smt x) (by simpa [tx] using hXNN)
            rcases int_value_canonical hXValTy with ⟨i, hXEval⟩
            have hNilEval :
                __smtx_model_eval M nilS = SmtValue.Seq (SmtSeq.empty T) := by
              simpa [nilS, pre] using
                eval_nil_str_concat_typeof_of_smt_type_seq M pre T hPreTy
            have hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq T := by
              simpa [hYEval, __smtx_typeof_value] using hYValTy
            have hElemTy : __smtx_elem_typeof_seq_value sy = T :=
              elem_typeof_seq_value_of_typeof_seq_value hSyTy
            rw [smtx_eval_imp_term_eq]
            simp [cond, rhs, decomposition, suffixS, nthS, preS, remaining,
              next, len, __smtx_model_eval, __smtx_model_eval_imp,
              __smtx_model_eval_and, __smtx_model_eval_eq,
              __smtx_model_eval_geq, __smtx_model_eval_gt,
              __smtx_model_eval_str_len, __smtx_model_eval_str_substr,
              __smtx_model_eval_str_concat, __smtx_model_eval__at_purify,
              __smtx_model_eval_plus, __smtx_model_eval__,
              hYEval, hXEval, hNilEval, native_seq_len, native_seq_concat,
              native_and, native_or, native_not, native_zleq, native_zlt,
              native_zplus, native_zneg]
            by_cases hi : 0 ≤ i
            · by_cases hlt : i < Int.ofNat (native_unpack_seq sy).length
              · let xs := native_unpack_seq sy
                let j := Int.toNat i
                have hCast : Int.ofNat j = i := by
                  simpa [j] using Int.toNat_of_nonneg hi
                have hjlt : j < xs.length := by
                  have hlt' := hlt
                  rw [← hCast] at hlt'
                  exact Int.ofNat_lt.mp (by simpa [xs] using hlt')
                have hjSuccLe : j + 1 ≤ xs.length := by omega
                have hNextCast : i + 1 = Int.ofNat (j + 1) := by
                  rw [← hCast]
                  simp
                have hRemainingCast :
                    Int.ofNat xs.length + -(i + 1) =
                      Int.ofNat (xs.length - (j + 1)) := by
                  rw [hNextCast]
                  simpa using (Int.ofNat_sub hjSuccLe).symm
                have hRemainingNatCast :
                    Int.ofNat xs.length + -Int.ofNat (j + 1) =
                      Int.ofNat (xs.length - (j + 1)) := by
                  simpa using (Int.ofNat_sub hjSuccLe).symm
                have hPreExtract :
                    native_seq_extract xs 0 i = xs.take j := by
                  rw [← hCast]
                  exact native_seq_extract_zero_nat xs j (Nat.le_of_lt hjlt)
                have hSuffixExtract :
                    native_seq_extract xs (i + 1)
                        (Int.ofNat xs.length + -(i + 1)) =
                      xs.drop (j + 1) := by
                  rw [hNextCast, hRemainingNatCast]
                  exact native_seq_extract_to_end_nat xs (j + 1) hjSuccLe
                have hNthEval :
                    __smtx_seq_nth M (SmtValue.Seq sy) (SmtValue.Numeral i) =
                      xs.getD j SmtValue.NotValue := by
                  simp only [__smtx_seq_nth]
                  rw [← hCast, sr_ssm_seq_nth_ofNat]
                  exact sr_getD_lt_eq _ _ _ _ hjlt
                have hDecomp :
                    native_seq_extract xs 0 i ++
                        [__smtx_seq_nth M (SmtValue.Seq sy)
                          (SmtValue.Numeral i)] ++
                        native_seq_extract xs (i + 1)
                          (Int.ofNat xs.length + -(i + 1)) = xs := by
                  rw [hPreExtract, hNthEval, hSuffixExtract]
                  exact sr_take_getD_drop_succ SmtValue.NotValue xs j hjlt
                have hPreLen :
                    Int.ofNat (native_seq_extract xs 0 i).length = i := by
                  rw [hPreExtract, List.length_take,
                    Nat.min_eq_left (Nat.le_of_lt hjlt), hCast]
                have hSuffixLen :
                    Int.ofNat
                        (native_seq_extract xs (i + 1)
                          (Int.ofNat xs.length + -(i + 1))).length =
                      Int.ofNat xs.length + -(i + 1) := by
                  rw [hSuffixExtract, List.length_drop, hRemainingCast]
                have hPack : native_pack_seq T xs = sy := by
                  rw [← hElemTy]
                  exact native_pack_unpack_seq sy
                simp only [__smtx_model_eval_leq, __smtx_model_eval_lt,
                  native_zleq, native_zlt, decide_eq_true_eq.mpr hi,
                  decide_eq_true_eq.mpr hlt, native_and, native_not,
                  __smtx_model_eval_not, __smtx_model_eval_or]
                simp only [Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                  native_unpack_seq]
                simp [xs] at hDecomp hPreLen hSuffixLen hPack
                simp [hElemTy, hDecomp, hPreLen, hSuffixLen, hPack,
                  native_veq, native_and, native_or]
              · simp [__smtx_model_eval_or, __smtx_model_eval_not,
                  __smtx_model_eval_leq, __smtx_model_eval_lt,
                  native_zleq, native_zlt, native_and, native_not,
                  native_or, hi, hlt, Int.le_of_not_gt hlt]
                exact Or.inl (Int.le_of_not_gt hlt)
            · simp [__smtx_model_eval_or, __smtx_model_eval_not,
                __smtx_model_eval_leq, __smtx_model_eval_lt, native_zleq,
                native_zlt, native_and, native_not, native_or, hi]
        case str_leq =>
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          have hOrigNN :
              term_has_non_none_type (SmtTerm.str_leq ty tx) := by
            simpa [ty, tx, RuleProofs.eo_has_smt_translation] using hTrans
          have hArgs := seq_char_binop_args_of_non_none
            (op := SmtTerm.str_leq) (typeof_str_leq_eq ty tx) hOrigNN
          have hyTy : __smtx_typeof ty = SmtType.Seq SmtType.Char := hArgs.1
          have hxTy : __smtx_typeof tx = SmtType.Seq SmtType.Char := hArgs.2
          have hYNN : term_has_non_none_type ty := by
            unfold term_has_non_none_type
            rw [hyTy]
            exact seq_ne_none SmtType.Char
          have hXNN : term_has_non_none_type tx := by
            unfold term_has_non_none_type
            rw [hxTy]
            exact seq_ne_none SmtType.Char
          have hLeqTy :
              __smtx_typeof (SmtTerm.str_leq ty tx) = SmtType.Bool := by
            rw [typeof_str_leq_eq, hyTy, hxTy]
            simp [native_ite, native_Teq]
          have hYValTy :
              __smtx_typeof_value (__smtx_model_eval M ty) =
                SmtType.Seq SmtType.Char := by
            simpa [hyTy] using
              smt_model_eval_preserves_type_of_non_none M hM ty hYNN
          have hXValTy :
              __smtx_typeof_value (__smtx_model_eval M tx) =
                SmtType.Seq SmtType.Char := by
            simpa [hxTy] using
              smt_model_eval_preserves_type_of_non_none M hM tx hXNN
          rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
          rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
          have hSyTy :
              __smtx_typeof_seq_value sy =
                SmtType.Seq SmtType.Char := by
            simpa [hYEval, __smtx_typeof_value] using hYValTy
          have hSxTy :
              __smtx_typeof_seq_value sx =
                SmtType.Seq SmtType.Char := by
            simpa [hXEval, __smtx_typeof_value] using hXValTy
          let ys := native_unpack_string sy
          let xs := native_unpack_string sx
          have hYValid : native_string_valid ys = true :=
            native_unpack_string_valid_of_typeof_seq_char hSyTy
          have hXValid : native_string_valid xs = true :=
            native_unpack_string_valid_of_typeof_seq_char hSxTy
          have hYPack : native_pack_string ys = sy :=
            sr_native_pack_unpack_string sy hSyTy
          have hXPack : native_pack_string xs = sx :=
            sr_native_pack_unpack_string sx hSxTy
          have hYEvalString :
              __smtx_model_eval M ty =
                SmtValue.Seq (native_pack_string ys) := by
            rw [hYPack]
            exact hYEval
          have hXEvalString :
              __smtx_model_eval M tx =
                SmtValue.Seq (native_pack_string xs) := by
            rw [hXPack]
            exact hXEval
          have hClosedArgs :
              __eo_is_closed y = Term.Boolean true ∧
                __eo_is_closed x = Term.Boolean true := by
            simpa [__eo_is_closed, __eo_is_closed_rec, __eo_and,
              native_and] using hClosed
          let idxName := native_string_lit "@var.str_index"
          let idx := SmtTerm.Var idxName SmtType.Int
          let sCode := SmtTerm.str_to_code
            (SmtTerm.str_substr ty idx (SmtTerm.Numeral 1))
          let tCode := SmtTerm.str_to_code
            (SmtTerm.str_substr tx idx (SmtTerm.Numeral 1))
          let leqResult := SmtTerm._at_purify (SmtTerm.str_leq ty tx)
          let prefixEq := SmtTerm.eq
            (SmtTerm.str_substr ty (SmtTerm.Numeral 0) idx)
            (SmtTerm.str_substr tx (SmtTerm.Numeral 0) idx)
          let cmp := SmtTerm.ite leqResult
            (SmtTerm.geq sCode tCode) (SmtTerm.geq tCode sCode)
          let qBody := SmtTerm.or
            (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
            (SmtTerm.or
              (SmtTerm.not (SmtTerm.leq idx (SmtTerm.str_len ty)))
              (SmtTerm.or
                (SmtTerm.not (SmtTerm.leq idx (SmtTerm.str_len tx)))
                (SmtTerm.or (SmtTerm.not prefixEq)
                  (SmtTerm.or cmp (SmtTerm.Boolean false)))))
          let formula := SmtTerm.ite (SmtTerm.eq ty tx) leqResult
            (SmtTerm.not (SmtTerm.forall idxName SmtType.Int qBody))
          apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof formula = SmtType.Bool
            simp [formula, qBody, cmp, prefixEq, leqResult, tCode,
              sCode, idx, typeof_ite_eq, typeof_eq_eq, typeof_not_eq,
              smtx_typeof_forall_term_eq, typeof_or_eq, typeof_geq_eq,
              typeof_leq_eq, typeof_str_len_eq, typeof_str_substr_eq,
              typeof_str_to_code_eq, hyTy, hxTy, hLeqTy,
              __smtx_typeof, __smtx_typeof_seq_op_1,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_str_substr,
              __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
              __smtx_typeof_guard, __smtx_typeof_ite, native_ite,
              native_Teq]
          · change __smtx_model_eval M formula = SmtValue.Boolean true
            have hLeqEval :
                __smtx_model_eval M leqResult =
                  SmtValue.Boolean (sr_native_str_leq_bool ys xs) := by
              simp [leqResult, __smtx_model_eval, hYEvalString,
                hXEvalString, __smtx_model_eval__at_purify,
                __smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
                __smtx_model_eval_eq, __smtx_model_eval_or,
                sr_native_str_leq_bool, sr_native_unpack_pack_string,
                native_veq, native_or]
            by_cases hEq : ys = xs
            · subst xs
              simp [formula, __smtx_model_eval, hYEvalString,
                hXEvalString, hLeqEval, __smtx_model_eval_ite,
                __smtx_model_eval_eq, sr_native_str_leq_bool,
                native_str_lt, native_veq, native_or]
            · rcases sr_native_str_leq_witness ys xs hYValid hXValid hEq with
                ⟨j, hjY, hjX, hPrefix, hCmp⟩
              have hForallFalse :
                  native_eval_tforall M idxName SmtType.Int qBody =
                    SmtValue.Boolean false := by
                simp only [native_eval_tforall]
                rw [if_neg]
                intro hAll
                have hAt := hAll (SmtValue.Numeral (Int.ofNat j))
                  (by rfl) (by simp [__smtx_value_canonical_bool])
                let Mj := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral (Int.ofNat j))
                have hYEvalPush :
                    __smtx_model_eval Mj ty =
                      SmtValue.Seq (native_pack_string ys) := by
                  rw [← hYEvalString]
                  exact (smt_model_eval_eq_of_eo_closed y hClosedArgs.1 M Mj
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral (Int.ofNat j)))).symm
                have hXEvalPush :
                    __smtx_model_eval Mj tx =
                      SmtValue.Seq (native_pack_string xs) := by
                  rw [← hXEvalString]
                  exact (smt_model_eval_eq_of_eo_closed x hClosedArgs.2 M Mj
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral (Int.ofNat j)))).symm
                have hLeqEvalPush :
                    __smtx_model_eval Mj leqResult =
                      SmtValue.Boolean (sr_native_str_leq_bool ys xs) := by
                  simp [leqResult, __smtx_model_eval, hYEvalPush,
                    hXEvalPush, __smtx_model_eval__at_purify,
                    __smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
                    __smtx_model_eval_eq, __smtx_model_eval_or,
                    sr_native_str_leq_bool, sr_native_unpack_pack_string,
                    native_veq, native_or]
                change __smtx_model_eval Mj qBody =
                    SmtValue.Boolean true at hAt
                have hPrefixStringY :=
                  sr_native_str_substr_zero_nat ys j hjY
                have hPrefixStringX :=
                  sr_native_str_substr_zero_nat xs j hjX
                simp [qBody, cmp, prefixEq, tCode, sCode, idx, Mj,
                  __smtx_model_eval, hYEvalPush, hXEvalPush, hLeqEvalPush,
                  native_model_var_lookup, native_model_push,
                  __smtx_model_eval_or, __smtx_model_eval_not,
                  __smtx_model_eval_geq, __smtx_model_eval_leq,
                  __smtx_model_eval_eq, __smtx_model_eval_ite,
                  __smtx_model_eval_str_len,
                  __smtx_model_eval_str_substr,
                  __smtx_model_eval_str_to_code, native_seq_len,
                  native_zleq, native_and, native_or, native_not,
                  Smtm.native_unpack_pack_seq, sr_native_unpack_pack_string,
                  sr_native_seq_extract_pack_string, hPrefixStringY,
                  hPrefixStringX, hPrefix, hjY, hjX,
                  sr_native_str_leq_bool] at hAt
                split at hCmp
                · omega
                · omega
              simp [formula, __smtx_model_eval, hYEvalString,
                hXEvalString, hLeqEval, hForallFalse,
                __smtx_model_eval_ite, __smtx_model_eval_eq,
                __smtx_model_eval_not, native_veq, native_not,
                sr_native_unpack_pack_string, hEq]
      case Apply h z =>
        cases h <;> try
          simp [__str_reduction_pred, stringReductionBody,
            __eo_mk_apply] at hBodyTy ⊢
        all_goals try
          (change Term.Stuck = Term.Bool at hBodyTy
           exact False.elim (Term.noConfusion hBodyTy))
        case UOp op =>
          cases op <;> try
            simp [__str_reduction_pred, stringReductionBody,
              __eo_mk_apply] at hBodyTy ⊢
          all_goals try
            (change Term.Stuck = Term.Bool at hBodyTy
             exact False.elim (Term.noConfusion hBodyTy))

/-- The complete generated result is true whenever its guard succeeds. -/
private theorem string_reduction_true
    (M : SmtModel) (hM : model_total_typed M) (s : Term)
    (hTrans : RuleProofs.eo_has_smt_translation s)
    (hTy : __eo_typeof (__eo_prog_string_reduction s) = Term.Bool) :
    eo_interprets M (__eo_prog_string_reduction s) true := by
  have hProg : __eo_prog_string_reduction s ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  have hsNe : s ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation s hTrans
  have hProgEq :
      __eo_prog_string_reduction s =
        __eo_requires (__is_closed_rec s Term.__eo_List_nil)
          (Term.Boolean true) (stringReductionBody s) := by
    cases s <;> simp [__eo_prog_string_reduction, stringReductionBody] at hsNe ⊢
  have hReqNe :
      __eo_requires (__is_closed_rec s Term.__eo_List_nil)
          (Term.Boolean true) (stringReductionBody s) ≠ Term.Stuck := by
    simpa [hProgEq] using hProg
  have hReduce :
      __eo_prog_string_reduction s = stringReductionBody s := by
    rw [hProgEq]
    exact eo_requires_eq_result_of_ne_stuck _ _ _ hReqNe
  have hClosedRec :
      __is_closed_rec s Term.__eo_List_nil = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck _ _ _ hReqNe
  have hClosed : __eo_is_closed s = Term.Boolean true := by
    cases s <;> simp [__eo_is_closed] at hsNe hClosedRec ⊢
    all_goals exact hClosedRec
  have hBodyTy : __eo_typeof (stringReductionBody s) = Term.Bool := by
    simpa [hReduce] using hTy
  rw [hReduce]
  exact string_reduction_body_true M s hTrans
    (string_reduction_pred_true M hM s hTrans hClosed hBodyTy)

theorem cmd_step_string_reduction_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_reduction args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_reduction args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.string_reduction args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      exact False.elim (hProg rfl)
  | cons a args =>
      cases args with
      | cons _ _ =>
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              exact False.elim (hProg rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation a := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using
                  hCmdTrans.1
              have hTrue : eo_interprets M (__eo_prog_string_reduction a) true := by
                exact string_reduction_true M hM a hATrans hResultTy
              refine ⟨?_, ?_⟩
              · intro _
                exact hTrue
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (RuleProofs.eo_has_bool_type_of_interprets_true M _ hTrue)
