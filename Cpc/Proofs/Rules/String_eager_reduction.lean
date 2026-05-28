import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.RuleSupport.StringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem native_unpack_string_length_eq (ss : SmtSeq) :
    (native_unpack_string ss).length = (native_unpack_seq ss).length := by
  simp [native_unpack_string]

private theorem native_unpack_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  unfold native_unpack_string native_pack_string
  rw [native_unpack_pack_seq]
  induction s with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [native_ssm_char_of_value, ih]

private theorem native_str_to_code_singleton_bounds
    {xs : native_String}
    (hValid : native_string_valid xs = true)
    (hLen : xs.length = 1) :
    0 ≤ native_str_to_code xs ∧ native_str_to_code xs < 196608 := by
  cases xs with
  | nil =>
      simp at hLen
  | cons c cs =>
      cases cs with
      | nil =>
          simp [native_string_valid] at hValid
          have hc : c < 196608 := by simpa [native_char_valid] using hValid
          simp [native_str_to_code, native_char_valid, hc]
          exact Int.ofNat_lt.mpr hc
      | cons d ds =>
          simp at hLen

private theorem native_str_to_code_non_singleton
    (xs : native_String)
    (hLen : xs.length ≠ 1) :
    native_str_to_code xs = -1 := by
  cases xs with
  | nil =>
      simp [native_str_to_code]
  | cons c cs =>
      cases cs with
      | nil =>
          exfalso
          exact hLen (by simp)
      | cons d ds =>
          simp [native_str_to_code]

private theorem native_str_to_code_from_code_of_valid
    {n : native_Int}
    (hn0 : 0 ≤ n) (hnHi : n < 196608) :
    native_str_to_code (native_str_from_code n) = n := by
  have hNatLt : Int.toNat n < 196608 := by
    exact (Int.toNat_lt hn0).mpr hnHi
  simp [native_str_from_code, native_str_to_code, native_char_valid, hn0,
    hNatLt, Int.toNat_of_nonneg hn0]

private theorem native_str_from_code_invalid
    {n : native_Int}
    (hBad : ¬ (0 ≤ n ∧ n < 196608)) :
    native_str_from_code n = [] := by
  unfold native_str_from_code
  by_cases hn0 : 0 ≤ n
  · have hNatLtFalse : ¬ Int.toNat n < 196608 := by
      intro hNatLt
      have hnHi : n < 196608 := (Int.toNat_lt hn0).mp hNatLt
      exact hBad ⟨hn0, hnHi⟩
    have hGuard :
        (0 ≤ n && native_char_valid (Int.toNat n)) = false := by
      simp [hn0, native_char_valid, hNatLtFalse]
    rw [hGuard]
    rfl
  · have hGuard :
        (0 ≤ n && native_char_valid (Int.toNat n)) = false := by
      simp [hn0]
    rw [hGuard]
    rfl

private theorem native_str_to_int_ge_neg_one
    (s : native_String) :
    (-1 : Int) ≤ native_str_to_int s := by
  cases s with
  | nil =>
      simp [native_str_to_int]
  | cons c cs =>
      by_cases hDigits : List.all (c :: cs) native_char_is_digit = true
      · simp [native_str_to_int, hDigits, Int.natCast_nonneg]
      · simp [native_str_to_int, hDigits]

private theorem int_nonneg_of_not_neg {i : native_Int} (hi : ¬ i < 0) :
    0 ≤ i := by
  cases i with
  | ofNat n =>
      simp
  | negSucc n =>
      exfalso
      exact hi (by simp)

private theorem native_seq_indexof_rec_eq_neg_one_or_ge
    (xs pat : List SmtValue) :
    (i fuel : Nat) ->
    native_seq_indexof_rec xs pat i fuel = -1 ∨
      Int.ofNat i ≤ native_seq_indexof_rec xs pat i fuel
  | i, 0 => by
      simp [native_seq_indexof_rec]
  | i, fuel + 1 => by
      unfold native_seq_indexof_rec
      split
      · right
        simp
      · cases xs with
        | nil =>
            simp
        | cons _ xs =>
            cases native_seq_indexof_rec_eq_neg_one_or_ge xs pat (i + 1) fuel with
            | inl h =>
                left
                exact h
            | inr h =>
                right
                exact Int.le_trans (Int.ofNat_le.mpr (Nat.le_succ i)) h

private theorem native_seq_indexof_eq_neg_one_or_ge
    (xs pat : List SmtValue) (i : native_Int) :
    native_seq_indexof xs pat i = -1 ∨ i ≤ native_seq_indexof xs pat i := by
  unfold native_seq_indexof
  by_cases hi : i < 0
  · simp [hi]
  · have hi0 : 0 ≤ i := int_nonneg_of_not_neg hi
    simp [hi]
    by_cases hBounds : Int.toNat i + pat.length ≤ xs.length
    · simp [hBounds]
      cases native_seq_indexof_rec_eq_neg_one_or_ge (xs.drop (Int.toNat i)) pat
          (Int.toNat i) (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl h =>
          exact Or.inl h
      | inr h =>
          right
          calc
            i = (Int.toNat i : Int) := (Int.toNat_of_nonneg hi0).symm
            _ ≤ native_seq_indexof_rec (xs.drop (Int.toNat i)) pat (Int.toNat i)
                (xs.length - (Int.toNat i + pat.length) + 1) := h
    · simp [hBounds]

private theorem native_seq_indexof_rec_bound
    (xs pat : List SmtValue) :
    (i fuel : Nat) ->
    native_seq_indexof_rec xs pat i fuel = -1 ∨
      ∃ j : Nat, native_seq_indexof_rec xs pat i fuel = Int.ofNat (i + j) ∧
        j < fuel
  | i, 0 => by
      simp [native_seq_indexof_rec]
  | i, fuel + 1 => by
      unfold native_seq_indexof_rec
      split
      · right
        exact ⟨0, by simp, by omega⟩
      · cases xs with
        | nil =>
            simp
        | cons _ xs =>
            cases native_seq_indexof_rec_bound xs pat (i + 1) fuel with
            | inl h =>
                left
                exact h
            | inr h =>
                rcases h with ⟨j, hj, hjlt⟩
                right
                refine ⟨j + 1, ?_, by omega⟩
                simpa [hj, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem native_seq_indexof_le_len
    (xs pat : List SmtValue) (i : native_Int) :
    native_seq_indexof xs pat i ≤ Int.ofNat xs.length := by
  unfold native_seq_indexof
  split
  · exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.natCast_nonneg _)
  · dsimp
    split
    · rename_i hStart h
      cases native_seq_indexof_rec_bound (xs.drop (Int.toNat i)) pat (Int.toNat i)
          (xs.length - (Int.toNat i + pat.length) + 1) with
      | inl hRec =>
          rw [hRec]
          exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.natCast_nonneg _)
      | inr hRec =>
          rcases hRec with ⟨j, hRec, hjlt⟩
          rw [hRec]
          apply Int.ofNat_le.mpr
          have hjle : j ≤ xs.length - (Int.toNat i + pat.length) := by
            omega
          omega
    · exact Int.le_trans (by decide : (-1 : Int) ≤ 0) (Int.natCast_nonneg _)

private theorem native_seq_extract_zero_nat
    (xs : List SmtValue) (n : Nat) (hle : n <= xs.length) :
    native_seq_extract xs 0 (Int.ofNat n) = xs.take n := by
  unfold native_seq_extract
  by_cases hn : n = 0
  · subst n
    simp
  · have hnPosNat : 0 < n := Nat.pos_of_ne_zero hn
    have hnPos : (0 : Int) < Int.ofNat n := Int.ofNat_lt.mpr hnPosNat
    have hxsPosNat : 0 < xs.length := Nat.lt_of_lt_of_le hnPosNat hle
    have hxsNe : xs ≠ [] := by
      intro h
      subst xs
      simp at hxsPosNat
    have hmin : min (Int.ofNat n) (Int.ofNat xs.length) = Int.ofNat n :=
      Int.min_eq_left (Int.ofNat_le.mpr hle)
    have hminToNat :
        (min (Int.ofNat n) (Int.ofNat xs.length)).toNat = n := by
      rw [hmin]
      simp
    have hminNat : min n xs.length = n := Nat.min_eq_left hle
    simp [hn, hxsNe, hnPos]
    change
      min ((min (Int.ofNat n) (Int.ofNat xs.length)).toNat) xs.length =
        min n xs.length
    rw [hminToNat, hminNat]

private theorem native_seq_extract_to_end_nat
    (xs : List SmtValue) (i : Nat) (hle : i <= xs.length) :
    native_seq_extract xs (Int.ofNat i) (Int.ofNat (xs.length - i)) =
      xs.drop i := by
  unfold native_seq_extract
  by_cases hend : xs.length - i = 0
  · have hLenLe : xs.length <= i := by omega
    have hcast : (Int.ofNat i >= Int.ofNat xs.length) = true := by
      simp [hLenLe]
    simp [hend, hcast, List.drop_eq_nil_of_le hLenLe]
  · have htailPosNat : 0 < xs.length - i := Nat.pos_of_ne_zero hend
    have hiltNat : i < xs.length := by omega
    have htailPos : (0 : Int) < Int.ofNat (xs.length - i) :=
      Int.ofNat_lt.mpr htailPosNat
    have hilt : Int.ofNat i < Int.ofNat xs.length :=
      Int.ofNat_lt.mpr hiltNat
    have hcastSub : Int.ofNat (xs.length - i) = Int.ofNat xs.length - Int.ofNat i :=
      Int.ofNat_sub hle
    have hmin :
        min (Int.ofNat (xs.length - i))
            (Int.ofNat xs.length - Int.ofNat i) =
          Int.ofNat (xs.length - i) := by
      rw [← hcastSub]
      exact Int.min_eq_left (Int.le_refl _)
    have htake :
        (xs.drop i).take (xs.length - i) = xs.drop i := by
      apply List.take_of_length_le
      rw [List.length_drop]
      exact Nat.le_refl _
    have hLenNotLe : ¬ xs.length <= i := Nat.not_le_of_gt hiltNat
    have hiNonneg : ¬ ((i : native_Int) < (0 : native_Int)) := by
      exact Int.not_lt_of_ge (Int.natCast_nonneg i)
    have hminToNat :
        (min (Int.ofNat (xs.length - i))
            (Int.ofNat xs.length - Int.ofNat i)).toNat =
          xs.length - i := by
      rw [hmin]
      simp
    simp [hend, hLenNotLe, htailPos, hilt]
    rw [if_neg hiNonneg]
    change
      List.take
          ((min (Int.ofNat (xs.length - i))
              (Int.ofNat xs.length - Int.ofNat i)).toNat)
          (List.drop i xs) =
        List.drop i xs
    rw [hminToNat]
    exact htake

private theorem native_seq_prefix_eq_append_drop
    (pat xs : List SmtValue) :
    native_seq_prefix_eq pat xs = true ->
      pat ++ xs.drop pat.length = xs := by
  induction pat generalizing xs with
  | nil =>
      intro _h
      simp
  | cons p ps ih =>
      cases xs with
      | nil =>
          intro h
          simp [native_seq_prefix_eq] at h
      | cons x xs =>
          intro h
          have hParts : p = x ∧ native_seq_prefix_eq ps xs = true := by
            simpa [native_seq_prefix_eq, native_veq] using h
          rcases hParts with ⟨rfl, hTail⟩
          simpa using ih xs hTail

private theorem native_seq_prefix_eq_self
    (xs : List SmtValue) :
    native_seq_prefix_eq xs xs = true := by
  induction xs with
  | nil =>
      rfl
  | cons x xs ih =>
      simp [native_seq_prefix_eq, native_veq, ih]

private theorem native_seq_indexof_self_zero
    (xs : List SmtValue) :
    native_seq_indexof xs xs 0 = 0 := by
  unfold native_seq_indexof
  have hBounds : xs.length ≤ xs.length := Nat.le_refl _
  simp [hBounds]
  unfold native_seq_indexof_rec
  simp [native_seq_prefix_eq_self]

private theorem native_seq_contains_self
    (xs : List SmtValue) :
    native_seq_contains xs xs = true := by
  simp [native_seq_contains, native_seq_indexof_self_zero]

private theorem native_seq_indexof_rec_decomp
    (xs pat : List SmtValue) :
    (i fuel j : Nat) ->
      native_seq_indexof_rec xs pat i fuel = Int.ofNat j ->
      i ≤ j ∧
        ∃ before after : List SmtValue,
          xs = before ++ pat ++ after ∧ before.length = j - i
  | i, 0, j, h => by
      simp [native_seq_indexof_rec] at h
  | i, fuel + 1, j, h => by
      unfold native_seq_indexof_rec at h
      by_cases hPrefix : native_seq_prefix_eq pat xs = true
      · rw [if_pos hPrefix] at h
        have hji : j = i := Int.ofNat.inj h.symm
        subst j
        constructor
        · exact Nat.le_refl _
        · refine ⟨[], xs.drop pat.length, ?_, by simp⟩
          exact (native_seq_prefix_eq_append_drop pat xs hPrefix).symm
      · rw [if_neg hPrefix] at h
        cases xs with
        | nil =>
            simp at h
        | cons x xs =>
            rcases native_seq_indexof_rec_decomp xs pat (i + 1) fuel j h with
              ⟨hLe, before, after, hXs, hBeforeLen⟩
            constructor
            · omega
            · refine ⟨x :: before, after, ?_, ?_⟩
              · simp [hXs, List.append_assoc]
              · simp [hBeforeLen]
                omega

private theorem native_seq_indexof_zero_decomp_of_nat
    (xs pat : List SmtValue) (j : Nat)
    (hIdx : native_seq_indexof xs pat 0 = Int.ofNat j) :
    native_seq_extract xs 0 (Int.ofNat j) ++ pat ++
        native_seq_extract xs (Int.ofNat j + Int.ofNat pat.length)
          (Int.ofNat xs.length - (Int.ofNat j + Int.ofNat pat.length)) =
      xs := by
  unfold native_seq_indexof at hIdx
  by_cases hBounds : pat.length ≤ xs.length
  · simp [hBounds] at hIdx
    rcases native_seq_indexof_rec_decomp xs pat 0
        (xs.length - pat.length + 1) j hIdx with
      ⟨_hLe, before, after, hXs, hBeforeLen⟩
    have hBeforeLen' : before.length = j := by
      simpa using hBeforeLen
    have hJLe : j ≤ xs.length := by
      have hLen := congrArg List.length hXs
      simp [hBeforeLen'] at hLen
      omega
    have hStartLe : j + pat.length ≤ xs.length := by
      have hLen := congrArg List.length hXs
      simp [hBeforeLen'] at hLen
      omega
    have hPre :
        native_seq_extract xs 0 (Int.ofNat j) = before := by
      rw [native_seq_extract_zero_nat xs j hJLe]
      rw [hXs]
      simp [hBeforeLen']
    have hSub :
        Int.ofNat xs.length - (Int.ofNat j + Int.ofNat pat.length) =
          Int.ofNat (xs.length - (j + pat.length)) := by
      have hAdd :
          Int.ofNat j + Int.ofNat pat.length =
            Int.ofNat (j + pat.length) := by
        simp
      rw [hAdd]
      exact (Int.ofNat_sub hStartLe).symm
    have hSuf :
        native_seq_extract xs (Int.ofNat j + Int.ofNat pat.length)
            (Int.ofNat xs.length - (Int.ofNat j + Int.ofNat pat.length)) =
          after := by
      have hAdd :
          Int.ofNat j + Int.ofNat pat.length =
            Int.ofNat (j + pat.length) := by
        simp
      have hSub' :
          Int.ofNat xs.length - Int.ofNat (j + pat.length) =
            Int.ofNat (xs.length - (j + pat.length)) :=
        (Int.ofNat_sub hStartLe).symm
      rw [hAdd, hSub']
      rw [native_seq_extract_to_end_nat xs (j + pat.length) hStartLe]
      rw [hXs]
      rw [← hBeforeLen']
      simp
    rw [hPre, hSuf, hXs]
  · simp [hBounds] at hIdx

private theorem native_seq_indexof_zero_decomp
    (xs pat : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    let idx := native_seq_indexof xs pat 0
    native_seq_extract xs 0 idx ++ pat ++
        native_seq_extract xs (idx + Int.ofNat pat.length)
          (Int.ofNat xs.length - (idx + Int.ofNat pat.length)) =
      xs := by
  let idx := native_seq_indexof xs pat 0
  let j := Int.toNat idx
  have hCast : Int.ofNat j = idx := Int.toNat_of_nonneg hIdxNonneg
  have hIdx : native_seq_indexof xs pat 0 = Int.ofNat j := by
    rw [hCast]
  change
    native_seq_extract xs 0 idx ++ pat ++
        native_seq_extract xs (idx + Int.ofNat pat.length)
          (Int.ofNat xs.length - (idx + Int.ofNat pat.length)) =
      xs
  rw [← hCast]
  exact native_seq_indexof_zero_decomp_of_nat xs pat j hIdx

private theorem native_seq_extract_prefix_length_of_indexof_nonneg
    (xs pat : List SmtValue)
    (hIdxNonneg : 0 ≤ native_seq_indexof xs pat 0) :
    Int.ofNat (native_seq_extract xs 0 (native_seq_indexof xs pat 0)).length =
      native_seq_indexof xs pat 0 := by
  let idx := native_seq_indexof xs pat 0
  let j := Int.toNat idx
  have hCast : Int.ofNat j = idx := Int.toNat_of_nonneg hIdxNonneg
  have hIdx : native_seq_indexof xs pat 0 = Int.ofNat j := by
    rw [hCast]
  unfold native_seq_indexof at hIdx
  by_cases hBounds : pat.length ≤ xs.length
  · simp [hBounds] at hIdx
    rcases native_seq_indexof_rec_decomp xs pat 0
        (xs.length - pat.length + 1) j hIdx with
      ⟨_hLe, before, after, hXs, hBeforeLen⟩
    have hBeforeLen' : before.length = j := by
      simpa using hBeforeLen
    have hJLe : j ≤ xs.length := by
      have hLen := congrArg List.length hXs
      simp [hBeforeLen'] at hLen
      omega
    change Int.ofNat (native_seq_extract xs 0 idx).length = idx
    rw [← hCast]
    rw [native_seq_extract_zero_nat xs j hJLe]
    simp [List.length_take, Nat.min_eq_left hJLe]
  · simp [native_seq_indexof, hBounds] at hIdx

private theorem strConcat_nil_eq_seq_empty_of_type {ty : Term} {T : SmtType}
    (hTy : __eo_to_smt_type ty = SmtType.Seq T) :
    __eo_nil (Term.UOp UserOp.str_concat) ty = __seq_empty ty := by
  rcases TranslationProofs.eo_to_smt_type_eq_seq hTy with ⟨V, hTyEq, _hV⟩
  subst ty
  rfl

private theorem smt_typeof_seq_empty_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof (__eo_to_smt (__seq_empty (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  have hSeqWF : __smtx_type_wf (SmtType.Seq T) = true := by
    have hGood :=
      smt_term_result_seq_components_wf_of_non_none (__eo_to_smt x) hTrans
    simpa [hxTy] using hGood
  by_cases hSpecial :
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)
  · rw [hSpecial]
    change __smtx_typeof (SmtTerm.String (native_string_lit "")) = SmtType.Seq T
    rw [__smtx_typeof.eq_4]
    rw [hSpecial] at hA
    simp [TranslationProofs.eo_to_smt_type_seq,
      TranslationProofs.eo_to_smt_type_char] at hA
    exact hA
  ·
    by_cases hStuck : __eo_typeof x = Term.Stuck
    · rw [hStuck] at hA
      simp [__eo_to_smt_type] at hA
    · have hDefault :
          __seq_empty (__eo_typeof x) = Term.UOp1 UserOp1.seq_empty (__eo_typeof x) := by
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
          (__eo_to_smt_type (__eo_typeof x))) = SmtType.Seq T
      rw [hA]
      change __smtx_typeof (SmtTerm.seq_empty T) = SmtType.Seq T
      simp [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, hSeqWF]

private theorem smt_typeof_nil_str_concat_typeof_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_typeof
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) =
      SmtType.Seq T := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rw [strConcat_nil_eq_seq_empty_of_type hA]
  exact smt_typeof_seq_empty_typeof_of_smt_type_seq x T hxTy

private theorem nil_str_concat_typeof_ne_stuck_of_smt_type_seq
    (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x) ≠ Term.Stuck := by
  intro h
  have hNilTy :=
    smt_typeof_nil_str_concat_typeof_of_smt_type_seq x T hxTy
  rw [h] at hNilTy
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hNilTy
  rw [TranslationProofs.smtx_typeof_none] at hNilTy
  cases hNilTy

private theorem eval_nil_str_concat_typeof_of_smt_type_seq
    (M : SmtModel) (x : Term) (T : SmtType)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __smtx_model_eval M
        (__eo_to_smt (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof x))) =
      SmtValue.Seq (SmtSeq.empty T) := by
  have hTrans : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
    rw [hxTy]
    exact seq_ne_none T
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation x hTrans
  have hA : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
    rw [← hTypeMatch, hxTy]
  rw [strConcat_nil_eq_seq_empty_of_type hA]
  exact eval_seq_empty_typeof M x T hxTy

private theorem native_re_find_idx_aux_bound
    {r : native_RegLan} :
    (xs : List native_Char) -> (idx : Nat) -> {found len : Nat} ->
      native_re_find_idx_aux r xs idx = some (found, len) ->
      idx ≤ found ∧ found ≤ idx + xs.length
  | xs, idx, found, len, hFind => by
      unfold native_re_find_idx_aux at hFind
      split at hFind
      · cases hFind
        omega
      · cases xs with
        | nil =>
            simp at hFind
        | cons _ cs =>
            have h := native_re_find_idx_aux_bound cs (idx + 1) hFind
            rcases h with ⟨hLo, hHi⟩
            constructor
            · omega
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hHi

private theorem native_str_indexof_re_eq_neg_one_or_ge
    (s : native_String) (r : native_RegLan) (i : native_Int) :
    native_str_indexof_re s r i = -1 ∨ i ≤ native_str_indexof_re s r i := by
  unfold native_str_indexof_re
  by_cases hi : i < 0
  · simp [hi]
  · have hi0 : 0 ≤ i := int_nonneg_of_not_neg hi
    by_cases hGuard : native_string_valid s = true ∧ i ≤ Int.ofNat s.length
    · have hValid := hGuard.1
      have hIle := hGuard.2
      simp [hi, hi0, Int.toNat_of_nonneg hi0, hValid, hIle]
      cases hFind : native_re_find_idx_from r s (Int.toNat i) with
      | none =>
          simp
      | some p =>
          cases p with
          | mk found len =>
              right
              unfold native_re_find_idx_from at hFind
              have hBound := native_re_find_idx_aux_bound (s.drop (Int.toNat i))
                (Int.toNat i) hFind
              have hLeFound : i ≤ (found : Int) := by
                calc
                i = (Int.toNat i : Int) := (Int.toNat_of_nonneg hi0).symm
                _ ≤ (found : Int) := Int.ofNat_le.mpr hBound.1
              by_cases hIle' : i ≤ (s.length : Int)
              · simpa [hIle'] using hLeFound
              · exact False.elim (hIle' hIle)
    · simp [hi, hi0, Int.toNat_of_nonneg hi0]
      left
      intro hValid hIle
      exact False.elim (hGuard ⟨hValid, hIle⟩)

private theorem native_str_indexof_re_le_len
    (s : native_String) (r : native_RegLan) (i : native_Int) :
    native_str_indexof_re s r i ≤ Int.ofNat s.length := by
  unfold native_str_indexof_re
  by_cases hi : i < 0
  · simp [hi]
  · have hi0 : 0 ≤ i := int_nonneg_of_not_neg hi
    by_cases hGuard : native_string_valid s = true ∧ i ≤ Int.ofNat s.length
    · have hValid := hGuard.1
      have hIle := hGuard.2
      simp [hi, hi0, Int.toNat_of_nonneg hi0, hValid, hIle]
      have hStartLe : Int.toNat i ≤ s.length := by
        exact Int.toNat_le.mpr hGuard.2
      cases hFind : native_re_find_idx_from r s (Int.toNat i) with
      | none =>
          by_cases hIle' : i ≤ (s.length : Int)
          · simp [hIle']
          · exact False.elim (hIle' hIle)
      | some p =>
          cases p with
          | mk found len =>
              by_cases hIle' : i ≤ (s.length : Int)
              · simp [hIle']
                unfold native_re_find_idx_from at hFind
                have hBound := native_re_find_idx_aux_bound (s.drop (Int.toNat i))
                  (Int.toNat i) hFind
                have hDropLen : (s.drop (Int.toNat i)).length =
                    s.length - Int.toNat i := by
                  simp [List.length_drop]
                have hFoundLe : found ≤ s.length := by
                  omega
                exact hFoundLe
              · exact False.elim (hIle' hIle)
    · have hGuardBool :
          (native_string_valid s && decide (Int.toNat i ≤ s.length)) = false := by
        cases hValidBool : native_string_valid s
        · simp [hValidBool]
        · have hNoStart : ¬ Int.toNat i ≤ s.length := by
            intro hStart
            have hIle : i ≤ Int.ofNat s.length := by
              rw [← Int.toNat_of_nonneg hi0]
              exact Int.ofNat_le.mpr hStart
            exact hGuard ⟨by simpa [hValidBool], hIle⟩
          simp [hValidBool, hNoStart]
      by_cases hAll : native_string_valid s = true ∧ i ≤ (s.length : Int)
      · exact False.elim (hGuard hAll)
      · simp [hAll]

private theorem int_eval_of_int_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int ->
    ∃ z : native_Int, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral z := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact int_value_canonical (by simpa [hTy] using hEvalTy)

private theorem seq_eval_of_seq_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    ∃ ss, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact seq_value_canonical (by simpa [hTy] using hEvalTy)

private theorem reglan_eval_of_reglan_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
    ∃ r, __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact reglan_value_canonical (by simpa [hTy] using hEvalTy)

private def nativeListInRe (xs : List native_Char) (r : native_RegLan) :
    native_Bool :=
  native_re_nullable <| xs.foldl (fun acc c => native_re_deriv c acc) r

private theorem nativeListInRe_empty :
    (xs : List native_Char) -> nativeListInRe xs SmtRegLan.empty = false
  | [] => by rfl
  | _ :: xs => by
      exact nativeListInRe_empty xs

private theorem native_re_nullable_mk_union (r s : native_RegLan) :
    native_re_nullable (native_re_mk_union r s) =
      (native_re_nullable r || native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem native_re_mk_union_self (r : native_RegLan) :
    native_re_mk_union r r = r := by
  cases r <;> simp [native_re_mk_union]

private theorem native_re_mk_union_eq_union_of_ne
    (r s : native_RegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_union r s = SmtRegLan.union r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_union] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem nativeListInRe_mk_union :
    (xs : List native_Char) -> (r s : native_RegLan) ->
      nativeListInRe xs (native_re_mk_union r s) =
        (nativeListInRe xs r || nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_union]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_union, nativeListInRe_empty]
      ·
        by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_union, nativeListInRe_empty]
        ·
          by_cases hEq : r = s
          · subst s
            rw [native_re_mk_union_self]
            simp [nativeListInRe]
          · rw [native_re_mk_union_eq_union_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_union cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_re_mk_inter_self (r : native_RegLan) :
    native_re_mk_inter r r = r := by
  cases r <;> simp [native_re_mk_inter]

private theorem native_re_mk_inter_eq_inter_of_ne
    (r s : native_RegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ s ->
    native_re_mk_inter r s = SmtRegLan.inter r s := by
  intro hr hs hrs
  cases r <;> cases s <;>
    simp [native_re_mk_inter] at hr hs ⊢
  all_goals
    try exact False.elim (hrs rfl)
    try
      intro h
      subst h
      exact False.elim (hrs rfl)
    try
      intro h1 h2
      subst h1
      subst h2
      exact False.elim (hrs rfl)

private theorem native_re_nullable_mk_inter (r s : native_RegLan) :
    native_re_nullable (native_re_mk_inter r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem nativeListInRe_mk_inter :
    (xs : List native_Char) -> (r s : native_RegLan) ->
      nativeListInRe xs (native_re_mk_inter r s) =
        (nativeListInRe xs r && nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_inter]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_inter, nativeListInRe_empty]
      ·
        by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_inter, nativeListInRe_empty]
        ·
          by_cases hEq : r = s
          · subst s
            rw [native_re_mk_inter_self]
            simp [nativeListInRe]
          · rw [native_re_mk_inter_eq_inter_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_inter cs
              (native_re_deriv c r) (native_re_deriv c s)

private theorem native_re_nullable_mk_concat (r s : native_RegLan) :
    native_re_nullable (native_re_mk_concat r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_nullable]

private theorem nativeListInRe_mk_concat_empty_left
    (xs : List native_Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat SmtRegLan.empty r) = false := by
  simp [native_re_mk_concat, nativeListInRe_empty]

private theorem nativeListInRe_mk_concat_empty_right
    (xs : List native_Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.empty) = false := by
  cases r <;> simp [native_re_mk_concat, nativeListInRe_empty]

private theorem nativeListInRe_mk_concat_epsilon_left
    (xs : List native_Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat SmtRegLan.epsilon r) =
      nativeListInRe xs r := by
  cases r <;> simp [native_re_mk_concat, nativeListInRe_empty]

private theorem nativeListInRe_mk_concat_epsilon_right
    (xs : List native_Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.epsilon) =
      nativeListInRe xs r := by
  cases r <;> simp [native_re_mk_concat, nativeListInRe_empty]

private theorem native_re_mk_concat_eq_concat_of_ne
    (r s : native_RegLan) :
    r ≠ SmtRegLan.empty ->
    s ≠ SmtRegLan.empty ->
    r ≠ SmtRegLan.epsilon ->
    s ≠ SmtRegLan.epsilon ->
    native_re_mk_concat r s = SmtRegLan.concat r s := by
  intro hrEmpty hsEmpty hrEps hsEps
  cases r <;> cases s <;>
    simp [native_re_mk_concat] at hrEmpty hsEmpty hrEps hsEps ⊢

private theorem nativeListInRe_deriv_mk_concat
    (xs : List native_Char) (c : native_Char) (r s : native_RegLan) :
    nativeListInRe xs (native_re_deriv c (native_re_mk_concat r s)) =
      nativeListInRe xs
        (native_re_mk_union
          (native_re_mk_concat (native_re_deriv c r) s)
          (if native_re_nullable r then native_re_deriv c s else SmtRegLan.empty)) := by
  by_cases hrEmpty : r = SmtRegLan.empty
  · subst r
    simp [native_re_mk_concat, native_re_deriv, native_re_nullable,
      nativeListInRe_mk_union, nativeListInRe_empty]
  ·
    by_cases hsEmpty : s = SmtRegLan.empty
    · subst s
      have hL :
          nativeListInRe xs
            (native_re_deriv c (native_re_mk_concat r SmtRegLan.empty)) =
            false := by
        simp [native_re_mk_concat, native_re_deriv, nativeListInRe_empty]
      rw [hL]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat_empty_right]
      simp [native_re_deriv, nativeListInRe_empty]
    ·
      by_cases hrEps : r = SmtRegLan.epsilon
      · subst r
        simp [native_re_mk_concat, native_re_deriv, native_re_nullable,
          nativeListInRe_mk_union, nativeListInRe_empty]
      ·
        by_cases hsEps : s = SmtRegLan.epsilon
        · subst s
          have hMk : native_re_mk_concat r SmtRegLan.epsilon = r := by
            cases r <;> simp [native_re_mk_concat] at hrEmpty hrEps ⊢
          rw [hMk]
          rw [nativeListInRe_mk_union]
          rw [nativeListInRe_mk_concat_epsilon_right]
          simp [native_re_deriv, nativeListInRe_empty]
        · have hMk :=
            native_re_mk_concat_eq_concat_of_ne r s hrEmpty hsEmpty hrEps hsEps
          rw [hMk]
          simp [native_re_deriv, nativeListInRe_mk_union]

private def nativeListInReConcat :
    List native_Char -> native_RegLan -> native_RegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && nativeListInRe (c :: cs) s) ||
        nativeListInReConcat cs (native_re_deriv c r) s

private theorem nativeListInRe_mk_concat :
    (xs : List native_Char) -> (r s : native_RegLan) ->
      nativeListInRe xs (native_re_mk_concat r s) =
        nativeListInReConcat xs r s
  | [], r, s => by
      simp [nativeListInRe, nativeListInReConcat,
        native_re_nullable_mk_concat]
  | c :: cs, r, s => by
      change
        nativeListInRe cs
            (native_re_deriv c (native_re_mk_concat r s)) =
          ((native_re_nullable r &&
              nativeListInRe cs (native_re_deriv c s)) ||
            nativeListInReConcat cs (native_re_deriv c r) s)
      rw [nativeListInRe_deriv_mk_concat cs c r s]
      rw [nativeListInRe_mk_union]
      rw [nativeListInRe_mk_concat cs (native_re_deriv c r) s]
      cases hNullable : native_re_nullable r <;>
        simp [hNullable, nativeListInRe_empty, Bool.or_comm]

private theorem nativeListInReConcat_true_iff_exists_append :
    (xs : List native_Char) -> (r s : native_RegLan) ->
      nativeListInReConcat xs r s = true ↔
        ∃ xs₁ xs₂ : List native_Char,
          xs₁ ++ xs₂ = xs ∧
            nativeListInRe xs₁ r = true ∧
            nativeListInRe xs₂ s = true
  | [], r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.and_eq_true] at h
        exact ⟨[], [], by rfl, by simpa [nativeListInRe] using h.1,
          by simpa [nativeListInRe] using h.2⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp [nativeListInReConcat, nativeListInRe] at hLeft hRight ⊢
                simp [hLeft, hRight]
            | cons _ _ =>
                simp at hAppend
        | cons _ _ =>
            simp at hAppend
  | c :: cs, r, s => by
      constructor
      · intro h
        simp [nativeListInReConcat, Bool.or_eq_true, Bool.and_eq_true] at h
        rcases h with hHead | hTail
        · exact ⟨[], c :: cs, by rfl,
            by simpa [nativeListInRe] using hHead.1, hHead.2⟩
        · have hTailExists :=
            (nativeListInReConcat_true_iff_exists_append cs
              (native_re_deriv c r) s).1 hTail
          rcases hTailExists with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
          exact ⟨c :: xs₁, xs₂, by simp [hAppend],
            by simpa [nativeListInRe] using hLeft, hRight⟩
      · intro h
        rcases h with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        cases xs₁ with
        | nil =>
            cases xs₂ with
            | nil =>
                simp at hAppend
            | cons _ _ =>
                cases hAppend
                have hNullable : native_re_nullable r = true := by
                  simpa [nativeListInRe] using hLeft
                simp [nativeListInReConcat, Bool.or_eq_true,
                  Bool.and_eq_true, hNullable, hRight]
        | cons _ ds =>
            cases hAppend
            have hLeftDeriv :
                nativeListInRe ds (native_re_deriv c r) = true := by
              simpa [nativeListInRe] using hLeft
            have hTail :
                nativeListInReConcat (ds ++ xs₂) (native_re_deriv c r) s =
                  true :=
              (nativeListInReConcat_true_iff_exists_append (ds ++ xs₂)
                (native_re_deriv c r) s).2
                ⟨ds, xs₂, by rfl, hLeftDeriv, hRight⟩
            simp [nativeListInReConcat, Bool.or_eq_true, hTail]

private theorem nativeListInRe_mk_concat_true_iff_exists_append
    (xs : List native_Char) (r s : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List native_Char,
        xs₁ ++ xs₂ = xs ∧
          nativeListInRe xs₁ r = true ∧
          nativeListInRe xs₂ s = true := by
  rw [nativeListInRe_mk_concat xs r s]
  exact nativeListInReConcat_true_iff_exists_append xs r s

private theorem native_str_in_re_mk_union
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_mk_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_mk_union str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

private theorem native_str_in_re_mk_inter
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_mk_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_mk_inter str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

private theorem native_str_in_re_union_true
    {str : native_String} {r s : native_RegLan}
    (h : native_str_in_re str (native_re_union r s) = true) :
    native_str_in_re str r = true ∨ native_str_in_re str s = true := by
  rw [native_re_union, native_str_in_re_mk_union] at h
  simpa [Bool.or_eq_true] using h

private theorem native_str_in_re_inter_true
    {str : native_String} {r s : native_RegLan}
    (h : native_str_in_re str (native_re_inter r s) = true) :
    native_str_in_re str r = true ∧ native_str_in_re str s = true := by
  rw [native_re_inter, native_str_in_re_mk_inter] at h
  simpa [Bool.and_eq_true] using h

private theorem native_string_valid_of_str_in_re_true
    {str : native_String} {r : native_RegLan}
    (h : native_str_in_re str r = true) :
    native_string_valid str = true := by
  by_cases hValid : native_string_valid str = true
  · exact hValid
  · have hInvalid : native_string_valid str = false := by
      cases hv : native_string_valid str <;> simp [hv] at hValid ⊢
    simp [native_str_in_re, hInvalid] at h

private theorem nativeListInRe_of_str_in_re_true
    {str : native_String} {r : native_RegLan}
    (h : native_str_in_re str r = true) :
    nativeListInRe str r = true := by
  have hValid := native_string_valid_of_str_in_re_true h
  simpa [native_str_in_re, hValid, nativeListInRe] using h

private theorem native_str_in_re_true_of_valid_list
    {str : native_String} {r : native_RegLan}
    (hValid : native_string_valid str = true)
    (hList : nativeListInRe str r = true) :
    native_str_in_re str r = true := by
  simpa [native_str_in_re, hValid, nativeListInRe] using hList

private theorem native_string_valid_left_of_append_valid
    {xs ys : native_String}
    (hValid : native_string_valid (xs ++ ys) = true) :
    native_string_valid xs = true := by
  simp [native_string_valid] at hValid
  simpa [native_string_valid] using hValid.1

private theorem native_string_valid_right_of_append_valid
    {xs ys : native_String}
    (hValid : native_string_valid (xs ++ ys) = true) :
    native_string_valid ys = true := by
  simp [native_string_valid] at hValid
  simpa [native_string_valid] using hValid.2

private theorem native_str_in_re_concat_true
    {str : native_String} {r s : native_RegLan}
    (h : native_str_in_re str (native_re_concat r s) = true) :
    ∃ xs ys : native_String,
      xs ++ ys = str ∧
        native_str_in_re xs r = true ∧
        native_str_in_re ys s = true := by
  have hValid := native_string_valid_of_str_in_re_true h
  have hList :
      nativeListInRe str (native_re_mk_concat r s) = true := by
    simpa [native_re_concat] using nativeListInRe_of_str_in_re_true h
  rcases (nativeListInRe_mk_concat_true_iff_exists_append str r s).1 hList with
    ⟨xs, ys, hAppend, hLeft, hRight⟩
  have hAppendValid : native_string_valid (xs ++ ys) = true := by
    rw [hAppend]
    exact hValid
  have hXsValid := native_string_valid_left_of_append_valid hAppendValid
  have hYsValid := native_string_valid_right_of_append_valid hAppendValid
  exact ⟨xs, ys, hAppend,
    native_str_in_re_true_of_valid_list hXsValid hLeft,
    native_str_in_re_true_of_valid_list hYsValid hRight⟩

private theorem native_str_in_re_empty_false (str : native_String) :
    native_str_in_re str SmtRegLan.empty = false := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_empty str
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

private theorem native_re_nullable_fold_empty_false (xs : List native_Char) :
    native_re_nullable
        (xs.foldl (fun acc c => native_re_deriv c acc) SmtRegLan.empty) =
      false := by
  simpa [nativeListInRe] using nativeListInRe_empty xs

private theorem native_str_in_re_epsilon_length
    {str : native_String}
    (h : native_str_in_re str SmtRegLan.epsilon = true) :
    str.length = 0 := by
  cases str with
  | nil =>
      rfl
  | cons c cs =>
      simp [native_str_in_re, nativeListInRe, native_re_deriv,
        native_re_nullable, native_re_nullable_fold_empty_false] at h

private theorem native_str_in_re_char_length
    {str : native_String} {c : native_Char}
    (h : native_str_in_re str (SmtRegLan.char c) = true) :
    str.length = 1 := by
  cases str with
  | nil =>
      simp [native_str_in_re, nativeListInRe, native_re_nullable] at h
  | cons d ds =>
      cases ds with
      | nil =>
          rfl
      | cons e es =>
          by_cases hMatch :
              (native_char_valid d = true ∧ native_char_valid c = true) ∧
                d = c
          · simp [native_str_in_re, nativeListInRe, native_re_deriv,
              native_re_nullable, native_re_nullable_fold_empty_false,
              hMatch] at h
          · simp [native_str_in_re, nativeListInRe, native_re_deriv,
              native_re_nullable, native_re_nullable_fold_empty_false,
              hMatch] at h

private theorem native_str_in_re_range_atom_length
    {str : native_String} {lo hi : native_Char}
    (h : native_str_in_re str (SmtRegLan.range lo hi) = true) :
    str.length = 1 := by
  cases str with
  | nil =>
      simp [native_str_in_re, nativeListInRe, native_re_nullable] at h
  | cons d ds =>
      cases ds with
      | nil =>
          rfl
      | cons e es =>
          by_cases hMatch :
              (((native_char_valid d = true ∧ native_char_valid lo = true) ∧
                    native_char_valid hi = true) ∧ lo ≤ d) ∧ d ≤ hi
          · simp [native_str_in_re, nativeListInRe, native_re_deriv,
              native_re_nullable, native_re_nullable_fold_empty_false,
              hMatch] at h
          · simp [native_str_in_re, nativeListInRe, native_re_deriv,
              native_re_nullable, native_re_nullable_fold_empty_false,
              hMatch] at h

private theorem native_str_in_re_allchar_length
    {str : native_String}
    (h : native_str_in_re str native_re_allchar = true) :
    str.length = 1 := by
  cases str with
  | nil =>
      simp [native_str_in_re, nativeListInRe, native_re_allchar,
        native_re_nullable] at h
  | cons d ds =>
      cases ds with
      | nil =>
          rfl
      | cons e es =>
          by_cases hValidD : native_char_valid d = true
          · simp [native_str_in_re, nativeListInRe, native_re_allchar,
              native_re_deriv, native_re_nullable,
              native_re_nullable_fold_empty_false, hValidD] at h
          · simp [native_str_in_re, nativeListInRe, native_re_allchar,
              native_re_deriv, native_re_nullable,
              native_re_nullable_fold_empty_false, hValidD] at h

private theorem native_str_in_re_range_length
    {str lo hi : native_String}
    (h : native_str_in_re str (native_re_range lo hi) = true) :
    str.length = 1 := by
  cases lo with
  | nil =>
      simp [native_re_range, native_str_in_re_empty_false] at h
  | cons lo0 los =>
      cases los with
      | nil =>
          cases hi with
          | nil =>
              simp [native_re_range, native_str_in_re_empty_false] at h
          | cons hi0 his =>
              cases his with
              | nil =>
                  exact native_str_in_re_range_atom_length h
              | cons _ _ =>
                  simp [native_re_range, native_str_in_re_empty_false] at h
      | cons _ _ =>
          simp [native_re_range, native_str_in_re_empty_false] at h

private theorem native_str_in_re_re_of_list_length :
    (pat : native_String) -> {str : native_String} ->
      native_str_in_re str (native_re_of_list pat) = true ->
      str.length = pat.length
  | [], str, h => by
      exact native_str_in_re_epsilon_length h
  | c :: cs, str, h => by
      rcases native_str_in_re_concat_true
          (r := SmtRegLan.char c) (s := native_re_of_list cs)
          (by simpa [native_re_concat, native_re_of_list] using h) with
        ⟨s1, s2, hAppend, hLeft, hRight⟩
      have hLeftLen := native_str_in_re_char_length hLeft
      have hRightLen := native_str_in_re_re_of_list_length cs hRight
      rw [← hAppend]
      simp [hLeftLen, hRightLen]
      omega

private theorem native_str_in_re_str_to_re_length
    {str pat : native_String}
    (h : native_str_in_re str (native_str_to_re pat) = true) :
    str.length = pat.length := by
  simpa [native_str_to_re] using native_str_in_re_re_of_list_length pat h

private theorem model_eval_re_concat_reglan
    (M : SmtModel) (t1 t2 : SmtTerm) {rr : native_RegLan}
    (h :
      __smtx_model_eval M (SmtTerm.re_concat t1 t2) =
        SmtValue.RegLan rr) :
    ∃ r1 r2 : native_RegLan,
      __smtx_model_eval M t1 = SmtValue.RegLan r1 ∧
        __smtx_model_eval M t2 = SmtValue.RegLan r2 ∧
        rr = native_re_concat r1 r2 := by
  cases h1 : __smtx_model_eval M t1 <;>
    cases h2 : __smtx_model_eval M t2 <;>
    simp [__smtx_model_eval, __smtx_model_eval_re_concat, h1, h2] at h
  case RegLan.RegLan r1 r2 =>
    cases h
    exact ⟨r1, r2, rfl, rfl, rfl⟩

private theorem model_eval_re_union_reglan
    (M : SmtModel) (t1 t2 : SmtTerm) {rr : native_RegLan}
    (h :
      __smtx_model_eval M (SmtTerm.re_union t1 t2) =
        SmtValue.RegLan rr) :
    ∃ r1 r2 : native_RegLan,
      __smtx_model_eval M t1 = SmtValue.RegLan r1 ∧
        __smtx_model_eval M t2 = SmtValue.RegLan r2 ∧
        rr = native_re_union r1 r2 := by
  cases h1 : __smtx_model_eval M t1 <;>
    cases h2 : __smtx_model_eval M t2 <;>
    simp [__smtx_model_eval, __smtx_model_eval_re_union, h1, h2] at h
  case RegLan.RegLan r1 r2 =>
    cases h
    exact ⟨r1, r2, rfl, rfl, rfl⟩

private theorem model_eval_re_inter_reglan
    (M : SmtModel) (t1 t2 : SmtTerm) {rr : native_RegLan}
    (h :
      __smtx_model_eval M (SmtTerm.re_inter t1 t2) =
        SmtValue.RegLan rr) :
    ∃ r1 r2 : native_RegLan,
      __smtx_model_eval M t1 = SmtValue.RegLan r1 ∧
        __smtx_model_eval M t2 = SmtValue.RegLan r2 ∧
        rr = native_re_inter r1 r2 := by
  cases h1 : __smtx_model_eval M t1 <;>
    cases h2 : __smtx_model_eval M t2 <;>
    simp [__smtx_model_eval, __smtx_model_eval_re_inter, h1, h2] at h
  case RegLan.RegLan r1 r2 =>
    cases h
    exact ⟨r1, r2, rfl, rfl, rfl⟩

private theorem model_eval_re_range_reglan
    (M : SmtModel) (t1 t2 : SmtTerm) {rr : native_RegLan}
    (h :
      __smtx_model_eval M (SmtTerm.re_range t1 t2) =
        SmtValue.RegLan rr) :
    ∃ s1 s2 : SmtSeq,
      __smtx_model_eval M t1 = SmtValue.Seq s1 ∧
        __smtx_model_eval M t2 = SmtValue.Seq s2 ∧
        rr = native_re_range (native_unpack_string s1) (native_unpack_string s2) := by
  cases h1 : __smtx_model_eval M t1 <;>
    cases h2 : __smtx_model_eval M t2 <;>
    simp [__smtx_model_eval, __smtx_model_eval_re_range, h1, h2] at h
  case Seq.Seq s1 s2 =>
    cases h
    exact ⟨s1, s2, rfl, rfl, rfl⟩

private theorem model_eval_str_to_re_reglan
    (M : SmtModel) (t : SmtTerm) {rr : native_RegLan}
    (h :
      __smtx_model_eval M (SmtTerm.str_to_re t) =
        SmtValue.RegLan rr) :
    ∃ s : SmtSeq,
      __smtx_model_eval M t = SmtValue.Seq s ∧
        rr = native_str_to_re (native_unpack_string s) := by
  cases hs : __smtx_model_eval M t <;>
    simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hs] at h
  case Seq s =>
    cases h
    exact ⟨s, rfl, rfl⟩

private theorem eo_add_numeral_or_stuck
    (a b : Term)
    (ha : (∃ n : native_Int, a = Term.Numeral n) ∨ a = Term.Stuck)
    (hb : (∃ n : native_Int, b = Term.Numeral n) ∨ b = Term.Stuck) :
    (∃ n : native_Int, __eo_add a b = Term.Numeral n) ∨
      __eo_add a b = Term.Stuck := by
  rcases ha with ⟨n0, rfl⟩ | rfl
  · rcases hb with ⟨n1, rfl⟩ | rfl
    · left
      exact ⟨native_zplus n0 n1, rfl⟩
    · right
      rfl
  · right
    rfl

private theorem eo_requires_same_numeral_or_stuck
    (a b : Term)
    (ha : (∃ n : native_Int, a = Term.Numeral n) ∨ a = Term.Stuck)
    (hb : (∃ n : native_Int, b = Term.Numeral n) ∨ b = Term.Stuck) :
    (∃ n : native_Int, __eo_requires a b b = Term.Numeral n) ∨
      __eo_requires a b b = Term.Stuck := by
  rcases hb with ⟨nb, rfl⟩ | rfl
  · rcases ha with ⟨na, rfl⟩ | rfl
    · by_cases hEq : na = nb
      · subst na
        left
        exact ⟨nb, by
          simp [__eo_requires, native_teq, native_ite, native_not]⟩
      · right
        simp [__eo_requires, native_teq, native_ite, native_not, hEq]
    · right
      simp [__eo_requires, native_teq, native_ite, native_not]
  · right
    cases a <;> simp [__eo_requires, native_teq, native_ite, native_not]

private theorem eo_ite_numeral_or_stuck
    (c a b : Term)
    (ha : (∃ n : native_Int, a = Term.Numeral n) ∨ a = Term.Stuck)
    (hb : (∃ n : native_Int, b = Term.Numeral n) ∨ b = Term.Stuck) :
    (∃ n : native_Int, __eo_ite c a b = Term.Numeral n) ∨
      __eo_ite c a b = Term.Stuck := by
  unfold __eo_ite
  cases hTrue : native_teq c (Term.Boolean true)
  · cases hFalse : native_teq c (Term.Boolean false)
    · right
      simp [native_ite, hTrue, hFalse]
    · simpa [native_ite, hTrue, hFalse] using hb
  · simpa [native_ite, hTrue] using ha

private theorem eo_requires_stuck_stuck (a : Term) :
    __eo_requires a Term.Stuck Term.Stuck = Term.Stuck := by
  cases a <;> simp [__eo_requires, native_teq, native_ite, native_not]

private theorem eo_ite_stuck_stuck (c : Term) :
    __eo_ite c Term.Stuck Term.Stuck = Term.Stuck := by
  unfold __eo_ite
  cases native_teq c (Term.Boolean true) <;>
    cases native_teq c (Term.Boolean false) <;>
    simp [native_ite]

private theorem str_fixed_len_re_numeral_or_stuck :
    (r : Term) ->
      (∃ n : native_Int, __str_fixed_len_re r = Term.Numeral n) ∨
        __str_fixed_len_re r = Term.Stuck
  | Term.UOp op => by
      cases op <;> simp [__str_fixed_len_re]
  | Term.UOp1 _ _ => by right; rfl
  | Term.UOp2 _ _ _ => by right; rfl
  | Term.UOp3 _ _ _ _ => by right; rfl
  | Term.__eo_List => by right; rfl
  | Term.__eo_List_nil => by right; rfl
  | Term.__eo_List_cons => by right; rfl
  | Term.Bool => by right; rfl
  | Term.Boolean _ => by right; rfl
  | Term.Numeral _ => by right; rfl
  | Term.Rational _ => by right; rfl
  | Term.String _ => by right; rfl
  | Term.Binary _ _ => by right; rfl
  | Term.Type => by right; rfl
  | Term.Stuck => by right; rfl
  | Term.Apply f x => by
      cases f
      case UOp op =>
        cases op <;> simp [__str_fixed_len_re, __eo_len]
        case str_to_re =>
          cases x <;> simp [__str_fixed_len_re, __eo_len]
      case Apply g y =>
        cases g
        case UOp op =>
          cases op <;> simp [__str_fixed_len_re]
          case re_concat =>
            exact eo_add_numeral_or_stuck
              (__str_fixed_len_re y) (__str_fixed_len_re x)
              (str_fixed_len_re_numeral_or_stuck y)
              (str_fixed_len_re_numeral_or_stuck x)
          case re_union =>
            exact eo_ite_numeral_or_stuck
              (__eo_eq x (Term.UOp UserOp.re_none))
              (__str_fixed_len_re y)
              (__eo_requires (__str_fixed_len_re x) (__str_fixed_len_re y)
                (__str_fixed_len_re y))
              (str_fixed_len_re_numeral_or_stuck y)
              (eo_requires_same_numeral_or_stuck
                (__str_fixed_len_re x) (__str_fixed_len_re y)
                (str_fixed_len_re_numeral_or_stuck x)
                (str_fixed_len_re_numeral_or_stuck y))
          case re_inter =>
            exact eo_ite_numeral_or_stuck
              (__eo_eq x (Term.UOp UserOp.re_all))
              (__str_fixed_len_re y)
              (__eo_requires (__str_fixed_len_re x) (__str_fixed_len_re y)
                (__str_fixed_len_re y))
              (str_fixed_len_re_numeral_or_stuck y)
              (eo_requires_same_numeral_or_stuck
                (__str_fixed_len_re x) (__str_fixed_len_re y)
                (str_fixed_len_re_numeral_or_stuck x)
                (str_fixed_len_re_numeral_or_stuck y))
        all_goals
          right
          rfl
      all_goals
        right
        rfl
  | Term.FunType => by right; rfl
  | Term.Var _ _ => by right; rfl
  | Term.DatatypeType _ _ => by right; rfl
  | Term.DatatypeTypeRef _ => by right; rfl
  | Term.DtcAppType _ _ => by right; rfl
  | Term.DtCons _ _ _ => by right; rfl
  | Term.DtSel _ _ _ _ => by right; rfl
  | Term.USort _ => by right; rfl
  | Term.UConst _ _ => by right; rfl
termination_by r => sizeOf r

private theorem str_fixed_len_re_numeral_of_ne_stuck
    (r : Term)
    (h : __str_fixed_len_re r ≠ Term.Stuck) :
    ∃ n : native_Int, __str_fixed_len_re r = Term.Numeral n := by
  rcases str_fixed_len_re_numeral_or_stuck r with hNum | hStuck
  · exact hNum
  · exact False.elim (h hStuck)

private theorem str_fixed_len_re_sound (M : SmtModel) :
    (r : Term) -> (str : native_String) -> (rr : native_RegLan) ->
      (n : native_Int) ->
      __str_fixed_len_re r = Term.Numeral n ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rr ->
      native_str_in_re str rr = true ->
      Int.ofNat str.length = n
  | Term.UOp op, str, rr, n, hFixed, hEval, hIn => by
      cases op <;> simp [__str_fixed_len_re] at hFixed
      case re_allchar =>
        cases hFixed
        simp [__smtx_model_eval] at hEval
        cases hEval
        have hLen := native_str_in_re_allchar_length hIn
        simpa [hLen]
  | Term.UOp1 _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.UOp2 _ _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.UOp3 _ _ _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.__eo_List, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.__eo_List_nil, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.__eo_List_cons, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Bool, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Boolean _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Numeral _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Rational _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.String _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Binary _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Type, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Stuck, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Apply f x, str, rr, n, hFixed, hEval, hIn => by
      cases f
      case UOp op =>
        cases op <;> simp [__str_fixed_len_re, __eo_len] at hFixed
        case str_to_re =>
          cases x <;> simp [__str_fixed_len_re, __eo_len] at hFixed
          case String pat =>
            cases hFixed
            change
              __smtx_model_eval M
                  (SmtTerm.str_to_re (SmtTerm.String pat)) =
                SmtValue.RegLan rr at hEval
            simp [__smtx_model_eval, __smtx_model_eval_str_to_re,
              native_unpack_pack_string] at hEval
            cases hEval
            have hLen := native_str_in_re_str_to_re_length hIn
            simpa [native_str_len, hLen]
          case Binary =>
            cases hFixed
            change
              __smtx_model_eval M
                  (SmtTerm.str_to_re (SmtTerm.Binary _ _)) =
                SmtValue.RegLan rr at hEval
            simp [__smtx_model_eval, __smtx_model_eval_str_to_re] at hEval
      case Apply g y =>
        cases g
        case UOp op =>
          cases op <;> simp [__str_fixed_len_re] at hFixed
          case re_concat =>
            rcases str_fixed_len_re_numeral_or_stuck y with
              ⟨n0, h0⟩ | h0
            · rcases str_fixed_len_re_numeral_or_stuck x with
                ⟨n1, h1⟩ | h1
              · have hSum : native_zplus n0 n1 = n := by
                  simpa [__str_fixed_len_re, h0, h1, __eo_add] using hFixed
                rcases model_eval_re_concat_reglan M (__eo_to_smt y)
                    (__eo_to_smt x) hEval with
                  ⟨rr0, rr1, hEval0, hEval1, rfl⟩
                rcases native_str_in_re_concat_true hIn with
                  ⟨s0, s1, hAppend, hIn0, hIn1⟩
                have hLen0 :=
                  str_fixed_len_re_sound M y s0 rr0 n0 h0 hEval0 hIn0
                have hLen1 :=
                  str_fixed_len_re_sound M x s1 rr1 n1 h1 hEval1 hIn1
                rw [← hAppend]
                calc
                  Int.ofNat (s0 ++ s1).length =
                      Int.ofNat s0.length + Int.ofNat s1.length := by simp
                  _ = n0 + n1 := by rw [hLen0, hLen1]
                  _ = n := by simpa [native_zplus] using hSum
              · simp [__str_fixed_len_re, h0, h1, __eo_add] at hFixed
            · simp [__str_fixed_len_re, h0, __eo_add] at hFixed
          case re_range =>
            cases hFixed
            rcases model_eval_re_range_reglan M (__eo_to_smt y)
                (__eo_to_smt x) hEval with
              ⟨_slo, _shi, _hLoEval, _hHiEval, rfl⟩
            have hLen := native_str_in_re_range_length hIn
            simpa [hLen]
          case re_union =>
            rcases str_fixed_len_re_numeral_or_stuck y with
              ⟨n0, h0⟩ | h0
            ·
              by_cases hNone : (x = Term.UOp UserOp.re_none)
              · subst x
                have hn : n0 = n := by
                  simpa [__str_fixed_len_re, h0, __eo_eq, __eo_ite,
                    native_teq, native_ite] using hFixed
                subst n
                rcases model_eval_re_union_reglan M (__eo_to_smt y)
                    SmtTerm.re_none hEval with
                  ⟨rr0, rr1, hEval0, hEval1, hRr⟩
                have hR1 : rr1 = native_re_none := by
                  simpa [__smtx_model_eval, native_re_none] using hEval1.symm
                subst rr1
                rw [hRr] at hIn
                rcases native_str_in_re_union_true hIn with hIn0 | hIn1
                · exact str_fixed_len_re_sound M y str rr0 n0 h0 hEval0 hIn0
                · rw [native_re_none, native_str_in_re_empty_false] at hIn1
                  cases hIn1
              ·
                by_cases hStuck : x = Term.Stuck
                · subst x
                  simp [__str_fixed_len_re, h0, __eo_eq, __eo_ite,
                    native_teq, native_ite] at hFixed
                · have hNone' : ¬ Term.UOp UserOp.re_none = x := by
                    intro h
                    exact hNone h.symm
                  rcases str_fixed_len_re_numeral_or_stuck x with
                    ⟨n1, h1⟩ | h1
                  ·
                    by_cases hLenEq : n1 = n0
                    · subst n1
                      have hn : n0 = n := by
                        simpa [__str_fixed_len_re, h0, h1, __eo_eq,
                          __eo_ite, __eo_requires, native_teq, native_ite,
                          native_not, hNone, hNone', hStuck] using hFixed
                      subst n
                      rcases model_eval_re_union_reglan M (__eo_to_smt y)
                          (__eo_to_smt x) hEval with
                        ⟨rr0, rr1, hEval0, hEval1, rfl⟩
                      rcases native_str_in_re_union_true hIn with hIn0 | hIn1
                      · exact str_fixed_len_re_sound M y str rr0 n0 h0 hEval0 hIn0
                      · exact str_fixed_len_re_sound M x str rr1 n0 h1 hEval1 hIn1
                    · simp [__str_fixed_len_re, h0, h1, __eo_eq, __eo_ite,
                        __eo_requires, native_teq, native_ite, native_not,
                        hNone, hNone', hStuck, hLenEq] at hFixed
                  · simp [__str_fixed_len_re, h0, h1, __eo_eq, __eo_ite,
                      __eo_requires, native_teq, native_ite, native_not,
                      hNone, hNone', hStuck] at hFixed
            · simp [h0, eo_requires_stuck_stuck, eo_ite_stuck_stuck] at hFixed
          case re_inter =>
            rcases str_fixed_len_re_numeral_or_stuck y with
              ⟨n0, h0⟩ | h0
            ·
              by_cases hAll : (x = Term.UOp UserOp.re_all)
              · subst x
                have hn : n0 = n := by
                  simpa [__str_fixed_len_re, h0, __eo_eq, __eo_ite,
                    native_teq, native_ite] using hFixed
                subst n
                rcases model_eval_re_inter_reglan M (__eo_to_smt y)
                    SmtTerm.re_all hEval with
                  ⟨rr0, rr1, hEval0, hEval1, hRr⟩
                have hR1 : rr1 = native_re_all := by
                  simpa [__smtx_model_eval, native_re_all] using hEval1.symm
                subst rr1
                rw [hRr] at hIn
                have hIn0 := (native_str_in_re_inter_true hIn).1
                exact str_fixed_len_re_sound M y str rr0 n0 h0 hEval0 hIn0
              ·
                by_cases hStuck : x = Term.Stuck
                · subst x
                  simp [__str_fixed_len_re, h0, __eo_eq, __eo_ite,
                    native_teq, native_ite] at hFixed
                · have hAll' : ¬ Term.UOp UserOp.re_all = x := by
                    intro h
                    exact hAll h.symm
                  rcases str_fixed_len_re_numeral_or_stuck x with
                    ⟨n1, h1⟩ | h1
                  ·
                    by_cases hLenEq : n1 = n0
                    · subst n1
                      have hn : n0 = n := by
                        simpa [__str_fixed_len_re, h0, h1, __eo_eq,
                          __eo_ite, __eo_requires, native_teq, native_ite,
                          native_not, hAll, hAll', hStuck] using hFixed
                      subst n
                      rcases model_eval_re_inter_reglan M (__eo_to_smt y)
                          (__eo_to_smt x) hEval with
                        ⟨rr0, rr1, hEval0, _hEval1, rfl⟩
                      have hIn0 := (native_str_in_re_inter_true hIn).1
                      exact str_fixed_len_re_sound M y str rr0 n0 h0 hEval0 hIn0
                    · simp [__str_fixed_len_re, h0, h1, __eo_eq, __eo_ite,
                        __eo_requires, native_teq, native_ite, native_not,
                        hAll, hAll', hStuck, hLenEq] at hFixed
                  · simp [__str_fixed_len_re, h0, h1, __eo_eq, __eo_ite,
                      __eo_requires, native_teq, native_ite, native_not,
                      hAll, hAll', hStuck] at hFixed
            · simp [h0, eo_requires_stuck_stuck, eo_ite_stuck_stuck] at hFixed
        all_goals simp [__str_fixed_len_re] at hFixed
      all_goals simp [__str_fixed_len_re] at hFixed
  | Term.FunType, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.Var _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DatatypeType _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DatatypeTypeRef _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DtcAppType _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DtCons _ _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.DtSel _ _ _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.USort _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
  | Term.UConst _ _, _str, _rr, _n, hFixed, _hEval, _hIn => by
      simp [__str_fixed_len_re] at hFixed
termination_by r _ _ _ _ _ _ => sizeOf r

private theorem string_eager_reduction_has_bool_type
    (a : Term)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hTy : __eo_typeof (__eo_prog_string_eager_reduction a) = Term.Bool) :
    RuleProofs.eo_has_bool_type (__eo_prog_string_eager_reduction a) := by
  cases a <;> simp [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] at hTy ⊢
  all_goals try cases hTy
  case Apply f x =>
    cases f <;> try simp [__mk_str_eager_reduction] at hTy ⊢
    all_goals try cases hTy
    case UOp op =>
      cases op <;> try simp [__mk_str_eager_reduction] at hTy ⊢
      all_goals try cases hTy
      case str_to_code =>
        apply RuleProofs.eo_typeof_bool_implies_has_bool_type
        · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
          have hsTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
            seq_char_arg_of_non_none (op := SmtTerm.str_to_code)
              (typeof_str_to_code_eq (__eo_to_smt x))
              (by simpa [term_has_non_none_type] using hATrans)
          change
            __smtx_typeof
              (SmtTerm.ite
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x)) (SmtTerm.Numeral 1))
                (SmtTerm.and
                  (SmtTerm.geq (SmtTerm.str_to_code (__eo_to_smt x)) (SmtTerm.Numeral 0))
                  (SmtTerm.and
                    (SmtTerm.lt (SmtTerm.str_to_code (__eo_to_smt x))
                      (SmtTerm.Numeral 196608))
                    (SmtTerm.Boolean true)))
                (SmtTerm.eq (SmtTerm.str_to_code (__eo_to_smt x))
                  (SmtTerm.Numeral (-1 : native_Int)))) ≠ SmtType.None
          simp [typeof_ite_eq, typeof_eq_eq, typeof_str_len_eq,
            typeof_str_to_code_eq, typeof_geq_eq, typeof_lt_eq, typeof_and_eq,
            hsTy, __smtx_typeof_seq_op_1_ret, __smtx_typeof_arith_overload_op_2_ret,
            __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof_ite,
            __smtx_typeof, native_ite, native_Teq]
        · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
      case str_from_code =>
        apply RuleProofs.eo_typeof_bool_implies_has_bool_type
        · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
          have hnTy : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
            int_arg_of_non_none_ret (op := SmtTerm.str_from_code)
              (typeof_str_from_code_eq (__eo_to_smt x))
              (by simpa [term_has_non_none_type] using hATrans)
          change
            __smtx_typeof
              (SmtTerm.ite
                (SmtTerm.and (SmtTerm.leq (SmtTerm.Numeral 0) (__eo_to_smt x))
                  (SmtTerm.and (SmtTerm.lt (__eo_to_smt x) (SmtTerm.Numeral 196608))
                    (SmtTerm.Boolean true)))
                (SmtTerm.eq (__eo_to_smt x)
                  (SmtTerm.str_to_code
                    (SmtTerm._at_purify (SmtTerm.str_from_code (__eo_to_smt x)))))
                (SmtTerm.eq
                  (SmtTerm._at_purify (SmtTerm.str_from_code (__eo_to_smt x)))
                  (SmtTerm.String []))) ≠ SmtType.None
          simp [typeof_ite_eq, typeof_eq_eq, typeof_leq_eq, typeof_lt_eq,
            typeof_and_eq, typeof_str_from_code_eq, typeof_str_to_code_eq,
            hnTy, __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
            __smtx_typeof_guard, __smtx_typeof_ite, __smtx_typeof,
            native_ite, native_Teq, native_string_valid]
        · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
      case str_to_int =>
        apply RuleProofs.eo_typeof_bool_implies_has_bool_type
        · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
          have hsTy :
              __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
            seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
              (typeof_str_to_int_eq (__eo_to_smt x))
              (by simpa [term_has_non_none_type] using hATrans)
          change
            __smtx_typeof
                (SmtTerm.geq (SmtTerm.str_to_int (__eo_to_smt x))
                  (SmtTerm.Numeral (-1 : native_Int))) ≠ SmtType.None
          rw [typeof_geq_eq, typeof_str_to_int_eq]
          rw [__smtx_typeof.eq_2]
          simp [hsTy, __smtx_typeof_arith_overload_op_2_ret, native_ite,
            native_Teq]
        · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
    case Apply f y =>
      cases f <;> try simp [__mk_str_eager_reduction] at hTy ⊢
      all_goals try cases hTy
      case UOp op =>
        cases op <;> try simp [__mk_str_eager_reduction] at hTy ⊢
        all_goals try cases hTy
        case str_contains =>
          apply RuleProofs.eo_typeof_bool_implies_has_bool_type
          · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
            rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
                (R := SmtType.Bool)
                (typeof_str_contains_eq (__eo_to_smt y) (__eo_to_smt x))
                (by simpa [term_has_non_none_type] using hATrans) with
              ⟨T, hyTy, hxTy⟩
            let pre :=
              Term.UOp1 UserOp1._at_purify
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_substr) y)
                    (Term.Numeral 0))
                  (Term.Apply
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp.str_indexof) y) x)
                    (Term.Numeral 0)))
            have hPreTy :
                __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
              change
                __smtx_typeof
                  (SmtTerm._at_purify
                    (SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0)
                      (SmtTerm.str_indexof (__eo_to_smt y) (__eo_to_smt x)
                        (SmtTerm.Numeral 0)))) = SmtType.Seq T
              simp [__smtx_typeof, typeof_str_substr_eq, typeof_str_indexof_eq,
                hyTy, hxTy, __smtx_typeof_str_indexof, __smtx_typeof_str_substr,
                __smtx_typeof_arith_overload_op_2, native_ite, native_Teq]
            have hNilNe :
                __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre) ≠
                  Term.Stuck := by
              exact nil_str_concat_typeof_ne_stuck_of_smt_type_seq pre T hPreTy
            have hNilNe' :
                __eo_nil (Term.UOp UserOp.str_concat)
                    (__eo_typeof
                      (Term.UOp1 UserOp1._at_purify
                        (Term.Apply
                          (Term.Apply
                            (Term.Apply (Term.UOp UserOp.str_substr) y)
                            (Term.Numeral 0))
                          (Term.Apply
                            (Term.Apply
                              (Term.Apply (Term.UOp UserOp.str_indexof) y) x)
                            (Term.Numeral 0))))) ≠
                  Term.Stuck := by
              simpa [pre] using hNilNe
            have hNilTy' :
                __smtx_typeof
                    (__eo_to_smt
                      (__eo_nil (Term.UOp UserOp.str_concat)
                        (__eo_typeof
                          (Term.UOp1 UserOp1._at_purify
                            (Term.Apply
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp.str_substr) y)
                                (Term.Numeral 0))
                              (Term.Apply
                                (Term.Apply
                                  (Term.Apply (Term.UOp UserOp.str_indexof) y) x)
                                (Term.Numeral 0))))))) =
                  SmtType.Seq T := by
              simpa [pre] using
                smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPreTy
            simp only [__eo_mk_apply, hNilNe']
            change
              __smtx_typeof
                (SmtTerm.ite
                  (SmtTerm.str_contains (__eo_to_smt y) (__eo_to_smt x))
                  (SmtTerm.eq (__eo_to_smt y)
                    (SmtTerm.str_concat
                      (SmtTerm._at_purify
                        (SmtTerm.str_substr (__eo_to_smt y) (SmtTerm.Numeral 0)
                          (SmtTerm.str_indexof (__eo_to_smt y) (__eo_to_smt x)
                            (SmtTerm.Numeral 0))))
                      (SmtTerm.str_concat (__eo_to_smt x)
                        (SmtTerm.str_concat
                          (SmtTerm._at_purify
                            (SmtTerm.str_substr (__eo_to_smt y)
                              (SmtTerm.plus
                                (SmtTerm.str_len
                                  (SmtTerm._at_purify
                                    (SmtTerm.str_substr (__eo_to_smt y)
                                      (SmtTerm.Numeral 0)
                                      (SmtTerm.str_indexof (__eo_to_smt y)
                                        (__eo_to_smt x) (SmtTerm.Numeral 0)))))
                                (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt x))
                                  (SmtTerm.Numeral 0)))
                              (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt y))
                                (SmtTerm.plus
                                  (SmtTerm.str_len
                                    (SmtTerm._at_purify
                                      (SmtTerm.str_substr (__eo_to_smt y)
                                        (SmtTerm.Numeral 0)
                                        (SmtTerm.str_indexof (__eo_to_smt y)
                                          (__eo_to_smt x) (SmtTerm.Numeral 0)))))
                                  (SmtTerm.plus (SmtTerm.str_len (__eo_to_smt x))
                                    (SmtTerm.Numeral 0))))))
                          (__eo_to_smt
                            (__eo_nil (Term.UOp UserOp.str_concat)
                              (__eo_typeof
                                (Term.UOp1 UserOp1._at_purify
                                  (Term.Apply
                                    (Term.Apply
                                      (Term.Apply (Term.UOp UserOp.str_substr) y)
                                      (Term.Numeral 0))
                                    (Term.Apply
                                      (Term.Apply
                                        (Term.Apply (Term.UOp UserOp.str_indexof) y)
                                        x)
                                      (Term.Numeral 0)))))))))))
                  (SmtTerm.not (SmtTerm.eq (__eo_to_smt y) (__eo_to_smt x)))) ≠
                SmtType.None
            simp [typeof_ite_eq, typeof_eq_eq,
              typeof_str_contains_eq,
              typeof_str_substr_eq, typeof_str_indexof_eq, typeof_str_len_eq,
              typeof_str_concat_eq, typeof_plus_eq, typeof_neg_eq, typeof_not_eq,
              hyTy, hxTy, __smtx_typeof_str_indexof,
              __smtx_typeof_str_substr,
              __smtx_typeof_seq_op_2, __smtx_typeof_seq_op_2_ret,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_arith_overload_op_2,
              __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof_ite,
              __smtx_typeof, native_ite, native_Teq, hNilTy']
          · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
        case str_in_re =>
          apply RuleProofs.eo_typeof_bool_implies_has_bool_type
          · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
            have hOrigNN :
                term_has_non_none_type
                  (SmtTerm.str_in_re (__eo_to_smt y) (__eo_to_smt x)) := by
              unfold term_has_non_none_type
              simpa using hATrans
            have hArgs :=
              seq_char_reglan_args_of_non_none
                (op := SmtTerm.str_in_re)
                (typeof_str_in_re_eq (__eo_to_smt y) (__eo_to_smt x))
                hOrigNN
            have hyTy : __smtx_typeof (__eo_to_smt y) =
                SmtType.Seq SmtType.Char := hArgs.1
            have hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
              hArgs.2
            let fixed := __str_fixed_len_re x
            let rhsEo :=
              __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply (Term.UOp UserOp.str_len) y))
                fixed
            let gen :=
              __eo_mk_apply
                (Term.Apply (Term.UOp UserOp.imp)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x))
                rhsEo
            have hGenTy : __eo_typeof gen = Term.Bool := by
              simpa [gen, rhsEo, fixed, __eo_prog_string_eager_reduction,
                __mk_str_eager_reduction] using hTy
            have hGenNe : gen ≠ Term.Stuck := by
              intro h
              rw [h] at hGenTy
              change Term.Stuck = Term.Bool at hGenTy
              cases hGenTy
            have hRhsNe : rhsEo ≠ Term.Stuck :=
              eo_mk_apply_arg_ne_stuck_of_ne_stuck
                (Term.Apply (Term.UOp UserOp.imp)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x))
                rhsEo hGenNe
            have hFixedNe : fixed ≠ Term.Stuck :=
              eo_mk_apply_arg_ne_stuck_of_ne_stuck
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply (Term.UOp UserOp.str_len) y))
                fixed hRhsNe
            rcases str_fixed_len_re_numeral_of_ne_stuck x hFixedNe with
              ⟨n, hFixed⟩
            simp only [rhsEo, gen, fixed, __eo_mk_apply, hFixed]
            change
              __smtx_typeof
                  (SmtTerm.imp
                    (SmtTerm.str_in_re (__eo_to_smt y) (__eo_to_smt x))
                    (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt y))
                      (SmtTerm.Numeral n))) ≠
                SmtType.None
            simp [typeof_imp_eq, typeof_str_in_re_eq, typeof_eq_eq,
              typeof_str_len_eq, hyTy, hxTy,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_eq,
              __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
          · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
      case Apply f z =>
        cases f <;> try simp [__mk_str_eager_reduction] at hTy ⊢
        all_goals try cases hTy
        case UOp op =>
          cases op <;> try simp [__mk_str_eager_reduction] at hTy ⊢
          all_goals try cases hTy
          case str_indexof =>
            apply RuleProofs.eo_typeof_bool_implies_has_bool_type
            · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
              rcases str_indexof_args_of_non_none
                  (by simpa [term_has_non_none_type] using hATrans) with
                ⟨T, hzTy, hyTy, hxTy⟩
              change
                __smtx_typeof
                  (SmtTerm.and
                    (SmtTerm.or
                      (SmtTerm.eq
                        (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y)
                          (__eo_to_smt x))
                        (SmtTerm.Numeral (-1 : native_Int)))
                      (SmtTerm.or
                        (SmtTerm.geq
                          (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y)
                            (__eo_to_smt x))
                          (__eo_to_smt x))
                        (SmtTerm.Boolean false)))
                    (SmtTerm.and
                      (SmtTerm.leq
                        (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y)
                          (__eo_to_smt x))
                        (SmtTerm.str_len (__eo_to_smt z)))
                      (SmtTerm.Boolean true))) ≠ SmtType.None
              simp [typeof_and_eq, typeof_or_eq, typeof_eq_eq, typeof_geq_eq,
                typeof_leq_eq, typeof_str_indexof_eq, typeof_str_len_eq,
                hzTy, hyTy, hxTy, __smtx_typeof_str_indexof,
                __smtx_typeof_seq_op_1_ret, __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_eq, __smtx_typeof_guard, __smtx_typeof,
                native_ite, native_Teq]
            · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy
          case str_indexof_re =>
            apply RuleProofs.eo_typeof_bool_implies_has_bool_type
            · unfold RuleProofs.eo_has_smt_translation at hATrans ⊢
              rcases str_indexof_re_args_of_non_none
                  (by simpa [term_has_non_none_type] using hATrans) with
                ⟨hzTy, hyTy, hxTy⟩
              change
                __smtx_typeof
                  (SmtTerm.and
                    (SmtTerm.or
                      (SmtTerm.eq
                        (SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y)
                          (__eo_to_smt x))
                        (SmtTerm.Numeral (-1 : native_Int)))
                      (SmtTerm.or
                        (SmtTerm.geq
                          (SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y)
                            (__eo_to_smt x))
                          (__eo_to_smt x))
                        (SmtTerm.Boolean false)))
                    (SmtTerm.and
                      (SmtTerm.leq
                        (SmtTerm.str_indexof_re (__eo_to_smt z) (__eo_to_smt y)
                          (__eo_to_smt x))
                        (SmtTerm.str_len (__eo_to_smt z)))
                      (SmtTerm.Boolean true))) ≠ SmtType.None
              simp [typeof_and_eq, typeof_or_eq, typeof_eq_eq, typeof_geq_eq,
                typeof_leq_eq, typeof_str_indexof_re_eq, typeof_str_len_eq,
                hzTy, hyTy, hxTy, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            · simpa [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] using hTy

private theorem string_eager_reduction_true
    (M : SmtModel) (hM : model_total_typed M)
    (a : Term)
    (hBool : RuleProofs.eo_has_bool_type (__eo_prog_string_eager_reduction a)) :
    eo_interprets M (__eo_prog_string_eager_reduction a) true := by
  cases a <;> simp [__eo_prog_string_eager_reduction, __mk_str_eager_reduction] at hBool ⊢
  all_goals try
    exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
  case Apply f x =>
    cases f <;> try simp [__mk_str_eager_reduction] at hBool ⊢
    all_goals try
      exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
    case UOp op =>
      cases op <;> try simp [__mk_str_eager_reduction] at hBool ⊢
      all_goals try
        exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
      case str_to_code =>
        let tx := __eo_to_smt x
        let code := SmtTerm.str_to_code tx
        let thenTerm :=
          SmtTerm.and (SmtTerm.geq code (SmtTerm.Numeral 0))
            (SmtTerm.and (SmtTerm.lt code (SmtTerm.Numeral 196608))
              (SmtTerm.Boolean true))
        let elseTerm := SmtTerm.eq code (SmtTerm.Numeral (-1 : native_Int))
        let cond := SmtTerm.eq (SmtTerm.str_len tx) (SmtTerm.Numeral 1)
        have hFormulaTy :
            __smtx_typeof (SmtTerm.ite cond thenTerm elseTerm) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type, tx, code, thenTerm, elseTerm, cond]
            using hBool
        have hFormulaNN : term_has_non_none_type (SmtTerm.ite cond thenTerm elseTerm) := by
          unfold term_has_non_none_type
          rw [hFormulaTy]
          simp
        rcases ite_args_of_non_none hFormulaNN with
          ⟨T, _hCondTy, hThenTy, _hElseTy, hTNN⟩
        have hThenNN : term_has_non_none_type thenTerm := by
          unfold term_has_non_none_type
          rw [hThenTy]
          exact hTNN
        have hGeqTy :
            __smtx_typeof (SmtTerm.geq code (SmtTerm.Numeral 0)) = SmtType.Bool :=
          (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
            (typeof_and_eq (SmtTerm.geq code (SmtTerm.Numeral 0))
              (SmtTerm.and (SmtTerm.lt code (SmtTerm.Numeral 196608))
                (SmtTerm.Boolean true))) hThenNN).1
        have hGeqNN : term_has_non_none_type
            (SmtTerm.geq code (SmtTerm.Numeral 0)) := by
          unfold term_has_non_none_type
          rw [hGeqTy]
          simp
        have hCodeTy : __smtx_typeof code = SmtType.Int := by
          rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
              (typeof_geq_eq code (SmtTerm.Numeral 0)) hGeqNN with
            hInt | hReal
          · exact hInt.1
          · have hNumTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
              rw [__smtx_typeof.eq_2]
            rw [hNumTy] at hReal
            cases hReal.2
        have hCodeNN : term_has_non_none_type code := by
          unfold term_has_non_none_type
          rw [hCodeTy]
          simp
        have hsTy : __smtx_typeof tx = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_code)
            (typeof_str_to_code_eq tx) hCodeNN
        rcases seq_eval_of_seq_type M hM x SmtType.Char (by simpa [tx] using hsTy) with
          ⟨ss, hSEval⟩
        have hEvalTy :
            __smtx_typeof_value (__smtx_model_eval M tx) = __smtx_typeof tx :=
          Smtm.smt_model_eval_preserves_type_of_non_none M hM tx
            (by simp [term_has_non_none_type, hsTy])
        have hSeqTy :
            __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
          simpa [tx, hSEval, hsTy] using hEvalTy
        have hValid :
            native_string_valid (native_unpack_string ss) = true :=
          native_unpack_string_valid_of_typeof_seq_char hSeqTy
        apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
        change __smtx_model_eval M (SmtTerm.ite cond thenTerm elseTerm) =
          SmtValue.Boolean true
        by_cases hLen : (native_unpack_seq ss).length = 1
        · have hLenString : (native_unpack_string ss).length = 1 := by
            simpa [native_unpack_string_length_eq ss] using hLen
          rcases native_str_to_code_singleton_bounds hValid hLenString with
            ⟨hLo, hHi⟩
          simp [tx, code, thenTerm, elseTerm, cond, __smtx_model_eval, hSEval,
            __smtx_model_eval_str_len, __smtx_model_eval_str_to_code,
            __smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, __smtx_model_eval_lt, __smtx_model_eval_and,
            native_seq_len, native_veq, native_zleq, native_zlt, native_and,
            hLen, hLo, hHi]
        · have hLenString : (native_unpack_string ss).length ≠ 1 := by
            intro h
            exact hLen (by simpa [native_unpack_string_length_eq ss] using h)
          have hCode : native_str_to_code (native_unpack_string ss) = -1 :=
            native_str_to_code_non_singleton (native_unpack_string ss) hLenString
          have hLenInt :
              (Int.ofNat (native_unpack_seq ss).length) ≠ (1 : Int) := by
            intro hEq
            exact hLen (Int.ofNat.inj hEq)
          have hCondFalse :
              (decide ((Int.ofNat (native_unpack_seq ss).length : Int) = 1)) = false := by
            exact decide_eq_false hLenInt
          simp [tx, code, thenTerm, elseTerm, cond, __smtx_model_eval, hSEval,
            __smtx_model_eval_str_len, __smtx_model_eval_str_to_code,
            __smtx_model_eval_ite, __smtx_model_eval_eq, __smtx_model_eval_geq,
            __smtx_model_eval_leq, __smtx_model_eval_lt, __smtx_model_eval_and,
            native_seq_len, native_veq, native_zleq, native_zlt, native_and,
            hLenInt, hCondFalse, hCode]
          cases hCond :
              decide ((Int.ofNat (native_unpack_seq ss).length : Int) = 1) with
          | false =>
              rfl
          | true =>
              exact False.elim (hLenInt (of_decide_eq_true hCond))
      case str_from_code =>
        let tx := __eo_to_smt x
        let strFrom := SmtTerm._at_purify (SmtTerm.str_from_code tx)
        let cond :=
          SmtTerm.and (SmtTerm.leq (SmtTerm.Numeral 0) tx)
            (SmtTerm.and (SmtTerm.lt tx (SmtTerm.Numeral 196608))
              (SmtTerm.Boolean true))
        let thenTerm := SmtTerm.eq tx (SmtTerm.str_to_code strFrom)
        let elseTerm := SmtTerm.eq strFrom (SmtTerm.String [])
        have hFormulaTy :
            __smtx_typeof (SmtTerm.ite cond thenTerm elseTerm) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type, tx, strFrom, cond, thenTerm, elseTerm]
            using hBool
        have hFormulaNN : term_has_non_none_type (SmtTerm.ite cond thenTerm elseTerm) := by
          unfold term_has_non_none_type
          rw [hFormulaTy]
          simp
        rcases ite_args_of_non_none hFormulaNN with
          ⟨T, hCondTy, _hThenTy, _hElseTy, _hTNN⟩
        have hCondNN : term_has_non_none_type cond := by
          unfold term_has_non_none_type
          rw [hCondTy]
          simp
        have hLeqTy :
            __smtx_typeof (SmtTerm.leq (SmtTerm.Numeral 0) tx) = SmtType.Bool :=
          (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
            (typeof_and_eq (SmtTerm.leq (SmtTerm.Numeral 0) tx)
              (SmtTerm.and (SmtTerm.lt tx (SmtTerm.Numeral 196608))
                (SmtTerm.Boolean true))) hCondNN).1
        have hLeqNN :
            term_has_non_none_type (SmtTerm.leq (SmtTerm.Numeral 0) tx) := by
          unfold term_has_non_none_type
          rw [hLeqTy]
          simp
        have hxTy : __smtx_typeof tx = SmtType.Int := by
          rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
              (typeof_leq_eq (SmtTerm.Numeral 0) tx) hLeqNN with
            hInt | hReal
          · exact hInt.2
          · have hNumTy : __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int := by
              rw [__smtx_typeof.eq_2]
            rw [hNumTy] at hReal
            cases hReal.1
        rcases int_eval_of_int_type M hM x (by simpa [tx] using hxTy) with
          ⟨z, hXEval⟩
        apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
        change __smtx_model_eval M (SmtTerm.ite cond thenTerm elseTerm) =
          SmtValue.Boolean true
        by_cases hz0 : 0 ≤ z
        ·
          by_cases hzHi : z < 196608
          · have hCode :
                native_str_to_code (native_str_from_code z) = z :=
              native_str_to_code_from_code_of_valid hz0 hzHi
            simp [tx, strFrom, cond, thenTerm, elseTerm, __smtx_model_eval, hXEval,
              __smtx_model_eval_ite, __smtx_model_eval_eq,
              __smtx_model_eval__at_purify, __smtx_model_eval_str_from_code,
              __smtx_model_eval_str_to_code, __smtx_model_eval_leq,
              __smtx_model_eval_lt, __smtx_model_eval_and, native_zleq,
              native_zlt, native_and, native_veq, native_unpack_pack_string,
              hz0, hzHi, hCode]
          · have hBad : ¬ (0 ≤ z ∧ z < 196608) := by
              intro h
              exact hzHi h.2
            have hFrom : native_str_from_code z = [] :=
              native_str_from_code_invalid hBad
            simp [tx, strFrom, cond, thenTerm, elseTerm, __smtx_model_eval, hXEval,
              __smtx_model_eval_ite, __smtx_model_eval_eq,
              __smtx_model_eval__at_purify, __smtx_model_eval_str_from_code,
              __smtx_model_eval_str_to_code, __smtx_model_eval_leq,
              __smtx_model_eval_lt, __smtx_model_eval_and, native_zleq,
              native_zlt, native_and, native_veq, hz0, hzHi, hFrom]
        · have hBad : ¬ (0 ≤ z ∧ z < 196608) := by
            intro h
            exact hz0 h.1
          have hFrom : native_str_from_code z = [] :=
            native_str_from_code_invalid hBad
          simp [tx, strFrom, cond, thenTerm, elseTerm, __smtx_model_eval, hXEval,
            __smtx_model_eval_ite, __smtx_model_eval_eq,
            __smtx_model_eval__at_purify, __smtx_model_eval_str_from_code,
            __smtx_model_eval_str_to_code, __smtx_model_eval_leq,
            __smtx_model_eval_lt, __smtx_model_eval_and, native_zleq,
            native_zlt, native_and, native_veq, hz0, hFrom]
      case str_to_int =>
        have hFormulaTy :
            __smtx_typeof
              (SmtTerm.geq (SmtTerm.str_to_int (__eo_to_smt x))
                (SmtTerm.Numeral (-1 : native_Int))) = SmtType.Bool := by
          simpa [RuleProofs.eo_has_bool_type] using hBool
        have hNN :
            term_has_non_none_type
              (SmtTerm.geq (SmtTerm.str_to_int (__eo_to_smt x))
                (SmtTerm.Numeral (-1 : native_Int))) := by
          unfold term_has_non_none_type
          rw [hFormulaTy]
          simp
        have hStrToIntTy :
            __smtx_typeof (SmtTerm.str_to_int (__eo_to_smt x)) = SmtType.Int := by
          rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
              (typeof_geq_eq (SmtTerm.str_to_int (__eo_to_smt x))
                (SmtTerm.Numeral (-1 : native_Int))) hNN with
            hInt | hReal
          · exact hInt.1
          · have hNumTy :
                __smtx_typeof (SmtTerm.Numeral (-1 : native_Int)) = SmtType.Int := by
              rw [__smtx_typeof.eq_2]
            rw [hNumTy] at hReal
            cases hReal.2
        have hStrToIntNN :
            term_has_non_none_type (SmtTerm.str_to_int (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [hStrToIntTy]
          simp
        have hsTy :
            __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
          seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
            (typeof_str_to_int_eq (__eo_to_smt x)) hStrToIntNN
        rcases seq_eval_of_seq_type M hM x SmtType.Char hsTy with ⟨ss, hSEval⟩
        apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
        change
          __smtx_model_eval M
              (SmtTerm.geq (SmtTerm.str_to_int (__eo_to_smt x))
                (SmtTerm.Numeral (-1 : native_Int))) =
            SmtValue.Boolean true
        have hGe :
            (-1 : Int) ≤ native_str_to_int (native_unpack_string ss) :=
          native_str_to_int_ge_neg_one (native_unpack_string ss)
        simp [__smtx_model_eval, hSEval, __smtx_model_eval_str_to_int, __smtx_model_eval_geq,
          __smtx_model_eval_leq, native_zleq, hGe]
    case Apply f y =>
      cases f <;> try simp [__mk_str_eager_reduction] at hBool ⊢
      all_goals try
        exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
      case UOp op =>
        cases op <;> try simp [__mk_str_eager_reduction] at hBool ⊢
        all_goals try
          exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
        case str_contains =>
          let condEo := Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) y) x
          let pre :=
            Term.UOp1 UserOp1._at_purify
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_substr) y)
                  (Term.Numeral 0))
                (Term.Apply
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_indexof) y) x)
                  (Term.Numeral 0)))
          let start :=
            Term.Apply
              (Term.Apply (Term.UOp UserOp.plus)
                (Term.Apply (Term.UOp UserOp.str_len) pre))
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.plus)
                  (Term.Apply (Term.UOp UserOp.str_len) x))
                (Term.Numeral 0))
          let suffix :=
            Term.UOp1 UserOp1._at_purify
              (Term.Apply
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.str_substr) y) start)
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.neg)
                    (Term.Apply (Term.UOp UserOp.str_len) y))
                  start))
          let nil := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre)
          let rhs3 := __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) suffix) nil
          let rhs2 := __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) x) rhs3
          let rhs1 := __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) pre) rhs2
          let thenEo := __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) y) rhs1
          let iteHead := __eo_mk_apply (Term.Apply (Term.UOp UserOp.ite) condEo) thenEo
          let elseEo :=
            Term.Apply (Term.UOp UserOp.not)
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)
          let gen := __eo_mk_apply iteHead elseEo
          have hGenBool : RuleProofs.eo_has_bool_type gen := by
            simpa [gen, iteHead, thenEo, rhs1, rhs2, rhs3, nil, suffix, start,
              pre, condEo, elseEo] using hBool
          have hGenNe : gen ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type gen hGenBool
          have hIteHeadNe : iteHead ≠ Term.Stuck :=
            eo_mk_apply_fun_ne_stuck_of_ne_stuck iteHead elseEo hGenNe
          have hThenNe : thenEo ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.ite) condEo) thenEo hIteHeadNe
          have hRhs1Ne : rhs1 ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.eq) y) rhs1 hThenNe
          have hRhs2Ne : rhs2 ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.str_concat) pre) rhs2 hRhs1Ne
          have hRhs3Ne : rhs3 ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.str_concat) x) rhs3 hRhs2Ne
          have hNilNe : nil ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.str_concat) suffix) nil hRhs3Ne
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          let idx := SmtTerm.str_indexof ty tx (SmtTerm.Numeral 0)
          let pfx := SmtTerm._at_purify (SmtTerm.str_substr ty (SmtTerm.Numeral 0) idx)
          let cut :=
            SmtTerm.plus (SmtTerm.str_len pfx)
              (SmtTerm.plus (SmtTerm.str_len tx) (SmtTerm.Numeral 0))
          let suffixS := SmtTerm._at_purify
            (SmtTerm.str_substr ty cut (SmtTerm.neg (SmtTerm.str_len ty) cut))
          let nilS := __eo_to_smt nil
          let rhs :=
            SmtTerm.str_concat pfx
              (SmtTerm.str_concat tx (SmtTerm.str_concat suffixS nilS))
          let cond := SmtTerm.str_contains ty tx
          let formula :=
            SmtTerm.ite cond (SmtTerm.eq ty rhs)
              (SmtTerm.not (SmtTerm.eq ty tx))
          have hFormulaTy : __smtx_typeof formula = SmtType.Bool := by
            unfold RuleProofs.eo_has_bool_type at hGenBool
            simpa [gen, iteHead, thenEo, rhs1, rhs2, rhs3, nil, suffix, start,
              pre, condEo, elseEo, formula, cond, rhs, nilS, suffixS, cut,
              pfx, idx, ty, tx, __eo_mk_apply, hNilNe] using hGenBool
          have hFormulaNN : term_has_non_none_type formula := by
            unfold term_has_non_none_type
            rw [hFormulaTy]
            simp
          rcases ite_args_of_non_none hFormulaNN with
            ⟨_R, hCondTy, _hThenTy, _hElseTy, _hRNN⟩
          have hCondNN : term_has_non_none_type cond := by
            unfold term_has_non_none_type
            rw [hCondTy]
            simp
          rcases seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
              (R := SmtType.Bool) (typeof_str_contains_eq ty tx) hCondNN with
            ⟨U, hyTy, hxTy⟩
          rcases seq_eval_of_seq_type M hM y U (by simpa [ty] using hyTy) with
            ⟨sy, hYEval⟩
          rcases seq_eval_of_seq_type M hM x U (by simpa [tx] using hxTy) with
            ⟨sx, hXEval⟩
          let ys := native_unpack_seq sy
          let xs := native_unpack_seq sx
          let idxVal := native_seq_indexof ys xs 0
          have hYEvalTy :
              __smtx_typeof_value (__smtx_model_eval M ty) = __smtx_typeof ty :=
            Smtm.smt_model_eval_preserves_type_of_non_none M hM ty
              (by simp [term_has_non_none_type, hyTy])
          have hSyTy : __smtx_typeof_seq_value sy = SmtType.Seq U := by
            simpa [ty, hYEval, hyTy] using hYEvalTy
          have hElemY : __smtx_elem_typeof_seq_value sy = U :=
            elem_typeof_seq_value_of_typeof_seq_value hSyTy
          have hPreTy :
              __smtx_typeof (__eo_to_smt pre) = SmtType.Seq U := by
            change __smtx_typeof pfx = SmtType.Seq U
            simp [pfx, idx, ty, tx, typeof_str_substr_eq,
              typeof_str_indexof_eq, hyTy, hxTy, __smtx_typeof,
              __smtx_typeof_str_indexof, __smtx_typeof_str_substr,
              __smtx_typeof_arith_overload_op_2, native_ite, native_Teq]
          have hNilEval : __smtx_model_eval M nilS =
              SmtValue.Seq (SmtSeq.empty U) := by
            simpa [nilS, nil] using
              eval_nil_str_concat_typeof_of_smt_type_seq M pre U hPreTy
          apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
          simp only [gen, iteHead, thenEo, rhs1, rhs2, rhs3, nil, suffix, start,
            pre, condEo, elseEo, __eo_mk_apply, hNilNe]
          change __smtx_model_eval M formula = SmtValue.Boolean true
          by_cases hContains : native_seq_contains ys xs = true
          · have hIdxNonneg : 0 ≤ idxVal := by
              simpa [idxVal, native_seq_contains] using hContains
            have hSplit :
                native_seq_extract ys 0 idxVal ++ xs ++
                    native_seq_extract ys (idxVal + Int.ofNat xs.length)
                      (Int.ofNat ys.length - (idxVal + Int.ofNat xs.length)) =
                  ys :=
              native_seq_indexof_zero_decomp ys xs hIdxNonneg
            have hPrefixLen :
                Int.ofNat (native_seq_extract ys 0 idxVal).length = idxVal := by
              simpa [idxVal] using
                native_seq_extract_prefix_length_of_indexof_nonneg ys xs hIdxNonneg
            have hStartEq :
                Int.ofNat (native_seq_extract ys 0 idxVal).length +
                    Int.ofNat xs.length =
                  idxVal + Int.ofNat xs.length := by
              rw [hPrefixLen]
            have hLenEq :
                Int.ofNat ys.length +
                    -((Int.ofNat (native_seq_extract ys 0 idxVal).length) +
                      Int.ofNat xs.length) =
                  Int.ofNat ys.length - (idxVal + Int.ofNat xs.length) := by
              rw [hPrefixLen]
              simp [Int.sub_eq_add_neg]
            have hPackSy : native_pack_seq U ys = sy := by
              dsimp [ys]
              rw [← hElemY]
              exact native_pack_unpack_seq sy
            simp [formula, cond, rhs, nilS, suffixS, cut, pfx, idx, ty, tx,
              ys, xs, idxVal, __smtx_model_eval, hYEval, hXEval, hNilEval,
              __smtx_model_eval_ite, __smtx_model_eval_str_contains,
              __smtx_model_eval_eq, __smtx_model_eval_str_concat,
              __smtx_model_eval_str_substr, __smtx_model_eval_str_indexof,
              __smtx_model_eval_str_len, __smtx_model_eval_plus,
              __smtx_model_eval__, __smtx_model_eval__at_purify, native_seq_concat,
              native_unpack_pack_seq, elem_typeof_pack_seq, native_seq_len,
              hElemY, hContains, hSplit, hPrefixLen, hStartEq, hLenEq, hPackSy,
              List.append_assoc, native_zplus, native_zneg, native_veq]
            apply Eq.trans hPackSy.symm
            apply congrArg (native_pack_seq U)
            dsimp [ys, xs, idxVal] at hSplit hStartEq hLenEq ⊢
            rw [hStartEq]
            simpa [native_unpack_seq, List.append_assoc, Int.sub_eq_add_neg] using hSplit.symm
          · have hContainsFalse : native_seq_contains ys xs = false := by
              cases h : native_seq_contains ys xs
              · rfl
              · exact False.elim (hContains (by simpa [h]))
            have hSyNeSx : sy ≠ sx := by
              intro hEq
              have hLists : ys = xs := by
                simp [ys, xs, hEq]
              have hSelf := native_seq_contains_self xs
              have hFalseSelf : native_seq_contains xs xs = false := by
                simpa [ys, xs, hLists] using hContainsFalse
              rw [hSelf] at hFalseSelf
              cases hFalseSelf
            have hValNe : SmtValue.Seq sy ≠ SmtValue.Seq sx := by
              intro hEq
              cases hEq
              exact hSyNeSx rfl
            have hEqFalse : native_veq (SmtValue.Seq sy) (SmtValue.Seq sx) = false := by
              simp [native_veq, hValNe]
            simp [formula, cond, rhs, nilS, suffixS, cut, pfx, idx, ty, tx,
              ys, xs, __smtx_model_eval, hYEval, hXEval,
              __smtx_model_eval_ite, __smtx_model_eval_str_contains,
              __smtx_model_eval_eq, __smtx_model_eval_not, native_not,
              native_veq, hContainsFalse, hEqFalse]
            exact hSyNeSx
        case str_in_re =>
          let fixed := __str_fixed_len_re x
          let rhsEo :=
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.str_len) y))
              fixed
          let gen :=
            __eo_mk_apply
              (Term.Apply (Term.UOp UserOp.imp)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x))
              rhsEo
          have hGenBool : RuleProofs.eo_has_bool_type gen := by
            simpa [gen, rhsEo, fixed] using hBool
          have hGenNe : gen ≠ Term.Stuck :=
            RuleProofs.term_ne_stuck_of_has_bool_type gen hGenBool
          have hRhsNe : rhsEo ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.imp)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x))
              rhsEo hGenNe
          have hFixedNe : fixed ≠ Term.Stuck :=
            eo_mk_apply_arg_ne_stuck_of_ne_stuck
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp UserOp.str_len) y))
              fixed hRhsNe
          rcases str_fixed_len_re_numeral_of_ne_stuck x hFixedNe with
            ⟨n, hFixed⟩
          let ty := __eo_to_smt y
          let tx := __eo_to_smt x
          let lhs := SmtTerm.str_in_re ty tx
          let rhs := SmtTerm.eq (SmtTerm.str_len ty) (SmtTerm.Numeral n)
          let formula := SmtTerm.imp lhs rhs
          have hFormulaTy : __smtx_typeof formula = SmtType.Bool := by
            unfold RuleProofs.eo_has_bool_type at hGenBool
            simpa [gen, rhsEo, fixed, formula, lhs, rhs, ty, tx,
              __eo_mk_apply, hFixed] using hGenBool
          have hFormulaNN : term_has_non_none_type formula := by
            unfold term_has_non_none_type
            rw [hFormulaTy]
            simp
          have hLhsTy : __smtx_typeof lhs = SmtType.Bool :=
            (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
              (typeof_imp_eq lhs rhs) hFormulaNN).1
          have hLhsNN : term_has_non_none_type lhs := by
            unfold term_has_non_none_type
            rw [hLhsTy]
            simp
          have hArgs :=
            seq_char_reglan_args_of_non_none
              (op := SmtTerm.str_in_re) (typeof_str_in_re_eq ty tx) hLhsNN
          have hyTy : __smtx_typeof ty = SmtType.Seq SmtType.Char := hArgs.1
          have hxTy : __smtx_typeof tx = SmtType.RegLan := hArgs.2
          rcases seq_eval_of_seq_type M hM y SmtType.Char
              (by simpa [ty] using hyTy) with
            ⟨sy, hYEval⟩
          rcases reglan_eval_of_reglan_type M hM x
              (by simpa [tx] using hxTy) with
            ⟨rx, hXEval⟩
          apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
          simp only [gen, rhsEo, fixed, __eo_mk_apply, hFixed]
          change __smtx_model_eval M formula = SmtValue.Boolean true
          by_cases hIn : native_str_in_re (native_unpack_string sy) rx = true
          · have hFixedLen :
                Int.ofNat (native_unpack_string sy).length = n :=
              str_fixed_len_re_sound M x (native_unpack_string sy) rx n
                hFixed hXEval hIn
            have hFixedLenSeq : native_seq_len (native_unpack_seq sy) = n := by
              simpa [native_seq_len, native_unpack_string_length_eq sy] using
                hFixedLen
            simp [formula, lhs, rhs, ty, tx, __smtx_model_eval, hYEval, hXEval,
              __smtx_model_eval_imp, __smtx_model_eval_str_in_re,
              __smtx_model_eval_str_len, __smtx_model_eval_eq,
              __smtx_model_eval_or, __smtx_model_eval_not, native_or,
              native_not, native_veq, hIn, hFixedLenSeq]
          · have hInFalse :
                native_str_in_re (native_unpack_string sy) rx = false := by
              cases h : native_str_in_re (native_unpack_string sy) rx
              · rfl
              · exact False.elim (hIn (by simpa [h]))
            simp [formula, lhs, rhs, ty, tx, __smtx_model_eval, hYEval, hXEval,
              __smtx_model_eval_imp, __smtx_model_eval_str_in_re,
              __smtx_model_eval_str_len, __smtx_model_eval_eq,
              __smtx_model_eval_or, __smtx_model_eval_not, native_or,
              native_not, native_veq, hInFalse]
      case Apply f z =>
        cases f <;> try simp [__mk_str_eager_reduction] at hBool ⊢
        all_goals try
          exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
        case UOp op =>
          cases op <;> try simp [__mk_str_eager_reduction] at hBool ⊢
          all_goals try
            exact False.elim (RuleProofs.term_ne_stuck_of_has_bool_type _ hBool rfl)
          case str_indexof =>
            let tz := __eo_to_smt z
            let ty := __eo_to_smt y
            let tx := __eo_to_smt x
            let idx := SmtTerm.str_indexof tz ty tx
            let leftTerm :=
              SmtTerm.or (SmtTerm.eq idx (SmtTerm.Numeral (-1 : native_Int)))
                (SmtTerm.or (SmtTerm.geq idx tx) (SmtTerm.Boolean false))
            let rightTerm :=
              SmtTerm.and (SmtTerm.leq idx (SmtTerm.str_len tz))
                (SmtTerm.Boolean true)
            have hFormulaTy :
                __smtx_typeof (SmtTerm.and leftTerm rightTerm) = SmtType.Bool := by
              simpa [RuleProofs.eo_has_bool_type, tz, ty, tx, idx, leftTerm,
                rightTerm] using hBool
            have hFormulaNN :
                term_has_non_none_type (SmtTerm.and leftTerm rightTerm) := by
              unfold term_has_non_none_type
              rw [hFormulaTy]
              simp
            have hRightTy : __smtx_typeof rightTerm = SmtType.Bool :=
              (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                (typeof_and_eq leftTerm rightTerm) hFormulaNN).2
            have hRightNN : term_has_non_none_type rightTerm := by
              unfold term_has_non_none_type
              rw [hRightTy]
              simp
            have hLeqTy :
                __smtx_typeof (SmtTerm.leq idx (SmtTerm.str_len tz)) =
                  SmtType.Bool :=
              (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                (typeof_and_eq (SmtTerm.leq idx (SmtTerm.str_len tz))
                  (SmtTerm.Boolean true)) hRightNN).1
            have hLeqNN :
                term_has_non_none_type (SmtTerm.leq idx (SmtTerm.str_len tz)) := by
              unfold term_has_non_none_type
              rw [hLeqTy]
              simp
            have hIdxTy : __smtx_typeof idx = SmtType.Int := by
              rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
                  (typeof_leq_eq idx (SmtTerm.str_len tz)) hLeqNN with
                hInt | hReal
              · exact hInt.1
              · have hLenNN : term_has_non_none_type (SmtTerm.str_len tz) := by
                  unfold term_has_non_none_type
                  rw [hReal.2]
                  simp
                rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
                    (typeof_str_len_eq tz) hLenNN with ⟨U, hSeq⟩
                have hLenTy :
                    __smtx_typeof (SmtTerm.str_len tz) = SmtType.Int := by
                  rw [typeof_str_len_eq]
                  simp [__smtx_typeof_seq_op_1_ret, hSeq]
                rw [hLenTy] at hReal
                cases hReal.2
            have hIdxNN : term_has_non_none_type idx := by
              unfold term_has_non_none_type
              rw [hIdxTy]
              simp
            rcases str_indexof_args_of_non_none (by simpa [idx] using hIdxNN) with
              ⟨U, hzTy, hyTy, hxTy⟩
            rcases seq_eval_of_seq_type M hM z U (by simpa [tz] using hzTy) with
              ⟨sz, hZEval⟩
            rcases seq_eval_of_seq_type M hM y U (by simpa [ty] using hyTy) with
              ⟨sy, hYEval⟩
            rcases int_eval_of_int_type M hM x (by simpa [tx] using hxTy) with
              ⟨n, hXEval⟩
            let idxVal :=
              native_seq_indexof (native_unpack_seq sz) (native_unpack_seq sy) n
            have hIdxOr :
                idxVal = -1 ∨ n ≤ idxVal :=
              native_seq_indexof_eq_neg_one_or_ge
                (native_unpack_seq sz) (native_unpack_seq sy) n
            have hIdxLe :
                idxVal ≤ Int.ofNat (native_unpack_seq sz).length :=
              native_seq_indexof_le_len
                (native_unpack_seq sz) (native_unpack_seq sy) n
            apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
            change __smtx_model_eval M (SmtTerm.and leftTerm rightTerm) =
              SmtValue.Boolean true
            rcases hIdxOr with hIdxEq | hIdxGe
            · simp [tz, ty, tx, idx, idxVal, leftTerm, rightTerm, __smtx_model_eval,
                hZEval, hYEval, hXEval, __smtx_model_eval_str_indexof,
                __smtx_model_eval_str_len, __smtx_model_eval_eq,
                __smtx_model_eval_geq, __smtx_model_eval_leq,
                __smtx_model_eval_or, __smtx_model_eval_and, native_seq_len,
                native_veq, native_zleq, native_or, native_and, hIdxEq, hIdxLe]
            · simp [tz, ty, tx, idx, idxVal, leftTerm, rightTerm, __smtx_model_eval,
                hZEval, hYEval, hXEval, __smtx_model_eval_str_indexof,
                __smtx_model_eval_str_len, __smtx_model_eval_eq,
                __smtx_model_eval_geq, __smtx_model_eval_leq,
                __smtx_model_eval_or, __smtx_model_eval_and, native_seq_len,
              native_veq, native_zleq, native_or, native_and, hIdxGe, hIdxLe]
              simpa [idxVal] using hIdxLe
          case str_indexof_re =>
            let tz := __eo_to_smt z
            let ty := __eo_to_smt y
            let tx := __eo_to_smt x
            let idx := SmtTerm.str_indexof_re tz ty tx
            let leftTerm :=
              SmtTerm.or (SmtTerm.eq idx (SmtTerm.Numeral (-1 : native_Int)))
                (SmtTerm.or (SmtTerm.geq idx tx) (SmtTerm.Boolean false))
            let rightTerm :=
              SmtTerm.and (SmtTerm.leq idx (SmtTerm.str_len tz))
                (SmtTerm.Boolean true)
            have hFormulaTy :
                __smtx_typeof (SmtTerm.and leftTerm rightTerm) = SmtType.Bool := by
              simpa [RuleProofs.eo_has_bool_type, tz, ty, tx, idx, leftTerm,
                rightTerm] using hBool
            have hFormulaNN :
                term_has_non_none_type (SmtTerm.and leftTerm rightTerm) := by
              unfold term_has_non_none_type
              rw [hFormulaTy]
              simp
            have hRightTy : __smtx_typeof rightTerm = SmtType.Bool :=
              (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                (typeof_and_eq leftTerm rightTerm) hFormulaNN).2
            have hRightNN : term_has_non_none_type rightTerm := by
              unfold term_has_non_none_type
              rw [hRightTy]
              simp
            have hLeqTy :
                __smtx_typeof (SmtTerm.leq idx (SmtTerm.str_len tz)) =
                  SmtType.Bool :=
              (bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                (typeof_and_eq (SmtTerm.leq idx (SmtTerm.str_len tz))
                  (SmtTerm.Boolean true)) hRightNN).1
            have hLeqNN :
                term_has_non_none_type (SmtTerm.leq idx (SmtTerm.str_len tz)) := by
              unfold term_has_non_none_type
              rw [hLeqTy]
              simp
            have hIdxTy : __smtx_typeof idx = SmtType.Int := by
              rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq)
                  (typeof_leq_eq idx (SmtTerm.str_len tz)) hLeqNN with
                hInt | hReal
              · exact hInt.1
              · have hLenNN : term_has_non_none_type (SmtTerm.str_len tz) := by
                  unfold term_has_non_none_type
                  rw [hReal.2]
                  simp
                rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
                    (typeof_str_len_eq tz) hLenNN with ⟨U, hSeq⟩
                have hLenTy :
                    __smtx_typeof (SmtTerm.str_len tz) = SmtType.Int := by
                  rw [typeof_str_len_eq]
                  simp [__smtx_typeof_seq_op_1_ret, hSeq]
                rw [hLenTy] at hReal
                cases hReal.2
            have hIdxNN : term_has_non_none_type idx := by
              unfold term_has_non_none_type
              rw [hIdxTy]
              simp
            rcases str_indexof_re_args_of_non_none (by simpa [idx] using hIdxNN) with
              ⟨hzTy, hyTy, hxTy⟩
            rcases seq_eval_of_seq_type M hM z SmtType.Char (by simpa [tz] using hzTy) with
              ⟨sz, hZEval⟩
            rcases reglan_eval_of_reglan_type M hM y (by simpa [ty] using hyTy) with
              ⟨ry, hYEval⟩
            rcases int_eval_of_int_type M hM x (by simpa [tx] using hxTy) with
              ⟨n, hXEval⟩
            let idxVal := native_str_indexof_re (native_unpack_string sz) ry n
            have hIdxOr :
                idxVal = -1 ∨ n ≤ idxVal :=
              native_str_indexof_re_eq_neg_one_or_ge (native_unpack_string sz) ry n
            have hIdxLe :
                idxVal ≤ Int.ofNat (native_unpack_string sz).length :=
              native_str_indexof_re_le_len (native_unpack_string sz) ry n
            have hIdxLeSeq :
                idxVal ≤ Int.ofNat (native_unpack_seq sz).length := by
              rw [← native_unpack_string_length_eq sz]
              exact hIdxLe
            apply RuleProofs.eo_interprets_of_bool_eval M _ true hBool
            change __smtx_model_eval M (SmtTerm.and leftTerm rightTerm) =
              SmtValue.Boolean true
            rcases hIdxOr with hIdxEq | hIdxGe
            · simp [tz, ty, tx, idx, idxVal, leftTerm, rightTerm, __smtx_model_eval,
                hZEval, hYEval, hXEval, __smtx_model_eval_str_indexof_re,
                __smtx_model_eval_str_len, __smtx_model_eval_eq,
                __smtx_model_eval_geq, __smtx_model_eval_leq,
                __smtx_model_eval_or, __smtx_model_eval_and, native_seq_len,
                native_veq, native_zleq, native_or, native_and, hIdxEq, hIdxLeSeq]
            · simp [tz, ty, tx, idx, idxVal, leftTerm, rightTerm, __smtx_model_eval,
                hZEval, hYEval, hXEval, __smtx_model_eval_str_indexof_re,
                __smtx_model_eval_str_len, __smtx_model_eval_eq,
                __smtx_model_eval_geq, __smtx_model_eval_leq,
                __smtx_model_eval_or, __smtx_model_eval_and, native_seq_len,
                native_veq, native_zleq, native_or, native_and, hIdxGe, hIdxLeSeq]
              simpa [idxVal] using hIdxLeSeq

theorem cmd_step_string_eager_reduction_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.string_eager_reduction args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.string_eager_reduction args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.string_eager_reduction args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.string_eager_reduction args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a args =>
      cases args with
      | cons b args =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons n premises =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hATrans : RuleProofs.eo_has_smt_translation a := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans.1
              have hPBool :
                  RuleProofs.eo_has_bool_type (__eo_prog_string_eager_reduction a) := by
                exact string_eager_reduction_has_bool_type a hATrans hResultTy
              refine ⟨?_, RuleProofs.eo_has_smt_translation_of_has_bool_type _ hPBool⟩
              intro _hPremisesTrue
              exact string_eager_reduction_true M hM a hPBool
