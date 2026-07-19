import Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.StrContainsReplCharSupport
import Cpc.Proofs.RuleSupport.ConcatSplitSupport
import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Closed.IsClosedRec

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

private theorem sr_native_unpack_pack_string_length (s : native_String) :
    (native_unpack_seq (native_pack_string s)).length = s.length := by
  simp [native_pack_string, Smtm.native_unpack_pack_seq]

private theorem sr_native_pack_string_injective :
    Function.Injective native_pack_string := by
  intro s t h
  have h' := congrArg native_unpack_string h
  simpa [sr_native_unpack_pack_string] using h'

private theorem sr_native_pack_string_eq_iff
    (s t : native_String) :
    native_pack_string s = native_pack_string t ↔ s = t :=
  sr_native_pack_string_injective.eq_iff

private theorem sr_smt_type_wf_int :
    __smtx_type_wf SmtType.Int = true := by
  native_decide

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
    generalize hl : native_unpack_seq ss = l at hTyped ⊢
    clear hl
    induction l with
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
  simp only [List.length_map, apply_ite, List.map_nil,
    List.map_take, List.map_drop]
  split <;> simp_all
  intro hbad
  rcases ‹(0 ≤ i ∧ 0 < n) ∧ i < Int.ofNat s.length› with
    ⟨⟨hi0, hn0⟩, hilt⟩
  rcases hbad with (hi | hn) | hlen
  · exact False.elim ((Int.not_lt_of_ge hi0) hi)
  · exact False.elim ((Int.not_le_of_gt hn0) hn)
  · exact False.elim ((Int.not_le_of_gt hilt) hlen)

/-- The generated evaluator retains the packed sequence's inferred element
    type at extraction sites; for strings, that type is `Char`. -/
private theorem sr_native_seq_extract_pack_string_eval
    (s : native_String) (i n : native_Int) :
    native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string s))
        (native_seq_extract (native_unpack_seq (native_pack_string s)) i n) =
      native_pack_string (native_str_substr s i n) := by
  have hElem :
      __smtx_elem_typeof_seq_value (native_pack_string s) =
        SmtType.Char := by
    simp [native_pack_string, elem_typeof_pack_seq]
  rw [hElem]
  exact sr_native_seq_extract_pack_string s i n

/-- The generated `Int.ofNat` constructor and Lean's ordinary natural-number
    cast denote the same integer. -/
private theorem sr_int_natCast_eq_ofNat (j : Nat) :
    (j : Int) = Int.ofNat j := by
  cases j <;> rfl

/-- Unpacking the evaluator's packed extraction gives the corresponding
    native-string substring. -/
private theorem sr_native_unpack_extract_pack_string
    (s : native_String) (i n : native_Int) :
    native_unpack_string
        (native_pack_seq (__smtx_elem_typeof_seq_value (native_pack_string s))
          (native_seq_extract (native_unpack_seq (native_pack_string s)) i n)) =
      native_str_substr s i n := by
  have hElem :
      __smtx_elem_typeof_seq_value (native_pack_string s) =
        SmtType.Char := by
    simp [native_pack_string, elem_typeof_pack_seq]
  rw [hElem]
  have h := congrArg native_unpack_string
    (sr_native_seq_extract_pack_string s i n)
  simpa [sr_native_unpack_pack_string] using h

/-- For an in-bounds natural index, extracting one sequence element is the
    corresponding one-element `drop`/`take` slice. -/
private theorem sr_native_seq_extract_one_nat
    (xs : List SmtValue) (j : Nat) (hj : j < xs.length) :
    native_seq_extract xs (Int.ofNat j) 1 = (xs.drop j).take 1 := by
  have e1 : decide ((Int.ofNat j : native_Int) < 0) = false :=
    decide_eq_false (show ¬ ((j : Int) < 0) by omega)
  have e2 : decide ((1 : native_Int) ≤ 0) = false := by decide
  have e3 :
      decide ((Int.ofNat j : native_Int) ≥ Int.ofNat xs.length) = false :=
    decide_eq_false (show ¬ ((j : Int) ≥ (xs.length : Int)) by omega)
  have h1 : (1 : Int) ≤ (xs.length : Int) - (j : Int) := by omega
  have hmin :
      min (1 : native_Int) (Int.ofNat xs.length - Int.ofNat j) = 1 :=
    Int.min_eq_left h1
  simp only [native_seq_extract]
  rw [e1, e2, e3, hmin]
  simp

/-- Outside the usual positive, in-bounds substring guard, extraction is
    empty. -/
private theorem sr_native_seq_extract_empty_of_inactive
    (xs : List SmtValue) (i n : native_Int)
    (h : ¬ (0 ≤ i ∧ i < Int.ofNat xs.length ∧ 0 < n)) :
    native_seq_extract xs i n = [] := by
  by_cases hi : i < 0
  · simp [native_seq_extract, hi]
  by_cases hn : n ≤ 0
  · exact native_seq_extract_empty_of_len_nonpos xs i n hn
  have hi0 : 0 ≤ i := Int.le_of_not_gt hi
  have hn0 : 0 < n := Int.lt_of_not_ge hn
  have hlen : Int.ofNat xs.length ≤ i := by
    apply Int.le_of_not_gt
    intro hiLen
    exact h ⟨hi0, hiLen, hn0⟩
  unfold native_seq_extract
  rw [if_pos (by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr hlen)]

/-- The prefix, selected slice, and residual suffix generated by the
    substring reduction reconstruct the source, with the advertised length
    bounds. -/
private theorem sr_native_seq_extract_active_facts
    (xs : List SmtValue) (i n : native_Int)
    (hi : 0 ≤ i) (hiLen : i < Int.ofNat xs.length) (hn : 0 < n) :
    native_seq_extract xs 0 i ++
          native_seq_extract xs i n ++
          native_seq_extract xs (i + n)
            (Int.ofNat xs.length - (i + n)) = xs ∧
      Int.ofNat (native_seq_extract xs 0 i).length = i ∧
      (Int.ofNat
            (native_seq_extract xs (i + n)
              (Int.ofNat xs.length - (i + n))).length =
          Int.ofNat xs.length - (i + n) ∨
        Int.ofNat
            (native_seq_extract xs (i + n)
              (Int.ofNat xs.length - (i + n))).length = 0) ∧
      Int.ofNat (native_seq_extract xs i n).length ≤ n := by
  let I := Int.toNat i
  let N := Int.toNat n
  have hICast : (I : native_Int) = i := Int.toNat_of_nonneg hi
  have hNCast : (N : native_Int) = n :=
    Int.toNat_of_nonneg (Int.le_of_lt hn)
  have hILt : I < xs.length := by
    apply Int.ofNat_lt.mp
    simpa [hICast] using hiLen
  have hILe : I ≤ xs.length := Nat.le_of_lt hILt
  have hPre : native_seq_extract xs 0 i = xs.take I := by
    rw [← hICast]
    exact native_seq_extract_zero_nat xs I hILe
  have hMid : native_seq_extract xs i n = (xs.drop I).take N := by
    rw [native_seq_extract_eq_drop_take xs i n hi hn]
  have hPreLen : Int.ofNat (native_seq_extract xs 0 i).length = i := by
    simpa [hPre, List.length_take, Nat.min_eq_left hILe] using hICast
  have hMidLen : Int.ofNat (native_seq_extract xs i n).length ≤ n := by
    calc
      Int.ofNat (native_seq_extract xs i n).length =
          Int.ofNat ((xs.drop I).take N).length := by rw [hMid]
      _ ≤ Int.ofNat N := Int.ofNat_le.mpr (by
        rw [List.length_take]
        exact Nat.min_le_left _ _)
      _ = n := hNCast
  have hINCast : ((I + N : Nat) : native_Int) = i + n := by
    calc
      ((I + N : Nat) : native_Int) =
          (I : native_Int) + (N : native_Int) :=
        (Int.ofNat_add_ofNat I N).symm
      _ = i + n := by rw [hICast, hNCast]
  by_cases hEnd : i + n ≤ Int.ofNat xs.length
  · have hINLe : I + N ≤ xs.length := by
      apply Int.ofNat_le.mp
      rw [← Int.ofNat_add_ofNat, hICast, hNCast]
      exact hEnd
    have hRemaining :
        Int.ofNat xs.length - (i + n) =
          Int.ofNat (xs.length - (I + N)) := by
      rw [← hINCast]
      exact (Int.ofNat_sub hINLe).symm
    have hSuffix :
        native_seq_extract xs (i + n)
            (Int.ofNat xs.length - (i + n)) =
          xs.drop (I + N) := by
      rw [hRemaining, ← hINCast]
      exact native_seq_extract_to_end_nat xs (I + N) hINLe
    have hDecomp :
        native_seq_extract xs 0 i ++ native_seq_extract xs i n ++
            native_seq_extract xs (i + n)
              (Int.ofNat xs.length - (i + n)) = xs := by
      rw [hPre, hMid, hSuffix]
      calc
        xs.take I ++ (xs.drop I).take N ++ xs.drop (I + N) =
            xs.take I ++
              ((xs.drop I).take N ++ (xs.drop I).drop N) := by
                simp only [List.drop_drop, List.append_assoc]
        _ = xs.take I ++ xs.drop I := by
              rw [List.take_append_drop]
        _ = xs := List.take_append_drop I xs
    have hSuffixLen :
        Int.ofNat
              (native_seq_extract xs (i + n)
                (Int.ofNat xs.length - (i + n))).length =
            Int.ofNat xs.length - (i + n) := by
      rw [hSuffix, List.length_drop, hRemaining]
    exact ⟨hDecomp, hPreLen, Or.inl hSuffixLen, hMidLen⟩
  · have hRemainingNonpos :
        Int.ofNat xs.length - (i + n) ≤ 0 := by
      have hOver : Int.ofNat xs.length < i + n := Int.lt_of_not_ge hEnd
      omega
    have hSuffix :
        native_seq_extract xs (i + n)
            (Int.ofNat xs.length - (i + n)) = [] :=
      native_seq_extract_empty_of_len_nonpos _ _ _ hRemainingNonpos
    have hTailLe : (xs.drop I).length ≤ N := by
      rw [List.length_drop]
      have hNotNat : ¬ I + N ≤ xs.length := by
        intro hLe
        apply hEnd
        rw [← hINCast]
        exact Int.ofNat_le.mpr hLe
      have hNatOver : xs.length < I + N := Nat.lt_of_not_ge hNotNat
      omega
    have hMidTail : (xs.drop I).take N = xs.drop I :=
      List.take_of_length_le hTailLe
    have hDecomp :
        native_seq_extract xs 0 i ++ native_seq_extract xs i n ++
            native_seq_extract xs (i + n)
              (Int.ofNat xs.length - (i + n)) = xs := by
      rw [hPre, hMid, hSuffix, hMidTail]
      simp [List.take_append_drop]
    have hSuffixLen :
        Int.ofNat
              (native_seq_extract xs (i + n)
                (Int.ofNat xs.length - (i + n))).length = 0 := by
      have h := congrArg (fun ys : List SmtValue => Int.ofNat ys.length)
        hSuffix
      simpa using h
    exact ⟨hDecomp, hPreLen, Or.inr hSuffixLen, hMidLen⟩

/-- Reversing a sequence maps an in-bounds one-element slice to its mirrored
    one-element slice. -/
private theorem sr_native_seq_extract_reverse_one
    (xs : List SmtValue) (j : Nat) (hj : j < xs.length) :
    native_seq_extract xs.reverse (Int.ofNat j) 1 =
      native_seq_extract xs (Int.ofNat (xs.length - (j + 1))) 1 := by
  rw [sr_native_seq_extract_one_nat xs.reverse j (by simpa using hj),
    sr_native_seq_extract_one_nat xs (xs.length - (j + 1)) (by omega)]
  simp only [List.take_one, List.head?_drop]
  have hMirror : xs.length - (j + 1) = xs.length - 1 - j := by omega
  rw [hMirror]
  exact congrArg Option.toList (List.getElem?_reverse hj)

/-- Sequence containment is equivalent to the existence of an in-bounds
    extraction equal to the pattern. -/
private theorem sr_native_seq_contains_iff_extract
    (xs pat : List SmtValue) :
    native_seq_contains xs pat = true ↔
      ∃ j : Nat,
        j ≤ xs.length - pat.length ∧
          native_seq_extract xs (Int.ofNat j) (Int.ofNat pat.length) = pat := by
  constructor
  · intro hContains
    rcases
        (StrContainsReplCharSupport.native_seq_contains_iff_decomp xs pat).1
          hContains with
      ⟨before, after, hXs⟩
    let j := before.length
    have hBound : j ≤ xs.length - pat.length := by
      have hLen := congrArg List.length hXs
      simp [j] at hLen ⊢
      omega
    refine ⟨j, hBound, ?_⟩
    by_cases hPatNil : pat = []
    · subst pat
      simp [native_seq_extract_empty_of_len_nonpos]
    · have hPatLen : 0 < pat.length := by
        cases pat with
        | nil => contradiction
        | cons => simp
      have hPatPos : (0 : Int) < Int.ofNat pat.length := by
        apply Int.ofNat_lt.mpr
        exact hPatLen
      rw [native_seq_extract_eq_drop_take xs (Int.ofNat j)
        (Int.ofNat pat.length) (Int.natCast_nonneg j) hPatPos]
      simp [hXs, j]
  · rintro ⟨j, hBound, hExtract⟩
    apply
      (StrContainsReplCharSupport.native_seq_contains_iff_decomp xs pat).2
    by_cases hPatNil : pat = []
    · subst pat
      exact ⟨[], xs, by simp⟩
    · have hPatLen : 0 < pat.length := by
        cases pat with
        | nil => contradiction
        | cons => simp
      have hPatPos : (0 : Int) < Int.ofNat pat.length := by
        apply Int.ofNat_lt.mpr
        exact hPatLen
      have hDropTake : (xs.drop j).take pat.length = pat := by
        rw [native_seq_extract_eq_drop_take xs (Int.ofNat j)
          (Int.ofNat pat.length) (Int.natCast_nonneg j) hPatPos] at hExtract
        simpa using hExtract
      refine ⟨xs.take j, xs.drop (j + pat.length), ?_⟩
      calc
        xs = xs.take j ++ xs.drop j := (List.take_append_drop j xs).symm
        _ = xs.take j ++
              ((xs.drop j).take pat.length ++
                (xs.drop j).drop pat.length) := by
            exact congrArg (fun zs => xs.take j ++ zs)
              (List.take_append_drop pat.length (xs.drop j)).symm
        _ = xs.take j ++ pat ++ xs.drop (j + pat.length) := by
            simp only [hDropTake, List.drop_drop, List.append_assoc]

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
    have h32 : 32 ≤ s[j] :=
      Nat.le_trans (by decide) hRange.1
    rw [Int.ofNat_sub h32]
    rw [Int.sub_eq_add_neg]
    have h32cast : Int.ofNat 32 = (32 : Int) := by decide
    exact congrArg (fun z : Int => Int.ofNat s[j] + -z) h32cast
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
  by_cases hj0 : j = 0
  · subst j
    simp [native_str_substr, native_str_len]
  by_cases hs0 : s = []
  · subst s
    have : j = 0 := by simpa using hj
    exact False.elim (hj0 this)
  have hmin :
      min (Int.ofNat j) (Int.ofNat s.length) = Int.ofNat j :=
    Int.min_eq_left (Int.ofNat_le.mpr hj)
  simp [native_str_substr, native_str_len, hj0, hs0]
  omega

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
    simpa using sr_native_str_substr_at_length (a :: s)

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
        have h := (show native_char_valid b = true ∧
            native_string_valid bs = true by
          simpa [native_string_valid, Bool.and_eq_true] using ht)
        exact h.1
      refine ⟨0, by simp, by simp, by simp, ?_⟩
      have hSub : native_str_substr (b :: bs) 0 1 = [b] := by
        simpa using sr_native_str_substr_one_nat (b :: bs) 0 (by simp)
      have hEmpty : native_str_substr [] 0 1 = [] := by
        simp [native_str_substr, native_str_len]
      simp [sr_native_str_leq_bool, native_str_lt, native_or,
        hSub, hEmpty, native_str_to_code, hb]
      have hb0 : (0 : Int) ≤ Int.ofNat b := Int.natCast_nonneg b
      exact Int.lt_of_lt_of_le (by decide) hb0
  | a :: as, [], hs, _ht, _hne => by
      have ha : native_char_valid a = true := by
        have h := (show native_char_valid a = true ∧
            native_string_valid as = true by
          simpa [native_string_valid, Bool.and_eq_true] using hs)
        exact h.1
      refine ⟨0, by simp, by simp, by simp, ?_⟩
      have hSub : native_str_substr (a :: as) 0 1 = [a] := by
        simpa using sr_native_str_substr_one_nat (a :: as) 0 (by simp)
      have hEmpty : native_str_substr [] 0 1 = [] := by
        simp [native_str_substr, native_str_len]
      simp [sr_native_str_leq_bool, native_str_lt, native_or,
        hSub, hEmpty, native_str_to_code, ha]
      have ha0 : (0 : Int) ≤ Int.ofNat a := Int.natCast_nonneg a
      exact Int.lt_of_lt_of_le (by decide) ha0
  | a :: as, b :: bs, hs, ht, hne => by
      have ha : native_char_valid a = true := by
        have h := (show native_char_valid a = true ∧
            native_string_valid as = true by
          simpa [native_string_valid, Bool.and_eq_true] using hs)
        exact h.1
      have hb : native_char_valid b = true := by
        have h := (show native_char_valid b = true ∧
            native_string_valid bs = true by
          simpa [native_string_valid, Bool.and_eq_true] using ht)
        exact h.1
      have has : native_string_valid as = true := by
        have h := (show native_char_valid a = true ∧
            native_string_valid as = true by
          simpa [native_string_valid, Bool.and_eq_true] using hs)
        exact h.2
      have hbs : native_string_valid bs = true := by
        have h := (show native_char_valid b = true ∧
            native_string_valid bs = true by
          simpa [native_string_valid, Bool.and_eq_true] using ht)
        exact h.2
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
        · have hba : b < a :=
            Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm hab)
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

/-- Recover top-level closedness from the recursive empty-environment form. -/
private theorem sr_eo_is_closed_of_rec_nil
    (t : Term) (hNe : t ≠ Term.Stuck)
    (hRec :
      __eo_is_closed_rec t Term.__eo_List_nil = Term.Boolean true) :
    __eo_is_closed t = Term.Boolean true := by
  cases t <;> simp [__eo_is_closed] at hNe ⊢
  all_goals exact hRec

/-- Closedness of a unary operator application implies closedness of its argument. -/
private theorem sr_eo_is_closed_apply_uop_arg
    (op : UserOp) (x : Term) (hNe : x ≠ Term.Stuck)
    (hClosed :
      __eo_is_closed (Term.Apply (Term.UOp op) x) = Term.Boolean true) :
    __eo_is_closed x = Term.Boolean true := by
  have hParentRec := eo_is_closed_eq_true_rec_nil hClosed
  have hArgRec := eo_is_closed_rec_apply_uop_arg_eq_true
    (hEnv := EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil) hParentRec
  exact sr_eo_is_closed_of_rec_nil x hNe hArgRec

/-- Closedness of a binary operator application splits over its arguments. -/
private theorem sr_eo_is_closed_binary_uop_args
    (op : UserOp) (x y : Term)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXNe : x ≠ Term.Stuck) (hYNe : y ≠ Term.Stuck)
    (hClosed :
      __eo_is_closed (Term.Apply (Term.Apply (Term.UOp op) x) y) =
        Term.Boolean true) :
    __eo_is_closed x = Term.Boolean true ∧
      __eo_is_closed y = Term.Boolean true := by
  have hParentRec := eo_is_closed_eq_true_rec_nil hClosed
  have hArgsRec := eo_is_closed_rec_binary_uop_eq_true_cases
    hNotForall hNotExists
    (hEnv := EoSmtVarEnvPerm.of_exact EoSmtVarEnv.nil) hParentRec
  exact ⟨sr_eo_is_closed_of_rec_nil x hXNe hArgsRec.1,
    sr_eo_is_closed_of_rec_nil y hYNe hArgsRec.2⟩

/-- The SMT encoding used for EO `forall` is true when its body is true
for every typed canonical value. -/
private theorem sr_eval_forall_encoding_true
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (hAll :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T →
        __smtx_value_canonical_bool v = true →
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true) :
    __smtx_model_eval M
        (SmtTerm.not (SmtTerm.exists s T (SmtTerm.not body))) =
      SmtValue.Boolean true := by
  classical
  have hNoSat :
      ¬ ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v)
            (SmtTerm.not body) = SmtValue.Boolean true := by
    rintro ⟨v, hvTy, hvCanonical, hvNot⟩
    have hvBody := hAll v hvTy hvCanonical
    simp [__smtx_model_eval, __smtx_model_eval_not, native_not,
      hvBody] at hvNot
  have hExistsEval :
      native_eval_texists M s T (SmtTerm.not body) =
        SmtValue.Boolean false := by
    change (if _h :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
          __smtx_value_canonical_bool v = true ∧
          __smtx_model_eval (native_model_push M s T v)
              (SmtTerm.not body) = SmtValue.Boolean true then
        SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean false
    rw [dif_neg hNoSat]
  change __smtx_model_eval_not
      (native_eval_texists M s T (SmtTerm.not body)) =
        SmtValue.Boolean true
  rw [hExistsEval]
  rfl

/-- A typed canonical counterexample makes the SMT encoding of EO `forall`
false. -/
private theorem sr_eval_forall_encoding_false
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm)
    (v : SmtValue)
    (hvTy : __smtx_typeof_value v = T)
    (hvCanonical : __smtx_value_canonical_bool v = true)
    (hvBody :
      __smtx_model_eval (native_model_push M s T v) body =
        SmtValue.Boolean false) :
    __smtx_model_eval M
        (SmtTerm.not (SmtTerm.exists s T (SmtTerm.not body))) =
      SmtValue.Boolean false := by
  classical
  have hvNot :
      __smtx_model_eval (native_model_push M s T v)
          (SmtTerm.not body) = SmtValue.Boolean true := by
    simp [__smtx_model_eval, __smtx_model_eval_not, native_not, hvBody]
  have hSat :
      ∃ w : SmtValue,
        __smtx_typeof_value w = T ∧
        __smtx_value_canonical_bool w = true ∧
        __smtx_model_eval (native_model_push M s T w)
            (SmtTerm.not body) = SmtValue.Boolean true :=
    ⟨v, hvTy, hvCanonical, hvNot⟩
  have hExistsEval :
      native_eval_texists M s T (SmtTerm.not body) =
        SmtValue.Boolean true := by
    change (if _h :
        ∃ w : SmtValue,
          __smtx_typeof_value w = T ∧
          __smtx_value_canonical_bool w = true ∧
          __smtx_model_eval (native_model_push M s T w)
              (SmtTerm.not body) = SmtValue.Boolean true then
        SmtValue.Boolean true else SmtValue.Boolean false) =
      SmtValue.Boolean true
    rw [dif_pos hSat]
  change __smtx_model_eval_not
      (native_eval_texists M s T (SmtTerm.not body)) =
        SmtValue.Boolean false
  rw [hExistsEval]
  rfl

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
      case str_to_int =>
        sorry
      case str_from_int =>
        sorry
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
          apply sr_eo_is_closed_apply_uop_arg UserOp.str_to_lower x
          · apply RuleProofs.term_ne_stuck_of_has_smt_translation
            simpa [RuleProofs.eo_has_smt_translation] using hXNN
          · exact hClosed
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
              __smtx_typeof_guard, __smtx_typeof,
              native_ite, native_Teq]
          · change __smtx_model_eval M
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len lowerS)) = SmtValue.Boolean true
            simp [lowerS, __smtx_model_eval, hXEvalString,
              __smtx_model_eval_str_len, __smtx_model_eval_str_to_lower,
              __smtx_model_eval__at_purify, __smtx_model_eval_eq,
              native_seq_len, native_str_to_lower,
              Smtm.native_unpack_pack_seq, sr_native_unpack_pack_string,
              sr_native_unpack_pack_string_length, List.length_map,
              native_veq]
        · apply RuleProofs.eo_interprets_and_intro M
          · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtType.Bool
              simp [qBody, expected, isUpper, lowerCode, origCode,
                lowerLen, lowerS, idx, smtx_typeof_exists_term_eq,
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
                sr_smt_type_wf_int,
                native_ite, native_Teq]
            · change __smtx_model_eval M
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtValue.Boolean true
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
                have hIdxEval :
                    native_model_var_lookup Mk idxName SmtType.Int =
                      SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
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
                    have hNotLenLe : ¬ Int.ofNat w.length ≤ k :=
                      Int.not_le_of_gt hklt
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hj : j < w.length := by
                      have h := hklt
                      rw [← hCast] at h
                      exact Int.ofNat_lt.mp h
                    have hCode := sr_lower_code_at w j hValid hj
                    rw [hCast] at hCode
                    simp [qBody, expected, isUpper, lowerCode, origCode,
                      lowerLen, lowerS, idx, __smtx_model_eval,
                      hXEvalPush, hIdxEval,
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
                      sr_native_unpack_pack_string_length, List.length_map,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hCode, hk0, hklt,
                      hNotLenLe]
                    right
                    rw [show List.map native_char_to_lower w =
                      native_str_to_lower w by rfl]
                    let c := native_str_to_code (native_str_substr w k 1)
                    by_cases hLo : 65 ≤ c
                    · by_cases hHi : c ≤ 90
                      · simpa [c, native_veq, hLo, hHi] using hCode
                      · simpa [c, native_veq, hLo, hHi] using hCode
                    · simpa [c, native_veq, hLo] using hCode
                  · have hLenLe : Int.ofNat w.length ≤ k :=
                      Int.le_of_not_gt hklt
                    simp [qBody, expected, isUpper, lowerCode, origCode,
                      lowerLen, lowerS, idx,
                      __smtx_model_eval, hXEvalPush,
                      hIdxEval,
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
                      sr_native_unpack_pack_string_length, List.length_map,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hk0, hklt, hLenLe]
                    left
                    simpa using hLenLe
                · have hkNeg : k < 0 := Int.lt_of_not_ge hk0
                  simp [qBody, expected, isUpper, lowerCode, origCode,
                    lowerLen, lowerS, idx, __smtx_model_eval,
                    hXEvalPush, hIdxEval,
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
                    sr_native_unpack_pack_string_length, List.length_map,
                    sr_native_seq_extract_pack_string,
                    sr_native_unpack_extract_pack_string,
                    hk0, hkNeg]
              exact sr_eval_forall_encoding_true M idxName SmtType.Int
                qBody hAll
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
          apply sr_eo_is_closed_apply_uop_arg UserOp.str_to_upper x
          · apply RuleProofs.term_ne_stuck_of_has_smt_translation
            simpa [RuleProofs.eo_has_smt_translation] using hXNN
          · exact hClosed
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
              __smtx_typeof_guard, __smtx_typeof,
              native_ite, native_Teq]
          · change __smtx_model_eval M
                (SmtTerm.eq (SmtTerm.str_len (__eo_to_smt x))
                  (SmtTerm.str_len upperS)) = SmtValue.Boolean true
            simp [upperS, __smtx_model_eval, hXEvalString,
              __smtx_model_eval_str_len, __smtx_model_eval_str_to_upper,
              __smtx_model_eval__at_purify, __smtx_model_eval_eq,
              native_seq_len, native_str_to_upper,
              Smtm.native_unpack_pack_seq, sr_native_unpack_pack_string,
              sr_native_unpack_pack_string_length, List.length_map,
              native_veq]
        · apply RuleProofs.eo_interprets_and_intro M
          · apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtType.Bool
              simp [qBody, expected, isLower, upperCode, origCode,
                upperLen, upperS, idx, smtx_typeof_exists_term_eq,
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
                sr_smt_type_wf_int,
                native_ite, native_Teq]
            · change __smtx_model_eval M
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtValue.Boolean true
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
                have hIdxEval :
                    native_model_var_lookup Mk idxName SmtType.Int =
                      SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
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
                    have hNotLenLe : ¬ Int.ofNat w.length ≤ k :=
                      Int.not_le_of_gt hklt
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hj : j < w.length := by
                      have h := hklt
                      rw [← hCast] at h
                      exact Int.ofNat_lt.mp h
                    have hCode := sr_upper_code_at w j hValid hj
                    rw [hCast] at hCode
                    simp [qBody, expected, isLower, upperCode, origCode,
                      upperLen, upperS, idx, __smtx_model_eval,
                      hXEvalPush, hIdxEval,
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
                      sr_native_unpack_pack_string_length, List.length_map,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hCode, hk0, hklt,
                      hNotLenLe]
                    right
                    rw [show List.map native_char_to_upper w =
                      native_str_to_upper w by rfl]
                    let c := native_str_to_code (native_str_substr w k 1)
                    by_cases hLo : 97 ≤ c
                    · by_cases hHi : c ≤ 122
                      · simpa [c, native_veq, hLo, hHi] using hCode
                      · simpa [c, native_veq, hLo, hHi] using hCode
                    · simpa [c, native_veq, hLo] using hCode
                  · have hLenLe : Int.ofNat w.length ≤ k :=
                      Int.le_of_not_gt hklt
                    simp [qBody, expected, isLower, upperCode, origCode,
                      upperLen, upperS, idx,
                      __smtx_model_eval, hXEvalPush,
                      hIdxEval,
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
                      sr_native_unpack_pack_string_length, List.length_map,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hk0, hklt, hLenLe]
                    left
                    simpa using hLenLe
                · have hkNeg : k < 0 := Int.lt_of_not_ge hk0
                  simp [qBody, expected, isLower, upperCode, origCode,
                    upperLen, upperS, idx, __smtx_model_eval,
                    hXEvalPush, hIdxEval,
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
                    sr_native_unpack_pack_string_length, List.length_map,
                    sr_native_seq_extract_pack_string,
                    sr_native_unpack_extract_pack_string,
                    hk0, hkNeg]
              exact sr_eval_forall_encoding_true M idxName SmtType.Int
                qBody hAll
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
          apply sr_eo_is_closed_apply_uop_arg UserOp.str_rev x
          · apply RuleProofs.term_ne_stuck_of_has_smt_translation
            simpa [RuleProofs.eo_has_smt_translation] using hXNN
          · exact hClosed
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
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtType.Bool
              simp [qBody, sliceEq, mirrorStart, revLen, revS, idx,
                smtx_typeof_exists_term_eq, typeof_or_eq, typeof_not_eq,
                typeof_geq_eq, typeof_lt_eq, typeof_eq_eq,
                typeof_str_len_eq, typeof_str_substr_eq, typeof_neg_eq,
                typeof_plus_eq, hxTy, hRevTy, __smtx_typeof,
                __smtx_typeof_seq_op_1, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_str_substr, __smtx_typeof_arith_overload_op_2,
                __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
                __smtx_typeof_guard_wf, __smtx_typeof_guard, hTWf,
                sr_smt_type_wf_int,
                native_ite, native_Teq]
            · change __smtx_model_eval M
                  (SmtTerm.not
                    (SmtTerm.exists idxName SmtType.Int
                      (SmtTerm.not qBody))) = SmtValue.Boolean true
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
                have hIdxEval :
                    native_model_var_lookup Mk idxName SmtType.Int =
                      SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
                have hXEvalPush :
                    __smtx_model_eval Mk (__eo_to_smt x) =
                      SmtValue.Seq sx := by
                  rw [← hXEval]
                  exact (smt_model_eval_eq_of_eo_closed x hXClosed M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                simp [qBody, sliceEq, mirrorStart, revLen, revS, idx,
                  __smtx_model_eval, hXEvalPush, hIdxEval,
                  __smtx_model_eval_or,
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
                by_cases hk0 : 0 ≤ k
                · by_cases hklt :
                      k < Int.ofNat (native_unpack_seq sx).length
                  · right
                    right
                    let j := Int.toNat k
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hj : j < (native_unpack_seq sx).length := by
                      have h := hklt
                      rw [← hCast] at h
                      exact Int.ofNat_lt.mp h
                    have hjSuccLe :
                        j + 1 ≤ (native_unpack_seq sx).length := by omega
                    have hMirrorCast :
                        Int.ofNat ((native_unpack_seq sx).length - (j + 1)) =
                          Int.ofNat (native_unpack_seq sx).length + -(k + 1) := by
                      calc
                        Int.ofNat ((native_unpack_seq sx).length - (j + 1)) =
                            Int.ofNat (native_unpack_seq sx).length -
                              Int.ofNat (j + 1) :=
                          Int.ofNat_sub hjSuccLe
                        _ = Int.ofNat (native_unpack_seq sx).length +
                              -(k + 1) := by
                          have hSuccCast :
                              Int.ofNat (j + 1) = Int.ofNat j + 1 := by
                            cases j <;> rfl
                          rw [hSuccCast, hCast, Int.sub_eq_add_neg]
                    apply congrArg (native_pack_seq T)
                    calc
                      native_seq_extract (native_unpack_seq sx).reverse k 1 =
                          native_seq_extract (native_unpack_seq sx).reverse
                            (Int.ofNat j) 1 := by rw [hCast]
                      _ = native_seq_extract (native_unpack_seq sx)
                            (Int.ofNat ((native_unpack_seq sx).length -
                              (j + 1))) 1 :=
                        sr_native_seq_extract_reverse_one
                          (native_unpack_seq sx) j hj
                      _ = native_seq_extract (native_unpack_seq sx)
                            (Int.ofNat (native_unpack_seq sx).length +
                              -(k + 1)) 1 := by rw [hMirrorCast]
                  · right
                    left
                    exact Int.le_of_not_gt hklt
                · left
                  exact Int.lt_of_not_ge hk0
              exact sr_eval_forall_encoding_true M idxName SmtType.Int
                qBody hAll
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
          rcases seq_binop_args_of_non_none_ret
              (op := SmtTerm.str_contains)
              (typeof_str_contains_eq ty tx) hOrigNN with
            ⟨T, hyTy, hxTy⟩
          have hYNN : term_has_non_none_type ty := by
            unfold term_has_non_none_type
            rw [hyTy]
            exact seq_ne_none T
          have hXNN : term_has_non_none_type tx := by
            unfold term_has_non_none_type
            rw [hxTy]
            exact seq_ne_none T
          have hContainsTy :
              __smtx_typeof (SmtTerm.str_contains ty tx) = SmtType.Bool := by
            rw [typeof_str_contains_eq, hyTy, hxTy]
            simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
          have hYValTy :
              __smtx_typeof_value (__smtx_model_eval M ty) =
                SmtType.Seq T := by
            simpa [hyTy] using
              smt_model_eval_preserves_type_of_non_none M hM ty hYNN
          have hXValTy :
              __smtx_typeof_value (__smtx_model_eval M tx) =
                SmtType.Seq T := by
            simpa [hxTy] using
              smt_model_eval_preserves_type_of_non_none M hM tx hXNN
          rcases seq_value_canonical hYValTy with ⟨sy, hYEval⟩
          rcases seq_value_canonical hXValTy with ⟨sx, hXEval⟩
          have hSyTy :
              __smtx_typeof_seq_value sy =
                SmtType.Seq T := by
            simpa [hYEval, __smtx_typeof_value] using hYValTy
          have hSxTy :
              __smtx_typeof_seq_value sx =
                SmtType.Seq T := by
            simpa [hXEval, __smtx_typeof_value] using hXValTy
          have hSyElem :
              __smtx_elem_typeof_seq_value sy = T :=
            elem_typeof_seq_value_of_typeof_seq_value hSyTy
          have hSxElem :
              __smtx_elem_typeof_seq_value sx = T :=
            elem_typeof_seq_value_of_typeof_seq_value hSxTy
          let ys := native_unpack_seq sy
          let xs := native_unpack_seq sx
          have hPackXAtY :
              native_pack_seq (__smtx_elem_typeof_seq_value sy) xs = sx := by
            rw [hSyElem, ← hSxElem]
            simpa [xs] using native_pack_unpack_seq sx
          have hClosedArgs :
              __eo_is_closed y = Term.Boolean true ∧
                __eo_is_closed x = Term.Boolean true := by
            apply sr_eo_is_closed_binary_uop_args UserOp.str_contains y x
            · decide
            · decide
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              simpa [ty, RuleProofs.eo_has_smt_translation] using hYNN
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              simpa [tx, RuleProofs.eo_has_smt_translation] using hXNN
            · exact hClosed
          let idxName := native_string_lit "@var.str_index"
          let idx := SmtTerm.Var idxName SmtType.Int
          let needleLen := SmtTerm.str_len tx
          let limit := SmtTerm.neg (SmtTerm.str_len ty) needleLen
          let slice := SmtTerm.str_substr ty idx needleLen
          let qBody := SmtTerm.or
            (SmtTerm.not (SmtTerm.geq idx (SmtTerm.Numeral 0)))
            (SmtTerm.or (SmtTerm.not (SmtTerm.leq idx limit))
              (SmtTerm.or (SmtTerm.not (SmtTerm.eq slice tx))
                (SmtTerm.Boolean false)))
          let forallEncoding :=
            SmtTerm.not
              (SmtTerm.exists idxName SmtType.Int (SmtTerm.not qBody))
          let containsResult :=
            SmtTerm._at_purify (SmtTerm.str_contains ty tx)
          let formula := SmtTerm.eq containsResult
            (SmtTerm.not forallEncoding)
          apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof formula = SmtType.Bool
            simp [formula, containsResult, forallEncoding, qBody, slice,
              limit, needleLen, idx, typeof_eq_eq, typeof_not_eq,
              smtx_typeof_exists_term_eq, typeof_or_eq, typeof_geq_eq,
              typeof_leq_eq, typeof_str_substr_eq, typeof_str_len_eq,
              typeof_neg_eq, hyTy, hxTy, hContainsTy,
              __smtx_typeof, __smtx_typeof_str_substr,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_seq_op_2_ret,
              __smtx_typeof_arith_overload_op_2,
              __smtx_typeof_arith_overload_op_2_ret,
              __smtx_typeof_eq, __smtx_typeof_guard_wf,
              __smtx_typeof_guard, sr_smt_type_wf_int,
              native_ite, native_Teq]
          · change __smtx_model_eval M formula = SmtValue.Boolean true
            have hContainsEval :
                __smtx_model_eval M containsResult =
                  SmtValue.Boolean (native_seq_contains ys xs) := by
              simp [containsResult, ty, tx, ys, xs, __smtx_model_eval,
                hYEval, hXEval, __smtx_model_eval__at_purify,
                __smtx_model_eval_str_contains]
            by_cases hContains : native_seq_contains ys xs = true
            · rcases (sr_native_seq_contains_iff_extract ys xs).1 hContains with
                ⟨j, hBound, hExtract⟩
              have hForallFalse :
                  __smtx_model_eval M forallEncoding =
                    SmtValue.Boolean false := by
                let Mj := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral (Int.ofNat j))
                have hIdxEval :
                    native_model_var_lookup Mj idxName SmtType.Int =
                      SmtValue.Numeral (Int.ofNat j) := by
                  simp [Mj, native_model_var_lookup, native_model_push]
                have hYEvalPush :
                    __smtx_model_eval Mj ty = SmtValue.Seq sy := by
                  rw [← hYEval]
                  exact (smt_model_eval_eq_of_eo_closed y hClosedArgs.1 M Mj
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral (Int.ofNat j)))).symm
                have hXEvalPush :
                    __smtx_model_eval Mj tx = SmtValue.Seq sx := by
                  rw [← hXEval]
                  exact (smt_model_eval_eq_of_eo_closed x hClosedArgs.2 M Mj
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral (Int.ofNat j)))).symm
                have hPatLe : xs.length ≤ ys.length := by
                  rcases
                      (StrContainsReplCharSupport.native_seq_contains_iff_decomp
                        ys xs).1 hContains with
                    ⟨before, after, hYs⟩
                  rw [hYs]
                  simp
                  omega
                have hLimitCast :
                    Int.ofNat ys.length - Int.ofNat xs.length =
                      Int.ofNat (ys.length - xs.length) :=
                  (Int.ofNat_sub hPatLe).symm
                have hIdxLe :
                    Int.ofNat j ≤
                      Int.ofNat ys.length - Int.ofNat xs.length := by
                  rw [hLimitCast]
                  exact Int.ofNat_le.mpr hBound
                have hIdxLeCast :
                    (j : Int) ≤
                      (ys.length : Int) + -(xs.length : Int) := by
                  rw [sr_int_natCast_eq_ofNat j,
                    sr_int_natCast_eq_ofNat ys.length,
                    sr_int_natCast_eq_ofNat xs.length,
                    ← Int.sub_eq_add_neg]
                  exact hIdxLe
                have hSliceEqEval :
                    __smtx_model_eval Mj (SmtTerm.eq slice tx) =
                      SmtValue.Boolean true := by
                  simp [slice, needleLen, idx, ys, xs, __smtx_model_eval,
                    hYEvalPush, hXEvalPush, hIdxEval,
                    __smtx_model_eval_eq, __smtx_model_eval_str_substr,
                    __smtx_model_eval_str_len, native_seq_len,
                    hExtract, hPackXAtY, native_veq]
                  rw [sr_int_natCast_eq_ofNat j,
                    sr_int_natCast_eq_ofNat xs.length, hExtract, hPackXAtY]
                have hSliceEqEval' :
                    __smtx_model_eval_eq (__smtx_model_eval Mj slice)
                        (SmtValue.Seq sx) = SmtValue.Boolean true := by
                  simpa [__smtx_model_eval, hXEvalPush] using hSliceEqEval
                have hAtFalse :
                    __smtx_model_eval Mj qBody =
                      SmtValue.Boolean false := by
                  simp [qBody, limit, needleLen, idx, ys, xs,
                    __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                    hSliceEqEval', __smtx_model_eval_or,
                    __smtx_model_eval_not, __smtx_model_eval_geq,
                    __smtx_model_eval_leq, __smtx_model_eval_str_len,
                    __smtx_model_eval__, native_seq_len, native_zleq,
                    native_zplus, native_zneg, native_and, native_or,
                    native_not, hIdxLe, hIdxLeCast]
                exact sr_eval_forall_encoding_false M idxName SmtType.Int
                  qBody (SmtValue.Numeral (Int.ofNat j)) rfl
                  (by simp [__smtx_value_canonical_bool]) hAtFalse
              simp [formula, __smtx_model_eval, hContainsEval, hContains,
                hForallFalse, __smtx_model_eval_eq,
                __smtx_model_eval_not, native_veq, native_not]
            · have hContainsFalse : native_seq_contains ys xs = false := by
                cases h : native_seq_contains ys xs
                · rfl
                · exact False.elim (hContains h)
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
                have hIdxEval :
                    native_model_var_lookup Mk idxName SmtType.Int =
                      SmtValue.Numeral k := by
                  simp [Mk, native_model_var_lookup, native_model_push]
                have hYEvalPush :
                    __smtx_model_eval Mk ty = SmtValue.Seq sy := by
                  rw [← hYEval]
                  exact (smt_model_eval_eq_of_eo_closed y hClosedArgs.1 M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                have hXEvalPush :
                    __smtx_model_eval Mk tx = SmtValue.Seq sx := by
                  rw [← hXEval]
                  exact (smt_model_eval_eq_of_eo_closed x hClosedArgs.2 M Mk
                    (model_agrees_on_globals_push M idxName SmtType.Int
                      (SmtValue.Numeral k))).symm
                change __smtx_model_eval Mk qBody = SmtValue.Boolean true
                by_cases hk0 : 0 ≤ k
                · by_cases hkLe :
                      k ≤ Int.ofNat ys.length - Int.ofNat xs.length
                  · let j := Int.toNat k
                    have hCast : Int.ofNat j = k := by
                      simpa [j] using Int.toNat_of_nonneg hk0
                    have hPatLe : xs.length ≤ ys.length := by
                      apply Nat.le_of_not_gt
                      intro hNotLe
                      have hNeg :
                          Int.ofNat ys.length - Int.ofNat xs.length < 0 := by
                        rw [← sr_int_natCast_eq_ofNat ys.length,
                          ← sr_int_natCast_eq_ofNat xs.length]
                        omega
                      exact Int.not_lt_of_ge hk0
                        (Int.lt_of_le_of_lt hkLe hNeg)
                    have hLimitCast :
                        Int.ofNat ys.length - Int.ofNat xs.length =
                          Int.ofNat (ys.length - xs.length) :=
                      (Int.ofNat_sub hPatLe).symm
                    have hBound : j ≤ ys.length - xs.length := by
                      apply Nat.le_of_not_gt
                      intro hNotLe
                      have hLt :
                          Int.ofNat (ys.length - xs.length) <
                            Int.ofNat j := Int.ofNat_lt.mpr hNotLe
                      rw [hCast, ← hLimitCast] at hLt
                      exact Int.not_lt_of_ge hkLe hLt
                    have hkLeCast :
                        k ≤ (ys.length : Int) + -(xs.length : Int) := by
                      rw [sr_int_natCast_eq_ofNat ys.length,
                        sr_int_natCast_eq_ofNat xs.length,
                        ← Int.sub_eq_add_neg]
                      exact hkLe
                    have hExtractNe :
                        native_seq_extract ys (Int.ofNat j)
                            (Int.ofNat xs.length) ≠ xs := by
                      intro hEq
                      have hTrue :=
                        (sr_native_seq_contains_iff_extract ys xs).2
                          ⟨j, hBound, hEq⟩
                      rw [hTrue] at hContainsFalse
                      contradiction
                    have hSliceEqEval :
                        __smtx_model_eval Mk (SmtTerm.eq slice tx) =
                          SmtValue.Boolean false := by
                      simp [slice, needleLen, idx, ys, xs,
                        __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                        __smtx_model_eval_eq, __smtx_model_eval_str_substr,
                        __smtx_model_eval_str_len, native_seq_len,
                        ← hCast, hExtractNe, hPackXAtY, native_veq]
                      rw [sr_int_natCast_eq_ofNat j,
                        sr_int_natCast_eq_ofNat xs.length]
                      intro hEq
                      apply hExtractNe
                      have hUnpack := congrArg native_unpack_seq hEq
                      simpa [xs, Smtm.native_unpack_pack_seq] using hUnpack
                    have hSliceEqEval' :
                        __smtx_model_eval_eq (__smtx_model_eval Mk slice)
                            (SmtValue.Seq sx) = SmtValue.Boolean false := by
                      simpa [__smtx_model_eval, hXEvalPush] using hSliceEqEval
                    simp [qBody, limit, needleLen, idx, ys, xs,
                      __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                      hSliceEqEval', __smtx_model_eval_or,
                      __smtx_model_eval_not, __smtx_model_eval_geq,
                      __smtx_model_eval_leq, __smtx_model_eval_str_len,
                      __smtx_model_eval__, native_seq_len, native_zleq,
                      native_zplus, native_zneg, native_and, native_or,
                      native_not, hk0, hkLe, hkLeCast]
                  · simp [qBody, limit, needleLen, idx, ys, xs,
                      __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                      __smtx_model_eval_or, __smtx_model_eval_not,
                      __smtx_model_eval_geq, __smtx_model_eval_leq,
                      __smtx_model_eval_eq, __smtx_model_eval_str_len,
                      __smtx_model_eval_str_substr, __smtx_model_eval__,
                      native_seq_len, native_zleq, native_zplus,
                      native_zneg, native_and, native_or, native_not,
                      hk0, hkLe]
                    left
                    rw [sr_int_natCast_eq_ofNat ys.length,
                      sr_int_natCast_eq_ofNat xs.length]
                    simpa [Int.sub_eq_add_neg] using Int.lt_of_not_ge hkLe
                · simp [qBody, limit, needleLen, idx, ys, xs,
                  __smtx_model_eval, hYEvalPush, hXEvalPush, hIdxEval,
                  __smtx_model_eval_or, __smtx_model_eval_not,
                  __smtx_model_eval_geq, __smtx_model_eval_leq,
                  __smtx_model_eval_eq, __smtx_model_eval_str_len,
                  __smtx_model_eval_str_substr, __smtx_model_eval__,
                  native_seq_len, native_zleq, native_zplus, native_zneg,
                  native_and, native_or, native_not, hk0]
              have hForallTrue :
                  __smtx_model_eval M forallEncoding =
                    SmtValue.Boolean true :=
                sr_eval_forall_encoding_true M idxName SmtType.Int qBody hAll
              simp [formula, __smtx_model_eval, hContainsEval,
                hContainsFalse, hForallTrue, __smtx_model_eval_eq,
                __smtx_model_eval_not, native_veq, native_not]
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
            apply sr_eo_is_closed_binary_uop_args UserOp.str_leq y x
            · decide
            · decide
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              simpa [ty, RuleProofs.eo_has_smt_translation] using hYNN
            · apply RuleProofs.term_ne_stuck_of_has_smt_translation
              simpa [tx, RuleProofs.eo_has_smt_translation] using hXNN
            · exact hClosed
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
          let forallEncoding :=
            SmtTerm.not
              (SmtTerm.exists idxName SmtType.Int (SmtTerm.not qBody))
          let formula := SmtTerm.ite (SmtTerm.eq ty tx) leqResult
            (SmtTerm.not forallEncoding)
          apply RuleProofs.eo_interprets_of_bool_eval M _ true
          · unfold RuleProofs.eo_has_bool_type
            change __smtx_typeof formula = SmtType.Bool
            simp [formula, forallEncoding, qBody, cmp, prefixEq, leqResult, tCode,
              sCode, idx, typeof_ite_eq, typeof_eq_eq, typeof_not_eq,
              smtx_typeof_exists_term_eq, typeof_or_eq, typeof_geq_eq,
              typeof_leq_eq, typeof_str_len_eq, typeof_str_substr_eq,
              typeof_str_to_code_eq, hyTy, hxTy, hLeqTy,
              __smtx_typeof, __smtx_typeof_seq_op_1,
              __smtx_typeof_seq_op_1_ret, __smtx_typeof_str_substr,
              __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
              __smtx_typeof_guard_wf, __smtx_typeof_guard,
              __smtx_typeof_ite, sr_smt_type_wf_int,
              native_ite, native_Teq]
          · change __smtx_model_eval M formula = SmtValue.Boolean true
            have hLeqEval :
                __smtx_model_eval M leqResult =
                  SmtValue.Boolean (sr_native_str_leq_bool ys xs) := by
              simp [leqResult, __smtx_model_eval, hYEvalString,
                hXEvalString, __smtx_model_eval__at_purify,
                __smtx_model_eval_str_leq, __smtx_model_eval_str_lt,
                __smtx_model_eval_eq, __smtx_model_eval_or,
                sr_native_str_leq_bool, sr_native_unpack_pack_string,
                sr_native_pack_string_eq_iff,
                native_veq, native_or]
            by_cases hEq : ys = xs
            · simp [formula, __smtx_model_eval, hYEvalString,
                hXEvalString, hLeqEval, __smtx_model_eval_ite,
                __smtx_model_eval_eq, sr_native_str_leq_bool,
                sr_native_pack_string_eq_iff,
                native_str_lt, native_veq, native_or, hEq]
            · rcases sr_native_str_leq_witness ys xs hYValid hXValid hEq with
                ⟨j, hjY, hjX, hPrefix, hCmp⟩
              have hForallFalse :
                  __smtx_model_eval M forallEncoding =
                    SmtValue.Boolean false := by
                let Mj := native_model_push M idxName SmtType.Int
                  (SmtValue.Numeral (Int.ofNat j))
                have hIdxEval :
                    native_model_var_lookup Mj idxName SmtType.Int =
                      SmtValue.Numeral (Int.ofNat j) := by
                  simp [Mj, native_model_var_lookup, native_model_push]
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
                    sr_native_pack_string_eq_iff,
                    native_veq, native_or]
                have hPrefixStringY :=
                  sr_native_str_substr_zero_nat ys j hjY
                have hPrefixStringX :=
                  sr_native_str_substr_zero_nat xs j hjX
                have hPrefixEval :
                    __smtx_model_eval Mj prefixEq =
                      SmtValue.Boolean true := by
                  simp [prefixEq, idx, __smtx_model_eval, hYEvalPush,
                    hXEvalPush, hIdxEval, __smtx_model_eval_eq,
                    __smtx_model_eval_str_substr,
                    Smtm.native_unpack_pack_seq,
                    sr_native_unpack_pack_string,
                    sr_native_pack_string_eq_iff,
                    sr_native_seq_extract_pack_string,
                    sr_native_seq_extract_pack_string_eval,
                    sr_native_unpack_extract_pack_string,
                    hPrefixStringY, hPrefixStringX, hPrefix, native_veq]
                  rw [sr_int_natCast_eq_ofNat j, hPrefixStringY,
                    hPrefixStringX, hPrefix]
                have hCmpEval :
                    __smtx_model_eval Mj cmp =
                      SmtValue.Boolean false := by
                  by_cases hLeqB : sr_native_str_leq_bool ys xs = true
                  · have hLt :
                        native_str_to_code
                            (native_str_substr ys (Int.ofNat j) 1) <
                          native_str_to_code
                            (native_str_substr xs (Int.ofNat j) 1) := by
                      simpa [hLeqB] using hCmp
                    have hNotLe := Int.not_le_of_gt hLt
                    simp [cmp, tCode, sCode, idx, __smtx_model_eval,
                      hYEvalPush, hXEvalPush, hLeqEvalPush, hIdxEval,
                      __smtx_model_eval_ite, __smtx_model_eval_geq,
                      __smtx_model_eval_leq,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code, native_zleq,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hLeqB, hNotLe]
                    rw [sr_int_natCast_eq_ofNat j]
                    exact hLt
                  · have hLt :
                        native_str_to_code
                            (native_str_substr xs (Int.ofNat j) 1) <
                          native_str_to_code
                            (native_str_substr ys (Int.ofNat j) 1) := by
                      simpa [hLeqB] using hCmp
                    have hNotLe := Int.not_le_of_gt hLt
                    simp [cmp, tCode, sCode, idx, __smtx_model_eval,
                      hYEvalPush, hXEvalPush, hLeqEvalPush, hIdxEval,
                      __smtx_model_eval_ite, __smtx_model_eval_geq,
                      __smtx_model_eval_leq,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_to_code, native_zleq,
                      Smtm.native_unpack_pack_seq,
                      sr_native_unpack_pack_string,
                      sr_native_seq_extract_pack_string,
                      sr_native_unpack_extract_pack_string,
                      hLeqB, hNotLe]
                    rw [sr_int_natCast_eq_ofNat j]
                    exact hLt
                have hAtFalse :
                    __smtx_model_eval Mj qBody =
                      SmtValue.Boolean false := by
                  simp [qBody, idx, __smtx_model_eval, hYEvalPush,
                    hXEvalPush, hIdxEval, hPrefixEval, hCmpEval,
                    __smtx_model_eval_or, __smtx_model_eval_not,
                    __smtx_model_eval_geq, __smtx_model_eval_leq,
                    __smtx_model_eval_str_len,
                    native_seq_len,
                    native_zleq, native_and, native_or, native_not,
                    Smtm.native_unpack_pack_seq,
                    sr_native_unpack_pack_string_length, List.length_map,
                    hjY, hjX]
                exact sr_eval_forall_encoding_false M idxName SmtType.Int
                  qBody (SmtValue.Numeral (Int.ofNat j)) rfl
                  (by simp [__smtx_value_canonical_bool]) hAtFalse
              simp [formula, __smtx_model_eval, hYEvalString,
                hXEvalString, hLeqEval, hForallFalse,
                __smtx_model_eval_ite, __smtx_model_eval_eq,
                __smtx_model_eval_not, native_veq, native_not,
                sr_native_unpack_pack_string,
                sr_native_pack_string_eq_iff, hEq]
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
          case str_substr =>
            have hOrigNN :
                term_has_non_none_type
                  (SmtTerm.str_substr (__eo_to_smt z) (__eo_to_smt y)
                    (__eo_to_smt x)) := by
              simpa [RuleProofs.eo_has_smt_translation] using hTrans
            rcases str_substr_args_of_non_none hOrigNN with
              ⟨T, hzTy, hyTy, hxTy⟩
            let pre := srPurify
              (Term.Apply
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z)
                  (Term.Numeral 0)) y)
            have hPreTy :
                __smtx_typeof (__eo_to_smt pre) = SmtType.Seq T := by
              change __smtx_typeof
                  (SmtTerm._at_purify
                    (SmtTerm.str_substr (__eo_to_smt z) (SmtTerm.Numeral 0)
                      (__eo_to_smt y))) = SmtType.Seq T
              simp [__smtx_typeof, typeof_str_substr_eq, hzTy, hyTy,
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
                            (Term.Apply (Term.UOp UserOp.str_substr) z)
                            (Term.Numeral 0)) y))) ≠
                  Term.Stuck := by
              simpa [pre] using hNilNe
            have hEmptyNe :
                __seq_empty (__eo_typeof z) ≠ Term.Stuck :=
              seq_empty_typeof_ne_stuck_of_smt_type_seq z T hzTy
            simp only [hNilNe', hEmptyNe, __eo_mk_apply] at hBodyTy ⊢
            have hTWf : __smtx_type_wf T = true :=
              (smt_seq_component_wf_of_non_none_type (__eo_to_smt z) T
                hzTy).2
            have hTInh : type_inhabited T :=
              (smt_seq_component_wf_of_non_none_type (__eo_to_smt z) T
                hzTy).1
            have hZNN : term_has_non_none_type (__eo_to_smt z) := by
              unfold term_has_non_none_type
              rw [hzTy]
              exact seq_ne_none T
            let tz := __eo_to_smt z
            let tn := __eo_to_smt y
            let tm := __eo_to_smt x
            let len := SmtTerm.str_len tz
            let mid := SmtTerm._at_purify (SmtTerm.str_substr tz tn tm)
            let next := SmtTerm.plus tn
              (SmtTerm.plus tm (SmtTerm.Numeral 0))
            let remaining := SmtTerm.neg len next
            let suffix := SmtTerm._at_purify
              (SmtTerm.str_substr tz next remaining)
            let preS := SmtTerm._at_purify
              (SmtTerm.str_substr tz (SmtTerm.Numeral 0) tn)
            let nilS := __eo_to_smt
              (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof pre))
            let emptyS := __eo_to_smt (__seq_empty (__eo_typeof z))
            let decomposition := SmtTerm.str_concat preS
              (SmtTerm.str_concat mid (SmtTerm.str_concat suffix nilS))
            let cond := SmtTerm.and (SmtTerm.geq tn (SmtTerm.Numeral 0))
              (SmtTerm.and (SmtTerm.gt len tn)
                (SmtTerm.and (SmtTerm.gt tm (SmtTerm.Numeral 0))
                  (SmtTerm.Boolean true)))
            let rhs := SmtTerm.and (SmtTerm.eq tz decomposition)
              (SmtTerm.and (SmtTerm.eq (SmtTerm.str_len preS) tn)
                (SmtTerm.and
                  (SmtTerm.or
                    (SmtTerm.eq (SmtTerm.str_len suffix) remaining)
                    (SmtTerm.or
                      (SmtTerm.eq (SmtTerm.str_len suffix)
                        (SmtTerm.Numeral 0))
                      (SmtTerm.Boolean false)))
                  (SmtTerm.and
                    (SmtTerm.leq (SmtTerm.str_len mid) tm)
                    (SmtTerm.Boolean true))))
            let formula := SmtTerm.ite cond rhs (SmtTerm.eq mid emptyS)
            have hEmptyNN : term_has_non_none_type emptyS := by
              simpa [emptyS] using
                seq_empty_typeof_has_smt_translation_of_smt_type_seq_wf
                  z T hzTy hTInh hTWf
            have hEmptyTy : __smtx_typeof emptyS = SmtType.Seq T := by
              simpa [emptyS] using
                smt_typeof_seq_empty_typeof z T hzTy hEmptyNN
            have hNilTy : __smtx_typeof nilS = SmtType.Seq T := by
              simpa [nilS, pre] using
                smt_typeof_nil_str_concat_typeof_of_smt_type_seq pre T hPreTy
            have hLenTy : __smtx_typeof len = SmtType.Int := by
              simp [len, tz, typeof_str_len_eq, hzTy,
                __smtx_typeof_seq_op_1_ret]
            have hNextTy : __smtx_typeof next = SmtType.Int := by
              simp [next, tn, tm, hyTy, hxTy, typeof_plus_eq,
                __smtx_typeof_arith_overload_op_2, __smtx_typeof]
            have hRemainingTy : __smtx_typeof remaining = SmtType.Int := by
              simp [remaining, hLenTy, hNextTy, typeof_neg_eq,
                __smtx_typeof_arith_overload_op_2]
            have hMidTy : __smtx_typeof mid = SmtType.Seq T := by
              change __smtx_typeof (SmtTerm.str_substr tz tn tm) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, tz, tn, tm, hzTy, hyTy, hxTy,
                __smtx_typeof_str_substr]
            have hPrefixTy : __smtx_typeof preS = SmtType.Seq T := by
              simpa [preS, tz, tn, pre] using hPreTy
            have hSuffixTy : __smtx_typeof suffix = SmtType.Seq T := by
              change __smtx_typeof (SmtTerm.str_substr tz next remaining) =
                SmtType.Seq T
              simp [typeof_str_substr_eq, tz, hzTy, hNextTy,
                hRemainingTy, __smtx_typeof_str_substr]
            have hDecompositionTy :
                __smtx_typeof decomposition = SmtType.Seq T := by
              simp [decomposition, typeof_str_concat_eq, hPrefixTy, hMidTy,
                hSuffixTy, hNilTy, __smtx_typeof_seq_op_2, native_ite,
                native_Teq]
            have hCondTy : __smtx_typeof cond = SmtType.Bool := by
              simp [cond, typeof_and_eq, typeof_geq_eq, typeof_gt_eq,
                hLenTy, tn, tm, hyTy, hxTy,
                __smtx_typeof_arith_overload_op_2_ret,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            have hRhsTy : __smtx_typeof rhs = SmtType.Bool := by
              simp [rhs, typeof_and_eq, typeof_or_eq, typeof_eq_eq,
                typeof_leq_eq, typeof_str_len_eq, tz, tn, tm, hzTy, hyTy,
                hxTy, hDecompositionTy, hPrefixTy, hMidTy, hSuffixTy,
                hRemainingTy, __smtx_typeof_seq_op_1_ret,
                __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_eq,
                __smtx_typeof_guard, __smtx_typeof, native_ite, native_Teq]
            apply RuleProofs.eo_interprets_of_bool_eval M _ true
            · unfold RuleProofs.eo_has_bool_type
              change __smtx_typeof formula = SmtType.Bool
              simp [formula, typeof_ite_eq, typeof_eq_eq, hCondTy, hRhsTy,
                hMidTy, hEmptyTy, __smtx_typeof_ite, __smtx_typeof_eq,
                __smtx_typeof_guard, native_ite, native_Teq]
            · change __smtx_model_eval M formula = SmtValue.Boolean true
              have hZValTy :
                  __smtx_typeof_value (__smtx_model_eval M tz) =
                    SmtType.Seq T := by
                simpa [tz, hzTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt z) hZNN
              rcases seq_value_canonical hZValTy with ⟨sz, hZEval⟩
              have hNNN : term_has_non_none_type tn := by
                unfold term_has_non_none_type
                rw [show __smtx_typeof tn = SmtType.Int by
                  simpa [tn] using hyTy]
                decide
              have hNValTy :
                  __smtx_typeof_value (__smtx_model_eval M tn) =
                    SmtType.Int := by
                simpa [tn, hyTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt y) (by simpa [tn] using hNNN)
              rcases int_value_canonical hNValTy with ⟨n, hNEval⟩
              have hMNN : term_has_non_none_type tm := by
                unfold term_has_non_none_type
                rw [show __smtx_typeof tm = SmtType.Int by
                  simpa [tm] using hxTy]
                decide
              have hMValTy :
                  __smtx_typeof_value (__smtx_model_eval M tm) =
                    SmtType.Int := by
                simpa [tm, hxTy] using
                  smt_model_eval_preserves_type_of_non_none M hM
                    (__eo_to_smt x) (by simpa [tm] using hMNN)
              rcases int_value_canonical hMValTy with ⟨m, hMEval⟩
              have hNilEval :
                  __smtx_model_eval M nilS =
                    SmtValue.Seq (SmtSeq.empty T) := by
                simpa [nilS, pre] using
                  eval_nil_str_concat_typeof_of_smt_type_seq M pre T hPreTy
              have hEmptyEval :
                  __smtx_model_eval M emptyS =
                    SmtValue.Seq (SmtSeq.empty T) := by
                simpa [emptyS] using eval_seq_empty_typeof M z T hzTy
              have hSzTy : __smtx_typeof_seq_value sz = SmtType.Seq T := by
                simpa [hZEval, __smtx_typeof_value] using hZValTy
              have hElemTy : __smtx_elem_typeof_seq_value sz = T :=
                elem_typeof_seq_value_of_typeof_seq_value hSzTy
              let xs := native_unpack_seq sz
              have hPack : native_pack_seq T xs = sz := by
                simpa [xs, hElemTy] using native_pack_unpack_seq sz
              dsimp [xs] at hPack
              by_cases hi : 0 ≤ n
              · by_cases hiLen : n < Int.ofNat xs.length
                · by_cases hm : 0 < m
                  · rcases sr_native_seq_extract_active_facts xs n m
                        hi hiLen hm with
                      ⟨hDecomp, hPreLen, hSuffixLen, hMidLen⟩
                    dsimp [xs] at hiLen hDecomp hPreLen hSuffixLen hMidLen
                    rcases hSuffixLen with hSuffixLen | hSuffixLen
                    all_goals
                      simp [formula, cond, rhs, decomposition, preS, mid,
                        suffix, remaining, next, len, __smtx_model_eval,
                        __smtx_model_eval_ite, __smtx_model_eval_and,
                        __smtx_model_eval_or, __smtx_model_eval_eq,
                        __smtx_model_eval_geq, __smtx_model_eval_gt,
                        __smtx_model_eval_lt, __smtx_model_eval_leq,
                        __smtx_model_eval_str_len,
                        __smtx_model_eval_str_substr,
                        __smtx_model_eval_str_concat,
                        __smtx_model_eval__at_purify,
                        __smtx_model_eval_plus, __smtx_model_eval__, hZEval,
                        hNEval, hMEval, hNilEval, hEmptyEval, native_seq_len,
                        native_seq_concat, native_and, native_or, native_not,
                        native_zleq, native_zlt, native_zplus, native_zneg,
                        Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                        native_unpack_seq, xs, hElemTy, hi, hiLen, hm, hPack,
                        hDecomp, hPreLen, hSuffixLen, hMidLen, native_veq,
                        native_pack_seq]
                    all_goals
                      constructor
                      · simpa [List.append_assoc, Int.sub_eq_add_neg] using
                          hPack.symm.trans
                            (congrArg (native_pack_seq T) hDecomp.symm)
                      · first
                        | left
                          simpa [Int.sub_eq_add_neg] using hSuffixLen
                        | right
                          simpa [Int.sub_eq_add_neg] using hSuffixLen
                  · have hInactive :
                        ¬ (0 ≤ n ∧ n < Int.ofNat xs.length ∧ 0 < m) := by
                      rintro ⟨_hi, _hiLen, hm'⟩
                      exact hm hm'
                    have hExtract :=
                      sr_native_seq_extract_empty_of_inactive xs n m hInactive
                    dsimp [xs] at hiLen hExtract
                    simp [formula, cond, rhs, decomposition, preS, mid,
                      suffix, remaining, next, len, __smtx_model_eval,
                      __smtx_model_eval_ite, __smtx_model_eval_and,
                      __smtx_model_eval_or, __smtx_model_eval_eq,
                      __smtx_model_eval_geq, __smtx_model_eval_gt,
                      __smtx_model_eval_lt, __smtx_model_eval_leq,
                      __smtx_model_eval_str_len,
                      __smtx_model_eval_str_substr,
                      __smtx_model_eval_str_concat,
                      __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                      __smtx_model_eval__, hZEval, hNEval, hMEval, hNilEval,
                      hEmptyEval, native_seq_len, native_seq_concat,
                      native_and, native_or, native_not, native_zleq,
                      native_zlt, native_zplus, native_zneg,
                      Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                      native_unpack_seq, xs, hElemTy, hi, hiLen, hm,
                      hExtract, native_veq, native_pack_seq]
                · have hInactive :
                      ¬ (0 ≤ n ∧ n < Int.ofNat xs.length ∧ 0 < m) := by
                    rintro ⟨_hi, hiLen', _hm⟩
                    exact hiLen hiLen'
                  have hExtract :=
                    sr_native_seq_extract_empty_of_inactive xs n m hInactive
                  dsimp [xs] at hiLen hExtract
                  simp [formula, cond, rhs, decomposition, preS, mid, suffix,
                    remaining, next, len, __smtx_model_eval,
                    __smtx_model_eval_ite, __smtx_model_eval_and,
                    __smtx_model_eval_or, __smtx_model_eval_eq,
                    __smtx_model_eval_geq, __smtx_model_eval_gt,
                    __smtx_model_eval_lt, __smtx_model_eval_leq,
                    __smtx_model_eval_str_len,
                    __smtx_model_eval_str_substr,
                    __smtx_model_eval_str_concat,
                    __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                    __smtx_model_eval__, hZEval, hNEval, hMEval, hNilEval,
                    hEmptyEval, native_seq_len, native_seq_concat,
                    native_and, native_or, native_not, native_zleq,
                    native_zlt, native_zplus, native_zneg,
                    Smtm.native_unpack_pack_seq, elem_typeof_pack_seq,
                    native_unpack_seq, xs, hElemTy, hi, hiLen, hExtract,
                    native_veq, native_pack_seq]
              · have hInactive :
                    ¬ (0 ≤ n ∧ n < Int.ofNat xs.length ∧ 0 < m) := by
                  rintro ⟨hi', _hiLen, _hm⟩
                  exact hi hi'
                have hExtract :=
                  sr_native_seq_extract_empty_of_inactive xs n m hInactive
                dsimp [xs] at hExtract
                simp [formula, cond, rhs, decomposition, preS, mid, suffix,
                  remaining, next, len, __smtx_model_eval,
                  __smtx_model_eval_ite, __smtx_model_eval_and,
                  __smtx_model_eval_or, __smtx_model_eval_eq,
                  __smtx_model_eval_geq, __smtx_model_eval_gt,
                  __smtx_model_eval_lt, __smtx_model_eval_leq,
                  __smtx_model_eval_str_len,
                  __smtx_model_eval_str_substr,
                  __smtx_model_eval_str_concat,
                  __smtx_model_eval__at_purify, __smtx_model_eval_plus,
                  __smtx_model_eval__, hZEval, hNEval, hMEval, hNilEval,
                  hEmptyEval, native_seq_len, native_seq_concat, native_and,
                  native_or, native_not, native_zleq, native_zlt,
                  native_zplus, native_zneg, Smtm.native_unpack_pack_seq,
                  elem_typeof_pack_seq, native_unpack_seq, xs, hElemTy, hi,
                  hExtract, native_veq, native_pack_seq]
          case str_replace =>
            sorry
          case str_indexof =>
            sorry
          case str_update =>
            sorry
          case str_replace_all =>
            sorry
          case str_replace_re =>
            sorry
          case str_replace_re_all =>
            sorry
          case str_indexof_re =>
            sorry

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
    rw [← is_closed_rec_eq_eo_is_closed_of_has_smt_translation hTrans]
    exact hClosedRec
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
