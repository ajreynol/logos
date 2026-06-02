import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.RuleSupport.StrConcatSupport
import Cpc.Proofs.RuleSupport.StringSupport
import Cpc.Proofs.RuleSupport.NativeSeqSupport
import Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

/-- Model-evaluation characterization of `str.contains`: when both arguments
    evaluate to sequence values, `str.contains x y` evaluates to the Boolean
    `native_seq_contains` of the underlying element lists. -/
theorem strContains_eval_eq (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y)) =
      SmtValue.Boolean
        (native_seq_contains (native_unpack_seq sx) (native_unpack_seq sy)) := by
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y) =
      SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y) by rfl]
  rw [show __smtx_model_eval M (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_str_contains (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) by simp only [__smtx_model_eval]]
  rw [hx, hy]
  rfl

/-- Model-evaluation characterization of `str.++`: when both arguments evaluate
    to sequence values, `str.++ x y` evaluates to a sequence whose underlying
    element list is the concatenation of the two argument element lists. -/
theorem strConcat_unpack_eval (M : SmtModel) (x y : Term) (sx sy : SmtSeq)
    (hx : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hy : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) :
    ∃ sxy,
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y)) =
        SmtValue.Seq sxy ∧
      native_unpack_seq sxy = native_unpack_seq sx ++ native_unpack_seq sy := by
  have h := smtx_model_eval_str_concat_term_eq M x y
  simp only [mkConcat] at h
  rw [h, hx, hy]
  refine ⟨_, rfl, ?_⟩
  simp [native_seq_concat, native_unpack_pack_seq]

/-! ### Native `contains` characterization and monotonicity -/

/-- A pattern is a prefix of itself followed by anything. -/
theorem native_seq_prefix_eq_append (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil => rfl
  | cons p ps ih =>
      have hp : native_veq p p = true := by simp [native_veq]
      simp [native_seq_prefix_eq, hp, ih]

/-- If `pat` occurs in `before ++ pat ++ after`, the bounded search does not
    return `-1` (provided there is enough fuel to reach the occurrence). -/
theorem native_seq_indexof_rec_append_ne_neg
    (pat after : List SmtValue) :
    ∀ (before : List SmtValue) (i fuel : Nat),
      before.length < fuel →
      native_seq_indexof_rec (before ++ pat ++ after) pat i fuel ≠ -1 := by
  intro before
  induction before with
  | nil =>
      intro i fuel hFuel
      cases fuel with
      | zero => simp at hFuel
      | succ f =>
          simp only [List.nil_append]
          unfold native_seq_indexof_rec
          rw [if_pos (native_seq_prefix_eq_append pat after)]
          simp
  | cons b bs ih =>
      intro i fuel hFuel
      cases fuel with
      | zero => simp at hFuel
      | succ f =>
          have hbs : bs.length < f := by
            simp only [List.length_cons] at hFuel; omega
          unfold native_seq_indexof_rec
          by_cases hPre : native_seq_prefix_eq pat ((b :: bs) ++ pat ++ after) = true
          · rw [if_pos hPre]; simp
          · rw [if_neg hPre]
            have hxs : (b :: bs) ++ pat ++ after = b :: (bs ++ pat ++ after) := by
              simp
            rw [hxs]
            simpa using ih (i + 1) f hbs

/-- Occurrence direction: if `xs` decomposes as `before ++ pat ++ after`, then
    `native_seq_contains xs pat` holds. -/
theorem native_seq_contains_of_decomp (before pat after : List SmtValue) :
    native_seq_contains (before ++ pat ++ after) pat = true := by
  have hLen : pat.length ≤ (before ++ pat ++ after).length := by
    simp [List.length_append]; omega
  have hNe :
      native_seq_indexof (before ++ pat ++ after) pat 0 ≠ -1 := by
    unfold native_seq_indexof
    simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add]
    rw [dif_pos hLen]
    have hFuel :
        before.length <
          (before ++ pat ++ after).length - pat.length + 1 := by
      simp [List.length_append]; omega
    simpa using
      native_seq_indexof_rec_append_ne_neg pat after before 0
        ((before ++ pat ++ after).length - pat.length + 1) hFuel
  have hGe :
      0 ≤ native_seq_indexof (before ++ pat ++ after) pat 0 := by
    rcases native_seq_indexof_eq_neg_one_or_ge (before ++ pat ++ after) pat 0 with h | h
    · exact absurd h hNe
    · exact h
  unfold native_seq_contains
  exact decide_eq_true hGe

/-- Forward direction: a positive `contains` yields an explicit decomposition. -/
theorem native_seq_contains_decomp_exists (xs pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    ∃ before after, xs = before ++ pat ++ after := by
  have hGe : 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at h
    exact of_decide_eq_true h
  exact ⟨_, _, (native_seq_indexof_zero_decomp xs pat hGe).symm⟩

/-- `contains` characterization in terms of list decomposition. -/
theorem native_seq_contains_iff_decomp (xs pat : List SmtValue) :
    native_seq_contains xs pat = true ↔ ∃ before after, xs = before ++ pat ++ after := by
  constructor
  · exact native_seq_contains_decomp_exists xs pat
  · rintro ⟨before, after, rfl⟩
    exact native_seq_contains_of_decomp before pat after

/-- Appending on the right preserves `contains`. -/
theorem native_seq_contains_append_right (xs rest pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    native_seq_contains (xs ++ rest) pat = true := by
  rcases native_seq_contains_decomp_exists xs pat h with ⟨before, after, rfl⟩
  have : before ++ pat ++ after ++ rest = before ++ pat ++ (after ++ rest) := by
    simp [List.append_assoc]
  rw [this]
  exact native_seq_contains_of_decomp before pat (after ++ rest)

/-- Appending on the left preserves `contains`. -/
theorem native_seq_contains_append_left (pre xs pat : List SmtValue)
    (h : native_seq_contains xs pat = true) :
    native_seq_contains (pre ++ xs) pat = true := by
  rcases native_seq_contains_decomp_exists xs pat h with ⟨before, after, rfl⟩
  have : pre ++ (before ++ pat ++ after) = (pre ++ before) ++ pat ++ after := by
    simp [List.append_assoc]
  rw [this]
  exact native_seq_contains_of_decomp (pre ++ before) pat after

/-! ### Prefix / compatibility lemmas -/

/-- `native_seq_prefix_eq a b` holds iff `a` is a list-prefix of `b`. -/
theorem native_seq_prefix_eq_iff (a b : List SmtValue) :
    native_seq_prefix_eq a b = true ↔ ∃ r, b = a ++ r := by
  constructor
  · intro h
    exact ⟨b.drop a.length, (native_seq_prefix_eq_append_drop a b h).symm⟩
  · rintro ⟨r, rfl⟩
    exact native_seq_prefix_eq_append a r

/-- Two lists are *overlap-compatible* if one is a prefix of the other. -/
def native_seq_compat (a b : List SmtValue) : Prop :=
  native_seq_prefix_eq a b = true ∨ native_seq_prefix_eq b a = true

/-- If two lists agree after appending (aligned at the front), then one of their
    heads is a prefix of the other. -/
theorem native_seq_compat_of_append_eq (a s d t : List SmtValue)
    (h : a ++ s = d ++ t) : native_seq_compat a d := by
  rcases Nat.le_total a.length d.length with hle | hle
  · left
    rw [native_seq_prefix_eq_iff]
    have h1 : (a ++ s).take a.length = (d ++ t).take a.length := by rw [h]
    rw [List.take_left, List.take_append_of_le_length hle] at h1
    refine ⟨d.drop a.length, ?_⟩
    have h2 : d.take a.length ++ d.drop a.length = d := List.take_append_drop a.length d
    rw [← h1] at h2
    exact h2.symm
  · right
    rw [native_seq_prefix_eq_iff]
    have h1 : (d ++ t).take d.length = (a ++ s).take d.length := by rw [h]
    rw [List.take_left, List.take_append_of_le_length hle] at h1
    refine ⟨a.drop d.length, ?_⟩
    have h2 : a.take d.length ++ a.drop d.length = a := List.take_append_drop d.length a
    rw [← h1] at h2
    exact h2.symm

/-! ### Window lemmas: occurrence survives `take`/`drop` -/

/-- An occurrence wholly contained in a `take k` prefix survives the truncation. -/
theorem native_seq_contains_take_of_decomp
    (before pat after : List SmtValue) (k : Nat)
    (hk : before.length + pat.length ≤ k) :
    native_seq_contains ((before ++ pat ++ after).take k) pat = true := by
  obtain ⟨m, hm⟩ : ∃ m, k = (before ++ pat).length + m :=
    ⟨k - (before ++ pat).length, by simp [List.length_append] at hk ⊢; omega⟩
  rw [hm, List.take_length_add_append]
  exact native_seq_contains_of_decomp before pat (after.take m)

/-- An occurrence wholly after the first `k` elements survives `drop k`. -/
theorem native_seq_contains_drop_of_decomp
    (before pat after : List SmtValue) (k : Nat)
    (hk : k ≤ before.length) :
    native_seq_contains ((before ++ pat ++ after).drop k) pat = true := by
  rw [List.append_assoc, List.drop_append_of_le_length hk, ← List.append_assoc]
  exact native_seq_contains_of_decomp (before.drop k) pat after

/-! ### The combinatorial core: no cross-boundary occurrence -/

/-- **Overlap split for `contains`.**

If no nonempty suffix of `C` is overlap-compatible with `D` (`hA`), and no
nonempty suffix of `D` is overlap-compatible with `C` (`hB`), then `D` cannot
occur straddling the middle block `C`: any occurrence of `D` in `T ++ C ++ S`
lies entirely within `T` or entirely within `S`. -/
theorem native_seq_contains_split_of_no_overlap
    (T C S D : List SmtValue)
    (hA : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D)
    (hB : ∀ k, k < D.length → ¬ native_seq_compat (D.drop k) C)
    (h : native_seq_contains (T ++ C ++ S) D = true) :
    native_seq_contains T D = true ∨ native_seq_contains S D = true := by
  rcases native_seq_contains_decomp_exists (T ++ C ++ S) D h with ⟨before, after, hEq⟩
  -- The occurrence starts at position `before.length`.
  have e1 : (before ++ D ++ after).drop before.length = D ++ after := by
    rw [List.append_assoc before D after]; exact List.drop_left
  have hdropT : (T ++ C ++ S).drop T.length = C ++ S := by
    rw [List.append_assoc]; exact List.drop_left
  by_cases h1 : before.length + D.length ≤ T.length
  · -- window within `T`
    left
    have hTtake : (before ++ D ++ after).take T.length = T := by
      rw [← hEq, List.append_assoc]; exact List.take_left
    have hwin := native_seq_contains_take_of_decomp before D after T.length h1
    rw [hTtake] at hwin
    exact hwin
  · by_cases h2 : T.length + C.length ≤ before.length
    · -- window within `S`
      right
      have hSdrop : (before ++ D ++ after).drop (T.length + C.length) = S := by
        rw [← hEq,
          show T.length + C.length = (T ++ C).length by rw [List.length_append]]
        exact List.drop_left
      have hwin := native_seq_contains_drop_of_decomp before D after (T.length + C.length) h2
      rw [hSdrop] at hwin
      exact hwin
    · -- window straddles `C`: contradiction
      exfalso
      by_cases hpT : T.length ≤ before.length
      · -- starts inside `C`
        obtain ⟨j, hpj⟩ : ∃ j, before.length = T.length + j :=
          ⟨before.length - T.length, by omega⟩
        have hjlt : j < C.length := by omega
        have e2 : (before ++ D ++ after).drop before.length = C.drop j ++ S := by
          rw [← hEq, hpj, ← List.drop_drop, hdropT,
            List.drop_append_of_le_length (Nat.le_of_lt hjlt)]
        have hAppend : C.drop j ++ S = D ++ after := by rw [← e2]; exact e1
        exact hA j hjlt (native_seq_compat_of_append_eq (C.drop j) S D after hAppend)
      · -- starts inside `T`, extends into `C`
        obtain ⟨m, hTm⟩ : ∃ m, T.length = before.length + m :=
          ⟨T.length - before.length, by omega⟩
        have hmlt : m < D.length := by omega
        have e3 : (before ++ D ++ after).drop T.length = D.drop m ++ after := by
          rw [hTm, ← List.drop_drop, e1,
            List.drop_append_of_le_length (Nat.le_of_lt hmlt)]
        have hAppend : D.drop m ++ after = C ++ S := by
          rw [← e3, ← hEq]; exact hdropT
        exact hB m hmlt (native_seq_compat_of_append_eq (D.drop m) after C S hAppend)

/-- Full `contains` split equivalence under the no-overlap conditions. -/
theorem native_seq_contains_split_iff_of_no_overlap
    (T C S D : List SmtValue)
    (hA : ∀ k, k < C.length → ¬ native_seq_compat (C.drop k) D)
    (hB : ∀ k, k < D.length → ¬ native_seq_compat (D.drop k) C) :
    native_seq_contains (T ++ C ++ S) D = true ↔
      (native_seq_contains T D = true ∨ native_seq_contains S D = true) := by
  constructor
  · exact native_seq_contains_split_of_no_overlap T C S D hA hB
  · rintro (hT | hS)
    · rw [List.append_assoc]
      exact native_seq_contains_append_right T (C ++ S) D hT
    · exact native_seq_contains_append_left (T ++ C) S D hS

/-! ### Bridge: `value_len` / `flatten` / `overlap_rec` term-computations

The rule's side conditions are EO term-level computations on the (flattened)
word arguments.  `__str_flatten (__str_nary_intro ·)` normalizes a word literal
into a canonical single-character `str.++`-chain (`charChainTerm`), on which
`__str_overlap_rec` computes the overlap "drop count" (`overlapDrop`) and
`__str_is_compatible` computes list prefix-compatibility. -/

/-- Canonical single-character `str.++` chain produced by `flatten`. -/
def charChainTerm : native_String → Term
  | [] => Term.String []
  | ch :: rest =>
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [ch]))
        (charChainTerm rest)

/-- Char-list overlap-compatibility: one is a prefix of the other. -/
def strCompat (x y : native_String) : Bool :=
  native_string_prefix_eq x y || native_string_prefix_eq y x

/-- The "overlap drop count": leading chars dropped from `x` until a suffix is
    compatible with `y`. -/
def overlapDrop : native_String → native_String → Nat
  | [], _ => 0
  | a :: x, y => if strCompat (a :: x) y then 0 else 1 + overlapDrop x y

theorem strChar_typeof (a : Nat) :
    __eo_typeof (Term.String [a]) =
      Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  rw [show __eo_typeof (Term.String [a]) = __eo_lit_type_String (Term.String [a]) from rfl]
  simp [__eo_lit_type_String]

theorem strChar_is_str (a : Nat) : __eo_is_str (Term.String [a]) = Term.Boolean true := by
  simp [__eo_is_str, __eo_is_str_internal, native_teq, SmtEval.native_and, SmtEval.native_not]

theorem strChar_eq (a b : Nat) :
    __eo_eq (Term.String [a]) (Term.String [b]) = Term.Boolean (decide (a = b)) := by
  simp [__eo_eq, native_teq]; rw [eq_comm]

theorem charChainTerm_ne_stuck (y : native_String) : charChainTerm y ≠ Term.Stuck := by
  cases y <;> simp [charChainTerm]

theorem overlap_rec_concat (s s1 t : Term) (ht : t ≠ Term.Stuck) :
    __str_overlap_rec (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) s1) t =
      __eo_ite (__str_is_compatible (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) s1) t)
        (Term.Numeral 0) (__eo_add (Term.Numeral 1) (__str_overlap_rec s1 t)) := by
  cases t <;> simp_all [__str_overlap_rec]

theorem overlap_rec_emptyfirst (t : Term) (ht : t ≠ Term.Stuck) :
    __str_overlap_rec (Term.String []) t = Term.Numeral 0 := by
  cases t <;> simp_all [__str_overlap_rec]

/-- `is_compatible` on char-chains computes list prefix-compatibility. -/
theorem str_is_compatible_charChain (x y : native_String) :
    __str_is_compatible (charChainTerm x) (charChainTerm y) =
      Term.Boolean (native_string_prefix_eq x y || native_string_prefix_eq y x) := by
  induction x generalizing y with
  | nil =>
      cases y <;>
        simp [charChainTerm, __str_is_compatible, __eo_l_1___str_is_compatible,
          __str_is_empty, __eo_or, native_string_prefix_eq, native_teq, SmtEval.native_ite,
          SmtEval.native_or]
  | cons a x ih =>
      cases y with
      | nil =>
          simp [charChainTerm, __str_is_compatible, __eo_l_1___str_is_compatible,
            __str_is_empty, __eo_or, native_string_prefix_eq, native_teq, SmtEval.native_ite,
            SmtEval.native_or]
      | cons b y =>
          by_cases hab : a = b
          · subst hab
            simp [charChainTerm, __str_is_compatible, strChar_eq, native_teq,
              SmtEval.native_ite, ih y, native_string_prefix_eq]
          · have hba : b ≠ a := fun h => hab h.symm
            simp [charChainTerm, __str_is_compatible, strChar_eq, decide_eq_false hab,
              native_teq, SmtEval.native_ite, __eo_l_1___str_is_compatible, __eo_requires,
              strChar_typeof, __are_distinct_terms_type, __eo_and, strChar_is_str,
              native_string_prefix_eq, SmtEval.native_and, SmtEval.native_not, hba]

/-- `overlap_rec` on char-chains computes the overlap drop count. -/
theorem str_overlap_rec_charChain (x y : native_String) :
    __str_overlap_rec (charChainTerm x) (charChainTerm y) =
      Term.Numeral (Int.ofNat (overlapDrop x y)) := by
  induction x with
  | nil => simp [charChainTerm, overlapDrop, overlap_rec_emptyfirst _ (charChainTerm_ne_stuck y)]
  | cons a x ih =>
      rw [show charChainTerm (a :: x) =
            Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [a]))
              (charChainTerm x) from rfl,
        overlap_rec_concat _ _ _ (charChainTerm_ne_stuck y),
        show (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) (Term.String [a]))
              (charChainTerm x)) = charChainTerm (a :: x) from rfl,
        str_is_compatible_charChain (a :: x) y,
        show (native_string_prefix_eq (a :: x) y || native_string_prefix_eq y (a :: x)) =
          strCompat (a :: x) y from rfl]
      cases hbc : strCompat (a :: x) y with
      | true => simp [__eo_ite, native_teq, SmtEval.native_ite, overlapDrop, hbc]
      | false =>
          simp only [overlapDrop, hbc, if_false]
          simp [__eo_ite, native_teq, SmtEval.native_ite, ih, __eo_add, native_zplus]

/-- `value_len` of a string literal is its length. -/
theorem str_value_len_string (w : native_String) :
    __str_value_len (Term.String w) = Term.Numeral (Int.ofNat w.length) := by
  simp [__str_value_len, __eo_requires, __eo_is_str, __eo_is_str_internal, __eo_len,
    native_str_len, native_teq, SmtEval.native_ite, SmtEval.native_and, SmtEval.native_not]

theorem overlapDrop_le (x y : native_String) : overlapDrop x y ≤ x.length := by
  induction x with
  | nil => simp [overlapDrop]
  | cons a x ih => simp only [overlapDrop, List.length_cons]; split <;> omega

/-- If the overlap drop count equals the full length, no nonempty suffix of `x`
    is compatible with `y`. -/
theorem overlapDrop_full_no_compat :
    ∀ (x y : native_String), overlapDrop x y = x.length →
      ∀ k, k < x.length → strCompat (x.drop k) y = false
  | [], y, h, k, hk => by simp at hk
  | a :: x, y, h, k, hk => by
      have hbc : strCompat (a :: x) y = false := by
        rcases hbcc : strCompat (a :: x) y with _ | _
        · rfl
        · exfalso; simp [overlapDrop, hbcc, List.length_cons] at h
      have hx : overlapDrop x y = x.length := by
        have h2 := h; simp [overlapDrop, hbc, List.length_cons] at h2; omega
      cases k with
      | zero => simpa using hbc
      | succ j =>
          have hj : j < x.length := by simp only [List.length_cons] at hk; omega
          simpa [List.drop_succ_cons] using overlapDrop_full_no_compat x y hx j hj

/-- The element list of an evaluated string literal is its chars tagged as
    `SmtValue.Char`. -/
theorem unpack_pack_string_map (w : native_String) :
    native_unpack_seq (native_pack_string w) = w.map SmtValue.Char := by
  simp [native_pack_string, native_unpack_pack_seq]

/-- Prefix-equality is preserved (both ways) by the injective `SmtValue.Char` tag. -/
theorem prefix_eq_map_char (a b : native_String) :
    native_seq_prefix_eq (a.map SmtValue.Char) (b.map SmtValue.Char) =
      native_string_prefix_eq a b := by
  induction a generalizing b with
  | nil => simp [native_seq_prefix_eq, native_string_prefix_eq]
  | cons c cs ih =>
      cases b with
      | nil => simp [native_seq_prefix_eq, native_string_prefix_eq]
      | cons d ds => simp [native_seq_prefix_eq, native_string_prefix_eq, native_veq, ih]

/-- The native no-overlap condition `(A)`, at the `SmtValue` level, from a full
    overlap drop count. -/
theorem no_compat_of_overlap_full (w w' : native_String)
    (hov : overlapDrop w w' = w.length) :
    ∀ k, k < (w.map SmtValue.Char).length →
      ¬ native_seq_compat ((w.map SmtValue.Char).drop k) (w'.map SmtValue.Char) := by
  intro k hk
  rw [List.length_map] at hk
  rw [← List.map_drop]
  intro hcompat
  have hsq := overlapDrop_full_no_compat w w' hov k hk
  unfold strCompat at hsq
  rw [Bool.or_eq_false_iff] at hsq
  unfold native_seq_compat at hcompat
  rw [prefix_eq_map_char, prefix_eq_map_char] at hcompat
  rcases hcompat with h | h
  · rw [hsq.1] at h; exact absurd h (by simp)
  · rw [hsq.2] at h; exact absurd h (by simp)

/-! ### Flatten structure: `flatten (nary_intro (String w))` is the char-chain -/

theorem extractString_cons_zero (c : native_Char) (cs : native_String) :
    extractString (c :: cs) 0 = [c] := by
  have h : native_str_len (c :: cs) = Int.ofNat (cs.length + 1) := by simp [native_str_len]
  have hge : (1:Int) ≤ native_str_len (c :: cs) - 0 := by
    rw [h, Int.sub_zero, Int.ofNat_eq_natCast]; omega
  unfold extractString native_str_substr
  rw [if_neg (by simp [native_str_len, native_zplus, native_zneg])]
  rw [show native_zplus (native_zplus 0 (native_zneg 0)) 1 = 1 from by simp [native_zplus, native_zneg]]
  rw [Int.min_eq_left hge]
  simp

theorem substrWord_eq_charChainTerm (w : native_String) :
    substrWord w 0 w.length = charChainTerm w := by
  induction w with
  | nil => rfl
  | cons c cs ih =>
      rw [show (c :: cs).length = cs.length + 1 from rfl, substrWord,
        show ((0:Int) + 1) = 1 from by omega, substrWord_cons_tail c cs, ih,
        extractString_cons_zero c cs]
      rfl

/-- `flatten (nary_intro (String w))` is exactly the canonical char-chain. -/
theorem flatten_nary_intro_string (w : native_String) :
    __str_flatten (__str_nary_intro (Term.String w)) = charChainTerm w := by
  cases w with
  | nil => rw [str_flatten_nary_intro_empty]; rfl
  | cons c cs => rw [str_flatten_nary_intro_cons, substrWord_eq_charChainTerm]

/-- The rule's `gt` side condition (`= false`) forces a full overlap drop count. -/
theorem overlap_cond_implies_overlapDrop_full (w w' : native_String)
    (hcond : __eo_gt (__str_value_len (Term.String w))
        (__str_overlap_rec (__str_flatten (__str_nary_intro (Term.String w)))
          (__str_flatten (__str_nary_intro (Term.String w')))) = Term.Boolean false) :
    overlapDrop w w' = w.length := by
  rw [str_value_len_string, flatten_nary_intro_string, flatten_nary_intro_string,
    str_overlap_rec_charChain] at hcond
  simp only [__eo_gt, native_zlt] at hcond
  have hd : decide (Int.ofNat (overlapDrop w w') < Int.ofNat w.length) = false := by
    injection hcond
  have hnlt : ¬ (Int.ofNat (overlapDrop w w') < Int.ofNat w.length) := of_decide_eq_false hd
  simp only [Int.ofNat_eq_natCast] at hnlt
  have hle := overlapDrop_le w w'
  omega

end RuleProofs
