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

/-! ### General atom-chains (handles `seq_unit` words, not just `String` literals)

A flattened word is a `str.++` chain of *atoms* (each a single-element term:
`String[ch]` for `Seq Char` literals, `seq_unit v` for general sequences),
terminated by an "empty".  `is_compatible`/`overlap_rec` compare atoms with the
*syntactic* `__eo_eq`; under the rule's guards (no comparison is `Stuck`), this
matches a syntactic list prefix-compatibility on the atom list. -/

/-- Syntactic list prefix on terms. -/
def listPrefixEq : List Term → List Term → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a = b) && listPrefixEq as bs

/-- Syntactic overlap-compatibility on term lists. -/
def listCompat (x y : List Term) : Bool := listPrefixEq x y || listPrefixEq y x

/-- Overlap drop count on term lists. -/
def listOverlapDrop : List Term → List Term → Nat
  | [], _ => 0
  | a :: x, y => if listCompat (a :: x) y then 0 else 1 + listOverlapDrop x y

theorem listOverlapDrop_le (x y : List Term) : listOverlapDrop x y ≤ x.length := by
  induction x with
  | nil => simp [listOverlapDrop]
  | cons a x ih => simp only [listOverlapDrop, List.length_cons]; split <;> omega

theorem listOverlapDrop_full_no_compat :
    ∀ (x y : List Term), listOverlapDrop x y = x.length →
      ∀ k, k < x.length → listCompat (x.drop k) y = false
  | [], y, h, k, hk => by simp at hk
  | a :: x, y, h, k, hk => by
      have hbc : listCompat (a :: x) y = false := by
        rcases hbcc : listCompat (a :: x) y with _ | _
        · rfl
        · exfalso; simp [listOverlapDrop, hbcc, List.length_cons] at h
      have hx : listOverlapDrop x y = x.length := by
        have h2 := h; simp [listOverlapDrop, hbc, List.length_cons] at h2; omega
      cases k with
      | zero => simpa using hbc
      | succ j =>
          have hj : j < x.length := by simp only [List.length_cons] at hk; omega
          simpa [List.drop_succ_cons] using listOverlapDrop_full_no_compat x y hx j hj

/-- `__eo_eq` is syntactic term equality (away from `Stuck`). -/
theorem eo_eq_val (a b : Term) (ha : a ≠ Term.Stuck) (hb : b ≠ Term.Stuck) :
    __eo_eq a b = Term.Boolean (native_teq b a) := by
  unfold __eo_eq; split <;> simp_all

/-- The `str.++`-chain of atoms terminated by `e`. -/
def atomChainTerm (atoms : List Term) (e : Term) : Term :=
  atoms.foldr (fun a acc => Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) acc) e

theorem atomChainTerm_cons (a : Term) (xs : List Term) (e : Term) :
    atomChainTerm (a :: xs) e =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) (atomChainTerm xs e) := rfl

theorem atomChainTerm_ne_stuck (xs : List Term) (e : Term) (he : e ≠ Term.Stuck) :
    atomChainTerm xs e ≠ Term.Stuck := by
  cases xs with
  | nil => exact he
  | cons a xs => rw [atomChainTerm_cons]; simp

/-- `is_compatible` on atom-chains computes syntactic list compatibility, under
    the resolution guard (every atom pair is syntactically equal or provably
    distinct — i.e. comparisons never get `Stuck`). -/
theorem is_compatible_atomChain (ex ey : Term)
    (hexL : ∀ Z, __str_is_compatible ex Z = Term.Boolean true)
    (heyR : ∀ a W, __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) ey = Term.Boolean true) :
    ∀ (xs ys : List Term),
      (∀ a ∈ xs, a ≠ Term.Stuck) → (∀ b ∈ ys, b ≠ Term.Stuck) →
      (∀ a ∈ xs, ∀ b ∈ ys,
        a = b ∨ __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true) →
      __str_is_compatible (atomChainTerm xs ex) (atomChainTerm ys ey) =
        Term.Boolean (listCompat xs ys) := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _ _
      simp only [atomChainTerm, List.foldr_nil, hexL, listCompat, listPrefixEq, Bool.true_or]
  | cons a xs ih =>
      intro ys hxne hyne hg
      cases ys with
      | nil =>
          rw [atomChainTerm_cons, show atomChainTerm [] ey = ey from rfl, heyR]
          simp [listCompat, listPrefixEq]
      | cons b ys =>
          have ha : a ≠ Term.Stuck := hxne a (by simp)
          have hb : b ≠ Term.Stuck := hyne b (by simp)
          rw [atomChainTerm_cons, atomChainTerm_cons]
          simp only [__str_is_compatible]
          by_cases hab : a = b
          · subst hab
            rw [eo_eq_val a a ha ha]
            have htt : native_teq a a = true := by simp [native_teq]
            simp only [htt, __eo_ite, native_teq, SmtEval.native_ite, if_true]
            rw [ih ys (fun a' h' => hxne a' (by simp [h'])) (fun b' h' => hyne b' (by simp [h']))
              (fun a' ha' b' hb' => hg a' (by simp [ha']) b' (by simp [hb']))]
            simp [listCompat, listPrefixEq]
          · have hba : b ≠ a := fun h => hab h.symm
            have heqab : __eo_eq a b = Term.Boolean false := by
              rw [eo_eq_val a b ha hb]; congr 1
              simp only [native_teq]; exact decide_eq_false hba
            have hdist : __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true := by
              rcases hg a (by simp) b (by simp) with h | h
              · exact absurd h hab
              · exact h
            simp [__eo_ite, __eo_l_1___str_is_compatible, __eo_requires, heqab, native_teq,
              SmtEval.native_ite, SmtEval.native_not, hdist, listCompat, listPrefixEq, hab, hba]

/-- `overlap_rec` on atom-chains computes the list overlap drop count. -/
theorem overlap_rec_atomChain (ex ey : Term)
    (heyne : ey ≠ Term.Stuck)
    (hexL : ∀ Z, __str_is_compatible ex Z = Term.Boolean true)
    (heyR : ∀ a W, __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) ey = Term.Boolean true)
    (hexO : ∀ Z, __str_overlap_rec ex Z = Term.Numeral 0) :
    ∀ (xs ys : List Term),
      (∀ a ∈ xs, a ≠ Term.Stuck) → (∀ b ∈ ys, b ≠ Term.Stuck) →
      (∀ a ∈ xs, ∀ b ∈ ys,
        a = b ∨ __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true) →
      __str_overlap_rec (atomChainTerm xs ex) (atomChainTerm ys ey) =
        Term.Numeral (Int.ofNat (listOverlapDrop xs ys)) := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _ _
      rw [show atomChainTerm [] ex = ex from rfl, hexO]
      simp [listOverlapDrop]
  | cons a xs ih =>
      intro ys hxne hyne hg
      rw [atomChainTerm_cons,
        overlap_rec_concat _ _ _ (atomChainTerm_ne_stuck ys ey heyne),
        ← atomChainTerm_cons,
        is_compatible_atomChain ex ey hexL heyR (a :: xs) ys hxne hyne hg]
      have ihres := ih ys (fun a' h' => hxne a' (by simp [h'])) hyne
        (fun a' ha' b' hb' => hg a' (by simp [ha']) b' hb')
      cases hbc : listCompat (a :: xs) ys with
      | true => simp [__eo_ite, native_teq, SmtEval.native_ite, listOverlapDrop, hbc]
      | false =>
          simp only [listOverlapDrop, hbc, if_false]
          simp [__eo_ite, native_teq, SmtEval.native_ite, ihres, __eo_add, native_zplus]

/-! ### Atom → value mapping

Under atom→value injectivity (distinct atoms have distinct values — from the
resolution guard plus `are_distinct` soundness), syntactic list compatibility on
atoms determines native value compatibility on the underlying value lists. -/

theorem listPrefixEq_of_map_prefix (f : Term → SmtValue) :
    ∀ (As Bs : List Term),
      (∀ a ∈ As, ∀ b ∈ Bs, f a = f b → a = b) →
      native_seq_prefix_eq (As.map f) (Bs.map f) = true → listPrefixEq As Bs = true := by
  intro As
  induction As with
  | nil => intro Bs _ _; rfl
  | cons a As ih =>
      intro Bs hinj h
      cases Bs with
      | nil => simp [native_seq_prefix_eq] at h
      | cons b Bs =>
          simp only [List.map_cons, native_seq_prefix_eq, native_veq, Bool.and_eq_true,
            decide_eq_true_eq] at h
          have hab : a = b := hinj a (by simp) b (by simp) h.1
          subst hab
          simp only [listPrefixEq, decide_true, Bool.true_and]
          exact ih Bs (fun a' ha' b' hb' => hinj a' (by simp [ha']) b' (by simp [hb']))
            (by simpa using h.2)

/-- Native value compatibility implies syntactic atom compatibility (so its
    negation transfers from atoms to values). -/
theorem native_seq_compat_to_listCompat (f : Term → SmtValue) (As Bs : List Term)
    (hinj : ∀ a ∈ As, ∀ b ∈ Bs, f a = f b → a = b)
    (h : native_seq_compat (As.map f) (Bs.map f)) : listCompat As Bs = true := by
  unfold native_seq_compat at h
  unfold listCompat
  rcases h with h | h
  · rw [listPrefixEq_of_map_prefix f As Bs hinj h]; simp
  · rw [listPrefixEq_of_map_prefix f Bs As (fun b hb a ha hba => (hinj a ha b hb hba.symm).symm) h]
    simp

/-- `__eo_eq` is syntactic term equality (when it yields `true`). -/
theorem eq_of_eo_eq (x y : Term) (h : __eo_eq x y = Term.Boolean true) : y = x := by
  cases x <;> cases y <;> simp_all [__eo_eq, native_teq]

/-- Splitting a true `__eo_and` into its two true conjuncts. -/
theorem eo_and_true_split (a b : Term) (h : __eo_and a b = Term.Boolean true) :
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  cases a <;> cases b <;> simp_all [__eo_and, native_and, SmtEval.native_and]
  all_goals (simp only [__eo_requires, native_ite, native_teq] at h)
  all_goals (split at h <;> exact Term.noConfusion h)

/-- An empty word evaluates to a sequence with empty underlying element list. -/
theorem str_is_empty_eval_unpack_nil (M : SmtModel) (e : Term) (s : SmtSeq)
    (hemp : __str_is_empty e = Term.Boolean true)
    (hev : __smtx_model_eval M (__eo_to_smt e) = SmtValue.Seq s) :
    native_unpack_seq s = [] := by
  unfold __str_is_empty at hemp
  split at hemp
  · exact Term.noConfusion hemp
  · rename_i U
    rw [show __eo_to_smt (Term.UOp1 UserOp1.seq_empty (Term.Apply (Term.UOp UserOp.Seq) U)) =
        __eo_to_smt_seq_empty (__eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U)) from rfl] at hev
    simp only [__eo_to_smt_type, __smtx_typeof_guard, native_ite] at hev
    split at hev
    · simp only [__eo_to_smt_seq_empty, __smtx_model_eval] at hev
      exact SmtValue.noConfusion hev
    · rw [show __eo_to_smt_seq_empty (SmtType.Seq (__eo_to_smt_type U)) =
          SmtTerm.seq_empty (__eo_to_smt_type U) from rfl,
        show __smtx_model_eval M (SmtTerm.seq_empty (__eo_to_smt_type U)) =
          SmtValue.Seq (SmtSeq.empty (__eo_to_smt_type U)) from by simp only [__smtx_model_eval]] at hev
      injection hev with hev; rw [← hev]; rfl
  · rw [show __eo_to_smt (Term.String []) = SmtTerm.String [] from rfl,
      show __smtx_model_eval M (SmtTerm.String []) = SmtValue.Seq (native_pack_string []) from by
        simp only [__smtx_model_eval]] at hev
    injection hev with hev; rw [← hev]
    simp [native_pack_string, native_pack_seq, native_unpack_seq]
  · simp at hemp

/-- `__eo_mk_apply` on non-`Stuck` arguments is plain application. -/
theorem mk_apply_eq (x y : Term) (hx : x ≠ Term.Stuck) (hy : y ≠ Term.Stuck) :
    __eo_mk_apply x y = Term.Apply x y := by
  cases x <;> cases y <;> simp_all [__eo_mk_apply]

/-- `flatten` keeps a non-`String` head atom (e.g. a `seq_unit`) in place. -/
theorem flatten_concat_nonstr (a rest : Term) (ha : __eo_is_str a = Term.Boolean false)
    (hrest : __str_flatten rest ≠ Term.Stuck) :
    __str_flatten (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) rest) =
      Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) (__str_flatten rest) := by
  simp only [__str_flatten, ha, eo_ite_false]
  exact mk_apply_eq _ _ (by simp) hrest

/-- The no-overlap `(A)` condition for `String`-literal arguments, from the `gt`
    side-condition (composes the committed String bridge). -/
theorem no_compat_string (wc wd : native_String)
    (hgt : __eo_gt (__str_value_len (Term.String wc))
        (__str_overlap_rec (__str_flatten (__str_nary_intro (Term.String wc)))
          (__str_flatten (__str_nary_intro (Term.String wd)))) = Term.Boolean false) :
    ∀ k, k < (wc.map SmtValue.Char).length →
      ¬ native_seq_compat ((wc.map SmtValue.Char).drop k) (wd.map SmtValue.Char) :=
  no_compat_of_overlap_full wc wd (overlap_cond_implies_overlapDrop_full wc wd hgt)

/-! ### Model-eval of the rule equation -/

/-- `contains` evaluating to a Boolean forces both arguments to evaluate to
    sequence values. -/
theorem contains_args_seq_of_eval_bool (M : SmtModel) (x y : Term) (b : Bool)
    (h : __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y))
      = SmtValue.Boolean b) :
    (∃ sx, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx) ∧
      (∃ sy, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy) := by
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y) =
      SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y) from rfl] at h
  rw [show __smtx_model_eval M (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) =
      __smtx_model_eval_str_contains (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) from by simp only [__smtx_model_eval]] at h
  cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
    cases hy : __smtx_model_eval M (__eo_to_smt y) <;>
    simp_all [__smtx_model_eval_str_contains]

/-- Model-evaluation of an `or`. -/
theorem model_eval_or_eq (M : SmtModel) (A B : Term) :
    __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B)) =
      __smtx_model_eval_or (__smtx_model_eval M (__eo_to_smt A))
        (__smtx_model_eval M (__eo_to_smt B)) := by
  rw [show __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) =
      SmtTerm.or (__eo_to_smt A) (__eo_to_smt B) from rfl]
  simp only [__smtx_model_eval]

/-- The rule's two sides evaluate equally, given the operands' sequence values,
    `emp` empty, and the no-overlap conditions `(A)/(B)` on the middle/needle. -/
theorem overlap_split_eval (M : SmtModel) (t c sw emp d : Term)
    (St Sc Ss Se Sd : SmtSeq)
    (ht : __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq St)
    (hc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq Sc)
    (hsw : __smtx_model_eval M (__eo_to_smt sw) = SmtValue.Seq Ss)
    (hemp : __smtx_model_eval M (__eo_to_smt emp) = SmtValue.Seq Se)
    (hd : __smtx_model_eval M (__eo_to_smt d) = SmtValue.Seq Sd)
    (hempnil : native_unpack_seq Se = [])
    (hA : ∀ k, k < (native_unpack_seq Sc).length →
      ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd))
    (hB : ∀ k, k < (native_unpack_seq Sd).length →
      ¬ native_seq_compat ((native_unpack_seq Sd).drop k) (native_unpack_seq Sc)) :
    __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp)))) d)) =
      __smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.Apply (Term.UOp UserOp.or)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) t) d))
          (Term.Apply (Term.Apply (Term.UOp UserOp.or)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) sw) d))
            (Term.Boolean false)))) := by
  obtain ⟨s1, hs1, hu1⟩ := strConcat_unpack_eval M sw emp Ss Se hsw hemp
  obtain ⟨s2, hs2, hu2⟩ := strConcat_unpack_eval M c
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp) Sc s1 hc hs1
  obtain ⟨s3, hs3, hu3⟩ := strConcat_unpack_eval M t
    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) sw) emp)) St s2 ht hs2
  have hfalse : __smtx_model_eval M (__eo_to_smt (Term.Boolean false)) = SmtValue.Boolean false := by
    rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false from rfl]
    simp only [__smtx_model_eval]
  rw [strContains_eval_eq M _ d s3 Sd hs3 hd]
  rw [model_eval_or_eq, model_eval_or_eq,
    strContains_eval_eq M t d St Sd ht hd, strContains_eval_eq M sw d Ss Sd hsw hd, hfalse]
  simp only [__smtx_model_eval_or]
  have hcs : native_unpack_seq s3 =
      native_unpack_seq St ++ native_unpack_seq Sc ++ native_unpack_seq Ss := by
    rw [hu3, hu2, hu1, hempnil]; simp [List.append_assoc]
  rw [hcs]
  have hsplit := native_seq_contains_split_iff_of_no_overlap
    (native_unpack_seq St) (native_unpack_seq Sc) (native_unpack_seq Ss) (native_unpack_seq Sd) hA hB
  congr 1
  rw [show native_or (native_seq_contains (native_unpack_seq St) (native_unpack_seq Sd))
        (native_or (native_seq_contains (native_unpack_seq Ss) (native_unpack_seq Sd)) false) =
      (native_seq_contains (native_unpack_seq St) (native_unpack_seq Sd) ||
        native_seq_contains (native_unpack_seq Ss) (native_unpack_seq Sd)) from by simp [native_or]]
  rw [Bool.eq_iff_iff, Bool.or_eq_true]
  exact hsplit

theorem eo_add_one_inv (R : Term) (N : Int)
    (h : __eo_add (Term.Numeral 1) R = Term.Numeral N) :
    R = Term.Numeral (N - 1) := by
  cases R with
  | Numeral m =>
      simp only [__eo_add, native_zplus] at h; injection h with h
      congr 1; rw [← h, Int.add_comm, Int.add_sub_cancel]
  | _ => simp_all [__eo_add, __eo_requires, native_ite, native_teq]

/-- If the overlap recursion runs to "full" on an atom chain, then every suffix of
the chain is incompatible with `W`. -/
theorem overlap_full_is_compat_false (ex W : Term) (hW : W ≠ Term.Stuck) :
    ∀ (xs : List Term),
      __str_overlap_rec (atomChainTerm xs ex) W = Term.Numeral (Int.ofNat xs.length) →
      ∀ k, k < xs.length →
        __str_is_compatible (atomChainTerm (xs.drop k) ex) W = Term.Boolean false := by
  intro xs
  induction xs with
  | nil => intro _ k hk; simp at hk
  | cons a xs ih =>
      intro hov k hk
      rw [atomChainTerm_cons, overlap_rec_concat _ _ _ hW, ← atomChainTerm_cons] at hov
      have hcompat : __str_is_compatible (atomChainTerm (a :: xs) ex) W = Term.Boolean false := by
        clear hk ih
        cases hc : __str_is_compatible (atomChainTerm (a :: xs) ex) W with
        | Boolean b =>
            cases b with
            | true =>
                exfalso; rw [hc, eo_ite_true] at hov; injection hov with hov
                rw [show (a :: xs).length = xs.length + 1 from rfl] at hov
                simp only [native_Int, Int.ofNat_eq_natCast] at hov; omega
            | false => rfl
        | _ => rw [hc] at hov; simp [__eo_ite, native_teq, SmtEval.native_ite] at hov
      have hrec : __str_overlap_rec (atomChainTerm xs ex) W = Term.Numeral (Int.ofNat xs.length) := by
        clear hk ih
        rw [hcompat, eo_ite_false] at hov
        rw [eo_add_one_inv _ _ hov]; congr 1
        rw [show (a :: xs).length = xs.length + 1 from rfl]
        simp only [native_Int, Int.ofNat_eq_natCast]; omega
      cases k with
      | zero => simpa using hcompat
      | succ j =>
          have hj : j < xs.length := by simp only [List.length_cons] at hk; omega
          simpa [List.drop_succ_cons] using ih hrec j hj

theorem nveq_self (v : SmtValue) : native_veq v v = true := by simp [native_veq]

theorem nveq_symm {v1 v2 : SmtValue} (h : native_veq v1 v2 = false) :
    native_veq v2 v1 = false := by
  simp only [native_veq, decide_eq_false_iff_not] at h ⊢; exact fun he => h he.symm

/-- The key inversion: when `is_compatible` of two atom-chains is *Boolean false*
(so the comparison never got `Stuck`), the underlying value lists are not
overlap-compatible.  The distinctness facts are extracted *locally* from each
head comparison (via `are_distinct` soundness, supplied as `hsound`), so no
global distinctness guard is needed. -/
theorem is_compat_false_no_compat
    (val : Term → SmtValue) (exX exY : Term)
    (hExYne : exY ≠ Term.Stuck)
    (hExX : ∀ W, W ≠ Term.Stuck → __str_is_compatible exX W = Term.Boolean true)
    (hExY : ∀ a W, __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) exY = Term.Boolean true) :
    ∀ (xs ys : List Term),
      (∀ a b, __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true →
        native_veq (val a) (val b) = false) →
      __str_is_compatible (atomChainTerm xs exX) (atomChainTerm ys exY) = Term.Boolean false →
      ¬ native_seq_compat (xs.map val) (ys.map val) := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ hfalse
      rw [show atomChainTerm [] exX = exX from rfl,
        hExX _ (atomChainTerm_ne_stuck ys exY hExYne)] at hfalse
      simp at hfalse
  | cons a xs ih =>
      intro ys hsound hfalse
      cases ys with
      | nil =>
          rw [atomChainTerm_cons, show atomChainTerm [] exY = exY from rfl, hExY] at hfalse
          simp at hfalse
      | cons b ys =>
          rw [atomChainTerm_cons, atomChainTerm_cons] at hfalse
          simp only [__str_is_compatible] at hfalse
          by_cases hab : __eo_eq a b = Term.Boolean true
          · have hba : b = a := eq_of_eo_eq a b hab
            subst hba
            rw [hab, eo_ite_true] at hfalse
            have ihres := ih ys hsound hfalse
            intro hcompat; apply ihres
            unfold native_seq_compat at hcompat ⊢
            simp only [List.map_cons, native_seq_prefix_eq, nveq_self, Bool.true_and] at hcompat
            exact hcompat
          · have habf : __eo_eq a b = Term.Boolean false := by
              cases h : __eo_eq a b with
              | Boolean bb => cases bb with
                | true => exact absurd h hab
                | false => rfl
              | _ => rw [h] at hfalse; simp [__eo_ite, native_teq, SmtEval.native_ite] at hfalse
            rw [habf] at hfalse
            simp only [__eo_ite, native_teq, SmtEval.native_ite,
              __eo_l_1___str_is_compatible, __eo_requires, habf] at hfalse
            have hdist : __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true := by
              revert hfalse
              cases h : __are_distinct_terms_type a b (__eo_typeof a) with
              | Boolean bb => cases bb with
                | true => intro _; rfl
                | false => intro hf; simp [native_ite, native_teq] at hf
              | _ => intro hf; simp [native_ite, native_teq] at hf
            have hvf := hsound a b hdist
            have hvf2 := nveq_symm hvf
            intro hcompat
            unfold native_seq_compat at hcompat
            simp only [List.map_cons, native_seq_prefix_eq, hvf, hvf2,
              Bool.false_and] at hcompat
            rcases hcompat with h | h <;> exact Bool.noConfusion h

/-- The overlap-recursion count is bounded by the number of atoms. -/
theorem overlap_rec_le_len (ex W : Term) (hW : W ≠ Term.Stuck)
    (hexz : __str_overlap_rec ex W = Term.Numeral 0) :
    ∀ (xs : List Term) (m : Int),
      __str_overlap_rec (atomChainTerm xs ex) W = Term.Numeral m → m ≤ Int.ofNat xs.length := by
  intro xs
  induction xs with
  | nil =>
      intro m h
      rw [show atomChainTerm [] ex = ex from rfl, hexz] at h
      injection h with h; simp only [native_Int, List.length_nil, Int.ofNat_eq_natCast] at h ⊢; omega
  | cons a xs ih =>
      intro m h
      rw [atomChainTerm_cons, overlap_rec_concat _ _ _ hW, ← atomChainTerm_cons] at h
      cases hc : __str_is_compatible (atomChainTerm (a :: xs) ex) W with
      | Boolean bb =>
          cases bb with
          | true =>
              rw [hc, eo_ite_true] at h; injection h with h
              simp only [native_Int] at h ⊢
              rw [show (a :: xs).length = xs.length + 1 from rfl]
              simp only [Int.ofNat_eq_natCast]; omega
          | false =>
              rw [hc, eo_ite_false] at h
              have key : __str_overlap_rec (atomChainTerm xs ex) W = Term.Numeral (m - 1) :=
                eo_add_one_inv _ _ h
              have ihres := ih (m - 1) key
              rw [show (a :: xs).length = xs.length + 1 from rfl]
              simp only [native_Int, Int.ofNat_eq_natCast] at ihres ⊢; omega
      | _ => rw [hc] at h; simp [__eo_ite, native_teq, SmtEval.native_ite] at h

/-- Unified no-overlap `(A)` derivation from a word characterization of `c`/`d`.
Given that `c`/`d` flatten to atom-chains with terminators `exX`/`exY`, whose
evaluated element lists are `xs.map val`/`ys.map val`, the `gt` side-condition
forces every nonempty suffix of `c`'s value to be incompatible with `d`'s. -/
theorem no_compat_of_word
    (val : Term → SmtValue) (c d : Term) (Sc Sd : SmtSeq)
    (xs ys : List Term) (exX exY : Term)
    (hflatc : __str_flatten (__str_nary_intro c) = atomChainTerm xs exX)
    (hflatd : __str_flatten (__str_nary_intro d) = atomChainTerm ys exY)
    (hlenc : __str_value_len c = Term.Numeral (Int.ofNat xs.length))
    (hunpc : native_unpack_seq Sc = xs.map val)
    (hunpd : native_unpack_seq Sd = ys.map val)
    (hexXne : exX ≠ Term.Stuck) (hexYne : exY ≠ Term.Stuck)
    (hexXcompatL : ∀ W, W ≠ Term.Stuck → __str_is_compatible exX W = Term.Boolean true)
    (hexYcompatR : ∀ a W, __str_is_compatible
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) a) W) exY = Term.Boolean true)
    (hexXz : ∀ W, W ≠ Term.Stuck → __str_overlap_rec exX W = Term.Numeral 0)
    (hsound : ∀ a b, __are_distinct_terms_type a b (__eo_typeof a) = Term.Boolean true →
      native_veq (val a) (val b) = false)
    (hgt : __eo_gt (__str_value_len c)
        (__str_overlap_rec (__str_flatten (__str_nary_intro c))
          (__str_flatten (__str_nary_intro d))) = Term.Boolean false) :
    ∀ k, k < (native_unpack_seq Sc).length →
      ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) := by
  rw [hlenc, hflatc, hflatd] at hgt
  have hWne : atomChainTerm ys exY ≠ Term.Stuck := atomChainTerm_ne_stuck ys exY hexYne
  have hrec : ∃ N2, __str_overlap_rec (atomChainTerm xs exX) (atomChainTerm ys exY)
      = Term.Numeral N2 ∧ Int.ofNat xs.length ≤ N2 := by
    revert hgt
    cases hb : __str_overlap_rec (atomChainTerm xs exX) (atomChainTerm ys exY) with
    | Numeral N2 =>
        intro hgt; refine ⟨N2, rfl, ?_⟩
        simp only [__eo_gt, native_zlt] at hgt; injection hgt with hgt
        have hnlt := of_decide_eq_false hgt
        simp only [native_Int, Int.ofNat_eq_natCast] at hnlt ⊢; omega
    | _ => intro hgt; simp [__eo_gt] at hgt
  obtain ⟨N2, hN2eq, hN2ge⟩ := hrec
  have hN2le := overlap_rec_le_len exX (atomChainTerm ys exY) hWne
    (hexXz _ hWne) xs N2 hN2eq
  have hN2 : N2 = Int.ofNat xs.length := by
    simp only [native_Int, Int.ofNat_eq_natCast] at hN2le hN2ge ⊢; omega
  rw [hN2] at hN2eq
  have hfull := overlap_full_is_compat_false exX (atomChainTerm ys exY) hWne xs hN2eq
  intro k hk
  rw [hunpc, List.length_map] at hk
  rw [hunpc, hunpd, ← List.map_drop]
  exact is_compat_false_no_compat val exX exY hexYne hexXcompatL hexYcompatR
    (xs.drop k) ys hsound (hfull k hk)

/-- A `String` literal evaluates to the packed string value. -/
theorem eval_string (M : SmtModel) (w : native_String) :
    __smtx_model_eval M (__eo_to_smt (Term.String w)) = SmtValue.Seq (native_pack_string w) := by
  rw [show __eo_to_smt (Term.String w) = SmtTerm.String w from rfl]; simp only [__smtx_model_eval]

/-- The no-overlap `(A)` condition, dispatching on the representation of the
constant-like words `c`/`d`.  The `String`-literal case is closed via the
committed char-chain bridge `no_compat_string`. -/
theorem no_compat_dispatch (M : SmtModel) (hM : model_total_typed M)
    (c d : Term) (Sc Sd : SmtSeq)
    (hSc : __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq Sc)
    (hSd : __smtx_model_eval M (__eo_to_smt d) = SmtValue.Seq Sd)
    (hgt : __eo_gt (__str_value_len c)
        (__str_overlap_rec (__str_flatten (__str_nary_intro c))
          (__str_flatten (__str_nary_intro d))) = Term.Boolean false) :
    ∀ k, k < (native_unpack_seq Sc).length →
      ¬ native_seq_compat ((native_unpack_seq Sc).drop k) (native_unpack_seq Sd) := by
  cases c with
  | String wc =>
      cases d with
      | String wd =>
          rw [eval_string] at hSc hSd
          injection hSc with hSc; injection hSd with hSd
          subst hSc; subst hSd
          rw [unpack_pack_string_map, unpack_pack_string_map]
          exact no_compat_string wc wd hgt
      | _ => sorry
  | _ => sorry

end RuleProofs
