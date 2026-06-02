import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.RuleSupport.StrConcatSupport
import Cpc.Proofs.RuleSupport.StringSupport
import Cpc.Proofs.RuleSupport.NativeSeqSupport

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

end RuleProofs
