import Cpc.Proofs.RuleSupport.StrEqReplSupport
import Cpc.Proofs.RuleSupport.StringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace StrContainsReplCharSupport

theorem eqs_of_requires4_and_eq_true_not_stuck
    (x1 y1 x2 y2 x3 y3 x4 y4 B : Term)
    (hProg :
      __eo_requires
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
              (__eo_eq x3 y3))
            (__eo_eq x4 y4))
          (Term.Boolean true) B ≠ Term.Stuck) :
    y1 = x1 ∧ y2 = x2 ∧ y3 = x3 ∧ y4 = x4 := by
  have hGuard :
      __eo_and
          (__eo_and
            (__eo_and (__eo_eq x1 y1) (__eo_eq x2 y2))
            (__eo_eq x3 y3))
          (__eo_eq x4 y4) =
        Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hProg
  have h123 := StrEqReplSupport.eo_and_eq_true_left hGuard
  have h4 := StrEqReplSupport.eo_and_eq_true_right hGuard
  have h12 := StrEqReplSupport.eo_and_eq_true_left h123
  have h3 := StrEqReplSupport.eo_and_eq_true_right h123
  have h1 := StrEqReplSupport.eo_and_eq_true_left h12
  have h2 := StrEqReplSupport.eo_and_eq_true_right h12
  exact ⟨RuleProofs.eq_of_eo_eq_true x1 y1 h1,
    RuleProofs.eq_of_eo_eq_true x2 y2 h2,
    RuleProofs.eq_of_eo_eq_true x3 y3 h3,
    RuleProofs.eq_of_eo_eq_true x4 y4 h4⟩

theorem eo_typeof_str_contains_args_of_ne_stuck
    (A B : Term)
    (h : __eo_typeof_str_contains A B ≠ Term.Stuck) :
    ∃ U, A = Term.Apply Term.Seq U ∧ B = Term.Apply Term.Seq U := by
  cases A <;> simp [__eo_typeof_str_contains] at h ⊢
  case Apply f x =>
    cases f <;> simp [__eo_typeof_str_contains] at h ⊢
    case UOp op =>
      cases op <;> simp [__eo_typeof_str_contains] at h ⊢
      case Seq =>
        cases B <;> simp [__eo_typeof_str_contains] at h ⊢
        case Apply g y =>
          cases g <;> simp [__eo_typeof_str_contains] at h ⊢
          case UOp opg =>
            cases opg <;> simp [__eo_typeof_str_contains] at h ⊢
            case Seq =>
              have hyx : y = x :=
                RuleProofs.eq_of_requires_eq_true_not_stuck x y Term.Bool h
              exact hyx

theorem smtx_eval_str_contains_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_contains x y) =
      __smtx_model_eval_str_contains
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

theorem native_seq_prefix_eq_append
    (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil => rfl
  | cons p ps ih =>
      have hp : native_veq p p = true := by simp [native_veq]
      simp [native_seq_prefix_eq, hp, ih]

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
            simp only [List.length_cons] at hFuel
            omega
          unfold native_seq_indexof_rec
          by_cases hPre :
              native_seq_prefix_eq pat ((b :: bs) ++ pat ++ after) = true
          · rw [if_pos hPre]
            simp
          · rw [if_neg hPre]
            have hxs :
                (b :: bs) ++ pat ++ after = b :: (bs ++ pat ++ after) := by
              simp
            rw [hxs]
            simpa using ih (i + 1) f hbs

theorem native_seq_contains_of_decomp
    (before pat after : List SmtValue) :
    native_seq_contains (before ++ pat ++ after) pat = true := by
  have hLen : pat.length ≤ (before ++ pat ++ after).length := by
    simp [List.length_append]
    omega
  have hNe :
      native_seq_indexof (before ++ pat ++ after) pat 0 ≠ -1 := by
    unfold native_seq_indexof
    simp only [Int.reduceLT, ↓reduceIte, Int.toNat_zero, Nat.zero_add]
    rw [dif_pos hLen]
    have hFuel :
        before.length <
          (before ++ pat ++ after).length - pat.length + 1 := by
      simp [List.length_append]
      omega
    simpa using
      native_seq_indexof_rec_append_ne_neg pat after before 0
        ((before ++ pat ++ after).length - pat.length + 1) hFuel
  have hGe : 0 ≤ native_seq_indexof (before ++ pat ++ after) pat 0 := by
    rcases native_seq_indexof_eq_neg_one_or_ge
        (before ++ pat ++ after) pat 0 with h | h
    · exact absurd h hNe
    · exact h
  unfold native_seq_contains
  exact decide_eq_true hGe

theorem native_seq_contains_iff_decomp
    (xs pat : List SmtValue) :
    native_seq_contains xs pat = true ↔
      ∃ before after, xs = before ++ pat ++ after := by
  constructor
  · intro h
    have hGe : 0 ≤ native_seq_indexof xs pat 0 := by
      unfold native_seq_contains at h
      exact of_decide_eq_true h
    exact ⟨_, _, (native_seq_indexof_zero_decomp xs pat hGe).symm⟩
  · rintro ⟨before, after, rfl⟩
    exact native_seq_contains_of_decomp before pat after

theorem native_seq_contains_trans
    (xs mid pat : List SmtValue)
    (hXMid : native_seq_contains xs mid = true)
    (hMidPat : native_seq_contains mid pat = true) :
    native_seq_contains xs pat = true := by
  rcases (native_seq_contains_iff_decomp xs mid).1 hXMid with
    ⟨before, after, hXs⟩
  rcases (native_seq_contains_iff_decomp mid pat).1 hMidPat with
    ⟨midBefore, midAfter, hMid⟩
  apply (native_seq_contains_iff_decomp xs pat).2
  refine ⟨before ++ midBefore, midAfter ++ after, ?_⟩
  rw [hXs, hMid]
  simp [List.append_assoc]

theorem native_seq_contains_replacement_of_pattern_present
    (source pattern replacement : List SmtValue)
    (hContains : native_seq_contains source pattern = true) :
    native_seq_contains
        (native_seq_replace source pattern replacement) replacement = true := by
  cases pattern with
  | nil =>
      simpa [native_seq_replace] using
        native_seq_contains_of_decomp [] replacement source
  | cons p ps =>
      have hNonneg : 0 ≤ native_seq_indexof source (p :: ps) 0 := by
        unfold native_seq_contains at hContains
        exact of_decide_eq_true hContains
      have hNotNeg : ¬ native_seq_indexof source (p :: ps) 0 < 0 :=
        Int.not_lt_of_ge hNonneg
      unfold native_seq_replace
      rw [if_neg hNotNeg]
      exact native_seq_contains_of_decomp
        (source.take (Int.toNat (native_seq_indexof source (p :: ps) 0)))
        replacement
        (source.drop
          (Int.toNat (native_seq_indexof source (p :: ps) 0) +
            (p :: ps).length))

theorem native_seq_length_le_of_contains
    (source pattern : List SmtValue)
    (hContains : native_seq_contains source pattern = true) :
    pattern.length ≤ source.length := by
  rcases (native_seq_contains_iff_decomp source pattern).1 hContains with
    ⟨before, after, rfl⟩
  simp [List.length_append]
  omega

theorem native_seq_replace_src_inv_no_contains1
    (xs source blocked : List SmtValue)
    (hAbsent : native_seq_contains source blocked = false) :
    native_seq_replace xs (native_seq_replace source xs blocked) source =
      native_seq_replace xs source source := by
  by_cases hSourceXs : native_seq_contains source xs = true
  · have hInnerBlocked :
        native_seq_contains (native_seq_replace source xs blocked) blocked =
          true :=
      native_seq_contains_replacement_of_pattern_present
        source xs blocked hSourceXs
    have hOuterAbsent :
        native_seq_contains xs (native_seq_replace source xs blocked) =
          false := by
      cases h :
          native_seq_contains xs (native_seq_replace source xs blocked)
      · rfl
      · have hXsBlocked := native_seq_contains_trans xs
            (native_seq_replace source xs blocked) blocked h hInnerBlocked
        have hSourceBlocked := native_seq_contains_trans source xs blocked
          hSourceXs hXsBlocked
        rw [hSourceBlocked] at hAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs (native_seq_replace source xs blocked) source hOuterAbsent]
    exact (StrEqReplSupport.native_seq_replace_id xs source).symm
  · have hSourceXsFalse : native_seq_contains source xs = false := by
      cases h : native_seq_contains source xs
      · rfl
      · exact False.elim (hSourceXs h)
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      source xs blocked hSourceXsFalse]

theorem native_seq_replace_src_inv_no_contains2
    (xs source blocked : List SmtValue)
    (hAbsent : native_seq_contains source blocked = false) :
    native_seq_replace xs (native_seq_replace source xs blocked) xs =
      native_seq_replace xs source xs := by
  by_cases hSourceXs : native_seq_contains source xs = true
  · have hInnerBlocked :
        native_seq_contains (native_seq_replace source xs blocked) blocked =
          true :=
      native_seq_contains_replacement_of_pattern_present
        source xs blocked hSourceXs
    have hOuterAbsent :
        native_seq_contains xs (native_seq_replace source xs blocked) =
          false := by
      cases h :
          native_seq_contains xs (native_seq_replace source xs blocked)
      · rfl
      · have hXsBlocked := native_seq_contains_trans xs
            (native_seq_replace source xs blocked) blocked h hInnerBlocked
        have hSourceBlocked := native_seq_contains_trans source xs blocked
          hSourceXs hXsBlocked
        rw [hSourceBlocked] at hAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs (native_seq_replace source xs blocked) xs hOuterAbsent]
    exact (StrEqReplSupport.native_seq_replace_source_of_pat_len_ge
      xs source (native_seq_length_le_of_contains source xs hSourceXs)).symm
  · have hSourceXsFalse : native_seq_contains source xs = false := by
      cases h : native_seq_contains source xs
      · rfl
      · exact False.elim (hSourceXs h)
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      source xs blocked hSourceXsFalse]

theorem native_seq_replace_src_inv_no_contains3
    (xs source pattern replacement outerReplacement : List SmtValue)
    (hPatternAbsent : native_seq_contains xs pattern = false)
    (hReplacementAbsent : native_seq_contains xs replacement = false) :
    native_seq_replace xs
        (native_seq_replace source pattern replacement) outerReplacement =
      native_seq_replace xs source outerReplacement := by
  by_cases hXsSource : native_seq_contains xs source = true
  · have hSourcePatternFalse :
        native_seq_contains source pattern = false := by
      cases h : native_seq_contains source pattern
      · rfl
      · have hXsPattern := native_seq_contains_trans xs source pattern
            hXsSource h
        rw [hXsPattern] at hPatternAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      source pattern replacement hSourcePatternFalse]
  · have hXsSourceFalse : native_seq_contains xs source = false := by
      cases h : native_seq_contains xs source
      · rfl
      · exact False.elim (hXsSource h)
    have hOuterPatternFalse :
        native_seq_contains xs
            (native_seq_replace source pattern replacement) = false := by
      by_cases hSourcePattern : native_seq_contains source pattern = true
      · have hInnerReplacement :
            native_seq_contains
                (native_seq_replace source pattern replacement) replacement =
              true :=
          native_seq_contains_replacement_of_pattern_present
            source pattern replacement hSourcePattern
        cases h :
            native_seq_contains xs
              (native_seq_replace source pattern replacement)
        · rfl
        · have hXsReplacement := native_seq_contains_trans xs
              (native_seq_replace source pattern replacement) replacement
              h hInnerReplacement
          rw [hXsReplacement] at hReplacementAbsent
          contradiction
      · have hSourcePatternFalse :
            native_seq_contains source pattern = false := by
          cases h : native_seq_contains source pattern
          · rfl
          · exact False.elim (hSourcePattern h)
        rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
          source pattern replacement hSourcePatternFalse]
        exact hXsSourceFalse
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs (native_seq_replace source pattern replacement) outerReplacement
      hOuterPatternFalse]
    exact (StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs source outerReplacement hXsSourceFalse).symm

theorem native_seq_replace_dual_ite1_of_contains_true
    (xs pattern replacement outerReplacement : List SmtValue)
    (hReplacementAbsent : native_seq_contains xs replacement = false)
    (hPatternPresent : native_seq_contains xs pattern = true) :
    native_seq_replace xs
        (native_seq_replace xs pattern replacement) outerReplacement = xs := by
  have hInnerReplacement :
      native_seq_contains
          (native_seq_replace xs pattern replacement) replacement = true :=
    native_seq_contains_replacement_of_pattern_present
      xs pattern replacement hPatternPresent
  have hInnerAbsent :
      native_seq_contains xs (native_seq_replace xs pattern replacement) =
        false := by
    cases h :
        native_seq_contains xs (native_seq_replace xs pattern replacement)
    · rfl
    · have hContradiction := native_seq_contains_trans xs
          (native_seq_replace xs pattern replacement) replacement
          h hInnerReplacement
      rw [hContradiction] at hReplacementAbsent
      contradiction
  exact StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
    xs (native_seq_replace xs pattern replacement) outerReplacement
    hInnerAbsent

theorem native_seq_replace_dual_ite1_of_contains_false
    (xs pattern replacement outerReplacement : List SmtValue)
    (hPatternAbsent : native_seq_contains xs pattern = false) :
    native_seq_replace xs
        (native_seq_replace xs pattern replacement) outerReplacement =
      outerReplacement := by
  rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
    xs pattern replacement hPatternAbsent]
  exact StrEqReplSupport.native_seq_replace_self xs outerReplacement

theorem native_seq_replace_tgt_no_contains
    (xs pat blocked repl : List SmtValue)
    (hAbsent : native_seq_contains xs blocked = false) :
    native_seq_replace xs pat (native_seq_replace pat blocked repl) = xs := by
  by_cases hContains : native_seq_contains xs pat = true
  · have hInnerAbsent : native_seq_contains pat blocked = false := by
      cases h : native_seq_contains pat blocked
      · rfl
      · have hContradiction := native_seq_contains_trans xs pat blocked
            hContains h
        rw [hContradiction] at hAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      pat blocked repl hInnerAbsent]
    exact StrEqReplSupport.native_seq_replace_id xs pat
  · have hContainsFalse : native_seq_contains xs pat = false := by
      cases h : native_seq_contains xs pat
      · rfl
      · exact False.elim (hContains h)
    exact StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs pat (native_seq_replace pat blocked repl) hContainsFalse

theorem native_seq_replace_src_tgt_no_contains
    (xs pat replacement innerRepl : List SmtValue)
    (hAbsent : native_seq_contains replacement pat = false) :
    native_seq_replace xs pat
        (native_seq_replace replacement xs innerRepl) =
      native_seq_replace xs pat replacement := by
  by_cases hContains : native_seq_contains xs pat = true
  · have hInnerAbsent :
        native_seq_contains replacement xs = false := by
      cases h : native_seq_contains replacement xs
      · rfl
      · have hContradiction := native_seq_contains_trans
            replacement xs pat h hContains
        rw [hContradiction] at hAbsent
        contradiction
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      replacement xs innerRepl hInnerAbsent]
  · have hContainsFalse : native_seq_contains xs pat = false := by
      cases h : native_seq_contains xs pat
      · rfl
      · exact False.elim (hContains h)
    rw [StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs pat (native_seq_replace replacement xs innerRepl)
      hContainsFalse]
    exact (StrEqReplSupport.native_seq_replace_eq_self_of_contains_false
      xs pat replacement hContainsFalse).symm

theorem native_seq_contains_singleton_iff_mem
    (xs : List SmtValue) (w : SmtValue) :
    native_seq_contains xs [w] = true ↔ w ∈ xs := by
  constructor
  · intro h
    rcases (native_seq_contains_iff_decomp xs [w]).1 h with
      ⟨before, after, hXs⟩
    rw [hXs]
    simp
  · intro h
    rcases List.mem_iff_append.mp h with ⟨before, after, hXs⟩
    rw [hXs]
    simpa [List.append_assoc] using
      native_seq_contains_of_decomp before [w] after

theorem native_seq_contains_nil (xs : List SmtValue) :
    native_seq_contains xs [] = true := by
  simpa using native_seq_contains_of_decomp [] [] xs

theorem native_seq_replace_eq_self_of_contains_false
    (xs pat repl : List SmtValue)
    (hContains : native_seq_contains xs pat = false) :
    native_seq_replace xs pat repl = xs := by
  have hNot : ¬ 0 ≤ native_seq_indexof xs pat 0 := by
    unfold native_seq_contains at hContains
    simpa using hContains
  have hNeg := Int.lt_of_not_ge hNot
  cases pat with
  | nil =>
      have hNil := native_seq_contains_nil xs
      rw [hNil] at hContains
      contradiction
  | cons p ps =>
      simp [native_seq_replace, hNeg]

theorem mem_native_seq_replace_iff_of_not_mem_pattern
    (w : SmtValue) (xs pat repl : List SmtValue)
    (hNotMem : w ∉ pat) :
    w ∈ native_seq_replace xs pat repl ↔
      w ∈ xs ∨ (native_seq_contains xs pat = true ∧ w ∈ repl) := by
  cases pat with
  | nil =>
      rw [native_seq_contains_nil]
      simp only [native_seq_replace, List.mem_append, true_and]
      exact or_comm
  | cons p ps =>
      by_cases hContains : native_seq_contains xs (p :: ps) = true
      · have hNonneg : 0 ≤ native_seq_indexof xs (p :: ps) 0 := by
          unfold native_seq_contains at hContains
          exact of_decide_eq_true hContains
        have hNotNeg : ¬ native_seq_indexof xs (p :: ps) 0 < 0 :=
          Int.not_lt_of_ge hNonneg
        let n := Int.toNat (native_seq_indexof xs (p :: ps) 0)
        have hDecomp :
            xs.take n ++ (p :: ps) ++
                xs.drop (n + (p :: ps).length) = xs := by
          simpa [n] using
            StrEqReplSupport.native_seq_indexof_zero_decomp_take_drop
              xs (p :: ps) hNonneg
        have hMemX :
            w ∈ xs ↔
              w ∈ xs.take n ∨
                w ∈ xs.drop (n + (p :: ps).length) := by
          constructor
          · intro hMem
            rw [← hDecomp] at hMem
            simp only [List.mem_append] at hMem
            rcases hMem with hTakeOrPat | hDrop
            · rcases hTakeOrPat with hTake | hPat
              · exact Or.inl hTake
              · exact False.elim (hNotMem hPat)
            · exact Or.inr hDrop
          · intro hMem
            rw [← hDecomp]
            simp only [List.mem_append]
            rcases hMem with hTake | hDrop
            · exact Or.inl (Or.inl hTake)
            · exact Or.inr hDrop
        unfold native_seq_replace
        rw [if_neg hNotNeg]
        change
          w ∈ xs.take n ++ repl ++
              xs.drop (n + (p :: ps).length) ↔
            w ∈ xs ∨
              (native_seq_contains xs (p :: ps) = true ∧ w ∈ repl)
        rw [hContains]
        simp only [true_and, List.mem_append]
        rw [hMemX]
        constructor
        · rintro ((hTake | hRepl) | hDrop)
          · exact Or.inl (Or.inl hTake)
          · exact Or.inr hRepl
          · exact Or.inl (Or.inr hDrop)
        · rintro ((hTake | hDrop) | hRepl)
          · exact Or.inl (Or.inl hTake)
          · exact Or.inr hDrop
          · exact Or.inl (Or.inr hRepl)
      · have hContainsFalse :
            native_seq_contains xs (p :: ps) = false := by
          cases h : native_seq_contains xs (p :: ps)
          · rfl
          · exact False.elim (hContains h)
        rw [native_seq_replace_eq_self_of_contains_false
          xs (p :: ps) repl hContainsFalse, hContainsFalse]
        simp

theorem native_seq_contains_replace_char
    (xs pat repl target : List SmtValue)
    (hLen : target.length = 1)
    (hPatTarget : native_seq_contains pat target = false) :
    native_seq_contains (native_seq_replace xs pat repl) target =
      SmtEval.native_or (native_seq_contains xs target)
        (SmtEval.native_and (native_seq_contains xs pat)
          (native_seq_contains repl target)) := by
  cases target with
  | nil => simp at hLen
  | cons w ws =>
      cases ws with
      | nil =>
          have hNotMem : w ∉ pat := by
            intro hMem
            have hTrue : native_seq_contains pat [w] = true :=
              (native_seq_contains_singleton_iff_mem pat w).2 hMem
            rw [hTrue] at hPatTarget
            contradiction
          apply Bool.eq_iff_iff.mpr
          rw [native_seq_contains_singleton_iff_mem]
          rw [mem_native_seq_replace_iff_of_not_mem_pattern
            w xs pat repl hNotMem]
          simp [SmtEval.native_or, SmtEval.native_and,
            native_seq_contains_singleton_iff_mem]
      | cons v vs => simp at hLen

theorem mem_native_seq_replace_self_iff
    (w : SmtValue) (xs pat : List SmtValue) :
    w ∈ native_seq_replace xs pat xs ↔ w ∈ xs := by
  cases pat with
  | nil =>
      simp [native_seq_replace]
  | cons p ps =>
      by_cases hNeg : native_seq_indexof xs (p :: ps) 0 < 0
      · simp [native_seq_replace, hNeg]
      · unfold native_seq_replace
        rw [if_neg hNeg]
        simp only [List.mem_append]
        constructor
        · intro h
          rcases h with hTakeOrXs | hDrop
          · rcases hTakeOrXs with hTake | hXs
            · exact List.mem_of_mem_take hTake
            · exact hXs
          · exact List.mem_of_mem_drop hDrop
        · intro hXs
          exact Or.inl (Or.inr hXs)

theorem native_seq_contains_replace_self_of_target_len_one
    (xs pat target : List SmtValue) (hLen : target.length = 1) :
    native_seq_contains (native_seq_replace xs pat xs) target =
      native_seq_contains xs target := by
  cases target with
  | nil => simp at hLen
  | cons w ws =>
      cases ws with
      | nil =>
          apply Bool.eq_iff_iff.mpr
          rw [native_seq_contains_singleton_iff_mem,
            native_seq_contains_singleton_iff_mem]
          exact mem_native_seq_replace_self_iff w xs pat
      | cons v vs => simp at hLen

end StrContainsReplCharSupport
