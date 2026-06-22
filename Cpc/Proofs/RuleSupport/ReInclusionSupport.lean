import Cpc.Proofs.RuleSupport.CoreSupport
import Cpc.Proofs.RuleSupport.ReConcatStarSupport
import Cpc.Proofs.RuleSupport.RegexSupport
import Cpc.Proofs.RuleSupport.ReUnfoldNegSupport
import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

def NativeIncludes (sup sub : native_RegLan) : Prop :=
  ∀ str : native_String,
    native_string_valid str = true ->
      native_str_in_re str sub = true ->
        native_str_in_re str sup = true

private def NativePrefixClosed (r : native_RegLan) : Prop :=
  ∀ pre suf : native_String,
    native_string_valid (pre ++ suf) = true ->
      native_str_in_re suf r = true ->
        native_str_in_re (pre ++ suf) r = true

theorem native_includes_refl (r : native_RegLan) :
    NativeIncludes r r := by
  intro _str _hValid hMem
  exact hMem

theorem native_includes_trans {r s t : native_RegLan}
    (hrs : NativeIncludes r s) (hst : NativeIncludes s t) :
    NativeIncludes r t := by
  intro str hValid hMem
  exact hrs str hValid (hst str hValid hMem)

theorem native_includes_of_smt_value_rel {r s : native_RegLan}
    (hRel : RuleProofs.smt_value_rel (SmtValue.RegLan r)
      (SmtValue.RegLan s)) :
    NativeIncludes r s := by
  intro str hValid hMem
  rwa [smt_value_rel_reglan_valid_eq hRel hValid]

private theorem native_includes_congr
    {sup sub flatSup flatSub : native_RegLan}
    (hSupRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatSup)
        (SmtValue.RegLan sup))
    (hSubRel :
      RuleProofs.smt_value_rel (SmtValue.RegLan flatSub)
        (SmtValue.RegLan sub))
    (hFlat : NativeIncludes flatSup flatSub) :
    NativeIncludes sup sub := by
  have hSupToFlat : NativeIncludes sup flatSup :=
    native_includes_of_smt_value_rel
      (RuleProofs.smt_value_rel_symm _ _ hSupRel)
  have hFlatSub : NativeIncludes flatSub sub :=
    native_includes_of_smt_value_rel hSubRel
  exact native_includes_trans hSupToFlat
    (native_includes_trans hFlat hFlatSub)

theorem native_includes_inter_left (r s : native_RegLan) :
    NativeIncludes r (native_re_inter r s) := by
  intro str _hValid hMem
  rw [native_str_in_re_re_inter] at hMem
  simp only [Bool.and_eq_true] at hMem
  exact hMem.1

theorem native_includes_inter_right (r s : native_RegLan) :
    NativeIncludes s (native_re_inter r s) := by
  intro str _hValid hMem
  rw [native_str_in_re_re_inter] at hMem
  simp only [Bool.and_eq_true] at hMem
  exact hMem.2

theorem native_includes_re_all (r : native_RegLan) :
    NativeIncludes native_re_all r := by
  intro str hValid _hMem
  exact native_str_in_re_re_all str hValid

theorem native_includes_concat
    {r1 r2 s1 s2 : native_RegLan}
    (h1 : NativeIncludes r1 s1) (h2 : NativeIncludes r2 s2) :
    NativeIncludes (native_re_concat r1 r2) (native_re_concat s1 s2) := by
  intro str hValid hMem
  have hListMem :
      nativeListInRe str (native_re_mk_concat s1 s2) = true := by
    simpa [native_str_in_re, hValid, native_re_concat, nativeListInRe] using hMem
  rcases (nativeListInRe_mk_concat_true_iff_exists_append str s1 s2).1 hListMem with
    ⟨xs1, xs2, hAppend, hLeft, hRight⟩
  have hValid1 : native_string_valid xs1 = true :=
    native_string_valid_append_left xs1 xs2 (by simpa [hAppend] using hValid)
  have hValid2 : native_string_valid xs2 = true :=
    native_string_valid_append_right xs1 xs2 (by simpa [hAppend] using hValid)
  have hLeft' : nativeListInRe xs1 r1 = true := by
    have hMemLeft : native_str_in_re xs1 s1 = true := by
      simpa [native_str_in_re, hValid1, nativeListInRe] using hLeft
    have hMemLeft' := h1 xs1 hValid1 hMemLeft
    simpa [native_str_in_re, hValid1, nativeListInRe] using hMemLeft'
  have hRight' : nativeListInRe xs2 r2 = true := by
    have hMemRight : native_str_in_re xs2 s2 = true := by
      simpa [native_str_in_re, hValid2, nativeListInRe] using hRight
    have hMemRight' := h2 xs2 hValid2 hMemRight
    simpa [native_str_in_re, hValid2, nativeListInRe] using hMemRight'
  have hConcat :
      nativeListInRe str (native_re_mk_concat r1 r2) = true :=
    (nativeListInRe_mk_concat_true_iff_exists_append str r1 r2).2
      ⟨xs1, xs2, hAppend, hLeft', hRight'⟩
  simpa [native_str_in_re, hValid, native_re_concat, nativeListInRe] using hConcat

private theorem native_includes_concat_left_of_prefix_closed
    {sup tail r : native_RegLan}
    (hClosed : NativePrefixClosed sup)
    (hTail : NativeIncludes sup tail) :
    NativeIncludes sup (native_re_concat r tail) := by
  intro str hValid hMem
  have hListMem :
      nativeListInRe str (native_re_mk_concat r tail) = true := by
    simpa [native_str_in_re, hValid, native_re_concat, nativeListInRe] using hMem
  rcases (nativeListInRe_mk_concat_true_iff_exists_append str r tail).1
      hListMem with
    ⟨xs1, xs2, hAppend, hLeft, hRight⟩
  have hXs2Valid : native_string_valid xs2 = true :=
    native_string_valid_append_right xs1 xs2 (by simpa [hAppend] using hValid)
  have hTailMem : native_str_in_re xs2 tail = true := by
    simpa [native_str_in_re, hXs2Valid, nativeListInRe] using hRight
  have hSupXs2 : native_str_in_re xs2 sup = true :=
    hTail xs2 hXs2Valid hTailMem
  simpa [hAppend] using hClosed xs1 xs2 (by simpa [hAppend] using hValid)
    hSupXs2

private theorem native_prefix_closed_all_concat (tail : native_RegLan) :
    NativePrefixClosed (native_re_concat native_re_all tail) := by
  intro pre suf hValid hMem
  have hSufValid : native_string_valid suf = true :=
    native_string_valid_append_right pre suf hValid
  have hListMem :
      nativeListInRe suf (native_re_mk_concat native_re_all tail) = true := by
    simpa [native_str_in_re, hSufValid, native_re_concat, nativeListInRe] using hMem
  rcases (nativeListInRe_mk_concat_true_iff_exists_append suf
      native_re_all tail).1 hListMem with
    ⟨xs1, xs2, hAppend, hLeft, hRight⟩
  have hPrefixValid :
      native_string_valid (pre ++ xs1) = true := by
    have hAll : native_string_valid ((pre ++ xs1) ++ xs2) = true := by
      rw [List.append_assoc, hAppend]
      exact hValid
    exact native_string_valid_append_left (pre ++ xs1) xs2 hAll
  have hAllPrefix :
      nativeListInRe (pre ++ xs1) native_re_all = true := by
    apply nativeListInRe_re_all
    simpa [native_string_valid] using hPrefixValid
  have hConcat :
      nativeListInRe ((pre ++ xs1) ++ xs2)
          (native_re_mk_concat native_re_all tail) = true :=
    (nativeListInRe_mk_concat_true_iff_exists_append ((pre ++ xs1) ++ xs2)
      native_re_all tail).2
      ⟨pre ++ xs1, xs2, rfl, hAllPrefix, hRight⟩
  simpa [native_str_in_re, hValid, native_re_concat, nativeListInRe,
    List.append_assoc, hAppend] using hConcat

private theorem native_prefix_closed_allchar_concat
    {tail : native_RegLan}
    (hTail : NativePrefixClosed tail) :
    NativePrefixClosed (native_re_concat native_re_allchar tail) := by
  intro pre suf hValid hMem
  cases pre with
  | nil =>
      simpa using hMem
  | cons c cs =>
      have hTailValidAll : native_string_valid (cs ++ suf) = true := by
        rcases native_string_valid_cons_parts (by simpa using hValid) with
          ⟨_hc, hRest⟩
        exact hRest
      have hSufValid : native_string_valid suf = true :=
        native_string_valid_append_right cs suf hTailValidAll
      have hListMem :
          nativeListInRe suf (native_re_mk_concat native_re_allchar tail) =
            true := by
        simpa [native_str_in_re, hSufValid, native_re_concat, nativeListInRe] using hMem
      rcases (nativeListInRe_mk_concat_true_iff_exists_append suf
          native_re_allchar tail).1 hListMem with
        ⟨xs1, xs2, hAppend, hLeft, hRight⟩
      have hLeftParts := (nativeListInRe_allchar_true_iff xs1).1 hLeft
      have hTailMem : native_str_in_re xs2 tail = true := by
        have hXs2Valid : native_string_valid xs2 = true := by
          have hSufValid' : native_string_valid (xs1 ++ xs2) = true := by
            simpa [hAppend] using hSufValid
          exact native_string_valid_append_right xs1 xs2 hSufValid'
        simpa [native_str_in_re, hXs2Valid, nativeListInRe] using hRight
      have hTailClosed :
          native_str_in_re ((cs ++ xs1) ++ xs2) tail = true := by
        have hClosedValid : native_string_valid ((cs ++ xs1) ++ xs2) = true := by
          rw [List.append_assoc, hAppend]
          exact hTailValidAll
        exact hTail (cs ++ xs1) xs2 hClosedValid hTailMem
      have hcValid : native_char_valid c = true :=
        (native_string_valid_cons_parts (by simpa using hValid)).1
      have hAllchar :
          native_str_in_re [c] native_re_allchar = true := by
        have hValidOne : native_string_valid [c] = true := by
          change native_char_valid c && true = true
          simp [hcValid]
        have hList :
            nativeListInRe [c] native_re_allchar = true :=
          (nativeListInRe_allchar_true_iff [c]).2 (by
            simp [hcValid])
        simpa [native_str_in_re, hValidOne, nativeListInRe] using hList
      have hConcatMem :=
        native_str_in_re_re_concat_intro [c] ((cs ++ xs1) ++ xs2)
          native_re_allchar tail hAllchar hTailClosed
      simpa [native_re_concat, List.append_assoc, hAppend] using hConcatMem

private theorem native_string_valid_cons_of_parts
    {c : native_Char} {cs : native_String}
    (hc : native_char_valid c = true)
    (hcs : native_string_valid cs = true) :
    native_string_valid (c :: cs) = true := by
  change (native_char_valid c && native_string_valid cs) = true
  simp [hc, hcs]

private theorem nativeListInRe_raw_star_once :
    (xs : List native_Char) -> (r : native_RegLan) ->
      nativeListInRe xs r = true ->
        nativeListInRe xs (SmtRegLan.star r) = true
  | [], r, _hMem => by
      simp [nativeListInRe, native_re_nullable]
  | c :: cs, r, hMem => by
      have hDer : nativeListInRe cs (native_re_deriv c r) = true := by
        simpa [nativeListInRe] using hMem
      have hNil : nativeListInRe [] (SmtRegLan.star r) = true := by
        simp [nativeListInRe, native_re_nullable]
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r) (SmtRegLan.star r)) =
            true :=
        (nativeListInRe_mk_concat_true_iff_exists_append cs
          (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨cs, [], by simp, hDer, hNil⟩
      simpa [nativeListInRe, native_re_deriv] using hConcat

private theorem nativeListInRe_mk_star_once
    (xs : List native_Char) (r : native_RegLan)
    (hMem : nativeListInRe xs r = true) :
    nativeListInRe xs (native_re_mk_star r) = true := by
  cases r with
  | empty =>
      have hFalse := nativeListInRe_empty xs
      rw [hFalse] at hMem
      cases hMem
  | epsilon =>
      have hNil : xs = [] := (nativeListInRe_epsilon_iff xs).1 hMem
      subst xs
      simp [native_re_mk_star, nativeListInRe, native_re_nullable]
  | star r =>
      simpa [native_re_mk_star] using hMem
  | char c =>
      simpa [native_re_mk_star] using
        nativeListInRe_raw_star_once xs (SmtRegLan.char c) hMem
  | range lo hi =>
      simpa [native_re_mk_star] using
        nativeListInRe_raw_star_once xs (SmtRegLan.range lo hi) hMem
  | allchar =>
      simpa [native_re_mk_star] using
        nativeListInRe_raw_star_once xs SmtRegLan.allchar hMem
  | concat r s =>
      simpa [native_re_mk_star] using
        nativeListInRe_raw_star_once xs (SmtRegLan.concat r s) hMem
  | union r s =>
      simpa [native_re_mk_star] using
        nativeListInRe_raw_star_once xs (SmtRegLan.union r s) hMem
  | inter r s =>
      simpa [native_re_mk_star] using
        nativeListInRe_raw_star_once xs (SmtRegLan.inter r s) hMem
  | comp r =>
      simpa [native_re_mk_star] using
        nativeListInRe_raw_star_once xs (SmtRegLan.comp r) hMem

private theorem nativeListInRe_raw_star_mono :
    (xs : List native_Char) -> (rSup rSub : native_RegLan) ->
      native_string_valid xs = true ->
      (∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys rSub = true ->
            nativeListInRe ys rSup = true) ->
      nativeListInRe xs (SmtRegLan.star rSub) = true ->
        nativeListInRe xs (native_re_mk_star rSup) = true
  | [], rSup, _rSub, _hValid, _hIncl, _hMem => by
      exact nativeListInRe_nil_mk_star rSup
  | c :: cs, rSup, rSub, hValid, hIncl, hMem => by
      rcases native_string_valid_cons_parts hValid with ⟨hc, hcs⟩
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c rSub)
                (SmtRegLan.star rSub)) = true := by
        simpa [nativeListInRe, native_re_deriv] using hMem
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append cs
            (native_re_deriv c rSub) (SmtRegLan.star rSub)).1 hConcat with
        ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
      have hAppendValid : native_string_valid (xs₁ ++ xs₂) = true := by
        rw [hAppend]
        exact hcs
      have hValid₁ := native_string_valid_append_left xs₁ xs₂ hAppendValid
      have hValid₂ := native_string_valid_append_right xs₁ xs₂ hAppendValid
      have hChunkSub : nativeListInRe (c :: xs₁) rSub = true := by
        simpa [nativeListInRe] using hLeft
      have hChunkValid : native_string_valid (c :: xs₁) = true :=
        native_string_valid_cons_of_parts hc hValid₁
      have hChunkSup : nativeListInRe (c :: xs₁) rSup = true :=
        hIncl (c :: xs₁) hChunkValid hChunkSub
      have hChunkStar :
          nativeListInRe (c :: xs₁) (native_re_mk_star rSup) = true :=
        nativeListInRe_mk_star_once (c :: xs₁) rSup hChunkSup
      have hTailStar :
          nativeListInRe xs₂ (native_re_mk_star rSup) = true :=
        nativeListInRe_raw_star_mono xs₂ rSup rSub hValid₂ hIncl hRight
      have hJoin :
          nativeListInRe ((c :: xs₁) ++ xs₂) (native_re_mk_star rSup) = true :=
        nativeListInRe_mk_star_append (c :: xs₁) xs₂ rSup hChunkStar hTailStar
      simpa [hAppend] using hJoin
termination_by xs _ _ _ _ _ => xs.length
decreasing_by
  all_goals
    have hLenEq := congrArg List.length hAppend
    simp at hLenEq ⊢
    omega

private theorem nativeListInRe_mk_star_mono
    (xs : List native_Char) (rSup rSub : native_RegLan)
    (hValid : native_string_valid xs = true)
    (hIncl :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys rSub = true ->
            nativeListInRe ys rSup = true)
    (hMem : nativeListInRe xs (native_re_mk_star rSub) = true) :
    nativeListInRe xs (native_re_mk_star rSup) = true := by
  cases rSub with
  | empty =>
      have hNil : xs = [] := by
        cases xs with
        | nil => rfl
        | cons c cs =>
            simp [native_re_mk_star, nativeListInRe, native_re_deriv] at hMem
            have hEmpty := nativeListInRe_empty cs
            unfold nativeListInRe at hEmpty
            rw [hEmpty] at hMem
            simp at hMem
      subst xs
      exact nativeListInRe_nil_mk_star rSup
  | epsilon =>
      have hNil : xs = [] := (nativeListInRe_epsilon_iff xs).1 (by
        simpa [native_re_mk_star] using hMem)
      subst xs
      exact nativeListInRe_nil_mk_star rSup
  | star r =>
      have hAsSub : nativeListInRe xs (SmtRegLan.star r) = true := by
        simpa [native_re_mk_star] using hMem
      exact nativeListInRe_mk_star_once xs rSup (hIncl xs hValid hAsSub)
  | char c =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.char c) hValid
        hIncl (by simpa [native_re_mk_star] using hMem)
  | range lo hi =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.range lo hi) hValid
        hIncl (by simpa [native_re_mk_star] using hMem)
  | allchar =>
      exact nativeListInRe_raw_star_mono xs rSup SmtRegLan.allchar hValid
        hIncl (by simpa [native_re_mk_star] using hMem)
  | concat r s =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.concat r s) hValid
        hIncl (by simpa [native_re_mk_star] using hMem)
  | union r s =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.union r s) hValid
        hIncl (by simpa [native_re_mk_star] using hMem)
  | inter r s =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.inter r s) hValid
        hIncl (by simpa [native_re_mk_star] using hMem)
  | comp r =>
      exact nativeListInRe_raw_star_mono xs rSup (SmtRegLan.comp r) hValid
        hIncl (by simpa [native_re_mk_star] using hMem)

theorem native_includes_star_self (r : native_RegLan) :
    NativeIncludes (native_re_mult r) r := by
  intro str hValid hMem
  have hList : nativeListInRe str r = true := by
    simpa [native_str_in_re, hValid, nativeListInRe] using hMem
  have hStar := nativeListInRe_mk_star_once str r hList
  simpa [native_str_in_re, hValid, native_re_mult, nativeListInRe] using hStar

theorem native_includes_star_mono {rSup rSub : native_RegLan}
    (hIncl : NativeIncludes rSup rSub) :
    NativeIncludes (native_re_mult rSup) (native_re_mult rSub) := by
  intro str hValid hMem
  have hList :
      nativeListInRe str (native_re_mk_star rSub) = true := by
    simpa [native_str_in_re, hValid, native_re_mult, nativeListInRe] using hMem
  have hInclList :
      ∀ ys : List native_Char,
        native_string_valid ys = true ->
          nativeListInRe ys rSub = true ->
            nativeListInRe ys rSup = true := by
    intro ys hys hysMem
    have hNative : native_str_in_re ys rSub = true := by
      simpa [native_str_in_re, hys, nativeListInRe] using hysMem
    have hNative' := hIncl ys hys hNative
    simpa [native_str_in_re, hys, nativeListInRe] using hNative'
  have hStar := nativeListInRe_mk_star_mono str rSup rSub hValid hInclList hList
  simpa [native_str_in_re, hValid, native_re_mult, nativeListInRe] using hStar

private theorem nativeListInRe_char_true_eq
    (xs : List native_Char) (c : native_Char)
    (hMem : nativeListInRe xs (SmtRegLan.char c) = true) :
    xs = [c] := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_nullable] at hMem
  | cons d ds =>
      cases ds with
      | nil =>
          by_cases hd : native_char_valid d = true <;>
            by_cases hc : native_char_valid c = true <;>
            by_cases hdc : d = c <;>
            simp [nativeListInRe, native_re_deriv, native_re_nullable,
              hd, hc, hdc] at hMem
          all_goals
            subst d
            rfl
      | cons e es =>
          by_cases hd : native_char_valid d = true <;>
            by_cases hc : native_char_valid c = true <;>
            by_cases hdc : d = c <;>
            simp [nativeListInRe, native_re_deriv, hd, hc, hdc] at hMem
          all_goals
            have hEmpty := nativeListInRe_empty es
            unfold nativeListInRe at hEmpty
            rw [hEmpty] at hMem
            cases hMem

private theorem nativeListInRe_re_of_list_true_eq :
    (pat xs : List native_Char) ->
      nativeListInRe xs (native_re_of_list pat) = true ->
        xs = pat
  | [], xs, hMem => by
      exact (nativeListInRe_epsilon_iff xs).1 (by
        simpa [native_re_of_list] using hMem)
  | c :: pat, xs, hMem => by
      have hConcat :
          nativeListInRe xs
              (native_re_mk_concat (SmtRegLan.char c)
                (native_re_of_list pat)) = true := by
        simpa [native_re_of_list] using hMem
      rcases
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (SmtRegLan.char c) (native_re_of_list pat)).1 hConcat with
        ⟨left, right, hAppend, hLeft, hRight⟩
      have hLeftEq : left = [c] :=
        nativeListInRe_char_true_eq left c hLeft
      have hRightEq : right = pat :=
        nativeListInRe_re_of_list_true_eq pat right hRight
      subst left
      subst right
      simpa using hAppend.symm

theorem native_str_in_re_str_to_re_eq
    {str pat : native_String}
    (hValid : native_string_valid str = true)
    (hMem : native_str_in_re str (native_str_to_re pat) = true) :
    str = pat := by
  have hList : nativeListInRe str (native_re_of_list pat) = true := by
    simpa [native_str_in_re, hValid, native_str_to_re, nativeListInRe] using hMem
  exact nativeListInRe_re_of_list_true_eq pat str hList

private theorem native_includes_range_singleton
    {loSup hiSup loSub hiSub : native_Char}
    (hLoSup : native_char_valid loSup = true)
    (hHiSup : native_char_valid hiSup = true)
    (hLoSub : native_char_valid loSub = true)
    (hHiSub : native_char_valid hiSub = true)
    (hLo : loSup ≤ loSub)
    (hHi : hiSub ≤ hiSup) :
    NativeIncludes
      (native_re_range [loSup] [hiSup])
      (native_re_range [loSub] [hiSub]) := by
  intro str hValid hMem
  cases str with
  | nil =>
      simp [native_re_range, native_str_in_re, hValid,
        native_re_nullable] at hMem
  | cons c rest =>
      rcases native_string_valid_cons_parts hValid with ⟨hc, hRestValid⟩
      cases rest with
      | nil =>
          have hBounds : loSub ≤ c ∧ c ≤ hiSub := by
            by_cases hb : loSub ≤ c ∧ c ≤ hiSub
            · exact hb
            · simp [native_re_range, native_str_in_re, hValid,
                native_re_deriv, native_re_nullable, hc, hLoSub, hHiSub,
                hb] at hMem
          have hSupBounds : loSup ≤ c ∧ c ≤ hiSup := by
            exact ⟨Nat.le_trans hLo hBounds.1, Nat.le_trans hBounds.2 hHi⟩
          simp [native_re_range, native_str_in_re, hValid,
            native_re_deriv, native_re_nullable, hc, hLoSup, hHiSup,
            hSupBounds.1, hSupBounds.2]
      | cons d ds =>
          have hTailEmpty := nativeListInRe_empty ds
          by_cases hb : loSub ≤ c ∧ c ≤ hiSub
          · simp [native_re_range, native_str_in_re, hValid,
              native_re_deriv, hc, hLoSub, hHiSub, hb] at hMem
            unfold nativeListInRe at hTailEmpty
            rw [hTailEmpty] at hMem
            cases hMem
          · simp [native_re_range, native_str_in_re, hValid,
              native_re_deriv, hc, hLoSub, hHiSub, hb] at hMem
            unfold nativeListInRe at hTailEmpty
            rw [hTailEmpty] at hMem
            cases hMem

theorem native_str_in_re_re_none (str : native_String) :
    native_str_in_re str native_re_none = false := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, native_re_none, nativeListInRe] using
      nativeListInRe_empty str
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_union
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_union r s) =
      (native_str_in_re str r || native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, native_re_union, nativeListInRe] using
      nativeListInRe_mk_union str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_includes_union_left (r s : native_RegLan) :
    NativeIncludes (native_re_union r s) r := by
  intro str _hValid hMem
  rw [native_str_in_re_re_union]
  simp [hMem]

theorem native_includes_union_right (r s : native_RegLan) :
    NativeIncludes (native_re_union r s) s := by
  intro str _hValid hMem
  rw [native_str_in_re_re_union]
  simp [hMem]

theorem smt_value_rel_re_inter_self_comp_all_none (r : native_RegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter r (native_re_inter (native_re_comp r) native_re_all)))
      (SmtValue.RegLan native_re_none) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_inter r (native_re_inter (native_re_comp r) native_re_all))
        native_re_none) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
    native_str_in_re_re_comp, native_str_in_re_re_all _ hValid,
    native_str_in_re_re_none]
  cases hMem : native_str_in_re str r <;> simp [hValid]

theorem smt_value_rel_re_inter_subset_comp_all_none
    (r1 r2 : native_RegLan)
    (hSub : NativeIncludes r2 r1) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_inter r1 (native_re_inter (native_re_comp r2) native_re_all)))
      (SmtValue.RegLan native_re_none) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_inter r1 (native_re_inter (native_re_comp r2) native_re_all))
        native_re_none) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_re_inter, native_str_in_re_re_inter,
    native_str_in_re_re_comp, native_str_in_re_re_all _ hValid,
    native_str_in_re_re_none]
  cases hMem1 : native_str_in_re str r1
  · simp [hValid]
  · have hMem2 : native_str_in_re str r2 = true :=
      hSub str hValid hMem1
    simp [hValid, hMem2]

theorem smt_value_rel_re_union_self_comp_none_all (r : native_RegLan) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_union r (native_re_union (native_re_comp r) native_re_none)))
      (SmtValue.RegLan native_re_all) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_union r (native_re_union (native_re_comp r) native_re_none))
        native_re_all) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    native_str_in_re_re_comp, native_str_in_re_re_none,
    native_str_in_re_re_all _ hValid]
  cases hMem : native_str_in_re str r <;> simp [hValid]

theorem smt_value_rel_re_union_subset_comp_none_all
    (r1 r2 : native_RegLan)
    (hSub : NativeIncludes r1 r2) :
    RuleProofs.smt_value_rel
      (SmtValue.RegLan
        (native_re_union r1 (native_re_union (native_re_comp r2) native_re_none)))
      (SmtValue.RegLan native_re_all) := by
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change SmtValue.Boolean
      (native_re_ext_eq
        (native_re_union r1 (native_re_union (native_re_comp r2) native_re_none))
        native_re_all) =
    SmtValue.Boolean true
  simp
  intro str hValid
  rw [native_str_in_re_re_union, native_str_in_re_re_union,
    native_str_in_re_re_comp, native_str_in_re_re_none,
    native_str_in_re_re_all _ hValid]
  cases hMem2 : native_str_in_re str r2
  · simp [hValid]
  · have hMem1 : native_str_in_re str r1 = true :=
      hSub str hValid hMem2
    simp [hValid, hMem1]

theorem smtx_model_eval_re_mult_allchar :
    __smtx_model_eval_re_mult (SmtValue.RegLan native_re_allchar) =
      SmtValue.RegLan native_re_all := by
  simp [__smtx_model_eval_re_mult, native_re_mult, native_re_allchar,
    native_re_all, native_re_mk_star]

private theorem smtx_model_eval_sigma_star_concat_eps (M : SmtModel) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.UOp UserOp.re_mult)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String []))))) =
      SmtValue.RegLan native_re_all := by
  change __smtx_model_eval M
      (SmtTerm.re_mult
        (SmtTerm.re_concat SmtTerm.re_allchar
          (SmtTerm.str_to_re (SmtTerm.String [])))) =
    SmtValue.RegLan native_re_all
  simp [__smtx_model_eval, __smtx_model_eval_re_mult,
    __smtx_model_eval_re_concat, __smtx_model_eval_str_to_re,
    native_unpack_string_pack_string, native_re_mult, native_re_concat,
    native_re_allchar, native_re_all, native_str_to_re, native_re_of_list,
    native_re_mk_concat, native_re_mk_star]

theorem smt_model_eval_reglan_of_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (hTy : __smtx_typeof (__eo_to_smt t) = SmtType.RegLan) :
    ∃ r : native_RegLan,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r := by
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact reglan_value_canonical hEvalTy

private theorem eo_ite_true_result
    (c e : Term)
    (h : __eo_ite c (Term.Boolean true) e = Term.Boolean true) :
    c = Term.Boolean true ∨
      c = Term.Boolean false ∧ e = Term.Boolean true := by
  have hNe : __eo_ite c (Term.Boolean true) e ≠ Term.Stuck := by
    rw [h]
    decide
  rcases eo_ite_cases_of_ne_stuck c (Term.Boolean true) e hNe with hc | hc
  · exact Or.inl hc
  · exact Or.inr ⟨hc, by simpa [hc, eo_ite_false] using h⟩

private theorem eo_ite_false_else_true
    (c x : Term)
    (h : __eo_ite c x (Term.Boolean false) = Term.Boolean true) :
    c = Term.Boolean true ∧ x = Term.Boolean true := by
  have hNe : __eo_ite c x (Term.Boolean false) ≠ Term.Stuck := by
    rw [h]
    decide
  rcases eo_ite_cases_of_ne_stuck c x (Term.Boolean false) hNe with hc | hc
  · exact ⟨hc, by simpa [hc, eo_ite_true] using h⟩
  · simp [hc, eo_ite_false] at h

private theorem eo_and_eq_true
    (a b : Term)
    (h : __eo_and a b = Term.Boolean true) :
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  cases a <;> cases b <;>
    try simp [__eo_and] at h
  case Boolean.Boolean x y =>
    simpa [__eo_and, SmtEval.native_and] using h
  case Binary.Binary w1 n1 w2 n2 =>
    simp [__eo_requires, native_ite, native_teq, native_not] at h
    split at h <;> cases h

private theorem eo_requires_true_parts
    (x y z : Term)
    (h : __eo_requires x y z = Term.Boolean true) :
    x = y ∧ z = Term.Boolean true := by
  have hNe : __eo_requires x y z ≠ Term.Stuck := by
    rw [h]
    decide
  have hxy := eo_requires_eq_of_ne_stuck x y z hNe
  have hres := eo_requires_eq_result_of_ne_stuck x y z hNe
  exact ⟨hxy, by simpa [hres] using h⟩

private theorem int_ge_of_eo_eq_or_gt_true
    (a b : native_Int)
    (h :
      __eo_ite (__eo_eq (Term.Numeral a) (Term.Numeral b))
          (Term.Boolean true)
          (__eo_gt (Term.Numeral a) (Term.Numeral b)) =
        Term.Boolean true) :
    b ≤ a := by
  rcases eo_ite_true_result (__eo_eq (Term.Numeral a) (Term.Numeral b))
      (__eo_gt (Term.Numeral a) (Term.Numeral b)) h with hEq | hElse
  · have hTerm := eq_of_eo_eq_true (Term.Numeral a) (Term.Numeral b) hEq
    cases hTerm
    exact Int.le_refl _
  · have hGt : __eo_gt (Term.Numeral a) (Term.Numeral b) =
        Term.Boolean true := hElse.2
    simp [__eo_gt, native_zlt] at hGt
    exact Int.le_of_lt hGt

private theorem native_includes_of_same_term_eval
    (M : SmtModel) (t : Term) (rv1 rv2 : native_RegLan)
    (hEval1 : __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan rv1)
    (hEval2 : __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan rv2) :
    NativeIncludes rv1 rv2 := by
  rw [hEval1] at hEval2
  cases hEval2
  exact native_includes_refl rv1

private theorem eval_re_union_reglan
    (M : SmtModel) (a b : Term) (ra rb : native_RegLan)
    (hA : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hB : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
      SmtValue.RegLan (native_re_union ra rb) := by
  change __smtx_model_eval M
      (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) =
    SmtValue.RegLan (native_re_union ra rb)
  simp [__smtx_model_eval, __smtx_model_eval_re_union, hA, hB]

private theorem eval_re_inter_reglan
    (M : SmtModel) (a b : Term) (ra rb : native_RegLan)
    (hA : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hB : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
      SmtValue.RegLan (native_re_inter ra rb) := by
  change __smtx_model_eval M
      (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
    SmtValue.RegLan (native_re_inter ra rb)
  simp [__smtx_model_eval, __smtx_model_eval_re_inter, hA, hB]

private theorem eval_re_concat_reglan
    (M : SmtModel) (a b : Term) (ra rb : native_RegLan)
    (hA : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra)
    (hB : __smtx_model_eval M (__eo_to_smt b) = SmtValue.RegLan rb) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
      SmtValue.RegLan (native_re_concat ra rb) := by
  change __smtx_model_eval M
      (SmtTerm.re_concat (__eo_to_smt a) (__eo_to_smt b)) =
    SmtValue.RegLan (native_re_concat ra rb)
  simp [__smtx_model_eval, __smtx_model_eval_re_concat, hA, hB]

private theorem eval_re_mult_reglan
    (M : SmtModel) (a : Term) (ra : native_RegLan)
    (hA : __smtx_model_eval M (__eo_to_smt a) = SmtValue.RegLan ra) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) a)) =
      SmtValue.RegLan (native_re_mult ra) := by
  change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt a)) =
    SmtValue.RegLan (native_re_mult ra)
  simp [__smtx_model_eval, __smtx_model_eval_re_mult, hA]

private theorem re_union_arg_types_of_reglan (a b : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) a) b)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_union (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.RegLan at hTy
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
    (typeof_re_union_eq (__eo_to_smt a) (__eo_to_smt b)) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

private theorem re_inter_arg_types_of_reglan (a b : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) a) b)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan := by
  change __smtx_typeof
      (SmtTerm.re_inter (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.RegLan at hTy
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
    (typeof_re_inter_eq (__eo_to_smt a) (__eo_to_smt b)) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

private theorem re_concat_arg_types_of_reglan (a b : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) a) b)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt b) = SmtType.RegLan := by
  exact RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_concat_args_of_reglan
    a b hTy

private theorem re_mult_arg_type_of_reglan (a : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.re_mult) a)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt a) = SmtType.RegLan := by
  exact RuleProofs.ReUnfoldNegSupport.smtx_typeof_re_mult_arg_of_reglan a hTy

private theorem str_to_re_arg_type_of_reglan (s : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.str_to_re) s)) =
        SmtType.RegLan) :
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtType.RegLan at hTy
  exact seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
    (typeof_str_to_re_eq (__eo_to_smt s)) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

private theorem re_range_arg_types_of_reglan (lo hi : Term)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) lo) hi)) =
        SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt lo) = SmtType.Seq SmtType.Char ∧
      __smtx_typeof (__eo_to_smt hi) = SmtType.Seq SmtType.Char := by
  change __smtx_typeof
      (SmtTerm.re_range (__eo_to_smt lo) (__eo_to_smt hi)) =
    SmtType.RegLan at hTy
  exact seq_char_binop_args_of_non_none (op := SmtTerm.re_range)
    (typeof_re_range_eq (__eo_to_smt lo) (__eo_to_smt hi)) (by
      unfold term_has_non_none_type
      rw [hTy]
      simp)

private theorem seq_char_term_to_z_singleton
    (s : Term)
    (hTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hNonneg : __eo_is_neg (__eo_to_z s) = Term.Boolean false) :
    ∃ c : native_Char,
      s = Term.String [c] ∧
        native_char_valid c = true ∧
        __eo_to_z s = Term.Numeral (Int.ofNat c) := by
  cases s with
  | Numeral n =>
      have hTo :
          __eo_to_smt (Term.Numeral n) = SmtTerm.Numeral n := rfl
      rw [hTo] at hTy
      rw [__smtx_typeof.eq_2] at hTy
      cases hTy
  | Rational q =>
      have hTo :
          __eo_to_smt (Term.Rational q) = SmtTerm.Rational q := rfl
      rw [hTo] at hTy
      rw [__smtx_typeof.eq_3] at hTy
      cases hTy
  | Binary w n =>
      have hTo :
          __eo_to_smt (Term.Binary w n) = SmtTerm.Binary w n := rfl
      rw [hTo] at hTy
      rw [__smtx_typeof.eq_5] at hTy
      cases hOk :
          native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [native_ite, hOk] at hTy
  | String xs =>
    cases xs with
    | nil =>
        simp [__eo_to_z, __eo_is_neg, native_ite, native_zeq,
          native_str_len] at hNonneg
    | cons c rest =>
        cases rest with
        | nil =>
            have hStringValid :
                native_string_valid [c] = true :=
              native_string_valid_of_smtx_typeof_eo_string [c]
                (by simpa using hTy)
            have hc : native_char_valid c = true :=
              (native_string_valid_cons_parts hStringValid).1
            refine ⟨c, rfl, hc, ?_⟩
            simp [__eo_to_z, native_ite, native_zeq, native_str_len,
              native_str_to_code, hc]
        | cons d ds =>
            have hLenNe :
                ¬ (1 : native_Int) = (↑ds.length + 1 + 1 : native_Int) := by
              intro hEq
              have hEqNat : (1 : Nat) = ds.length + 1 + 1 := by
                exact_mod_cast hEq
              omega
            simp [__eo_to_z, __eo_is_neg, native_ite, native_zeq, native_str_len,
              hLenNe] at hNonneg
  | _ =>
      simp [__eo_to_z, __eo_is_neg] at hNonneg

private theorem native_includes_str_to_re_of_eval_side
    (M : SmtModel) (hM : model_total_typed M)
    (r : Term) (pat : native_String) (rv : native_RegLan)
    (hSTy :
      __smtx_typeof (__eo_to_smt (Term.String pat)) =
        SmtType.Seq SmtType.Char)
    (hRTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hREval : __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv)
    (hSide :
      __str_eval_str_in_re_rec
          (__str_flatten (__str_nary_intro (Term.String pat))) r =
        Term.Boolean true) :
    NativeIncludes rv (native_str_to_re pat) := by
  let side :=
    __str_eval_str_in_re_rec
      (__str_flatten (__str_nary_intro (Term.String pat))) r
  have hSideNe : side ≠ Term.Stuck := by
    dsimp [side]
    rw [hSide]
    decide
  have hEvalSide :=
    smtx_model_eval_str_in_re_eval_side M hM pat r side rv hSTy hRTy
      hREval rfl hSideNe
  have hPatMem : native_str_in_re pat rv = true := by
    dsimp [side] at hEvalSide
    rw [hSide] at hEvalSide
    simpa [__smtx_model_eval] using hEvalSide
  intro str hValid hMem
  have hEq : str = pat :=
    native_str_in_re_str_to_re_eq hValid hMem
  subst str
  exact hPatMem

private theorem native_includes_range_of_side
    (M : SmtModel) (hM : model_total_typed M)
    (s1 s2 s3 s4 : Term) (rvSup rvSub : native_RegLan)
    (hSupTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s1) s2)) =
        SmtType.RegLan)
    (hSubTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s4)) =
        SmtType.RegLan)
    (hSupEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s1) s2)) =
        SmtValue.RegLan rvSup)
    (hSubEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) s3) s4)) =
        SmtValue.RegLan rvSub)
    (hSide :
      (let _v0 := (__eo_to_z s1)
       let _v1 := (__eo_to_z s4)
       let _v2 := (__eo_to_z s2)
       let _v3 := (__eo_to_z s3)
       (__eo_requires (__eo_is_neg _v0) (Term.Boolean false)
        (__eo_requires (__eo_is_neg _v2) (Term.Boolean false)
        (__eo_requires (__eo_is_neg _v3) (Term.Boolean false)
        (__eo_requires (__eo_is_neg _v1) (Term.Boolean false)
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_ite (__eo_eq _v2 _v3) (Term.Boolean true)
                (__eo_gt _v2 _v3))
              (__eo_ite (__eo_eq _v3 _v0) (Term.Boolean true)
                (__eo_gt _v3 _v0)))
            (__eo_ite (__eo_eq _v2 _v1) (Term.Boolean true)
              (__eo_gt _v2 _v1)))
          (__eo_ite (__eo_eq _v1 _v0) (Term.Boolean true)
            (__eo_gt _v1 _v0)))))))) =
        Term.Boolean true) :
    NativeIncludes rvSup rvSub := by
  let v0 := __eo_to_z s1
  let v1 := __eo_to_z s4
  let v2 := __eo_to_z s2
  let v3 := __eo_to_z s3
  let core :=
    __eo_and
      (__eo_and
        (__eo_and
          (__eo_ite (__eo_eq v2 v3) (Term.Boolean true) (__eo_gt v2 v3))
          (__eo_ite (__eo_eq v3 v0) (Term.Boolean true) (__eo_gt v3 v0)))
        (__eo_ite (__eo_eq v2 v1) (Term.Boolean true) (__eo_gt v2 v1)))
      (__eo_ite (__eo_eq v1 v0) (Term.Boolean true) (__eo_gt v1 v0))
  have hSide' :
      __eo_requires (__eo_is_neg v0) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v2) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v3) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v1) (Term.Boolean false) core))) =
        Term.Boolean true := by
    simpa [v0, v1, v2, v3, core] using hSide
  rcases eo_requires_true_parts (__eo_is_neg v0) (Term.Boolean false)
      (__eo_requires (__eo_is_neg v2) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v3) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v1) (Term.Boolean false) core)))
      hSide' with ⟨hNeg0, hRest0⟩
  rcases eo_requires_true_parts (__eo_is_neg v2) (Term.Boolean false)
      (__eo_requires (__eo_is_neg v3) (Term.Boolean false)
        (__eo_requires (__eo_is_neg v1) (Term.Boolean false) core))
      hRest0 with ⟨hNeg2, hRest2⟩
  rcases eo_requires_true_parts (__eo_is_neg v3) (Term.Boolean false)
      (__eo_requires (__eo_is_neg v1) (Term.Boolean false) core)
      hRest2 with ⟨hNeg3, hRest3⟩
  rcases eo_requires_true_parts (__eo_is_neg v1) (Term.Boolean false) core
      hRest3 with ⟨hNeg1, hCore⟩
  have hSupArgs := re_range_arg_types_of_reglan s1 s2 hSupTy
  have hSubArgs := re_range_arg_types_of_reglan s3 s4 hSubTy
  rcases seq_char_term_to_z_singleton s1 hSupArgs.1 (by
      simpa [v0] using hNeg0) with
    ⟨loSup, rfl, hLoSupValid, hToLoSup⟩
  rcases seq_char_term_to_z_singleton s2 hSupArgs.2 (by
      simpa [v2] using hNeg2) with
    ⟨hiSup, rfl, hHiSupValid, hToHiSup⟩
  rcases seq_char_term_to_z_singleton s3 hSubArgs.1 (by
      simpa [v3] using hNeg3) with
    ⟨loSub, rfl, hLoSubValid, hToLoSub⟩
  rcases seq_char_term_to_z_singleton s4 hSubArgs.2 (by
      simpa [v1] using hNeg1) with
    ⟨hiSub, rfl, hHiSubValid, hToHiSub⟩
  dsimp [core, v0, v1, v2, v3] at hCore
  simp [__eo_to_z, native_ite, native_zeq, native_str_len,
    native_str_to_code, hLoSupValid, hHiSupValid, hLoSubValid,
    hHiSubValid] at hCore
  rcases eo_and_eq_true _ _ hCore with ⟨hLeft3, _hHiSubLoSup⟩
  rcases eo_and_eq_true _ _ hLeft3 with ⟨hLeft2, hHiSupHiSubTerm⟩
  rcases eo_and_eq_true _ _ hLeft2 with
    ⟨_hHiSupLoSub, hLoSubLoSupTerm⟩
  have hLoInt :
      (Int.ofNat loSup : native_Int) ≤ Int.ofNat loSub :=
    int_ge_of_eo_eq_or_gt_true (Int.ofNat loSub) (Int.ofNat loSup)
      hLoSubLoSupTerm
  have hHiInt :
      (Int.ofNat hiSub : native_Int) ≤ Int.ofNat hiSup :=
    int_ge_of_eo_eq_or_gt_true (Int.ofNat hiSup) (Int.ofNat hiSub)
      hHiSupHiSubTerm
  have hLo : loSup ≤ loSub := by
    exact Int.ofNat_le.mp hLoInt
  have hHi : hiSub ≤ hiSup := by
    exact Int.ofNat_le.mp hHiInt
  change __smtx_model_eval M
      (SmtTerm.re_range (SmtTerm.String [loSup]) (SmtTerm.String [hiSup])) =
    SmtValue.RegLan rvSup at hSupEval
  simp [__smtx_model_eval, __smtx_model_eval_re_range,
    native_unpack_string_pack_string] at hSupEval
  cases hSupEval
  change __smtx_model_eval M
      (SmtTerm.re_range (SmtTerm.String [loSub]) (SmtTerm.String [hiSub])) =
    SmtValue.RegLan rvSub at hSubEval
  simp [__smtx_model_eval, __smtx_model_eval_re_range,
    native_unpack_string_pack_string] at hSubEval
  cases hSubEval
  exact native_includes_range_singleton hLoSupValid hHiSupValid hLoSubValid
    hHiSubValid hLo hHi

private theorem re_unbound_base_prefix_closed
    (M : SmtModel) (hM : model_total_typed M)
    (tail : Term) (rv : native_RegLan)
    (hTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (Term.UOp UserOp.re_allchar))
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))))
              tail)) =
        SmtType.RegLan)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.Apply (Term.UOp UserOp.re_mult)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.re_concat)
                      (Term.UOp UserOp.re_allchar))
                    (Term.Apply (Term.UOp UserOp.str_to_re)
                      (Term.String [])))))
              tail)) =
        SmtValue.RegLan rv) :
    NativePrefixClosed rv := by
  let sigmaStar :=
    Term.Apply (Term.UOp UserOp.re_mult)
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.re_concat)
          (Term.UOp UserOp.re_allchar))
        (Term.Apply (Term.UOp UserOp.str_to_re) (Term.String [])))
  have hArgs := re_concat_arg_types_of_reglan sigmaStar tail (by
    simpa [sigmaStar] using hTy)
  rcases smt_model_eval_reglan_of_type M hM tail hArgs.2 with
    ⟨rtail, hTailEval⟩
  have hFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) sigmaStar)
              tail)) =
        SmtValue.RegLan (native_re_concat native_re_all rtail) :=
    eval_re_concat_reglan M sigmaStar tail native_re_all rtail
      (by simpa [sigmaStar] using smtx_model_eval_sigma_star_concat_eps M)
      hTailEval
  rw [show
      Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) sigmaStar) tail =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.re_concat)
            (Term.Apply (Term.UOp UserOp.re_mult)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.re_concat)
                  (Term.UOp UserOp.re_allchar))
                (Term.Apply (Term.UOp UserOp.str_to_re)
                  (Term.String [])))))
          tail by rfl] at hFullEval
  rw [hFullEval] at hEval
  cases hEval
  exact native_prefix_closed_all_concat rtail

private theorem re_unbound_allchar_prefix_closed
    (M : SmtModel) (hM : model_total_typed M)
    (tail : Term) (rv rtail : native_RegLan)
    (hTailEval :
      __smtx_model_eval M (__eo_to_smt tail) = SmtValue.RegLan rtail)
    (hEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              tail)) =
        SmtValue.RegLan rv)
    (hTailClosed : NativePrefixClosed rtail) :
    NativePrefixClosed rv := by
  have hAllcharEval :
      __smtx_model_eval M (__eo_to_smt (Term.UOp UserOp.re_allchar)) =
        SmtValue.RegLan native_re_allchar := by
    change __smtx_model_eval M SmtTerm.re_allchar =
      SmtValue.RegLan native_re_allchar
    rw [__smtx_model_eval.eq_103]
  have hFullEval :
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.re_concat)
                (Term.UOp UserOp.re_allchar))
              tail)) =
        SmtValue.RegLan (native_re_concat native_re_allchar rtail) :=
    eval_re_concat_reglan M (Term.UOp UserOp.re_allchar) tail
      native_re_allchar rtail hAllcharEval hTailEval
  rw [hFullEval] at hEval
  cases hEval
  exact native_prefix_closed_allchar_concat hTailClosed

private theorem re_is_unbound_wildcard_prefix_closed
    (M : SmtModel) (hM : model_total_typed M) :
    (t : Term) -> (rv : native_RegLan) ->
      __smtx_typeof (__eo_to_smt t) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan rv ->
      __re_is_unbound_wildcard t = Term.Boolean true ->
        NativePrefixClosed rv
  | t, rv, hTy, hEval, hWild => by
      cases t <;> try simp [__re_is_unbound_wildcard] at hWild
      case Apply f tail =>
        cases f <;> try simp [__re_is_unbound_wildcard] at hWild
        case Apply g left =>
          cases g <;> try simp [__re_is_unbound_wildcard] at hWild
          case UOp op =>
            cases op <;> try simp [__re_is_unbound_wildcard] at hWild
            case re_concat =>
              cases left <;> try simp [__re_is_unbound_wildcard] at hWild
              case UOp leftOp =>
                cases leftOp <;> try simp [__re_is_unbound_wildcard] at hWild
                case re_allchar =>
                  have hTailWild :
                      __re_is_unbound_wildcard tail = Term.Boolean true := by
                    simpa [__re_is_unbound_wildcard] using hWild
                  have hArgs :=
                    re_concat_arg_types_of_reglan
                      (Term.UOp UserOp.re_allchar) tail hTy
                  rcases smt_model_eval_reglan_of_type M hM tail hArgs.2 with
                    ⟨rtail, hTailEval⟩
                  exact
                    re_unbound_allchar_prefix_closed M hM tail rv rtail
                      hTailEval hEval
                      (re_is_unbound_wildcard_prefix_closed M hM tail rtail
                        hArgs.2 hTailEval hTailWild)
              case Apply lf lx =>
                cases lf <;> try simp [__re_is_unbound_wildcard] at hWild
                case UOp leftOp =>
                  cases leftOp <;> try simp [__re_is_unbound_wildcard] at hWild
                  case re_mult =>
                    cases lx <;> try simp [__re_is_unbound_wildcard] at hWild
                    case Apply sf sx =>
                      cases sf <;> try simp [__re_is_unbound_wildcard] at hWild
                      case Apply sg sy =>
                        cases sg <;> try simp [__re_is_unbound_wildcard] at hWild
                        case UOp sop =>
                          cases sop <;> try simp [__re_is_unbound_wildcard] at hWild
                          case re_concat =>
                            cases sy <;> try simp [__re_is_unbound_wildcard] at hWild
                            case UOp syop =>
                              cases syop <;> try simp [__re_is_unbound_wildcard] at hWild
                              case re_allchar =>
                                cases sx <;> try simp [__re_is_unbound_wildcard] at hWild
                                case Apply epsF epsX =>
                                  cases epsF <;> try simp [__re_is_unbound_wildcard] at hWild
                                  case UOp epsOp =>
                                    cases epsOp <;> try simp [__re_is_unbound_wildcard] at hWild
                                    case str_to_re =>
                                      cases epsX <;> try simp [__re_is_unbound_wildcard] at hWild
                                      case String xs =>
                                        cases xs <;> try simp [__re_is_unbound_wildcard] at hWild
                                        case nil =>
                                          exact re_unbound_base_prefix_closed M hM tail rv
                                            hTy hEval
termination_by t _ _ _ _ => sizeOf t

private theorem native_includes_concat_rhs_of_unbound
    (M : SmtModel) (hM : model_total_typed M)
    (lhs : Term) (rvLhs rvHead rvTail : native_RegLan)
    (hLhsTy : __smtx_typeof (__eo_to_smt lhs) = SmtType.RegLan)
    (hLhsEval :
      __smtx_model_eval M (__eo_to_smt lhs) = SmtValue.RegLan rvLhs)
    (hWild : __re_is_unbound_wildcard lhs = Term.Boolean true)
    (hTailIncl : NativeIncludes rvLhs rvTail) :
    NativeIncludes rvLhs (native_re_concat rvHead rvTail) := by
  exact native_includes_concat_left_of_prefix_closed
    (re_is_unbound_wildcard_prefix_closed M hM lhs rvLhs hLhsTy hLhsEval
      hWild)
    hTailIncl

theorem re_inclusion_side_native_includes
    (M : SmtModel) (hM : model_total_typed M)
    (sup sub flatSup flatSub side : Term)
    (rvSup rvSub : native_RegLan)
    (hSupTy : __smtx_typeof (__eo_to_smt sup) = SmtType.RegLan)
    (hSubTy : __smtx_typeof (__eo_to_smt sub) = SmtType.RegLan)
    (hSupEval : __smtx_model_eval M (__eo_to_smt sup) = SmtValue.RegLan rvSup)
    (hSubEval : __smtx_model_eval M (__eo_to_smt sub) = SmtValue.RegLan rvSub)
    (hFlatSup :
      flatSup = __re_flatten (Term.Boolean false) (Term.Boolean true) sup)
    (hFlatSub :
      flatSub = __re_flatten (Term.Boolean false) (Term.Boolean true) sub)
    (hSide :
      side =
        __eo_ite (__eo_eq flatSup flatSub) (Term.Boolean true)
          (__str_re_includes_rec flatSup flatSub))
    (hSideTrue : side = Term.Boolean true) :
    NativeIncludes rvSup rvSub := by
  sorry

end RuleProofs
