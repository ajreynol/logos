module

public import Cpc.Proofs.RuleSupport.Support
import all Cpc.Proofs.RuleSupport.Support

public section

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

def nativeListInRe (xs : List native_Char) (r : native_RegLan) : native_Bool :=
  native_re_nullable <| xs.foldl (fun acc c => native_re_deriv c acc) r

theorem nativeListInRe_empty :
    (xs : List native_Char) -> nativeListInRe xs SmtRegLan.empty = false
  | [] => by rfl
  | _ :: xs => by
      exact nativeListInRe_empty xs

theorem native_re_nullable_mk_union (r s : native_RegLan) :
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

theorem nativeListInRe_mk_union :
    (xs : List native_Char) -> (r s : native_RegLan) ->
      nativeListInRe xs (native_re_mk_union r s) =
        (nativeListInRe xs r || nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_union]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_union, nativeListInRe_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_union, nativeListInRe_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_union_self]
            simp [nativeListInRe]
          · rw [native_re_mk_union_eq_union_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_union cs
              (native_re_deriv c r) (native_re_deriv c s)

theorem native_re_mk_inter_self (r : native_RegLan) :
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

theorem native_re_nullable_mk_inter (r s : native_RegLan) :
    native_re_nullable (native_re_mk_inter r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

theorem nativeListInRe_mk_inter :
    (xs : List native_Char) -> (r s : native_RegLan) ->
      nativeListInRe xs (native_re_mk_inter r s) =
        (nativeListInRe xs r && nativeListInRe xs s)
  | [], r, s => by
      simp [nativeListInRe, native_re_nullable_mk_inter]
  | c :: cs, r, s => by
      by_cases hr : r = SmtRegLan.empty
      · subst r
        simp [native_re_mk_inter, nativeListInRe_empty]
      · by_cases hs : s = SmtRegLan.empty
        · subst s
          simp [native_re_mk_inter, nativeListInRe_empty]
        · by_cases hEq : r = s
          · subst s
            rw [native_re_mk_inter_self]
            simp [nativeListInRe]
          · rw [native_re_mk_inter_eq_inter_of_ne r s hr hs hEq]
            simp [nativeListInRe, native_re_deriv]
            exact nativeListInRe_mk_inter cs
              (native_re_deriv c r) (native_re_deriv c s)

theorem native_re_nullable_mk_concat (r s : native_RegLan) :
    native_re_nullable (native_re_mk_concat r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_concat, native_re_nullable]

theorem nativeListInRe_mk_concat_empty_left
    (xs : List native_Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat SmtRegLan.empty r) = false := by
  simp [native_re_mk_concat, nativeListInRe_empty]

theorem nativeListInRe_mk_concat_empty_right
    (xs : List native_Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.empty) = false := by
  cases r <;> simp [native_re_mk_concat, nativeListInRe_empty]

theorem nativeListInRe_mk_concat_epsilon_left
    (xs : List native_Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat SmtRegLan.epsilon r) =
      nativeListInRe xs r := by
  cases r <;> simp [native_re_mk_concat, nativeListInRe_empty]

theorem nativeListInRe_mk_concat_epsilon_right
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

theorem nativeListInRe_deriv_mk_concat
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
  · by_cases hsEmpty : s = SmtRegLan.empty
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
    · by_cases hrEps : r = SmtRegLan.epsilon
      · subst r
        simp [native_re_mk_concat, native_re_deriv, native_re_nullable,
          nativeListInRe_mk_union, nativeListInRe_empty]
      · by_cases hsEps : s = SmtRegLan.epsilon
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

def nativeListInReConcat :
    List native_Char -> native_RegLan -> native_RegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && nativeListInRe (c :: cs) s) ||
        nativeListInReConcat cs (native_re_deriv c r) s

theorem nativeListInRe_mk_concat :
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
        simp [nativeListInRe_empty, Bool.or_comm]

theorem nativeListInReConcat_true_iff_exists_append :
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
                simp [nativeListInReConcat,
                  hNullable, hRight]
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
            simp [nativeListInReConcat, hTail]

theorem nativeListInRe_mk_concat_true_iff_exists_append
    (xs : List native_Char) (r s : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List native_Char,
        xs₁ ++ xs₂ = xs ∧
          nativeListInRe xs₁ r = true ∧
          nativeListInRe xs₂ s = true := by
  rw [nativeListInRe_mk_concat xs r s]
  exact nativeListInReConcat_true_iff_exists_append xs r s

theorem native_str_in_re_mk_inter
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_mk_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  by_cases hValid : native_string_valid str = true
  · simpa [native_str_in_re, hValid, nativeListInRe] using
      nativeListInRe_mk_inter str r s
  · have hInvalid : native_string_valid str = false := by
      cases h : native_string_valid str <;> simp [h] at hValid ⊢
    simp [native_str_in_re, hInvalid]

theorem native_str_in_re_re_inter
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  simp [native_re_inter, native_str_in_re_mk_inter]

theorem nativeListInRe_mk_comp :
    ∀ (xs : List native_Char) (r : native_RegLan),
      native_re_nullable
          (xs.foldl (fun acc c => native_re_deriv c acc)
            (native_re_mk_comp r)) =
        Bool.not
          (native_re_nullable
            (xs.foldl (fun acc c => native_re_deriv c acc) r))
  | [], r => by
      cases r <;> simp [native_re_mk_comp, native_re_nullable]
  | c :: cs, r => by
      have h := nativeListInRe_mk_comp cs (native_re_deriv c r)
      cases r <;> simp [native_re_mk_comp, native_re_deriv] at h ⊢
      case comp r =>
        have hComp := nativeListInRe_mk_comp cs (native_re_deriv c r)
        have hComp' :
            native_re_nullable
                (List.foldl (fun acc c => native_re_deriv c acc)
                  (match native_re_deriv c r with
                  | SmtRegLan.comp r => r
                  | r => SmtRegLan.comp r)
                  cs) =
              Bool.not
                (native_re_nullable
                    (List.foldl (fun acc c => native_re_deriv c acc)
                      (native_re_deriv c r) cs)) := by
          simpa [native_re_mk_comp] using hComp
        cases hA :
            native_re_nullable
              (List.foldl (fun acc c => native_re_deriv c acc)
                (native_re_deriv c r) cs) <;>
          cases hB :
            native_re_nullable
              (List.foldl (fun acc c => native_re_deriv c acc)
                (match native_re_deriv c r with
                | SmtRegLan.comp r => r
                | r => SmtRegLan.comp r)
                cs) <;>
          simp [hA, hB] at hComp' ⊢ <;> assumption
      all_goals exact h

theorem native_str_in_re_re_comp
    (str : native_String) (r : native_RegLan) :
    native_str_in_re str (native_re_comp r) =
      (native_string_valid str && Bool.not (native_str_in_re str r)) := by
  cases hValid : native_string_valid str <;>
    simp [native_str_in_re, native_re_comp, hValid,
      nativeListInRe_mk_comp]

theorem native_str_in_re_mk_comp
    (str : native_String) (r : native_RegLan) :
    native_str_in_re str (native_re_mk_comp r) =
      (native_string_valid str && Bool.not (native_str_in_re str r)) := by
  simpa [native_re_comp] using native_str_in_re_re_comp str r

theorem native_str_in_re_re_concat_intro
    (s1 s2 : native_String) (r1 r2 : native_RegLan) :
    native_str_in_re s1 r1 = true ->
    native_str_in_re s2 r2 = true ->
    native_str_in_re (s1 ++ s2) (native_re_concat r1 r2) = true := by
  intro h1 h2
  have h1Parts :
      native_string_valid s1 = true ∧ nativeListInRe s1 r1 = true := by
    simpa [native_str_in_re, nativeListInRe] using h1
  have h2Parts :
      native_string_valid s2 = true ∧ nativeListInRe s2 r2 = true := by
    simpa [native_str_in_re, nativeListInRe] using h2
  have hValidAppend : native_string_valid (s1 ++ s2) = true := by
    have hAll1 : s1.all native_char_valid = true := by
      simpa [native_string_valid] using h1Parts.1
    have hAll2 : s2.all native_char_valid = true := by
      simpa [native_string_valid] using h2Parts.1
    change (s1 ++ s2).all native_char_valid = true
    simp [hAll1, hAll2]
  have h := (nativeListInRe_mk_concat_true_iff_exists_append
    (s1 ++ s2) r1 r2).2
    ⟨s1, s2, by simp, h1Parts.2, h2Parts.2⟩
  simpa [native_str_in_re, hValidAppend, nativeListInRe, native_re_concat] using h

theorem nativeListInRe_mk_concat_congr
    (xs : List native_Char) (r r' s s' : native_RegLan)
    (hr : ∀ ys : List native_Char, nativeListInRe ys r = nativeListInRe ys r')
    (hs : ∀ ys : List native_Char, nativeListInRe ys s = nativeListInRe ys s') :
    nativeListInRe xs (native_re_mk_concat r s) =
      nativeListInRe xs (native_re_mk_concat r' s') := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs r s).1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r' s').2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [← hr xs₁]
    · rwa [← hs xs₂]
  · intro h
    rcases
      (nativeListInRe_mk_concat_true_iff_exists_append xs r' s').1 h
        with ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r s).2
    refine ⟨xs₁, xs₂, hAppend, ?_, ?_⟩
    · rwa [hr xs₁]
    · rwa [hs xs₂]

theorem nativeListInRe_mk_concat_assoc
    (xs : List native_Char) (r s t : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat (native_re_mk_concat r s) t) =
      nativeListInRe xs (native_re_mk_concat r (native_re_mk_concat s t)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
        (native_re_mk_concat r s) t).1 h with
      ⟨xrs, xt, hAppend, hrs, ht⟩
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xrs r s).1 hrs with
      ⟨xr, xs', hAppendRS, hr, hs⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs r
      (native_re_mk_concat s t)).2
    refine ⟨xr, xs' ++ xt, ?_, hr, ?_⟩
    · rw [← List.append_assoc, hAppendRS, hAppend]
    · exact (nativeListInRe_mk_concat_true_iff_exists_append (xs' ++ xt) s t).2
        ⟨xs', xt, rfl, hs, ht⟩
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs r
        (native_re_mk_concat s t)).1 h with
      ⟨xr, xst, hAppend, hr, hst⟩
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xst s t).1 hst with
      ⟨xs', xt, hAppendST, hs, ht⟩
    apply (nativeListInRe_mk_concat_true_iff_exists_append xs
      (native_re_mk_concat r s) t).2
    refine ⟨xr ++ xs', xt, ?_, ?_, ht⟩
    · rw [List.append_assoc, hAppendST, hAppend]
    · exact (nativeListInRe_mk_concat_true_iff_exists_append (xr ++ xs') r s).2
        ⟨xr, xs', rfl, hr, hs⟩

theorem nativeListInRe_allchar_true_iff (xs : List native_Char) :
    nativeListInRe xs native_re_allchar = true ↔
      xs.length = 1 ∧ xs.all native_char_valid = true := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_allchar, native_re_nullable]
  | cons c xs =>
      cases xs with
      | nil =>
          cases hValid : native_char_valid c <;>
            simp [nativeListInRe, native_re_allchar, native_re_deriv,
              native_re_nullable, hValid]
      | cons d ds =>
          have hEmpty := nativeListInRe_empty ds
          cases hValid : native_char_valid c <;>
            simpa [nativeListInRe, native_re_allchar, native_re_deriv,
              hValid] using hEmpty

private theorem native_re_deriv_re_all
    (c : native_Char) (hValid : native_char_valid c = true) :
    native_re_deriv c native_re_all = native_re_all := by
  simp [native_re_all, native_re_deriv, native_re_mk_concat, hValid]

private theorem native_re_deriv_re_all_invalid
    (c : native_Char) (hValid : native_char_valid c = false) :
    native_re_deriv c native_re_all = SmtRegLan.empty := by
  simp [native_re_all, native_re_deriv, native_re_mk_concat, hValid]

theorem nativeListInRe_re_all_true_iff (xs : List native_Char) :
    nativeListInRe xs native_re_all = true ↔
      xs.all native_char_valid = true := by
  induction xs with
  | nil =>
      simp [nativeListInRe, native_re_all, native_re_nullable]
  | cons c xs ih =>
      cases hValid : native_char_valid c
      · simpa [nativeListInRe, native_re_deriv_re_all_invalid c hValid,
          hValid] using nativeListInRe_empty xs
      · simpa [nativeListInRe, native_re_deriv_re_all c hValid, hValid,
          List.all_eq_true] using ih

theorem nativeListInRe_re_all
    (xs : List native_Char) (hValid : xs.all native_char_valid = true) :
    nativeListInRe xs native_re_all = true := by
  exact (nativeListInRe_re_all_true_iff xs).2 hValid

theorem native_str_in_re_re_all (str : native_String)
    (hValid : native_string_valid str = true) :
    native_str_in_re str native_re_all = true := by
  have hListValid : str.all native_char_valid = true := by
    simpa [native_string_valid] using hValid
  simpa [native_str_in_re, hValid, nativeListInRe] using
    nativeListInRe_re_all str hListValid

def nativeSigmaExact : Nat -> native_RegLan
  | 0 => SmtRegLan.epsilon
  | n + 1 => native_re_mk_concat (nativeSigmaExact n) native_re_allchar

def nativeSigmaAtLeast : Nat -> native_RegLan
  | 0 => native_re_all
  | n + 1 => native_re_mk_concat (nativeSigmaAtLeast n) native_re_allchar

theorem nativeListInRe_sigmaExact_true_iff :
    (n : Nat) -> (xs : List native_Char) ->
      nativeListInRe xs (nativeSigmaExact n) = true ↔
        xs.length = n ∧ xs.all native_char_valid = true
  | 0, xs => by
      cases xs with
      | nil =>
          simp [nativeSigmaExact, nativeListInRe, native_re_nullable]
      | cons c cs =>
          simpa [nativeSigmaExact, nativeListInRe, native_re_nullable,
            native_re_deriv] using nativeListInRe_empty cs
  | n + 1, xs => by
      constructor
      · intro h
        rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaExact n) native_re_allchar).1
            (by simpa [nativeSigmaExact] using h) with
          ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        have hLeftParts :
            xs₁.length = n ∧ xs₁.all native_char_valid = true :=
          (nativeListInRe_sigmaExact_true_iff n xs₁).1 hLeft
        have hRightParts :
            xs₂.length = 1 ∧ xs₂.all native_char_valid = true :=
          (nativeListInRe_allchar_true_iff xs₂).1 hRight
        have hLen := congrArg List.length hAppend
        simp [hLeftParts.1, hRightParts.1] at hLen
        have hValid : xs.all native_char_valid = true := by
          rw [← hAppend, List.all_append]
          simp [hLeftParts.2, hRightParts.2]
        exact ⟨by omega, hValid⟩
      · intro hParts
        rcases hParts with ⟨hLen, hValid⟩
        let xs₁ := xs.take n
        let xs₂ := xs.drop n
        have hLeftLen : xs₁.length = n := by
          simp [xs₁]
          omega
        have hRightLen : xs₂.length = 1 := by
          simp [xs₂]
          omega
        have hAppend : xs₁ ++ xs₂ = xs := by
          simp [xs₁, xs₂]
        have hValidAppend : (xs₁ ++ xs₂).all native_char_valid = true := by
          simpa [hAppend] using hValid
        rw [List.all_append] at hValidAppend
        have hValidParts :
            xs₁.all native_char_valid = true ∧
              xs₂.all native_char_valid = true := by
          simpa [Bool.and_eq_true] using hValidAppend
        have hLeftValid : xs₁.all native_char_valid = true :=
          hValidParts.1
        have hRightValid : xs₂.all native_char_valid = true :=
          hValidParts.2
        have hLeft :
            nativeListInRe xs₁ (nativeSigmaExact n) = true :=
          (nativeListInRe_sigmaExact_true_iff n xs₁).2
            ⟨hLeftLen, hLeftValid⟩
        have hRight :
            nativeListInRe xs₂ native_re_allchar = true :=
          (nativeListInRe_allchar_true_iff xs₂).2
            ⟨hRightLen, hRightValid⟩
        have hConcat :
            nativeListInRe xs
                (native_re_mk_concat (nativeSigmaExact n) native_re_allchar) =
              true :=
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaExact n) native_re_allchar).2
            ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        simpa [nativeSigmaExact] using hConcat

theorem nativeListInRe_sigmaAtLeast_true_iff :
    (n : Nat) -> (xs : List native_Char) ->
      nativeListInRe xs (nativeSigmaAtLeast n) = true ↔
        n ≤ xs.length ∧ xs.all native_char_valid = true
  | 0, xs => by
      constructor
      · intro h
        exact ⟨by omega, (nativeListInRe_re_all_true_iff xs).1 h⟩
      · intro hParts
        exact nativeListInRe_re_all xs hParts.2
  | n + 1, xs => by
      constructor
      · intro h
        rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaAtLeast n) native_re_allchar).1
            (by simpa [nativeSigmaAtLeast] using h) with
          ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        have hLeftParts :
            n ≤ xs₁.length ∧ xs₁.all native_char_valid = true :=
          (nativeListInRe_sigmaAtLeast_true_iff n xs₁).1 hLeft
        have hRightParts :
            xs₂.length = 1 ∧ xs₂.all native_char_valid = true :=
          (nativeListInRe_allchar_true_iff xs₂).1 hRight
        have hLen := congrArg List.length hAppend
        simp [hRightParts.1] at hLen
        have hValid : xs.all native_char_valid = true := by
          rw [← hAppend, List.all_append]
          simp [hLeftParts.2, hRightParts.2]
        exact ⟨by omega, hValid⟩
      · intro hParts
        rcases hParts with ⟨hLen, hValid⟩
        let cut := xs.length - 1
        let xs₁ := xs.take cut
        let xs₂ := xs.drop cut
        have hLeftLen : n ≤ xs₁.length := by
          simp [xs₁, cut]
          omega
        have hRightLen : xs₂.length = 1 := by
          simp [xs₂, cut]
          omega
        have hAppend : xs₁ ++ xs₂ = xs := by
          simp [xs₁, xs₂]
        have hValidAppend : (xs₁ ++ xs₂).all native_char_valid = true := by
          simpa [hAppend] using hValid
        rw [List.all_append] at hValidAppend
        have hValidParts :
            xs₁.all native_char_valid = true ∧
              xs₂.all native_char_valid = true := by
          simpa [Bool.and_eq_true] using hValidAppend
        have hLeftValid : xs₁.all native_char_valid = true :=
          hValidParts.1
        have hRightValid : xs₂.all native_char_valid = true :=
          hValidParts.2
        have hLeft :
            nativeListInRe xs₁ (nativeSigmaAtLeast n) = true :=
          (nativeListInRe_sigmaAtLeast_true_iff n xs₁).2
            ⟨hLeftLen, hLeftValid⟩
        have hRight :
            nativeListInRe xs₂ native_re_allchar = true :=
          (nativeListInRe_allchar_true_iff xs₂).2
            ⟨hRightLen, hRightValid⟩
        have hConcat :
            nativeListInRe xs
                (native_re_mk_concat (nativeSigmaAtLeast n) native_re_allchar) =
              true :=
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaAtLeast n) native_re_allchar).2
            ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        simpa [nativeSigmaAtLeast] using hConcat

theorem nativeListInRe_exact_concat_re_all_true_iff
    (n : Nat) (xs : List native_Char) :
    nativeListInRe xs (native_re_mk_concat (nativeSigmaExact n) native_re_all) = true ↔
      n ≤ xs.length ∧ xs.all native_char_valid = true := by
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
        (nativeSigmaExact n) native_re_all).1 h with
      ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    have hLeftParts :
        xs₁.length = n ∧ xs₁.all native_char_valid = true :=
      (nativeListInRe_sigmaExact_true_iff n xs₁).1 hLeft
    have hRightValid : xs₂.all native_char_valid = true :=
      (nativeListInRe_re_all_true_iff xs₂).1 hRight
    have hLen := congrArg List.length hAppend
    simp [hLeftParts.1] at hLen
    have hValid : xs.all native_char_valid = true := by
      rw [← hAppend, List.all_append]
      simp [hLeftParts.2, hRightValid]
    exact ⟨by omega, hValid⟩
  · intro hParts
    rcases hParts with ⟨hLen, hValid⟩
    let k := xs.length - n
    let xs₁ := xs.take n
    let xs₂ := xs.drop n
    have hLeftLen : xs₁.length = n := by
      simp [xs₁]
      omega
    have hAppend : xs₁ ++ xs₂ = xs := by
      simp [xs₁, xs₂]
    have hValidAppend : (xs₁ ++ xs₂).all native_char_valid = true := by
      simpa [hAppend] using hValid
    rw [List.all_append] at hValidAppend
    have hValidParts :
        xs₁.all native_char_valid = true ∧
          xs₂.all native_char_valid = true := by
      simpa [Bool.and_eq_true] using hValidAppend
    have hLeftValid : xs₁.all native_char_valid = true :=
      hValidParts.1
    have hRightValid : xs₂.all native_char_valid = true :=
      hValidParts.2
    have hLeft : nativeListInRe xs₁ (nativeSigmaExact n) = true :=
      (nativeListInRe_sigmaExact_true_iff n xs₁).2
        ⟨hLeftLen, hLeftValid⟩
    have hRight : nativeListInRe xs₂ native_re_all = true :=
      nativeListInRe_re_all xs₂ hRightValid
    exact (nativeListInRe_mk_concat_true_iff_exists_append xs
      (nativeSigmaExact n) native_re_all).2
      ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩

theorem nativeListInRe_exact_concat_re_all_eq_atLeast
    (n : Nat) (xs : List native_Char) :
    nativeListInRe xs (native_re_mk_concat (nativeSigmaExact n) native_re_all) =
      nativeListInRe xs (nativeSigmaAtLeast n) := by
  apply Bool.eq_iff_iff.mpr
  rw [nativeListInRe_exact_concat_re_all_true_iff,
    nativeListInRe_sigmaAtLeast_true_iff]

theorem nativeListInRe_atLeast_concat_re_all_eq_atLeast
    (n : Nat) (xs : List native_Char) :
    nativeListInRe xs (native_re_mk_concat (nativeSigmaAtLeast n) native_re_all) =
      nativeListInRe xs (nativeSigmaAtLeast n) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
        (nativeSigmaAtLeast n) native_re_all).1 h with
      ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
    have hLeftParts :
        n ≤ xs₁.length ∧ xs₁.all native_char_valid = true :=
      (nativeListInRe_sigmaAtLeast_true_iff n xs₁).1 hLeft
    have hRightValid : xs₂.all native_char_valid = true :=
      (nativeListInRe_re_all_true_iff xs₂).1 hRight
    apply (nativeListInRe_sigmaAtLeast_true_iff n xs).2
    have hLen := congrArg List.length hAppend
    simp at hLen
    have hValid : xs.all native_char_valid = true := by
      rw [← hAppend, List.all_append]
      simp [hLeftParts.2, hRightValid]
    exact ⟨by omega, hValid⟩
  · intro h
    have hNilAll : nativeListInRe [] native_re_all = true :=
      nativeListInRe_re_all [] (by simp)
    exact (nativeListInRe_mk_concat_true_iff_exists_append xs
      (nativeSigmaAtLeast n) native_re_all).2
      ⟨xs, [], by simp, h, hNilAll⟩

end RuleProofs
