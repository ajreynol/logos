import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace RuleProofs

def nativeListInRe (xs : List Char) (r : native_RegLan) : native_Bool :=
  native_re_nullable <| xs.foldl (fun acc c => native_re_deriv c acc) r

theorem nativeListInRe_empty :
    (xs : List Char) -> nativeListInRe xs SmtRegLan.empty = false
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
    (xs : List Char) -> (r s : native_RegLan) ->
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
    (xs : List Char) -> (r s : native_RegLan) ->
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
    (xs : List Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat SmtRegLan.empty r) = false := by
  simp [native_re_mk_concat, nativeListInRe_empty]

theorem nativeListInRe_mk_concat_empty_right
    (xs : List Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.empty) = false := by
  cases r <;> simp [native_re_mk_concat, nativeListInRe_empty]

theorem nativeListInRe_mk_concat_epsilon_left
    (xs : List Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat SmtRegLan.epsilon r) =
      nativeListInRe xs r := by
  cases r <;> simp [native_re_mk_concat, nativeListInRe_empty]

theorem nativeListInRe_mk_concat_epsilon_right
    (xs : List Char) (r : native_RegLan) :
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
    (xs : List Char) (c : Char) (r s : native_RegLan) :
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
    List Char -> native_RegLan -> native_RegLan -> native_Bool
  | [], r, s => native_re_nullable r && native_re_nullable s
  | c :: cs, r, s =>
      (native_re_nullable r && nativeListInRe (c :: cs) s) ||
        nativeListInReConcat cs (native_re_deriv c r) s

theorem nativeListInRe_mk_concat :
    (xs : List Char) -> (r s : native_RegLan) ->
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

theorem nativeListInReConcat_true_iff_exists_append :
    (xs : List Char) -> (r s : native_RegLan) ->
      nativeListInReConcat xs r s = true ↔
        ∃ xs₁ xs₂ : List Char,
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

theorem nativeListInRe_mk_concat_true_iff_exists_append
    (xs : List Char) (r s : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat r s) = true ↔
      ∃ xs₁ xs₂ : List Char,
        xs₁ ++ xs₂ = xs ∧
          nativeListInRe xs₁ r = true ∧
          nativeListInRe xs₂ s = true := by
  rw [nativeListInRe_mk_concat xs r s]
  exact nativeListInReConcat_true_iff_exists_append xs r s

theorem native_str_in_re_mk_inter
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_mk_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  simpa [native_str_in_re, nativeListInRe] using
    nativeListInRe_mk_inter str.toList r s

theorem native_str_in_re_re_inter
    (str : native_String) (r s : native_RegLan) :
    native_str_in_re str (native_re_inter r s) =
      (native_str_in_re str r && native_str_in_re str s) := by
  simp [native_re_inter, native_str_in_re_mk_inter]

theorem native_str_in_re_re_concat_intro
    (s1 s2 : native_String) (r1 r2 : native_RegLan) :
    native_str_in_re s1 r1 = true ->
    native_str_in_re s2 r2 = true ->
    native_str_in_re (s1 ++ s2) (native_re_concat r1 r2) = true := by
  intro h1 h2
  have h := (nativeListInRe_mk_concat_true_iff_exists_append
    ((s1 ++ s2).toList) r1 r2).2
    ⟨s1.toList, s2.toList, by simp [String.toList_append],
      by simpa [native_str_in_re, nativeListInRe] using h1,
      by simpa [native_str_in_re, nativeListInRe] using h2⟩
  simpa [native_str_in_re, nativeListInRe, native_re_concat] using h

theorem nativeListInRe_mk_concat_congr
    (xs : List Char) (r r' s s' : native_RegLan)
    (hr : ∀ ys : List Char, nativeListInRe ys r = nativeListInRe ys r')
    (hs : ∀ ys : List Char, nativeListInRe ys s = nativeListInRe ys s') :
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
    (xs : List Char) (r s t : native_RegLan) :
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

theorem nativeListInRe_allchar_true_iff (xs : List Char) :
    nativeListInRe xs native_re_allchar = true ↔ xs.length = 1 := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_allchar, native_re_nullable]
  | cons c xs =>
      cases xs with
      | nil =>
          simp [nativeListInRe, native_re_allchar, native_re_deriv,
            native_re_nullable]
      | cons d ds =>
          simpa [nativeListInRe, native_re_allchar, native_re_deriv] using
            nativeListInRe_empty ds

private theorem native_re_deriv_re_all (c : Char) :
    native_re_deriv c native_re_all = native_re_all := by
  simp [native_re_all, native_re_deriv, native_re_mk_concat]

theorem nativeListInRe_re_all (xs : List Char) :
    nativeListInRe xs native_re_all = true := by
  induction xs with
  | nil =>
      simp [nativeListInRe, native_re_all, native_re_nullable]
  | cons c xs ih =>
      simpa [nativeListInRe, native_re_deriv_re_all] using ih

theorem native_str_in_re_re_all (str : native_String) :
    native_str_in_re str native_re_all = true := by
  simpa [native_str_in_re, nativeListInRe] using nativeListInRe_re_all str.toList

def nativeSigmaExact : Nat -> native_RegLan
  | 0 => SmtRegLan.epsilon
  | n + 1 => native_re_mk_concat (nativeSigmaExact n) native_re_allchar

def nativeSigmaAtLeast : Nat -> native_RegLan
  | 0 => native_re_all
  | n + 1 => native_re_mk_concat (nativeSigmaAtLeast n) native_re_allchar

theorem nativeListInRe_sigmaExact_true_iff :
    (n : Nat) -> (xs : List Char) ->
      nativeListInRe xs (nativeSigmaExact n) = true ↔ xs.length = n
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
        have hLeftLen : xs₁.length = n :=
          (nativeListInRe_sigmaExact_true_iff n xs₁).1 hLeft
        have hRightLen : xs₂.length = 1 :=
          (nativeListInRe_allchar_true_iff xs₂).1 hRight
        have hLen := congrArg List.length hAppend
        simp [hLeftLen, hRightLen] at hLen
        omega
      · intro hLen
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
        have hLeft :
            nativeListInRe xs₁ (nativeSigmaExact n) = true :=
          (nativeListInRe_sigmaExact_true_iff n xs₁).2 hLeftLen
        have hRight :
            nativeListInRe xs₂ native_re_allchar = true :=
          (nativeListInRe_allchar_true_iff xs₂).2 hRightLen
        have hConcat :
            nativeListInRe xs
                (native_re_mk_concat (nativeSigmaExact n) native_re_allchar) =
              true :=
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaExact n) native_re_allchar).2
            ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        simpa [nativeSigmaExact] using hConcat

theorem nativeListInRe_sigmaAtLeast_true_iff :
    (n : Nat) -> (xs : List Char) ->
      nativeListInRe xs (nativeSigmaAtLeast n) = true ↔ n ≤ xs.length
  | 0, xs => by
      constructor
      · intro _; omega
      · intro _; exact nativeListInRe_re_all xs
  | n + 1, xs => by
      constructor
      · intro h
        rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaAtLeast n) native_re_allchar).1
            (by simpa [nativeSigmaAtLeast] using h) with
          ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        have hLeftLen : n ≤ xs₁.length :=
          (nativeListInRe_sigmaAtLeast_true_iff n xs₁).1 hLeft
        have hRightLen : xs₂.length = 1 :=
          (nativeListInRe_allchar_true_iff xs₂).1 hRight
        have hLen := congrArg List.length hAppend
        simp [hRightLen] at hLen
        omega
      · intro hLen
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
        have hLeft :
            nativeListInRe xs₁ (nativeSigmaAtLeast n) = true :=
          (nativeListInRe_sigmaAtLeast_true_iff n xs₁).2 hLeftLen
        have hRight :
            nativeListInRe xs₂ native_re_allchar = true :=
          (nativeListInRe_allchar_true_iff xs₂).2 hRightLen
        have hConcat :
            nativeListInRe xs
                (native_re_mk_concat (nativeSigmaAtLeast n) native_re_allchar) =
              true :=
          (nativeListInRe_mk_concat_true_iff_exists_append xs
            (nativeSigmaAtLeast n) native_re_allchar).2
            ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
        simpa [nativeSigmaAtLeast] using hConcat

theorem nativeListInRe_exact_concat_re_all_true_iff
    (n : Nat) (xs : List Char) :
    nativeListInRe xs (native_re_mk_concat (nativeSigmaExact n) native_re_all) = true ↔
      n ≤ xs.length := by
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
        (nativeSigmaExact n) native_re_all).1 h with
      ⟨xs₁, xs₂, hAppend, hLeft, _hRight⟩
    have hLeftLen : xs₁.length = n :=
      (nativeListInRe_sigmaExact_true_iff n xs₁).1 hLeft
    have hLen := congrArg List.length hAppend
    simp [hLeftLen] at hLen
    omega
  · intro hLen
    let k := xs.length - n
    let xs₁ := xs.take n
    let xs₂ := xs.drop n
    have hLeftLen : xs₁.length = n := by
      simp [xs₁]
      omega
    have hAppend : xs₁ ++ xs₂ = xs := by
      simp [xs₁, xs₂]
    have hLeft : nativeListInRe xs₁ (nativeSigmaExact n) = true :=
      (nativeListInRe_sigmaExact_true_iff n xs₁).2 hLeftLen
    have hRight : nativeListInRe xs₂ native_re_all = true :=
      nativeListInRe_re_all xs₂
    exact (nativeListInRe_mk_concat_true_iff_exists_append xs
      (nativeSigmaExact n) native_re_all).2
      ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩

theorem nativeListInRe_exact_concat_re_all_eq_atLeast
    (n : Nat) (xs : List Char) :
    nativeListInRe xs (native_re_mk_concat (nativeSigmaExact n) native_re_all) =
      nativeListInRe xs (nativeSigmaAtLeast n) := by
  apply Bool.eq_iff_iff.mpr
  rw [nativeListInRe_exact_concat_re_all_true_iff,
    nativeListInRe_sigmaAtLeast_true_iff]

theorem nativeListInRe_atLeast_concat_re_all_eq_atLeast
    (n : Nat) (xs : List Char) :
    nativeListInRe xs (native_re_mk_concat (nativeSigmaAtLeast n) native_re_all) =
      nativeListInRe xs (nativeSigmaAtLeast n) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rcases (nativeListInRe_mk_concat_true_iff_exists_append xs
        (nativeSigmaAtLeast n) native_re_all).1 h with
      ⟨xs₁, xs₂, hAppend, hLeft, _hRight⟩
    have hLeftLen : n ≤ xs₁.length :=
      (nativeListInRe_sigmaAtLeast_true_iff n xs₁).1 hLeft
    apply (nativeListInRe_sigmaAtLeast_true_iff n xs).2
    have hLen := congrArg List.length hAppend
    simp at hLen
    omega
  · intro h
    have hNilAll : nativeListInRe [] native_re_all = true :=
      nativeListInRe_re_all []
    exact (nativeListInRe_mk_concat_true_iff_exists_append xs
      (nativeSigmaAtLeast n) native_re_all).2
      ⟨xs, [], by simp, h, hNilAll⟩

end RuleProofs
