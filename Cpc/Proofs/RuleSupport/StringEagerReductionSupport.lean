module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.RuleSupport.StringSupport
import all Cpc.Proofs.RuleSupport.StringSupport
public import Cpc.Proofs.RuleSupport.NativeSeqSupport
import all Cpc.Proofs.RuleSupport.NativeSeqSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem native_unpack_pack_string (s : native_String) :
    native_unpack_string (native_pack_string s) = s := by
  unfold native_unpack_string native_pack_string
  rw [_root_.native_unpack_pack_seq]
  induction s with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [native_ssm_char_of_value, ih]

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

private theorem nativeListInRe_mk_concat_empty_right
    (xs : List native_Char) (r : native_RegLan) :
    nativeListInRe xs (native_re_mk_concat r SmtRegLan.empty) = false := by
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
        simp [nativeListInRe_empty, Bool.or_comm]

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
                simp [nativeListInReConcat, hNullable, hRight]
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
      simp [native_str_in_re, native_re_deriv,
        native_re_nullable_fold_empty_false] at h

private theorem native_str_in_re_char_length
    {str : native_String} {c : native_Char}
    (h : native_str_in_re str (SmtRegLan.char c) = true) :
    str.length = 1 := by
  cases str with
  | nil =>
      simp [native_str_in_re, native_re_nullable] at h
  | cons d ds =>
      cases ds with
      | nil =>
          rfl
      | cons e es =>
          by_cases hMatch :
              (native_char_valid d = true ∧ native_char_valid c = true) ∧
                d = c
          · simp [native_str_in_re, native_re_deriv,
              native_re_nullable_fold_empty_false,
              hMatch] at h
          · simp [native_str_in_re, native_re_deriv,
              native_re_nullable_fold_empty_false,
              hMatch] at h

private theorem native_str_in_re_range_atom_length
    {str : native_String} {lo hi : native_Char}
    (h : native_str_in_re str (SmtRegLan.range lo hi) = true) :
    str.length = 1 := by
  cases str with
  | nil =>
      simp [native_str_in_re, native_re_nullable] at h
  | cons d ds =>
      cases ds with
      | nil =>
          rfl
      | cons e es =>
          by_cases hMatch :
              (((native_char_valid d = true ∧ native_char_valid lo = true) ∧
                    native_char_valid hi = true) ∧ lo ≤ d) ∧ d ≤ hi
          · simp [native_str_in_re, native_re_deriv,
              native_re_nullable_fold_empty_false,
              hMatch] at h
          · simp [native_str_in_re, native_re_deriv,
              native_re_nullable_fold_empty_false,
              hMatch] at h

private theorem native_str_in_re_allchar_length
    {str : native_String}
    (h : native_str_in_re str native_re_allchar = true) :
    str.length = 1 := by
  cases str with
  | nil =>
      simp [native_str_in_re, native_re_allchar,
        native_re_nullable] at h
  | cons d ds =>
      cases ds with
      | nil =>
          rfl
      | cons e es =>
          by_cases hValidD : native_char_valid d = true
          · simp [native_str_in_re, native_re_allchar,
              native_re_deriv, native_re_nullable_fold_empty_false, hValidD] at h
          · simp [native_str_in_re, native_re_allchar,
              native_re_deriv, native_re_nullable_fold_empty_false, hValidD] at h

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
        simp [__eo_requires, native_teq, native_ite, hEq]
    · right
      simp [__eo_requires, native_teq, native_ite]
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
      simp [native_ite]
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

theorem str_fixed_len_re_numeral_or_stuck :
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
          cases x <;> simp
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

theorem str_fixed_len_re_numeral_of_ne_stuck
    (r : Term)
    (h : __str_fixed_len_re r ≠ Term.Stuck) :
    ∃ n : native_Int, __str_fixed_len_re r = Term.Numeral n := by
  rcases str_fixed_len_re_numeral_or_stuck r with hNum | hStuck
  · exact hNum
  · exact False.elim (h hStuck)

theorem str_fixed_len_re_sound (M : SmtModel) :
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
        simp [hLen]
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
          cases x <;> simp  at hFixed
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
            simp [native_str_len, hLen]
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
              · simp [h0, h1, __eo_add] at hFixed
            · simp [h0, __eo_add] at hFixed
          case re_range =>
            cases hFixed
            rcases model_eval_re_range_reglan M (__eo_to_smt y)
                (__eo_to_smt x) hEval with
              ⟨_slo, _shi, _hLoEval, _hHiEval, rfl⟩
            have hLen := native_str_in_re_range_length hIn
            simp [hLen]
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
                  simp [__eo_eq, __eo_ite,
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
                    · simp [h0, h1, __eo_eq, __eo_ite,
                        __eo_requires, native_teq, native_ite, hNone', hLenEq] at hFixed
                  · simp [h0, h1, __eo_eq, __eo_ite,
                      __eo_requires, native_teq, native_ite, hNone'] at hFixed
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
                  simp [__eo_eq, __eo_ite,
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
                    · simp [h0, h1, __eo_eq, __eo_ite,
                        __eo_requires, native_teq, native_ite, hAll', hLenEq] at hFixed
                  · simp [h0, h1, __eo_eq, __eo_ite,
                      __eo_requires, native_teq, native_ite, hAll'] at hFixed
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
