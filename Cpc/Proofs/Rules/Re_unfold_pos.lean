import Cpc.Proofs.RuleSupport.ReUnfoldNegSupport
import Cpc.Proofs.RuleSupport.StringSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace RuleProofs
namespace ReUnfoldPosSupport

open ReUnfoldNegSupport

private abbrev mkAnd := ReUnfoldNegSupport.mkAnd
private abbrev mkOr := ReUnfoldNegSupport.mkOr
private abbrev mkEq := ReUnfoldNegSupport.mkEq
private abbrev mkNeg := ReUnfoldNegSupport.mkNeg
private abbrev mkStrLen := ReUnfoldNegSupport.mkStrLen
private abbrev mkSubstr := ReUnfoldNegSupport.mkSubstr
private abbrev mkStrInRe := ReUnfoldNegSupport.mkStrInRe
private abbrev mkReMult := ReUnfoldNegSupport.mkReMult
private abbrev mkReConcat := ReUnfoldNegSupport.mkReConcat

private abbrev mkStrConcat (s t : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s) t

private abbrev mkReDiff (r s : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) r) s

private abbrev mkStrToRe (s : Term) : Term :=
  Term.Apply (Term.UOp UserOp.str_to_re) s

private abbrev mkAtReUnfoldPosComponent (t r i : Term) : Term :=
  Term.UOp3 UserOp3._at_re_unfold_pos_component t r i

private abbrev idxTerm (i : Nat) : Term :=
  Term.Numeral (Int.ofNat i)

abbrev reUnfoldPosStarFactor (r : Term) : Term :=
  mkReConcat (mkReDiff r (mkStrToRe (Term.String [])))
    (mkReConcat (mkReMult r)
      (mkReConcat (mkReDiff r (mkStrToRe (Term.String [])))
        (mkStrToRe (Term.String []))))

private abbrev reUnfoldPosStarComponent (t r : Term) (i : Nat) : Term :=
  mkAtReUnfoldPosComponent t (reUnfoldPosStarFactor r) (idxTerm i)

abbrev reUnfoldPosStarFirst (t r : Term) : Term :=
  mkStrConcat (reUnfoldPosStarComponent t r 0)
    (mkStrConcat (reUnfoldPosStarComponent t r 1)
      (mkStrConcat (reUnfoldPosStarComponent t r 2) (Term.String [])))

abbrev reUnfoldPosStarGuard (t r : Term) : Term :=
  mkAnd
    (mkStrInRe (reUnfoldPosStarComponent t r 0)
      (mkReDiff r (mkStrToRe (Term.String []))))
    (mkAnd
      (mkStrInRe (reUnfoldPosStarComponent t r 1) (mkReMult r))
      (mkAnd
        (mkStrInRe (reUnfoldPosStarComponent t r 2)
          (mkReDiff r (mkStrToRe (Term.String []))))
        (Term.Boolean true)))

abbrev reUnfoldPosStarFormula (t r : Term) : Term :=
  mkOr (mkEq t (Term.String []))
    (mkOr (mkStrInRe t r)
      (mkOr
        (mkAnd (mkEq t (reUnfoldPosStarFirst t r))
          (reUnfoldPosStarGuard t r))
        (Term.Boolean false)))

theorem re_unfold_pos_initial_component (t r : Term) :
    ∀ j : Nat,
      __eo_to_smt (mkAtReUnfoldPosComponent t r (idxTerm (0 + j))) =
        __eo_to_smt_re_unfold_pos_component (__eo_to_smt t) (__eo_to_smt r) j := by
  intro j
  change native_ite (__eo_to_smt_nat_is_valid (idxTerm (0 + j)))
      (__eo_to_smt_re_unfold_pos_component (__eo_to_smt t) (__eo_to_smt r)
        (__eo_to_smt_nat (idxTerm (0 + j))))
      SmtTerm.None =
    __eo_to_smt_re_unfold_pos_component (__eo_to_smt t) (__eo_to_smt r) j
  have hValid : native_zleq 0 (Int.ofNat j) = true := by
    simp [native_zleq, SmtEval.native_zleq]
  have hNat : native_int_to_nat (Int.ofNat j) = j := by
    simp [native_int_to_nat, SmtEval.native_int_to_nat]
  unfold native_ite
  simp only [idxTerm, __eo_to_smt_nat_is_valid, __eo_to_smt_nat, Nat.zero_add]
  rw [hValid, hNat]
  simp

private theorem native_unpack_seq_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, native_unpack_seq,
        native_unpack_seq_pack_seq T xs]

private theorem elem_typeof_native_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue,
      __smtx_elem_typeof_seq_value (native_pack_seq T xs) = T
  | [] => rfl
  | _ :: xs => by
      simp [native_pack_seq, __smtx_elem_typeof_seq_value,
        elem_typeof_native_pack_seq T xs]

private theorem native_unpack_string_pack_concat
    (T : SmtType) (ss1 ss2 : SmtSeq) :
    native_unpack_string
        (native_pack_seq T
          (native_seq_concat (native_unpack_seq ss1) (native_unpack_seq ss2))) =
      native_unpack_string ss1 ++ native_unpack_string ss2 := by
  simp [native_unpack_string, native_seq_concat,
    native_unpack_seq_pack_seq, List.map_append]

private theorem native_string_valid_append_left
    (xs ys : native_String) :
    native_string_valid (xs ++ ys) = true ->
      native_string_valid xs = true := by
  intro h
  have h' :
      xs.all native_char_valid && ys.all native_char_valid = true := by
    simpa [native_string_valid, List.all_append] using h
  have hParts :
      xs.all native_char_valid = true ∧ ys.all native_char_valid = true := by
    simpa [Bool.and_eq_true] using h'
  exact hParts.1

private theorem native_string_valid_append_right
    (xs ys : native_String) :
    native_string_valid (xs ++ ys) = true ->
      native_string_valid ys = true := by
  intro h
  have h' :
      xs.all native_char_valid && ys.all native_char_valid = true := by
    simpa [native_string_valid, List.all_append] using h
  have hParts :
      xs.all native_char_valid = true ∧ ys.all native_char_valid = true := by
    simpa [Bool.and_eq_true] using h'
  exact hParts.2

private theorem nativeListInRe_mk_comp_list :
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
      have h := nativeListInRe_mk_comp_list cs (native_re_deriv c r)
      cases r <;> simp [native_re_mk_comp, native_re_deriv] at h ⊢
      case comp r =>
        have hComp := nativeListInRe_mk_comp_list cs (native_re_deriv c r)
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

private theorem native_str_in_re_re_comp
    (s : native_String) (r : native_RegLan) :
    native_str_in_re s (native_re_comp r) =
      (native_string_valid s && Bool.not (native_str_in_re s r)) := by
  cases hValid : native_string_valid s <;>
    simp [native_str_in_re, native_re_comp, hValid,
      nativeListInRe_mk_comp_list]

private theorem native_str_in_re_re_diff
    (s : native_String) (r₁ r₂ : native_RegLan) :
    native_str_in_re s (native_re_diff r₁ r₂) =
      (native_str_in_re s r₁ && Bool.not (native_str_in_re s r₂)) := by
  rw [native_re_diff, RuleProofs.native_str_in_re_mk_inter,
    (by
      simpa [native_re_comp] using native_str_in_re_re_comp s r₂ :
        native_str_in_re s (native_re_mk_comp r₂) =
          (native_string_valid s && Bool.not (native_str_in_re s r₂)))]
  cases hValid : native_string_valid s <;>
    simp [native_str_in_re, hValid]

private theorem nativeListInRe_char_true_eq_singleton
    {xs : List native_Char} {c : native_Char} :
    nativeListInRe xs (SmtRegLan.char c) = true ->
      xs = [c] := by
  cases xs with
  | nil =>
      simp [nativeListInRe, native_re_nullable]
  | cons d ds =>
      cases hcond : (native_char_valid d && native_char_valid c && d = c)
      · intro h
        have hEq : nativeListInRe ds SmtRegLan.empty = true := by
          simpa [nativeListInRe, native_re_deriv, hcond] using h
        have hFalse : false = true :=
          (RuleProofs.nativeListInRe_empty ds).symm.trans hEq
        cases hFalse
      · have hdc : d = c := by
          simp [Bool.and_eq_true] at hcond
          exact hcond.2
        subst d
        cases ds with
        | nil =>
            intro _h
            rfl
        | cons e es =>
            intro h
            have hValidC : native_char_valid c = true := by
              simpa [Bool.and_eq_true] using hcond
            have hEq : nativeListInRe es SmtRegLan.empty = true := by
              simpa [nativeListInRe, native_re_deriv, hValidC] using h
            have hFalse : false = true :=
              (RuleProofs.nativeListInRe_empty es).symm.trans hEq
            cases hFalse

private theorem nativeListInRe_str_to_re_true_eq :
    ∀ {xs pat : native_String},
      nativeListInRe xs (native_str_to_re pat) = true -> xs = pat
  | xs, [], h => by
      cases xs with
      | nil => rfl
      | cons c cs =>
          have hEq : nativeListInRe cs SmtRegLan.empty = true := by
            simpa [native_str_to_re, native_re_of_list, nativeListInRe,
              native_re_deriv] using h
          have hFalse : false = true :=
            (RuleProofs.nativeListInRe_empty cs).symm.trans hEq
          cases hFalse
  | xs, c :: cs, h => by
      have hConcat :
          nativeListInRe xs
              (native_re_mk_concat (SmtRegLan.char c)
                (native_re_of_list cs)) = true := by
        simpa [native_str_to_re, native_re_of_list] using h
      rcases
          (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append xs
            (SmtRegLan.char c) (native_re_of_list cs)).1 hConcat with
        ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
      have hLeftEq : xs₁ = [c] :=
        nativeListInRe_char_true_eq_singleton hLeft
      have hRightEq : xs₂ = cs := by
        exact nativeListInRe_str_to_re_true_eq (by
          simpa [native_str_to_re] using hRight)
      subst xs₁
      subst xs₂
      simp at hAppend
      simpa [hAppend]

private theorem native_str_in_re_str_to_re_true_eq
    {xs pat : native_String} :
    native_str_in_re xs (native_str_to_re pat) = true -> xs = pat := by
  intro h
  have hParts :
      native_string_valid xs = true ∧
        nativeListInRe xs (native_str_to_re pat) = true := by
    simpa [native_str_in_re, nativeListInRe] using h
  exact nativeListInRe_str_to_re_true_eq hParts.2

private theorem native_str_in_re_re_mult_empty (r : native_RegLan) :
    native_str_in_re [] (native_re_mult r) = true := by
  cases r <;> simp [native_str_in_re, native_string_valid, native_re_mult,
    native_re_mk_star, native_re_nullable]

private theorem nativeListInRe_star_append_intro (r : native_RegLan) :
    (xs ys : List native_Char) ->
      nativeListInRe xs r = true ->
      nativeListInRe ys (SmtRegLan.star r) = true ->
      nativeListInRe (xs ++ ys) (SmtRegLan.star r) = true
  | [], ys, rMem, ysStar => by
      simpa using ysStar
  | c :: cs, ys, rMem, ysStar => by
      change
        nativeListInRe (cs ++ ys)
            (native_re_mk_concat (native_re_deriv c r) (SmtRegLan.star r)) =
          true
      exact
        (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          (cs ++ ys) (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨cs, ys, rfl, by simpa [nativeListInRe] using rMem, ysStar⟩

private theorem nativeListInRe_star_append_closed :
    (xs ys : List native_Char) -> (r : native_RegLan) ->
      nativeListInRe xs (SmtRegLan.star r) = true ->
      nativeListInRe ys (SmtRegLan.star r) = true ->
      nativeListInRe (xs ++ ys) (SmtRegLan.star r) = true
  | [], ys, r, _hLeft, hRight => by
      simpa using hRight
  | c :: cs, ys, r, hLeft, hRight => by
      have hConcat :
          nativeListInRe cs
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true := by
        simpa [nativeListInRe, native_re_deriv] using hLeft
      rcases
          (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append cs
            (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
        ⟨xs₁, xs₂, hAppend, hLeftPart, hTail⟩
      have hLen : xs₂.length < (c :: cs).length := by
        have hLenEq := congrArg List.length hAppend
        simp at hLenEq ⊢
        omega
      have hTailAppend :
          nativeListInRe (xs₂ ++ ys) (SmtRegLan.star r) = true :=
        nativeListInRe_star_append_closed xs₂ ys r hTail hRight
      have hAppend' : xs₁ ++ (xs₂ ++ ys) = cs ++ ys := by
        rw [← List.append_assoc, hAppend]
      have hConcat' :
          nativeListInRe (cs ++ ys)
              (native_re_mk_concat (native_re_deriv c r)
                (SmtRegLan.star r)) = true :=
        (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          (cs ++ ys) (native_re_deriv c r) (SmtRegLan.star r)).2
          ⟨xs₁, xs₂ ++ ys, hAppend', hLeftPart, hTailAppend⟩
      simpa [nativeListInRe, native_re_deriv] using hConcat'
termination_by xs _ _ _ _ => xs.length
decreasing_by
  all_goals
    omega

private theorem nativeListInRe_raw_star_cons_decomp
    {c : native_Char} {cs : List native_Char} {r : native_RegLan} :
    nativeListInRe (c :: cs) (SmtRegLan.star r) = true ->
      ∃ xs₁ xs₂,
        xs₁ ++ xs₂ = cs ∧
        nativeListInRe (c :: xs₁) r = true ∧
        nativeListInRe xs₂ (SmtRegLan.star r) = true := by
  intro h
  have hConcat :
      nativeListInRe cs
          (native_re_mk_concat (native_re_deriv c r) (SmtRegLan.star r)) =
        true := by
    simpa [nativeListInRe, native_re_deriv] using h
  rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append cs
        (native_re_deriv c r) (SmtRegLan.star r)).1 hConcat with
    ⟨xs₁, xs₂, hAppend, hLeft, hRight⟩
  exact ⟨xs₁, xs₂, hAppend, by simpa [nativeListInRe] using hLeft, hRight⟩

private theorem nativeListInRe_raw_star_middle_last :
    (xs : List native_Char) -> (r : native_RegLan) ->
      nativeListInRe xs (SmtRegLan.star r) = true ->
      xs ≠ [] ->
      nativeListInRe xs r ≠ true ->
      ∃ first middle last : native_String,
        xs = first ++ middle ++ last ∧
        first ≠ [] ∧
        last ≠ [] ∧
        nativeListInRe first r = true ∧
        nativeListInRe middle (SmtRegLan.star r) = true ∧
        nativeListInRe last r = true
  | [], r, _hStar, hNe, _hNot => by
      exact False.elim (hNe rfl)
  | c :: cs, r, hStar, _hNe, hNot => by
      rcases nativeListInRe_raw_star_cons_decomp hStar with
        ⟨headTail, rest, hAppend, hHead, hRestStar⟩
      let first : native_String := c :: headTail
      have hFirstNe : first ≠ [] := by simp [first]
      by_cases hRestEmpty : rest = []
      · subst rest
        have hWholeInR : nativeListInRe (c :: cs) r = true := by
          have hCs : headTail = cs := by
            simpa using hAppend
          subst headTail
          simpa [first] using hHead
        exact False.elim (hNot hWholeInR)
      · by_cases hRestInR : nativeListInRe rest r = true
        · refine ⟨first, [], rest, ?_, hFirstNe, hRestEmpty, hHead, ?_, hRestInR⟩
          · simp [first, hAppend]
          · simp [nativeListInRe, native_re_nullable]
        · have hRestLen : rest.length < (c :: cs).length := by
            have hLenEq := congrArg List.length hAppend
            simp at hLenEq ⊢
            omega
          rcases
            nativeListInRe_raw_star_middle_last rest r hRestStar hRestEmpty
              hRestInR with
            ⟨restFirst, restMiddle, restLast, hRestEq, hRestFirstNe,
              hRestLastNe, hRestFirst, hRestMiddle, hRestLast⟩
          have hMiddleStar :
              nativeListInRe (restFirst ++ restMiddle)
                (SmtRegLan.star r) = true := by
            exact nativeListInRe_star_append_intro r restFirst restMiddle
              hRestFirst hRestMiddle
          refine ⟨first, restFirst ++ restMiddle, restLast, ?_,
            hFirstNe, hRestLastNe, hHead, hMiddleStar, hRestLast⟩
          calc
            c :: cs = first ++ rest := by
              simp [first, hAppend]
            _ = first ++ (restFirst ++ restMiddle ++ restLast) := by
              rw [hRestEq]
            _ = first ++ (restFirst ++ restMiddle) ++ restLast := by
              simp [List.append_assoc]
termination_by xs _ _ _ _ => xs.length
decreasing_by
  all_goals
    simp_all

private theorem native_str_in_re_re_mult_append_intro
    (s1 s2 : native_String) (r : native_RegLan) :
    native_str_in_re s1 r = true ->
    native_str_in_re s2 (native_re_mult r) = true ->
    native_str_in_re (s1 ++ s2) (native_re_mult r) = true := by
  intro h1 h2
  have h1Parts :
      native_string_valid s1 = true ∧ nativeListInRe s1 r = true := by
    simpa [native_str_in_re, nativeListInRe] using h1
  have h2Parts :
      native_string_valid s2 = true ∧
        nativeListInRe s2 (native_re_mult r) = true := by
    simpa [native_str_in_re, nativeListInRe] using h2
  have hValidAppend : native_string_valid (s1 ++ s2) = true := by
    have hAll1 : s1.all native_char_valid = true := by
      simpa [native_string_valid] using h1Parts.1
    have hAll2 : s2.all native_char_valid = true := by
      simpa [native_string_valid] using h2Parts.1
    change (s1 ++ s2).all native_char_valid = true
    simp [hAll1, hAll2]
  have hList :
      nativeListInRe (s1 ++ s2) (native_re_mult r) = true := by
    cases r with
    | empty =>
        have hBad : False := by
          have hEmpty := RuleProofs.nativeListInRe_empty s1
          have hEq : false = true := by
            simpa [hEmpty] using h1Parts.2
          cases hEq
        exact False.elim hBad
    | epsilon =>
        cases s1 with
        | nil =>
            simpa [native_re_mult, native_re_mk_star] using h2Parts.2
        | cons c cs =>
            have hBad : False := by
              have hCsEmpty : nativeListInRe cs SmtRegLan.empty = true := by
                simpa [nativeListInRe, native_re_deriv] using h1Parts.2
              have hEq : false = true := by
                simpa [RuleProofs.nativeListInRe_empty cs] using hCsEmpty
              cases hEq
            exact False.elim hBad
    | star r0 =>
        have h2Star :
            nativeListInRe s2 (SmtRegLan.star r0) = true := by
          simpa [native_re_mult, native_re_mk_star] using h2Parts.2
        simpa [native_re_mult, native_re_mk_star] using
          nativeListInRe_star_append_closed s1 s2 r0 h1Parts.2 h2Star
    | char c =>
        simp [native_re_mult, native_re_mk_star] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.char c) s1 s2
          h1Parts.2 h2Parts.2
    | range lo hi =>
        simp [native_re_mult, native_re_mk_star] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.range lo hi) s1 s2
          h1Parts.2 h2Parts.2
    | allchar =>
        simp [native_re_mult, native_re_mk_star] at h2Parts ⊢
        exact nativeListInRe_star_append_intro SmtRegLan.allchar s1 s2
          h1Parts.2 h2Parts.2
    | concat r0 r1 =>
        simp [native_re_mult, native_re_mk_star] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.concat r0 r1) s1 s2
          h1Parts.2 h2Parts.2
    | union r0 r1 =>
        simp [native_re_mult, native_re_mk_star] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.union r0 r1) s1 s2
          h1Parts.2 h2Parts.2
    | inter r0 r1 =>
        simp [native_re_mult, native_re_mk_star] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.inter r0 r1) s1 s2
          h1Parts.2 h2Parts.2
    | comp r0 =>
        simp [native_re_mult, native_re_mk_star] at h2Parts ⊢
        exact nativeListInRe_star_append_intro (SmtRegLan.comp r0) s1 s2
          h1Parts.2 h2Parts.2
  simpa [native_str_in_re, hValidAppend, nativeListInRe] using hList

private theorem native_str_in_re_str_to_re_empty_false_of_ne
    {s : native_String} :
    s ≠ [] ->
      native_str_in_re s (native_str_to_re ([] : native_String)) = false := by
  intro hNe
  cases hMem : native_str_in_re s (native_str_to_re ([] : native_String))
  · rfl
  · have hs : s = [] := native_str_in_re_str_to_re_true_eq hMem
    exact False.elim (hNe hs)

private theorem native_str_in_re_re_mult_middle_factor
    (s : native_String) (r : native_RegLan) :
    native_str_in_re s (native_re_mult r) = true ->
    s ≠ [] ->
    native_str_in_re s r ≠ true ->
      native_str_in_re s
        (native_re_concat (native_re_diff r (native_str_to_re []))
          (native_re_concat (native_re_mult r)
            (native_re_concat (native_re_diff r (native_str_to_re []))
              (native_str_to_re [])))) = true := by
  intro hStar hNe hNotBase
  have hParts :
      native_string_valid s = true ∧
        nativeListInRe s (native_re_mult r) = true := by
    simpa [native_str_in_re, nativeListInRe] using hStar
  have hRawStar :
      nativeListInRe s (SmtRegLan.star r) = true := by
    cases r with
    | empty =>
        have hs : s = [] := native_str_in_re_str_to_re_true_eq (by
          simpa [native_re_mult, native_re_mk_star, native_str_to_re,
            native_re_of_list] using hStar)
        exact False.elim (hNe hs)
    | epsilon =>
        have hs : s = [] := native_str_in_re_str_to_re_true_eq (by
          simpa [native_re_mult, native_re_mk_star, native_str_to_re,
            native_re_of_list] using hStar)
        exact False.elim (hNe hs)
    | star r0 =>
        exact False.elim (hNotBase (by
          simpa [native_re_mult, native_re_mk_star] using hStar))
    | char c =>
        simpa [native_re_mult, native_re_mk_star] using hParts.2
    | range lo hi =>
        simpa [native_re_mult, native_re_mk_star] using hParts.2
    | allchar =>
        simpa [native_re_mult, native_re_mk_star] using hParts.2
    | concat r0 r1 =>
        simpa [native_re_mult, native_re_mk_star] using hParts.2
    | union r0 r1 =>
        simpa [native_re_mult, native_re_mk_star] using hParts.2
    | inter r0 r1 =>
        simpa [native_re_mult, native_re_mk_star] using hParts.2
    | comp r0 =>
        simpa [native_re_mult, native_re_mk_star] using hParts.2
  have hNotRaw : nativeListInRe s r ≠ true := by
    intro hRaw
    have hBase : native_str_in_re s r = true := by
      simpa [native_str_in_re, hParts.1, nativeListInRe] using hRaw
    exact hNotBase hBase
  rcases nativeListInRe_raw_star_middle_last s r hRawStar hNe hNotRaw with
    ⟨first, middle, last, hEq, hFirstNe, hLastNe, hFirstRaw, hMiddleRaw,
      hLastRaw⟩
  have hValidFirst : native_string_valid first = true :=
    native_string_valid_append_left first (middle ++ last) (by
      rw [← List.append_assoc, ← hEq]
      exact hParts.1)
  have hValidMiddleLast : native_string_valid (middle ++ last) = true :=
    native_string_valid_append_right first (middle ++ last) (by
      rw [← List.append_assoc, ← hEq]
      exact hParts.1)
  have hValidMiddle : native_string_valid middle = true :=
    native_string_valid_append_left middle last hValidMiddleLast
  have hValidLast : native_string_valid last = true :=
    native_string_valid_append_right middle last hValidMiddleLast
  have hFirst : native_str_in_re first r = true := by
    simpa [native_str_in_re, hValidFirst, nativeListInRe] using hFirstRaw
  have hMiddle : native_str_in_re middle (native_re_mult r) = true := by
    have hList :
        nativeListInRe middle (native_re_mult r) = true := by
      cases r with
      | empty =>
          have hs : s = [] := native_str_in_re_str_to_re_true_eq (by
            simpa [native_re_mult, native_re_mk_star, native_str_to_re,
              native_re_of_list] using hStar)
          exact False.elim (hNe hs)
      | epsilon =>
          have hs : s = [] := native_str_in_re_str_to_re_true_eq (by
            simpa [native_re_mult, native_re_mk_star, native_str_to_re,
              native_re_of_list] using hStar)
          exact False.elim (hNe hs)
      | star r0 =>
          exact False.elim (hNotBase (by
            simpa [native_re_mult, native_re_mk_star] using hStar))
      | char c =>
          simpa [native_re_mult, native_re_mk_star] using hMiddleRaw
      | range lo hi =>
          simpa [native_re_mult, native_re_mk_star] using hMiddleRaw
      | allchar =>
          simpa [native_re_mult, native_re_mk_star] using hMiddleRaw
      | concat r0 r1 =>
          simpa [native_re_mult, native_re_mk_star] using hMiddleRaw
      | union r0 r1 =>
          simpa [native_re_mult, native_re_mk_star] using hMiddleRaw
      | inter r0 r1 =>
          simpa [native_re_mult, native_re_mk_star] using hMiddleRaw
      | comp r0 =>
          simpa [native_re_mult, native_re_mk_star] using hMiddleRaw
    simpa [native_str_in_re, hValidMiddle, nativeListInRe] using hList
  have hLast : native_str_in_re last r = true := by
    simpa [native_str_in_re, hValidLast, nativeListInRe] using hLastRaw
  have hFirstDiff :
      native_str_in_re first
        (native_re_diff r (native_str_to_re ([] : native_String))) = true := by
    rw [native_str_in_re_re_diff]
    simp [hFirst, native_str_in_re_str_to_re_empty_false_of_ne hFirstNe]
  have hLastDiff :
      native_str_in_re last
        (native_re_diff r (native_str_to_re ([] : native_String))) = true := by
    rw [native_str_in_re_re_diff]
    simp [hLast, native_str_in_re_str_to_re_empty_false_of_ne hLastNe]
  have hEps :
      native_str_in_re ([] : native_String)
        (native_str_to_re ([] : native_String)) = true := by
    simp [native_str_in_re, native_string_valid, native_str_to_re,
      native_re_of_list, nativeListInRe, native_re_nullable]
  have hLastConcat :
      native_str_in_re (last ++ ([] : native_String))
        (native_re_concat
          (native_re_diff r (native_str_to_re ([] : native_String)))
          (native_str_to_re ([] : native_String))) = true := by
    have hValidLE : native_string_valid (last ++ ([] : native_String)) = true := by
      simpa using hValidLast
    have hList :
        nativeListInRe (last ++ ([] : native_String))
          (native_re_concat
            (native_re_diff r (native_str_to_re ([] : native_String)))
            (native_str_to_re ([] : native_String))) = true := by
      have hLD :
          nativeListInRe last
            (native_re_diff r (native_str_to_re ([] : native_String))) =
            true := by
        have hPartsLD :
            native_string_valid last = true ∧
              nativeListInRe last
                (native_re_diff r (native_str_to_re ([] : native_String))) =
                true := by
          simpa [native_str_in_re, nativeListInRe] using hLastDiff
        exact hPartsLD.2
      have hE :
          nativeListInRe ([] : native_String)
            (native_str_to_re ([] : native_String)) = true := by
        have hPartsE :
            native_string_valid ([] : native_String) = true ∧
              nativeListInRe ([] : native_String)
                (native_str_to_re ([] : native_String)) = true := by
          simpa [native_str_in_re, nativeListInRe] using hEps
        exact hPartsE.2
      exact
        (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          (last ++ ([] : native_String))
          (native_re_diff r (native_str_to_re ([] : native_String)))
          (native_str_to_re ([] : native_String))).2
          ⟨last, [], rfl, hLD, hE⟩
    unfold native_str_in_re
    change
      (if native_string_valid (last ++ ([] : native_String)) = true then
        nativeListInRe (last ++ ([] : native_String))
          (native_re_concat
            (native_re_diff r (native_str_to_re ([] : native_String)))
            (native_str_to_re ([] : native_String)))
      else false) = true
    rw [hValidLE]
    exact hList
  have hMiddleTail :
      native_str_in_re (middle ++ (last ++ ([] : native_String)))
        (native_re_concat (native_re_mult r)
          (native_re_concat
            (native_re_diff r (native_str_to_re ([] : native_String)))
            (native_str_to_re ([] : native_String)))) = true := by
    have hValidMT : native_string_valid (middle ++ (last ++ ([] : native_String))) = true := by
      have hAllM : middle.all native_char_valid = true := by
        simpa [native_string_valid] using hValidMiddle
      have hAllL : last.all native_char_valid = true := by
        simpa [native_string_valid] using hValidLast
      simp [native_string_valid, hAllM, hAllL]
    have hList :
        nativeListInRe (middle ++ (last ++ ([] : native_String)))
          (native_re_concat (native_re_mult r)
            (native_re_concat
              (native_re_diff r (native_str_to_re ([] : native_String)))
              (native_str_to_re ([] : native_String)))) = true := by
      have hMList :
          nativeListInRe middle (native_re_mult r) = true := by
        unfold native_str_in_re at hMiddle
        change
          (if native_string_valid middle = true then
            nativeListInRe middle (native_re_mult r)
          else false) = true at hMiddle
        rw [hValidMiddle] at hMiddle
        exact hMiddle
      have hTailList :
          nativeListInRe (last ++ ([] : native_String))
            (native_re_concat
              (native_re_diff r (native_str_to_re ([] : native_String)))
              (native_str_to_re ([] : native_String))) = true := by
        have hValidTail : native_string_valid (last ++ ([] : native_String)) = true := by
          simpa using hValidLast
        unfold native_str_in_re at hLastConcat
        change
          (if native_string_valid (last ++ ([] : native_String)) = true then
            nativeListInRe (last ++ ([] : native_String))
              (native_re_concat
                (native_re_diff r (native_str_to_re ([] : native_String)))
                (native_str_to_re ([] : native_String)))
          else false) = true at hLastConcat
        rw [hValidTail] at hLastConcat
        exact hLastConcat
      exact
        (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          (middle ++ (last ++ ([] : native_String))) (native_re_mult r)
          (native_re_concat
            (native_re_diff r (native_str_to_re ([] : native_String)))
            (native_str_to_re ([] : native_String)))).2
          ⟨middle, last ++ ([] : native_String), rfl, hMList,
            hTailList⟩
    unfold native_str_in_re
    change
      (if native_string_valid
          (middle ++ (last ++ ([] : native_String))) = true then
        nativeListInRe (middle ++ (last ++ ([] : native_String)))
          (native_re_concat (native_re_mult r)
            (native_re_concat
              (native_re_diff r (native_str_to_re ([] : native_String)))
              (native_str_to_re ([] : native_String))))
      else false) = true
    rw [hValidMT]
    exact hList
  have hAll :
      native_str_in_re
        (first ++ (middle ++ (last ++ ([] : native_String))))
        (native_re_concat (native_re_diff r (native_str_to_re []))
          (native_re_concat (native_re_mult r)
            (native_re_concat (native_re_diff r (native_str_to_re []))
              (native_str_to_re [])))) = true := by
    have hValidAll : native_string_valid
        (first ++ (middle ++ (last ++ ([] : native_String)))) = true := by
      have hAllF : first.all native_char_valid = true := by
        simpa [native_string_valid] using hValidFirst
      have hAllM : middle.all native_char_valid = true := by
        simpa [native_string_valid] using hValidMiddle
      have hAllL : last.all native_char_valid = true := by
        simpa [native_string_valid] using hValidLast
      simp [native_string_valid, hAllF, hAllM, hAllL]
    have hList :
        nativeListInRe
          (first ++ (middle ++ (last ++ ([] : native_String))))
          (native_re_concat (native_re_diff r (native_str_to_re []))
            (native_re_concat (native_re_mult r)
              (native_re_concat (native_re_diff r (native_str_to_re []))
                (native_str_to_re [])))) = true := by
      have hFList :
            nativeListInRe first
              (native_re_diff r (native_str_to_re ([] : native_String))) =
            true := by
        unfold native_str_in_re at hFirstDiff
        change
          (if native_string_valid first = true then
            nativeListInRe first
              (native_re_diff r (native_str_to_re ([] : native_String)))
          else false) = true at hFirstDiff
        rw [hValidFirst] at hFirstDiff
        exact hFirstDiff
      have hTailList :
          nativeListInRe (middle ++ (last ++ ([] : native_String)))
            (native_re_concat (native_re_mult r)
              (native_re_concat
                (native_re_diff r (native_str_to_re ([] : native_String)))
                (native_str_to_re ([] : native_String)))) = true := by
        have hValidTail : native_string_valid
            (middle ++ (last ++ ([] : native_String))) = true := by
          have hAllM : middle.all native_char_valid = true := by
            simpa [native_string_valid] using hValidMiddle
          have hAllL : last.all native_char_valid = true := by
            simpa [native_string_valid] using hValidLast
          simp [native_string_valid, hAllM, hAllL]
        unfold native_str_in_re at hMiddleTail
        change
          (if native_string_valid
              (middle ++ (last ++ ([] : native_String))) = true then
            nativeListInRe (middle ++ (last ++ ([] : native_String)))
              (native_re_concat (native_re_mult r)
                (native_re_concat
                  (native_re_diff r (native_str_to_re ([] : native_String)))
                  (native_str_to_re ([] : native_String))))
          else false) = true at hMiddleTail
        rw [hValidTail] at hMiddleTail
        exact hMiddleTail
      exact
        (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append
          (first ++ (middle ++ (last ++ ([] : native_String))))
          (native_re_diff r (native_str_to_re ([] : native_String)))
          (native_re_concat (native_re_mult r)
            (native_re_concat
              (native_re_diff r (native_str_to_re ([] : native_String)))
              (native_str_to_re ([] : native_String))))).2
          ⟨first, middle ++ (last ++ ([] : native_String)), rfl, hFList,
            hTailList⟩
    unfold native_str_in_re
    change
      (if native_string_valid
          (first ++ (middle ++ (last ++ ([] : native_String)))) = true then
        nativeListInRe (first ++ (middle ++ (last ++ ([] : native_String))))
          (native_re_concat (native_re_diff r (native_str_to_re []))
            (native_re_concat (native_re_mult r)
              (native_re_concat (native_re_diff r (native_str_to_re []))
                (native_str_to_re []))))
      else false) = true
    rw [hValidAll]
    exact hList
  have hSeq :
      first ++ (middle ++ (last ++ ([] : native_String))) = s := by
    rw [hEq]
    simp [List.append_assoc]
  rw [← hSeq]
  exact hAll

private theorem native_str_indexof_re_split_aux_spec
    (r1 r2 : native_RegLan) :
    ∀ (pre suf : native_String) (i : native_Nat),
      i = pre.length ->
      (∃ mid right : native_String,
        mid ++ right = suf ∧
          native_str_in_re (pre ++ mid) r1 = true ∧
          native_str_in_re right r2 = true) ->
      ∃ left right : native_String,
        left ++ right = pre ++ suf ∧
          native_str_in_re left r1 = true ∧
          native_str_in_re right r2 = true ∧
          native_str_indexof_re_split_aux r1 r2 pre suf i =
            Int.ofNat left.length
  | pre, suf, i, hi, hExists => by
      cases hCur :
          (native_str_in_re pre r1 && native_str_in_re suf r2)
      · cases suf with
        | nil =>
            rcases hExists with ⟨mid, right, hAppend, hLeft, hRight⟩
            cases mid <;> cases right <;> simp at hAppend
            have hLeftPre : native_str_in_re pre r1 = true := by
              simpa using hLeft
            have hBoth :
                (native_str_in_re pre r1 && native_str_in_re [] r2) =
                  true := by
              simp [hLeftPre, hRight]
            rw [hBoth] at hCur
            cases hCur
        | cons c cs =>
            rcases hExists with ⟨mid, right, hAppend, hLeft, hRight⟩
            cases mid with
            | nil =>
                have hRightEq : right = c :: cs := by
                  simpa using hAppend
                subst right
                have hLeftPre : native_str_in_re pre r1 = true := by
                  simpa using hLeft
                have hBoth :
                    (native_str_in_re pre r1 &&
                        native_str_in_re (c :: cs) r2) = true := by
                  simp [hLeftPre, hRight]
                rw [hBoth] at hCur
                cases hCur
            | cons d midTail =>
                cases hAppend
                let tailRight : native_String := right
                have hRecExists :
                    ∃ mid right' : native_String,
                      mid ++ right' = midTail ++ tailRight ∧
                        native_str_in_re ((pre ++ [c]) ++ mid) r1 = true ∧
                        native_str_in_re right' r2 = true := by
                  refine ⟨midTail, tailRight, rfl, ?_, ?_⟩
                  · simpa [tailRight, List.append_assoc] using hLeft
                  · simpa [tailRight] using hRight
                have hIdxStep :
                    native_str_indexof_re_split_aux r1 r2 pre
                        (c :: midTail ++ tailRight) i =
                      native_str_indexof_re_split_aux r1 r2
                        (pre ++ [c]) (midTail ++ tailRight) (i + 1) := by
                  rw [native_str_indexof_re_split_aux.eq_def]
                  change
                    (if
                        (native_str_in_re pre r1 &&
                            native_str_in_re (c :: midTail ++ tailRight) r2) =
                          true
                      then Int.ofNat i
                      else
                        native_str_indexof_re_split_aux r1 r2
                          (pre ++ [c]) (midTail ++ tailRight) (i + 1)) =
                    native_str_indexof_re_split_aux r1 r2
                      (pre ++ [c]) (midTail ++ tailRight) (i + 1)
                  have hCur' :
                      (native_str_in_re pre r1 &&
                          native_str_in_re (c :: midTail ++ tailRight) r2) =
                        false := by
                    simpa [tailRight] using hCur
                  have hCondFalse :
                      ¬ ((native_str_in_re pre r1 &&
                            native_str_in_re (c :: midTail ++ tailRight) r2) =
                          true) := by
                    intro hTrue
                    rw [hTrue] at hCur'
                    cases hCur'
                  rw [if_neg hCondFalse]
                have hi' : i + 1 = (pre ++ [c]).length := by
                  subst i
                  simp
                rcases
                  native_str_indexof_re_split_aux_spec r1 r2
                    (pre ++ [c]) (midTail ++ tailRight) (i + 1) hi'
                    hRecExists with
                  ⟨left, right, hAppendLR, hLeftLR, hRightLR, hIdx⟩
                refine ⟨left, right, ?_, hLeftLR, hRightLR, ?_⟩
                · simpa [tailRight, List.append_assoc] using hAppendLR
                · exact (by
                    simpa [tailRight] using hIdxStep.trans hIdx)
      · refine ⟨pre, suf, by simp, ?_, ?_, ?_⟩
        · have hParts :
              native_str_in_re pre r1 = true ∧
                native_str_in_re suf r2 = true := by
            simpa [Bool.and_eq_true] using hCur
          exact hParts.1
        · have hParts :
              native_str_in_re pre r1 = true ∧
                native_str_in_re suf r2 = true := by
            simpa [Bool.and_eq_true] using hCur
          exact hParts.2
        · subst i
          have hCondTrue :
              (native_str_in_re pre r1 && native_str_in_re suf r2) = true :=
            hCur
          simpa [native_str_indexof_re_split_aux.eq_def, hCondTrue]
termination_by pre suf _ _ _ => suf.length

private theorem native_str_indexof_re_split_spec
    (s : native_String) (r1 r2 : native_RegLan) :
    native_str_in_re s (native_re_concat r1 r2) = true ->
      ∃ left right : native_String,
        left ++ right = s ∧
          native_str_in_re left r1 = true ∧
          native_str_in_re right r2 = true ∧
          native_str_indexof_re_split s r1 r2 =
            Int.ofNat left.length := by
  intro h
  have hParts :
      native_string_valid s = true ∧
        nativeListInRe s (native_re_concat r1 r2) = true := by
    simpa [native_str_in_re, nativeListInRe] using h
  have hList :
      nativeListInRe s (native_re_mk_concat r1 r2) = true := by
    simpa [native_re_concat] using hParts.2
  rcases
      (RuleProofs.nativeListInRe_mk_concat_true_iff_exists_append s r1 r2).1
        hList with
    ⟨left, right, hAppend, hLeftList, hRightList⟩
  have hValidLeft : native_string_valid left = true :=
    native_string_valid_append_left left right (by
      rw [hAppend]
      exact hParts.1)
  have hValidRight : native_string_valid right = true :=
    native_string_valid_append_right left right (by
      rw [hAppend]
      exact hParts.1)
  have hLeft : native_str_in_re left r1 = true := by
    simpa [native_str_in_re, hValidLeft, nativeListInRe] using hLeftList
  have hRight : native_str_in_re right r2 = true := by
    simpa [native_str_in_re, hValidRight, nativeListInRe] using hRightList
  have hAuxExists :
      ∃ mid right : native_String,
        mid ++ right = s ∧
          native_str_in_re ([] ++ mid) r1 = true ∧
          native_str_in_re right r2 = true := by
    exact ⟨left, right, hAppend, by simpa using hLeft, hRight⟩
  rcases
    native_str_indexof_re_split_aux_spec r1 r2 [] s 0 (by rfl)
      hAuxExists with
    ⟨splitLeft, splitRight, hSplitAppend, hSplitLeft, hSplitRight, hIdx⟩
  refine ⟨splitLeft, splitRight, by simpa using hSplitAppend,
    hSplitLeft, hSplitRight, ?_⟩
  simp [native_str_indexof_re_split, hParts.1, hIdx]

private theorem list_typed_char_pack_unpack :
    ∀ {xs : List SmtValue},
      list_typed SmtType.Char xs ->
        xs.map (fun v => SmtValue.Char (native_ssm_char_of_value v)) = xs
  | [], _ => rfl
  | v :: vs, hxs => by
      rcases hxs with ⟨hv, hvs⟩
      rcases char_value_canonical hv with ⟨c, hvc, _hc⟩
      rw [hvc]
      simpa [native_ssm_char_of_value] using list_typed_char_pack_unpack hvs

private theorem native_pack_string_unpack_string_of_typeof_seq_char
    (ss : SmtSeq)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char) :
    native_pack_string (native_unpack_string ss) = ss := by
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (native_ssm_char_of_value v)) =
        native_unpack_seq ss :=
    list_typed_char_pack_unpack hTyped
  unfold native_pack_string native_unpack_string
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  simp only [List.map_map]
  change native_pack_seq SmtType.Char
      ((native_unpack_seq ss).map
        (fun v => SmtValue.Char (native_ssm_char_of_value v))) =
    ss
  rw [hMap]
  rw [← native_pack_unpack_seq ss, hElem]
  simp [native_unpack_pack_seq]

private theorem native_seq_substr_split
    (ss : SmtSeq) (i : native_Int)
    (hi0 : 0 <= i)
    (hile : i <= native_seq_len (native_unpack_seq ss)) :
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
        (native_seq_extract (native_unpack_seq ss) 0 i ++
          native_seq_extract (native_unpack_seq ss) i
            (native_seq_len (native_unpack_seq ss) - i)) =
      native_pack_seq (__smtx_elem_typeof_seq_value ss)
        (native_unpack_seq ss) := by
  let xs := native_unpack_seq ss
  let n := Int.toNat i
  have hiCast : (Int.ofNat n : Int) = i := by
    simpa [n] using Int.toNat_of_nonneg hi0
  have hNLe : n <= xs.length := by
    have hInt : (Int.ofNat n : Int) <= Int.ofNat xs.length := by
      rw [hiCast]
      simpa [xs, native_seq_len] using hile
    exact Int.ofNat_le.mp hInt
  have hLeft :
      native_seq_extract xs 0 i = xs.take n := by
    rw [← hiCast]
    exact native_seq_extract_zero_nat xs n hNLe
  have hLenSub :
      native_seq_len xs - Int.ofNat n = Int.ofNat (xs.length - n) := by
    rw [native_seq_len]
    exact (Int.ofNat_sub hNLe).symm
  have hRight :
      native_seq_extract xs i (native_seq_len xs - i) = xs.drop n := by
    rw [← hiCast, hLenSub]
    exact native_seq_extract_to_end_nat xs n hNLe
  rw [hLeft, hRight, List.take_append_drop]

private theorem native_seq_substr_split_self
    (ss : SmtSeq) (i : native_Int)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hi0 : 0 <= i)
    (hile : i <= native_seq_len (native_unpack_seq ss)) :
    native_pack_seq (__smtx_elem_typeof_seq_value ss)
        (native_seq_extract (native_unpack_seq ss) 0 i ++
          native_seq_extract (native_unpack_seq ss) i
            (native_seq_len (native_unpack_seq ss) - i)) =
      ss := by
  rw [native_seq_substr_split ss i hi0 hile]
  exact native_pack_unpack_seq ss

private theorem native_string_append_to_seq_append
    (xs ys : native_String) :
    native_pack_string (xs ++ ys) =
      native_pack_seq SmtType.Char
        (native_unpack_seq (native_pack_string xs) ++
          native_unpack_seq (native_pack_string ys)) := by
  simp [native_pack_string, native_unpack_pack_seq, List.map_append]

private theorem smtx_typeof_str_concat_of_seq_char (x y : Term)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char) :
    __smtx_typeof (__eo_to_smt (mkStrConcat x y)) =
      SmtType.Seq SmtType.Char := by
  simpa [mkStrConcat] using
    smt_typeof_str_concat_of_seq x y SmtType.Char hx hy

private theorem smtx_typeof_str_to_re_of_seq_char (s : Term)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char) :
    __smtx_typeof (__eo_to_smt (mkStrToRe s)) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtType.RegLan
  rw [typeof_str_to_re_eq]
  simp [hs, native_Teq, native_ite]

private theorem smtx_typeof_str_to_re_arg_of_reglan (s : Term) :
    __smtx_typeof (__eo_to_smt (mkStrToRe s)) = SmtType.RegLan ->
      __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char := by
  intro hTy
  change __smtx_typeof (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtType.RegLan at hTy
  rw [typeof_str_to_re_eq] at hTy
  by_cases hs : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char
  · exact hs
  · simp [hs, native_Teq, native_ite] at hTy

private theorem smtx_typeof_re_diff_of_reglan (r s : Term)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan)
    (hs : __smtx_typeof (__eo_to_smt s) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (mkReDiff r s)) = SmtType.RegLan := by
  change __smtx_typeof (SmtTerm.re_diff (__eo_to_smt r) (__eo_to_smt s)) =
    SmtType.RegLan
  rw [typeof_re_diff_eq]
  simp [hr, hs, native_ite, native_Teq]

private theorem eval_str_concat_of_seq (M : SmtModel)
    (s t : Term) (ss tt : SmtSeq) :
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq tt ->
    __smtx_model_eval M (__eo_to_smt (mkStrConcat s t)) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_unpack_seq ss ++ native_unpack_seq tt)) := by
  intro hs ht
  change __smtx_model_eval M
      (SmtTerm.str_concat (__eo_to_smt s) (__eo_to_smt t)) =
    SmtValue.Seq
      (native_pack_seq (__smtx_elem_typeof_seq_value ss)
        (native_unpack_seq ss ++ native_unpack_seq tt))
  simp [__smtx_model_eval, __smtx_model_eval_str_concat, hs, ht,
    native_seq_concat]

private theorem eval_str_to_re_of_seq (M : SmtModel)
    (s : Term) (ss : SmtSeq) :
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ->
    __smtx_model_eval M (__eo_to_smt (mkStrToRe s)) =
      SmtValue.RegLan (native_str_to_re (native_unpack_string ss)) := by
  intro hs
  change __smtx_model_eval M (SmtTerm.str_to_re (__eo_to_smt s)) =
    SmtValue.RegLan (native_str_to_re (native_unpack_string ss))
  simp [__smtx_model_eval, __smtx_model_eval_str_to_re, hs]

private theorem eval_re_diff_of_reglan (M : SmtModel)
    (r s : Term) (rv sv : native_RegLan) :
    __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
    __smtx_model_eval M (__eo_to_smt s) = SmtValue.RegLan sv ->
    __smtx_model_eval M (__eo_to_smt (mkReDiff r s)) =
      SmtValue.RegLan (native_re_diff rv sv) := by
  intro hr hs
  change __smtx_model_eval M
      (SmtTerm.re_diff (__eo_to_smt r) (__eo_to_smt s)) =
    SmtValue.RegLan (native_re_diff rv sv)
  simp [__smtx_model_eval, __smtx_model_eval_re_diff, hr, hs]

private theorem eval_re_mult_of_reglan (M : SmtModel)
    (r : Term) (rv : native_RegLan) :
    __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
    __smtx_model_eval M (__eo_to_smt (mkReMult r)) =
      SmtValue.RegLan (native_re_mult rv) := by
  intro hr
  change __smtx_model_eval M (SmtTerm.re_mult (__eo_to_smt r)) =
    SmtValue.RegLan (native_re_mult rv)
  simp [__smtx_model_eval, __smtx_model_eval_re_mult, hr]

private theorem eval_smt_str_concat_of_seq (M : SmtModel)
    (s t : SmtTerm) (ss tt : SmtSeq) :
    __smtx_model_eval M s = SmtValue.Seq ss ->
    __smtx_model_eval M t = SmtValue.Seq tt ->
    __smtx_model_eval M (SmtTerm.str_concat s t) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_unpack_seq ss ++ native_unpack_seq tt)) := by
  intro hs ht
  simp [__smtx_model_eval, __smtx_model_eval_str_concat, hs, ht,
    native_seq_concat]

private theorem eval_smt_substr_of_seq_ints (M : SmtModel)
    (s i n : SmtTerm) (ss : SmtSeq) (zi zn : native_Int) :
    __smtx_model_eval M s = SmtValue.Seq ss ->
    __smtx_model_eval M i = SmtValue.Numeral zi ->
    __smtx_model_eval M n = SmtValue.Numeral zn ->
    __smtx_model_eval M (SmtTerm.str_substr s i n) =
      SmtValue.Seq
        (native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_extract (native_unpack_seq ss) zi zn)) := by
  intro hs hi hn
  simp [__smtx_model_eval, __smtx_model_eval_str_substr, hs, hi, hn]

private theorem eval_smt_strlen_of_seq (M : SmtModel)
    (s : SmtTerm) (ss : SmtSeq) :
    __smtx_model_eval M s = SmtValue.Seq ss ->
    __smtx_model_eval M (SmtTerm.str_len s) =
      SmtValue.Numeral (native_seq_len (native_unpack_seq ss)) := by
  intro hs
  simp [__smtx_model_eval, __smtx_model_eval_str_len, hs]

private theorem eval_smt_neg_of_ints (M : SmtModel)
    (x y : SmtTerm) (zx zy : native_Int) :
    __smtx_model_eval M x = SmtValue.Numeral zx ->
    __smtx_model_eval M y = SmtValue.Numeral zy ->
    __smtx_model_eval M (SmtTerm.neg x y) =
      SmtValue.Numeral (zx - zy) := by
  intro hx hy
  simp [__smtx_model_eval, __smtx_model_eval__, hx, hy,
    SmtEval.native_zplus, SmtEval.native_zneg, Int.sub_eq_add_neg]

private theorem eval_smt_str_indexof_re_split_of_seq_reglan
    (M : SmtModel) (s r1 r2 : SmtTerm)
    (ss : SmtSeq) (rv1 rv2 : native_RegLan) :
    __smtx_model_eval M s = SmtValue.Seq ss ->
    __smtx_model_eval M r1 = SmtValue.RegLan rv1 ->
    __smtx_model_eval M r2 = SmtValue.RegLan rv2 ->
    __smtx_model_eval M (SmtTerm.str_indexof_re_split s r1 r2) =
      SmtValue.Numeral
        (native_str_indexof_re_split (native_unpack_string ss) rv1 rv2) := by
  intro hs hr1 hr2
  simp [__smtx_model_eval, __smtx_model_eval_str_indexof_re_split,
    hs, hr1, hr2]

private theorem smtx_typeof_smt_str_indexof_re_split_of_seq_reglan
    (s r1 r2 : SmtTerm)
    (hs : __smtx_typeof s = SmtType.Seq SmtType.Char)
    (hr1 : __smtx_typeof r1 = SmtType.RegLan)
    (hr2 : __smtx_typeof r2 = SmtType.RegLan) :
    __smtx_typeof (SmtTerm.str_indexof_re_split s r1 r2) =
      SmtType.Int := by
  rw [typeof_str_indexof_re_split_eq]
  simp [hs, hr1, hr2, native_ite, native_Teq]

private theorem smtx_typeof_smt_substr_of_seq_char
    (s i n : SmtTerm)
    (hs : __smtx_typeof s = SmtType.Seq SmtType.Char)
    (hi : __smtx_typeof i = SmtType.Int)
    (hn : __smtx_typeof n = SmtType.Int) :
    __smtx_typeof (SmtTerm.str_substr s i n) =
      SmtType.Seq SmtType.Char := by
  rw [typeof_str_substr_eq]
  simp [__smtx_typeof_str_substr, hs, hi, hn]

private theorem smtx_typeof_smt_strlen_of_seq_char (s : SmtTerm)
    (hs : __smtx_typeof s = SmtType.Seq SmtType.Char) :
    __smtx_typeof (SmtTerm.str_len s) = SmtType.Int := by
  rw [typeof_str_len_eq]
  simp [hs, __smtx_typeof_seq_op_1_ret]

private theorem smtx_typeof_smt_neg_of_ints (x y : SmtTerm)
    (hx : __smtx_typeof x = SmtType.Int)
    (hy : __smtx_typeof y = SmtType.Int) :
    __smtx_typeof (SmtTerm.neg x y) = SmtType.Int := by
  simpa using smtx_typeof_neg_int x y hx hy

private theorem seq_value_type_of_eval_seq
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (ss : SmtSeq)
    (hTy : __smtx_typeof t = SmtType.Seq SmtType.Char)
    (hEval : __smtx_model_eval M t = SmtValue.Seq ss) :
    __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) =
        SmtType.Seq SmtType.Char :=
    by
      simpa [hTy] using
        smt_model_eval_preserves_type_of_non_none M hM t hNN
  simpa [hEval] using hValTy

private theorem term_ne_stuck_of_smt_type_seq_char (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char ->
      t ≠ Term.Stuck := by
  intro hTy hStuck
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.Seq SmtType.Char at hTy
  simp [__smtx_typeof] at hTy

private theorem eo_mk_apply_ne_stuck_of_ne_stuck (f x : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x ≠ Term.Stuck := by
  intro hf hx
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem native_unpack_string_substr_left
    (ss : SmtSeq) (left right : native_String)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hUnpack : native_unpack_string ss = left ++ right) :
    native_unpack_string
        (native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_extract (native_unpack_seq ss) 0
            (Int.ofNat left.length))) = left := by
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMap :
      (native_unpack_seq ss).map
          (fun v => SmtValue.Char (native_ssm_char_of_value v)) =
        native_unpack_seq ss :=
    list_typed_char_pack_unpack hTyped
  have hMapChars :
      (native_unpack_seq ss).map native_ssm_char_of_value = left ++ right := by
    simpa [native_unpack_string] using hUnpack
  have hLenLe : left.length <= (native_unpack_seq ss).length := by
    have hLen := congrArg List.length hMapChars
    simp at hLen
    omega
  have hExtract :
      native_seq_extract (native_unpack_seq ss) 0 (Int.ofNat left.length) =
        (native_unpack_seq ss).take left.length :=
    native_seq_extract_zero_nat (native_unpack_seq ss) left.length hLenLe
  unfold native_unpack_string
  rw [hElem, hExtract]
  simp [native_unpack_seq_pack_seq]
  rw [hMapChars]
  simp

private theorem native_unpack_string_substr_right
    (ss : SmtSeq) (left right : native_String)
    (hTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hUnpack : native_unpack_string ss = left ++ right) :
    native_unpack_string
        (native_pack_seq (__smtx_elem_typeof_seq_value ss)
          (native_seq_extract (native_unpack_seq ss)
            (Int.ofNat left.length)
            (native_seq_len (native_unpack_seq ss) -
              Int.ofNat left.length))) = right := by
  have hElem : __smtx_elem_typeof_seq_value ss = SmtType.Char :=
    elem_typeof_seq_value_of_typeof_seq_value hTy
  have hTyped : list_typed SmtType.Char (native_unpack_seq ss) :=
    typed_unpack_seq_of_typeof_seq_value hTy
  have hMapChars :
      (native_unpack_seq ss).map native_ssm_char_of_value = left ++ right := by
    simpa [native_unpack_string] using hUnpack
  have hLenLe : left.length <= (native_unpack_seq ss).length := by
    have hLen := congrArg List.length hMapChars
    simp at hLen
    omega
  have hLenSub :
      native_seq_len (native_unpack_seq ss) - Int.ofNat left.length =
        Int.ofNat ((native_unpack_seq ss).length - left.length) := by
    rw [native_seq_len]
    exact (Int.ofNat_sub hLenLe).symm
  have hExtract :
      native_seq_extract (native_unpack_seq ss) (Int.ofNat left.length)
          (native_seq_len (native_unpack_seq ss) - Int.ofNat left.length) =
        (native_unpack_seq ss).drop left.length := by
    rw [hLenSub]
    exact native_seq_extract_to_end_nat (native_unpack_seq ss) left.length hLenLe
  unfold native_unpack_string
  rw [hElem, hExtract]
  simp [native_unpack_seq_pack_seq]
  rw [hMapChars]
  simp

private theorem native_seq_concat_eq_of_unpack_string
    (ss leftSeq rightSeq : SmtSeq) (left right : native_String)
    (hSsTy : __smtx_typeof_seq_value ss = SmtType.Seq SmtType.Char)
    (hLeftTy : __smtx_typeof_seq_value leftSeq = SmtType.Seq SmtType.Char)
    (hRightTy : __smtx_typeof_seq_value rightSeq = SmtType.Seq SmtType.Char)
    (hSs : native_unpack_string ss = left ++ right)
    (hLeft : native_unpack_string leftSeq = left)
    (hRight : native_unpack_string rightSeq = right) :
    native_pack_seq (__smtx_elem_typeof_seq_value leftSeq)
        (native_unpack_seq leftSeq ++ native_unpack_seq rightSeq) = ss := by
  have hLeftPack :
      leftSeq = native_pack_string left := by
    calc
      leftSeq = native_pack_string (native_unpack_string leftSeq) :=
        (native_pack_string_unpack_string_of_typeof_seq_char
          leftSeq hLeftTy).symm
      _ = native_pack_string left := by rw [hLeft]
  have hRightPack :
      rightSeq = native_pack_string right := by
    calc
      rightSeq = native_pack_string (native_unpack_string rightSeq) :=
        (native_pack_string_unpack_string_of_typeof_seq_char
          rightSeq hRightTy).symm
      _ = native_pack_string right := by rw [hRight]
  have hSsPack :
      ss = native_pack_string (left ++ right) := by
    calc
      ss = native_pack_string (native_unpack_string ss) :=
        (native_pack_string_unpack_string_of_typeof_seq_char ss hSsTy).symm
      _ = native_pack_string (left ++ right) := by rw [hSs]
  rw [hLeftPack, hRightPack, hSsPack]
  simp [native_pack_string, native_unpack_pack_seq, List.map_append,
    elem_typeof_native_pack_seq]

private theorem str_in_re_native_true
    (M : SmtModel) (hM : model_total_typed M) (s r : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hrTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    eo_interprets M (mkStrInRe s r) true ->
      ∃ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
        native_str_in_re (native_unpack_string ss) rv = true := by
  intro hPrem
  rcases smt_eval_seq_char_of_smt_type_seq_char M hM (__eo_to_smt s) hsTy with
    ⟨ss, hsEval⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r) hrTy with
    ⟨rv, hrEval⟩
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _hTy hEval =>
      have hNative :
          native_str_in_re (native_unpack_string ss) rv = true := by
        change __smtx_model_eval M
            (SmtTerm.str_in_re (__eo_to_smt s) (__eo_to_smt r)) =
          SmtValue.Boolean true at hEval
        simp [__smtx_model_eval, __smtx_model_eval_str_in_re,
          hsEval, hrEval] at hEval
        exact hEval
      exact ⟨ss, rv, hsEval, hrEval, hNative⟩

private theorem str_in_re_re_mult_native_true
    (M : SmtModel) (hM : model_total_typed M) (s r : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hrTy : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    eo_interprets M (mkStrInRe s (mkReMult r)) true ->
      ∃ ss rv,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
        __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ∧
        native_str_in_re (native_unpack_string ss)
          (native_re_mult rv) = true := by
  intro hPrem
  rcases str_in_re_native_true M hM s (mkReMult r) hsTy
      (smtx_typeof_re_mult_of_reglan r hrTy) hPrem with
    ⟨ss, rvStar, hsEval, hStarEval, hYes⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r) hrTy with
    ⟨rv, hrEval⟩
  have hStarEval' := eval_re_mult_of_reglan M r rv hrEval
  rw [hStarEval'] at hStarEval
  cases hStarEval
  exact ⟨ss, rv, hsEval, hrEval, hYes⟩

private theorem str_in_re_re_concat_native_true
    (M : SmtModel) (hM : model_total_typed M) (s r1 r2 : Term)
    (hsTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq SmtType.Char)
    (hr1Ty : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan) :
    eo_interprets M (mkStrInRe s (mkReConcat r1 r2)) true ->
      ∃ ss rv1 rv2,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.Seq ss ∧
        __smtx_model_eval M (__eo_to_smt r1) = SmtValue.RegLan rv1 ∧
        __smtx_model_eval M (__eo_to_smt r2) = SmtValue.RegLan rv2 ∧
        native_str_in_re (native_unpack_string ss)
          (native_re_concat rv1 rv2) = true := by
  intro hPrem
  rcases str_in_re_native_true M hM s (mkReConcat r1 r2) hsTy
      (smtx_typeof_re_concat_of_reglan r1 r2 hr1Ty hr2Ty) hPrem with
    ⟨ss, rvConcat, hsEval, hConcatEval, hYes⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r1) hr1Ty with
    ⟨rv1, hr1Eval⟩
  rcases smt_eval_reglan_of_smt_type_reglan M hM (__eo_to_smt r2) hr2Ty with
    ⟨rv2, hr2Eval⟩
  have hConcatEval' := eval_re_concat_of_reglan M r1 r2 rv1 rv2 hr1Eval hr2Eval
  rw [hConcatEval'] at hConcatEval
  cases hConcatEval
  exact ⟨ss, rv1, rv2, hsEval, hr1Eval, hr2Eval, hYes⟩

private theorem re_unfold_pos_concat_rec_tail_ne_of_ne
    (t r1 r2 ro : Term) (idx : Nat) :
    __re_unfold_pos_concat_rec t
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2)
        ro (idxTerm idx) ≠ Term.Stuck ->
    __re_unfold_pos_concat_rec t r2 ro (idxTerm (idx + 1)) ≠ Term.Stuck := by
  intro hNe hTail
  apply hNe
  have hTail' :
      __re_unfold_pos_concat_rec t r2 ro
          (__eo_add (idxTerm idx) (Term.Numeral 1)) = Term.Stuck := by
    simpa [idxTerm, __eo_add, SmtEval.native_zplus] using hTail
  unfold __re_unfold_pos_concat_rec
  split <;> simp_all [idxTerm, __eo_add, SmtEval.native_zplus, __pair_first,
    __pair_second, __eo_mk_apply]

private theorem re_unfold_pos_concat_rec_eval_true
    (M : SmtModel) (hM : model_total_typed M)
    (t ro : Term) :
    ∀ (r : Term) (idx : Nat) (curS : SmtTerm) (ss : SmtSeq)
      (rv : native_RegLan),
      (∀ j : Nat,
        __eo_to_smt (mkAtReUnfoldPosComponent t ro (idxTerm (idx + j))) =
          __eo_to_smt_re_unfold_pos_component curS (__eo_to_smt r) j) ->
      __smtx_typeof curS = SmtType.Seq SmtType.Char ->
      __smtx_model_eval M curS = SmtValue.Seq ss ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      native_str_in_re (native_unpack_string ss) rv = true ->
      __re_unfold_pos_concat_rec t r ro (idxTerm idx) ≠ Term.Stuck ->
      ∃ first guard,
        __re_unfold_pos_concat_rec t r ro (idxTerm idx) =
          Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) first) guard ∧
        __smtx_model_eval M (__eo_to_smt first) = SmtValue.Seq ss ∧
        __smtx_typeof (__eo_to_smt first) = SmtType.Seq SmtType.Char ∧
        __smtx_model_eval M (__eo_to_smt guard) = SmtValue.Boolean true ∧
        RuleProofs.eo_has_bool_type guard
  | Term.Apply f arg, idx, curS, ss, rv, hComponent, hCurTy, hCurEval,
      hrTy, hrEval, hMem, hRecNe => by
      cases f with
      | UOp op =>
          cases op with
          | str_to_re =>
              cases arg with
              | String pat =>
                  cases pat with
                  | nil =>
                      change __smtx_model_eval M
                          (SmtTerm.str_to_re (SmtTerm.String [])) =
                        SmtValue.RegLan rv at hrEval
                      simp [__smtx_model_eval, __smtx_model_eval_str_to_re] at hrEval
                      cases hrEval
                      have hSeqTy :=
                        seq_value_type_of_eval_seq M hM curS ss hCurTy hCurEval
                      have hEmpty :
                          native_unpack_string ss = ([] : native_String) :=
                        native_str_in_re_str_to_re_true_eq hMem
                      have hss :
                          ss = native_pack_string ([] : native_String) := by
                        calc
                          ss = native_pack_string (native_unpack_string ss) :=
                            (native_pack_string_unpack_string_of_typeof_seq_char
                              ss hSeqTy).symm
                          _ = native_pack_string ([] : native_String) := by rw [hEmpty]
                      have htNe : t ≠ Term.Stuck := by
                        intro ht
                        apply hRecNe
                        subst t
                        simp [__re_unfold_pos_concat_rec]
                      have hroNe : ro ≠ Term.Stuck := by
                        intro hro
                        apply hRecNe
                        subst ro
                        unfold __re_unfold_pos_concat_rec
                        split <;> simp_all [idxTerm]
                      refine ⟨Term.String [], Term.Boolean true, ?_, ?_, ?_, ?_, ?_⟩
                      · unfold __re_unfold_pos_concat_rec
                        split <;> simp_all [idxTerm]
                      · change __smtx_model_eval M (SmtTerm.String []) =
                          SmtValue.Seq ss
                        simp [__smtx_model_eval, hss]
                      · change __smtx_typeof (SmtTerm.String []) =
                          SmtType.Seq SmtType.Char
                        simp [__smtx_typeof, native_string_valid, native_ite]
                      · simp [__smtx_model_eval]
                      · exact RuleProofs.eo_has_bool_type_true
                  | cons _ _ =>
                      exact False.elim (by
                        unfold __re_unfold_pos_concat_rec at hRecNe
                        split at hRecNe <;> simp_all)
              | _ =>
                  exact False.elim (by
                    unfold __re_unfold_pos_concat_rec at hRecNe
                    split at hRecNe <;> simp_all)
          | _ =>
              exact False.elim (by
                unfold __re_unfold_pos_concat_rec at hRecNe
                split at hRecNe <;> simp_all)
      | Apply fHead r1 =>
          cases fHead with
          | UOp op =>
              cases op with
              | re_concat =>
                  have hRArgs :=
                    smtx_typeof_re_concat_args_of_reglan r1 arg hrTy
                  rcases smt_eval_reglan_of_smt_type_reglan M hM
                      (__eo_to_smt r1) hRArgs.1 with
                    ⟨rv1, hr1Eval⟩
                  rcases smt_eval_reglan_of_smt_type_reglan M hM
                      (__eo_to_smt arg) hRArgs.2 with
                    ⟨rv2, hr2Eval⟩
                  have hConcatEval :=
                    eval_re_concat_of_reglan M r1 arg rv1 rv2 hr1Eval hr2Eval
                  rw [hConcatEval] at hrEval
                  cases hrEval
                  rcases native_str_indexof_re_split_spec
                      (native_unpack_string ss) rv1 rv2 hMem with
                    ⟨left, right, hAppend, hLeftMem, hRightMem, hSplit⟩
                  let splitTerm : SmtTerm :=
                    SmtTerm.str_indexof_re_split curS (__eo_to_smt r1)
                      (__eo_to_smt arg)
                  let suffixSmt : SmtTerm :=
                    SmtTerm.str_substr curS splitTerm
                      (SmtTerm.neg (SmtTerm.str_len curS) splitTerm)
                  let rightSeq : SmtSeq :=
                    native_pack_seq (__smtx_elem_typeof_seq_value ss)
                      (native_seq_extract (native_unpack_seq ss)
                        (Int.ofNat left.length)
                        (native_seq_len (native_unpack_seq ss) -
                          Int.ofNat left.length))
                  have hSplitEval :
                      __smtx_model_eval M splitTerm =
                        SmtValue.Numeral (Int.ofNat left.length) := by
                    simpa [splitTerm, hSplit] using
                      eval_smt_str_indexof_re_split_of_seq_reglan
                        M curS (__eo_to_smt r1) (__eo_to_smt arg)
                        ss rv1 rv2 hCurEval hr1Eval hr2Eval
                  have hLenEval :
                      __smtx_model_eval M (SmtTerm.str_len curS) =
                        SmtValue.Numeral
                          (native_seq_len (native_unpack_seq ss)) :=
                    eval_smt_strlen_of_seq M curS ss hCurEval
                  have hNegEval :
                      __smtx_model_eval M
                          (SmtTerm.neg (SmtTerm.str_len curS) splitTerm) =
                        SmtValue.Numeral
                          (native_seq_len (native_unpack_seq ss) -
                            Int.ofNat left.length) :=
                    eval_smt_neg_of_ints M (SmtTerm.str_len curS) splitTerm
                      (native_seq_len (native_unpack_seq ss))
                      (Int.ofNat left.length) hLenEval hSplitEval
                  have hSuffixEval :
                      __smtx_model_eval M suffixSmt = SmtValue.Seq rightSeq := by
                    simpa [suffixSmt, rightSeq] using
                      eval_smt_substr_of_seq_ints M curS splitTerm
                        (SmtTerm.neg (SmtTerm.str_len curS) splitTerm)
                        ss (Int.ofNat left.length)
                        (native_seq_len (native_unpack_seq ss) -
                          Int.ofNat left.length)
                        hCurEval hSplitEval hNegEval
                  have hSplitTy :
                      __smtx_typeof splitTerm = SmtType.Int :=
                    smtx_typeof_smt_str_indexof_re_split_of_seq_reglan
                      curS (__eo_to_smt r1) (__eo_to_smt arg)
                      hCurTy hRArgs.1 hRArgs.2
                  have hLenTy :
                      __smtx_typeof (SmtTerm.str_len curS) = SmtType.Int :=
                    smtx_typeof_smt_strlen_of_seq_char curS hCurTy
                  have hNegTy :
                      __smtx_typeof
                          (SmtTerm.neg (SmtTerm.str_len curS) splitTerm) =
                        SmtType.Int :=
                    smtx_typeof_smt_neg_of_ints (SmtTerm.str_len curS)
                      splitTerm hLenTy hSplitTy
                  have hSuffixTy :
                      __smtx_typeof suffixSmt =
                        SmtType.Seq SmtType.Char := by
                    simpa [suffixSmt] using
                      smtx_typeof_smt_substr_of_seq_char curS splitTerm
                        (SmtTerm.neg (SmtTerm.str_len curS) splitTerm)
                        hCurTy hSplitTy hNegTy
                  have hSeqTy :=
                    seq_value_type_of_eval_seq M hM curS ss hCurTy hCurEval
                  have hRightUnpack :
                      native_unpack_string rightSeq = right := by
                    simpa [rightSeq] using
                      native_unpack_string_substr_right ss left right hSeqTy
                        hAppend.symm
                  have hRightMemSeq :
                      native_str_in_re (native_unpack_string rightSeq) rv2 =
                        true := by
                    simpa [hRightUnpack] using hRightMem
                  have hComponent' :
                      ∀ j : Nat,
                        __eo_to_smt
                            (mkAtReUnfoldPosComponent t ro
                              (idxTerm ((idx + 1) + j))) =
                          __eo_to_smt_re_unfold_pos_component suffixSmt
                            (__eo_to_smt arg) j := by
                    intro j
                    have h := hComponent (j + 1)
                    have hNat : idx + (j + 1) = (idx + 1) + j := by omega
                    simpa [hNat, __eo_to_smt_re_unfold_pos_component,
                      suffixSmt, splitTerm] using h
                  have hTailRecNe :
                      __re_unfold_pos_concat_rec t arg ro (idxTerm (idx + 1)) ≠
                        Term.Stuck :=
                    re_unfold_pos_concat_rec_tail_ne_of_ne t r1 arg ro idx hRecNe
                  rcases re_unfold_pos_concat_rec_eval_true M hM t ro arg
                      (idx + 1) suffixSmt rightSeq rv2 hComponent'
                      hSuffixTy hSuffixEval hRArgs.2 hr2Eval hRightMemSeq
                      hTailRecNe with
                    ⟨tailFirst, tailGuard, hTailEq, hTailFirstEval,
                      hTailFirstTy, hTailGuardEval, hTailGuardBool⟩
                  have hRightSeqTy :=
                    seq_value_type_of_eval_seq M hM suffixSmt rightSeq
                      hSuffixTy hSuffixEval
                  have hTailFirstNe :
                      tailFirst ≠ Term.Stuck :=
                    term_ne_stuck_of_smt_type_seq_char tailFirst hTailFirstTy
                  have hTailGuardNe :
                      tailGuard ≠ Term.Stuck :=
                    term_ne_stuck_of_has_smt_translation tailGuard
                      (RuleProofs.eo_has_smt_translation_of_has_bool_type
                        tailGuard hTailGuardBool)
                  have htNe : t ≠ Term.Stuck := by
                    intro ht
                    apply hRecNe
                    subst t
                    simp [__re_unfold_pos_concat_rec]
                  have hroNe : ro ≠ Term.Stuck := by
                    intro hro
                    apply hRecNe
                    subst ro
                    unfold __re_unfold_pos_concat_rec
                    split <;> simp_all [idxTerm]
                  by_cases hLit : ∃ s1, r1 = mkStrToRe s1
                  · rcases hLit with ⟨s1, rfl⟩
                    have hs1Ty :
                        __smtx_typeof (__eo_to_smt s1) =
                          SmtType.Seq SmtType.Char :=
                      smtx_typeof_str_to_re_arg_of_reglan s1 hRArgs.1
                    rcases smt_eval_seq_char_of_smt_type_seq_char M hM
                        (__eo_to_smt s1) hs1Ty with
                      ⟨s1Seq, hs1Eval⟩
                    have hr1Eval' :=
                      eval_str_to_re_of_seq M s1 s1Seq hs1Eval
                    rw [hr1Eval'] at hr1Eval
                    cases hr1Eval
                    have hLeftEq :
                        left = native_unpack_string s1Seq :=
                      native_str_in_re_str_to_re_true_eq hLeftMem
                    have hs1SeqTy :=
                      seq_value_type_of_eval_seq M hM (__eo_to_smt s1)
                        s1Seq hs1Ty hs1Eval
                    let first := mkStrConcat s1 tailFirst
                    have hFirstTy :
                        __smtx_typeof (__eo_to_smt first) =
                          SmtType.Seq SmtType.Char :=
                      smtx_typeof_str_concat_of_seq_char s1 tailFirst
                        hs1Ty hTailFirstTy
                    have hFirstNe : first ≠ Term.Stuck := by
                      simp [first, mkStrConcat]
                    have hConcatAppNe :
                        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                            tailFirst ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.Apply (Term.UOp UserOp.str_concat) s1)
                        tailFirst (by simp) hTailFirstNe
                    have hConcatAppEq :
                        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                            tailFirst = first :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hConcatAppNe
                    have hPairFunNe :
                        __eo_mk_apply
                            (Term.UOp UserOp._at__at_pair) first ≠
                          Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.UOp UserOp._at__at_pair) first
                        (by simp) hFirstNe
                    have hFinalNe :
                        __eo_mk_apply
                            (__eo_mk_apply
                              (Term.UOp UserOp._at__at_pair) first)
                            tailGuard ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (__eo_mk_apply
                          (Term.UOp UserOp._at__at_pair) first)
                        tailGuard hPairFunNe hTailGuardNe
                    have hFinalEq :
                        __eo_mk_apply
                            (__eo_mk_apply
                              (Term.UOp UserOp._at__at_pair) first)
                            tailGuard =
                          Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_pair) first)
                            tailGuard :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hFinalNe
                    refine ⟨first, tailGuard, ?_, ?_, hFirstTy,
                      hTailGuardEval, hTailGuardBool⟩
                    · simp_all [__re_unfold_pos_concat_rec, idxTerm, __eo_add,
                        SmtEval.native_zplus, __pair_first, __pair_second,
                        hConcatAppEq, hFinalEq, __eo_mk_apply, mkStrConcat,
                        mkStrToRe]
                    · have hConcatEvalFirst :=
                        eval_str_concat_of_seq M s1 tailFirst s1Seq rightSeq
                          hs1Eval hTailFirstEval
                      change __smtx_model_eval M (__eo_to_smt first) =
                        SmtValue.Seq ss
                      rw [hConcatEvalFirst]
                      congr
                      exact
                        native_seq_concat_eq_of_unpack_string ss s1Seq rightSeq
                          (native_unpack_string s1Seq) right
                          hSeqTy hs1SeqTy hRightSeqTy
                          (by simpa [hLeftEq] using hAppend.symm)
                          rfl hRightUnpack
                  · have hComponent0 := hComponent 0
                    let comp :=
                      mkAtReUnfoldPosComponent t ro (idxTerm idx)
                    let leftSeq : SmtSeq :=
                      native_pack_seq (__smtx_elem_typeof_seq_value ss)
                        (native_seq_extract (native_unpack_seq ss) 0
                          (Int.ofNat left.length))
                    have hLeftUnpack :
                        native_unpack_string leftSeq = left := by
                      simpa [leftSeq] using
                        native_unpack_string_substr_left ss left right hSeqTy
                          hAppend.symm
                    have hComponent0' :
                        __eo_to_smt comp =
                          __eo_to_smt_re_unfold_pos_component curS
                            (__eo_to_smt
                              (((Term.UOp UserOp.re_concat).Apply r1).Apply arg))
                            0 := by
                      simpa [comp, idxTerm] using hComponent0
                    have hCompEval :
                        __smtx_model_eval M (__eo_to_smt comp) =
                          SmtValue.Seq leftSeq := by
                      rw [hComponent0']
                      simpa [leftSeq, splitTerm,
                        __eo_to_smt_re_unfold_pos_component] using
                        eval_smt_substr_of_seq_ints M curS
                          (SmtTerm.Numeral 0) splitTerm ss 0
                          (Int.ofNat left.length) hCurEval
                          (by simp [__smtx_model_eval])
                          hSplitEval
                    have hCompTy :
                        __smtx_typeof (__eo_to_smt comp) =
                          SmtType.Seq SmtType.Char := by
                      rw [hComponent0']
                      simpa [splitTerm,
                        __eo_to_smt_re_unfold_pos_component] using
                        smtx_typeof_smt_substr_of_seq_char curS
                          (SmtTerm.Numeral 0) splitTerm hCurTy
                          (by simp [__smtx_typeof])
                          hSplitTy
                    have hLeftSeqTy :=
                      seq_value_type_of_eval_seq M hM (__eo_to_smt comp)
                        leftSeq hCompTy hCompEval
                    have hLeftInEval :
                        __smtx_model_eval M (__eo_to_smt (mkStrInRe comp r1)) =
                          SmtValue.Boolean true := by
                      have hRaw :=
                        eval_str_in_re_of_seq_reglan M comp r1 leftSeq rv1
                          hCompEval hr1Eval
                      simpa [hLeftUnpack, hLeftMem] using hRaw
                    have hLeftInBool :
                        RuleProofs.eo_has_bool_type (mkStrInRe comp r1) :=
                      smtx_typeof_str_in_re_of_seq_reglan comp r1
                        hCompTy hRArgs.1
                    let first := mkStrConcat comp tailFirst
                    let guard := mkAnd (mkStrInRe comp r1) tailGuard
                    have hFirstTy :
                        __smtx_typeof (__eo_to_smt first) =
                          SmtType.Seq SmtType.Char :=
                      smtx_typeof_str_concat_of_seq_char comp tailFirst
                        hCompTy hTailFirstTy
                    have hGuardBool :
                        RuleProofs.eo_has_bool_type guard :=
                      RuleProofs.eo_has_bool_type_and_of_bool_args
                        _ _ hLeftInBool hTailGuardBool
                    have hGuardEval :
                        __smtx_model_eval M (__eo_to_smt guard) =
                          SmtValue.Boolean true := by
                      change __smtx_model_eval M
                          (SmtTerm.and (__eo_to_smt (mkStrInRe comp r1))
                            (__eo_to_smt tailGuard)) =
                        SmtValue.Boolean true
                      simp [__smtx_model_eval, __smtx_model_eval_and,
                        hLeftInEval, hTailGuardEval, SmtEval.native_and]
                    have hCompNe :
                        comp ≠ Term.Stuck :=
                      term_ne_stuck_of_smt_type_seq_char comp hCompTy
                    have hFirstNe : first ≠ Term.Stuck := by
                      simp [first, mkStrConcat]
                    have hLeftInNe :
                        mkStrInRe comp r1 ≠ Term.Stuck :=
                      term_ne_stuck_of_has_smt_translation (mkStrInRe comp r1)
                        (RuleProofs.eo_has_smt_translation_of_has_bool_type
                          (mkStrInRe comp r1) hLeftInBool)
                    have hGuardNe : guard ≠ Term.Stuck := by
                      simp [guard, mkAnd]
                    have hConcatAppNe :
                        __eo_mk_apply
                            (Term.Apply (Term.UOp UserOp.str_concat) comp)
                            tailFirst ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.Apply (Term.UOp UserOp.str_concat) comp)
                        tailFirst (by simp) hTailFirstNe
                    have hConcatAppEq :
                        __eo_mk_apply
                            (Term.Apply (Term.UOp UserOp.str_concat) comp)
                            tailFirst = first :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hConcatAppNe
                    have hGuardAppNe :
                        __eo_mk_apply
                            (Term.Apply (Term.UOp UserOp.and)
                              (mkStrInRe comp r1))
                            tailGuard ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.Apply (Term.UOp UserOp.and)
                          (mkStrInRe comp r1))
                        tailGuard (by simp) hTailGuardNe
                    have hGuardAppEq :
                        __eo_mk_apply
                            (Term.Apply (Term.UOp UserOp.and)
                              (mkStrInRe comp r1))
                            tailGuard = guard :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hGuardAppNe
                    have hPairFunNe :
                        __eo_mk_apply (Term.UOp UserOp._at__at_pair) first ≠
                          Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.UOp UserOp._at__at_pair) first
                        (by simp) hFirstNe
                    have hFinalNe :
                        __eo_mk_apply
                            (__eo_mk_apply
                              (Term.UOp UserOp._at__at_pair) first)
                            guard ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (__eo_mk_apply
                          (Term.UOp UserOp._at__at_pair) first)
                        guard hPairFunNe hGuardNe
                    have hFinalEq :
                        __eo_mk_apply
                            (__eo_mk_apply
                              (Term.UOp UserOp._at__at_pair) first)
                            guard =
                          Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_pair) first)
                            guard :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hFinalNe
                    refine ⟨first, guard, ?_, ?_, hFirstTy, hGuardEval,
                      hGuardBool⟩
                    · simp_all [__re_unfold_pos_concat_rec, idxTerm, __eo_add,
                        SmtEval.native_zplus, __pair_first, __pair_second,
                        hFinalEq, __eo_mk_apply, mkStrToRe]
                      constructor
                      · simpa [comp, mkAtReUnfoldPosComponent] using hConcatAppEq
                      · simpa [comp, mkAtReUnfoldPosComponent, mkStrInRe] using
                          hGuardAppEq
                    · have hConcatEvalFirst :=
                        eval_str_concat_of_seq M comp tailFirst leftSeq rightSeq
                          hCompEval hTailFirstEval
                      change __smtx_model_eval M (__eo_to_smt first) =
                        SmtValue.Seq ss
                      rw [hConcatEvalFirst]
                      congr
                      exact
                        native_seq_concat_eq_of_unpack_string ss leftSeq rightSeq
                          left right hSeqTy hLeftSeqTy hRightSeqTy
                          hAppend.symm hLeftUnpack hRightUnpack
              | _ =>
                  exact False.elim (by
                    unfold __re_unfold_pos_concat_rec at hRecNe
                    split at hRecNe <;> simp_all)
          | _ =>
              exact False.elim (by
                unfold __re_unfold_pos_concat_rec at hRecNe
                split at hRecNe <;> simp_all)
      | _ =>
          exact False.elim (by
            unfold __re_unfold_pos_concat_rec at hRecNe
            split at hRecNe <;> simp_all)
  | Term.UOp _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy, hrEval,
      hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.UOp1 _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.UOp2 _ _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.UOp3 _ _ _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.__eo_List, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.__eo_List_nil, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.__eo_List_cons, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Bool, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy, hrEval,
      hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Boolean _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Numeral _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Rational _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.String _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Binary _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Type, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy, hrEval,
      hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Stuck, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy, hrEval,
      hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.FunType, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Var _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DatatypeType _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval,
      hrTy, hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DatatypeTypeRef _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval,
      hrTy, hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DtcAppType _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval,
      hrTy, hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DtCons _ _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DtSel _ _ _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.USort _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.UConst _ _, idx, curS, ss, rv, hComponent, hCurTy, hCurEval, hrTy,
      hrEval, hMem, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
termination_by r idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem
    hRecNe => sizeOf r
decreasing_by
  simp_wf
  omega

private theorem re_unfold_pos_concat_rec_types
    (t ro : Term) :
    ∀ (r : Term) (idx : Nat) (curS : SmtTerm),
      (∀ j : Nat,
        __eo_to_smt (mkAtReUnfoldPosComponent t ro (idxTerm (idx + j))) =
          __eo_to_smt_re_unfold_pos_component curS (__eo_to_smt r) j) ->
      __smtx_typeof curS = SmtType.Seq SmtType.Char ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __re_unfold_pos_concat_rec t r ro (idxTerm idx) ≠ Term.Stuck ->
      ∃ first guard,
        __re_unfold_pos_concat_rec t r ro (idxTerm idx) =
          Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) first) guard ∧
        __smtx_typeof (__eo_to_smt first) = SmtType.Seq SmtType.Char ∧
        RuleProofs.eo_has_bool_type guard
  | Term.Apply f arg, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      cases f with
      | UOp op =>
          cases op with
          | str_to_re =>
              cases arg with
              | String pat =>
                  cases pat with
                  | nil =>
                      have htNe : t ≠ Term.Stuck := by
                        intro ht
                        apply hRecNe
                        subst t
                        simp [__re_unfold_pos_concat_rec]
                      have hroNe : ro ≠ Term.Stuck := by
                        intro hro
                        apply hRecNe
                        subst ro
                        unfold __re_unfold_pos_concat_rec
                        split <;> simp_all [idxTerm]
                      refine ⟨Term.String [], Term.Boolean true, ?_, ?_, ?_⟩
                      · unfold __re_unfold_pos_concat_rec
                        split <;> simp_all [idxTerm]
                      · change __smtx_typeof (SmtTerm.String []) =
                          SmtType.Seq SmtType.Char
                        simp [__smtx_typeof, native_string_valid, native_ite]
                      · exact RuleProofs.eo_has_bool_type_true
                  | cons _ _ =>
                      exact False.elim (by
                        unfold __re_unfold_pos_concat_rec at hRecNe
                        split at hRecNe <;> simp_all)
              | _ =>
                  exact False.elim (by
                    unfold __re_unfold_pos_concat_rec at hRecNe
                    split at hRecNe <;> simp_all)
          | _ =>
              exact False.elim (by
                unfold __re_unfold_pos_concat_rec at hRecNe
                split at hRecNe <;> simp_all)
      | Apply fHead r1 =>
          cases fHead with
          | UOp op =>
              cases op with
              | re_concat =>
                  have hRArgs :=
                    smtx_typeof_re_concat_args_of_reglan r1 arg hrTy
                  let splitTerm : SmtTerm :=
                    SmtTerm.str_indexof_re_split curS (__eo_to_smt r1)
                      (__eo_to_smt arg)
                  let suffixSmt : SmtTerm :=
                    SmtTerm.str_substr curS splitTerm
                      (SmtTerm.neg (SmtTerm.str_len curS) splitTerm)
                  have hSplitTy :
                      __smtx_typeof splitTerm = SmtType.Int :=
                    smtx_typeof_smt_str_indexof_re_split_of_seq_reglan
                      curS (__eo_to_smt r1) (__eo_to_smt arg)
                      hCurTy hRArgs.1 hRArgs.2
                  have hLenTy :
                      __smtx_typeof (SmtTerm.str_len curS) = SmtType.Int :=
                    smtx_typeof_smt_strlen_of_seq_char curS hCurTy
                  have hNegTy :
                      __smtx_typeof
                          (SmtTerm.neg (SmtTerm.str_len curS) splitTerm) =
                        SmtType.Int :=
                    smtx_typeof_smt_neg_of_ints (SmtTerm.str_len curS)
                      splitTerm hLenTy hSplitTy
                  have hSuffixTy :
                      __smtx_typeof suffixSmt =
                        SmtType.Seq SmtType.Char := by
                    simpa [suffixSmt] using
                      smtx_typeof_smt_substr_of_seq_char curS splitTerm
                        (SmtTerm.neg (SmtTerm.str_len curS) splitTerm)
                        hCurTy hSplitTy hNegTy
                  have hComponent' :
                      ∀ j : Nat,
                        __eo_to_smt
                            (mkAtReUnfoldPosComponent t ro
                              (idxTerm ((idx + 1) + j))) =
                          __eo_to_smt_re_unfold_pos_component suffixSmt
                            (__eo_to_smt arg) j := by
                    intro j
                    have h := hComponent (j + 1)
                    have hNat : idx + (j + 1) = (idx + 1) + j := by omega
                    simpa [hNat, __eo_to_smt_re_unfold_pos_component,
                      suffixSmt, splitTerm] using h
                  have hTailRecNe :
                      __re_unfold_pos_concat_rec t arg ro (idxTerm (idx + 1)) ≠
                        Term.Stuck :=
                    re_unfold_pos_concat_rec_tail_ne_of_ne t r1 arg ro idx hRecNe
                  rcases re_unfold_pos_concat_rec_types t ro arg
                      (idx + 1) suffixSmt hComponent' hSuffixTy hRArgs.2
                      hTailRecNe with
                    ⟨tailFirst, tailGuard, hTailEq, hTailFirstTy,
                      hTailGuardBool⟩
                  have hTailFirstNe :
                      tailFirst ≠ Term.Stuck :=
                    term_ne_stuck_of_smt_type_seq_char tailFirst hTailFirstTy
                  have hTailGuardNe :
                      tailGuard ≠ Term.Stuck :=
                    term_ne_stuck_of_has_smt_translation tailGuard
                      (RuleProofs.eo_has_smt_translation_of_has_bool_type
                        tailGuard hTailGuardBool)
                  have htNe : t ≠ Term.Stuck := by
                    intro ht
                    apply hRecNe
                    subst t
                    simp [__re_unfold_pos_concat_rec]
                  have hroNe : ro ≠ Term.Stuck := by
                    intro hro
                    apply hRecNe
                    subst ro
                    unfold __re_unfold_pos_concat_rec
                    split <;> simp_all [idxTerm]
                  by_cases hLit : ∃ s1, r1 = mkStrToRe s1
                  · rcases hLit with ⟨s1, rfl⟩
                    have hs1Ty :
                        __smtx_typeof (__eo_to_smt s1) =
                          SmtType.Seq SmtType.Char :=
                      smtx_typeof_str_to_re_arg_of_reglan s1 hRArgs.1
                    let first := mkStrConcat s1 tailFirst
                    have hFirstTy :
                        __smtx_typeof (__eo_to_smt first) =
                          SmtType.Seq SmtType.Char :=
                      smtx_typeof_str_concat_of_seq_char s1 tailFirst
                        hs1Ty hTailFirstTy
                    have hFirstNe : first ≠ Term.Stuck := by
                      simp [first, mkStrConcat]
                    have hConcatAppNe :
                        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                            tailFirst ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.Apply (Term.UOp UserOp.str_concat) s1)
                        tailFirst (by simp) hTailFirstNe
                    have hConcatAppEq :
                        __eo_mk_apply (Term.Apply (Term.UOp UserOp.str_concat) s1)
                            tailFirst = first :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hConcatAppNe
                    have hPairFunNe :
                        __eo_mk_apply
                            (Term.UOp UserOp._at__at_pair) first ≠
                          Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.UOp UserOp._at__at_pair) first
                        (by simp) hFirstNe
                    have hFinalNe :
                        __eo_mk_apply
                            (__eo_mk_apply
                              (Term.UOp UserOp._at__at_pair) first)
                            tailGuard ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (__eo_mk_apply
                          (Term.UOp UserOp._at__at_pair) first)
                        tailGuard hPairFunNe hTailGuardNe
                    have hFinalEq :
                        __eo_mk_apply
                            (__eo_mk_apply
                              (Term.UOp UserOp._at__at_pair) first)
                            tailGuard =
                          Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_pair) first)
                            tailGuard :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hFinalNe
                    refine ⟨first, tailGuard, ?_, hFirstTy, hTailGuardBool⟩
                    · simp_all [__re_unfold_pos_concat_rec, idxTerm, __eo_add,
                        SmtEval.native_zplus, __pair_first, __pair_second,
                        hConcatAppEq, hFinalEq, __eo_mk_apply, mkStrConcat,
                        mkStrToRe]
                  · have hComponent0 := hComponent 0
                    let comp :=
                      mkAtReUnfoldPosComponent t ro (idxTerm idx)
                    have hComponent0' :
                        __eo_to_smt comp =
                          __eo_to_smt_re_unfold_pos_component curS
                            (__eo_to_smt
                              (Term.Apply
                                (Term.Apply (Term.UOp UserOp.re_concat) r1)
                                arg)) 0 := by
                      simpa [comp, idxTerm, Nat.add_zero] using hComponent0
                    have hCompTy :
                        __smtx_typeof (__eo_to_smt comp) =
                          SmtType.Seq SmtType.Char := by
                      rw [hComponent0']
                      simpa [comp, splitTerm,
                        __eo_to_smt_re_unfold_pos_component] using
                        smtx_typeof_smt_substr_of_seq_char curS
                          (SmtTerm.Numeral 0) splitTerm hCurTy
                          (by simp [__smtx_typeof])
                          hSplitTy
                    have hLeftInBool :
                        RuleProofs.eo_has_bool_type (mkStrInRe comp r1) :=
                      smtx_typeof_str_in_re_of_seq_reglan comp r1
                        hCompTy hRArgs.1
                    let first := mkStrConcat comp tailFirst
                    let guard := mkAnd (mkStrInRe comp r1) tailGuard
                    have hFirstTy :
                        __smtx_typeof (__eo_to_smt first) =
                          SmtType.Seq SmtType.Char :=
                      smtx_typeof_str_concat_of_seq_char comp tailFirst
                        hCompTy hTailFirstTy
                    have hGuardBool :
                        RuleProofs.eo_has_bool_type guard :=
                      RuleProofs.eo_has_bool_type_and_of_bool_args
                        _ _ hLeftInBool hTailGuardBool
                    have hFirstNe : first ≠ Term.Stuck := by
                      simp [first, mkStrConcat]
                    have hGuardNe : guard ≠ Term.Stuck := by
                      simp [guard, mkAnd]
                    have hConcatAppNe :
                        __eo_mk_apply
                            (Term.Apply (Term.UOp UserOp.str_concat) comp)
                            tailFirst ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.Apply (Term.UOp UserOp.str_concat) comp)
                        tailFirst (by simp) hTailFirstNe
                    have hConcatAppEq :
                        __eo_mk_apply
                            (Term.Apply (Term.UOp UserOp.str_concat) comp)
                            tailFirst = first :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hConcatAppNe
                    have hGuardAppNe :
                        __eo_mk_apply
                            (Term.Apply (Term.UOp UserOp.and)
                              (mkStrInRe comp r1))
                            tailGuard ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.Apply (Term.UOp UserOp.and)
                          (mkStrInRe comp r1))
                        tailGuard (by simp) hTailGuardNe
                    have hGuardAppEq :
                        __eo_mk_apply
                            (Term.Apply (Term.UOp UserOp.and)
                              (mkStrInRe comp r1))
                            tailGuard = guard :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hGuardAppNe
                    have hPairFunNe :
                        __eo_mk_apply (Term.UOp UserOp._at__at_pair) first ≠
                          Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (Term.UOp UserOp._at__at_pair) first
                        (by simp) hFirstNe
                    have hFinalNe :
                        __eo_mk_apply
                            (__eo_mk_apply
                              (Term.UOp UserOp._at__at_pair) first)
                            guard ≠ Term.Stuck :=
                      eo_mk_apply_ne_stuck_of_ne_stuck
                        (__eo_mk_apply
                          (Term.UOp UserOp._at__at_pair) first)
                        guard hPairFunNe hGuardNe
                    have hFinalEq :
                        __eo_mk_apply
                            (__eo_mk_apply
                              (Term.UOp UserOp._at__at_pair) first)
                            guard =
                          Term.Apply
                            (Term.Apply (Term.UOp UserOp._at__at_pair) first)
                            guard :=
                      eo_mk_apply_eq_apply_of_ne_stuck _ _ hFinalNe
                    refine ⟨first, guard, ?_, hFirstTy, hGuardBool⟩
                    · simp_all [__re_unfold_pos_concat_rec, idxTerm, __eo_add,
                        SmtEval.native_zplus, __pair_first, __pair_second,
                        hFinalEq, __eo_mk_apply, mkStrToRe]
                      constructor
                      · simpa [comp, mkAtReUnfoldPosComponent] using hConcatAppEq
                      · simpa [comp, mkAtReUnfoldPosComponent, mkStrInRe] using
                          hGuardAppEq
              | _ =>
                  exact False.elim (by
                    unfold __re_unfold_pos_concat_rec at hRecNe
                    split at hRecNe <;> simp_all)
          | _ =>
              exact False.elim (by
                unfold __re_unfold_pos_concat_rec at hRecNe
                split at hRecNe <;> simp_all)
      | _ =>
          exact False.elim (by
            unfold __re_unfold_pos_concat_rec at hRecNe
            split at hRecNe <;> simp_all)
  | Term.Stuck, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Var _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.__eo_List, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.__eo_List_nil, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.__eo_List_cons, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Bool, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.String _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Numeral _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Rational _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Binary _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.Boolean _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.UOp _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.UOp1 _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.UOp2 _ _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.UOp3 _ _ _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.«Type», idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.FunType, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DatatypeType _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DatatypeTypeRef _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DtcAppType _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DtCons _ _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.DtSel _ _ _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.USort _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
  | Term.UConst _ _, idx, curS, hComponent, hCurTy, hrTy, hRecNe => by
      exact False.elim (by
        unfold __re_unfold_pos_concat_rec at hRecNe
        split at hRecNe <;> simp_all)
termination_by r idx curS hComponent hCurTy hrTy hRecNe => sizeOf r
decreasing_by
  simp_wf
  omega

/- TODO: reintroduce this induction in equation style; `Term` is mutually inductive,
so tactic induction is not available here.
private theorem re_unfold_pos_concat_rec_eval_true
    (M : SmtModel) (hM : model_total_typed M)
    (t ro r : Term) :
    ∀ (idx : Nat) (curS : SmtTerm) (ss : SmtSeq) (rv : native_RegLan),
      (∀ j : Nat,
        __eo_to_smt (mkAtReUnfoldPosComponent t ro (idxTerm (idx + j))) =
          __eo_to_smt_re_unfold_pos_component curS (__eo_to_smt r) j) ->
      __smtx_typeof curS = SmtType.Seq SmtType.Char ->
      __smtx_model_eval M curS = SmtValue.Seq ss ->
      __smtx_typeof (__eo_to_smt r) = SmtType.RegLan ->
      __smtx_model_eval M (__eo_to_smt r) = SmtValue.RegLan rv ->
      native_str_in_re (native_unpack_string ss) rv = true ->
      __re_unfold_pos_concat_rec t r ro (idxTerm idx) ≠ Term.Stuck ->
      ∃ first guard,
        __re_unfold_pos_concat_rec t r ro (idxTerm idx) =
          Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) first) guard ∧
        __smtx_model_eval M (__eo_to_smt first) = SmtValue.Seq ss ∧
        __smtx_typeof (__eo_to_smt first) = SmtType.Seq SmtType.Char ∧
        __smtx_model_eval M (__eo_to_smt guard) = SmtValue.Boolean true ∧
        RuleProofs.eo_has_bool_type guard := by
  intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
  revert idx curS ss rv
  induction r with
  | Stuck =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | Var v ty =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | __eo_List =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | __eo_List_nil =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | __eo_List_cons =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | Bool =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | String s =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | Numeral n =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | Rational q =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | Binary w n =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | Boolean b =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | UOp op =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | UOp1 op a =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | UOp2 op a b =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | UOp3 op a b c =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | «Type» =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | FunType =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | DatatypeType s d =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | DatatypeTypeRef s =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | DtcAppType a b ihA ihB =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | DtCons s d i =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | DtSel s d i j =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | USort n =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | UConst n ty ih =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      exact False.elim (by
        simpa [__re_unfold_pos_concat_rec] using hRecNe)
  | Apply f arg ihF ihArg =>
      intro idx curS ss rv hComponent hCurTy hCurEval hrTy hrEval hMem hRecNe
      cases f with
      | UOp op =>
          cases op with
          | str_to_re =>
              cases arg with
              | String pat =>
                  cases pat with
                  | nil =>
                      change __smtx_model_eval M
                          (SmtTerm.str_to_re (SmtTerm.String [])) =
                        SmtValue.RegLan rv at hrEval
                      simp [__smtx_model_eval, __smtx_model_eval_str_to_re] at hrEval
                      cases hrEval
                      have hSeqTy :=
                        seq_value_type_of_eval_seq M hM curS ss hCurTy hCurEval
                      have hEmpty :
                          native_unpack_string ss = ([] : native_String) :=
                        native_str_in_re_str_to_re_true_eq hMem
                      have hss :
                          ss = native_pack_string ([] : native_String) := by
                        calc
                          ss = native_pack_string (native_unpack_string ss) :=
                            (native_pack_string_unpack_string_of_typeof_seq_char
                              ss hSeqTy).symm
                          _ = native_pack_string ([] : native_String) := by rw [hEmpty]
                      refine ⟨Term.String [], Term.Boolean true, ?_, ?_, ?_, ?_, ?_⟩
                      · simp [__re_unfold_pos_concat_rec]
                      · change __smtx_model_eval M (SmtTerm.String []) =
                          SmtValue.Seq ss
                        simp [__smtx_model_eval, hss]
                      · change __smtx_typeof (SmtTerm.String []) =
                          SmtType.Seq SmtType.Char
                        simp [__smtx_typeof, native_string_valid, native_ite]
                      · simp [__smtx_model_eval]
                      · exact RuleProofs.eo_has_bool_type_true
                  | cons c cs =>
                      exact False.elim (by
                        simpa [__re_unfold_pos_concat_rec] using hRecNe)
              | _ =>
                  exact False.elim (by
                    simpa [__re_unfold_pos_concat_rec] using hRecNe)
          | _ =>
              exact False.elim (by
                simpa [__re_unfold_pos_concat_rec] using hRecNe)
      | Apply fHead r1 =>
          cases fHead with
          | UOp op =>
              cases op with
              | re_concat =>
                  have hRArgs :=
                    smtx_typeof_re_concat_args_of_reglan r1 arg hrTy
                  rcases smt_eval_reglan_of_smt_type_reglan M hM
                      (__eo_to_smt r1) hRArgs.1 with
                    ⟨rv1, hr1Eval⟩
                  rcases smt_eval_reglan_of_smt_type_reglan M hM
                      (__eo_to_smt arg) hRArgs.2 with
                    ⟨rv2, hr2Eval⟩
                  have hConcatEval :=
                    eval_re_concat_of_reglan M r1 arg rv1 rv2 hr1Eval hr2Eval
                  rw [hConcatEval] at hrEval
                  cases hrEval
                  rcases native_str_indexof_re_split_spec
                      (native_unpack_string ss) rv1 rv2 hMem with
                    ⟨left, right, hAppend, hLeftMem, hRightMem, hSplit⟩
                  let splitTerm : SmtTerm :=
                    SmtTerm.str_indexof_re_split curS (__eo_to_smt r1)
                      (__eo_to_smt arg)
                  let suffixSmt : SmtTerm :=
                    SmtTerm.str_substr curS splitTerm
                      (SmtTerm.neg (SmtTerm.str_len curS) splitTerm)
                  let rightSeq : SmtSeq :=
                    native_pack_seq (__smtx_elem_typeof_seq_value ss)
                      (native_seq_extract (native_unpack_seq ss)
                        (Int.ofNat left.length)
                        (native_seq_len (native_unpack_seq ss) -
                          Int.ofNat left.length))
                  have hSplitEval :
                      __smtx_model_eval M splitTerm =
                        SmtValue.Numeral (Int.ofNat left.length) := by
                    simpa [splitTerm, hSplit] using
                      eval_smt_str_indexof_re_split_of_seq_reglan
                        M curS (__eo_to_smt r1) (__eo_to_smt arg)
                        ss rv1 rv2 hCurEval hr1Eval hr2Eval
                  have hLenEval :
                      __smtx_model_eval M (SmtTerm.str_len curS) =
                        SmtValue.Numeral
                          (native_seq_len (native_unpack_seq ss)) :=
                    eval_smt_strlen_of_seq M curS ss hCurEval
                  have hNegEval :
                      __smtx_model_eval M
                          (SmtTerm.neg (SmtTerm.str_len curS) splitTerm) =
                        SmtValue.Numeral
                          (native_seq_len (native_unpack_seq ss) -
                            Int.ofNat left.length) :=
                    eval_smt_neg_of_ints M (SmtTerm.str_len curS) splitTerm
                      (native_seq_len (native_unpack_seq ss))
                      (Int.ofNat left.length) hLenEval hSplitEval
                  have hSuffixEval :
                      __smtx_model_eval M suffixSmt = SmtValue.Seq rightSeq := by
                    simpa [suffixSmt, rightSeq] using
                      eval_smt_substr_of_seq_ints M curS splitTerm
                        (SmtTerm.neg (SmtTerm.str_len curS) splitTerm)
                        ss (Int.ofNat left.length)
                        (native_seq_len (native_unpack_seq ss) -
                          Int.ofNat left.length)
                        hCurEval hSplitEval hNegEval
                  have hSplitTy :
                      __smtx_typeof splitTerm = SmtType.Int :=
                    smtx_typeof_smt_str_indexof_re_split_of_seq_reglan
                      curS (__eo_to_smt r1) (__eo_to_smt arg)
                      hCurTy hRArgs.1 hRArgs.2
                  have hLenTy :
                      __smtx_typeof (SmtTerm.str_len curS) = SmtType.Int :=
                    smtx_typeof_smt_strlen_of_seq_char curS hCurTy
                  have hNegTy :
                      __smtx_typeof
                          (SmtTerm.neg (SmtTerm.str_len curS) splitTerm) =
                        SmtType.Int :=
                    smtx_typeof_smt_neg_of_ints (SmtTerm.str_len curS)
                      splitTerm hLenTy hSplitTy
                  have hSuffixTy :
                      __smtx_typeof suffixSmt =
                        SmtType.Seq SmtType.Char := by
                    simpa [suffixSmt] using
                      smtx_typeof_smt_substr_of_seq_char curS splitTerm
                        (SmtTerm.neg (SmtTerm.str_len curS) splitTerm)
                        hCurTy hSplitTy hNegTy
                  have hSeqTy :=
                    seq_value_type_of_eval_seq M hM curS ss hCurTy hCurEval
                  have hRightUnpack :
                      native_unpack_string rightSeq = right := by
                    simpa [rightSeq] using
                      native_unpack_string_substr_right ss left right hSeqTy
                        hAppend.symm
                  have hRightMemSeq :
                      native_str_in_re (native_unpack_string rightSeq) rv2 =
                        true := by
                    simpa [hRightUnpack] using hRightMem
                  have hComponent' :
                      ∀ j : Nat,
                        __eo_to_smt
                            (mkAtReUnfoldPosComponent t ro
                              (idxTerm (idx + 1 + j))) =
                          __eo_to_smt_re_unfold_pos_component suffixSmt
                            (__eo_to_smt arg) j := by
                    intro j
                    have h := hComponent (j + 1)
                    have hNat : idx + (j + 1) = idx + 1 + j := by omega
                    simpa [hNat, __eo_to_smt_re_unfold_pos_component,
                      suffixSmt, splitTerm] using h
                  have hTailRecNe :
                      __re_unfold_pos_concat_rec t arg ro (idxTerm (idx + 1)) ≠
                        Term.Stuck := by
                    intro hTail
                    apply hRecNe
                    cases r1 <;>
                      simp [__re_unfold_pos_concat_rec, idxTerm, __eo_add,
                        SmtEval.native_zplus, hTail, __pair_first,
                        __pair_second, __eo_mk_apply]
                  rcases ihArg (idx + 1) suffixSmt rightSeq rv2 hComponent'
                      hSuffixTy hSuffixEval hRArgs.2 hr2Eval hRightMemSeq
                      hTailRecNe with
                    ⟨tailFirst, tailGuard, hTailEq, hTailFirstEval,
                      hTailFirstTy, hTailGuardEval, hTailGuardBool⟩
                  have hRightSeqTy :=
                    seq_value_type_of_eval_seq M hM suffixSmt rightSeq
                      hSuffixTy hSuffixEval
                  have hRightSeqEq :
                      rightSeq = native_pack_string right := by
                    calc
                      rightSeq =
                          native_pack_string (native_unpack_string rightSeq) :=
                        (native_pack_string_unpack_string_of_typeof_seq_char
                          rightSeq hRightSeqTy).symm
                      _ = native_pack_string right := by rw [hRightUnpack]
                  have hssEq :
                      ss = native_pack_string (left ++ right) := by
                    calc
                      ss = native_pack_string (native_unpack_string ss) :=
                        (native_pack_string_unpack_string_of_typeof_seq_char
                          ss hSeqTy).symm
                      _ = native_pack_string (left ++ right) := by
                        rw [← hAppend]
                  cases r1 with
                  | Apply rf rx =>
                      cases rf with
                      | UOp op2 =>
                          cases op2 with
                          | str_to_re =>
                              cases rx with
                              | String lit =>
                                  change __smtx_model_eval M
                                      (SmtTerm.str_to_re (SmtTerm.String lit)) =
                                    SmtValue.RegLan rv1 at hr1Eval
                                  simp [__smtx_model_eval,
                                    __smtx_model_eval_str_to_re] at hr1Eval
                                  cases hr1Eval
                                  have hLeftEq : left = lit :=
                                    native_str_in_re_str_to_re_true_eq hLeftMem
                                  have hTailFirstNe :
                                      tailFirst ≠ Term.Stuck :=
                                    term_ne_stuck_of_smt_type_seq_char
                                      tailFirst hTailFirstTy
                                  have hTailGuardNe :
                                      tailGuard ≠ Term.Stuck :=
                                    term_ne_stuck_of_has_smt_translation tailGuard
                                      (RuleProofs.eo_has_smt_translation_of_has_bool_type
                                        tailGuard hTailGuardBool)
                                  let first :=
                                    mkStrConcat (Term.String lit) tailFirst
                                  have hFirstNe : first ≠ Term.Stuck := by
                                    simp [first, mkStrConcat]
                                  have hPairFunNe :
                                      __eo_mk_apply
                                          (Term.UOp UserOp._at__at_pair) first ≠
                                        Term.Stuck :=
                                    eo_mk_apply_ne_stuck_of_ne_stuck
                                      (Term.UOp UserOp._at__at_pair) first
                                      (by simp) hFirstNe
                                  have hFinalNe :
                                      __eo_mk_apply
                                          (__eo_mk_apply
                                            (Term.UOp UserOp._at__at_pair)
                                            first) tailGuard ≠ Term.Stuck :=
                                    eo_mk_apply_ne_stuck_of_ne_stuck
                                      (__eo_mk_apply
                                        (Term.UOp UserOp._at__at_pair) first)
                                      tailGuard hPairFunNe hTailGuardNe
                                  refine ⟨first, tailGuard, ?_, ?_, ?_,
                                    hTailGuardEval, hTailGuardBool⟩
                                  · change __re_unfold_pos_concat_rec t
                                      (Term.Apply
                                        (Term.Apply
                                          (Term.UOp UserOp.re_concat)
                                          (Term.Apply
                                            (Term.UOp UserOp.str_to_re)
                                            (Term.String lit))) arg) ro
                                      (idxTerm idx) =
                                      Term.Apply
                                        (Term.Apply
                                          (Term.UOp UserOp._at__at_pair) first)
                                        tailGuard
                                    rw [show
                                      __eo_add (idxTerm idx) (Term.Numeral 1) =
                                        idxTerm (idx + 1) by
                                          simp [idxTerm, __eo_add,
                                            SmtEval.native_zplus]]
                                    rw [hTailEq]
                                    simp [__re_unfold_pos_concat_rec,
                                      __pair_first, __pair_second, first,
                                      mkStrConcat]
                                    exact
                                      eo_mk_apply_eq_apply_of_ne_stuck _ _
                                        hFinalNe
                                  · have hLitEval :
                                        __smtx_model_eval M
                                            (__eo_to_smt (Term.String lit)) =
                                          SmtValue.Seq
                                            (native_pack_string lit) := by
                                      simp [__smtx_model_eval]
                                    have hConcatEvalFirst :=
                                      eval_str_concat_of_seq M
                                        (Term.String lit) tailFirst
                                        (native_pack_string lit) rightSeq
                                        hLitEval hTailFirstEval
                                    change __smtx_model_eval M
                                        (__eo_to_smt first) = SmtValue.Seq ss
                                    rw [hConcatEvalFirst]
                                    congr
                                    rw [hssEq, hRightSeqEq, hLeftEq]
                                    simp [native_pack_string,
                                      native_unpack_pack_seq, List.map_append]
                                  · exact smtx_typeof_str_concat_of_seq_char
                                      (Term.String lit) tailFirst
                                      (by
                                        change __smtx_typeof
                                            (SmtTerm.String lit) =
                                          SmtType.Seq SmtType.Char
                                        simp [__smtx_typeof])
                                      hTailFirstTy
                              | _ =>
                                  -- A non-string argument to str.to_re is handled by
                                  -- the generic concat branch below.
                                  have hComponent0 := hComponent 0
                                  let comp :=
                                    mkAtReUnfoldPosComponent t ro
                                      (idxTerm idx)
                                  let leftSeq : SmtSeq :=
                                    native_pack_seq
                                      (__smtx_elem_typeof_seq_value ss)
                                      (native_seq_extract
                                        (native_unpack_seq ss) 0
                                        (Int.ofNat left.length))
                                  have hLeftUnpack :
                                      native_unpack_string leftSeq = left := by
                                    simpa [leftSeq] using
                                      native_unpack_string_substr_left ss left
                                        right hSeqTy hAppend.symm
                                  have hCompEval :
                                      __smtx_model_eval M (__eo_to_smt comp) =
                                        SmtValue.Seq leftSeq := by
                                    rw [hComponent0]
                                    simpa [comp, leftSeq, splitTerm,
                                      __eo_to_smt_re_unfold_pos_component] using
                                      eval_smt_substr_of_seq_ints M curS
                                        (SmtTerm.Numeral 0) splitTerm ss 0
                                        (Int.ofNat left.length) hCurEval
                                        (by simp [__smtx_model_eval])
                                        hSplitEval
                                  have hCompTy :
                                      __smtx_typeof (__eo_to_smt comp) =
                                        SmtType.Seq SmtType.Char := by
                                    rw [hComponent0]
                                    simpa [comp, splitTerm,
                                      __eo_to_smt_re_unfold_pos_component] using
                                      smtx_typeof_smt_substr_of_seq_char curS
                                        (SmtTerm.Numeral 0) splitTerm hCurTy
                                        (by simp [__smtx_typeof])
                                        hSplitTy
                                  have hLeftInEval :
                                      __smtx_model_eval M
                                          (__eo_to_smt (mkStrInRe comp
                                            (Term.Apply (Term.UOp UserOp.str_to_re)
                                              rx))) =
                                        SmtValue.Boolean true := by
                                    have hRaw :=
                                      eval_str_in_re_of_seq_reglan M comp
                                        (Term.Apply
                                          (Term.UOp UserOp.str_to_re) rx)
                                        leftSeq rv1 hCompEval hr1Eval
                                    simpa [hLeftUnpack] using hRaw.trans
                                      (by simp [hLeftMem])
                                  have hLeftInBool :
                                      RuleProofs.eo_has_bool_type
                                        (mkStrInRe comp
                                          (Term.Apply
                                            (Term.UOp UserOp.str_to_re) rx)) :=
                                    smtx_typeof_str_in_re_of_seq_reglan comp
                                      (Term.Apply (Term.UOp UserOp.str_to_re) rx)
                                      hCompTy hRArgs.1
                                  let first := mkStrConcat comp tailFirst
                                  let guard :=
                                    mkAnd
                                      (mkStrInRe comp
                                        (Term.Apply
                                          (Term.UOp UserOp.str_to_re) rx))
                                      tailGuard
                                  have hGuardBool :
                                      RuleProofs.eo_has_bool_type guard := by
                                    exact RuleProofs.eo_has_bool_type_and_of_bool_args
                                      _ _ hLeftInBool hTailGuardBool
                                  have hGuardEval :
                                      __smtx_model_eval M (__eo_to_smt guard) =
                                        SmtValue.Boolean true := by
                                    change __smtx_model_eval M
                                        (SmtTerm.and
                                          (__eo_to_smt
                                            (mkStrInRe comp
                                              (Term.Apply
                                                (Term.UOp UserOp.str_to_re) rx)))
                                          (__eo_to_smt tailGuard)) =
                                      SmtValue.Boolean true
                                    simp [__smtx_model_eval,
                                      __smtx_model_eval_and, hLeftInEval,
                                      hTailGuardEval, SmtEval.native_and]
                                  refine ⟨first, guard, ?_, ?_, ?_,
                                    hGuardEval, hGuardBool⟩
                                  · exact False.elim (by
                                      simpa [__re_unfold_pos_concat_rec] using
                                        hRecNe)
                                  · exact False.elim (by
                                      simpa [__re_unfold_pos_concat_rec] using
                                        hRecNe)
                                  · exact False.elim (by
                                      simpa [__re_unfold_pos_concat_rec] using
                                        hRecNe)
                          | _ =>
                              exact False.elim (by
                                simpa [__re_unfold_pos_concat_rec] using hRecNe)
                      | _ =>
                          exact False.elim (by
                            simpa [__re_unfold_pos_concat_rec] using hRecNe)
                  | _ =>
                      exact False.elim (by
                        simpa [__re_unfold_pos_concat_rec] using hRecNe)
              | _ =>
                  exact False.elim (by
                    simpa [__re_unfold_pos_concat_rec] using hRecNe)
          | _ =>
              exact False.elim (by
                simpa [__re_unfold_pos_concat_rec] using hRecNe)
      | _ =>
          exact False.elim (by
            simpa [__re_unfold_pos_concat_rec] using hRecNe)
-/

theorem re_unfold_pos_nonstuck_shape (p : Term) :
    __eo_prog_re_unfold_pos (Proof.pf p) ≠ Term.Stuck ->
    ∃ t r,
      p = mkStrInRe t r ∧
      __eo_prog_re_unfold_pos (Proof.pf p) = __mk_re_unfold_pos t r := by
  intro h
  cases p with
  | Apply f r =>
      cases f with
      | Apply op t =>
          cases op with
          | UOp op =>
              cases op <;> try (simp [__eo_prog_re_unfold_pos] at h)
              case str_in_re =>
                exact ⟨t, r, rfl, rfl⟩
          | _ => simp [__eo_prog_re_unfold_pos] at h
      | _ => simp [__eo_prog_re_unfold_pos] at h
  | _ => simp [__eo_prog_re_unfold_pos] at h

theorem re_unfold_pos_concat_rec_ne_of_mk_ne (t r1 r2 : Term) :
    __mk_re_unfold_pos t (mkReConcat r1 r2) ≠ Term.Stuck ->
    __re_unfold_pos_concat_rec t (mkReConcat r1 r2)
      (mkReConcat r1 r2) (Term.Numeral 0) ≠ Term.Stuck := by
  intro hMk hRec
  apply hMk
  change __mk_re_unfold_pos t
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) r1) r2) =
    Term.Stuck
  cases t <;>
    simp [__mk_re_unfold_pos, mkReConcat, hRec, __pair_first,
      __pair_second, __eo_eq, __eo_ite, __eo_mk_apply, native_ite,
      native_teq]

theorem re_unfold_pos_star_rec_ne_of_mk_ne (t r : Term) :
    __mk_re_unfold_pos t (mkReMult r) ≠ Term.Stuck ->
    __re_unfold_pos_concat_rec t (reUnfoldPosStarFactor r)
      (reUnfoldPosStarFactor r) (Term.Numeral 0) ≠ Term.Stuck := by
  intro hMk hRec
  apply hMk
  change __mk_re_unfold_pos t (Term.Apply (Term.UOp UserOp.re_mult) r) =
    Term.Stuck
  cases t <;> cases r <;>
    simp [__mk_re_unfold_pos, mkReMult, reUnfoldPosStarFactor,
      mkReConcat, mkReDiff, mkStrToRe, hRec, __mk_re_unfold_pos_star,
      native_ite, native_teq]

theorem re_unfold_pos_star_factor_rec_eq (t r : Term)
    (htNe : t ≠ Term.Stuck) :
    __re_unfold_pos_concat_rec t (reUnfoldPosStarFactor r)
        (reUnfoldPosStarFactor r) (Term.Numeral 0) =
      Term.Apply
        (Term.Apply (Term.UOp UserOp._at__at_pair)
          (reUnfoldPosStarFirst t r))
        (reUnfoldPosStarGuard t r) := by
  cases t <;> try exact False.elim (htNe rfl)
  all_goals
    simp [reUnfoldPosStarFactor, reUnfoldPosStarFirst,
      reUnfoldPosStarGuard, reUnfoldPosStarComponent,
      __re_unfold_pos_concat_rec, idxTerm, __eo_add,
      SmtEval.native_zplus, __pair_first, __pair_second, __eo_mk_apply,
      mkReConcat, mkReDiff, mkReMult, mkStrToRe, mkStrConcat, mkStrInRe,
      mkAnd]

theorem re_unfold_pos_star_eq_formula_of_ne_stuck (t r : Term) :
    __mk_re_unfold_pos t (mkReMult r) ≠ Term.Stuck ->
    __mk_re_unfold_pos t (mkReMult r) =
      reUnfoldPosStarFormula t r := by
  intro hMkNe
  have htNe : t ≠ Term.Stuck := by
    intro ht
    apply hMkNe
    subst t
    simp [__mk_re_unfold_pos]
  have hRecEq := re_unfold_pos_star_factor_rec_eq t r htNe
  cases t <;> try exact False.elim (htNe rfl)
  all_goals
    cases r <;>
      first
      | exact False.elim (by
          apply hMkNe
          simp [__mk_re_unfold_pos, mkReMult, hRecEq,
            __mk_re_unfold_pos_star])
      | simp [__mk_re_unfold_pos, mkReMult, hRecEq,
          __mk_re_unfold_pos_star, reUnfoldPosStarFormula,
          reUnfoldPosStarFirst, reUnfoldPosStarGuard,
          reUnfoldPosStarComponent, mkOr, mkEq, mkStrInRe, mkAnd,
          mkStrConcat]

theorem smtx_typeof_re_unfold_pos_star_factor_of_reglan (r : Term)
    (hr : __smtx_typeof (__eo_to_smt r) = SmtType.RegLan) :
    __smtx_typeof (__eo_to_smt (reUnfoldPosStarFactor r)) =
      SmtType.RegLan := by
  have hEmpty :
      __smtx_typeof (__eo_to_smt (Term.String [])) =
        SmtType.Seq SmtType.Char :=
    smtx_typeof_empty_string
  have hEps :
      __smtx_typeof (__eo_to_smt (mkStrToRe (Term.String []))) =
        SmtType.RegLan :=
    smtx_typeof_str_to_re_of_seq_char (Term.String []) hEmpty
  have hDiff :
      __smtx_typeof (__eo_to_smt (mkReDiff r (mkStrToRe (Term.String [])))) =
        SmtType.RegLan :=
    smtx_typeof_re_diff_of_reglan r (mkStrToRe (Term.String [])) hr hEps
  have hStar :
      __smtx_typeof (__eo_to_smt (mkReMult r)) = SmtType.RegLan :=
    smtx_typeof_re_mult_of_reglan r hr
  have hTail :
      __smtx_typeof
          (__eo_to_smt
            (mkReConcat (mkReDiff r (mkStrToRe (Term.String [])))
              (mkStrToRe (Term.String [])))) =
        SmtType.RegLan :=
    smtx_typeof_re_concat_of_reglan
      (mkReDiff r (mkStrToRe (Term.String [])))
      (mkStrToRe (Term.String [])) hDiff hEps
  have hMiddle :
      __smtx_typeof
          (__eo_to_smt
            (mkReConcat (mkReMult r)
              (mkReConcat (mkReDiff r (mkStrToRe (Term.String [])))
                (mkStrToRe (Term.String []))))) =
        SmtType.RegLan :=
    smtx_typeof_re_concat_of_reglan (mkReMult r)
      (mkReConcat (mkReDiff r (mkStrToRe (Term.String [])))
        (mkStrToRe (Term.String []))) hStar hTail
  exact
    smtx_typeof_re_concat_of_reglan
      (mkReDiff r (mkStrToRe (Term.String [])))
      (mkReConcat (mkReMult r)
        (mkReConcat (mkReDiff r (mkStrToRe (Term.String [])))
          (mkStrToRe (Term.String [])))) hDiff hMiddle

theorem re_unfold_pos_concat_eval_true_and_bool
    (M : SmtModel) (hM : model_total_typed M)
    (t r1 r2 : Term)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1Ty : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan)
    (hPrem : eo_interprets M (mkStrInRe t (mkReConcat r1 r2)) true)
    (hMkNe : __mk_re_unfold_pos t (mkReConcat r1 r2) ≠ Term.Stuck) :
    __smtx_model_eval M
        (__eo_to_smt (__mk_re_unfold_pos t (mkReConcat r1 r2))) =
      SmtValue.Boolean true ∧
    RuleProofs.eo_has_bool_type
      (__mk_re_unfold_pos t (mkReConcat r1 r2)) := by
  let re := mkReConcat r1 r2
  rcases str_in_re_re_concat_native_true M hM t r1 r2 htTy hr1Ty hr2Ty hPrem with
    ⟨ss, rv1, rv2, htEval, hr1Eval, hr2Eval, hMem⟩
  have hReTy : __smtx_typeof (__eo_to_smt re) = SmtType.RegLan := by
    simpa [re] using smtx_typeof_re_concat_of_reglan r1 r2 hr1Ty hr2Ty
  have hReEval :
      __smtx_model_eval M (__eo_to_smt re) =
        SmtValue.RegLan (native_re_concat rv1 rv2) := by
    simpa [re] using eval_re_concat_of_reglan M r1 r2 rv1 rv2 hr1Eval hr2Eval
  have hRecNe :
      __re_unfold_pos_concat_rec t re re (Term.Numeral 0) ≠ Term.Stuck := by
    simpa [re] using re_unfold_pos_concat_rec_ne_of_mk_ne t r1 r2 hMkNe
  rcases re_unfold_pos_concat_rec_eval_true M hM t re re 0
      (__eo_to_smt t) ss (native_re_concat rv1 rv2)
      (by simpa [re] using re_unfold_pos_initial_component t re)
      htTy htEval hReTy hReEval hMem hRecNe with
    ⟨first, guard, hRecEq, hFirstEval, hFirstTy, hGuardEval, hGuardBool⟩
  let eqTerm := mkEq t first
  let andTerm := mkAnd eqTerm guard
  have hEqBool : RuleProofs.eo_has_bool_type eqTerm := by
    have hSame :
        __smtx_typeof (__eo_to_smt t) =
          __smtx_typeof (__eo_to_smt first) := by
      rw [htTy, hFirstTy]
    have hNonNone :
        __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
      rw [htTy]
      simp
    simpa [eqTerm, mkEq] using
      RuleProofs.eo_has_bool_type_eq_of_same_smt_type t first hSame hNonNone
  have hEqEval :
      __smtx_model_eval M (__eo_to_smt eqTerm) = SmtValue.Boolean true := by
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt t) (__eo_to_smt first)) =
      SmtValue.Boolean true
    simp [__smtx_model_eval, __smtx_model_eval_eq, htEval, hFirstEval,
      native_veq]
  have hAndBool : RuleProofs.eo_has_bool_type andTerm := by
    simpa [andTerm, mkAnd] using
      RuleProofs.eo_has_bool_type_and_of_bool_args eqTerm guard
        hEqBool hGuardBool
  have hAndEval :
      __smtx_model_eval M (__eo_to_smt andTerm) = SmtValue.Boolean true := by
    change __smtx_model_eval M
        (SmtTerm.and (__eo_to_smt eqTerm) (__eo_to_smt guard)) =
      SmtValue.Boolean true
    simp [andTerm, mkAnd, __smtx_model_eval, __smtx_model_eval_and,
      hEqEval, hGuardEval, SmtEval.native_and]
  have hFirstNe : first ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq_char first hFirstTy
  have hEqAppNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) first ≠
        Term.Stuck :=
    eo_mk_apply_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) first (by simp) hFirstNe
  have hEqAppEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) first = eqTerm := by
    simpa [eqTerm, mkEq] using
      eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqAppNe
  have hEqTermNe : eqTerm ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation eqTerm
      (RuleProofs.eo_has_smt_translation_of_has_bool_type eqTerm hEqBool)
  have hGuardNe0 : guard ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation guard
      (RuleProofs.eo_has_smt_translation_of_has_bool_type guard hGuardBool)
  have hAndFunNe :
      __eo_mk_apply (Term.UOp UserOp.and) eqTerm ≠ Term.Stuck :=
    eo_mk_apply_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.and) eqTerm (by simp) hEqTermNe
  have hAndFunEq :
      __eo_mk_apply (Term.UOp UserOp.and) eqTerm =
        Term.Apply (Term.UOp UserOp.and) eqTerm :=
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hAndFunNe
  have hAndAppNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.and) eqTerm) guard ≠
        Term.Stuck :=
    eo_mk_apply_ne_stuck_of_ne_stuck
      (__eo_mk_apply (Term.UOp UserOp.and) eqTerm) guard
      hAndFunNe hGuardNe0
  have hAndAppEq :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.and) eqTerm) guard =
        andTerm := by
    have h := eo_mk_apply_eq_apply_of_ne_stuck _ _ hAndAppNe
    rw [hAndFunEq] at h
    simpa [andTerm, mkAnd] using h
  have hRecEq0 :
      __re_unfold_pos_concat_rec t (mkReConcat r1 r2)
          (mkReConcat r1 r2) (Term.Numeral 0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) first) guard := by
    simpa [re, idxTerm] using hRecEq
  have hMkEq :
      __mk_re_unfold_pos t (mkReConcat r1 r2) =
        __eo_ite (__eo_eq guard (Term.Boolean true)) eqTerm andTerm := by
    cases t <;>
      simp_all [__mk_re_unfold_pos, mkReConcat, re, hRecEq0, __pair_first,
        __pair_second, hEqAppEq, hAndAppEq, eqTerm, andTerm, mkEq, mkAnd]
  by_cases hGuardSyn : guard = Term.Boolean true
  · subst guard
    have hFinal :
        __mk_re_unfold_pos t (mkReConcat r1 r2) = eqTerm := by
      rw [hMkEq]
      simp [__eo_eq, __eo_ite, native_teq, native_ite]
    constructor
    · simpa [hFinal] using hEqEval
    · simpa [hFinal] using hEqBool
  · have hGuardNe : guard ≠ Term.Stuck := hGuardNe0
    have hFinal :
        __mk_re_unfold_pos t (mkReConcat r1 r2) = andTerm := by
      rw [hMkEq]
      cases guard with
      | Boolean b =>
          cases b
          · simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
          · exact False.elim (hGuardSyn rfl)
      | Stuck =>
          exact False.elim (hGuardNe rfl)
      | UOp op =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | UOp1 op a =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | UOp2 op a b =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | UOp3 op a b c =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | __eo_List =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | __eo_List_nil =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | __eo_List_cons =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Bool =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Numeral n =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Rational q =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | String s =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Binary w n =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | «Type» =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Apply f a =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | FunType =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Var n T =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DatatypeType s d =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DatatypeTypeRef s =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DtcAppType a b =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DtCons s d i =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DtSel s d i j =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | USort n =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | UConst n ty =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
    constructor
    · simpa [hFinal] using hAndEval
    · simpa [hFinal] using hAndBool

theorem re_unfold_pos_concat_has_bool_type
    (t r1 r2 : Term)
    (htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char)
    (hr1Ty : __smtx_typeof (__eo_to_smt r1) = SmtType.RegLan)
    (hr2Ty : __smtx_typeof (__eo_to_smt r2) = SmtType.RegLan)
    (hMkNe : __mk_re_unfold_pos t (mkReConcat r1 r2) ≠ Term.Stuck) :
    RuleProofs.eo_has_bool_type
      (__mk_re_unfold_pos t (mkReConcat r1 r2)) := by
  let re := mkReConcat r1 r2
  have hReTy : __smtx_typeof (__eo_to_smt re) = SmtType.RegLan := by
    simpa [re] using smtx_typeof_re_concat_of_reglan r1 r2 hr1Ty hr2Ty
  have hRecNe :
      __re_unfold_pos_concat_rec t re re (Term.Numeral 0) ≠ Term.Stuck := by
    simpa [re] using re_unfold_pos_concat_rec_ne_of_mk_ne t r1 r2 hMkNe
  rcases re_unfold_pos_concat_rec_types t re re 0 (__eo_to_smt t)
      (by simpa [re] using re_unfold_pos_initial_component t re)
      htTy hReTy hRecNe with
    ⟨first, guard, hRecEq, hFirstTy, hGuardBool⟩
  let eqTerm := mkEq t first
  let andTerm := mkAnd eqTerm guard
  have hEqBool : RuleProofs.eo_has_bool_type eqTerm := by
    have hSame :
        __smtx_typeof (__eo_to_smt t) =
          __smtx_typeof (__eo_to_smt first) := by
      rw [htTy, hFirstTy]
    have hNonNone :
        __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
      rw [htTy]
      simp
    simpa [eqTerm, mkEq] using
      RuleProofs.eo_has_bool_type_eq_of_same_smt_type t first hSame hNonNone
  have hAndBool : RuleProofs.eo_has_bool_type andTerm := by
    simpa [andTerm, mkAnd] using
      RuleProofs.eo_has_bool_type_and_of_bool_args eqTerm guard
        hEqBool hGuardBool
  have hFirstNe : first ≠ Term.Stuck :=
    term_ne_stuck_of_smt_type_seq_char first hFirstTy
  have hEqAppNe :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) first ≠
        Term.Stuck :=
    eo_mk_apply_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) first (by simp) hFirstNe
  have hEqAppEq :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) first = eqTerm := by
    simpa [eqTerm, mkEq] using
      eo_mk_apply_eq_apply_of_ne_stuck _ _ hEqAppNe
  have hEqTermNe : eqTerm ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation eqTerm
      (RuleProofs.eo_has_smt_translation_of_has_bool_type eqTerm hEqBool)
  have hGuardNe0 : guard ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation guard
      (RuleProofs.eo_has_smt_translation_of_has_bool_type guard hGuardBool)
  have hAndFunNe :
      __eo_mk_apply (Term.UOp UserOp.and) eqTerm ≠ Term.Stuck :=
    eo_mk_apply_ne_stuck_of_ne_stuck
      (Term.UOp UserOp.and) eqTerm (by simp) hEqTermNe
  have hAndFunEq :
      __eo_mk_apply (Term.UOp UserOp.and) eqTerm =
        Term.Apply (Term.UOp UserOp.and) eqTerm :=
    eo_mk_apply_eq_apply_of_ne_stuck _ _ hAndFunNe
  have hAndAppNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.and) eqTerm) guard ≠
        Term.Stuck :=
    eo_mk_apply_ne_stuck_of_ne_stuck
      (__eo_mk_apply (Term.UOp UserOp.and) eqTerm) guard
      hAndFunNe hGuardNe0
  have hAndAppEq :
      __eo_mk_apply (__eo_mk_apply (Term.UOp UserOp.and) eqTerm) guard =
        andTerm := by
    have h := eo_mk_apply_eq_apply_of_ne_stuck _ _ hAndAppNe
    rw [hAndFunEq] at h
    simpa [andTerm, mkAnd] using h
  have hRecEq0 :
      __re_unfold_pos_concat_rec t (mkReConcat r1 r2)
          (mkReConcat r1 r2) (Term.Numeral 0) =
        Term.Apply (Term.Apply (Term.UOp UserOp._at__at_pair) first) guard := by
    simpa [re, idxTerm] using hRecEq
  have hMkEq :
      __mk_re_unfold_pos t (mkReConcat r1 r2) =
        __eo_ite (__eo_eq guard (Term.Boolean true)) eqTerm andTerm := by
    cases t <;>
      simp_all [__mk_re_unfold_pos, mkReConcat, re, hRecEq0, __pair_first,
        __pair_second, hEqAppEq, hAndAppEq, eqTerm, andTerm, mkEq, mkAnd]
  by_cases hGuardSyn : guard = Term.Boolean true
  · subst guard
    have hFinal :
        __mk_re_unfold_pos t (mkReConcat r1 r2) = eqTerm := by
      rw [hMkEq]
      simp [__eo_eq, __eo_ite, native_teq, native_ite]
    simpa [hFinal] using hEqBool
  · have hGuardNe : guard ≠ Term.Stuck := hGuardNe0
    have hFinal :
        __mk_re_unfold_pos t (mkReConcat r1 r2) = andTerm := by
      rw [hMkEq]
      cases guard with
      | Boolean b =>
          cases b
          · simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
          · exact False.elim (hGuardSyn rfl)
      | Stuck =>
          exact False.elim (hGuardNe rfl)
      | UOp op =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | UOp1 op a =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | UOp2 op a b =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | UOp3 op a b c =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | __eo_List =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | __eo_List_nil =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | __eo_List_cons =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Bool =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Numeral n =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Rational q =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | String s =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Binary w n =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | «Type» =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Apply f a =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | FunType =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | Var n T =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DatatypeType s d =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DatatypeTypeRef s =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DtcAppType a b =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DtCons s d i =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | DtSel s d i j =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | USort n =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
      | UConst n ty =>
          simp [__eo_eq, __eo_ite, native_teq, native_ite, andTerm, mkAnd]
    simpa [hFinal] using hAndBool

end ReUnfoldPosSupport
end RuleProofs

theorem cmd_step_re_unfold_pos_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.re_unfold_pos args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.re_unfold_pos args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.re_unfold_pos args premises) :=
by
  sorry
