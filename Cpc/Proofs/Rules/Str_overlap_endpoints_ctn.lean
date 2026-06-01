import Cpc.Proofs.RuleSupport.StrInReEvalSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace RuleProofs

private theorem native_seq_prefix_eq_append_drop
    (pat xs : List SmtValue) :
    native_seq_prefix_eq pat xs = true ->
      pat ++ xs.drop pat.length = xs := by
  induction pat generalizing xs with
  | nil =>
      intro _h
      simp
  | cons p ps ih =>
      cases xs with
      | nil =>
          intro h
          simp [native_seq_prefix_eq] at h
      | cons x xs =>
          intro h
          have hParts : p = x ∧ native_seq_prefix_eq ps xs = true := by
            simpa [native_seq_prefix_eq, native_veq] using h
          rcases hParts with ⟨rfl, hTail⟩
          simpa using ih xs hTail

private theorem native_seq_prefix_eq_append
    (pat rest : List SmtValue) :
    native_seq_prefix_eq pat (pat ++ rest) = true := by
  induction pat with
  | nil =>
      rfl
  | cons p ps ih =>
      simp [native_seq_prefix_eq, native_veq, ih]

private theorem native_seq_indexof_rec_exists_of_append
    (pat pre suf xs : List SmtValue) :
    xs = pre ++ pat ++ suf ->
    ∀ j fuel, pre.length + 1 ≤ fuel ->
      0 ≤ native_seq_indexof_rec xs pat j fuel := by
  intro hxs
  induction pre generalizing xs with
  | nil =>
      intro j fuel hfuel
      subst xs
      cases fuel with
      | zero =>
          omega
      | succ fuel =>
          simp only [List.nil_append]
          unfold native_seq_indexof_rec
          rw [if_pos (native_seq_prefix_eq_append pat suf)]
          exact Int.natCast_nonneg j
  | cons a pre ih =>
      intro j fuel hfuel
      subst xs
      cases fuel with
      | zero =>
          omega
      | succ fuel =>
          unfold native_seq_indexof_rec
          by_cases hp :
              native_seq_prefix_eq pat (a :: pre ++ pat ++ suf) = true
          · rw [if_pos (by simpa using hp)]
            exact Int.natCast_nonneg j
          · rw [if_neg (by simpa using hp)]
            have hfuel' : pre.length + 1 ≤ fuel := by
              exact Nat.succ_le_succ_iff.mp
                (by simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hfuel)
            exact ih (pre ++ pat ++ suf) rfl (j + 1) fuel hfuel'

private theorem native_seq_contains_of_append
    (pre pat suf : List SmtValue) :
    native_seq_contains (pre ++ pat ++ suf) pat = true := by
  unfold native_seq_contains native_seq_indexof
  rw [if_neg (by decide : ¬ ((0 : native_Int) < 0))]
  have hBounds :
      Int.toNat (0 : native_Int) + pat.length ≤
        (pre ++ pat ++ suf).length := by
    simp
    omega
  rw [dif_pos hBounds]
  simp only [Int.toNat_zero, List.drop_zero, Nat.zero_add]
  have hNonneg :
      0 ≤ native_seq_indexof_rec (pre ++ pat ++ suf) pat 0
        ((pre ++ pat ++ suf).length - pat.length + 1) := by
    apply native_seq_indexof_rec_exists_of_append pat pre suf
      (pre ++ pat ++ suf) rfl
    simp
    omega
  simpa [List.append_assoc] using hNonneg

private theorem native_seq_indexof_rec_decomp
    (xs pat : List SmtValue) :
    (i fuel j : Nat) ->
      native_seq_indexof_rec xs pat i fuel = Int.ofNat j ->
      i ≤ j ∧
        ∃ before after : List SmtValue,
          xs = before ++ pat ++ after ∧ before.length = j - i
  | i, 0, j, h => by
      simp [native_seq_indexof_rec] at h
  | i, fuel + 1, j, h => by
      unfold native_seq_indexof_rec at h
      by_cases hPrefix : native_seq_prefix_eq pat xs = true
      · rw [if_pos hPrefix] at h
        have hji : j = i := Int.ofNat.inj h.symm
        subst j
        constructor
        · exact Nat.le_refl _
        · refine ⟨[], xs.drop pat.length, ?_, by simp⟩
          exact (native_seq_prefix_eq_append_drop pat xs hPrefix).symm
      · rw [if_neg hPrefix] at h
        cases xs with
        | nil =>
            simp at h
        | cons x xs =>
            rcases native_seq_indexof_rec_decomp xs pat (i + 1) fuel j h with
              ⟨hLe, before, after, hXs, hBeforeLen⟩
            constructor
            · omega
            · refine ⟨x :: before, after, ?_, ?_⟩
              · simp [hXs, List.append_assoc]
              · simp [hBeforeLen]
                omega

private theorem native_seq_contains_exists
    (xs pat : List SmtValue) :
    native_seq_contains xs pat = true ->
      ∃ before after : List SmtValue, xs = before ++ pat ++ after := by
  intro h
  unfold native_seq_contains native_seq_indexof at h
  rw [if_neg (by decide : ¬ ((0 : native_Int) < 0))] at h
  by_cases hBounds : Int.toNat (0 : native_Int) + pat.length ≤ xs.length
  · rw [dif_pos hBounds] at h
    simp only [Int.toNat_zero, Nat.zero_add, List.drop_zero] at h
    have hNonneg :
        0 ≤ native_seq_indexof_rec xs pat 0 (xs.length - pat.length + 1) := by
      simpa using h
    let j :=
      Int.toNat (native_seq_indexof_rec xs pat 0
        (xs.length - pat.length + 1))
    have hCast :
        Int.ofNat j =
          native_seq_indexof_rec xs pat 0 (xs.length - pat.length + 1) :=
      Int.toNat_of_nonneg hNonneg
    have hIdx :
        native_seq_indexof_rec xs pat 0 (xs.length - pat.length + 1) =
          Int.ofNat j := by
      rw [hCast]
    rcases native_seq_indexof_rec_decomp xs pat 0
        (xs.length - pat.length + 1) j hIdx with
      ⟨_hLe, before, after, hXs, _hLen⟩
    exact ⟨before, after, hXs⟩
  · rw [dif_neg hBounds] at h
    simp at h

private def list_prefix_compat {α : Type} (xs ys : List α) : Prop :=
  (∃ rest, ys = xs ++ rest) ∨ (∃ rest, xs = ys ++ rest)

private def list_suffix_compat {α : Type} (xs ys : List α) : Prop :=
  list_prefix_compat xs.reverse ys.reverse

private theorem list_prefix_comparable_of_append_eq {α : Type} :
    (xs ys zs ws : List α) ->
      xs ++ zs = ys ++ ws ->
        list_prefix_compat xs ys
  | [], ys, _zs, _ws, _h => by
      left
      exact ⟨ys, by simp⟩
  | x :: xs, [], _zs, _ws, _h => by
      right
      exact ⟨x :: xs, by simp⟩
  | x :: xs, y :: ys, zs, ws, h => by
      injection h with hHead hTail
      subst y
      rcases list_prefix_comparable_of_append_eq xs ys zs ws hTail with
        ⟨rest, hRest⟩ | ⟨rest, hRest⟩
      · left
        exact ⟨rest, by simp [hRest]⟩
      · right
        exact ⟨rest, by simp [hRest]⟩

private theorem list_prefix_compat_of_common_prefix {α : Type}
    {xs ys zs : List α}
    (hxs : ∃ rest, zs = xs ++ rest)
    (hys : ∃ rest, zs = ys ++ rest) :
    list_prefix_compat xs ys := by
  rcases hxs with ⟨xrest, hxrest⟩
  rcases hys with ⟨yrest, hyrest⟩
  exact list_prefix_comparable_of_append_eq xs ys xrest yrest
    (by simpa [hxrest] using hyrest)

private theorem list_prefix_compat_symm {α : Type}
    {xs ys : List α} :
    list_prefix_compat xs ys -> list_prefix_compat ys xs := by
  intro hCompat
  rcases hCompat with hCompat | hCompat
  · exact Or.inr hCompat
  · exact Or.inl hCompat

private theorem list_suffix_compat_symm {α : Type}
    {xs ys : List α} :
    list_suffix_compat xs ys -> list_suffix_compat ys xs := by
  unfold list_suffix_compat
  exact list_prefix_compat_symm

private theorem list_prefix_compat_of_compat_prefix {α : Type}
    {xs ys zs : List α}
    (hCompat : list_prefix_compat xs zs)
    (hPrefix : ∃ rest, zs = ys ++ rest) :
    list_prefix_compat xs ys := by
  rcases hCompat with ⟨rest, hRest⟩ | ⟨rest, hRest⟩
  · exact list_prefix_compat_of_common_prefix ⟨rest, hRest⟩ hPrefix
  · rcases hPrefix with ⟨ypost, hypost⟩
    right
    exact ⟨ypost ++ rest, by simp [hRest, hypost, List.append_assoc]⟩

private theorem list_suffix_compat_of_compat_suffix {α : Type}
    {xs ys zs : List α}
    (hCompat : list_suffix_compat xs zs)
    (hSuffix : ∃ rest, zs = rest ++ ys) :
    list_suffix_compat xs ys := by
  unfold list_suffix_compat at hCompat ⊢
  apply list_prefix_compat_of_compat_prefix hCompat
  rcases hSuffix with ⟨rest, hrest⟩
  exact ⟨rest.reverse, by simp [hrest, List.reverse_append]⟩

private theorem list_prefix_compat_of_prefix_append_eq {α : Type}
    {xs ys rest tail : List α}
    (hEq : xs ++ rest = ys ++ tail) :
    list_prefix_compat xs ys :=
  list_prefix_comparable_of_append_eq xs ys rest tail hEq

private theorem list_suffix_compat_of_append_suffix {α : Type}
    (pre xs : List α) :
    list_suffix_compat (pre ++ xs) xs := by
  unfold list_suffix_compat
  right
  exact ⟨pre.reverse, by simp [List.reverse_append]⟩

private theorem list_match_after_left_of_no_overlap
    (c1 rest pat d1 : List SmtValue)
    (hLeft :
      ∀ pre suf, c1 = pre ++ suf -> suf ≠ [] ->
        list_prefix_compat suf d1 -> False)
    (hD1Prefix : ∃ tail, pat = d1 ++ tail) :
    (before after : List SmtValue) ->
      c1 ++ rest = before ++ pat ++ after ->
        ∃ before' after', rest = before' ++ pat ++ after'
  | [], after, h => by
      cases c1 with
      | nil =>
          exact ⟨[], after, by simpa using h⟩
      | cons c c1tail =>
          by_cases hPat : pat = []
          · subst pat
            exact ⟨[], rest, by simp⟩
          · have hc1Ne : c :: c1tail ≠ [] := by simp
            have hCompatPat : list_prefix_compat (c :: c1tail) pat := by
              exact list_prefix_compat_of_prefix_append_eq
                (xs := c :: c1tail) (ys := pat) (rest := rest)
                (tail := after) h
            have hCompatD1 : list_prefix_compat (c :: c1tail) d1 :=
              list_prefix_compat_of_compat_prefix hCompatPat hD1Prefix
            exact False.elim
              (hLeft [] (c :: c1tail) (by simp) hc1Ne hCompatD1)
  | b :: before, after, h => by
      cases c1 with
      | nil =>
          exact ⟨b :: before, after, by simpa using h⟩
      | cons c c1tail =>
          injection h with hHead hTail
          subst b
          exact list_match_after_left_of_no_overlap c1tail rest pat d1
            (fun pre suf hSplit hSufNe hCompat =>
              hLeft (c :: pre) suf (by simp [hSplit, List.append_assoc])
                hSufNe hCompat)
            hD1Prefix before after hTail

private theorem list_match_inside_of_no_right_overlap
    (s c2 pat d2 : List SmtValue)
    (hRight :
      ∀ pre suf, c2 = pre ++ suf -> pre ≠ [] ->
        list_suffix_compat pre d2 -> False)
    (hD2Suffix : ∃ init, pat = init ++ d2) :
    (before after : List SmtValue) ->
      s ++ c2 = before ++ pat ++ after ->
        ∃ before' after', s = before' ++ pat ++ after'
  | [], after, h => by
      cases s with
      | nil =>
          by_cases hPat : pat = []
          · subst pat
            exact ⟨[], [], by simp⟩
          · let pre := pat
            have hPreNe : pre ≠ [] := by
              simpa [pre] using hPat
            have hSplit : c2 = pre ++ after := by
              simpa [pre] using h
            have hCompatPat : list_suffix_compat pre d2 := by
              have hCompatSelf : list_suffix_compat pre pat := by
                subst pre
                unfold list_suffix_compat list_prefix_compat
                left
                exact ⟨[], by simp⟩
              exact list_suffix_compat_of_compat_suffix hCompatSelf hD2Suffix
            exact False.elim (hRight pre after hSplit hPreNe hCompatPat)
      | cons x xs =>
          have hCompat : list_prefix_compat (x :: xs) pat :=
            list_prefix_compat_of_prefix_append_eq
              (xs := x :: xs) (ys := pat) (rest := c2) (tail := after) h
          rcases hCompat with ⟨restPat, hPat⟩ | ⟨restS, hS⟩
          · by_cases hRestPat : restPat = []
            · subst restPat
              subst pat
              exact ⟨[], [], by simp⟩
            · have hSplit : c2 = restPat ++ after := by
                rw [hPat] at h
                simpa [List.append_assoc] using h
              have hCompatD2 : list_suffix_compat restPat d2 := by
                have hCompatPat : list_suffix_compat restPat pat := by
                  rw [hPat]
                  exact list_suffix_compat_symm
                    (list_suffix_compat_of_append_suffix (x :: xs) restPat)
                exact list_suffix_compat_of_compat_suffix hCompatPat hD2Suffix
              exact False.elim (hRight restPat after hSplit hRestPat hCompatD2)
          · exact ⟨[], restS, by simp [hS, List.append_assoc]⟩
  | b :: before, after, h => by
      cases s with
      | nil =>
          let pre := b :: before ++ pat
          have hPreNe : pre ≠ [] := by simp [pre]
          have hSplit : c2 = pre ++ after := by
            simpa [pre, List.append_assoc] using h
          have hCompatPat : list_suffix_compat pre d2 := by
            have hCompatSelf : list_suffix_compat pre pat := by
              have hSuffix : pre = (b :: before) ++ pat := by
                simp [pre, List.append_assoc]
              rw [hSuffix]
              exact list_suffix_compat_of_append_suffix (b :: before) pat
            exact list_suffix_compat_of_compat_suffix hCompatSelf hD2Suffix
          exact False.elim (hRight pre after hSplit hPreNe hCompatPat)
      | cons x xs =>
          injection h with hHead hTail
          subst b
          rcases list_match_inside_of_no_right_overlap xs c2 pat d2
              hRight hD2Suffix before after hTail with
            ⟨before', after', hInside⟩
          exact ⟨x :: before', after', by simp [hInside, List.append_assoc]⟩
private theorem native_seq_contains_eq_of_no_endpoint_overlap
    (c1 s c2 d1 t d2 : List SmtValue)
    (hLeft :
      ∀ pre suf, c1 = pre ++ suf -> suf ≠ [] ->
        list_prefix_compat suf d1 -> False)
    (hRight :
      ∀ pre suf, c2 = pre ++ suf -> pre ≠ [] ->
        list_suffix_compat pre d2 -> False) :
    native_seq_contains (c1 ++ s ++ c2) (d1 ++ t ++ d2) =
      native_seq_contains s (d1 ++ t ++ d2) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hContains
    rcases native_seq_contains_exists (c1 ++ s ++ c2) (d1 ++ t ++ d2)
        hContains with
      ⟨before, after, hMatch⟩
    have hD1Prefix : ∃ tail, d1 ++ t ++ d2 = d1 ++ tail :=
      ⟨t ++ d2, by simp [List.append_assoc]⟩
    have hD2Suffix : ∃ init, d1 ++ t ++ d2 = init ++ d2 :=
      ⟨d1 ++ t, by simp [List.append_assoc]⟩
    rcases list_match_after_left_of_no_overlap c1 (s ++ c2)
        (d1 ++ t ++ d2) d1 hLeft hD1Prefix before after
        (by simpa [List.append_assoc] using hMatch) with
      ⟨before', after', hRestMatch⟩
    rcases list_match_inside_of_no_right_overlap s c2
        (d1 ++ t ++ d2) d2 hRight hD2Suffix before' after'
        hRestMatch with
      ⟨beforeS, afterS, hSMatch⟩
    subst s
    simpa [List.append_assoc] using
      native_seq_contains_of_append beforeS (d1 ++ t ++ d2) afterS
  · intro hContains
    rcases native_seq_contains_exists s (d1 ++ t ++ d2) hContains with
      ⟨before, after, hMatch⟩
    subst s
    have hFull :
        native_seq_contains
          (c1 ++ before ++ (d1 ++ t ++ d2) ++ after ++ c2)
          (d1 ++ t ++ d2) = true := by
      simpa [List.append_assoc] using
        native_seq_contains_of_append (c1 ++ before) (d1 ++ t ++ d2)
          (after ++ c2)
    simpa [List.append_assoc] using hFull

private theorem seq_eval_of_seq_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    ∃ ss, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq ss := by
  intro hTy
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact seq_value_canonical (by simpa [hTy] using hEvalTy)

private theorem str_contains_args_of_non_none (x y : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) x) y)) ≠
      SmtType.None ->
    ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T ∧
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T := by
  intro hNN
  have hNN' : term_has_non_none_type
      (SmtTerm.str_contains (__eo_to_smt x) (__eo_to_smt y)) := by
    simpa [term_has_non_none_type] using hNN
  exact seq_binop_args_of_non_none_ret (op := SmtTerm.str_contains)
    (R := SmtType.Bool) (typeof_str_contains_eq (__eo_to_smt x) (__eo_to_smt y))
    hNN'

private theorem eval_mkConcat_lists
    (M : SmtModel) (x y : Term) (T : SmtType)
    (sx sy : SmtSeq)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy)
    (hxElem : __smtx_elem_typeof_seq_value sx = T) :
    __smtx_model_eval M (__eo_to_smt (mkConcat x y)) =
      SmtValue.Seq
        (native_pack_seq T (native_unpack_seq sx ++ native_unpack_seq sy)) := by
  rw [smtx_model_eval_str_concat_term_eq M x y, hxEval, hyEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat, hxElem]

private theorem eval_mkConcat3_lists
    (M : SmtModel) (x y z : Term) (T : SmtType)
    (sx sy sz : SmtSeq)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy)
    (hzEval : __smtx_model_eval M (__eo_to_smt z) = SmtValue.Seq sz)
    (hxElem : __smtx_elem_typeof_seq_value sx = T) :
    __smtx_model_eval M (__eo_to_smt (mkConcat x (mkConcat y z))) =
      SmtValue.Seq
        (native_pack_seq T
          (native_unpack_seq sx ++ native_unpack_seq sy ++ native_unpack_seq sz)) := by
  rw [smtx_model_eval_str_concat_term_eq M x (mkConcat y z)]
  rw [smtx_model_eval_str_concat_term_eq M y z]
  rw [hxEval, hyEval, hzEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat, hxElem,
    native_unpack_pack_seq, List.append_assoc]

private theorem elem_typeof_of_seq_eval_type
    (M : SmtModel) (hM : model_total_typed M) (x : Term) (T : SmtType)
    (sx : SmtSeq)
    (hxTy : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx) :
    __smtx_elem_typeof_seq_value sx = T := by
  have hxValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        __smtx_typeof (__eo_to_smt x) :=
    Smtm.smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x)
      (by simp [term_has_non_none_type, hxTy])
  have hsxTy : __smtx_typeof_seq_value sx = SmtType.Seq T := by
    simpa [hxEval, hxTy, __smtx_typeof_value] using hxValTy
  exact elem_typeof_seq_value_of_typeof_seq_value hsxTy

private theorem eval_mkConcat4_lists
    (M : SmtModel) (w x y z : Term) (T : SmtType)
    (sw sx sy sz : SmtSeq)
    (hwEval : __smtx_model_eval M (__eo_to_smt w) = SmtValue.Seq sw)
    (hxEval : __smtx_model_eval M (__eo_to_smt x) = SmtValue.Seq sx)
    (hyEval : __smtx_model_eval M (__eo_to_smt y) = SmtValue.Seq sy)
    (hzEval : __smtx_model_eval M (__eo_to_smt z) = SmtValue.Seq sz)
    (hwElem : __smtx_elem_typeof_seq_value sw = T) :
    __smtx_model_eval M (__eo_to_smt (mkConcat w (mkConcat x (mkConcat y z)))) =
      SmtValue.Seq
        (native_pack_seq T
          (native_unpack_seq sw ++ native_unpack_seq sx ++
            native_unpack_seq sy ++ native_unpack_seq sz)) := by
  rw [smtx_model_eval_str_concat_term_eq M w (mkConcat x (mkConcat y z))]
  rw [smtx_model_eval_str_concat_term_eq M x (mkConcat y z)]
  rw [smtx_model_eval_str_concat_term_eq M y z]
  rw [hwEval, hxEval, hyEval, hzEval]
  simp [__smtx_model_eval_str_concat, native_seq_concat, hwElem,
    native_unpack_pack_seq, List.append_assoc]

private theorem eval_of_str_is_empty_true
    (M : SmtModel) (emp : Term) (T : SmtType)
    (hEmpTy : __smtx_typeof (__eo_to_smt emp) = SmtType.Seq T)
    (hEmpty : __str_is_empty emp = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt emp) =
      SmtValue.Seq (SmtSeq.empty T) := by
  cases emp <;> simp [__str_is_empty] at hEmpty
  case UOp1 op arg =>
    cases op
    all_goals try simp [__str_is_empty] at hEmpty
    case seq_empty =>
      cases arg
      all_goals try simp [__str_is_empty] at hEmpty
      case Apply f U =>
        cases f
        all_goals try simp [__str_is_empty] at hEmpty
        case UOp op =>
          cases op
          all_goals try simp [__str_is_empty] at hEmpty
          case Seq =>
            change
              __smtx_model_eval M
                (__eo_to_smt_seq_empty
                  (__eo_to_smt_type
                    (Term.Apply (Term.UOp UserOp.Seq) U))) =
                SmtValue.Seq (SmtSeq.empty T)
            change
              __smtx_typeof
                (__eo_to_smt_seq_empty
                  (__eo_to_smt_type
                    (Term.Apply (Term.UOp UserOp.Seq) U))) =
                SmtType.Seq T at hEmpTy
            cases hTy :
                __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) U) <;>
              simp [__eo_to_smt_seq_empty, hTy] at hEmpTy ⊢
            case Seq A =>
              have hNN : __smtx_typeof (SmtTerm.seq_empty A) ≠ SmtType.None := by
                rw [hEmpTy]
                exact seq_ne_none T
              have hTyA :
                  __smtx_typeof (SmtTerm.seq_empty A) = SmtType.Seq A :=
                TranslationProofs.smtx_typeof_seq_empty_of_non_none A hNN
              have hAT : A = T := by
                have hSeq : SmtType.Seq A = SmtType.Seq T := by
                  rw [← hTyA, hEmpTy]
                injection hSeq
              subst T
              rw [__smtx_model_eval.eq_78]
  case String str =>
    cases str with
    | nil =>
        change
          __smtx_model_eval M
              (SmtTerm.String (native_string_lit "")) =
            SmtValue.Seq (SmtSeq.empty T)
        change
          __smtx_typeof (SmtTerm.String (native_string_lit "")) =
            SmtType.Seq T at hEmpTy
        rw [__smtx_typeof.eq_4] at hEmpTy
        simp [native_string_lit, native_string_valid, native_ite] at hEmpTy
        cases hEmpTy
        rw [__smtx_model_eval.eq_4]
        simp [native_pack_string, native_string_lit, native_pack_seq]
    | cons c cs =>
        simp [__str_is_empty] at hEmpty

private theorem eo_and_true_parts {a b : Term} :
    __eo_and a b = Term.Boolean true ->
      a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite,
      SmtEval.native_and, SmtEval.native_not] at h ⊢
  · exact h
  · split at h <;> simp at h

private theorem str_overlap_endpoints_ctn_valid_properties
    (M : SmtModel) (hM : model_total_typed M)
    (c1 s c2 emp d1 t d2 : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_contains)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) ->
    __eo_prog_str_overlap_endpoints_ctn
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_contains)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) ≠
        Term.Stuck ->
    StepRuleProperties M []
      (__eo_prog_str_overlap_endpoints_ctn
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_contains)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))) := by
  intro hTrans hNe
  let pat : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))
  let full : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))
  let lhs : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) full) pat
  let rhs : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s) pat
  let body : Term :=
    Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
  let leftGuard : Term :=
    __eo_gt (__str_value_len c1)
      (__str_overlap_rec (__str_flatten (__str_nary_intro c1))
        (__str_flatten (__str_nary_intro d1)))
  let rightGuard : Term :=
    __eo_gt (__str_value_len c2)
      (__str_overlap_rec
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro c2)))
        (__eo_list_rev (Term.UOp UserOp.str_concat)
          (__str_flatten (__str_nary_intro d2))))
  let rightReq : Term := __eo_requires rightGuard (Term.Boolean false) body
  let leftReq : Term := __eo_requires leftGuard (Term.Boolean false) rightReq
  let emptyReq : Term :=
    __eo_requires (__str_is_empty emp) (Term.Boolean true) leftReq
  let shapeGuard : Term :=
    __eo_and
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and (__eo_eq emp emp) (__eo_eq s s))
            (__eo_eq d1 d1))
          (__eo_eq t t))
        (__eo_eq d2 d2))
      (__eo_eq emp emp)
  change __eo_requires shapeGuard (Term.Boolean true) emptyReq ≠
    Term.Stuck at hNe
  have hShapeEq : shapeGuard = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck shapeGuard (Term.Boolean true) emptyReq hNe
  have hEmptyReqNe : emptyReq ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck shapeGuard (Term.Boolean true)
      emptyReq hNe
  have hShapeResult :
      __eo_requires shapeGuard (Term.Boolean true) emptyReq = emptyReq :=
    eo_requires_result_eq_of_ne_stuck shapeGuard (Term.Boolean true)
      emptyReq hNe
  have hEmptyEq : __str_is_empty emp = Term.Boolean true :=
    eo_requires_eq_of_ne_stuck (__str_is_empty emp) (Term.Boolean true)
      leftReq hEmptyReqNe
  have hLeftReqNe : leftReq ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck (__str_is_empty emp)
      (Term.Boolean true) leftReq hEmptyReqNe
  have hEmptyResult :
      __eo_requires (__str_is_empty emp) (Term.Boolean true) leftReq =
        leftReq :=
    eo_requires_result_eq_of_ne_stuck (__str_is_empty emp)
      (Term.Boolean true) leftReq hEmptyReqNe
  have hLeftGuardEq : leftGuard = Term.Boolean false :=
    eo_requires_eq_of_ne_stuck leftGuard (Term.Boolean false) rightReq
      hLeftReqNe
  have hRightReqNe : rightReq ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck leftGuard (Term.Boolean false)
      rightReq hLeftReqNe
  have hLeftResult :
      __eo_requires leftGuard (Term.Boolean false) rightReq = rightReq :=
    eo_requires_result_eq_of_ne_stuck leftGuard (Term.Boolean false)
      rightReq hLeftReqNe
  have hRightGuardEq : rightGuard = Term.Boolean false :=
    eo_requires_eq_of_ne_stuck rightGuard (Term.Boolean false) body
      hRightReqNe
  have hBodyNe : body ≠ Term.Stuck :=
    eo_requires_result_ne_stuck_of_ne_stuck rightGuard (Term.Boolean false)
      body hRightReqNe
  have hRightResult :
      __eo_requires rightGuard (Term.Boolean false) body = body :=
    eo_requires_result_eq_of_ne_stuck rightGuard (Term.Boolean false)
      body hRightReqNe
  have hProgEq :
      __eo_prog_str_overlap_endpoints_ctn
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.str_contains)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) =
        body := by
    calc
      __eo_prog_str_overlap_endpoints_ctn
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.str_contains)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
              (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) =
          __eo_requires shapeGuard (Term.Boolean true) emptyReq := by
            rfl
      _ = emptyReq := hShapeResult
      _ = leftReq := hEmptyResult
      _ = rightReq := hLeftResult
      _ = body := hRightResult
  have hBodyBool : RuleProofs.eo_has_bool_type body := by
    have hNN :
        term_has_non_none_type
          (SmtTerm.eq (__eo_to_smt lhs) (__eo_to_smt rhs)) := by
      unfold term_has_non_none_type
      simpa [RuleProofs.eo_has_smt_translation, body, lhs, rhs] using hTrans
    have hTy :
        __smtx_typeof (SmtTerm.eq (__eo_to_smt lhs) (__eo_to_smt rhs)) =
          SmtType.Bool :=
      Smtm.eq_term_typeof_of_non_none hNN
    simpa [RuleProofs.eo_has_bool_type, body, lhs, rhs] using hTy
  refine ⟨?_, ?_⟩
  · intro _hPremises
    rw [hProgEq]
    have hRel :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt lhs))
          (__smtx_model_eval M (__eo_to_smt rhs)) := by
      rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
      have hEqBool :
          RuleProofs.eo_has_bool_type
            (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) := by
        simpa [body] using hBodyBool
      rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          lhs rhs hEqBool with
        ⟨hLhsRhsTy, hLhsNN⟩
      have hRhsNN : __smtx_typeof (__eo_to_smt rhs) ≠ SmtType.None := by
        simpa [hLhsRhsTy] using hLhsNN
      rcases str_contains_args_of_non_none full pat
          (by simpa [lhs] using hLhsNN) with
        ⟨T, hFullTy, hPatTy⟩
      rcases str_contains_args_of_non_none s pat
          (by simpa [rhs] using hRhsNN) with
        ⟨U, hSTyU, hPatTyU⟩
      have hUT : U = T := by
        have hSeq : SmtType.Seq U = SmtType.Seq T := by
          rw [← hPatTyU, hPatTy]
        injection hSeq
      subst U
      have hSTy : __smtx_typeof (__eo_to_smt s) = SmtType.Seq T := hSTyU
      rcases str_concat_args_of_seq_type c1 (mkConcat s (mkConcat c2 emp))
          T (by simpa [full] using hFullTy) with
        ⟨hC1Ty, hSRestTy⟩
      rcases str_concat_args_of_seq_type s (mkConcat c2 emp) T hSRestTy with
        ⟨_hSTyFromFull, hC2EmpTy⟩
      rcases str_concat_args_of_seq_type c2 emp T hC2EmpTy with
        ⟨hC2Ty, hEmpTy⟩
      rcases str_concat_args_of_seq_type d1 (mkConcat t (mkConcat d2 emp))
          T (by simpa [pat] using hPatTy) with
        ⟨hD1Ty, hTRestTy⟩
      rcases str_concat_args_of_seq_type t (mkConcat d2 emp) T hTRestTy with
        ⟨hTTy, hD2EmpTy⟩
      rcases str_concat_args_of_seq_type d2 emp T hD2EmpTy with
        ⟨hD2Ty, _hEmpTyFromPat⟩
      rcases seq_eval_of_seq_type M hM c1 T hC1Ty with ⟨sc1, hC1Eval⟩
      rcases seq_eval_of_seq_type M hM s T hSTy with ⟨ss, hSEval⟩
      rcases seq_eval_of_seq_type M hM c2 T hC2Ty with ⟨sc2, hC2Eval⟩
      rcases seq_eval_of_seq_type M hM d1 T hD1Ty with ⟨sd1, hD1Eval⟩
      rcases seq_eval_of_seq_type M hM t T hTTy with ⟨st, hTEval⟩
      rcases seq_eval_of_seq_type M hM d2 T hD2Ty with ⟨sd2, hD2Eval⟩
      have hEmpEval :
          __smtx_model_eval M (__eo_to_smt emp) =
            SmtValue.Seq (SmtSeq.empty T) :=
        eval_of_str_is_empty_true M emp T hEmpTy hEmptyEq
      have hC1Elem : __smtx_elem_typeof_seq_value sc1 = T :=
        elem_typeof_of_seq_eval_type M hM c1 T sc1 hC1Ty hC1Eval
      have hD1Elem : __smtx_elem_typeof_seq_value sd1 = T :=
        elem_typeof_of_seq_eval_type M hM d1 T sd1 hD1Ty hD1Eval
      have hFullEval :
          __smtx_model_eval M (__eo_to_smt full) =
            SmtValue.Seq
              (native_pack_seq T
                (native_unpack_seq sc1 ++ native_unpack_seq ss ++
                  native_unpack_seq sc2)) := by
        have hFullEvalRaw :=
          eval_mkConcat4_lists M c1 s c2 emp T sc1 ss sc2
            (SmtSeq.empty T) hC1Eval hSEval hC2Eval hEmpEval hC1Elem
        simpa [full, native_unpack_seq, List.append_assoc] using hFullEvalRaw
      have hPatEval :
          __smtx_model_eval M (__eo_to_smt pat) =
            SmtValue.Seq
              (native_pack_seq T
                (native_unpack_seq sd1 ++ native_unpack_seq st ++
                  native_unpack_seq sd2)) := by
        have hPatEvalRaw :=
          eval_mkConcat4_lists M d1 t d2 emp T sd1 st sd2
            (SmtSeq.empty T) hD1Eval hTEval hD2Eval hEmpEval hD1Elem
        simpa [pat, native_unpack_seq, List.append_assoc] using hPatEvalRaw
      have hNoLeft :
          ∀ pre suf, native_unpack_seq sc1 = pre ++ suf -> suf ≠ [] ->
            list_prefix_compat suf (native_unpack_seq sd1) -> False := by
        -- Remaining guard-soundness direction for the left endpoint:
        -- `hLeftGuardEq` states that no nonempty suffix of `c1` overlaps
        -- the prefix component `d1`.
        sorry
      have hNoRight :
          ∀ pre suf, native_unpack_seq sc2 = pre ++ suf -> pre ≠ [] ->
            list_suffix_compat pre (native_unpack_seq sd2) -> False := by
        -- Remaining guard-soundness direction for the right endpoint:
        -- `hRightGuardEq` is the same overlap check after reversing both
        -- endpoint lists.
        sorry
      have hContainsEq :
          native_seq_contains
              (native_unpack_seq sc1 ++ native_unpack_seq ss ++
                native_unpack_seq sc2)
              (native_unpack_seq sd1 ++ native_unpack_seq st ++
                native_unpack_seq sd2) =
            native_seq_contains (native_unpack_seq ss)
              (native_unpack_seq sd1 ++ native_unpack_seq st ++
                native_unpack_seq sd2) := by
        simpa [List.append_assoc] using
          native_seq_contains_eq_of_no_endpoint_overlap
            (native_unpack_seq sc1) (native_unpack_seq ss)
            (native_unpack_seq sc2) (native_unpack_seq sd1)
            (native_unpack_seq st) (native_unpack_seq sd2)
            hNoLeft hNoRight
      change
        __smtx_model_eval_eq
          (__smtx_model_eval M
            (SmtTerm.str_contains (__eo_to_smt full) (__eo_to_smt pat)))
          (__smtx_model_eval M
            (SmtTerm.str_contains (__eo_to_smt s) (__eo_to_smt pat))) =
          SmtValue.Boolean true
      simpa [__smtx_model_eval, __smtx_model_eval_str_contains,
        hFullEval, hPatEval, hSEval, hContainsEq,
        native_unpack_pack_seq, elem_typeof_pack_seq, __smtx_model_eval_eq,
        native_veq, List.append_assoc] using hContainsEq
    exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBodyBool hRel
  · rw [hProgEq]
    exact hTrans

private theorem str_overlap_endpoints_ctn_arg_properties
    (M : SmtModel) (hM : model_total_typed M) :
    (a1 : Term) ->
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_prog_str_overlap_endpoints_ctn a1 ≠ Term.Stuck ->
    StepRuleProperties M [] (__eo_prog_str_overlap_endpoints_ctn a1)
  | a1, hTrans, hNe => by
      rw [__eo_prog_str_overlap_endpoints_ctn.eq_def] at hNe
      rw [__eo_prog_str_overlap_endpoints_ctn.eq_def]
      split at hNe
      · rename_i _ c1 s c2 emp d1 t d2 emp2 s2 d12 t2 d22 emp3
        have hShapeEq := eo_requires_eq_of_ne_stuck _ _ _ hNe
        rcases eo_and_true_parts hShapeEq with ⟨hABCDE, hEmp3EqTerm⟩
        rcases eo_and_true_parts hABCDE with ⟨hABCD, hD2EqTerm⟩
        rcases eo_and_true_parts hABCD with ⟨hABC, hTEqTerm⟩
        rcases eo_and_true_parts hABC with ⟨hAB, hD1EqTerm⟩
        rcases eo_and_true_parts hAB with ⟨hEmp2EqTerm, hSEqTerm⟩
        have hEmp2 : emp2 = emp := eq_of_eo_eq_true_local emp emp2 hEmp2EqTerm
        have hS2 : s2 = s := eq_of_eo_eq_true_local s s2 hSEqTerm
        have hD12 : d12 = d1 := eq_of_eo_eq_true_local d1 d12 hD1EqTerm
        have hT2 : t2 = t := eq_of_eo_eq_true_local t t2 hTEqTerm
        have hD22 : d22 = d2 := eq_of_eo_eq_true_local d2 d22 hD2EqTerm
        have hEmp3 : emp3 = emp := eq_of_eo_eq_true_local emp emp3 hEmp3EqTerm
        subst emp2
        subst s2
        subst d12
        subst t2
        subst d22
        subst emp3
        have hTrans' :
            RuleProofs.eo_has_smt_translation
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_contains)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) := by
          simpa using hTrans
        have hNe' :
            __eo_prog_str_overlap_endpoints_ctn
              (Term.Apply
                (Term.Apply (Term.UOp UserOp.eq)
                  (Term.Apply
                    (Term.Apply (Term.UOp UserOp.str_contains)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c1)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) s)
                          (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) c2) emp))))
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                        (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp)))))
                (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) s)
                  (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d1)
                    (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) t)
                      (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) d2) emp))))) ≠
              Term.Stuck := by
          simpa [__eo_prog_str_overlap_endpoints_ctn.eq_def] using hNe
        simpa [__eo_prog_str_overlap_endpoints_ctn.eq_def] using
          str_overlap_endpoints_ctn_valid_properties M hM c1 s c2 emp d1 t d2
            hTrans' hNe'
      · change Term.Stuck ≠ Term.Stuck at hNe
        exact False.elim (hNe rfl)

end RuleProofs

theorem cmd_step_str_overlap_endpoints_ctn_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.str_overlap_endpoints_ctn args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.str_overlap_endpoints_ctn args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using hCmdTrans.1
              change StepRuleProperties M [] (__eo_prog_str_overlap_endpoints_ctn a1)
              exact RuleProofs.str_overlap_endpoints_ctn_arg_properties
                M hM a1 hA1Trans hProg
