import Cpc.Proofs.Canonical.Basic

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Empty sequence values are canonical. -/
theorem seq_canonical_empty (T : SmtType) :
    __smtx_seq_canonical (SmtSeq.empty T) = true := by
  simp [__smtx_seq_canonical]

/-- Consing a canonical value onto a canonical sequence preserves sequence canonicality. -/
theorem seq_canonical_cons
    {v : SmtValue}
    {s : SmtSeq}
    (hv : __smtx_value_canonical v)
    (hs : __smtx_seq_canonical s = true) :
    __smtx_seq_canonical (SmtSeq.cons v s) = true := by
  have hvBool : __smtx_value_canonical_bool v = true := by
    simpa [__smtx_value_canonical] using hv
  simp [__smtx_seq_canonical, hvBool, hs, SmtEval.native_and]

/-- Canonical sequences give canonical `Seq` values. -/
theorem value_canonical_seq_of_seq_canonical
    {s : SmtSeq}
    (h : __smtx_seq_canonical s = true) :
    __smtx_value_canonical (SmtValue.Seq s) := by
  simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using h

/-- Packing and then unpacking a list of values gives the original list. -/
theorem native_unpack_pack_seq (T : SmtType) :
    ∀ xs : List SmtValue, native_unpack_seq (native_pack_seq T xs) = xs
  | [] => by
      simp [native_pack_seq, native_unpack_seq]
  | x :: xs => by
      simp [native_pack_seq, native_unpack_seq, native_unpack_pack_seq T xs]

/-- Packing a list of canonical values gives a canonical sequence. -/
theorem seq_canonical_pack_seq
    (T : SmtType) :
    ∀ {xs : List SmtValue},
      (∀ v, v ∈ xs -> __smtx_value_canonical v) ->
        __smtx_seq_canonical (native_pack_seq T xs) = true
  | [], _h => by
      simp [native_pack_seq, __smtx_seq_canonical]
  | v :: vs, h => by
      have hv : __smtx_value_canonical v := h v (by simp)
      have hvs : ∀ u, u ∈ vs -> __smtx_value_canonical u := by
        intro u hu
        exact h u (by simp [hu])
      simpa [native_pack_seq] using
        seq_canonical_cons hv (seq_canonical_pack_seq T hvs)

/-- Unpacking a canonical sequence gives a list of canonical values. -/
theorem seq_unpack_values_canonical :
    ∀ {s : SmtSeq},
      __smtx_seq_canonical s = true ->
        ∀ v, v ∈ native_unpack_seq s -> __smtx_value_canonical v
  | SmtSeq.empty T, _h, v, hv => by
      simp [native_unpack_seq] at hv
  | SmtSeq.cons x xs, h, v, hv => by
      have hx : __smtx_value_canonical x := by
        have hParts := h
        simp [__smtx_seq_canonical, SmtEval.native_and] at hParts
        exact hParts.1
      have hxs : __smtx_seq_canonical xs = true := by
        have hParts := h
        simp [__smtx_seq_canonical, SmtEval.native_and] at hParts
        exact hParts.2
      simp [native_unpack_seq] at hv
      rcases hv with rfl | hv
      · exact hx
      · exact seq_unpack_values_canonical hxs v hv

/-- Repacking the concatenation of two canonical sequences is canonical. -/
theorem seq_canonical_pack_unpack_concat
    (T : SmtType)
    {s1 s2 : SmtSeq}
    (h1 : __smtx_seq_canonical s1 = true)
    (h2 : __smtx_seq_canonical s2 = true) :
    __smtx_seq_canonical
      (native_pack_seq T (native_unpack_seq s1 ++ native_unpack_seq s2)) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  simp at hv
  rcases hv with hv | hv
  · exact seq_unpack_values_canonical h1 v hv
  · exact seq_unpack_values_canonical h2 v hv

/-- Repacking the reverse of a canonical sequence is canonical. -/
theorem seq_canonical_pack_unpack_reverse
    (T : SmtType)
    {s : SmtSeq}
    (h : __smtx_seq_canonical s = true) :
    __smtx_seq_canonical
      (native_pack_seq T (native_unpack_seq s).reverse) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  exact seq_unpack_values_canonical h v (by simpa using hv)

/-- Repacking a canonical sequence is canonical, even under a different empty-sequence tag. -/
theorem seq_canonical_pack_unpack
    (T : SmtType)
    {s : SmtSeq}
    (h : __smtx_seq_canonical s = true) :
    __smtx_seq_canonical (native_pack_seq T (native_unpack_seq s)) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  exact seq_unpack_values_canonical h v hv

/-- Repacking a subsequence extracted from a canonical sequence is canonical. -/
theorem seq_canonical_pack_unpack_extract
    (T : SmtType)
    {s : SmtSeq}
    (h : __smtx_seq_canonical s = true)
    (i n : native_Int) :
    __smtx_seq_canonical
      (native_pack_seq T (native_seq_extract (native_unpack_seq s) i n)) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  simp [native_seq_extract] at hv
  exact seq_unpack_values_canonical h v
    (List.mem_of_mem_drop (List.mem_of_mem_take hv.2))

/-- Repacking a one-shot replacement of canonical sequences is canonical. -/
theorem seq_canonical_pack_unpack_replace
    (T : SmtType)
    {s pat repl : SmtSeq}
    (hs : __smtx_seq_canonical s = true)
    (_hpat : __smtx_seq_canonical pat = true)
    (hrepl : __smtx_seq_canonical repl = true) :
    __smtx_seq_canonical
      (native_pack_seq T
        (native_seq_replace (native_unpack_seq s)
          (native_unpack_seq pat) (native_unpack_seq repl))) = true := by
  unfold native_seq_replace
  cases hpat : native_unpack_seq pat with
  | nil =>
      simp [hpat]
      apply seq_canonical_pack_seq
      intro v hv
      simp [List.mem_append] at hv
      rcases hv with hv | hv
      · exact seq_unpack_values_canonical hrepl v hv
      · exact seq_unpack_values_canonical hs v hv
  | cons p ps =>
      simp [hpat]
      split
      · exact seq_canonical_pack_unpack T hs
      · apply seq_canonical_pack_seq
        intro v hv
        simp [List.mem_append] at hv
        rcases hv with hv | hv | hv
        · exact seq_unpack_values_canonical hs v
            (List.mem_of_mem_take hv)
        · exact seq_unpack_values_canonical hrepl v hv
        · exact seq_unpack_values_canonical hs v
            (List.mem_of_mem_drop hv)

/-- Auxiliary canonicality invariant for repeated sequence replacement. -/
theorem seq_canonical_pack_replace_all_aux
    (T : SmtType)
    {pat repl : List SmtValue}
    (hrepl : ∀ v, v ∈ repl -> __smtx_value_canonical v) :
    ∀ (fuel : Nat) {xs : List SmtValue},
      (∀ v, v ∈ xs -> __smtx_value_canonical v) ->
        __smtx_seq_canonical
          (native_pack_seq T (native_seq_replace_all_aux fuel pat repl xs)) = true
  | 0, xs, hxs => by
      simpa [native_seq_replace_all_aux] using
        seq_canonical_pack_seq T hxs
  | fuel + 1, xs, hxs => by
      cases pat with
      | nil =>
          simpa [native_seq_replace_all_aux] using
            seq_canonical_pack_seq T hxs
      | cons p ps =>
          simp [native_seq_replace_all_aux]
          split
          · exact seq_canonical_pack_seq T hxs
          · apply seq_canonical_pack_seq
            intro v hv
            simp [List.mem_append] at hv
            rcases hv with hv | hv | hv
            · exact hxs v (List.mem_of_mem_take hv)
            · exact hrepl v hv
            · exact
                (seq_unpack_values_canonical
                  (seq_canonical_pack_replace_all_aux T hrepl fuel
                    (fun u hu => hxs u (List.mem_of_mem_drop hu))) v
                  (by simpa [native_unpack_pack_seq] using hv))

/-- Repacking a repeated replacement of canonical sequences is canonical. -/
theorem seq_canonical_pack_unpack_replace_all
    (T : SmtType)
    {s pat repl : SmtSeq}
    (hs : __smtx_seq_canonical s = true)
    (_hpat : __smtx_seq_canonical pat = true)
    (hrepl : __smtx_seq_canonical repl = true) :
    __smtx_seq_canonical
      (native_pack_seq T
        (native_seq_replace_all (native_unpack_seq s)
          (native_unpack_seq pat) (native_unpack_seq repl))) = true := by
  unfold native_seq_replace_all
  exact seq_canonical_pack_replace_all_aux T
    (fun u hu => seq_unpack_values_canonical hrepl u hu)
    ((native_unpack_seq s).length + 1)
    (fun u hu => seq_unpack_values_canonical hs u hu)

/-- Repacking a sequence update with canonical replacement values is canonical. -/
theorem seq_canonical_pack_unpack_update
    (T : SmtType)
    {s repl : SmtSeq}
    (hs : __smtx_seq_canonical s = true)
    (hrepl : __smtx_seq_canonical repl = true)
    (i : native_Int) :
    __smtx_seq_canonical
      (native_pack_seq T
        (native_seq_update (native_unpack_seq s) i (native_unpack_seq repl))) = true := by
  apply seq_canonical_pack_seq
  intro v hv
  unfold native_seq_update at hv
  dsimp at hv
  generalize hb :
    (decide (i < 0) ||
      decide (Int.ofNat (native_unpack_seq s).length ≤ i)) = b at hv
  cases b
  · simp [hb, List.mem_append] at hv
    rcases hv with hv | hv | hv
    · exact seq_unpack_values_canonical hs v
        (List.mem_of_mem_take hv)
    · exact seq_unpack_values_canonical hrepl v hv
    · exact seq_unpack_values_canonical hs v
        (List.mem_of_mem_drop hv)
  · simp [hb] at hv
    exact seq_unpack_values_canonical hs v hv

/-- Packed strings are canonical sequences, since every character value is canonical. -/
theorem seq_canonical_pack_string (s : native_String) :
    __smtx_seq_canonical (native_pack_string s) = true := by
  unfold native_pack_string
  apply seq_canonical_pack_seq
  intro v hv
  simp [__smtx_ssm_char_values_of_string] at hv
  rcases hv with ⟨c, _hc, rfl⟩
  exact value_canonical_char c

theorem value_canonical_string (s : native_String) :
    __smtx_value_canonical (SmtValue.Seq (native_pack_string s)) := by
  exact value_canonical_seq_of_seq_canonical (seq_canonical_pack_string s)

theorem value_canonical_seq_empty (T : SmtType) :
    __smtx_value_canonical (SmtValue.Seq (SmtSeq.empty T)) := by
  exact value_canonical_seq_of_seq_canonical (seq_canonical_empty T)

theorem value_canonical_seq_cons
    {v : SmtValue}
    {s : SmtSeq}
    (hv : __smtx_value_canonical v)
    (hs : __smtx_seq_canonical s = true) :
    __smtx_value_canonical (SmtValue.Seq (SmtSeq.cons v s)) := by
  exact value_canonical_seq_of_seq_canonical (seq_canonical_cons hv hs)

end Smtm
