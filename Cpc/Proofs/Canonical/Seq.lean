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
