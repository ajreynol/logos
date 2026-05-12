import Cpc.Proofs.TypePreservation.Support

open SmtEval
open Smtm

namespace Smtm

/-- Describes how `model_total_typed` behaves under lookup for well-formed types. -/
theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_typeof_value (__smtx_model_lookup M s T) = T :=
  hM.1 s T hT

/-- Describes how `model_total_typed` preserves canonical lookup values for well-formed types. -/
theorem model_total_typed_lookup_canonical
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = true) :
    __smtx_value_canonical (__smtx_model_lookup M s T) :=
  hM.2.1 s T hT

/-- Describes how `model_total_typed` behaves under lookup for non-well-formed types. -/
theorem model_total_typed_lookup_not_wf
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = false) :
    __smtx_model_lookup M s T = SmtValue.NotValue :=
  hM.2.2 s T hT

theorem model_total_typed_lookup_uninhabited
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : __smtx_type_wf T = false) :
    __smtx_model_lookup M s T = SmtValue.NotValue :=
  model_total_typed_lookup_not_wf hM s T hT

/-- Describes how `model_typed_at` behaves under `push`. -/
theorem model_typed_at_push
    {M : SmtModel}
    {s : native_String}
    {T : SmtType}
    {v : SmtValue}
    (hWF : __smtx_type_wf T = true)
    (hv : __smtx_typeof_value v = T) :
    model_typed_at (__smtx_model_push M s T v) s T := by
  constructor
  · intro hT
    simp [__smtx_model_lookup, __smtx_model_push, __smtx_model_key, hv]
  · intro hT
    rw [hWF] at hT
    cases hT

/-- Describes how `model_total_typed` behaves under `push`. -/
theorem model_total_typed_push
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (v : SmtValue)
    (hWF : __smtx_type_wf T = true)
    (hv : __smtx_typeof_value v = T)
    (hvCanon : __smtx_value_canonical v) :
    model_total_typed (__smtx_model_push M s T v) := by
  constructor
  · intro s' T' hT'
    unfold __smtx_model_lookup __smtx_model_push
    by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
    · cases h
      simp [hv]
    · simp [h]
      exact model_total_typed_lookup hM s' T' hT'
  · constructor
    · intro s' T' hT'
      unfold __smtx_model_lookup __smtx_model_push
      by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
      · cases h
        simp [hvCanon]
      · simp [h]
        exact model_total_typed_lookup_canonical hM s' T' hT'
    · intro s' T' hT'
      unfold __smtx_model_lookup __smtx_model_push
      by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
      · cases h
        rw [hWF] at hT'
        cases hT'
      · simp [h]
        exact model_total_typed_lookup_uninhabited hM s' T' hT'

end Smtm
