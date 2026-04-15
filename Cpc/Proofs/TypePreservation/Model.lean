import Cpc.Proofs.TypePreservation.Support

open Smtm

namespace Smtm

/-- Describes how `model_total_typed` behaves under `lookup`. -/
theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : type_inhabited T) :
    __smtx_typeof_value (__smtx_model_lookup M s T) = T :=
  hM.1 s T hT

/-- Describes how `model_total_typed` behaves under `lookup_uninhabited`. -/
theorem model_total_typed_lookup_uninhabited
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : ¬ type_inhabited T) :
    __smtx_model_lookup M s T = SmtValue.NotValue :=
  hM.2 s T hT

/-- Describes how `model_typed_at` behaves under `push`. -/
theorem model_typed_at_push
    {M : SmtModel}
    {s : native_String}
    {T : SmtType}
    {v : SmtValue}
    (hv : __smtx_typeof_value v = T) :
    model_typed_at (__smtx_model_push M s T v) s T := by
  constructor
  · intro hT
    simp [__smtx_model_lookup, __smtx_model_push, __smtx_model_key, hv]
  · intro hT
    exfalso
    exact hT ⟨v, hv⟩

/-- Describes how `model_total_typed` behaves under `push`. -/
theorem model_total_typed_push
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (v : SmtValue)
    (hv : __smtx_typeof_value v = T) :
    model_total_typed (__smtx_model_push M s T v) := by
  constructor
  · intro s' T' hT'
    unfold __smtx_model_lookup __smtx_model_push
    by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
    · cases h
      simp [hv]
    · simp [h]
      exact model_total_typed_lookup hM s' T' hT'
  · intro s' T' hT'
    unfold __smtx_model_lookup __smtx_model_push
    by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
    · cases h
      exfalso
      exact hT' ⟨v, hv⟩
    · simp [h]
      exact model_total_typed_lookup_uninhabited hM s' T' hT'

/-- Shows that `default_typed_model` is total and type-correct on every inhabited SMT type. -/
theorem default_typed_model_total_typed :
    model_total_typed default_typed_model := by
  classical
  constructor
  · intro s T hT
    simp [default_typed_model, __smtx_model_lookup, __smtx_model_key, hT,
      Classical.choose_spec hT]
  · intro s T hT
    simp [default_typed_model, __smtx_model_lookup, __smtx_model_key, hT]

/-- Constructs a total typed SMT model. -/
theorem exists_total_typed_model :
    ∃ M : SmtModel, model_total_typed M :=
  ⟨default_typed_model, default_typed_model_total_typed⟩

end Smtm
