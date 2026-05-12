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

/-- Choice-based model from canonical witnesses for every well-formed SMT type. -/
noncomputable def default_typed_model_of
    (hCan :
      ∀ T : SmtType,
        __smtx_type_wf T = true ->
          ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v) :
    SmtModel := by
  classical
  exact fun k =>
    if hWF : __smtx_type_wf k.ty = true then
      some (Classical.choose (hCan k.ty hWF))
    else
      none

/--
Reduces nonvacuity of total typed models to the canonical-inhabitant theorem
for well-formed SMT types.
-/
theorem exists_total_typed_model_of_canonical_type_inhabited
    (hCan :
      ∀ T : SmtType,
        __smtx_type_wf T = true ->
          ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v) :
    ∃ M : SmtModel, model_total_typed M := by
  classical
  refine ⟨default_typed_model_of hCan, ?_⟩
  constructor
  · intro s T hT
    simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT,
      (Classical.choose_spec (hCan T hT)).1]
  · constructor
    · intro s T hT
      simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT,
        (Classical.choose_spec (hCan T hT)).2]
    · intro s T hT
      simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT]

/--
Every well-formed SMT type has a canonical inhabitant.

The remaining hard cases are generated datatype defaults, and finite-domain
map/function defaults whose canonicality is tied to `__smtx_type_default`.
-/
theorem canonical_type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
  sorry

/-- Choice-based model that returns a canonical inhabitant for every well-formed SMT type. -/
noncomputable def default_typed_model : SmtModel :=
  default_typed_model_of canonical_type_inhabited_of_type_wf

/-- Shows that `default_typed_model` is total and type-correct on every well-formed SMT type. -/
theorem default_typed_model_total_typed :
    model_total_typed default_typed_model := by
  classical
  unfold default_typed_model
  constructor
  · intro s T hT
    simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT,
      (Classical.choose_spec (canonical_type_inhabited_of_type_wf T hT)).1]
  · constructor
    · intro s T hT
      simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT,
        (Classical.choose_spec (canonical_type_inhabited_of_type_wf T hT)).2]
    · intro s T hT
      simp [default_typed_model_of, __smtx_model_lookup, __smtx_model_key, hT]

/-- Constructs a total typed SMT model. -/
theorem exists_total_typed_model :
    ∃ M : SmtModel, model_total_typed M :=
  ⟨default_typed_model, default_typed_model_total_typed⟩

end Smtm
