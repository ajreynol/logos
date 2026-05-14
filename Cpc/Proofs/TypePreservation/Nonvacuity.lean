import Cpc.Proofs.TypePreservation.Model

open SmtEval
open Smtm

namespace Smtm

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

/-- Shows that total typed SMT models exist. -/
theorem total_typed_model_nonvacuous :
    ∃ M : SmtModel, model_total_typed M :=
  exists_total_typed_model

end Smtm
