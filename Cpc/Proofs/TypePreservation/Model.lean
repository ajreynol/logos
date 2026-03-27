import Cpc.Proofs.TypePreservation.Support

open Smtm

namespace Smtm

theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType)
    (hT : type_inhabited T) :
    __smtx_typeof_value (__smtx_model_lookup M s T) = T :=
  hM.1 s T hT

theorem model_total_typed_lookup_uninhabited
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType)
    (hT : ¬ type_inhabited T) :
    __smtx_model_lookup M s T = SmtValue.NotValue :=
  hM.2 s T hT

theorem model_typed_at_push
    {M : SmtModel}
    {s : smt_lit_String}
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

theorem model_total_typed_push
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : smt_lit_String)
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

theorem default_typed_model_total_typed :
    model_total_typed default_typed_model := by
  classical
  constructor
  · intro s T hT
    simp [default_typed_model, __smtx_model_lookup, __smtx_model_key, hT,
      Classical.choose_spec hT]
  · intro s T hT
    simp [default_typed_model, __smtx_model_lookup, __smtx_model_key, hT]

theorem exists_total_typed_model :
    ∃ M : SmtModel, model_total_typed M :=
  ⟨default_typed_model, default_typed_model_total_typed⟩

end Smtm
