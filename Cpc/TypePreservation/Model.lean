import Cpc.TypePreservation.Support

open Smtm

namespace Smtm

theorem model_total_typed_lookup
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType) :
    __smtx_typeof_value (__smtx_model_lookup M s T) = T :=
  hM s T

theorem model_typed_at_push
    {M : SmtModel}
    {s : smt_lit_String}
    {T : SmtType}
    {v : SmtValue}
    (hv : __smtx_typeof_value v = T) :
    model_typed_at (__smtx_model_push M s T v) s T := by
  unfold model_typed_at __smtx_model_lookup __smtx_model_push
  simp [__smtx_model_key, hv]

theorem model_total_typed_push
    {M : SmtModel}
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (T : SmtType)
    (v : SmtValue)
    (hv : __smtx_typeof_value v = T) :
    model_total_typed (__smtx_model_push M s T v) := by
  intro s' T'
  unfold __smtx_model_lookup __smtx_model_push
  by_cases h : __smtx_model_key s' T' = __smtx_model_key s T
  · cases h
    simp [hv]
  · simp [h]
    exact hM s' T'

end Smtm
