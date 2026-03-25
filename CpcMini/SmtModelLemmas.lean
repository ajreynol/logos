import CpcMini.SmtModel

open Smtm

def smt_type_inhabited (T : SmtType) : Prop :=
  ∃ v : SmtValue, __smtx_typeof_value v = T

theorem smt_type_inhabited_bool : smt_type_inhabited SmtType.Bool := by
  exact ⟨SmtValue.Boolean true, rfl⟩

def smt_model_well_typed (M : SmtModel) : Prop :=
  ∀ s T, smt_type_inhabited T ->
    __smtx_typeof_value (__smtx_model_lookup M s T) = T

theorem smt_model_lookup_type_of_well_typed
    (M : SmtModel) (hM : smt_model_well_typed M)
    (s : smt_lit_String) (T : SmtType) :
  smt_type_inhabited T ->
  __smtx_typeof_value (__smtx_model_lookup M s T) = T := by
  exact hM s T

theorem smt_model_well_typed_push
    (M : SmtModel) (hM : smt_model_well_typed M)
    (s : smt_lit_String) (T : SmtType) (v : SmtValue) :
  __smtx_typeof_value v = T ->
  smt_model_well_typed (__smtx_model_push M s T v) := by
  intro hTy
  intro s' T' hInh
  unfold __smtx_model_push
  by_cases hKey : __smtx_model_key s' T' = __smtx_model_key s T
  · cases hKey with
    | _ =>
        simp [__smtx_model_key, __smtx_model_lookup, hTy]
  · simp [hKey, __smtx_model_lookup]
    exact hM s' T' hInh

theorem smt_model_eval_preserves_type
    (M : SmtModel) (hM : smt_model_well_typed M)
    (t : SmtTerm) (T : SmtType) :
  __smtx_typeof t = T ->
  smt_type_inhabited T ->
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  sorry

theorem smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : smt_model_well_typed M)
    (t : SmtTerm) :
  __smtx_typeof t = SmtType.Bool ->
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  sorry
