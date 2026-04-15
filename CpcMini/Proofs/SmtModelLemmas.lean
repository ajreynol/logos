import CpcMini.SmtModel

open Smtm

/-- Predicate asserting that an SMT type has at least one value. -/
def smt_type_inhabited (T : SmtType) : Prop :=
  ∃ v : SmtValue, __smtx_typeof_value v = T

/-- Shows that `SmtType.Bool` is inhabited. -/
theorem smt_type_inhabited_bool : smt_type_inhabited SmtType.Bool := by
  exact ⟨SmtValue.Boolean true, rfl⟩

/-- Predicate asserting that model lookups return values of the requested inhabited type. -/
def smt_model_well_typed (M : SmtModel) : Prop :=
  ∀ s T, smt_type_inhabited T ->
    __smtx_typeof_value (__smtx_model_lookup M s T) = T

/-- Derives `smt_model_lookup_type` from `well_typed`. -/
theorem smt_model_lookup_type_of_well_typed
    (M : SmtModel) (hM : smt_model_well_typed M)
    (s : native_String) (T : SmtType) :
  smt_type_inhabited T ->
  __smtx_typeof_value (__smtx_model_lookup M s T) = T := by
  exact hM s T

/-- Lemma about `smt_model_well_typed_push`. -/
theorem smt_model_well_typed_push
    (M : SmtModel) (hM : smt_model_well_typed M)
    (s : native_String) (T : SmtType) (v : SmtValue) :
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
