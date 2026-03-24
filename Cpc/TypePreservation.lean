import Cpc.SmtModel

open Smtm

namespace Smtm

noncomputable abbrev model_eval := __smtx_model_eval
abbrev typeof := __smtx_typeof
abbrev typeofvalue := __smtx_typeof_value

/--
A minimal well-typedness condition on the explicit entries stored in a model.
This is weaker than requiring every lookup to succeed.
-/
def ModelEntryWellTyped (M : SmtModel) : Prop :=
  ∀ k v, M k = some v -> typeofvalue v = k.ty

theorem empty_model_entry_well_typed : ModelEntryWellTyped SmtModel.empty := by
  intro k v h
  simp [SmtModel.empty] at h

theorem preserve_var_of_lookup
    {M : SmtModel} {s : smt_lit_String} {T : SmtType} {v : SmtValue}
    (hM : ModelEntryWellTyped M)
    (hlookup : M (__smtx_model_key s T) = some v) :
    typeofvalue (model_eval M (SmtTerm.Var s T)) = typeof (SmtTerm.Var s T) := by
  change typeofvalue (__smtx_model_lookup M s T) = T
  rw [show __smtx_model_lookup M s T =
      match M (__smtx_model_key s T) with
      | some v => v
      | none => SmtValue.NotValue by rfl]
  rw [hlookup]
  simpa [__smtx_model_key] using hM (__smtx_model_key s T) v hlookup

theorem preserve_uconst_of_lookup
    {M : SmtModel} {s : smt_lit_String} {T : SmtType} {v : SmtValue}
    (hM : ModelEntryWellTyped M)
    (hlookup : M (__smtx_model_key s T) = some v) :
    typeofvalue (model_eval M (SmtTerm.UConst s T)) = typeof (SmtTerm.UConst s T) := by
  change typeofvalue (__smtx_model_lookup M s T) = T
  rw [show __smtx_model_lookup M s T =
      match M (__smtx_model_key s T) with
      | some v => v
      | none => SmtValue.NotValue by rfl]
  rw [hlookup]
  simpa [__smtx_model_key] using hM (__smtx_model_key s T) v hlookup

theorem preserve_boolean_literal (M : SmtModel) (b : smt_lit_Bool) :
    typeofvalue (model_eval M (SmtTerm.Boolean b)) = typeof (SmtTerm.Boolean b) := by
  rfl

theorem preserve_numeral_literal (M : SmtModel) (n : smt_lit_Int) :
    typeofvalue (model_eval M (SmtTerm.Numeral n)) = typeof (SmtTerm.Numeral n) := by
  rfl

theorem preserve_rational_literal (M : SmtModel) (q : smt_lit_Rat) :
    typeofvalue (model_eval M (SmtTerm.Rational q)) = typeof (SmtTerm.Rational q) := by
  rfl

def strIndexOfCounterexample : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.Apply
      (SmtTerm.Apply SmtTerm.str_indexof (SmtTerm.String "abc"))
      (SmtTerm.String "b"))
    (SmtTerm.Numeral 0)

theorem typeof_strIndexOfCounterexample :
    typeof strIndexOfCounterexample = SmtType.Seq SmtType.Char := by
  rfl

theorem typeofvalue_eval_strIndexOfCounterexample :
    typeofvalue (model_eval SmtModel.empty strIndexOfCounterexample) = SmtType.Int := by
  rfl

theorem strIndexOf_breaks_type_preservation :
    typeofvalue (model_eval SmtModel.empty strIndexOfCounterexample) ≠
      typeof strIndexOfCounterexample := by
  decide

theorem no_full_type_preservation :
    ¬ (∀ M, ModelEntryWellTyped M -> ∀ t, typeof t ≠ SmtType.None ->
        typeofvalue (model_eval M t) = typeof t) := by
  intro h
  have hpres :=
    h SmtModel.empty empty_model_entry_well_typed strIndexOfCounterexample (by
      rw [typeof_strIndexOfCounterexample]
      decide)
  exact strIndexOf_breaks_type_preservation hpres

end Smtm
