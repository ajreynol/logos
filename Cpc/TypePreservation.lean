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

theorem typeof_pack_seq_chars (xs : List Char) :
    __smtx_typeof_seq_value (smt_lit_pack_seq SmtType.Char (xs.map SmtValue.Char)) =
      SmtType.Seq SmtType.Char := by
  induction xs with
  | nil => rfl
  | cons c cs ih =>
      simp [smt_lit_pack_seq, __smtx_typeof_seq_value, ih, smt_lit_Teq,
        __smtx_typeof_value, smt_lit_ite]

theorem preserve_string_literal (M : SmtModel) (s : smt_lit_String) :
    typeofvalue (model_eval M (SmtTerm.String s)) = typeof (SmtTerm.String s) := by
  simpa [model_eval, typeof, typeofvalue, smt_lit_pack_string, __smtx_ssm_char_values_of_string] using
    typeof_pack_seq_chars s.toList

theorem preserve_seq_empty (M : SmtModel) (T : SmtType) :
    typeofvalue (model_eval M (SmtTerm.seq_empty T)) = typeof (SmtTerm.seq_empty T) := by
  rfl

theorem preserve_set_empty (M : SmtModel) (T : SmtType) :
    typeofvalue (model_eval M (SmtTerm.set_empty T)) = typeof (SmtTerm.set_empty T) := by
  rfl

theorem preserve_re_allchar (M : SmtModel) :
    typeofvalue (model_eval M SmtTerm.re_allchar) = typeof SmtTerm.re_allchar := by
  rfl

theorem preserve_re_none (M : SmtModel) :
    typeofvalue (model_eval M SmtTerm.re_none) = typeof SmtTerm.re_none := by
  rfl

theorem preserve_re_all (M : SmtModel) :
    typeofvalue (model_eval M SmtTerm.re_all) = typeof SmtTerm.re_all := by
  rfl

def strIndexOfExample : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.Apply
      (SmtTerm.Apply SmtTerm.str_indexof (SmtTerm.String "abc"))
      (SmtTerm.String "b"))
    (SmtTerm.Numeral 0)

theorem preserve_strIndexOf_example :
    typeofvalue (model_eval SmtModel.empty strIndexOfExample) =
      typeof strIndexOfExample := by
  rfl

def missingVarCounterexample : SmtTerm :=
  SmtTerm.Var "x" SmtType.Int

theorem typeof_missingVarCounterexample :
    typeof missingVarCounterexample = SmtType.Int := by
  rfl

theorem typeofvalue_eval_missingVarCounterexample :
    typeofvalue (model_eval SmtModel.empty missingVarCounterexample) = SmtType.None := by
  rfl

theorem missingVar_breaks_type_preservation :
    typeofvalue (model_eval SmtModel.empty missingVarCounterexample) ≠
      typeof missingVarCounterexample := by
  decide

def seqNthCounterexample : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.Apply SmtTerm.seq_nth (SmtTerm.seq_empty SmtType.Int))
    (SmtTerm.Numeral 0)

theorem typeof_seqNthCounterexample :
    typeof seqNthCounterexample = SmtType.Int := by
  rfl

theorem typeofvalue_eval_seqNthCounterexample :
    typeofvalue (model_eval SmtModel.empty seqNthCounterexample) = SmtType.None := by
  rfl

theorem seqNth_breaks_type_preservation :
    typeofvalue (model_eval SmtModel.empty seqNthCounterexample) ≠
      typeof seqNthCounterexample := by
  decide

def extractCounterexample : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.Apply
      (SmtTerm.Apply SmtTerm.extract (SmtTerm.Numeral 3))
      (SmtTerm.Numeral 1))
    (SmtTerm.Binary 4 0)

theorem typeof_extractCounterexample :
    typeof extractCounterexample = SmtType.BitVec (-1) := by
  rfl

theorem typeofvalue_eval_extractCounterexample :
    typeofvalue (model_eval SmtModel.empty extractCounterexample) = SmtType.BitVec 3 := by
  rfl

theorem extract_breaks_type_preservation :
    typeofvalue (model_eval SmtModel.empty extractCounterexample) ≠
      typeof extractCounterexample := by
  decide

def divZeroCounterexample : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.Apply SmtTerm.div (SmtTerm.Numeral 5))
    (SmtTerm.Numeral 0)

theorem typeof_divZeroCounterexample :
    typeof divZeroCounterexample = SmtType.Int := by
  rfl

theorem typeofvalue_eval_divZeroCounterexample :
    typeofvalue (model_eval SmtModel.empty divZeroCounterexample) = SmtType.None := by
  rfl

theorem divZero_breaks_type_preservation :
    typeofvalue (model_eval SmtModel.empty divZeroCounterexample) ≠
      typeof divZeroCounterexample := by
  decide

def modZeroCounterexample : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.Apply SmtTerm.mod (SmtTerm.Numeral 5))
    (SmtTerm.Numeral 0)

theorem typeof_modZeroCounterexample :
    typeof modZeroCounterexample = SmtType.Int := by
  rfl

theorem typeofvalue_eval_modZeroCounterexample :
    typeofvalue (model_eval SmtModel.empty modZeroCounterexample) = SmtType.None := by
  rfl

theorem modZero_breaks_type_preservation :
    typeofvalue (model_eval SmtModel.empty modZeroCounterexample) ≠
      typeof modZeroCounterexample := by
  decide

def multmultNegativeZeroCounterexample : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.Apply SmtTerm.multmult (SmtTerm.Numeral 0))
    (SmtTerm.Numeral (-1))

theorem typeof_multmultNegativeZeroCounterexample :
    typeof multmultNegativeZeroCounterexample = SmtType.Int := by
  rfl

theorem typeofvalue_eval_multmultNegativeZeroCounterexample :
    typeofvalue (model_eval SmtModel.empty multmultNegativeZeroCounterexample) = SmtType.None := by
  rfl

theorem multmultNegativeZero_breaks_type_preservation :
    typeofvalue (model_eval SmtModel.empty multmultNegativeZeroCounterexample) ≠
      typeof multmultNegativeZeroCounterexample := by
  decide

theorem no_full_type_preservation :
    ¬ (∀ M, ModelEntryWellTyped M -> ∀ t, typeof t ≠ SmtType.None ->
        typeofvalue (model_eval M t) = typeof t) := by
  intro h
  have hpres :=
    h SmtModel.empty empty_model_entry_well_typed extractCounterexample (by
      rw [typeof_extractCounterexample]
      decide)
  exact extract_breaks_type_preservation hpres

/-
Known remaining failure families in the current semantics:

* `Var` / `UConst` if the model does not contain the requested key.
* `seq_nth` on out-of-bounds indices.
* `extract`, because `__smtx_typeof_extract` computes the output width as `lo - hi + 1`
  while `__smtx_model_eval_extract` returns width `hi - lo + 1`.
* `div`, `mod`, and `multmult` in the branches that consult the special model symbols
  `@div_by_zero` / `@mod_by_zero`; if those are absent, evaluation yields `NotValue`.
* `qdiv` has the same issue on the real-by-zero branch via `@qdiv_by_zero`.
* `DtSel` can fall back to `@wrong_apply_sel` when the argument is not headed by the
  matching constructor.
* Non-nullary datatype constructors use different function-type encodings:
  `typeof` uses `Map`, while `typeofvalue` on evaluated constructor values uses
  `DtConsType`, and `__smtx_model_eval_apply` does not apply bare `SmtValue.DtCons`.
* `choice` can return `NotValue` when asked to choose from a type with no runtime
  inhabitants in `SmtValue`, for example `USort` and `TypeRef`.
-/

end Smtm
