import Cpc.SmtModel

namespace Smtm

set_option linter.unusedVariables false

/--
A natural statement for type preservation needs at least a typed lookup
assumption for variables and uninterpreted constants.
-/
def ModelLookupWellTyped (M : SmtModel) : Prop :=
  ∀ s T, __smtx_typeof_value (__smtx_model_lookup M s T) = T

def PreservesType (M : SmtModel) (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None ->
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t

theorem model_lookup_preserves_type
    (hM : ModelLookupWellTyped M) (s : smt_lit_String) (T : SmtType) :
    __smtx_typeof_value (__smtx_model_lookup M s T) = T :=
  hM s T

theorem eval_var_preserves_type
    (hM : ModelLookupWellTyped M) (s : smt_lit_String) (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Var s T)) =
      __smtx_typeof (SmtTerm.Var s T) := by
  exact hM s T

theorem eval_uconst_preserves_type
    (hM : ModelLookupWellTyped M) (s : smt_lit_String) (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.UConst s T)) =
      __smtx_typeof (SmtTerm.UConst s T) := by
  exact hM s T

theorem eval_boolean_preserves_type (M : SmtModel) (b : smt_lit_Bool) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Boolean b)) =
      __smtx_typeof (SmtTerm.Boolean b) := rfl

theorem eval_numeral_preserves_type (M : SmtModel) (n : smt_lit_Int) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Numeral n)) =
      __smtx_typeof (SmtTerm.Numeral n) := rfl

theorem eval_rational_preserves_type (M : SmtModel) (q : smt_lit_Rat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Rational q)) =
      __smtx_typeof (SmtTerm.Rational q) := rfl

theorem eval_string_preserves_type (M : SmtModel) (s : smt_lit_String) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.String s)) =
      __smtx_typeof (SmtTerm.String s) := rfl

theorem eval_seq_empty_preserves_type (M : SmtModel) (T : SmtType) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.seq_empty T)) =
      __smtx_typeof (SmtTerm.seq_empty T) := rfl

/--
Without assumptions on model lookup, even the variable case breaks.
-/
def badVar : SmtTerm :=
  SmtTerm.Var "x" SmtType.Bool

theorem badVar_typed :
    __smtx_typeof badVar = SmtType.Bool := rfl

theorem badVar_eval_empty :
    __smtx_model_eval SmtModel.empty badVar = SmtValue.NotValue := rfl

theorem badVar_breaks_preservation :
    ¬ PreservesType SmtModel.empty badVar := by
  intro h
  have hne : __smtx_typeof badVar ≠ SmtType.None := by
    rw [badVar_typed]
    decide
  have hpres := h hne
  rw [badVar_eval_empty, badVar_typed] at hpres
  simp [__smtx_typeof_value] at hpres

/--
The naive closed-term preservation theorem also fails. `seq_nth` expects a
sequence value, but string literals evaluate to `SmtValue.String`, not
`SmtValue.Seq ...`.
-/
def badSeqNth : SmtTerm :=
  SmtTerm.Apply (SmtTerm.Apply SmtTerm.seq_nth (SmtTerm.String "a")) (SmtTerm.Numeral 0)

theorem badSeqNth_typed :
    __smtx_typeof badSeqNth = SmtType.Char := rfl

theorem badSeqNth_eval_empty :
    __smtx_model_eval SmtModel.empty badSeqNth = SmtValue.NotValue := rfl

theorem badSeqNth_breaks_preservation :
    ¬ PreservesType SmtModel.empty badSeqNth := by
  intro h
  have hne : __smtx_typeof badSeqNth ≠ SmtType.None := by
    rw [badSeqNth_typed]
    decide
  have hpres := h hne
  rw [badSeqNth_eval_empty, badSeqNth_typed] at hpres
  simp [__smtx_typeof_value] at hpres

/--
`_at_bv` is also mismatched: the evaluator uses the second numeral as the bit
width, while the typechecker returns `BitVec` of the first numeral.
-/
def badAtBv : SmtTerm :=
  SmtTerm.Apply (SmtTerm.Apply SmtTerm._at_bv (SmtTerm.Numeral 5)) (SmtTerm.Numeral 3)

theorem badAtBv_typed :
    __smtx_typeof badAtBv = SmtType.BitVec 5 := rfl

theorem badAtBv_eval_empty :
    __smtx_model_eval SmtModel.empty badAtBv =
      SmtValue.Binary 3 (smt_lit_mod_total 5 (smt_lit_int_pow2 3)) := rfl

theorem badAtBv_eval_type :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty badAtBv) = SmtType.BitVec 3 := rfl

theorem badAtBv_breaks_preservation :
    ¬ PreservesType SmtModel.empty badAtBv := by
  intro h
  have hne : __smtx_typeof badAtBv ≠ SmtType.None := by
    rw [badAtBv_typed]
    decide
  have hpres := h hne
  rw [badAtBv_eval_type, badAtBv_typed] at hpres
  simp at hpres

end Smtm
