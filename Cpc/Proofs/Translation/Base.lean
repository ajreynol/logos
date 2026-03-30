import Cpc.Spec

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

@[simp] theorem eo_typeof_boolean (b : eo_lit_Bool) :
    __eo_typeof (Term.Boolean b) = Term.Bool := by
  cases b <;> native_decide

@[simp] theorem eo_typeof_re_allchar :
    __eo_typeof Term.re_allchar = Term.RegLan := by
  native_decide

@[simp] theorem eo_typeof_re_none :
    __eo_typeof Term.re_none = Term.RegLan := by
  native_decide

@[simp] theorem eo_typeof_re_all :
    __eo_typeof Term.re_all = Term.RegLan := by
  native_decide

@[simp] theorem eo_to_smt_boolean (b : eo_lit_Bool) :
    __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_re_allchar :
    __eo_to_smt Term.re_allchar = SmtTerm.re_allchar := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_re_none :
    __eo_to_smt Term.re_none = SmtTerm.re_none := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_re_all :
    __eo_to_smt Term.re_all = SmtTerm.re_all := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_type_bool :
    __eo_to_smt_type Term.Bool = SmtType.Bool := rfl

@[simp] theorem eo_to_smt_type_int :
    __eo_to_smt_type Term.Int = SmtType.Int := rfl

@[simp] theorem eo_to_smt_type_real :
    __eo_to_smt_type Term.Real = SmtType.Real := rfl

@[simp] theorem eo_to_smt_type_char :
    __eo_to_smt_type Term.Char = SmtType.Char := rfl

@[simp] theorem eo_to_smt_type_reglan :
    __eo_to_smt_type Term.RegLan = SmtType.RegLan := rfl

@[simp] theorem eo_to_smt_type_seq (T : Term) :
    __eo_to_smt_type (Term.Apply Term.Seq T) = SmtType.Seq (__eo_to_smt_type T) := by
  simp [__eo_to_smt_type]

@[simp] theorem eo_to_smt_type_array (A B : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.Array A) B) =
      SmtType.Map (__eo_to_smt_type A) (__eo_to_smt_type B) := by
  simp [__eo_to_smt_type]

@[simp] theorem eo_to_smt_type_set (T : Term) :
    __eo_to_smt_type (Term.Apply Term.Set T) =
      SmtType.Map (__eo_to_smt_type T) SmtType.Bool := by
  simp [__eo_to_smt_type]

end TranslationProofs
