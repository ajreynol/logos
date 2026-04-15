import CpcMini.Proofs.Translation.Base

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `term_dt_cons`. -/
@[simp] theorem eo_to_smt_term_dt_cons
    (s : native_String) (d : Datatype) (i : native_Nat) :
    __eo_to_smt (Term.DtCons s d i) = SmtTerm.DtCons s (__eo_to_smt_datatype d) i := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `term_dt_sel`. -/
@[simp] theorem eo_to_smt_term_dt_sel
    (s : native_String) (d : Datatype) (i j : native_Nat) :
    __eo_to_smt (Term.DtSel s d i j) = SmtTerm.DtSel s (__eo_to_smt_datatype d) i j := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `datatype_cons_unit`. -/
@[simp] theorem eo_to_smt_datatype_cons_unit :
    __eo_to_smt_datatype_cons DatatypeCons.unit = SmtDatatypeCons.unit := rfl

/-- Simplifies EO-to-SMT translation for `datatype_null`. -/
@[simp] theorem eo_to_smt_datatype_null :
    __eo_to_smt_datatype Datatype.null = SmtDatatype.null := rfl

/-- Simplifies EO-to-SMT type translation for `datatype`. -/
@[simp] theorem eo_to_smt_type_datatype (s : native_String) (d : Datatype) :
    __eo_to_smt_type (Term.DatatypeType s d) = SmtType.Datatype s (__eo_to_smt_datatype d) := by
  simp [__eo_to_smt_type]

/-- Computes `__smtx_typeof` for `dt_sel_head_none`. -/
@[simp] theorem smtx_typeof_dt_sel_head_none
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := rfl

end TranslationProofs
