import Cpc.Proofs.Translation.Base

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Computes `__eo_typeof` for `tuple_unit`. -/
@[simp] theorem eo_typeof_tuple_unit :
    __eo_typeof Term.tuple_unit = Term.UnitTuple := by
  native_decide

/-- Simplifies EO-to-SMT translation for `term_tuple_unit`. -/
@[simp] theorem eo_to_smt_term_tuple_unit :
    __eo_to_smt Term.tuple_unit =
      SmtTerm.DtCons "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) 0 := by
  simp [__eo_to_smt.eq_def]

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
    __eo_to_smt_type (Term.DatatypeType s d) =
      SmtType.Datatype s (__eo_to_smt_datatype d) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `unit_tuple`. -/
@[simp] theorem eo_to_smt_type_unit_tuple :
    __eo_to_smt_type Term.UnitTuple =
      SmtType.Datatype "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT type translation for `tuple_step`. -/
@[simp] theorem eo_to_smt_type_tuple_step (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.Tuple T) U) =
      __eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U) := by
  simp [__eo_to_smt_type]

/-- Simplifies EO-to-SMT translation for `tester_of_dtcons`. -/
@[simp] theorem eo_to_smt_tester_of_dtcons
    (s : native_String) (d : SmtDatatype) (n : native_Nat) :
    __eo_to_smt_tester (SmtTerm.DtCons s d n) = SmtTerm.DtTester s d n := rfl

/-- Computes `__smtx_typeof` for `dt_sel_head_none`. -/
@[simp] theorem smtx_typeof_dt_sel_head_none
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := rfl

/-- Computes `__smtx_typeof` for `eo_to_smt_tester_none`. -/
@[simp] theorem smtx_typeof_eo_to_smt_tester_none
    (t : SmtTerm) :
    __smtx_typeof (__eo_to_smt_tester t) = SmtType.None := by
  cases t <;> simp [__eo_to_smt_tester, __smtx_typeof]

/-- Computes `__smtx_typeof` for `tuple_unit_translation`. -/
theorem smtx_typeof_tuple_unit_translation :
    __smtx_typeof
        (SmtTerm.DtCons "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) 0) =
      SmtType.Datatype "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) := by
  change
    __smtx_typeof_dt_cons_rec
        (SmtType.Datatype "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null))
        (__smtx_dt_substitute "_at_Tuple"
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) 0 =
      SmtType.Datatype "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
  simp [__smtx_dt_substitute, __smtx_dtc_substitute, __smtx_typeof_dt_cons_rec]

end TranslationProofs
