import CpcMini.Proofs.Translation.Base

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `term_dt_cons`. -/
@[simp] theorem eo_to_smt_term_dt_cons
    (s : native_String) (d : Datatype) (i : native_Nat) :
    __eo_to_smt (Term.DtCons s d i) =
      native_ite (native_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) := by
  rfl

/-- Simplifies EO-to-SMT translation for `term_dt_sel`. -/
@[simp] theorem eo_to_smt_term_dt_sel
    (s : native_String) (d : Datatype) (i j : native_Nat) :
    __eo_to_smt (Term.DtSel s d i j) =
      native_ite (native_reserved_datatype_name s) SmtTerm.None
        (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) := by
  rfl

/-- Simplifies EO-to-SMT translation for `datatype_cons_unit`. -/
@[simp] theorem eo_to_smt_datatype_cons_unit :
    __eo_to_smt_datatype_cons DatatypeCons.unit = SmtDatatypeCons.unit := rfl

/-- Simplifies EO-to-SMT translation for `datatype_null`. -/
@[simp] theorem eo_to_smt_datatype_null :
    __eo_to_smt_datatype Datatype.null = SmtDatatype.null := rfl

/-- Simplifies EO-to-SMT type translation for `datatype`. -/
@[simp] theorem eo_to_smt_type_datatype (s : native_String) (d : Datatype) :
    __eo_to_smt_type (Term.DatatypeType s d) =
      native_ite (native_reserved_datatype_name s) SmtType.None
        (SmtType.Datatype s (__eo_to_smt_datatype d)) := by
  rfl

/-- Computes `__smtx_typeof` for `dt_sel_head_none`. -/
@[simp] theorem smtx_typeof_dt_sel_head_none
    (s : native_String) (d : SmtDatatype) (i j : native_Nat) :
    __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := by
  simp [__smtx_typeof.eq_def]

end TranslationProofs
