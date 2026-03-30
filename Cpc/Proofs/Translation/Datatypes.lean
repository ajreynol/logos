import Cpc.Proofs.Translation.Base

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

@[simp] theorem eo_to_smt_datatype_cons_unit :
    __eo_to_smt_datatype_cons DatatypeCons.unit = SmtDatatypeCons.unit := rfl

@[simp] theorem eo_to_smt_datatype_null :
    __eo_to_smt_datatype Datatype.null = SmtDatatype.null := rfl

@[simp] theorem eo_to_smt_type_datatype (s : eo_lit_String) (d : Datatype) :
    __eo_to_smt_type (Term.DatatypeType s d) =
      SmtType.Datatype s (__eo_to_smt_datatype d) := by
  simp [__eo_to_smt_type]

@[simp] theorem eo_to_smt_type_unit_tuple :
    __eo_to_smt_type Term.UnitTuple =
      SmtType.Datatype "_at_Tuple" (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) := by
  simp [__eo_to_smt_type]

@[simp] theorem eo_to_smt_type_tuple_step (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.Tuple T) U) =
      __eo_to_smt_type_tuple (__eo_to_smt_type T) (__eo_to_smt_type U) := by
  simp [__eo_to_smt_type]

@[simp] theorem eo_to_smt_tester_of_dtcons
    (s : smt_lit_String) (d : SmtDatatype) (n : smt_lit_Nat) :
    __eo_to_smt_tester (SmtTerm.DtCons s d n) = SmtTerm.DtTester s d n := rfl

end TranslationProofs
