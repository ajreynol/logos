import CpcMicro.Proofs.Translation.Base

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

@[simp] theorem eo_to_smt_term_dt_cons
    (s : eo_lit_String) (d : Datatype) (i : eo_lit_Nat) :
    __eo_to_smt (Term.DtCons s d i) = SmtTerm.None := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_term_dt_sel
    (s : eo_lit_String) (d : Datatype) (i j : eo_lit_Nat) :
    __eo_to_smt (Term.DtSel s d i j) = SmtTerm.None := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_datatype_cons_unit :
    __eo_to_smt_datatype_cons DatatypeCons.unit = SmtDatatypeCons.unit := rfl

@[simp] theorem eo_to_smt_datatype_null :
    __eo_to_smt_datatype Datatype.null = SmtDatatype.null := rfl

@[simp] theorem eo_to_smt_type_datatype (s : eo_lit_String) (d : Datatype) :
    __eo_to_smt_type (Term.DatatypeType s d) = SmtType.None := by
  simp [__eo_to_smt_type]

@[simp] theorem smtx_typeof_dt_sel_head_none
    (s : eo_lit_String) (d : Datatype) (i j : eo_lit_Nat) :
    __smtx_typeof (__eo_to_smt (Term.DtSel s d i j)) = SmtType.None := by
  simp [__eo_to_smt.eq_def, __smtx_typeof]

end TranslationProofs
