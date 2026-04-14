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
    (s : eo_lit_String) (d : Datatype) (i : eo_lit_Nat) :
    __eo_to_smt (Term.DtCons s d i) =
      smt_lit_ite (__smtx_type_eo_safe (SmtType.Datatype s (__eo_to_smt_datatype d)))
        (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) SmtTerm.None := by
  simp [__eo_to_smt.eq_def]

/-- Removes the EO datatype-safety guard from `term_dt_cons` under a non-`None` translation hypothesis. -/
theorem eo_to_smt_term_dt_cons_of_non_none
    (s : eo_lit_String) (d : Datatype) (i : eo_lit_Nat) :
    __eo_to_smt (Term.DtCons s d i) ≠ SmtTerm.None ->
    __eo_to_smt (Term.DtCons s d i) = SmtTerm.DtCons s (__eo_to_smt_datatype d) i := by
  intro h
  rw [eo_to_smt_term_dt_cons] at h ⊢
  cases hSafe : __smtx_type_eo_safe (SmtType.Datatype s (__eo_to_smt_datatype d)) <;>
    simp [smt_lit_ite, hSafe] at h ⊢

/-- Simplifies EO-to-SMT translation for `term_dt_sel`. -/
@[simp] theorem eo_to_smt_term_dt_sel
    (s : eo_lit_String) (d : Datatype) (i j : eo_lit_Nat) :
    __eo_to_smt (Term.DtSel s d i j) =
      smt_lit_ite (__smtx_type_eo_safe (SmtType.Datatype s (__eo_to_smt_datatype d)))
        (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) SmtTerm.None := by
  simp [__eo_to_smt.eq_def]

/-- Removes the EO datatype-safety guard from `term_dt_sel` under a non-`None` translation hypothesis. -/
theorem eo_to_smt_term_dt_sel_of_non_none
    (s : eo_lit_String) (d : Datatype) (i j : eo_lit_Nat) :
    __eo_to_smt (Term.DtSel s d i j) ≠ SmtTerm.None ->
    __eo_to_smt (Term.DtSel s d i j) = SmtTerm.DtSel s (__eo_to_smt_datatype d) i j := by
  intro h
  rw [eo_to_smt_term_dt_sel] at h ⊢
  cases hSafe : __smtx_type_eo_safe (SmtType.Datatype s (__eo_to_smt_datatype d)) <;>
    simp [smt_lit_ite, hSafe] at h ⊢

/-- Simplifies EO-to-SMT translation for `datatype_cons_unit`. -/
@[simp] theorem eo_to_smt_datatype_cons_unit :
    __eo_to_smt_datatype_cons DatatypeCons.unit = SmtDatatypeCons.unit := rfl

/-- Simplifies EO-to-SMT translation for `datatype_null`. -/
@[simp] theorem eo_to_smt_datatype_null :
    __eo_to_smt_datatype Datatype.null = SmtDatatype.null := rfl

/-- Simplifies EO-to-SMT type translation for `datatype`. -/
@[simp] theorem eo_to_smt_type_datatype (s : eo_lit_String) (d : Datatype) :
    __eo_to_smt_type (Term.DatatypeType s d) =
      __smtx_typeof_guard_eo_safe
        (SmtType.Datatype s (__eo_to_smt_datatype d))
        (SmtType.Datatype s (__eo_to_smt_datatype d)) := by
  simp [__eo_to_smt_type]

/-- Removes the EO datatype-safety guard from `datatype` types under a non-`None` translation hypothesis. -/
theorem eo_to_smt_type_datatype_of_non_none (s : eo_lit_String) (d : Datatype) :
    __eo_to_smt_type (Term.DatatypeType s d) ≠ SmtType.None ->
    __eo_to_smt_type (Term.DatatypeType s d) = SmtType.Datatype s (__eo_to_smt_datatype d) := by
  intro h
  rw [eo_to_smt_type_datatype]
  exact smtx_typeof_guard_eo_safe_of_non_none
    (SmtType.Datatype s (__eo_to_smt_datatype d))
    (SmtType.Datatype s (__eo_to_smt_datatype d)) h

/-- Computes `__smtx_typeof` for `dt_sel_head_none`. -/
@[simp] theorem smtx_typeof_dt_sel_head_none
    (s : smt_lit_String) (d : SmtDatatype) (i j : smt_lit_Nat) :
    __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := rfl

end TranslationProofs
