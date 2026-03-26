import Cpc.TypePreservation.Helpers

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

theorem typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero
    (T : SmtType) :
    ∀ c d,
      __smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) smt_lit_nat_zero =
        __smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) smt_lit_nat_zero
  | SmtDatatypeCons.unit, d => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec]
  | SmtDatatypeCons.cons U c, d => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec,
        typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero T c d]

theorem typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec
    (T : SmtType) :
    ∀ d n,
      __smtx_typeof_dt_cons_value_rec T d n =
        __smtx_typeof_dt_cons_rec T d n
  | SmtDatatype.null, n => by
      cases n <;> simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec]
  | SmtDatatype.sum c d, smt_lit_nat_zero =>
      typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero T c d
  | SmtDatatype.sum c d, smt_lit_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec] using
        typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec T d n

theorem typeof_value_model_eval_dt_cons
    (M : SmtModel)
    (s : smt_lit_String)
    (d : SmtDatatype)
    (i : smt_lit_Nat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s d i) := by
  change
    __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i =
      __smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i
  exact typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec (SmtType.Datatype s d)
    (__smtx_dt_substitute s d d) i

theorem dt_tester_arg_datatype_of_non_none
    {s : smt_lit_String}
    {d : SmtDatatype}
    {i : smt_lit_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof x = SmtType.Datatype s d := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof x <;>
    simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite,
      smt_lit_Teq, h] at ht ⊢
  rcases ht with ⟨rfl, rfl⟩
  simp

theorem dt_tester_term_typeof_of_non_none
    {s : smt_lit_String}
    {d : SmtDatatype}
    {i : smt_lit_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) = SmtType.Bool := by
  have hx : __smtx_typeof x = SmtType.Datatype s d := dt_tester_arg_datatype_of_non_none ht
  simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx]

theorem typeof_value_model_eval_dt_tester
    (M : SmtModel)
    (s : smt_lit_String)
    (d : SmtDatatype)
    (i : smt_lit_Nat)
    (x : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) := by
  rw [dt_tester_term_typeof_of_non_none ht]
  change
    __smtx_typeof_value (__smtx_model_eval_dt_tester s d i (__smtx_model_eval M x)) =
      SmtType.Bool
  simp [__smtx_model_eval_dt_tester, __smtx_typeof_value]

def dt_sel_counterexample_datatype : SmtDatatype :=
  SmtDatatype.sum
    (SmtDatatypeCons.cons (SmtType.TypeRef "R") SmtDatatypeCons.unit)
    (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)

def dt_sel_counterexample_arg : SmtTerm :=
  SmtTerm.DtCons "R" dt_sel_counterexample_datatype (smt_lit_nat_succ smt_lit_nat_zero)

def dt_sel_counterexample : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.DtSel "R" dt_sel_counterexample_datatype smt_lit_nat_zero smt_lit_nat_zero)
    dt_sel_counterexample_arg

theorem dt_sel_counterexample_typeof :
    __smtx_typeof dt_sel_counterexample = SmtType.Datatype "R" dt_sel_counterexample_datatype := by
  simp [dt_sel_counterexample, dt_sel_counterexample_arg, dt_sel_counterexample_datatype,
    __smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, __smtx_typeof_dt_cons_rec,
    __smtx_ret_typeof_sel, __smtx_dt_substitute, __smtx_dtc_substitute, smt_lit_ite,
    smt_lit_Teq]

theorem dt_sel_counterexample_has_non_none_type :
    term_has_non_none_type dt_sel_counterexample := by
  simp [term_has_non_none_type, dt_sel_counterexample_typeof]

theorem dt_sel_counterexample_arg_eval :
    __smtx_model_eval SmtModel.empty dt_sel_counterexample_arg =
      SmtValue.DtCons "R" dt_sel_counterexample_datatype (smt_lit_nat_succ smt_lit_nat_zero) := by
  rfl

theorem dt_sel_counterexample_eval :
    __smtx_model_eval SmtModel.empty dt_sel_counterexample = SmtValue.NotValue := by
  change
    __smtx_model_eval_dt_sel SmtModel.empty "R" dt_sel_counterexample_datatype
      smt_lit_nat_zero smt_lit_nat_zero
      (__smtx_model_eval SmtModel.empty dt_sel_counterexample_arg) =
        SmtValue.NotValue
  rw [dt_sel_counterexample_arg_eval]
  simp [SmtModel.empty, __smtx_model_eval_dt_sel, __smtx_map_select, __smtx_model_lookup,
    __vsm_apply_head, smt_lit_ite, smt_lit_veq]

theorem dt_sel_counterexample_value_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty dt_sel_counterexample) = SmtType.None := by
  rw [dt_sel_counterexample_eval]
  rfl

theorem dt_sel_counterexample_not_preserved :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty dt_sel_counterexample) ≠
      __smtx_typeof dt_sel_counterexample := by
  rw [dt_sel_counterexample_value_typeof, dt_sel_counterexample_typeof]
  simp

end Smtm
