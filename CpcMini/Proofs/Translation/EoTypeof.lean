import CpcMini.Proofs.Translation.Datatypes

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Computes `__smtx_typeof_guard` under a non-`None` premise. -/
theorem smtx_typeof_guard_of_non_none
    (T U : SmtType) (h : T ≠ SmtType.None) :
    __smtx_typeof_guard T U = U := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq] at h ⊢

/-- Selector return typing commutes with EO-to-SMT type translation. -/
theorem eo_to_smt_type_typeof_dt_sel_return :
    ∀ d : Datatype, ∀ i j : native_Nat,
      __eo_to_smt_type (__eo_typeof_dt_sel_return d i j) =
        __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_zero => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons]
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_succ j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return (Datatype.sum c d) native_nat_zero j
  | Datatype.sum c d, native_nat_succ i, j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return d i j
  | Datatype.null, i, j => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_type]
  | Datatype.sum DatatypeCons.unit d, native_nat_zero, j => by
      cases j <;> simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons, __eo_to_smt_type]
termination_by d i j => sizeOf d + i + j

/-- Selector return typing commutes with EO-to-SMT type translation on the EO-side substituted datatype. -/
theorem eo_to_smt_type_typeof_dt_sel_return_on_substituted_datatype
    (s : native_String) (d : Datatype) (i j : native_Nat) :
    __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) =
      __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype (__eo_dt_substitute s d d)) i j := by
  simpa using eo_to_smt_type_typeof_dt_sel_return (__eo_dt_substitute s d d) i j

/--
If the EO argument already has the exact datatype expected by a selector, the
translated EO result type matches the SMT selector return type.
-/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_exact_eo_datatype
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hx : __eo_typeof x = Term.DatatypeType s d) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype (__eo_dt_substitute s d d)) i j := by
  simp [__eo_typeof, __eo_typeof_apply, __eo_requires, hx,
    eo_to_smt_type_typeof_dt_sel_return_on_substituted_datatype,
    native_ite, native_teq, native_not]

end TranslationProofs
