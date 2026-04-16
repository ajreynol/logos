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

/-- A translated sequence type is never an SMT type reference. -/
theorem smtx_typeof_guard_seq_ne_typeref
    (T : SmtType) (s : native_String) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.TypeRef s := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT type reference. -/
theorem smtx_typeof_guard_fun_ne_typeref
    (T U : SmtType) (s : native_String) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠
      SmtType.TypeRef s := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT type reference. -/
theorem smtx_typeof_guard_dtc_app_ne_typeref
    (T U : SmtType) (s : native_String) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠
      SmtType.TypeRef s := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- An EO application never translates to an SMT type reference. -/
theorem eo_to_smt_type_apply_ne_typeref
    (f x : Term) (s : native_String) :
    __eo_to_smt_type (Term.Apply f x) ≠ SmtType.TypeRef s := by
  cases f with
  | BitVec =>
      cases x with
      | Numeral n =>
          by_cases hz : native_zleq 0 n = true
          · simp [__eo_to_smt_type, native_ite, hz]
          · simp [__eo_to_smt_type, native_ite, hz]
      | _ =>
          simp [__eo_to_smt_type]
  | Seq =>
      simpa [__eo_to_smt_type] using
        smtx_typeof_guard_seq_ne_typeref (__eo_to_smt_type x) s
  | Apply f1 x1 =>
      cases f1 <;>
        simp [__eo_to_smt_type, smtx_typeof_guard_fun_ne_typeref]
  | _ =>
      simp [__eo_to_smt_type]

/-- Translating EO type-reference substitution matches the corresponding SMT substitution step. -/
theorem eo_to_smt_type_substitute_typeref
    (s : native_String) (d : Datatype) :
    ∀ T : Term,
      __eo_to_smt_type
          (native_ite (native_teq T (Term.DatatypeTypeRef s))
            (Term.DatatypeType s d) T) =
        native_ite (native_Teq (__eo_to_smt_type T) (SmtType.TypeRef s))
          (SmtType.Datatype s (__eo_to_smt_datatype d))
          (__eo_to_smt_type T)
  | Term.__eo_pf t => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Int => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Real => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.BitVec => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Char => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Seq => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List_nil => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List_cons => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Bool => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Boolean b => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Numeral n => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Rational q => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.String str => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Binary w n => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Type => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Stuck => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Apply f x => by
      have hneq : __eo_to_smt_type (Term.Apply f x) ≠ SmtType.TypeRef s :=
        eo_to_smt_type_apply_ne_typeref f x s
      simp [native_ite, native_teq, native_Teq, hneq]
  | Term.FunType => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Var name ty => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DatatypeType s2 d2 => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DatatypeTypeRef s2 => by
      by_cases hs : s2 = s
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hs]
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hs]
  | Term.DtcAppType T U => by
      let V :=
        __smtx_typeof_guard (__eo_to_smt_type T)
          (__smtx_typeof_guard (__eo_to_smt_type U)
            (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)))
      have hneq : V ≠ SmtType.TypeRef s := by
        dsimp [V]
        exact smtx_typeof_guard_dtc_app_ne_typeref (__eo_to_smt_type T) (__eo_to_smt_type U) s
      by_cases hV : V = SmtType.TypeRef s
      · exact False.elim (hneq hV)
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, V, hV]
  | Term.DtCons s2 d2 i => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DtSel s2 d2 i j => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.USort u => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.UConst i T => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.not => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.or => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.and => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.imp => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.eq => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]

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

/--
The selector-return bridge already works on the EO-side substituted datatype.

Upgrading this to the final SMT-side substituted datatype will need a separate
commutation lemma for `__eo_dt_substitute` and `__smtx_dt_substitute`.
-/
theorem eo_to_smt_type_typeof_dt_sel_return_on_eo_substituted_datatype
    (s : native_String) (d : Datatype) (i j : native_Nat) :
    __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) =
      __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype (__eo_dt_substitute s d d)) i j := by
  simpa using eo_to_smt_type_typeof_dt_sel_return (__eo_dt_substitute s d d) i j

end TranslationProofs
