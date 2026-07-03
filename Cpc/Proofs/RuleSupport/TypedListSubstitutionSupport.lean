import Cpc.Proofs.RuleSupport.SubstituteTypeSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/-!
# Typed-list substitution support

This module collects typed-list facts needed by substitution preservation
lemmas whose SMT translation is not obtained by translating the typed-list term
as an ordinary EO subterm. The motivating examples are `distinct` and
`set_insert`: their arguments are inspected through
`__eo_to_smt_typed_list_elem_type`.
-/

namespace TypedListSubstitutionSupport

theorem typed_list_elem_type_non_none_not_stuck
    {xs : Term}
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    xs ≠ Term.Stuck := by
  intro h
  subst xs
  exact hElemNN (by simp [__eo_to_smt_typed_list_elem_type])

theorem typed_list_cons_elem_type_parts
    (x xs : Term)
    (hNN :
      __eo_to_smt_typed_list_elem_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt x) =
        __eo_to_smt_typed_list_elem_type xs ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ∧
      __eo_to_smt_typed_list_elem_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) =
        __smtx_typeof (__eo_to_smt x) := by
  let headTy := __smtx_typeof (__eo_to_smt x)
  let tailTy := __eo_to_smt_typed_list_elem_type xs
  have hEqBool : native_Teq headTy tailTy = true := by
    cases hEq : native_Teq headTy tailTy <;>
      simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy, native_ite, hEq]
        at hNN ⊢
  have hHeadTail : headTy = tailTy := by
    simpa [native_Teq] using hEqBool
  have hHeadNN : headTy ≠ SmtType.None := by
    intro hHeadNone
    apply hNN
    simp [__eo_to_smt_typed_list_elem_type, headTy, native_ite, hHeadNone]
  have hTailNN : tailTy ≠ SmtType.None := by
    rw [← hHeadTail]
    exact hHeadNN
  have hConsEq :
      __eo_to_smt_typed_list_elem_type
          (Term.Apply
            (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs) =
        headTy := by
    simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy, native_ite,
      hEqBool]
  exact ⟨hHeadTail, hHeadNN, hTailNN, hConsEq⟩

theorem typed_list_nil_elem_type_eq_of_non_none
    (T : Term)
    (hNN :
      __eo_to_smt_typed_list_elem_type
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) ≠
        SmtType.None) :
    __eo_to_smt_typed_list_elem_type
        (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T) =
      __eo_to_smt_type T := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type T) <;>
    simp [__eo_to_smt_typed_list_elem_type, hWf, native_ite] at hNN ⊢

theorem native_Teq_none_false_of_non_none
    {T : SmtType}
    (h : T ≠ SmtType.None) :
    native_Teq T SmtType.None = false := by
  cases T <;> simp [native_Teq] at h ⊢

theorem eo_to_smt_distinct_eq_of_elem_type_non_none
    (xs : Term)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs) =
      __eo_to_smt_distinct xs := by
  change
    native_ite (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
      SmtTerm.None (__eo_to_smt_distinct xs) =
      __eo_to_smt_distinct xs
  rw [native_Teq_none_false_of_non_none hElemNN]
  simp [native_ite]

end TypedListSubstitutionSupport
