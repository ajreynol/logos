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

inductive TypedListShape : Term -> Prop where
  | nil (T : Term) :
      TypedListShape (Term.Apply (Term.UOp UserOp._at__at_TypedList_nil) T)
  | cons (x xs : Term) :
      TypedListShape xs ->
      TypedListShape
        (Term.Apply
          (Term.Apply (Term.UOp UserOp._at__at_TypedList_cons) x) xs)

theorem typed_list_elem_type_non_none_not_stuck
    {xs : Term}
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    xs ≠ Term.Stuck := by
  intro h
  subst xs
  exact hElemNN (by simp [__eo_to_smt_typed_list_elem_type])

theorem typed_list_shape_of_elem_type_non_none :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      TypedListShape xs := by
  intro xs hNN
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            exact TypedListShape.nil tail
          all_goals
            exact False.elim
              (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                have hTailNN :
                    __eo_to_smt_typed_list_elem_type tail ≠ SmtType.None := by
                  intro hTail
                  apply hNN
                  cases hHead : __smtx_typeof (__eo_to_smt head) <;>
                    simp [__eo_to_smt_typed_list_elem_type, hHead, hTail,
                      native_ite, native_Teq]
                exact TypedListShape.cons head tail
                  (typed_list_shape_of_elem_type_non_none tail hTailNN)
              all_goals
                exact False.elim
                  (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim (hNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by xs _ => xs

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

theorem typed_list_elem_type_non_none_of_distinct_has_smt_translation
    {xs : Term}
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.distinct) xs)) :
    __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
  unfold RuleProofs.eo_has_smt_translation at hTrans
  change
      __smtx_typeof
          (native_ite
            (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
            SmtTerm.None (__eo_to_smt_distinct xs)) ≠
        SmtType.None at hTrans
  intro hNone
  exact hTrans (by
    simp [hNone, native_ite, TranslationProofs.smtx_typeof_none])

theorem eo_typeof_distinct_eq_bool_of_elem_type_non_none
    (xs : Term)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.distinct) xs) = Term.Bool := by
  rcases
      TranslationProofs.eo_to_smt_typed_list_elem_type_of_non_none
        xs hElemNN with
    ⟨T, hType, _hSmt, _hValid⟩
  change __eo_typeof_distinct (__eo_typeof xs) = Term.Bool
  rw [hType]
  rfl

theorem eo_typeof_distinct_ne_stuck_of_elem_type_non_none
    (xs : Term)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    __eo_typeof (Term.Apply (Term.UOp UserOp.distinct) xs) ≠ Term.Stuck := by
  rw [eo_typeof_distinct_eq_bool_of_elem_type_non_none xs hElemNN]
  intro h
  cases h

theorem smtx_typeof_distinct_pairs_of_elem_type :
    ∀ (s : SmtTerm) (xs : Term),
      __smtx_typeof s = __eo_to_smt_typed_list_elem_type xs ->
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt_distinct_pairs s xs) = SmtType.Bool := by
  intro s xs hS hElemNN
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
            rw [__smtx_typeof.eq_1]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                rcases typed_list_cons_elem_type_parts head tail hElemNN with
                  ⟨hHeadTail, hHeadNN, hTailNN, hConsEq⟩
                have hSElem :
                    __smtx_typeof s = __smtx_typeof (__eo_to_smt head) := by
                  rw [hS, hConsEq]
                have hEqBool :
                    __smtx_typeof
                      (SmtTerm.eq s (__eo_to_smt head)) = SmtType.Bool := by
                  rw [typeof_eq_eq]
                  exact (RuleProofs.smtx_typeof_eq_bool_iff
                    (__smtx_typeof s)
                    (__smtx_typeof (__eo_to_smt head))).mpr
                    ⟨hSElem, by rw [hSElem]; exact hHeadNN⟩
                have hNotBool :
                    __smtx_typeof
                      (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head))) =
                        SmtType.Bool := by
                  rw [typeof_not_eq, hEqBool]
                  rfl
                have hRec :
                    __smtx_typeof
                      (__eo_to_smt_distinct_pairs s tail) = SmtType.Bool :=
                  smtx_typeof_distinct_pairs_of_elem_type s tail
                    (hSElem.trans hHeadTail)
                    hTailNN
                change
                  __smtx_typeof
                    (SmtTerm.and
                      (SmtTerm.not (SmtTerm.eq s (__eo_to_smt head)))
                      (__eo_to_smt_distinct_pairs s tail)) = SmtType.Bool
                rw [typeof_and_eq, hNotBool, hRec]
                rfl
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by s xs _ _ => xs

theorem smtx_typeof_distinct_of_elem_type_non_none :
    ∀ xs,
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt_distinct xs) = SmtType.Bool := by
  intro xs hElemNN
  cases xs with
  | Apply f tail =>
      cases f with
      | UOp op =>
          cases op
          case _at__at_TypedList_nil =>
            change __smtx_typeof (SmtTerm.Boolean true) = SmtType.Bool
            rw [__smtx_typeof.eq_1]
          all_goals
            exact False.elim
              (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                rcases typed_list_cons_elem_type_parts head tail hElemNN with
                  ⟨hHeadTail, _hHeadNN, hTailNN, _hConsEq⟩
                have hPairs :
                    __smtx_typeof
                      (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail) =
                        SmtType.Bool :=
                  smtx_typeof_distinct_pairs_of_elem_type
                    (__eo_to_smt head) tail hHeadTail hTailNN
                have hTailDistinct :
                    __smtx_typeof (__eo_to_smt_distinct tail) =
                      SmtType.Bool :=
                  smtx_typeof_distinct_of_elem_type_non_none tail hTailNN
                change
                  __smtx_typeof
                    (SmtTerm.and
                      (__eo_to_smt_distinct_pairs (__eo_to_smt head) tail)
                      (__eo_to_smt_distinct tail)) = SmtType.Bool
                rw [typeof_and_eq, hPairs, hTailDistinct]
                rfl
              all_goals
                exact False.elim
                  (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
          | _ =>
              exact False.elim
                (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
      | _ =>
          exact False.elim
            (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
  | _ =>
      exact False.elim (hElemNN (by simp [__eo_to_smt_typed_list_elem_type]))
termination_by xs _ => xs

theorem eo_has_smt_translation_distinct_of_elem_type_non_none
    (xs : Term)
    (hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.distinct) xs) := by
  unfold RuleProofs.eo_has_smt_translation
  rw [eo_to_smt_distinct_eq_of_elem_type_non_none xs hElemNN]
  rw [smtx_typeof_distinct_of_elem_type_non_none xs hElemNN]
  simp

end TypedListSubstitutionSupport
