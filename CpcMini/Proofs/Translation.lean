import CpcMini.Proofs.Translation.Datatypes
import CpcMini.Proofs.Translation.Apply
import CpcMini.Proofs.TypePreservation.Datatypes

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-!
This file is the staging area for the `CpcMini` EO-to-SMT translation typing
port.

Unlike `Cpc`, the current mini `__eo_to_smt_type` only translates first-order EO
types, so the full wrapper theorem from `Cpc/Proofs/Translation.lean` is too
strong for constructor heads whose SMT translation has a function-like datatype
type. The port here therefore focuses on the fragment that already lines up
cleanly in `CpcMini`:

1. Direct translation helpers for literals and symbols.
2. Datatype head translation helpers.
3. Fully translated boolean/equality applications.
-/

inductive supported_bool_translation_term : Term -> Prop where
  | boolean (b : eo_lit_Bool) :
      supported_bool_translation_term (Term.Boolean b)
  | «not» (x : Term) :
      supported_bool_translation_term (Term.Apply Term.not x)
  | «or» (x y : Term) :
      supported_bool_translation_term (Term.Apply (Term.Apply Term.or x) y)
  | «and» (x y : Term) :
      supported_bool_translation_term (Term.Apply (Term.Apply Term.and x) y)
  | «imp» (x y : Term) :
      supported_bool_translation_term (Term.Apply (Term.Apply Term.imp x) y)
  | eq (x y : Term) :
      supported_bool_translation_term (Term.Apply (Term.Apply Term.eq x) y)

theorem eo_to_smt_supported_bool_term_has_bool_smt_type
    {t : Term} :
    supported_bool_translation_term t ->
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
  intro hs hNonNone
  cases hs with
  | boolean b =>
      simp [__eo_to_smt.eq_def, __smtx_typeof]
  | not x =>
      simpa using smtx_typeof_translation_not_of_non_none x hNonNone
  | or x y =>
      simpa using smtx_typeof_translation_or_of_non_none x y hNonNone
  | and x y =>
      simpa using smtx_typeof_translation_and_of_non_none x y hNonNone
  | imp x y =>
      simpa using smtx_typeof_translation_imp_of_non_none x y hNonNone
  | eq x y =>
      simpa using smtx_typeof_translation_eq_of_non_none x y hNonNone

/--
Compatibility wrapper in the shape used by the mini proofs. The EO typing
assumption is redundant for this supported fragment, but we keep it in the
statement to match the eventual full theorem shape.
-/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool_of_supported
    {t : Term} (s : SmtTerm) :
    supported_bool_translation_term t ->
    __eo_to_smt t = s ->
    __smtx_typeof s ≠ SmtType.None ->
    __eo_typeof t = Term.Bool ->
    __smtx_typeof s = SmtType.Bool := by
  intro hs hsmt hNonNone _hTy
  subst s
  exact eo_to_smt_supported_bool_term_has_bool_smt_type hs hNonNone

private theorem eo_requires_eq_bool
    {T X U : Term} :
    __eo_requires T X U = Term.Bool ->
      T = X ∧ T ≠ Term.Stuck ∧ U = Term.Bool := by
  intro h
  by_cases hEq : T = X
  · by_cases hStuck : T = Term.Stuck
    · subst X
      subst T
      have : False := by
        simpa [__eo_requires, eo_lit_teq, eo_lit_ite, SmtEval.smt_lit_not] using h
      exact False.elim this
    · have hU : U = Term.Bool := by
        subst X
        simpa [__eo_requires, eo_lit_teq, eo_lit_not, eo_lit_ite, hStuck] using h
      exact ⟨hEq, hStuck, hU⟩
  · simp [__eo_requires, eo_lit_ite, eo_lit_teq, eo_lit_not, hEq] at h

private theorem eo_requires_fun_ends_in_bool
    {T X U : Term} :
    eo_fun_ends_in_bool (__eo_requires T X U) ->
      T = X ∧ T ≠ Term.Stuck ∧ eo_fun_ends_in_bool U := by
  intro h
  by_cases hEq : T = X
  · by_cases hStuck : T = Term.Stuck
    · subst X
      subst T
      have : False := by
        simpa [__eo_requires, eo_lit_teq, eo_lit_ite, SmtEval.smt_lit_not,
          eo_fun_ends_in_bool] using h
      exact False.elim this
    · have hU : eo_fun_ends_in_bool U := by
        subst X
        simpa [__eo_requires, eo_lit_teq, eo_lit_not, eo_lit_ite, hStuck,
          eo_fun_ends_in_bool] using h
      exact ⟨hEq, hStuck, hU⟩
  · simp [__eo_requires, eo_lit_ite, eo_lit_teq, eo_lit_not, hEq,
      eo_fun_ends_in_bool] at h

private theorem eo_typeof_apply_eq_bool
    {F X : Term} :
    __eo_typeof_apply F X = Term.Bool ->
      F = Term.Apply (Term.Apply Term.FunType X) Term.Bool := by
  intro h
  by_cases hX : X = Term.Stuck
  · subst X
    simp [__eo_typeof_apply] at h
  · cases F with
    | Apply F1 U =>
        cases F1 with
        | Apply F11 T =>
            cases F11 with
            | FunType =>
                obtain ⟨hEq, _hStuck, hU⟩ :=
                  eo_requires_eq_bool (T := T) (X := X) (U := U)
                    (by simpa [__eo_typeof_apply, hX] using h)
                subst hEq
                subst hU
                rfl
            | _ =>
                simp [__eo_typeof_apply, hX] at h
        | _ =>
            simp [__eo_typeof_apply, hX] at h
    | _ =>
        simp [__eo_typeof_apply, hX] at h

private theorem eo_fun_ends_in_bool_of_typeof_apply
    {F X : Term} :
    eo_fun_ends_in_bool (__eo_typeof_apply F X) ->
      eo_fun_ends_in_bool F := by
  intro h
  by_cases hX : X = Term.Stuck
  · subst X
    simp [__eo_typeof_apply, eo_fun_ends_in_bool] at h
  · cases F with
    | Apply F1 U =>
        cases F1 with
        | Apply F11 T =>
            cases F11 with
            | FunType =>
                obtain ⟨hEq, _hStuck, hU⟩ :=
                  eo_requires_fun_ends_in_bool (T := T) (X := X) (U := U)
                    (by simpa [__eo_typeof_apply, hX] using h)
                subst hEq
                simpa [eo_fun_ends_in_bool] using Or.inr hU
            | _ =>
                simp [__eo_typeof_apply, hX, eo_fun_ends_in_bool] at h
        | _ =>
            simp [__eo_typeof_apply, hX, eo_fun_ends_in_bool] at h
    | _ =>
        simp [__eo_typeof_apply, hX, eo_fun_ends_in_bool] at h

theorem eo_typeof_apply_eq_fun
    {F X A U : Term} :
    __eo_typeof_apply F X = Term.Apply (Term.Apply Term.FunType A) U ->
      F = Term.Apply (Term.Apply Term.FunType X) (Term.Apply (Term.Apply Term.FunType A) U) := by
  intro h
  by_cases hX : X = Term.Stuck
  · subst X
    simp [__eo_typeof_apply] at h
  · cases F with
    | Apply F1 V =>
        cases F1 with
        | Apply F11 T =>
            cases F11 with
            | FunType =>
                by_cases hEq : T = X
                · by_cases hStuck : T = Term.Stuck
                  · have : False := hX (hEq.symm.trans hStuck)
                    exact False.elim this
                  · have hV : V = Term.Apply (Term.Apply Term.FunType A) U := by
                      simpa [__eo_typeof_apply, __eo_requires, hX, hEq, hStuck,
                        eo_lit_ite, eo_lit_teq, eo_lit_not] using h
                    subst T
                    subst V
                    rfl
                · simp [__eo_typeof_apply, __eo_requires, hEq,
                    eo_lit_ite, eo_lit_teq] at h
            | _ =>
                simp [__eo_typeof_apply] at h
        | _ =>
            simp [__eo_typeof_apply] at h
    | _ =>
        simp [__eo_typeof_apply] at h

theorem eo_typeof_apply_fun_ends_in_bool_inv
    {F X : Term} :
    eo_fun_ends_in_bool (__eo_typeof_apply F X) ->
      ∃ A U,
        F = Term.Apply (Term.Apply Term.FunType X) (Term.Apply (Term.Apply Term.FunType A) U) ∧
          (U = Term.Bool ∨ eo_fun_ends_in_bool U) := by
  intro h
  cases hTy : __eo_typeof_apply F X with
  | Apply T1 U =>
      rw [hTy] at h
      cases T1 with
      | Apply T11 A =>
          cases T11 with
          | FunType =>
              simp [eo_fun_ends_in_bool] at h
              refine ⟨A, U, ?_, h⟩
              exact eo_typeof_apply_eq_fun (F := F) (X := X) (A := A) (U := U) hTy
          | _ =>
              simp [eo_fun_ends_in_bool] at h
      | _ =>
          simp [eo_fun_ends_in_bool] at h
  | _ =>
      rw [hTy] at h
      simp [eo_fun_ends_in_bool] at h

private theorem not_typeof_not_fun_ends_in_bool
    (x : Term) :
    ¬ eo_fun_ends_in_bool (__eo_typeof (Term.Apply Term.not x)) := by
  intro h
  rcases eo_typeof_apply_fun_ends_in_bool_inv
      (F := __eo_typeof Term.not) (X := __eo_typeof x)
      (by simpa [__eo_typeof] using h) with
    ⟨A, U, hF, _hU⟩
  simp [__eo_typeof] at hF

private theorem not_typeof_full_or_fun_ends_in_bool
    (x y : Term) :
    ¬ eo_fun_ends_in_bool (__eo_typeof (Term.Apply (Term.Apply Term.or y) x)) := by
  intro h
  rcases eo_typeof_apply_fun_ends_in_bool_inv
      (F := __eo_typeof (Term.Apply Term.or y)) (X := __eo_typeof x)
      (by simpa [__eo_typeof] using h) with
    ⟨A, U, hF, _hU⟩
  have hHead :
      __eo_typeof_apply (__eo_typeof Term.or) (__eo_typeof y) =
        Term.Apply (Term.Apply Term.FunType (__eo_typeof x))
          (Term.Apply (Term.Apply Term.FunType A) U) := by
    simpa [__eo_typeof] using hF
  have hInv :=
    eo_typeof_apply_eq_fun
      (F := __eo_typeof Term.or) (X := __eo_typeof y)
      (A := __eo_typeof x) (U := Term.Apply (Term.Apply Term.FunType A) U) hHead
  simp [__eo_typeof] at hInv

private theorem not_typeof_full_and_fun_ends_in_bool
    (x y : Term) :
    ¬ eo_fun_ends_in_bool (__eo_typeof (Term.Apply (Term.Apply Term.and y) x)) := by
  intro h
  rcases eo_typeof_apply_fun_ends_in_bool_inv
      (F := __eo_typeof (Term.Apply Term.and y)) (X := __eo_typeof x)
      (by simpa [__eo_typeof] using h) with
    ⟨A, U, hF, _hU⟩
  have hHead :
      __eo_typeof_apply (__eo_typeof Term.and) (__eo_typeof y) =
        Term.Apply (Term.Apply Term.FunType (__eo_typeof x))
          (Term.Apply (Term.Apply Term.FunType A) U) := by
    simpa [__eo_typeof] using hF
  have hInv :=
    eo_typeof_apply_eq_fun
      (F := __eo_typeof Term.and) (X := __eo_typeof y)
      (A := __eo_typeof x) (U := Term.Apply (Term.Apply Term.FunType A) U) hHead
  simp [__eo_typeof] at hInv

private theorem not_typeof_full_imp_fun_ends_in_bool
    (x y : Term) :
    ¬ eo_fun_ends_in_bool (__eo_typeof (Term.Apply (Term.Apply Term.imp y) x)) := by
  intro h
  rcases eo_typeof_apply_fun_ends_in_bool_inv
      (F := __eo_typeof (Term.Apply Term.imp y)) (X := __eo_typeof x)
      (by simpa [__eo_typeof] using h) with
    ⟨A, U, hF, _hU⟩
  have hHead :
      __eo_typeof_apply (__eo_typeof Term.imp) (__eo_typeof y) =
        Term.Apply (Term.Apply Term.FunType (__eo_typeof x))
          (Term.Apply (Term.Apply Term.FunType A) U) := by
    simpa [__eo_typeof] using hF
  have hInv :=
    eo_typeof_apply_eq_fun
      (F := __eo_typeof Term.imp) (X := __eo_typeof y)
      (A := __eo_typeof x) (U := Term.Apply (Term.Apply Term.FunType A) U) hHead
  simp [__eo_typeof] at hInv

private theorem not_typeof_full_eq_fun_ends_in_bool
    (x y : Term) :
    ¬ eo_fun_ends_in_bool (__eo_typeof (Term.Apply (Term.Apply Term.eq y) x)) := by
  intro h
  rcases eo_typeof_apply_fun_ends_in_bool_inv
      (F := __eo_typeof (Term.Apply Term.eq y)) (X := __eo_typeof x)
      (by simpa [__eo_typeof] using h) with
    ⟨A, U, hF, _hU⟩
  cases hy : __eo_typeof y <;>
    simp [__eo_typeof, __eo_typeof_eq, hy] at hF

private theorem smtx_typeof_guard_inhabited_none :
    __smtx_typeof_guard_inhabited SmtType.None SmtType.None = SmtType.None := by
  unfold __smtx_typeof_guard_inhabited
  cases h : smt_lit_inhabited_type SmtType.None <;> simp [smt_lit_ite, h]

private theorem smtx_typeof_translation_var_none_of_fun_ends_in_bool
    (s : eo_lit_String) (T : Term) :
    eo_fun_ends_in_bool T ->
      __smtx_typeof (__eo_to_smt (Term.Var s T)) = SmtType.None := by
  intro hT
  have hTyNone : __eo_to_smt_type T = SmtType.None :=
    eo_to_smt_type_none_of_fun_ends_in_bool hT
  simpa [eo_to_smt_var, __smtx_typeof, hTyNone] using smtx_typeof_guard_inhabited_none

private theorem smtx_typeof_translation_uconst_none_of_fun_ends_in_bool
    (i : eo_lit_Nat) (T : Term) :
    eo_fun_ends_in_bool T ->
      __smtx_typeof (__eo_to_smt (Term.UConst i T)) = SmtType.None := by
  intro hT
  have hTyNone : __eo_to_smt_type T = SmtType.None :=
    eo_to_smt_type_none_of_fun_ends_in_bool hT
  simpa [eo_to_smt_uconst, __smtx_typeof, hTyNone] using smtx_typeof_guard_inhabited_none

private theorem smtx_typeof_translation_dt_sel_apply_none_of_fun_ends_in_bool
    (s : eo_lit_String) (d : Datatype) (i j : eo_lit_Nat) (x : Term) :
    eo_fun_ends_in_bool (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) = SmtType.None := by
  intro hRet
  have hRetNone :
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j = SmtType.None :=
    smtx_ret_typeof_sel_none_of_eo_dt_sel_return_fun_ends_in_bool s d i j hRet
  rw [__eo_to_smt.eq_def]
  cases hX : __smtx_typeof (__eo_to_smt x) <;>
    simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite,
      smt_lit_Teq, hRetNone, hX]

@[simp] private theorem smtx_typeof_translation_partial_or_none
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.or x)) = SmtType.None := by
  have hHead : __eo_to_smt Term.or = SmtTerm.None := by
    rw [__eo_to_smt.eq_def]
  rw [__eo_to_smt.eq_def]
  change __smtx_typeof (SmtTerm.Apply (__eo_to_smt Term.or) (__eo_to_smt x)) = SmtType.None
  rw [hHead]
  rfl

@[simp] private theorem smtx_typeof_translation_partial_and_none
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.and x)) = SmtType.None := by
  have hHead : __eo_to_smt Term.and = SmtTerm.None := by
    rw [__eo_to_smt.eq_def]
  rw [__eo_to_smt.eq_def]
  change __smtx_typeof (SmtTerm.Apply (__eo_to_smt Term.and) (__eo_to_smt x)) = SmtType.None
  rw [hHead]
  rfl

@[simp] private theorem smtx_typeof_translation_partial_imp_none
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.imp x)) = SmtType.None := by
  have hHead : __eo_to_smt Term.imp = SmtTerm.None := by
    rw [__eo_to_smt.eq_def]
  rw [__eo_to_smt.eq_def]
  change __smtx_typeof (SmtTerm.Apply (__eo_to_smt Term.imp) (__eo_to_smt x)) = SmtType.None
  rw [hHead]
  rfl

@[simp] private theorem smtx_typeof_translation_partial_eq_none
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.eq x)) = SmtType.None := by
  have hHead : __eo_to_smt Term.eq = SmtTerm.None := by
    rw [__eo_to_smt.eq_def]
  rw [__eo_to_smt.eq_def]
  change __smtx_typeof (SmtTerm.Apply (__eo_to_smt Term.eq) (__eo_to_smt x)) = SmtType.None
  rw [hHead]
  rfl

private theorem smtx_typeof_translation_dt_sel_apply_bool_of_non_none
    (s : eo_lit_String) (d : Datatype) (i j : eo_lit_Nat) (x : Term) :
    __eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j = Term.Bool ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) = SmtType.Bool := by
  intro hRet hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hSelTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) (__eo_to_smt x)) =
        __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j :=
    dt_sel_term_typeof_of_non_none hApplyNN
  have hRetTy :
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j = SmtType.Bool :=
    smtx_ret_typeof_sel_bool_of_eo_dt_sel_return_bool s d i j hRet
  exact hSelTy.trans hRetTy


end TranslationProofs
