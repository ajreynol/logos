import Cpc.Proofs.Translation.Datatypes
import Cpc.Proofs.Translation.Quantifiers
import Cpc.Proofs.Translation.Special
import Cpc.Proofs.Translation.Inversions
import Cpc.Proofs.Translation.Heads
import Cpc.Proofs.TypePreservation

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof
attribute [local reducible] __eo_to_smt

namespace TranslationProofs

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_concat`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_concat
    (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply Term.concat y) x) =
        SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat (__eo_to_smt y)) (__eo_to_smt x))
    (hEo :
      ∀ w1 w2 : smt_lit_Int,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w1 ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w2 ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.concat y) x)) =
          SmtType.BitVec (smt_lit_zplus w1 w2))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.concat y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.concat y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.concat y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat (__eo_to_smt y)) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_concat_args_of_non_none hApplyNN with ⟨w1, w2, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.concat y) x)) =
        SmtType.BitVec (smt_lit_zplus w1 w2) := by
    rw [hTranslate]
    simp [__smtx_typeof, __smtx_typeof_concat, hy, hx]
  exact hSmt.trans (hEo w1 w2 hy hx).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_bv_binop`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bv_binop
    (eoOp : Term) (smtOp : SmtTerm) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply eoOp y) x) =
        SmtTerm.Apply (SmtTerm.Apply smtOp (__eo_to_smt y)) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply smtOp (__eo_to_smt y)) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2 (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)))
    (hEo :
      ∀ w : smt_lit_Int,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) = SmtType.BitVec w)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply smtOp (__eo_to_smt y)) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_binop_args_of_non_none hTy hApplyNN with ⟨w, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) = SmtType.BitVec w := by
    rw [hTranslate]
    rw [hTy, hy, hx]
    simp [__smtx_typeof_bv_op_2, smt_lit_ite, SmtEval.smt_lit_zeq]
  exact hSmt.trans (hEo w hy hx).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_bv_binop_ret`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
    (eoOp : Term) (smtOp : SmtTerm) (ret : SmtType) (x y : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply eoOp y) x) =
        SmtTerm.Apply (SmtTerm.Apply smtOp (__eo_to_smt y)) (__eo_to_smt x))
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply smtOp (__eo_to_smt y)) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x))
          ret)
    (hEo :
      ∀ w : smt_lit_Int,
        __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ->
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) = ret)
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply eoOp y) x)) := by
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply smtOp (__eo_to_smt y)) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hNonNone
  rcases bv_binop_ret_args_of_non_none hTy hApplyNN with
    ⟨w, hy, hx⟩
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply eoOp y) x)) = ret := by
    rw [hTranslate]
    rw [hTy, hy, hx]
    simp [__smtx_typeof_bv_op_2_ret, smt_lit_ite, SmtEval.smt_lit_zeq]
  exact hSmt.trans (hEo w hy hx).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_apply_apply_generic`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
    (g z y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply g z) y) x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply g z) y)) (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTranslate] using hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
  have hHeadNN :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g z) y)) ≠ SmtType.None := by
    cases hHead with
    | inl hMap =>
        rw [hMap]
        simp
    | inr hDt =>
        rw [hDt]
        simp
  have hHeadEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)) = SmtType.Map A B ∨
        __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g z) y)) = SmtType.FunType A B := by
    rw [← ihF hHeadNN]
    exact hHead
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply g z) y) x)) = B := by
    rw [hTranslate]
    rw [hGeneric]
    cases hHead with
    | inl hMap =>
        simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hMap, hX, hA]
    | inr hDt =>
        simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hDt, hX, hA]
  exact hSmt.trans
    (eo_to_smt_type_typeof_apply_of_smt_apply
      x (Term.Apply (Term.Apply g z) y) A B hHeadEo hX).symm

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply_apply_generic`. -/
private theorem eo_to_smt_typeof_matches_translation_apply_apply_generic
    (g y x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) =
        __eo_to_smt_type (__eo_typeof (Term.Apply g y)))
    (hGeneric :
      generic_apply_type (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g y) x) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x))
    (hNonNone :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply g y) x)) := by
  have hApplyNN :
      __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply g y)))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    have hApplyNN' :
        __smtx_typeof
            (SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTranslate] using hNonNone
    rw [hGeneric] at hApplyNN'
    exact hApplyNN'
  rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
  have hHeadNN :
      __smtx_typeof (__eo_to_smt (Term.Apply g y)) ≠ SmtType.None := by
    cases hHead with
    | inl hMap =>
        rw [hMap]
        simp
    | inr hDt =>
        rw [hDt]
        simp
  have hHeadEo :
      __eo_to_smt_type (__eo_typeof (Term.Apply g y)) = SmtType.Map A B ∨
        __eo_to_smt_type (__eo_typeof (Term.Apply g y)) = SmtType.FunType A B := by
    rw [← ihF hHeadNN]
    exact hHead
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply g y) x)) = B := by
    rw [hTranslate]
    rw [hGeneric]
    cases hHead with
    | inl hMap =>
        simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hMap, hX, hA]
    | inr hDt =>
        simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hDt, hX, hA]
  exact hSmt.trans
    (eo_to_smt_type_typeof_apply_of_smt_apply
      x (Term.Apply g y) A B hHeadEo hX).symm

/-- Computes `__smtx_typeof` for `eq_non_none`. -/
private theorem smtx_typeof_eq_non_none
    {T U : SmtType}
    (h : __smtx_typeof_eq T U ≠ SmtType.None) :
    T = U ∧ T ≠ SmtType.None := by
  by_cases hNone : T = SmtType.None
  · subst hNone
    exfalso
    exact h (by simp [__smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq])
  · by_cases hEq : T = U
    · exact ⟨hEq, hNone⟩
    · exfalso
      exact h (by
        simp [__smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hNone, hEq])

/-- Lemma about `smt_type_ne_set_self`. -/
private theorem smt_type_ne_set_self
    (T : SmtType) :
    T ≠ SmtType.Set T := by
  cases T <;> intro h <;> cases h

/-- Lemma about `smt_type_ne_guard_inhabited_set_self`. -/
private theorem smt_type_ne_guard_inhabited_set_self
    {T : SmtType}
    (hT : T ≠ SmtType.None) :
    T ≠ __smtx_typeof_guard_inhabited T (SmtType.Set T) := by
  intro h
  by_cases hInh : smt_lit_inhabited_type T = true
  · have hSet : T = SmtType.Set T := by
      simpa [__smtx_typeof_guard_inhabited, hInh, smt_lit_ite] using h
    exact smt_type_ne_set_self T hSet
  · have hNone : T = SmtType.None := by
      simpa [__smtx_typeof_guard_inhabited, hInh, smt_lit_ite] using h
    exact hT hNone

/-- Computes `__smtx_typeof` for `apply_eo_to_smt_set_empty_eq_none`. -/
private theorem smtx_typeof_apply_eo_to_smt_set_empty_eq_none
    (T X : SmtType) :
    __smtx_typeof_apply (__smtx_typeof (__eo_to_smt_set_empty T)) X = SmtType.None := by
  cases T with
  | None
  | Bool
  | Int
  | Real
  | RegLan
  | BitVec _
  | Seq _
  | Char
  | Datatype _ _
  | TypeRef _
  | USort _
  | Map _ _
  | FunType _ _ =>
      simp [__eo_to_smt_set_empty, __smtx_typeof, __smtx_typeof_apply]
  | Set U =>
      by_cases hInh : smt_lit_inhabited_type U = true
      · simp [__eo_to_smt_set_empty, __smtx_typeof_apply,
          __smtx_typeof_guard_inhabited, smt_lit_ite, hInh]
      · simp [__eo_to_smt_set_empty, __smtx_typeof_apply,
          __smtx_typeof_guard_inhabited, smt_lit_ite, hInh]

/-- Simplifies EO-to-SMT translation for `typeof_matches_translation_apply`. -/
theorem eo_to_smt_typeof_matches_translation_apply
    (f x : Term)
    (ihF :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt f) = __eo_to_smt_type (__eo_typeof f))
    (ihX :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x)) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  cases f <;> intro hNonNone
  case Var name T =>
    cases name
    case String s =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x) =
              SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x) := by
          have hGeneric :
              __eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x) =
                SmtTerm.Apply (__eo_to_smt (Term.Var (Term.String s) T)) (__eo_to_smt x) := by
            rw [__eo_to_smt.eq_def]
          rw [eo_to_smt_var] at hGeneric
          exact hGeneric
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          simpa [hTranslate, __smtx_typeof] using hNonNone
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hVarNN : __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) ≠ SmtType.None := by
          intro hVarNone
          apply hApplyNN
          simp [__smtx_typeof_apply, hVarNone]
        have hHeadTy :
            __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) = __eo_to_smt_type T := by
          simpa using smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hVarNN
        have hT :
            __eo_to_smt_type T = SmtType.Map A B ∨
              __eo_to_smt_type T = SmtType.FunType A B := by
          rw [← hHeadTy]
          exact hHead
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x)) = B := by
          rw [hTranslate]
          change
            __smtx_typeof_apply
                (__smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)))
                (__smtx_typeof (__eo_to_smt x)) = B
          cases hHead with
          | inl hMap =>
              rw [hMap, hX]
              simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA]
          | inr hDt =>
              rw [hDt, hX]
              simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA]
        exact hSmt.trans (eo_to_smt_type_typeof_apply_var_of_smt_apply x T s A B hT hX).symm
    all_goals
      sorry
  case DtCons s d i =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
          SmtTerm.Apply (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
            SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      simpa [eo_to_smt_term_dt_cons] using hGeneric
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTranslate, __smtx_typeof] using hNonNone
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hHeadEo :
        __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = SmtType.Map A B ∨
          __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = SmtType.FunType A B := by
      rw [eo_to_smt_type_typeof_dt_cons s d i]
      exact hHead
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtCons s d i) x)) = B := by
      rw [hTranslate]
      change
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i))
            (__smtx_typeof (__eo_to_smt x)) = B
      cases hHead with
      | inl hMap =>
          rw [hMap, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA]
      | inr hDt =>
          rw [hDt, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_dt_cons_of_smt_apply x s d i A B hHeadEo hX).symm
  case DtSel s d i j =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
          SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
            SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      simpa [eo_to_smt_term_dt_sel] using hGeneric
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg :
        __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s (__eo_to_smt_datatype d) :=
      dt_sel_arg_datatype_of_non_none hApplyNN
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) =
          __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
      rw [hTranslate]
      exact dt_sel_term_typeof_of_non_none hApplyNN
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype x s d i j hArg).symm
  case UConst i T =>
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.UConst i T) x) =
          SmtTerm.Apply (SmtTerm.UConst (smt_lit_uconst_id i) (__eo_to_smt_type T)) (__eo_to_smt x) := by
      have hGeneric :
          __eo_to_smt (Term.Apply (Term.UConst i T) x) =
            SmtTerm.Apply (__eo_to_smt (Term.UConst i T)) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      rw [eo_to_smt_uconst] at hGeneric
      exact hGeneric
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.UConst (smt_lit_uconst_id i) (__eo_to_smt_type T)))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      simpa [hTranslate, __smtx_typeof] using hNonNone
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hUConstNN :
        __smtx_typeof (SmtTerm.UConst (smt_lit_uconst_id i) (__eo_to_smt_type T)) ≠ SmtType.None := by
      intro hUConstNone
      apply hApplyNN
      simp [__smtx_typeof_apply, hUConstNone]
    have hHeadTy :
        __smtx_typeof (SmtTerm.UConst (smt_lit_uconst_id i) (__eo_to_smt_type T)) =
          __eo_to_smt_type T := by
      simpa using
        smtx_typeof_uconst_of_non_none (smt_lit_uconst_id i) (__eo_to_smt_type T) hUConstNN
    have hT :
        __eo_to_smt_type T = SmtType.Map A B ∨
          __eo_to_smt_type T = SmtType.FunType A B := by
      rw [← hHeadTy]
      exact hHead
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term.UConst i T) x)) = B := by
      rw [hTranslate]
      change
        __smtx_typeof_apply
            (__smtx_typeof (SmtTerm.UConst (smt_lit_uconst_id i) (__eo_to_smt_type T)))
            (__smtx_typeof (__eo_to_smt x)) = B
      cases hHead with
      | inl hMap =>
          rw [hMap, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA]
      | inr hDt =>
          rw [hDt, hX]
          simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_uconst_of_smt_apply x T i A B hT hX).symm
  case Apply f y =>
    cases f
    case eq =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.eq y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hEqNN :
          __smtx_typeof_eq
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate, __smtx_typeof] using hNonNone
      have hArgs := smtx_typeof_eq_non_none hEqNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.eq y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        change
          __smtx_typeof_eq
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) = SmtType.Bool
        rw [hArgs.1]
        cases hT : __smtx_typeof (__eo_to_smt x) <;>
          simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq,
            hT] at hArgs ⊢
      have hXNotNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [← hArgs.1]
        exact hArgs.2
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_eq_of_smt_same_non_none
          x y
          (__smtx_typeof (__eo_to_smt x))
          hArgs.1
          rfl
          hXNotNone).symm
    case distinct =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.distinct y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hEqNN :
          __smtx_typeof_eq
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate, __smtx_typeof] using hNonNone
      have hArgs := smtx_typeof_eq_non_none hEqNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.distinct y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        change
          __smtx_typeof_eq
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) = SmtType.Bool
        rw [hArgs.1]
        cases hT : __smtx_typeof (__eo_to_smt x) <;>
          simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq,
            hT] at hArgs ⊢
      have hXNotNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
        rw [← hArgs.1]
        exact hArgs.2
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_distinct_of_smt_same_non_none
          x y
          (__smtx_typeof (__eo_to_smt x))
          hArgs.1
          rfl
          hXNotNone).symm
    case not =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.not y) =
            SmtTerm.Apply SmtTerm.not (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.not y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.not y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case to_real =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.to_real y) =
            SmtTerm.Apply SmtTerm.to_real (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.to_real y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.to_real y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case to_int =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.to_int y) =
            SmtTerm.Apply SmtTerm.to_int (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.to_int y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.to_int y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case is_int =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.is_int y) =
            SmtTerm.Apply SmtTerm.is_int (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.is_int y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.is_int y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case abs =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.abs y) =
            SmtTerm.Apply SmtTerm.abs (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.abs y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.abs y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case str_to_re =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.str_to_re y) =
            SmtTerm.Apply SmtTerm.str_to_re (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.str_to_re y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.str_to_re y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case re_mult =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.re_mult y) =
            SmtTerm.Apply SmtTerm.re_mult (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.re_mult y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.re_mult y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case re_plus =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.re_plus y) =
            SmtTerm.Apply SmtTerm.re_plus (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.re_plus y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.re_plus y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case re_opt =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.re_opt y) =
            SmtTerm.Apply SmtTerm.re_opt (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.re_opt y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.re_opt y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case re_comp =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.re_comp y) =
            SmtTerm.Apply SmtTerm.re_comp (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.re_comp y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.re_comp y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case set_singleton =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.set_singleton y) =
            SmtTerm.Apply SmtTerm.set_singleton (__eo_to_smt y) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.set_singleton y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.set_singleton y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case set_is_empty =>
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.set_is_empty y) =
            let _v0 := __eo_to_smt y
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq _v0) (SmtTerm.set_empty (__smtx_typeof _v0)) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.set_is_empty y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.set_is_empty y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case set_is_singleton =>
      let T := __eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose y))
      have hHeadTranslate :
          __eo_to_smt (Term.Apply Term.set_is_singleton y) =
            SmtTerm.Apply (SmtTerm.exists "_at_x" T)
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt y))
                (SmtTerm.Apply SmtTerm.set_singleton (SmtTerm.Var "_at_x" T))) := by
        rw [__eo_to_smt.eq_def]
      have hGeneric :
          generic_apply_type (__eo_to_smt (Term.Apply Term.set_is_singleton y)) (__eo_to_smt x) := by
        unfold generic_apply_type
        rw [hHeadTranslate]
      exact eo_to_smt_typeof_matches_translation_apply_apply_generic
        Term.set_is_singleton y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
    case str_contains =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_contains y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_contains (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :
          ∃ T : SmtType,
            __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ∧
              __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
        unfold term_has_non_none_type at hApplyNN
        cases hY : __smtx_typeof (__eo_to_smt y) with
        | Seq T =>
            cases hX : __smtx_typeof (__eo_to_smt x) with
            | Seq U =>
                have hEq : T = U := by
                  simpa [__smtx_typeof, __smtx_typeof_seq_op_2_ret, smt_lit_ite, smt_lit_Teq, hY,
                    hX] using hApplyNN
                subst hEq
                exact ⟨T, rfl, rfl⟩
            | _ =>
                simp [__smtx_typeof, __smtx_typeof_seq_op_2_ret, hY, hX] at hApplyNN
        | _ =>
            cases hX : __smtx_typeof (__eo_to_smt x) <;>
              simp [__smtx_typeof, __smtx_typeof_seq_op_2_ret, hY, hX] at hApplyNN
      rcases hArgs with ⟨T, hY, hX⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_contains y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simpa [__smtx_typeof, __smtx_typeof_seq_op_2_ret, hY, hX, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_contains_of_smt_seq x y T hY hX).symm
    case str_prefixof =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_prefixof y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_prefixof (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :=
        seq_char_binop_args_of_non_none (op := SmtTerm.str_prefixof) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_prefixof y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_prefixof_of_smt_seq
          x y SmtType.Char hArgs.1 hArgs.2).symm
    case str_suffixof =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_suffixof y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_suffixof (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs :=
        seq_char_binop_args_of_non_none (op := SmtTerm.str_suffixof) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_suffixof y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_suffixof_of_smt_seq
          x y SmtType.Char hArgs.1 hArgs.2).symm
    case str_lt =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_lt y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_lt (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_lt) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_lt y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_lt_of_smt_seq_char x y hArgs.1 hArgs.2).symm
    case str_leq =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_leq y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_leq (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.str_leq) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_leq y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_leq_of_smt_seq_char x y hArgs.1 hArgs.2).symm
    case str_concat =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_concat y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_concat (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases seq_binop_args_of_non_none (op := SmtTerm.str_concat) rfl hApplyNN with
        ⟨T, hY, hX⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_concat y) x)) =
            SmtType.Seq T := by
        rw [hTranslate]
        simp [__smtx_typeof, __smtx_typeof_seq_op_2, smt_lit_ite, smt_lit_Teq, hY, hX]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_concat_of_smt_seq x y T hY hX).symm
    case re_range =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_range y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := seq_char_binop_args_of_non_none (op := SmtTerm.re_range) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_range y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_range_of_smt_seq_char x y hArgs.1 hArgs.2).symm
    case re_concat =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_concat y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_concat (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_concat) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_concat y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_concat_of_smt_reglan x y hArgs.1 hArgs.2).symm
    case re_inter =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_inter y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_inter (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_inter) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_inter y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_inter_of_smt_reglan x y hArgs.1 hArgs.2).symm
    case re_union =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_union y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_union (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_union) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_union y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_union_of_smt_reglan x y hArgs.1 hArgs.2).symm
    case re_diff =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.re_diff y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_diff (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := reglan_binop_args_of_non_none (op := SmtTerm.re_diff) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.re_diff y) x)) =
            SmtType.RegLan := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_re_diff_of_smt_reglan x y hArgs.1 hArgs.2).symm
    case str_in_re =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_in_re y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_in_re (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := seq_char_reglan_args_of_non_none (op := SmtTerm.str_in_re) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_in_re y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_in_re_of_smt_seq_char_reglan
          x y hArgs.1 hArgs.2).symm
    case seq_nth =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.seq_nth y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.seq_nth (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.seq_nth (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases seq_nth_args_of_non_none hApplyNN with ⟨T, hY, hX⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.seq_nth y) x)) = T := by
        rw [hTranslate]
        simpa [__smtx_typeof, __smtx_typeof_seq_nth, hY, hX]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_seq_nth_of_smt_seq_int x y T hY hX).symm
    case or =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.or y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans (eo_to_smt_type_typeof_apply_apply_or_of_smt_bool x y hArgs.1 hArgs.2).symm
    case and =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.and y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_and_of_smt_bool x y hArgs.1 hArgs.2).symm
    case imp =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.imp y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_imp_of_smt_bool x y hArgs.1 hArgs.2).symm
    case xor =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.xor y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.xor) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.xor y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_xor_of_smt_bool x y hArgs.1 hArgs.2).symm
    case plus =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.plus y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.plus (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_args_of_non_none (op := SmtTerm.plus) rfl hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.plus y) x)) =
              SmtType.Int := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_plus_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.plus y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_plus_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case neg =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.neg y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.neg (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_args_of_non_none (op := SmtTerm.neg) rfl hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.neg y) x)) =
              SmtType.Int := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_neg_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.neg y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_neg_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case mult =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.mult y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mult (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_args_of_non_none (op := SmtTerm.mult) rfl hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.mult y) x)) =
              SmtType.Int := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_mult_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.mult y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_mult_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case lt =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.lt y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.lt (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.lt) rfl hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.lt y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_lt_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.lt y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_lt_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case leq =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.leq y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.leq (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.leq) rfl hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.leq y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_leq_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.leq y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_leq_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case gt =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.gt y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.gt (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.gt) rfl hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.gt y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_gt_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.gt y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_gt_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case geq =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.geq y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq) rfl hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.geq y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_geq_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.geq y) x)) =
              SmtType.Bool := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_geq_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case div =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.div y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.div (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.div) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.div y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_div_of_smt_int x y hArgs.1 hArgs.2).symm
    case mod =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.mod y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.mod y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_mod_of_smt_int x y hArgs.1 hArgs.2).symm
    case multmult =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.multmult y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.multmult) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.multmult y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_multmult_of_smt_int x y hArgs.1 hArgs.2).symm
    case divisible =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.divisible y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.divisible (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.divisible) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.divisible y) x)) =
            SmtType.Bool := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_divisible_of_smt_int x y hArgs.1 hArgs.2).symm
    case div_total =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.div_total y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div_total (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.div_total) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.div_total y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_div_total_of_smt_int x y hArgs.1 hArgs.2).symm
    case mod_total =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.mod_total y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod_total (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.mod_total) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.mod_total y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_mod_total_of_smt_int x y hArgs.1 hArgs.2).symm
    case multmult_total =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.multmult_total y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.multmult_total (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hArgs := int_binop_args_of_non_none (op := SmtTerm.multmult_total) rfl hApplyNN
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.multmult_total y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        simp [__smtx_typeof, hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_multmult_total_of_smt_int x y hArgs.1 hArgs.2).symm
    case qdiv =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.qdiv y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real) rfl hApplyNN with
        hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_qdiv_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_qdiv_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case qdiv_total =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases arith_binop_ret_args_of_non_none
          (op := SmtTerm.qdiv_total) (R := SmtType.Real) rfl hApplyNN with hArgs | hArgs
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_qdiv_total_of_smt_arith
            x y SmtType.Int hArgs.1 hArgs.2 (Or.inl rfl)).symm
      · have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total y) x)) =
              SmtType.Real := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_qdiv_total_of_smt_arith
            x y SmtType.Real hArgs.1 hArgs.2 (Or.inr rfl)).symm
    case select =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.select y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt y)) (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt y)) (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases select_args_of_non_none hApplyNN with ⟨A, B, hY, hX⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.select y) x)) = B := by
        rw [hTranslate]
        simp [__smtx_typeof, __smtx_typeof_select, smt_lit_ite, smt_lit_Teq, hY, hX]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_select_of_smt_map x y A B hY hX).symm
    case concat =>
      exact eo_to_smt_typeof_matches_translation_apply_concat x y
        (by rw [__eo_to_smt.eq_def])
        (fun w1 w2 hy hx =>
          eo_to_smt_type_typeof_apply_apply_concat_of_smt_bitvec x y w1 w2 hy hx)
        hNonNone
    case bvand =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvand SmtTerm.bvand x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvand_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvor =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvor SmtTerm.bvor x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvor_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvnand =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvnand SmtTerm.bvnand x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvnand_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvnor =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvnor SmtTerm.bvnor x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvnor_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvxor =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvxor SmtTerm.bvxor x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvxor_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvxnor =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvxnor SmtTerm.bvxnor x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvxnor_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvcomp =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvcomp SmtTerm.bvcomp (SmtType.BitVec 1) x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvcomp_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvadd =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvadd SmtTerm.bvadd x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvadd_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvmul =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvmul SmtTerm.bvmul x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvmul_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvudiv =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvudiv SmtTerm.bvudiv x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvudiv_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvurem =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvurem SmtTerm.bvurem x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvurem_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsub =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvsub SmtTerm.bvsub x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsub_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsdiv =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvsdiv SmtTerm.bvsdiv x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsdiv_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsrem =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvsrem SmtTerm.bvsrem x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsrem_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsmod =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvsmod SmtTerm.bvsmod x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsmod_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvult =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvult SmtTerm.bvult SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvult_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvule =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvule SmtTerm.bvule SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvule_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvugt =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvugt SmtTerm.bvugt SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvugt_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvuge =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvuge SmtTerm.bvuge SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvuge_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvslt =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvslt SmtTerm.bvslt SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvslt_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsle =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsle SmtTerm.bvsle SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsle_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsgt =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsgt SmtTerm.bvsgt SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsgt_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsge =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsge SmtTerm.bvsge SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsge_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvshl =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvshl SmtTerm.bvshl x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvshl_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvlshr =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvlshr SmtTerm.bvlshr x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvlshr_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvashr =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop
        Term.bvashr SmtTerm.bvashr x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvashr_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvuaddo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvuaddo SmtTerm.bvuaddo SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvuaddo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsaddo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsaddo SmtTerm.bvsaddo SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsaddo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvumulo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvumulo SmtTerm.bvumulo SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvumulo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsmulo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsmulo SmtTerm.bvsmulo SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsmulo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvusubo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvusubo SmtTerm.bvusubo SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvusubo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvssubo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvssubo SmtTerm.bvssubo SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvssubo_of_smt_bitvec x y w hy hx)
        hNonNone
    case bvsdivo =>
      exact eo_to_smt_typeof_matches_translation_apply_bv_binop_ret
        Term.bvsdivo SmtTerm.bvsdivo SmtType.Bool x y
        (by rw [__eo_to_smt.eq_def])
        rfl
        (fun w hy hx => eo_to_smt_type_typeof_apply_apply_bvsdivo_of_smt_bitvec x y w hy hx)
        hNonNone
    case «repeat» =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.repeat y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.repeat (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.repeat (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases repeat_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.repeat y) x)) =
            SmtType.BitVec (smt_lit_zmult i w) := by
        rw [hTranslate, typeof_repeat_eq, hy, hx]
        simp [__smtx_typeof_repeat, smt_lit_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_repeat_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case zero_extend =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.zero_extend y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases zero_extend_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.zero_extend y) x)) =
            SmtType.BitVec (smt_lit_zplus i w) := by
        rw [hTranslate, typeof_zero_extend_eq, hy, hx]
        simp [__smtx_typeof_zero_extend, smt_lit_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_zero_extend_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case sign_extend =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.sign_extend y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases sign_extend_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.sign_extend y) x)) =
            SmtType.BitVec (smt_lit_zplus i w) := by
        rw [hTranslate, typeof_sign_extend_eq, hy, hx]
        simp [__smtx_typeof_sign_extend, smt_lit_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_sign_extend_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case rotate_left =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.rotate_left y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases rotate_left_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.rotate_left y) x)) =
            SmtType.BitVec w := by
        rw [hTranslate, typeof_rotate_left_eq, hy, hx]
        simp [__smtx_typeof_rotate_left, smt_lit_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_rotate_left_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case rotate_right =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.rotate_right y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases rotate_right_args_of_non_none hApplyNN with ⟨i, w, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.rotate_right y) x)) =
            SmtType.BitVec w := by
        rw [hTranslate, typeof_rotate_right_eq, hy, hx]
        simp [__smtx_typeof_rotate_right, smt_lit_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_rotate_right_of_smt_numeral_bitvec
          x y i w hy hx hi).symm
    case int_to_bv =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases int_to_bv_args_of_non_none hApplyNN with ⟨i, hy, hx, hi⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv y) x)) =
            SmtType.BitVec i := by
        rw [hTranslate, typeof_int_to_bv_eq, hy, hx]
        simp [__smtx_typeof_int_to_bv, smt_lit_ite, hi]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_int_to_bv_of_smt_numeral_int
          x y i hy hx hi).symm
    case str_at =>
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term.str_at y) x) =
            SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at (__eo_to_smt y))
              (__eo_to_smt x) := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN :
          term_has_non_none_type
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_at (__eo_to_smt y))
              (__eo_to_smt x)) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      rcases str_at_args_of_non_none hApplyNN with ⟨T, hY, hX⟩
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.str_at y) x)) =
            SmtType.Seq T := by
        rw [hTranslate]
        simp [__smtx_typeof, __smtx_typeof_str_at, smt_lit_ite, smt_lit_Teq, hY, hX]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_str_at_of_smt_seq_int x y T hY hX).symm
    case _at_strings_stoi_result =>
      let subTerm :=
        SmtTerm.Apply
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr (__eo_to_smt y)) (SmtTerm.Numeral 0))
          (__eo_to_smt x)
      have hTranslate :
          __eo_to_smt (Term.Apply (Term.Apply Term._at_strings_stoi_result y) x) =
            SmtTerm.Apply SmtTerm.str_to_int subTerm := by
        rw [__eo_to_smt.eq_def]
      have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_int subTerm) := by
        unfold term_has_non_none_type
        rw [← hTranslate]
        exact hNonNone
      have hSubTy : __smtx_typeof subTerm = SmtType.Seq SmtType.Char :=
        seq_char_arg_of_non_none (op := SmtTerm.str_to_int) rfl hApplyNN
      have hSubNN : term_has_non_none_type subTerm := by
        unfold term_has_non_none_type
        rw [hSubTy]
        simp
      rcases str_substr_args_of_non_none hSubNN with ⟨T, hY, hZero, hX⟩
      have hSubTy' : __smtx_typeof subTerm = SmtType.Seq T := by
        simp [subTerm, __smtx_typeof, __smtx_typeof_str_substr, smt_lit_ite, smt_lit_Teq, hY, hZero, hX]
      have hTChar : T = SmtType.Char := by
        have hEq : SmtType.Seq SmtType.Char = SmtType.Seq T := hSubTy.symm.trans hSubTy'
        injection hEq with hT
        exact hT.symm
      have hYChar : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char := by
        simpa [hTChar] using hY
      have hSmt :
          __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term._at_strings_stoi_result y) x)) =
            SmtType.Int := by
        rw [hTranslate]
        simp [__smtx_typeof, __smtx_typeof_seq_op_1_ret, hSubTy, smt_lit_ite, smt_lit_Teq]
      exact hSmt.trans
        (eo_to_smt_type_typeof_apply_apply_at_strings_stoi_result_of_smt_seq_char_int x y
          hYChar hX).symm
    case Apply f z =>
      cases f
      case ite =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.ite z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases ite_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX, hT⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.ite z) y) x)) =
              T := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_ite, smt_lit_ite, smt_lit_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_ite_of_smt_bool_same_non_none
            x y z T hZ hY hX hT).symm
      case bvite =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.bvite z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply
                  (SmtTerm.Apply SmtTerm.ite
                    (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt z))
                      (SmtTerm.Binary 1 1)))
                  (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply
                  (SmtTerm.Apply SmtTerm.ite
                    (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt z))
                      (SmtTerm.Binary 1 1)))
                  (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases ite_args_of_non_none hApplyNN with ⟨T, hCond, hY, hX, hT⟩
        have hCondNN :
            __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt z)) (SmtTerm.Binary 1 1)) ≠
              SmtType.None := by
          rw [hCond]
          simp
        have hEqNN :
            __smtx_typeof_eq (__smtx_typeof (__eo_to_smt z)) (SmtType.BitVec 1) ≠
              SmtType.None := by
          simpa [__smtx_typeof] using hCondNN
        have hZ : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec 1 := (smtx_typeof_eq_non_none hEqNN).1
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.bvite z) y) x)) =
              T := by
          rw [hTranslate]
          change
            __smtx_typeof_ite
              (__smtx_typeof ((SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt z))
                (SmtTerm.Binary 1 1))))
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) = T
          rw [hCond, hY, hX]
          simp [__smtx_typeof_ite, smt_lit_ite, smt_lit_Teq, hT]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_bvite_of_smt_bitvec1_same_non_none
            x y z T hZ hY hX hT).symm
      case extract =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.extract z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases extract_args_of_non_none hApplyNN with ⟨i, j, w, hZ, hY, hX, hj0, hji, hiw⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.extract z) y) x)) =
              SmtType.BitVec (smt_lit_zplus (smt_lit_zplus i (smt_lit_zneg j)) 1) := by
          rw [hTranslate, typeof_extract_eq, hZ, hY, hX]
          simp [__smtx_typeof_extract, smt_lit_ite, hj0, hji, hiw]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_extract_of_smt_numeral_numeral_bitvec
            x y z i j w hZ hY hX hj0 hji hiw).symm
      case str_substr =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_substr z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_substr (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases str_substr_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_substr z) y) x)) =
              SmtType.Seq T := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_str_substr, smt_lit_ite, smt_lit_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_substr_of_smt_seq_int_int
            x y z T hZ hY hX).symm
      case str_indexof =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases str_indexof_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof z) y) x)) =
              SmtType.Int := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_str_indexof, smt_lit_ite, smt_lit_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_indexof_of_smt_seq_seq_int
            x y z T hZ hY hX).symm
      case str_update =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_update z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_update (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases str_update_args_of_non_none hApplyNN with ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_update z) y) x)) =
              SmtType.Seq T := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_str_update, smt_lit_ite, smt_lit_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_update_of_smt_seq_int_seq
            x y z T hZ hY hX).symm
      case str_replace =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace) rfl hApplyNN with
          ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace z) y) x)) =
              SmtType.Seq T := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_seq_op_3, smt_lit_ite, smt_lit_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_smt_seq
            x y z T hZ hY hX).symm
      case str_replace_all =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_all (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases seq_triop_args_of_non_none (op := SmtTerm.str_replace_all) rfl hApplyNN with
          ⟨T, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all z) y) x)) =
              SmtType.Seq T := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_seq_op_3, smt_lit_ite, smt_lit_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_smt_seq
            x y z T hZ hY hX).symm
      case str_replace_re =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        have hArgs := str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re) rfl hApplyNN
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re z) y) x)) =
              SmtType.Seq SmtType.Char := by
          rw [hTranslate]
          simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_of_smt_seq_char_reglan
            x y z hArgs.1 hArgs.2.1 hArgs.2.2).symm
      case str_replace_re_all =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_replace_re_all (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        have hArgs :=
          str_replace_re_args_of_non_none (op := SmtTerm.str_replace_re_all) rfl hApplyNN
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all z) y) x)) =
              SmtType.Seq SmtType.Char := by
          rw [hTranslate]
          simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_all_of_smt_seq_char_reglan
            x y z hArgs.1 hArgs.2.1 hArgs.2.2).symm
      case str_indexof_re =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.str_indexof_re (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        have hArgs := str_indexof_re_args_of_non_none hApplyNN
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re z) y) x)) =
              SmtType.Int := by
          rw [hTranslate]
          simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2.1, hArgs.2.2]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_str_indexof_re_of_smt_seq_char_reglan
            x y z hArgs.1 hArgs.2.1 hArgs.2.2).symm
      case store =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.store (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        rcases store_args_of_non_none hApplyNN with ⟨A, B, hZ, hY, hX⟩
        have hSmt :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store z) y) x)) =
              SmtType.Map A B := by
          rw [hTranslate]
          simp [__smtx_typeof, __smtx_typeof_store, smt_lit_ite, smt_lit_Teq, hZ, hY, hX]
        exact hSmt.trans
          (eo_to_smt_type_typeof_apply_apply_apply_store_of_smt_map x y z A B hZ hY hX).symm
      case re_loop =>
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.re_loop z) y) x) =
              SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_loop (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hApplyNN :
            term_has_non_none_type
              (SmtTerm.Apply
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_loop (__eo_to_smt z)) (__eo_to_smt y))
                (__eo_to_smt x)) := by
          unfold term_has_non_none_type
          rw [← hTranslate]
          exact hNonNone
        cases hz : __eo_to_smt z with
        | Numeral n1 =>
            cases hy : __eo_to_smt y with
            | Numeral n2 =>
                have hLoopNN :
                    term_has_non_none_type
                      (SmtTerm.Apply
                        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_loop (SmtTerm.Numeral n1))
                          (SmtTerm.Numeral n2))
                        (__eo_to_smt x)) := by
                  simpa [hz, hy] using hApplyNN
                rcases re_loop_arg_of_non_none hLoopNN with ⟨hn1, hn2, hX⟩
                have hSmt :
                    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.re_loop z) y) x)) =
                      SmtType.RegLan := by
                  rw [hTranslate, hz, hy]
                  simp [__smtx_typeof, __smtx_typeof_re_loop, hX, hn1, hn2, smt_lit_ite]
                exact hSmt.trans
                  (eo_to_smt_type_typeof_apply_apply_apply_re_loop_of_smt_numeral_numeral_reglan
                    x y z n1 n2 hz hy hX hn1 hn2).symm
            | _ =>
                have hBad := hApplyNN
                unfold term_has_non_none_type at hBad
                simp [hz, hy, __smtx_typeof, __smtx_typeof_re_loop, smt_lit_ite] at hBad
        | _ =>
            have hBad := hApplyNN
            unfold term_has_non_none_type at hBad
            simp [hz, __smtx_typeof, __smtx_typeof_re_loop, smt_lit_ite] at hBad
      case re_exp =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.re_exp z) y) =
              SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_exp (__eo_to_smt z)) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.re_exp z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.re_exp z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case _at_strings_deq_diff =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term._at_strings_deq_diff z) y) =
              let _v0 := SmtTerm.Numeral 1
              let _v2 := SmtTerm.Var "_at_x" SmtType.Int
              SmtTerm.Apply (SmtTerm.choice "_at_x" SmtType.Int)
                (SmtTerm.Apply SmtTerm.not
                  (SmtTerm.Apply
                    (SmtTerm.Apply SmtTerm.eq
                      (SmtTerm.Apply
                        (SmtTerm.Apply
                          (SmtTerm.Apply SmtTerm.str_substr (__eo_to_smt z)) _v2) _v0))
                    (SmtTerm.Apply
                      (SmtTerm.Apply
                        (SmtTerm.Apply SmtTerm.str_substr (__eo_to_smt y)) _v2) _v0))) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term._at_strings_deq_diff z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term._at_strings_deq_diff z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case _at_strings_itos_result =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term._at_strings_itos_result z) y) =
              SmtTerm.Apply SmtTerm.str_from_int
                (SmtTerm.Apply
                  (SmtTerm.Apply SmtTerm.mod (__eo_to_smt z))
                  (SmtTerm.Apply
                    (SmtTerm.Apply SmtTerm.multmult (SmtTerm.Numeral 10))
                    (__eo_to_smt y))) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type
              (__eo_to_smt (Term.Apply (Term.Apply Term._at_strings_itos_result z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term._at_strings_itos_result z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case _at_strings_num_occur =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term._at_strings_num_occur z) y) =
              let _v0 := __eo_to_smt y
              let _v1 := __eo_to_smt z
              SmtTerm.Apply
                (SmtTerm.Apply SmtTerm.div
                  (SmtTerm.Apply
                    (SmtTerm.Apply SmtTerm.neg (SmtTerm.Apply SmtTerm.str_len _v1))
                    (SmtTerm.Apply SmtTerm.str_len
                      (SmtTerm.Apply
                        (SmtTerm.Apply
                          (SmtTerm.Apply SmtTerm.str_replace_all _v1) _v0)
                        (SmtTerm.seq_empty (SmtType.Seq SmtType.Char))))))
                (SmtTerm.Apply SmtTerm.str_len _v0) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type
              (__eo_to_smt (Term.Apply (Term.Apply Term._at_strings_num_occur z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term._at_strings_num_occur z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case bvultbv =>
        let head :=
          SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.ite
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult (__eo_to_smt z)) (__eo_to_smt y)))
              (SmtTerm.Binary 1 1))
            (SmtTerm.Binary 1 0)
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.bvultbv z) y) = head := by
          rw [__eo_to_smt.eq_def]
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.bvultbv z) y) x) =
              SmtTerm.Apply head (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          simp [hHeadTranslate]
        have hApplyNN :
            __smtx_typeof_apply (__smtx_typeof head) (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          simpa [hTranslate, head, __smtx_typeof] using hNonNone
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN : __smtx_typeof head ≠ SmtType.None := by
          cases hHead with
          | inl hMap =>
              rw [hMap]
              simp
          | inr hDt =>
              rw [hDt]
              simp
        have hIteNN : term_has_non_none_type head := by
          unfold term_has_non_none_type
          exact hHeadNN
        rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
        have hThenNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
          rw [hThen]
          exact hT
        have hElseNN : __smtx_typeof (SmtTerm.Binary 1 0) ≠ SmtType.None := by
          rw [hElse]
          exact hT
        have hBitVec1 : T = SmtType.BitVec 1 := by
          exact hThen.symm.trans (smtx_typeof_binary_of_non_none 1 1 hThenNN)
        have hBranchEq :
            __smtx_typeof (SmtTerm.Binary 1 1) = __smtx_typeof (SmtTerm.Binary 1 0) := by
          exact hThen.trans hElse.symm
        have hTeq :
            smt_lit_Teq (__smtx_typeof (SmtTerm.Binary 1 1))
              (__smtx_typeof (SmtTerm.Binary 1 0)) = true := by
          simpa [smt_lit_Teq] using hBranchEq
        have hHeadTy : __smtx_typeof head = T := by
          change
            __smtx_typeof_ite
              (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvult (__eo_to_smt z)) (__eo_to_smt y)))
              (__smtx_typeof (SmtTerm.Binary 1 1))
              (__smtx_typeof (SmtTerm.Binary 1 0)) = T
          rw [hCond, hThen, hElse]
          simp [__smtx_typeof_ite, smt_lit_ite, smt_lit_Teq]
        cases hHead with
        | inl hMap =>
            cases (hBitVec1.symm.trans (hHeadTy.symm.trans hMap))
        | inr hDt =>
            cases (hBitVec1.symm.trans (hHeadTy.symm.trans hDt))
      case bvsltbv =>
        let head :=
          SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.ite
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt (__eo_to_smt z)) (__eo_to_smt y)))
              (SmtTerm.Binary 1 1))
            (SmtTerm.Binary 1 0)
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.bvsltbv z) y) = head := by
          rw [__eo_to_smt.eq_def]
        have hTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.bvsltbv z) y) x) =
              SmtTerm.Apply head (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
          simp [hHeadTranslate]
        have hApplyNN :
            __smtx_typeof_apply (__smtx_typeof head) (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          simpa [hTranslate, head, __smtx_typeof] using hNonNone
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN : __smtx_typeof head ≠ SmtType.None := by
          cases hHead with
          | inl hMap =>
              rw [hMap]
              simp
          | inr hDt =>
              rw [hDt]
              simp
        have hIteNN : term_has_non_none_type head := by
          unfold term_has_non_none_type
          exact hHeadNN
        rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
        have hThenNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
          rw [hThen]
          exact hT
        have hElseNN : __smtx_typeof (SmtTerm.Binary 1 0) ≠ SmtType.None := by
          rw [hElse]
          exact hT
        have hBitVec1 : T = SmtType.BitVec 1 := by
          exact hThen.symm.trans (smtx_typeof_binary_of_non_none 1 1 hThenNN)
        have hBranchEq :
            __smtx_typeof (SmtTerm.Binary 1 1) = __smtx_typeof (SmtTerm.Binary 1 0) := by
          exact hThen.trans hElse.symm
        have hTeq :
            smt_lit_Teq (__smtx_typeof (SmtTerm.Binary 1 1))
              (__smtx_typeof (SmtTerm.Binary 1 0)) = true := by
          simpa [smt_lit_Teq] using hBranchEq
        have hHeadTy : __smtx_typeof head = T := by
          change
            __smtx_typeof_ite
              (__smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvslt (__eo_to_smt z)) (__eo_to_smt y)))
              (__smtx_typeof (SmtTerm.Binary 1 1))
              (__smtx_typeof (SmtTerm.Binary 1 0)) = T
          rw [hCond, hThen, hElse]
          simp [__smtx_typeof_ite, smt_lit_ite, smt_lit_Teq]
        cases hHead with
        | inl hMap =>
            cases (hBitVec1.symm.trans (hHeadTy.symm.trans hMap))
        | inr hDt =>
            cases (hBitVec1.symm.trans (hHeadTy.symm.trans hDt))
      case _at_re_unfold_pos_component =>
        sorry
      case _at_witness_string_length =>
        sorry
      case update =>
        cases hz : __eo_to_smt z with
        | DtSel s d n m =>
            have hTranslate :
                __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.update z) y) x) =
                  __eo_to_smt_updater (SmtTerm.DtSel s d n m) (__eo_to_smt y) (__eo_to_smt x) := by
              rw [__eo_to_smt.eq_def]
              simp [hz]
            have hUpdaterNN :
                __smtx_typeof
                    (__eo_to_smt_updater (SmtTerm.DtSel s d n m) (__eo_to_smt y) (__eo_to_smt x)) ≠
                  SmtType.None := by
              rw [← hTranslate]
              exact hNonNone
            have hIteNN :
                term_has_non_none_type
                  (SmtTerm.Apply
                    (SmtTerm.Apply
                      (SmtTerm.Apply SmtTerm.ite
                        (SmtTerm.Apply (SmtTerm.DtTester s d n) (__eo_to_smt y)))
                      (__eo_to_smt_updater_rec
                        (SmtTerm.DtSel s d n m) (__smtx_dt_num_sels d n) (__eo_to_smt y)
                        (__eo_to_smt x) (SmtTerm.DtCons s d n)))
                    (__eo_to_smt y)) := by
              unfold term_has_non_none_type
              simpa [__eo_to_smt_updater] using hUpdaterNN
            rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
            have hCondNN :
                term_has_non_none_type
                  (SmtTerm.Apply (SmtTerm.DtTester s d n) (__eo_to_smt y)) := by
              unfold term_has_non_none_type
              rw [hCond]
              simp
            have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype s d := by
              exact dt_tester_arg_datatype_of_non_none hCondNN
            have hTTy : T = SmtType.Datatype s d := by
              exact hElse.symm.trans hYTy
            have hSmt :
                __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.update z) y) x)) =
                  SmtType.Datatype s d := by
              rw [hTranslate, __eo_to_smt_updater]
              change
                __smtx_typeof_ite
                    (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d n) (__eo_to_smt y)))
                    (__smtx_typeof
                      (__eo_to_smt_updater_rec
                        (SmtTerm.DtSel s d n m) (__smtx_dt_num_sels d n) (__eo_to_smt y)
                        (__eo_to_smt x) (SmtTerm.DtCons s d n)))
                    (__smtx_typeof (__eo_to_smt y)) =
                  SmtType.Datatype s d
              rw [hCond, hThen, hElse, hTTy]
              simp [__smtx_typeof_ite, smt_lit_ite, smt_lit_Teq]
            exact hSmt.trans
              (eo_to_smt_type_typeof_apply_apply_apply_update_of_smt_dt_sel
                x y z s d n m hz hNonNone).symm
        | _ =>
            have hBad := hNonNone
            rw [__eo_to_smt.eq_def] at hBad
            simp [hz] at hBad
            simp [__eo_to_smt_updater] at hBad
      case tuple_update =>
        cases hy : __eo_to_smt_type (__eo_typeof y) with
        | Datatype s d =>
            by_cases hTuple : s = "_at_Tuple"
            · subst hTuple
              cases hz : __eo_to_smt z with
              | Numeral n =>
                  have hTranslate :
                      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.tuple_update z) y) x) =
                        __eo_to_smt_tuple_update (SmtType.Datatype "_at_Tuple" d)
                          (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x) := by
                    rw [__eo_to_smt.eq_def]
                    simp [hy, hz]
                  have hTupleNN :
                      __smtx_typeof
                          (__eo_to_smt_tuple_update (SmtType.Datatype "_at_Tuple" d)
                            (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x)) ≠
                        SmtType.None := by
                    rw [← hTranslate]
                    exact hNonNone
                  have hGe : smt_lit_zleq 0 n = true := by
                    cases hTest : smt_lit_zleq 0 n <;>
                      simp [__eo_to_smt_tuple_update, hTest, smt_lit_ite] at hTupleNN
                    simpa using hTest
                  have hUpdaterNN :
                      __smtx_typeof
                          (__eo_to_smt_updater
                            (SmtTerm.DtSel "_at_Tuple" d smt_lit_nat_zero
                              (smt_lit_int_to_nat n))
                            (__eo_to_smt y) (__eo_to_smt x)) ≠
                        SmtType.None := by
                    simpa [__eo_to_smt_tuple_update, hGe, smt_lit_ite] using hTupleNN
                  have hIteNN :
                      term_has_non_none_type
                        (SmtTerm.Apply
                          (SmtTerm.Apply
                            (SmtTerm.Apply SmtTerm.ite
                              (SmtTerm.Apply (SmtTerm.DtTester "_at_Tuple" d smt_lit_nat_zero)
                                (__eo_to_smt y)))
                            (__eo_to_smt_updater_rec
                              (SmtTerm.DtSel "_at_Tuple" d smt_lit_nat_zero
                                (smt_lit_int_to_nat n))
                              (__smtx_dt_num_sels d smt_lit_nat_zero) (__eo_to_smt y)
                              (__eo_to_smt x)
                              (SmtTerm.DtCons "_at_Tuple" d smt_lit_nat_zero)))
                          (__eo_to_smt y)) := by
                    unfold term_has_non_none_type
                    simpa [__eo_to_smt_updater] using hUpdaterNN
                  rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
                  have hCondNN :
                      term_has_non_none_type
                        (SmtTerm.Apply (SmtTerm.DtTester "_at_Tuple" d smt_lit_nat_zero)
                          (__eo_to_smt y)) := by
                    unfold term_has_non_none_type
                    rw [hCond]
                    simp
                  have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype "_at_Tuple" d := by
                    exact dt_tester_arg_datatype_of_non_none hCondNN
                  have hTTy : T = SmtType.Datatype "_at_Tuple" d := by
                    exact hElse.symm.trans hYTy
                  have hInnerTy :
                      __smtx_typeof
                          (__eo_to_smt_updater
                            (SmtTerm.DtSel "_at_Tuple" d smt_lit_nat_zero
                              (smt_lit_int_to_nat n))
                            (__eo_to_smt y) (__eo_to_smt x)) =
                        SmtType.Datatype "_at_Tuple" d := by
                    rw [__eo_to_smt_updater]
                    change
                      __smtx_typeof_ite
                          (__smtx_typeof
                            (SmtTerm.Apply (SmtTerm.DtTester "_at_Tuple" d smt_lit_nat_zero)
                              (__eo_to_smt y)))
                          (__smtx_typeof
                            (__eo_to_smt_updater_rec
                              (SmtTerm.DtSel "_at_Tuple" d smt_lit_nat_zero
                                (smt_lit_int_to_nat n))
                              (__smtx_dt_num_sels d smt_lit_nat_zero) (__eo_to_smt y)
                              (__eo_to_smt x)
                              (SmtTerm.DtCons "_at_Tuple" d smt_lit_nat_zero)))
                          (__smtx_typeof (__eo_to_smt y)) =
                        SmtType.Datatype "_at_Tuple" d
                    rw [hCond, hThen, hElse, hTTy]
                    simp [__smtx_typeof_ite, smt_lit_ite, smt_lit_Teq]
                  have hSmt :
                      __smtx_typeof
                          (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.tuple_update z) y) x)) =
                        SmtType.Datatype "_at_Tuple" d := by
                    rw [hTranslate]
                    simpa [__eo_to_smt_tuple_update, hGe, smt_lit_ite] using hInnerTy
                  exact hSmt.trans
                    (eo_to_smt_type_typeof_apply_apply_apply_tuple_update_of_smt_numeral_tuple
                      x y z d n hy hz hNonNone).symm
              | _ =>
                  have hBad := hNonNone
                  rw [__eo_to_smt.eq_def] at hBad
                  simp [hy, hz] at hBad
                  simp [__eo_to_smt_tuple_update] at hBad
            · have hBad := hNonNone
              rw [__eo_to_smt.eq_def] at hBad
              simp [hy] at hBad
              simp [__eo_to_smt_tuple_update, hTuple] at hBad
        | _ =>
            have hBad := hNonNone
            rw [__eo_to_smt.eq_def] at hBad
            simp [hy] at hBad
            simp [__eo_to_smt_tuple_update] at hBad
      case set_union =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_union z) y) =
              SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_union (__eo_to_smt z)) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_union z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.set_union z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case set_inter =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_inter z) y) =
              SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_inter (__eo_to_smt z)) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_inter z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.set_inter z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case set_minus =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_minus z) y) =
              SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_minus (__eo_to_smt z)) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_minus z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.set_minus z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case set_choose =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_choose z) y) =
              let _v0 := __eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose z))
              SmtTerm.Apply (SmtTerm.choice "_at_x" _v0)
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member (SmtTerm.Var "_at_x" _v0))
                  (__eo_to_smt z)) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_choose z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        exact eo_to_smt_typeof_matches_translation_apply_apply_apply_generic
          Term.set_choose z y x ihF hGeneric (by rw [__eo_to_smt.eq_def]) hNonNone
      case set_member =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y) =
              SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member (__eo_to_smt z)) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hOuterTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.set_member z) y) x) =
              SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y))
                    (__eo_to_smt x)) ≠
                SmtType.None := by
            rw [← hOuterTranslate]
            exact hNonNone
          rw [hGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN :
            term_has_non_none_type
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_member (__eo_to_smt z)) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [← hHeadTranslate]
          cases hHead with
          | inl hMap =>
              rw [hMap]
              simp
          | inr hDt =>
              rw [hDt]
              simp
        have hHeadTy :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.set_member z) y)) =
              SmtType.Bool := by
          rcases set_member_args_of_non_none hHeadNN with ⟨A, hzTy, hyTy⟩
          rw [hHeadTranslate]
          simp [__smtx_typeof, __smtx_typeof_set_member, hzTy, hyTy,
            smt_lit_ite, smt_lit_Teq]
        cases hHead with
        | inl hMap =>
            cases (hHeadTy.symm.trans hMap)
        | inr hDt =>
            cases (hHeadTy.symm.trans hDt)
      case set_subset =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y) =
              SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset (__eo_to_smt z)) (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hOuterTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.set_subset z) y) x) =
              SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y))
                    (__eo_to_smt x)) ≠
                SmtType.None := by
            rw [← hOuterTranslate]
            exact hNonNone
          rw [hGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN :
            term_has_non_none_type
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.set_subset (__eo_to_smt z)) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [← hHeadTranslate]
          cases hHead with
          | inl hMap =>
              rw [hMap]
              simp
          | inr hDt =>
              rw [hDt]
              simp
        have hHeadTy :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.set_subset z) y)) =
              SmtType.Bool := by
          rcases set_binop_ret_args_of_non_none
              (op := SmtTerm.set_subset) (T := SmtType.Bool) rfl hHeadNN with
            ⟨A, hzTy, hyTy⟩
          rw [hHeadTranslate]
          simp [__smtx_typeof, __smtx_typeof_sets_op_2_ret, hzTy, hyTy,
            smt_lit_ite, smt_lit_Teq]
        cases hHead with
        | inl hMap =>
            cases (hHeadTy.symm.trans hMap)
        | inr hDt =>
            cases (hHeadTy.symm.trans hDt)
      case qdiv_total =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y) =
              SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total (__eo_to_smt z))
                (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hOuterTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.qdiv_total z) y) x) =
              SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y))
                    (__eo_to_smt x)) ≠
                SmtType.None := by
            rw [← hOuterTranslate]
            exact hNonNone
          rw [hGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN :
            term_has_non_none_type
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv_total (__eo_to_smt z)) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [← hHeadTranslate]
          cases hHead with
          | inl hMap =>
              rw [hMap]
              simp
          | inr hDt =>
              rw [hDt]
              simp
        rcases arith_binop_ret_args_of_non_none
            (op := SmtTerm.qdiv_total) (R := SmtType.Real) rfl hHeadNN with hArgs | hArgs
        · have hHeadTy :
              __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y)) =
                SmtType.Real := by
            rw [hHeadTranslate]
            simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
          cases hHead with
          | inl hMap =>
              cases (hHeadTy.symm.trans hMap)
          | inr hDt =>
              cases (hHeadTy.symm.trans hDt)
        · have hHeadTy :
              __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.qdiv_total z) y)) =
                SmtType.Real := by
            rw [hHeadTranslate]
            simp [__smtx_typeof, __smtx_typeof_arith_overload_op_2_ret, hArgs.1, hArgs.2]
          cases hHead with
          | inl hMap =>
              cases (hHeadTy.symm.trans hMap)
          | inr hDt =>
              cases (hHeadTy.symm.trans hDt)
      case int_to_bv =>
        have hHeadTranslate :
            __eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y) =
              SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv (__eo_to_smt z))
                (__eo_to_smt y) := by
          rw [__eo_to_smt.eq_def]
        have hOuterTranslate :
            __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.int_to_bv z) y) x) =
              SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y))
                (__eo_to_smt x) := by
          rw [__eo_to_smt.eq_def]
        have hGeneric :
            generic_apply_type (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y))
              (__eo_to_smt x) := by
          unfold generic_apply_type
          rw [hHeadTranslate]
        have hApplyNN :
            __smtx_typeof_apply
                (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y)))
                (__smtx_typeof (__eo_to_smt x)) ≠
              SmtType.None := by
          have hApplyNN' :
              __smtx_typeof
                  (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y))
                    (__eo_to_smt x)) ≠
                SmtType.None := by
            rw [← hOuterTranslate]
            exact hNonNone
          rw [hGeneric] at hApplyNN'
          exact hApplyNN'
        rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
        have hHeadNN :
            term_has_non_none_type
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv (__eo_to_smt z)) (__eo_to_smt y)) := by
          unfold term_has_non_none_type
          rw [← hHeadTranslate]
          cases hHead with
          | inl hMap =>
              rw [hMap]
              simp
          | inr hDt =>
              rw [hDt]
              simp
        rcases int_to_bv_args_of_non_none hHeadNN with ⟨i, hz', hy', hi⟩
        have hHeadTy :
            __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.int_to_bv z) y)) =
              SmtType.BitVec i := by
          rw [hHeadTranslate, typeof_int_to_bv_eq, hz', hy']
          simp [__smtx_typeof_int_to_bv, smt_lit_ite, hi]
        cases hHead with
        | inl hMap =>
            cases (hHeadTy.symm.trans hMap)
        | inr hDt =>
            cases (hHeadTy.symm.trans hDt)
      all_goals sorry
    all_goals sorry
  case not =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.not x) =
          SmtTerm.Apply SmtTerm.not (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.not (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
      unfold term_has_non_none_type at hApplyNN
      cases h : __smtx_typeof (__eo_to_smt x) <;>
        simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at hApplyNN
      simp
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Bool := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Bool := eo_to_smt_type_eq_bool hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) = SmtType.Bool := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
          SmtType.Bool SmtType.None) = SmtType.Bool
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_not_of_bool x hxEo).symm
  case _at_purify y =>
    sorry
  case to_real =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.to_real x) =
          SmtTerm.Apply SmtTerm.to_real (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_real (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∨
        __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
      to_real_arg_of_non_none (t := __eo_to_smt x) hApplyNN
    cases hArg with
    | inl hArgInt =>
        have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgInt]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
          rw [← hXTyped]
          exact hArgInt
        have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
        have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.to_real x)) = SmtType.Real := by
          rw [hTranslate]
          change
            (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
              SmtType.Real
              (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
                SmtType.Real SmtType.None)) = SmtType.Real
          simp [hArgInt, smt_lit_ite, smt_lit_Teq]
        exact hSmt.trans (eo_to_smt_type_typeof_apply_to_real_of_int x hxEo).symm
    | inr hArgReal =>
        have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
          rw [hArgReal]
          simp
        have hXTyped := ihX hXNonNone
        have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
          rw [← hXTyped]
          exact hArgReal
        have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
        have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.to_real x)) = SmtType.Real := by
          rw [hTranslate]
          change
            (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
              SmtType.Real
              (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
                SmtType.Real SmtType.None)) = SmtType.Real
          simp [hArgReal, smt_lit_ite, smt_lit_Teq]
        exact hSmt.trans (eo_to_smt_type_typeof_apply_to_real_of_real x hxEo).symm
  case to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.to_int x) =
          SmtTerm.Apply SmtTerm.to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
      real_arg_of_non_none (op := SmtTerm.to_int) (t := __eo_to_smt x) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.to_int x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_to_int_of_real x hxEo).symm
  case is_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.is_int x) =
          SmtTerm.Apply SmtTerm.is_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.is_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
      real_arg_of_non_none (op := SmtTerm.is_int) (t := __eo_to_smt x) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.is_int x)) = SmtType.Bool := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Real)
          SmtType.Bool SmtType.None) = SmtType.Bool
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_is_int_of_real x hxEo).symm
  case abs =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.abs x) =
          SmtTerm.Apply SmtTerm.abs (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.abs (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_arg_of_non_none (t := __eo_to_smt x) hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.abs x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_abs_of_int x hxEo).symm
  case int_pow2 =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.int_pow2 x) =
          SmtTerm.Apply SmtTerm.int_pow2 (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.int_pow2 (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := SmtTerm.int_pow2) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.int_pow2 x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_int_pow2_of_int x hxEo).symm
  case int_log2 =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.int_log2 x) =
          SmtTerm.Apply SmtTerm.int_log2 (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.int_log2 (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := SmtTerm.int_log2) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.int_log2 x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_int_log2_of_int x hxEo).symm
  case int_ispow2 =>
    let geqTerm :=
      SmtTerm.Apply (SmtTerm.Apply SmtTerm.geq (__eo_to_smt x)) (SmtTerm.Numeral 0)
    let eqTerm :=
      SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x))
        (SmtTerm.Apply SmtTerm.int_pow2 (SmtTerm.Apply SmtTerm.int_log2 (__eo_to_smt x)))
    have hTranslate :
        __eo_to_smt (Term.Apply Term.int_ispow2 x) =
          SmtTerm.Apply (SmtTerm.Apply SmtTerm.and geqTerm) eqTerm := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and geqTerm) eqTerm) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs :
        __smtx_typeof geqTerm = SmtType.Bool ∧
          __smtx_typeof eqTerm = SmtType.Bool :=
      bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl hApplyNN
    have hGeqNN : term_has_non_none_type geqTerm := by
      unfold term_has_non_none_type
      rw [hArgs.1]
      simp
    have hGeqArgs :
        (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
            __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int) ∨
          (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
            __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Real) :=
      arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq) rfl hGeqNN
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int := by
      rcases hGeqArgs with hInt | hReal
      · exact hInt.1
      · have hZeroReal := hReal.2
        simp [__smtx_typeof] at hZeroReal
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.int_ispow2 x)) = SmtType.Bool := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof geqTerm) SmtType.Bool)
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof eqTerm) SmtType.Bool)
            SmtType.Bool SmtType.None)
          SmtType.None) = SmtType.Bool
      simp [hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_int_ispow2_of_int x hxEo).symm
  case _at_int_div_by_zero =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_int_div_by_zero x) =
          SmtTerm.Apply (SmtTerm.Apply SmtTerm.div (__eo_to_smt x)) (SmtTerm.Numeral 0) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.div (__eo_to_smt x)) (SmtTerm.Numeral 0)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
        __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int :=
      int_binop_args_of_non_none (op := SmtTerm.div) (R := SmtType.Int) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgs.1]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArgs.1
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term._at_int_div_by_zero x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof (SmtTerm.Numeral 0)) SmtType.Int)
            SmtType.Int SmtType.None)
          SmtType.None) = SmtType.Int
      simp [hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_at_int_div_by_zero_of_int x hxEo).symm
  case _at_mod_by_zero =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_mod_by_zero x) =
          SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod (__eo_to_smt x)) (SmtTerm.Numeral 0) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.mod (__eo_to_smt x)) (SmtTerm.Numeral 0)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs : __smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
        __smtx_typeof (SmtTerm.Numeral 0) = SmtType.Int :=
      int_binop_args_of_non_none (op := SmtTerm.mod) (R := SmtType.Int) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgs.1]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArgs.1
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term._at_mod_by_zero x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (smt_lit_ite (smt_lit_Teq (__smtx_typeof (SmtTerm.Numeral 0)) SmtType.Int)
            SmtType.Int SmtType.None)
          SmtType.None) = SmtType.Int
      simp [hArgs.1, hArgs.2, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_at_mod_by_zero_of_int x hxEo).symm
  case _at_array_deq_diff x1 x2 =>
    have hHeadTranslate :
        __eo_to_smt (Term._at_array_deq_diff x1 x2) =
          let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))
          let _v2 := SmtTerm.Var "_at_x" _v0
          SmtTerm.Apply (SmtTerm.choice "_at_x" _v0)
            (SmtTerm.Apply SmtTerm.not
              (SmtTerm.Apply
                (SmtTerm.Apply SmtTerm.eq
                  (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt x1)) _v2))
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.select (__eo_to_smt x2)) _v2))) := by
      rw [__eo_to_smt.eq_def]
    have hTranslate :
        __eo_to_smt (Term.Apply (Term._at_array_deq_diff x1 x2) x) =
          SmtTerm.Apply (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hGeneric :
        generic_apply_type (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x) := by
      rw [hHeadTranslate]
      rfl
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      have hApplyNN' :
          __smtx_typeof
              (SmtTerm.Apply (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate] using hNonNone
      rw [hGeneric] at hApplyNN'
      exact hApplyNN'
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hHeadNN :
        __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) ≠ SmtType.None := by
      cases hHead with
      | inl hMap =>
          rw [hMap]
          simp
      | inr hDt =>
          rw [hDt]
          simp
    have hHeadEo :
        __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) = SmtType.Map A B ∨
          __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) = SmtType.FunType A B := by
      rw [← ihF hHeadNN]
      exact hHead
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term._at_array_deq_diff x1 x2) x)) = B := by
      rw [hTranslate]
      rw [hGeneric]
      cases hHead with
      | inl hMap =>
          simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hMap, hX, hA]
      | inr hDt =>
          simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hDt, hX, hA]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_at_array_deq_diff_of_smt_apply x x1 x2 A B hHeadEo hX).symm
  case _at_bvsize =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_bvsize x) =
          SmtTerm.Numeral (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) := by
      rw [__eo_to_smt.eq_def]
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term._at_bvsize x)) = SmtType.Int := by
      simpa [hTranslate, __smtx_typeof]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_at_bvsize x).symm
  case bvnot =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvnot x) =
          SmtTerm.Apply SmtTerm.bvnot (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.bvnot (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot) rfl hApplyNN with ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.bvnot x)) = SmtType.BitVec w := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_bv_op_1, hArg]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvnot_of_bitvec x w hxEo).symm
  case bvneg =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvneg x) =
          SmtTerm.Apply SmtTerm.bvneg (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.bvneg (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_arg_of_non_none (op := SmtTerm.bvneg) rfl hApplyNN with ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.bvneg x)) = SmtType.BitVec w := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_bv_op_1, hArg]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvneg_of_bitvec x w hxEo).symm
  case bvnego =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvnego x) =
          SmtTerm.Apply SmtTerm.bvnego (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.bvnego (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.bvnego) (ret := SmtType.Bool) rfl hApplyNN with
      ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.bvnego x)) = SmtType.Bool := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_bv_op_1_ret, hArg]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvnego_of_bitvec x w hxEo).symm
  case bvredand =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvredand x) =
          let _v0 := __eo_to_smt x
          SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp _v0)
            (SmtTerm.Apply SmtTerm.bvnot
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (let _v0 := __eo_to_smt x
           SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp _v0)
             (SmtTerm.Apply SmtTerm.bvnot
               (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0))) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1) rfl hApplyNN with
      ⟨w, hArgX, hArgY⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgX]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArgX
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hArgY' :
        __smtx_typeof
            (SmtTerm.Apply SmtTerm.bvnot
              (SmtTerm.Binary (__smtx_bv_sizeof_type (SmtType.BitVec w)) 0)) =
          SmtType.BitVec w := by
      simpa [hArgX] using hArgY
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.bvredand x)) = SmtType.BitVec 1 := by
      rw [hTranslate]
      change
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof
            (SmtTerm.Apply SmtTerm.bvnot
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)))
          (SmtType.BitVec 1) = SmtType.BitVec 1
      rw [hArgX, hArgY']
      simp [__smtx_typeof_bv_op_2_ret, smt_lit_ite, SmtEval.smt_lit_zeq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvredand_of_bitvec x w hxEo).symm
  case bvredor =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.bvredor x) =
          let _v0 := __eo_to_smt x
          SmtTerm.Apply SmtTerm.bvnot
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp _v0)
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0)) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (let _v0 := __eo_to_smt x
           SmtTerm.Apply SmtTerm.bvnot
             (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp _v0)
               (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof _v0)) 0))) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hInner :
        ∃ w : smt_lit_Int,
          __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp (__eo_to_smt x))
                (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)) =
            SmtType.BitVec w := by
      rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot) rfl hApplyNN with ⟨w, hInner⟩
      exact ⟨w, hInner⟩
    rcases hInner with ⟨_, hInnerTy⟩
    have hInnerNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp (__eo_to_smt x))
            (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)) := by
      unfold term_has_non_none_type
      rw [hInnerTy]
      simp
    rcases bv_binop_ret_args_of_non_none
        (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1) rfl hInnerNN with
      ⟨w, hArgX, hArgY⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgX]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArgX
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hArgY' :
        __smtx_typeof (SmtTerm.Binary (__smtx_bv_sizeof_type (SmtType.BitVec w)) 0) =
          SmtType.BitVec w := by
      simpa [hArgX] using hArgY
    have hInnerOne :
        __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.bvcomp (__eo_to_smt x))
              (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0)) =
          SmtType.BitVec 1 := by
      change
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof
            (SmtTerm.Binary (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))) 0))
          (SmtType.BitVec 1) = SmtType.BitVec 1
      rw [hArgX, hArgY']
      simp [__smtx_typeof_bv_op_2_ret, smt_lit_ite, SmtEval.smt_lit_zeq]
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.bvredor x)) = SmtType.BitVec 1 := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_bv_op_1, hInnerOne]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_bvredor_of_bitvec x w hxEo).symm
  case str_len =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_len x) =
          SmtTerm.Apply SmtTerm.str_len (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_len (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgExists : ∃ T, __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
      unfold term_has_non_none_type at hApplyNN
      cases h : __smtx_typeof (__eo_to_smt x) with
      | Seq T =>
          exact ⟨T, rfl⟩
      | _ =>
          simp [__smtx_typeof, __smtx_typeof_seq_op_1_ret, h] at hApplyNN
    rcases hArgExists with ⟨T, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
      rw [← hXTyped]
      exact hArg
    rcases eo_to_smt_type_eq_seq hxSmt with ⟨V, hxEo, hV⟩
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_len x)) = SmtType.Int := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_seq_op_1_ret, hArg]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_len_of_seq x V hxEo).symm
  case str_rev =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_rev x) =
          SmtTerm.Apply SmtTerm.str_rev (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_rev (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases seq_arg_of_non_none (op := SmtTerm.str_rev) rfl hApplyNN with ⟨T, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq T := by
      rw [← hXTyped]
      exact hArg
    rcases eo_to_smt_type_eq_seq hxSmt with ⟨V, hxEo, hV⟩
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_rev x)) = SmtType.Seq T := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_seq_op_1, hArg]
    have hEo :
        __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_rev x)) =
          SmtType.Seq (__eo_to_smt_type V) :=
      eo_to_smt_type_typeof_apply_str_rev_of_seq x V hxEo
    rw [hV] at hEo
    exact hSmt.trans hEo.symm
  case str_to_lower =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_lower x) =
          SmtTerm.Apply SmtTerm.str_to_lower (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_lower (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_lower) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_lower x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          (SmtType.Seq SmtType.Char) SmtType.None) = SmtType.Seq SmtType.Char
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_lower_of_seq_char x hxEo).symm
  case str_to_upper =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_upper x) =
          SmtTerm.Apply SmtTerm.str_to_upper (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_upper (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_upper) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_upper x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          (SmtType.Seq SmtType.Char) SmtType.None) = SmtType.Seq SmtType.Char
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_upper_of_seq_char x hxEo).symm
  case str_to_code =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_code x) =
          SmtTerm.Apply SmtTerm.str_to_code (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_code (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_code) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_code x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_code_of_seq_char x hxEo).symm
  case str_from_code =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_from_code x) =
          SmtTerm.Apply SmtTerm.str_from_code (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_from_code (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := SmtTerm.str_from_code) (R := SmtType.Seq SmtType.Char) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_from_code x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (SmtType.Seq SmtType.Char) SmtType.None) = SmtType.Seq SmtType.Char
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_code_of_int x hxEo).symm
  case str_is_digit =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_is_digit x) =
          SmtTerm.Apply SmtTerm.str_is_digit (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_is_digit (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_is_digit) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_is_digit x)) = SmtType.Bool := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          SmtType.Bool SmtType.None) = SmtType.Bool
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_is_digit_of_seq_char x hxEo).symm
  case str_to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_int x) =
          SmtTerm.Apply SmtTerm.str_to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_int) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_int x)) = SmtType.Int := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          SmtType.Int SmtType.None) = SmtType.Int
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_int_of_seq_char x hxEo).symm
  case str_from_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_from_int x) =
          SmtTerm.Apply SmtTerm.str_from_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_from_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
      int_ret_arg_of_non_none (op := SmtTerm.str_from_int) (R := SmtType.Seq SmtType.Char) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Int := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Int := eo_to_smt_type_eq_int hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.str_from_int x)) =
          SmtType.Seq SmtType.Char := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (SmtType.Seq SmtType.Char) SmtType.None) = SmtType.Seq SmtType.Char
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_from_int_of_int x hxEo).symm
  case _at_strings_stoi_non_digit =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_strings_stoi_non_digit x) =
          SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.str_indexof_re (__eo_to_smt x))
              (SmtTerm.Apply SmtTerm.re_comp
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range (SmtTerm.String "0"))
                  (SmtTerm.String "9"))))
            (SmtTerm.Numeral 0) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply
            (SmtTerm.Apply
              (SmtTerm.Apply SmtTerm.str_indexof_re (__eo_to_smt x))
              (SmtTerm.Apply SmtTerm.re_comp
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.re_range (SmtTerm.String "0"))
                  (SmtTerm.String "9"))))
            (SmtTerm.Numeral 0)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs := str_indexof_re_args_of_non_none hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArgs.1]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArgs.1
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term._at_strings_stoi_non_digit x)) =
          SmtType.Int := by
      rw [hTranslate]
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_at_strings_stoi_non_digit_of_seq_char x hxEo).symm
  case str_to_re =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.str_to_re x) =
          SmtTerm.Apply SmtTerm.str_to_re (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.str_to_re (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
      seq_char_arg_of_non_none (op := SmtTerm.str_to_re) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Seq SmtType.Char := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.Seq Term.Char := eo_to_smt_type_eq_seq_char hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.str_to_re x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite
          (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) (SmtType.Seq SmtType.Char))
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_str_to_re_of_seq_char x hxEo).symm
  case re_mult =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_mult x) =
          SmtTerm.Apply SmtTerm.re_mult (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_mult (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_mult) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_mult x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_mult_of_reglan x hxEo).symm
  case re_plus =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_plus x) =
          SmtTerm.Apply SmtTerm.re_plus (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_plus (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_plus) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_plus x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_plus_of_reglan x hxEo).symm
  case re_opt =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_opt x) =
          SmtTerm.Apply SmtTerm.re_opt (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_opt (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_opt) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_opt x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_opt_of_reglan x hxEo).symm
  case re_comp =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.re_comp x) =
          SmtTerm.Apply SmtTerm.re_comp (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.re_comp (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
      reglan_arg_of_non_none (op := SmtTerm.re_comp) rfl hApplyNN
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.RegLan := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.RegLan := eo_to_smt_type_eq_reglan hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.re_comp x)) = SmtType.RegLan := by
      rw [hTranslate]
      change
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None) = SmtType.RegLan
      simp [hArg, smt_lit_ite, smt_lit_Teq]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_re_comp_of_reglan x hxEo).symm
  case seq_unit =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.seq_unit x) =
          SmtTerm.Apply SmtTerm.seq_unit (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      intro hXNone
      apply hNonNone
      rw [hTranslate]
      simp [__smtx_typeof, hXNone, smt_lit_ite, smt_lit_Teq]
    have hXTyped := ihX hXNonNone
    have hxEoNonNone : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
      rw [← hXTyped]
      exact hXNonNone
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.seq_unit x)) =
          SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
      rw [hTranslate]
      simp [__smtx_typeof, hXTyped, smt_lit_ite, smt_lit_Teq, hxEoNonNone]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_seq_unit_of_non_none x hxEoNonNone).symm
  case is =>
    exfalso
    apply hNonNone
    rw [__eo_to_smt.eq_def]
    simpa using smtx_typeof_eo_to_smt_tester_none (__eo_to_smt x)
  case set_empty T =>
    exfalso
    apply hNonNone
    have hTranslate :
        __eo_to_smt (Term.Apply (Term.set_empty T) x) =
          SmtTerm.Apply (__eo_to_smt_set_empty (__eo_to_smt_type T)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
      change (__eo_to_smt (Term.set_empty T)).Apply (__eo_to_smt x) =
          SmtTerm.Apply (__eo_to_smt_set_empty (__eo_to_smt_type T)) (__eo_to_smt x)
      rw [eo_to_smt_set_empty]
    rw [hTranslate]
    cases hT : __eo_to_smt_type T with
    | Set U =>
        by_cases hInh : smt_lit_inhabited_type U = true
        · simp [__eo_to_smt_set_empty, __smtx_typeof_apply,
            __smtx_typeof_guard_inhabited, hInh, smt_lit_ite]
        · simp [__eo_to_smt_set_empty, __smtx_typeof_apply,
            __smtx_typeof_guard_inhabited, hInh, smt_lit_ite]
    | None
    | Bool
    | Int
    | Real
    | RegLan
    | BitVec _
    | Seq _
    | Char
    | Datatype _ _
    | TypeRef _
    | USort _
    | Map _ _
    | FunType _ _ =>
        simp [__eo_to_smt_set_empty, __smtx_typeof_apply]
  case set_singleton =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.set_singleton x) =
          SmtTerm.Apply SmtTerm.set_singleton (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      intro hXNone
      apply hNonNone
      rw [hTranslate]
      simp [__smtx_typeof, hXNone, smt_lit_ite, smt_lit_Teq]
    have hXTyped := ihX hXNonNone
    have hxEoNonNone : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None := by
      rw [← hXTyped]
      exact hXNonNone
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton x)) =
          SmtType.Set (__eo_to_smt_type (__eo_typeof x)) := by
      rw [hTranslate]
      simp [__smtx_typeof, hXTyped, smt_lit_ite, smt_lit_Teq, hxEoNonNone]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_set_singleton_of_non_none x hxEoNonNone).symm
  case set_is_empty =>
    exfalso
    have hTranslate :
        __eo_to_smt (Term.Apply Term.set_is_empty x) =
          let _v0 := __eo_to_smt x
          SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq _v0) (SmtTerm.set_empty (__smtx_typeof _v0)) := by
      rw [__eo_to_smt.eq_def]
    have hEqNN :
        __smtx_typeof_eq
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof_guard_inhabited
              (__smtx_typeof (__eo_to_smt x))
              (SmtType.Set (__smtx_typeof (__eo_to_smt x)))) ≠
          SmtType.None := by
      simpa [hTranslate, __smtx_typeof] using hNonNone
    have hEqArgs := smtx_typeof_eq_non_none hEqNN
    exact smt_type_ne_guard_inhabited_set_self hEqArgs.2 <| by
      simpa [__smtx_typeof] using hEqArgs.1
  case set_is_singleton =>
    let T := __eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose x))
    have hTranslate :
        __eo_to_smt (Term.Apply Term.set_is_singleton x) =
          SmtTerm.Apply (SmtTerm.exists "_at_x" T)
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x))
              (SmtTerm.Apply SmtTerm.set_singleton (SmtTerm.Var "_at_x" T))) := by
      rw [__eo_to_smt.eq_def]
    have hExistsNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.exists "_at_x" T)
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x))
              (SmtTerm.Apply SmtTerm.set_singleton (SmtTerm.Var "_at_x" T)))) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hBodyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x))
            (SmtTerm.Apply SmtTerm.set_singleton (SmtTerm.Var "_at_x" T))) := by
      unfold term_has_non_none_type
      rw [exists_body_bool_of_non_none hExistsNN]
      simp
    have hEqNN :
        __smtx_typeof_eq
            (__smtx_typeof (__eo_to_smt x))
            (__smtx_typeof (SmtTerm.Apply SmtTerm.set_singleton (SmtTerm.Var "_at_x" T))) ≠
          SmtType.None := by
      unfold term_has_non_none_type at hBodyNN
      simpa [__smtx_typeof] using hBodyNN
    have hEqArgs := smtx_typeof_eq_non_none hEqNN
    have hSingletonNN :
        __smtx_typeof (SmtTerm.Apply SmtTerm.set_singleton (SmtTerm.Var "_at_x" T)) ≠
          SmtType.None := by
      rw [← hEqArgs.1]
      exact hEqArgs.2
    have hVarNN : __smtx_typeof (SmtTerm.Var "_at_x" T) ≠ SmtType.None := by
      intro hVarNone
      apply hSingletonNN
      simp [__smtx_typeof, hVarNone, smt_lit_ite, smt_lit_Teq]
    have hTNonNone : T ≠ SmtType.None := by
      intro hTNone
      apply hVarNN
      simpa [hTNone, __smtx_typeof, __smtx_typeof_guard_inhabited, smt_lit_ite]
    have hVarTy : __smtx_typeof (SmtTerm.Var "_at_x" T) = T := by
      simpa using smtx_typeof_var_of_non_none "_at_x" T hVarNN
    have hXTy :
        __smtx_typeof (__eo_to_smt x) = SmtType.Set T := by
      rw [hEqArgs.1]
      simp [__smtx_typeof, hVarTy, smt_lit_ite, smt_lit_Teq, hTNonNone]
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term.set_is_singleton x)) = SmtType.Bool := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_eq, __smtx_typeof_guard,
        smt_lit_ite, smt_lit_Teq, hXTy, hVarTy, hTNonNone]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_set_is_singleton_of_smt_set x hXTy).symm
  case _at_sets_deq_diff x1 x2 =>
    have hHeadTranslate :
        __eo_to_smt (Term._at_sets_deq_diff x1 x2) =
          let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))
          let _v2 := SmtTerm.Apply SmtTerm.set_member (SmtTerm.Var "_at_x" _v0)
          SmtTerm.Apply (SmtTerm.choice "_at_x" _v0)
            (SmtTerm.Apply SmtTerm.not
              (SmtTerm.Apply
                (SmtTerm.Apply SmtTerm.eq (SmtTerm.Apply _v2 (__eo_to_smt x1)))
                (SmtTerm.Apply _v2 (__eo_to_smt x2)))) := by
      rw [__eo_to_smt.eq_def]
    have hTranslate :
        __eo_to_smt (Term.Apply (Term._at_sets_deq_diff x1 x2) x) =
          SmtTerm.Apply (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hGeneric :
        generic_apply_type (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x) := by
      rw [hHeadTranslate]
      rfl
    have hApplyNN :
        __smtx_typeof_apply
            (__smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)))
            (__smtx_typeof (__eo_to_smt x)) ≠
          SmtType.None := by
      have hApplyNN' :
          __smtx_typeof
              (SmtTerm.Apply (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x)) ≠
            SmtType.None := by
        simpa [hTranslate] using hNonNone
      rw [hGeneric] at hApplyNN'
      exact hApplyNN'
    rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHead, hX, hA, hB⟩
    have hHeadNN :
        __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) ≠ SmtType.None := by
      cases hHead with
      | inl hMap =>
          rw [hMap]
          simp
      | inr hDt =>
          rw [hDt]
          simp
    have hHeadEo :
        __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) = SmtType.Map A B ∨
          __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) = SmtType.FunType A B := by
      rw [← ihF hHeadNN]
      exact hHead
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply (Term._at_sets_deq_diff x1 x2) x)) = B := by
      rw [hTranslate]
      rw [hGeneric]
      cases hHead with
      | inl hMap =>
          simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hMap, hX, hA]
      | inr hDt =>
          simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hDt, hX, hA]
    exact hSmt.trans
      (eo_to_smt_type_typeof_apply_at_sets_deq_diff_of_smt_apply x x1 x2 A B hHeadEo hX).symm
  case _at_div_by_zero =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term._at_div_by_zero x) =
          SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv (__eo_to_smt x))
            (SmtTerm.Rational (smt_lit_mk_rational 0 1)) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.qdiv (__eo_to_smt x))
            (SmtTerm.Rational (smt_lit_mk_rational 0 1))) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    have hArgs :
        (__smtx_typeof (__eo_to_smt x) = SmtType.Int ∧
            __smtx_typeof (SmtTerm.Rational (smt_lit_mk_rational 0 1)) = SmtType.Int) ∨
          (__smtx_typeof (__eo_to_smt x) = SmtType.Real ∧
            __smtx_typeof (SmtTerm.Rational (smt_lit_mk_rational 0 1)) = SmtType.Real) :=
      arith_binop_ret_args_of_non_none (op := SmtTerm.qdiv) (R := SmtType.Real) rfl hApplyNN
    have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Real := by
      rcases hArgs with hInt | hReal
      · have hZeroInt := hInt.2
        simp [__smtx_typeof] at hZeroInt
      · exact hReal.1
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.Real := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Real := eo_to_smt_type_eq_real hxSmt
    have hSmt :
        __smtx_typeof (__eo_to_smt (Term.Apply Term._at_div_by_zero x)) = SmtType.Real := by
      rw [hTranslate]
      change
        (__smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (SmtTerm.Rational (smt_lit_mk_rational 0 1)))
          SmtType.Real) = SmtType.Real
      simp [__smtx_typeof_arith_overload_op_2_ret, __smtx_typeof, hArg]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_at_div_by_zero_of_real x hxEo).symm
  case _at_quantifiers_skolemize x1 x2 =>
    sorry
  case ubv_to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.ubv_to_int x) =
          SmtTerm.Apply SmtTerm.ubv_to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.ubv_to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.ubv_to_int) (ret := SmtType.Int) rfl hApplyNN with
      ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.ubv_to_int x)) = SmtType.Int := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_bv_op_1_ret, hArg]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_ubv_to_int_of_bitvec x w hxEo).symm
  case sbv_to_int =>
    have hTranslate :
        __eo_to_smt (Term.Apply Term.sbv_to_int x) =
          SmtTerm.Apply SmtTerm.sbv_to_int (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    have hApplyNN : term_has_non_none_type (SmtTerm.Apply SmtTerm.sbv_to_int (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      rw [← hTranslate]
      exact hNonNone
    rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.sbv_to_int) (ret := SmtType.Int) rfl hApplyNN with
      ⟨w, hArg⟩
    have hXNonNone : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
      rw [hArg]
      simp
    have hXTyped := ihX hXNonNone
    have hxSmt : __eo_to_smt_type (__eo_typeof x) = SmtType.BitVec w := by
      rw [← hXTyped]
      exact hArg
    have hxEo : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w) :=
      eo_to_smt_type_eq_bitvec hxSmt
    have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply Term.sbv_to_int x)) = SmtType.Int := by
      rw [hTranslate]
      simp [__smtx_typeof, __smtx_typeof_bv_op_1_ret, hArg]
    exact hSmt.trans (eo_to_smt_type_typeof_apply_sbv_to_int_of_bitvec x w hxEo).symm
  all_goals
    sorry

end TranslationProofs
