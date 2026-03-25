import Cpc.TypePreservation.Helpers

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

theorem bv_concat_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2)) :
    ∃ w1 w2 : smt_lit_Int,
      __smtx_typeof t1 = SmtType.BitVec w1 ∧
        __smtx_typeof t2 = SmtType.BitVec w2 := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          exact ⟨w1, w2, rfl, rfl⟩
      | _ =>
          simp [__smtx_typeof, __smtx_typeof_concat, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof, __smtx_typeof_concat, h1, h2] at ht

theorem extract_args_of_non_none
    {t1 t2 t3 : SmtTerm}
    (ht : term_has_non_none_type
      (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3)) :
    ∃ i j w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        t2 = SmtTerm.Numeral j ∧
        __smtx_typeof t3 = SmtType.BitVec w ∧
        smt_lit_zleq 0 j = true ∧
        smt_lit_zleq j i = true ∧
        smt_lit_zlt i w = true := by
  unfold term_has_non_none_type at ht
  cases t1 <;> cases t2 <;> cases h3 : __smtx_typeof t3 <;>
    simp [__smtx_typeof, __smtx_typeof_extract, smt_lit_ite, h3] at ht
  case Numeral.Numeral i j =>
    rename_i i j w
    by_cases hj0 : smt_lit_zleq 0 j = true
    · by_cases hji : smt_lit_zleq j i = true
      · by_cases hiw : smt_lit_zlt i w = true
        · exact ⟨i, j, w, rfl, rfl, h3, hj0, hji, hiw⟩
        · exfalso
          exact ht (by
            simp [__smtx_typeof, __smtx_typeof_extract, smt_lit_ite, h3, hj0, hji, hiw])
      · exfalso
        exact ht (by
          simp [__smtx_typeof, __smtx_typeof_extract, smt_lit_ite, h3, hj0, hji])
    · exfalso
      exact ht (by
        simp [__smtx_typeof, __smtx_typeof_extract, smt_lit_ite, h3, hj0])

theorem zero_extend_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2)) :
    ∃ i w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        smt_lit_zleq 0 i = true := by
  unfold term_has_non_none_type at ht
  cases t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_zero_extend, smt_lit_ite, h2] at ht
  case Numeral.Numeral i =>
    rename_i i w
    by_cases hi0 : smt_lit_zleq 0 i = true
    · exact ⟨i, w, rfl, h2, hi0⟩
    · exfalso
      exact ht (by
        simp [__smtx_typeof, __smtx_typeof_zero_extend, smt_lit_ite, h2, hi0])

theorem sign_extend_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2)) :
    ∃ i w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        smt_lit_zleq 0 i = true := by
  unfold term_has_non_none_type at ht
  cases t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_sign_extend, smt_lit_ite, h2] at ht
  case Numeral.Numeral i =>
    rename_i i w
    by_cases hi0 : smt_lit_zleq 0 i = true
    · exact ⟨i, w, rfl, h2, hi0⟩
    · exfalso
      exact ht (by
        simp [__smtx_typeof, __smtx_typeof_sign_extend, smt_lit_ite, h2, hi0])

theorem int_to_bv_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2)) :
    ∃ i : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.Int ∧
        smt_lit_zleq 0 i = true := by
  unfold term_has_non_none_type at ht
  cases t1 <;> cases h2 : __smtx_typeof t2 <;>
    simp [__smtx_typeof, __smtx_typeof_int_to_bv, smt_lit_ite, h2] at ht
  case Numeral.Numeral i =>
    by_cases hi0 : smt_lit_zleq 0 i = true
    · exact ⟨i, rfl, h2, hi0⟩
    · exfalso
      exact ht (by
        simp [__smtx_typeof, __smtx_typeof_int_to_bv, smt_lit_ite, h2, hi0])

theorem bv_unop_arg_of_non_none
    {op t : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        __smtx_typeof_bv_op_1 (__smtx_typeof t))
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    ∃ w : smt_lit_Int, __smtx_typeof t = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | BitVec w =>
      exact ⟨w, rfl⟩
  | _ =>
      simp [hTy, __smtx_typeof_bv_op_1, h] at ht

theorem bv_unop_ret_arg_of_non_none
    {op t : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply op t) =
        __smtx_typeof_bv_op_1_ret (__smtx_typeof t) ret)
    (ht : term_has_non_none_type (SmtTerm.Apply op t)) :
    ∃ w : smt_lit_Int, __smtx_typeof t = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof t with
  | BitVec w =>
      exact ⟨w, rfl⟩
  | _ =>
      simp [hTy, __smtx_typeof_bv_op_1_ret, h] at ht

theorem bv_binop_args_of_non_none
    {op t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    ∃ w : smt_lit_Int,
      __smtx_typeof t1 = SmtType.BitVec w ∧
        __smtx_typeof t2 = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          by_cases hEq : smt_lit_zeq w1 w2 = true
          · have hw : w1 = w2 := by
              simpa [SmtEval.smt_lit_zeq] using hEq
            cases hw
            exact ⟨w1, rfl, rfl⟩
          · exfalso
            exact ht (by
              simp [hTy, __smtx_typeof_bv_op_2, smt_lit_ite, h1, h2, hEq])
      | _ =>
          simp [hTy, __smtx_typeof_bv_op_2, smt_lit_ite, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_bv_op_2, smt_lit_ite, h1, h2] at ht

theorem bv_binop_ret_args_of_non_none
    {op t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply op t1) t2) =
        __smtx_typeof_bv_op_2_ret (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply op t1) t2)) :
    ∃ w : smt_lit_Int,
      __smtx_typeof t1 = SmtType.BitVec w ∧
        __smtx_typeof t2 = SmtType.BitVec w := by
  unfold term_has_non_none_type at ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          by_cases hEq : smt_lit_zeq w1 w2 = true
          · have hw : w1 = w2 := by
              simpa [SmtEval.smt_lit_zeq] using hEq
            cases hw
            exact ⟨w1, rfl, rfl⟩
          · exfalso
            exact ht (by
              simp [hTy, __smtx_typeof_bv_op_2_ret, smt_lit_ite, h1, h2, hEq])
      | _ =>
          simp [hTy, __smtx_typeof_bv_op_2_ret, smt_lit_ite, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_bv_op_2_ret, smt_lit_ite, h1, h2] at ht


end Smtm
