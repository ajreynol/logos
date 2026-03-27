import Cpc.Proofs.TypePreservation.Helpers

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true

namespace Smtm

theorem typeof_concat_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2) =
      __smtx_typeof_concat (__smtx_typeof t1) (__smtx_typeof t2) := rfl

theorem typeof_extract_eq
    (t1 t2 t3 : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Apply SmtTerm.extract t1) t2) t3) =
      __smtx_typeof_extract t1 t2 (__smtx_typeof t3) := rfl

theorem typeof_repeat_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.__smt_repeat t1) t2) =
      __smtx_typeof_repeat t1 (__smtx_typeof t2) := rfl

theorem typeof_zero_extend_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2) =
      __smtx_typeof_zero_extend t1 (__smtx_typeof t2) := rfl

theorem typeof_sign_extend_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2) =
      __smtx_typeof_sign_extend t1 (__smtx_typeof t2) := rfl

theorem typeof_rotate_left_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left t1) t2) =
      __smtx_typeof_rotate_left t1 (__smtx_typeof t2) := rfl

theorem typeof_rotate_right_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right t1) t2) =
      __smtx_typeof_rotate_right t1 (__smtx_typeof t2) := rfl

theorem typeof_int_to_bv_eq
    (t1 t2 : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2) =
      __smtx_typeof_int_to_bv t1 (__smtx_typeof t2) := rfl

theorem bv_concat_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.concat t1) t2)) :
    ∃ w1 w2 : smt_lit_Int,
      __smtx_typeof t1 = SmtType.BitVec w1 ∧
        __smtx_typeof t2 = SmtType.BitVec w2 := by
  have ht' : __smtx_typeof_concat (__smtx_typeof t1) (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_concat_eq t1 t2]
    exact ht
  cases h1 : __smtx_typeof t1 with
  | BitVec w1 =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w2 =>
          exact ⟨w1, w2, rfl, rfl⟩
      | _ =>
          simp [__smtx_typeof_concat, h1, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_concat, h1, h2] at ht'

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
  have ht' : __smtx_typeof_extract t1 t2 (__smtx_typeof t3) ≠ SmtType.None := by
    rw [← typeof_extract_eq t1 t2 t3]
    exact ht
  cases t1 with
  | Numeral i =>
      cases t2 with
      | Numeral j =>
          cases h3 : __smtx_typeof t3 with
          | BitVec w =>
              by_cases hj0 : smt_lit_zleq 0 j = true
              · by_cases hji : smt_lit_zleq j i = true
                · by_cases hiw : smt_lit_zlt i w = true
                  · exact ⟨i, j, w, rfl, rfl, rfl, hj0, hji, hiw⟩
                  · exfalso
                    exact ht' (by
                      simp [__smtx_typeof_extract, smt_lit_ite, h3, hj0, hji, hiw])
                · exfalso
                  exact ht' (by
                    simp [__smtx_typeof_extract, smt_lit_ite, h3, hj0, hji])
              · exfalso
                exact ht' (by
                  simp [__smtx_typeof_extract, smt_lit_ite, h3, hj0])
          | _ =>
              simp [__smtx_typeof_extract, h3] at ht'
      | _ =>
          simp [__smtx_typeof_extract] at ht'
  | _ =>
      simp [__smtx_typeof_extract] at ht'

theorem repeat_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.__smt_repeat t1) t2)) :
    ∃ i w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        smt_lit_zleq 1 i = true := by
  have ht' : __smtx_typeof_repeat t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_repeat_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi1 : smt_lit_zleq 1 i = true
          · exact ⟨i, w, rfl, rfl, hi1⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_repeat, smt_lit_ite, h2, hi1])
      | _ =>
          simp [__smtx_typeof_repeat, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_repeat] at ht'

theorem zero_extend_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.zero_extend t1) t2)) :
    ∃ i w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        smt_lit_zleq 0 i = true := by
  have ht' : __smtx_typeof_zero_extend t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_zero_extend_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi0 : smt_lit_zleq 0 i = true
          · exact ⟨i, w, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_zero_extend, smt_lit_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_zero_extend, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_zero_extend] at ht'

theorem sign_extend_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.sign_extend t1) t2)) :
    ∃ i w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        smt_lit_zleq 0 i = true := by
  have ht' : __smtx_typeof_sign_extend t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_sign_extend_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi0 : smt_lit_zleq 0 i = true
          · exact ⟨i, w, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_sign_extend, smt_lit_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_sign_extend, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_sign_extend] at ht'

theorem rotate_left_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_left t1) t2)) :
    ∃ i w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        smt_lit_zleq 0 i = true := by
  have ht' : __smtx_typeof_rotate_left t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_rotate_left_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi0 : smt_lit_zleq 0 i = true
          · exact ⟨i, w, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_rotate_left, smt_lit_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_rotate_left, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_rotate_left] at ht'

theorem rotate_right_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.rotate_right t1) t2)) :
    ∃ i w : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.BitVec w ∧
        smt_lit_zleq 0 i = true := by
  have ht' : __smtx_typeof_rotate_right t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_rotate_right_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | BitVec w =>
          by_cases hi0 : smt_lit_zleq 0 i = true
          · exact ⟨i, w, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_rotate_right, smt_lit_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_rotate_right, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_rotate_right] at ht'

theorem int_to_bv_args_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.Apply SmtTerm.int_to_bv t1) t2)) :
    ∃ i : smt_lit_Int,
      t1 = SmtTerm.Numeral i ∧
        __smtx_typeof t2 = SmtType.Int ∧
        smt_lit_zleq 0 i = true := by
  have ht' : __smtx_typeof_int_to_bv t1 (__smtx_typeof t2) ≠ SmtType.None := by
    rw [← typeof_int_to_bv_eq t1 t2]
    exact ht
  cases t1 with
  | Numeral i =>
      cases h2 : __smtx_typeof t2 with
      | Int =>
          by_cases hi0 : smt_lit_zleq 0 i = true
          · exact ⟨i, rfl, rfl, hi0⟩
          · exfalso
            exact ht' (by
              simp [__smtx_typeof_int_to_bv, smt_lit_ite, h2, hi0])
      | _ =>
          simp [__smtx_typeof_int_to_bv, h2] at ht'
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [__smtx_typeof_int_to_bv] at ht'

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
          simp [hTy, __smtx_typeof_bv_op_2, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_bv_op_2, h1, h2] at ht

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
          simp [hTy, __smtx_typeof_bv_op_2_ret, h1, h2] at ht
  | _ =>
      cases h2 : __smtx_typeof t2 <;>
        simp [hTy, __smtx_typeof_bv_op_2_ret, h1, h2] at ht


end Smtm
