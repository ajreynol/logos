import Cpc.Proofs.Common
import Cpc.Proofs.Assumptions
import Cpc.Proofs.Closed.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

abbrev __str_nary_intro : Term -> Term :=
  __eo_list_singleton_intro (Term.UOp UserOp.str_concat)

abbrev __str_nary_elim : Term -> Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.str_concat)

abbrev __re_nary_intro : Term -> Term :=
  __eo_list_singleton_intro (Term.UOp UserOp.re_concat)

abbrev __re_nary_elim : Term -> Term :=
  __eo_list_singleton_elim (Term.UOp UserOp.re_concat)

/-- Stable rewrite for evaluating SMT equality terms. -/
theorem smtx_eval_eq_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.eq x y) =
      __smtx_model_eval_eq (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT if-then-else terms. -/
theorem smtx_eval_ite_term_eq
    (M : SmtModel) (c t e : SmtTerm) :
    __smtx_model_eval M (SmtTerm.ite c t e) =
      __smtx_model_eval_ite
        (__smtx_model_eval M c) (__smtx_model_eval M t)
        (__smtx_model_eval M e) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT negation terms. -/
theorem smtx_eval_not_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.not x) =
      __smtx_model_eval_not (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT conjunction terms. -/
theorem smtx_eval_and_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.and x y) =
      __smtx_model_eval_and (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT disjunction terms. -/
theorem smtx_eval_or_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.or x y) =
      __smtx_model_eval_or (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT implication terms. -/
theorem smtx_eval_imp_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.imp x y) =
      __smtx_model_eval_imp (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT unsigned bit-vector-to-int terms. -/
theorem smtx_eval_ubv_to_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.ubv_to_int x) =
      __smtx_model_eval_ubv_to_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT signed bit-vector-to-int terms. -/
theorem smtx_eval_sbv_to_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.sbv_to_int x) =
      __smtx_model_eval_sbv_to_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT int-to-bit-vector terms. -/
theorem smtx_eval_int_to_bv_term_eq
    (M : SmtModel) (w x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.int_to_bv w x) =
      __smtx_model_eval_int_to_bv
        (__smtx_model_eval M w) (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

@[simp] theorem smtx_eval_int_to_bv_numerals
    (M : SmtModel) (w k : native_Int) :
    __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral w) (SmtTerm.Numeral k)) =
      SmtValue.Binary w (native_mod_total k (native_int_pow2 w)) := by
  rw [smtx_eval_int_to_bv_term_eq]
  change
    __smtx_model_eval_int_to_bv (SmtValue.Numeral w) (SmtValue.Numeral k) =
      SmtValue.Binary w (native_mod_total k (native_int_pow2 w))
  rfl

theorem support_eo_requires_cond_eq_of_non_stuck {x y z : Term}
    (h : __eo_requires x y z ≠ Term.Stuck) :
    x = y := by
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · have hxyFalse : native_teq x y = false := by
      cases hTeq : native_teq x y <;> simp_all
    simp [native_ite, hxyFalse] at h

theorem support_eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

theorem support_eo_typeof_eq_bool_operands_eq (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

theorem eo_requires_eq_true_stuck_of_ne (x y B : Term) :
    x ≠ y ->
    __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck := by
  intro hNe
  by_cases hReq :
      __eo_requires (__eo_eq x y) (Term.Boolean true) B = Term.Stuck
  · exact hReq
  · have hEq : y = x :=
      support_eq_of_eo_eq_true x y (support_eo_requires_cond_eq_of_non_stuck hReq)
    exact False.elim (hNe hEq.symm)

theorem bv_width_eq_of_typeof_bvand_at_bv_left_bool (n w : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hTy :
      __eo_typeof_eq
        (__eo_typeof_bvand
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))
          (Term.Apply (Term.UOp UserOp.BitVec) w))
        (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)) =
      Term.Bool) :
    w = n := by
  have hTy' :
      __eo_typeof_eq
        (__eo_typeof_bvand
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n))
          (Term.Apply (Term.UOp UserOp.BitVec) w))
        (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)) =
      Term.Bool := by
    simpa [__eo_typeof_int_to_bv, hNTy, hN] using hTy
  have hAtReqNN :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    intro hReq
    simp [__eo_typeof_eq, __eo_typeof_bvand, hReq] at hTy'
  have hAtGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hAtReqNN
  have hAtReqEq :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simp [__eo_requires, hAtGuard, native_ite, native_teq, native_not]
  have hTypesEq :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof_bvand
        (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n))
        (Term.Apply (Term.UOp UserOp.BitVec) w))
      (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
        (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n))
      hTy'
  have hReqEq :
      __eo_requires (__eo_eq n w) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simpa [__eo_typeof_bvand, hAtReqEq] using hTypesEq
  have hReqNN :
      __eo_requires (__eo_eq n w) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    rw [hReqEq]
    intro h
    cases h
  exact support_eq_of_eo_eq_true n w
    (support_eo_requires_cond_eq_of_non_stuck hReqNN)

theorem bv_width_eq_of_typeof_bvand_at_bv_right_bool (w n : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hTy :
      __eo_typeof_eq
        (__eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)))
        (Term.Apply (Term.UOp UserOp.BitVec) w) =
      Term.Bool) :
    n = w := by
  have hTy' :
      __eo_typeof_eq
        (__eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
        (Term.Apply (Term.UOp UserOp.BitVec) w) =
      Term.Bool := by
    simpa [__eo_typeof_int_to_bv, hNTy, hN] using hTy
  have hAtReqNN :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    intro hReq
    simp [__eo_typeof_eq, __eo_typeof_bvand, hReq] at hTy'
  have hAtGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hAtReqNN
  have hAtReqEq :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simp [__eo_requires, hAtGuard, native_ite, native_teq, native_not]
  have hTypesEq :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) w)
        (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
      (Term.Apply (Term.UOp UserOp.BitVec) w)
      hTy'
  have hReqEq :
      __eo_requires (__eo_eq w n) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) w := by
    simpa [__eo_typeof_bvand, hAtReqEq] using hTypesEq
  have hReqNN :
      __eo_requires (__eo_eq w n) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck := by
    rw [hReqEq]
    intro h
    cases h
  exact support_eq_of_eo_eq_true w n
    (support_eo_requires_cond_eq_of_non_stuck hReqNN)

theorem bv_width_eq_of_typeof_bvand_at_bv_right_at_bv_bool (w n : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hTy :
      __eo_typeof_eq
        (__eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)))
        (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)) =
      Term.Bool) :
    n = w := by
  have hTy' :
      __eo_typeof_eq
        (__eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
        (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)) =
      Term.Bool := by
    simpa [__eo_typeof_int_to_bv, hNTy, hN] using hTy
  have hAtReqNN :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    intro hReq
    simp [__eo_typeof_eq, __eo_typeof_bvand, hReq] at hTy'
  have hAtGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hAtReqNN
  have hAtReqEq :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simp [__eo_requires, hAtGuard, native_ite, native_teq, native_not]
  have hTypesEq :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) w)
        (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
      (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
        (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n))
      hTy'
  have hReqEq :
      __eo_requires (__eo_eq w n) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simpa [__eo_typeof_bvand, hAtReqEq] using hTypesEq
  have hReqNN :
      __eo_requires (__eo_eq w n) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck := by
    rw [hReqEq]
    intro h
    cases h
  exact support_eq_of_eo_eq_true w n
    (support_eo_requires_cond_eq_of_non_stuck hReqNN)

theorem bv_width_eq_of_typeof_bvand_at_bv_right_bvnot_at_bv_bool
    (w n : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hTy :
      __eo_typeof_eq
        (__eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)))
        (__eo_typeof_bvnot
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))) =
      Term.Bool) :
    n = w := by
  have hTy' :
      __eo_typeof_eq
        (__eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
        (__eo_typeof_bvnot
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n))) =
      Term.Bool := by
    simpa [__eo_typeof_int_to_bv, hNTy, hN] using hTy
  have hAtReqNN :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    intro hReq
    simp [__eo_typeof_eq, __eo_typeof_bvand, __eo_typeof_bvnot, hReq] at hTy'
  have hAtGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hAtReqNN
  have hAtReqEq :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simp [__eo_requires, hAtGuard, native_ite, native_teq, native_not]
  have hTypesEq :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof_bvand (Term.Apply (Term.UOp UserOp.BitVec) w)
        (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
      (__eo_typeof_bvnot
        (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
      hTy'
  have hReqEq :
      __eo_requires (__eo_eq w n) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) w) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simpa [__eo_typeof_bvand, __eo_typeof_bvnot, hAtReqEq] using hTypesEq
  have hReqNN :
      __eo_requires (__eo_eq w n) (Term.Boolean true)
          (Term.Apply (Term.UOp UserOp.BitVec) w) ≠
        Term.Stuck := by
    rw [hReqEq]
    intro h
    cases h
  exact support_eq_of_eo_eq_true w n
    (support_eo_requires_cond_eq_of_non_stuck hReqNN)

theorem bv_width_eq_of_typeof_bvult_at_bv_left_bool (n w : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hTy :
      __eo_typeof_eq
        (__eo_typeof_bvult
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))
          (Term.Apply (Term.UOp UserOp.BitVec) w))
        Term.Bool =
      Term.Bool) :
    w = n := by
  have hTy' :
      __eo_typeof_eq
        (__eo_typeof_bvult
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n))
          (Term.Apply (Term.UOp UserOp.BitVec) w))
        Term.Bool =
      Term.Bool := by
    simpa [__eo_typeof_int_to_bv, hNTy, hN] using hTy
  have hAtReqNN :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    intro hReq
    simp [__eo_typeof_eq, __eo_typeof_bvult, hReq] at hTy'
  have hAtGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hAtReqNN
  have hAtReqEq :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simp [__eo_requires, hAtGuard, native_ite, native_teq, native_not]
  have hTypesEq :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof_bvult
        (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n))
        (Term.Apply (Term.UOp UserOp.BitVec) w))
      Term.Bool
      hTy'
  have hReqEq :
      __eo_requires (__eo_eq n w) (Term.Boolean true) Term.Bool =
        Term.Bool := by
    simpa [__eo_typeof_bvult, hAtReqEq] using hTypesEq
  have hReqNN :
      __eo_requires (__eo_eq n w) (Term.Boolean true) Term.Bool ≠
        Term.Stuck := by
    rw [hReqEq]
    intro h
    cases h
  exact support_eq_of_eo_eq_true n w
    (support_eo_requires_cond_eq_of_non_stuck hReqNN)

theorem bv_width_eq_of_typeof_bvult_at_bv_right_bool (w n : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hTy :
      __eo_typeof_eq
        (__eo_typeof_bvult (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)))
        Term.Bool =
      Term.Bool) :
    n = w := by
  have hTy' :
      __eo_typeof_eq
        (__eo_typeof_bvult (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
        Term.Bool =
      Term.Bool := by
    simpa [__eo_typeof_int_to_bv, hNTy, hN] using hTy
  have hAtReqNN :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    intro hReq
    simp [__eo_typeof_eq, __eo_typeof_bvult, hReq] at hTy'
  have hAtGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hAtReqNN
  have hAtReqEq :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simp [__eo_requires, hAtGuard, native_ite, native_teq, native_not]
  have hTypesEq :=
    support_eo_typeof_eq_bool_operands_eq
      (__eo_typeof_bvult (Term.Apply (Term.UOp UserOp.BitVec) w)
        (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
      Term.Bool
      hTy'
  have hReqEq :
      __eo_requires (__eo_eq w n) (Term.Boolean true) Term.Bool =
        Term.Bool := by
    simpa [__eo_typeof_bvult, hAtReqEq] using hTypesEq
  have hReqNN :
      __eo_requires (__eo_eq w n) (Term.Boolean true) Term.Bool ≠
        Term.Stuck := by
    rw [hReqEq]
    intro h
    cases h
  exact support_eq_of_eo_eq_true w n
    (support_eo_requires_cond_eq_of_non_stuck hReqNN)

theorem bv_width_eq_of_typeof_bvult_at_bv_right_eq_bool (w n : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hTy :
      __eo_typeof_eq
        (__eo_typeof_bvult (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)))
        (__eo_typeof_eq (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))) =
      Term.Bool) :
    n = w := by
  have hTy' :
      __eo_typeof_eq
        (__eo_typeof_bvult (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))
        (__eo_typeof_eq (Term.Apply (Term.UOp UserOp.BitVec) w)
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n))) =
      Term.Bool := by
    simpa [__eo_typeof_int_to_bv, hNTy, hN] using hTy
  have hAtReqNN :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    intro hReq
    simp [__eo_typeof_eq, __eo_typeof_bvult, hReq] at hTy'
  have hAtGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hAtReqNN
  have hAtReqEq :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simp [__eo_requires, hAtGuard, native_ite, native_teq, native_not]
  by_cases hEq : n = w
  · exact hEq
  · exfalso
    have hNeWN : w ≠ n := by
      intro h
      exact hEq h.symm
    have hLeftStuck :
        __eo_typeof_bvult (Term.Apply (Term.UOp UserOp.BitVec) w)
            (Term.Apply (Term.UOp UserOp.BitVec) n) =
          Term.Stuck := by
      simpa [__eo_typeof_bvult] using
        eo_requires_eq_true_stuck_of_ne w n Term.Bool hNeWN
    have hApplyNe :
        Term.Apply (Term.UOp UserOp.BitVec) w ≠
          Term.Apply (Term.UOp UserOp.BitVec) n := by
      intro hApply
      cases hApply
      exact hNeWN rfl
    have hRightStuck :
        __eo_typeof_eq (Term.Apply (Term.UOp UserOp.BitVec) w)
            (Term.Apply (Term.UOp UserOp.BitVec) n) =
          Term.Stuck := by
      simpa [__eo_typeof_eq] using
        eo_requires_eq_true_stuck_of_ne
          (Term.Apply (Term.UOp UserOp.BitVec) w)
          (Term.Apply (Term.UOp UserOp.BitVec) n)
          Term.Bool hApplyNe
    have hTy'' :
        __eo_typeof_eq
            (__eo_typeof_bvult (Term.Apply (Term.UOp UserOp.BitVec) w)
              (Term.Apply (Term.UOp UserOp.BitVec) n))
            (__eo_typeof_eq (Term.Apply (Term.UOp UserOp.BitVec) w)
              (Term.Apply (Term.UOp UserOp.BitVec) n)) =
          Term.Bool := by
      simpa [__eo_typeof_int_to_bv, hNTy, hN, hAtReqEq] using hTy
    rw [hLeftStuck, hRightStuck] at hTy''
    simp [__eo_typeof_eq] at hTy''

theorem bv_width_eq_of_typeof_bvult_at_bv_left_not_eq_bool (n w : Term)
    (hN : n ≠ Term.Stuck)
    (hNTy : __eo_typeof n = Term.UOp UserOp.Int)
    (hTy :
      __eo_typeof_eq
        (__eo_typeof_bvult
          (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int))
          (Term.Apply (Term.UOp UserOp.BitVec) w))
        (__eo_typeof_not
          (__eo_typeof_eq (Term.Apply (Term.UOp UserOp.BitVec) w)
            (__eo_typeof_int_to_bv (__eo_typeof n) n (Term.UOp UserOp.Int)))) =
      Term.Bool) :
    n = w := by
  have hTy' :
      __eo_typeof_eq
        (__eo_typeof_bvult
          (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
            (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n))
          (Term.Apply (Term.UOp UserOp.BitVec) w))
        (__eo_typeof_not
          (__eo_typeof_eq (Term.Apply (Term.UOp UserOp.BitVec) w)
            (__eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
              (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n)))) =
      Term.Bool := by
    simpa [__eo_typeof_int_to_bv, hNTy, hN] using hTy
  have hAtReqNN :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
        Term.Stuck := by
    intro hReq
    simp [__eo_typeof_eq, __eo_typeof_bvult, __eo_typeof_not, hReq] at hTy'
  have hAtGuard :
      __eo_gt n (Term.Numeral (-1 : native_Int)) = Term.Boolean true :=
    support_eo_requires_cond_eq_of_non_stuck hAtReqNN
  have hAtReqEq :
      __eo_requires (__eo_gt n (Term.Numeral (-1 : native_Int)))
          (Term.Boolean true) (Term.Apply (Term.UOp UserOp.BitVec) n) =
        Term.Apply (Term.UOp UserOp.BitVec) n := by
    simp [__eo_requires, hAtGuard, native_ite, native_teq, native_not]
  by_cases hEq : n = w
  · exact hEq
  · exfalso
    have hLeftStuck :
        __eo_typeof_bvult (Term.Apply (Term.UOp UserOp.BitVec) n)
            (Term.Apply (Term.UOp UserOp.BitVec) w) =
          Term.Stuck := by
      simpa [__eo_typeof_bvult] using
        eo_requires_eq_true_stuck_of_ne n w Term.Bool hEq
    have hTy'' :
        __eo_typeof_eq
            (__eo_typeof_bvult (Term.Apply (Term.UOp UserOp.BitVec) n)
              (Term.Apply (Term.UOp UserOp.BitVec) w))
            (__eo_typeof_not
              (__eo_typeof_eq (Term.Apply (Term.UOp UserOp.BitVec) w)
                (Term.Apply (Term.UOp UserOp.BitVec) n))) =
          Term.Bool := by
      simpa [__eo_typeof_int_to_bv, hNTy, hN, hAtReqEq] using hTy
    rw [hLeftStuck] at hTy''
    simp [__eo_typeof_eq] at hTy''

/-- Stable rewrite for evaluating SMT extraction terms. -/
theorem smtx_eval_extract_term_eq
    (M : SmtModel) (hi lo x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.extract hi lo x) =
      __smtx_model_eval_extract
        (__smtx_model_eval M hi) (__smtx_model_eval M lo)
        (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT arithmetic `to_real` terms. -/
theorem smtx_eval_to_real_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.to_real x) =
      __smtx_model_eval_to_real (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT arithmetic `to_int` terms. -/
theorem smtx_eval_to_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.to_int x) =
      __smtx_model_eval_to_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT arithmetic `is_int` terms. -/
theorem smtx_eval_is_int_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.is_int x) =
      __smtx_model_eval_is_int (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT string/sequence length terms. -/
theorem smtx_eval_str_len_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_len x) =
      __smtx_model_eval_str_len (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT empty sequence terms. -/
theorem smtx_eval_seq_empty_term_eq
    (M : SmtModel) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.seq_empty T) =
      SmtValue.Seq (SmtSeq.empty T) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT sequence singleton terms. -/
theorem smtx_eval_seq_unit_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.seq_unit x) =
      SmtValue.Seq
        (SmtSeq.cons (__smtx_model_eval M x)
          (SmtSeq.empty (__smtx_typeof_value (__smtx_model_eval M x)))) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT string-code terms. -/
theorem smtx_eval_str_to_code_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.str_to_code x) =
      __smtx_model_eval_str_to_code (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT empty set terms. -/
theorem smtx_eval_set_empty_term_eq
    (M : SmtModel) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.set_empty T) =
      SmtValue.Set (SmtMap.default T (SmtValue.Boolean false)) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT set singleton terms. -/
theorem smtx_eval_set_singleton_term_eq
    (M : SmtModel) (x : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_singleton x) =
      __smtx_model_eval_set_singleton (__smtx_model_eval M x) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT set union terms. -/
theorem smtx_eval_set_union_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.set_union x y) =
      __smtx_model_eval_set_union
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT total rational division terms. -/
theorem smtx_eval_qdiv_total_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.qdiv_total x y) =
      __smtx_model_eval_qdiv_total
        (__smtx_model_eval M x) (__smtx_model_eval M y) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT rational division terms. -/
theorem smtx_eval_qdiv_term_eq
    (M : SmtModel) (x y : SmtTerm) :
    __smtx_model_eval M (SmtTerm.qdiv x y) =
      (let yr := __smtx_model_eval_to_real (__smtx_model_eval M y)
       let xr := __smtx_model_eval_to_real (__smtx_model_eval M x)
       __smtx_model_eval_ite
        (__smtx_model_eval_eq yr
          (SmtValue.Rational (native_mk_rational 0 1)))
        (__smtx_model_eval_apply M
          (native_model_lookup M native_qdiv_by_zero_id
            (SmtType.FunType SmtType.Real SmtType.Real))
          xr)
        (__smtx_model_eval_qdiv_total xr yr)) := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT choice witnesses. -/
theorem smtx_eval_choice_term_eq
    (M : SmtModel) (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_model_eval M (SmtTerm.choice s T body) =
      native_eval_tchoice M s T body := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT let-bindings. -/
theorem smtx_eval_bind_term_eq
    (M : SmtModel) (s : native_String) (T : SmtType) (x1 x2 : SmtTerm) :
    __smtx_model_eval M (SmtTerm.bind s T x1 x2) =
      __smtx_model_eval (native_model_push M s T (__smtx_model_eval M x1)) x2 := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for evaluating SMT variables. -/
theorem smtx_eval_var_term_eq
    (M : SmtModel) (s : native_String) (T : SmtType) :
    __smtx_model_eval M (SmtTerm.Var s T) =
      native_model_var_lookup M s T := by
  rw [__smtx_model_eval.eq_def] <;> simp only

/-- Stable rewrite for typing SMT choice witnesses. -/
theorem smtx_typeof_choice_term_eq
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.choice s T body) =
      native_ite (native_Teq (__smtx_typeof body) SmtType.Bool)
        (__smtx_typeof_guard_wf T T) SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT let-bindings. -/
theorem smtx_typeof_bind_term_eq
    (s : native_String) (T : SmtType) (x1 x2 : SmtTerm) :
    __smtx_typeof (SmtTerm.bind s T x1 x2) =
      native_ite (native_Teq (__smtx_typeof x1) T)
        (__smtx_typeof_guard_wf T (__smtx_typeof x2)) SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT existential terms. -/
theorem smtx_typeof_exists_term_eq
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T body) =
      native_ite (native_Teq (__smtx_typeof body) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT universal terms. -/
theorem smtx_typeof_forall_term_eq
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.forall s T body) =
      native_ite (native_Teq (__smtx_typeof body) SmtType.Bool)
        (__smtx_typeof_guard_wf T SmtType.Bool) SmtType.None := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT empty sequence terms. -/
theorem smtx_typeof_seq_empty_term_eq
    (T : SmtType) :
    __smtx_typeof (SmtTerm.seq_empty T) =
      __smtx_typeof_guard_wf (SmtType.Seq T) (SmtType.Seq T) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT sequence singleton terms. -/
theorem smtx_typeof_seq_unit_term_eq
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.seq_unit x) =
      __smtx_typeof_guard_wf
        (SmtType.Seq (__smtx_typeof x)) (SmtType.Seq (__smtx_typeof x)) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT empty set terms. -/
theorem smtx_typeof_set_empty_term_eq
    (T : SmtType) :
    __smtx_typeof (SmtTerm.set_empty T) =
      __smtx_typeof_guard_wf (SmtType.Set T) (SmtType.Set T) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT set singleton terms. -/
theorem smtx_typeof_set_singleton_term_eq
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.set_singleton x) =
      __smtx_typeof_guard_wf
        (SmtType.Set (__smtx_typeof x)) (SmtType.Set (__smtx_typeof x)) := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT variables. -/
theorem smtx_typeof_var_term_eq
    (s : native_String) (T : SmtType) :
    __smtx_typeof (SmtTerm.Var s T) =
      __smtx_typeof_guard_wf T T := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT unsigned bit-vector-to-int terms. -/
theorem smtx_typeof_ubv_to_int_term_eq
    (x : SmtTerm) :
    __smtx_typeof (SmtTerm.ubv_to_int x) =
      __smtx_typeof_bv_op_1_ret (__smtx_typeof x) SmtType.Int := by
  rw [__smtx_typeof.eq_def] <;> simp only

/-- Stable rewrite for typing SMT int-to-bit-vector terms. -/
theorem smtx_typeof_int_to_bv_term_eq
    (w x : SmtTerm) :
    __smtx_typeof (SmtTerm.int_to_bv w x) =
      __smtx_typeof_int_to_bv w (__smtx_typeof x) := by
  rw [__smtx_typeof.eq_def] <;> simp only

@[simp] theorem smtx_typeof_int_to_bv_numerals
    (w k : native_Int)
    (hNonneg : native_zleq 0 w = true) :
    __smtx_typeof
        (SmtTerm.int_to_bv (SmtTerm.Numeral w) (SmtTerm.Numeral k)) =
      SmtType.BitVec (native_int_to_nat w) := by
  rw [smtx_typeof_int_to_bv_term_eq]
  change
    __smtx_typeof_int_to_bv (SmtTerm.Numeral w) SmtType.Int =
      SmtType.BitVec (native_int_to_nat w)
  simp [__smtx_typeof_int_to_bv, native_ite, hNonneg]

/-- Builds the right-associated conjunction of a list of premise terms, using `true` as the empty case. -/
def premiseAndFormulaList : List Term -> Term
  | [] => Term.Boolean true
  | p :: ps => Term.Apply (Term.Apply (Term.UOp UserOp.and) p) (premiseAndFormulaList ps)

/-- Collects the proven terms referenced by a premise index list in a checker state. -/
def premiseTermList (s : CState) : CIndexList -> List Term
  | CIndexList.nil => []
  | CIndexList.cons n premises =>
      __eo_state_proven_nth s n :: premiseTermList s premises

/-- Predicate asserting that every term in a list is interpreted as `true` by a model. -/
def AllInterpretedTrue (M : SmtModel) (ts : List Term) : Prop :=
  ∀ t ∈ ts, eo_interprets M t true

/--
Contextual truth for a derived formula.

The first field is the ordinary checker fact in the current model. The second
field is the freshness/parametricity fact needed by binder-sensitive rules:
the derived formula remains true in any model that only changes variables,
provided the same assumptions and local pushes hold there.
-/
structure ContextualTruth
    (M : SmtModel) (assumes pushes P : Term) : Prop where
  true_here :
    eo_interprets M assumes true ->
    eo_interprets M pushes true ->
    eo_interprets M P true
  true_in_var_model :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      eo_interprets N assumes true ->
      eo_interprets N pushes true ->
      eo_interprets N P true

/--
The premise evidence supplied to a rule.

Most rules only use `true_here`. Binder-sensitive congruence uses
`true_in_var_model`: the checker constructs that field only when the ambient
assumptions and pushes are known to remain true across variable-model changes.
-/
structure RulePremiseEvidence
    (M : SmtModel) (premises : List Term) : Prop where
  true_here :
    AllInterpretedTrue M premises
  true_in_var_model :
    ∀ N, model_total_typed N ->
      model_agrees_on_globals M N ->
      AllInterpretedTrue N premises

instance RulePremiseEvidence.instCoeFun
    {M : SmtModel} {premises : List Term} :
    CoeFun (RulePremiseEvidence M premises)
      (fun _ => ∀ t, t ∈ premises -> eo_interprets M t true) where
  coe h := h.true_here

/-- Predicate asserting that every term in a list has an SMT translation. -/
def AllHaveSmtTranslation (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_smt_translation t

/-- Predicate asserting that every term in a list has translated SMT Boolean type. -/
def AllHaveBoolType (ts : List Term) : Prop :=
  ∀ t ∈ ts, RuleProofs.eo_has_bool_type t

/-- Predicate asserting that every term in a list has EO type `Bool`. -/
def AllTypeofBool (ts : List Term) : Prop :=
  ∀ t ∈ ts, __eo_typeof t = Term.Bool

/-- A term with EO type `Bool` cannot be `Stuck`. -/
theorem term_ne_stuck_of_typeof_bool
    {t : Term}
    (hTy : __eo_typeof t = Term.Bool) :
    t ≠ Term.Stuck := by
  intro hStuck
  rw [hStuck] at hTy
  have hStuckTy : __eo_typeof Term.Stuck ≠ Term.Bool := by
    native_decide
  exact hStuckTy hTy

/-- Derives `premiseAndFormulaList_true` from `all_true`. -/
theorem premiseAndFormulaList_true_of_all_true
    (M : SmtModel) :
  ∀ premises : List Term,
    AllInterpretedTrue M premises ->
    eo_interprets M (premiseAndFormulaList premises) true :=
by
  intro premises hPremises
  induction premises with
  | nil =>
      simpa [premiseAndFormulaList] using RuleProofs.eo_interprets_true M
  | cons p premises ih =>
      apply RuleProofs.eo_interprets_and_intro
      · exact hPremises p (by simp)
      · apply ih
        intro t ht
        exact hPremises t (by simp [ht])

/-- Shows that a conjunction built from Boolean premises still has Boolean type. -/
theorem premiseAndFormulaList_has_bool_type :
  ∀ premises : List Term,
    AllHaveBoolType premises ->
    RuleProofs.eo_has_bool_type (premiseAndFormulaList premises) :=
by
  intro premises hPremises
  induction premises with
  | nil =>
      simpa [premiseAndFormulaList] using RuleProofs.eo_has_bool_type_true
  | cons p premises ih =>
      apply RuleProofs.eo_has_bool_type_and_of_bool_args
      · exact hPremises p (by simp)
      · apply ih
        intro t ht
        exact hPremises t (by simp [ht])

/-- Shows that `premiseAndFormulaList` is recognized as an `and`-list by `__eo_is_list`. -/
theorem premiseAndFormulaList_is_and_list :
  ∀ premises : List Term,
    __eo_is_list (Term.UOp UserOp.and) (premiseAndFormulaList premises) = Term.Boolean true
:=
by
  have hGetNil :
      ∀ premises : List Term,
        __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList premises) ≠ Term.Stuck
  :=
  by
    intro premises
    induction premises with
    | nil =>
        unfold premiseAndFormulaList
        unfold __eo_get_nil_rec
        unfold __eo_requires
        unfold __eo_is_list_nil
        simp [native_ite, native_teq, native_not, SmtEval.native_not]
    | cons p premises ih =>
        unfold premiseAndFormulaList
        unfold __eo_get_nil_rec
        unfold __eo_requires
        simpa [native_ite, native_teq, native_not, SmtEval.native_not] using ih
  intro premises
  have hNotStuck :
      __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList premises) ≠ Term.Stuck :=
    hGetNil premises
  have hPremNotStuck : premiseAndFormulaList premises ≠ Term.Stuck :=
    by
      induction premises with
      | nil =>
          simp [premiseAndFormulaList]
      | cons p premises ih =>
          simp [premiseAndFormulaList]
  unfold __eo_is_list
  unfold __eo_is_ok
  simpa [native_teq, native_not, SmtEval.native_not] using hNotStuck

/-- Establishes an equality relating `mk_premise_list_and` and `premiseAndFormulaList`. -/
theorem mk_premise_list_and_eq_premiseAndFormulaList :
  ∀ (s : CState) (premises : CIndexList),
    __eo_mk_premise_list (Term.UOp UserOp.and) premises s =
      premiseAndFormulaList (premiseTermList s premises)
:=
by
  intro s premises
  induction premises with
  | nil =>
      simp [__eo_mk_premise_list, premiseAndFormulaList, premiseTermList, __eo_nil]
  | cons n premises ih =>
      simp [__eo_mk_premise_list, premiseAndFormulaList, premiseTermList, __eo_cons,
        __eo_requires, native_ite, native_teq, native_not, ih,
        premiseAndFormulaList_is_and_list, SmtEval.native_not]

/--
Standard correctness and translation template for rules that add a proven fact.

Most rules only use `RulePremiseEvidence.true_here`. Binder-sensitive rules use
`RulePremiseEvidence.true_in_var_model` to reason under the fresh variable
models introduced by quantified binders.
-/
structure StepRuleProperties
    (M : SmtModel) (premises : List Term) (P : Term) : Prop where
  facts_of_true :
    RulePremiseEvidence M premises ->
    eo_interprets M P true
  has_smt_translation :
    RuleProofs.eo_has_smt_translation P

/-- Predicate packaging the correctness and translation obligations for rules that also pop assumptions. -/
def StepPopRuleProperties
    (x1 : Term) (premises : List Term) (P : Term) : Prop :=
  ∃ x2,
    x2 ∈ premises ∧
    (forall (M : SmtModel), model_total_typed M ->
      ((eo_interprets M x1 true) -> eo_interprets M x2 true) ->
      eo_interprets M P true) ∧
    RuleProofs.eo_has_smt_translation P
