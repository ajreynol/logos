import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CnfSupport
import Cpc.Proofs.TypePreservation.Helpers

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_requires_self_of_non_stuck
    (T U : Term) :
    T ≠ Term.Stuck ->
    __eo_requires T T U = U := by
  intro hT
  simp [__eo_requires, native_ite, native_not, native_teq, hT]

private theorem prog_dt_cons_eq_condition_of_not_stuck
    (t s B : Term) :
    __eo_prog_dt_cons_eq
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B) ≠
      Term.Stuck ->
    let cond := __eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s)
    cond = B ∧ cond ≠ Term.Stuck := by
  intro hProg
  simp [__eo_prog_dt_cons_eq, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg
  simpa

private theorem prog_dt_cons_eq_eq_input_of_not_stuck
    (t s B : Term) :
    __eo_prog_dt_cons_eq
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B) ≠
      Term.Stuck ->
    __eo_prog_dt_cons_eq
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B) =
      Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) B := by
  intro hProg
  let cond := __eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s)
  have hCond := prog_dt_cons_eq_condition_of_not_stuck t s B hProg
  have hEq : cond = B := hCond.1
  have hCondNe : cond ≠ Term.Stuck := hCond.2
  subst B
  simpa [__eo_prog_dt_cons_eq, cond] using
    eo_requires_self_of_non_stuck
      cond
      (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq t) s)) cond)
      hCondNe

private theorem and_concat_rec_true (z : Term) :
    __eo_list_concat_rec (Term.Boolean true) z = z := by
  cases z <;> simp [__eo_list_concat_rec]

private theorem and_concat_rec_cons (x xs z : Term) :
    __eo_list_concat_rec xs z ≠ Term.Stuck ->
    __eo_list_concat_rec (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) z =
      Term.Apply (Term.Apply (Term.UOp UserOp.and) x) (__eo_list_concat_rec xs z) := by
  intro hTail
  cases z with
  | Stuck =>
      have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
        cases xs <;> simp [__eo_list_concat_rec]
      exact False.elim (hTail hStuck)
  | _ =>
      simp [__eo_list_concat_rec, __eo_mk_apply]

private theorem concat_rec_preserves_andList {c1 c2 : Term} :
    CnfSupport.AndList c1 ->
    CnfSupport.AndList c2 ->
    CnfSupport.AndList (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC2
  induction hC1 generalizing c2 with
  | true =>
      simpa [and_concat_rec_true] using hC2
  | cons x xs hXs ih =>
      have hTail : CnfSupport.AndList (__eo_list_concat_rec xs c2) := ih hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        CnfSupport.andList_ne_stuck hTail
      rw [and_concat_rec_cons x xs c2 hTailNe]
      exact CnfSupport.AndList.cons x (__eo_list_concat_rec xs c2) hTail

private theorem concat_preserves_andList {c1 c2 : Term} :
    CnfSupport.AndList c1 ->
    CnfSupport.AndList c2 ->
    CnfSupport.AndList (__eo_list_concat (Term.UOp UserOp.and) c1 c2) := by
  intro hC1 hC2
  simp [__eo_list_concat, CnfSupport.andList_is_list_true hC1,
    CnfSupport.andList_is_list_true hC2, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]
  exact concat_rec_preserves_andList hC1 hC2

private theorem list_concat_nonstuck_left {a b : Term} :
    __eo_list_concat (Term.UOp UserOp.and) a b ≠ Term.Stuck ->
    a ≠ Term.Stuck := by
  intro hConcat
  intro hA
  subst a
  simp [__eo_list_concat, __eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
    native_ite, native_teq, native_not, SmtEval.native_not] at hConcat

private theorem model_eval_eq_is_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b :=
  bool_value_canonical (typeof_value_model_eval_eq_value v1 v2)

private theorem eo_eq_eq_of_true {c c2 : Term} :
    __eo_eq c c2 = Term.Boolean true ->
    c2 = c := by
  cases c <;> cases c2 <;> simp [__eo_eq, native_teq]

private theorem eval_eo_eq_is_boolean (M : SmtModel) (x y : Term) :
    ∃ b : Bool,
      __smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply Term.eq x) y)) =
        SmtValue.Boolean b := by
  rw [__eo_to_smt.eq_def, __smtx_model_eval.eq_133]
  exact model_eval_eq_is_boolean
    (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y))

private theorem eval_and_bool_components
    (M : SmtModel) (x y : Term) :
    (∃ b : Bool,
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) =
          SmtValue.Boolean b) ->
      (∃ bx : Bool, __smtx_model_eval M (__eo_to_smt x) = SmtValue.Boolean bx) ∧
        (∃ byy : Bool, __smtx_model_eval M (__eo_to_smt y) = SmtValue.Boolean byy) := by
  intro hEval
  rcases hEval with ⟨b, hEval⟩
  rw [__eo_to_smt.eq_def, __smtx_model_eval.eq_8] at hEval
  cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
    cases hy : __smtx_model_eval M (__eo_to_smt y) <;>
    simp [hx, hy, __smtx_model_eval_and, SmtEval.native_and] at hEval
  case Boolean.Boolean bx byy =>
    constructor
    · refine ⟨bx, ?_⟩
      simpa using hx
    · refine ⟨byy, ?_⟩
      simpa using hy

private theorem concat_rec_eval_eq_and
    (M : SmtModel) {c1 c2 : Term} :
    CnfSupport.AndList c1 ->
    CnfSupport.AndList c2 ->
    (∃ b1 : Bool, __smtx_model_eval M (__eo_to_smt c1) = SmtValue.Boolean b1) ->
    (∃ b2 : Bool, __smtx_model_eval M (__eo_to_smt c2) = SmtValue.Boolean b2) ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec c1 c2)) =
      __smtx_model_eval_and (__smtx_model_eval M (__eo_to_smt c1))
        (__smtx_model_eval M (__eo_to_smt c2)) := by
  intro hC1 hC2 hEval1 hEval2
  induction hC1 generalizing c2 with
  | true =>
      rcases hEval2 with ⟨b2, hEval2⟩
      rw [and_concat_rec_true c2]
      rw [hEval2]
      cases b2 <;>
        simp [__eo_to_smt.eq_def, __smtx_model_eval.eq_1,
          __smtx_model_eval_and, SmtEval.native_and]
  | cons x xs hXs ih =>
      have hComps := eval_and_bool_components M x xs hEval1
      have hTail : CnfSupport.AndList (__eo_list_concat_rec xs c2) :=
        concat_rec_preserves_andList hXs hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        CnfSupport.andList_ne_stuck hTail
      rcases hComps with ⟨hEvalX, hEvalXs⟩
      rcases hEvalX with ⟨bx, hEvalX⟩
      rcases hEvalXs with ⟨bxs, hEvalXs⟩
      rcases hEval2 with ⟨b2, hEval2⟩
      have hEvalAndXs :
          __smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs)) =
            SmtValue.Boolean (native_and bx bxs) := by
        rw [__eo_to_smt.eq_def, __smtx_model_eval.eq_8, hEvalX, hEvalXs]
        simp [__smtx_model_eval_and, SmtEval.native_and]
      rw [and_concat_rec_cons x xs c2 hTailNe]
      rw [__eo_to_smt.eq_def, __smtx_model_eval.eq_8]
      rw [ih hC2 ⟨bxs, hEvalXs⟩ ⟨b2, hEval2⟩]
      rw [hEvalX, hEvalXs, hEval2, hEvalAndXs]
      cases bx <;> cases bxs <;> cases b2 <;>
        simp [__smtx_model_eval_and, SmtEval.native_and]

private theorem concat_eval_eq_and
    (M : SmtModel) {c1 c2 : Term} :
    CnfSupport.AndList c1 ->
    CnfSupport.AndList c2 ->
    (∃ b1 : Bool, __smtx_model_eval M (__eo_to_smt c1) = SmtValue.Boolean b1) ->
    (∃ b2 : Bool, __smtx_model_eval M (__eo_to_smt c2) = SmtValue.Boolean b2) ->
    __smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.and) c1 c2)) =
      __smtx_model_eval_and (__smtx_model_eval M (__eo_to_smt c1))
        (__smtx_model_eval M (__eo_to_smt c2)) := by
  intro hC1 hC2 hEval1 hEval2
  simp [__eo_list_concat, CnfSupport.andList_is_list_true hC1,
    CnfSupport.andList_is_list_true hC2, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]
  exact concat_rec_eval_eq_and M hC1 hC2 hEval1 hEval2

private theorem singleton_elim_eval_eq
    (M : SmtModel) {c : Term} :
    CnfSupport.AndList c ->
    (∃ b : Bool, __smtx_model_eval M (__eo_to_smt c) = SmtValue.Boolean b) ->
    __smtx_model_eval M (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.and) c)) =
      __smtx_model_eval M (__eo_to_smt c) := by
  intro hC hEval
  rw [__eo_list_singleton_elim, CnfSupport.andList_is_list_true hC]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hC with
  | true =>
      simp [__eo_list_singleton_elim_2]
  | cons x xs hXs =>
      cases hXs with
      | true =>
          have hComps := eval_and_bool_components M x (Term.Boolean true) hEval
          rcases hComps with ⟨hEvalX, _⟩
          rcases hEvalX with ⟨bx, hEvalX⟩
          have hSingleton :
              __eo_list_singleton_elim_2
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) (Term.Boolean true)) =
              x := by
            simp [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite, native_ite,
              native_teq]
          have hEvalAndTrue :
              __smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) (Term.Boolean true))) =
                __smtx_model_eval M (__eo_to_smt x) := by
            rw [__eo_to_smt.eq_def, __smtx_model_eval.eq_8, hEvalX]
            simp [__eo_to_smt.eq_def, __smtx_model_eval.eq_1,
              __smtx_model_eval_and, SmtEval.native_and]
          rw [hSingleton]
          exact hEvalAndTrue.symm
      | cons y ys hYs =>
          simp [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite, native_ite,
            native_teq]

private theorem mk_dt_cons_eq_base_andList
    (c c2 : Term) :
    __eo_requires (__eo_eq c c2) (Term.Boolean true)
      (__eo_requires
        (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
            (__eo_is_ok (__eo_dt_selectors c))))
        (Term.Boolean true) (Term.Boolean true)) ≠ Term.Stuck ->
    CnfSupport.AndList
      (__eo_requires (__eo_eq c c2) (Term.Boolean true)
        (__eo_requires
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
            (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
              (__eo_is_ok (__eo_dt_selectors c))))
          (Term.Boolean true) (Term.Boolean true))) := by
  intro hReq
  have hReq' := hReq
  simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
    SmtEval.native_not] at hReq'
  have hBaseTrue :
      __eo_requires (__eo_eq c c2) (Term.Boolean true)
        (__eo_requires
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
            (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
              (__eo_is_ok (__eo_dt_selectors c))))
          (Term.Boolean true) (Term.Boolean true)) = Term.Boolean true := by
    rcases hReq' with ⟨hEq, _hEqNe, hCons, hConsNe⟩
    simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
      SmtEval.native_not, hEq, hCons, hConsNe]
  rw [hBaseTrue]
  exact CnfSupport.AndList.true

private theorem mk_dt_cons_eq_base_eval_eq
    (M : SmtModel) (c c2 : Term) :
    __eo_requires (__eo_eq c c2) (Term.Boolean true)
      (__eo_requires
        (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
            (__eo_is_ok (__eo_dt_selectors c))))
        (Term.Boolean true) (Term.Boolean true)) ≠ Term.Stuck ->
    __smtx_model_eval M
        (__eo_to_smt
          (__eo_requires (__eo_eq c c2) (Term.Boolean true)
            (__eo_requires
              (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
                (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
                  (__eo_is_ok (__eo_dt_selectors c))))
              (Term.Boolean true) (Term.Boolean true)))) =
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt c))
        (__smtx_model_eval M (__eo_to_smt c2)) := by
  intro hReq
  have hReq' := hReq
  simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
    SmtEval.native_not] at hReq'
  rcases hReq' with ⟨hEq, _hEqNe, hCons, hConsNe⟩
  have hEq' : c2 = c := eo_eq_eq_of_true hEq
  have hBaseTrue :
      __eo_requires (__eo_eq c c2) (Term.Boolean true)
        (__eo_requires
          (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple)) (Term.Boolean true)
            (__eo_ite (__eo_is_eq c (Term.UOp UserOp.tuple_unit)) (Term.Boolean true)
              (__eo_is_ok (__eo_dt_selectors c))))
          (Term.Boolean true) (Term.Boolean true)) = Term.Boolean true := by
    simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
      SmtEval.native_not, hEq, hCons, hConsNe]
  subst c2
  have hRefl :
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt c))
        (__smtx_model_eval M (__eo_to_smt c)) = SmtValue.Boolean true :=
    RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt c))
  rw [hBaseTrue]
  rw [__eo_to_smt.eq_def]
  rw [__smtx_model_eval.eq_1, hRefl]

private theorem mk_apply_and_preserves_andList
    (x xs : Term) :
    CnfSupport.AndList xs ->
    CnfSupport.AndList (__eo_mk_apply (Term.Apply (Term.UOp UserOp.and) x) xs) := by
  intro hXs
  cases hXs with
  | true =>
      simp [__eo_mk_apply]
      exact CnfSupport.AndList.cons x (Term.Boolean true) CnfSupport.AndList.true
  | cons y ys hYs =>
      simp [__eo_mk_apply]
      exact CnfSupport.AndList.cons x
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) ys)
        (CnfSupport.AndList.cons y ys hYs)

private theorem mk_dt_cons_eq_andList_of_not_stuck
    (t s : Term) :
    __mk_dt_cons_eq t s ≠ Term.Stuck ->
    CnfSupport.AndList (__mk_dt_cons_eq t s) := by
  intro h
  fun_cases __mk_dt_cons_eq t s
  · simp [__mk_dt_cons_eq] at h
  · simp [__mk_dt_cons_eq] at h
  · rename_i a as b bs
    subst_vars
    have hTail : __mk_dt_cons_eq as bs ≠ Term.Stuck := by
      intro hTailStuck
      apply h
      exact by simp [__mk_dt_cons_eq, __eo_mk_apply, hTailStuck]
    exact mk_apply_and_preserves_andList
      (Term.Apply (Term.Apply Term.eq a) b)
      (__mk_dt_cons_eq as bs)
      (mk_dt_cons_eq_andList_of_not_stuck as bs hTail)
  · rename_i f a g b _hNotTuple
    subst_vars
    let right :=
      Term.Apply (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply Term.eq a) b))
        (Term.Boolean true)
    change CnfSupport.AndList
      (__eo_list_concat (Term.UOp UserOp.and) (__mk_dt_cons_eq f g) right)
    have hConcat :
        __eo_list_concat (Term.UOp UserOp.and) (__mk_dt_cons_eq f g) right ≠
          Term.Stuck := by
      simpa [__mk_dt_cons_eq] using h
    have hLeft : __mk_dt_cons_eq f g ≠ Term.Stuck :=
      list_concat_nonstuck_left hConcat
    have hLeftList : CnfSupport.AndList (__mk_dt_cons_eq f g) :=
      mk_dt_cons_eq_andList_of_not_stuck f g hLeft
    have hRightList : CnfSupport.AndList right :=
      CnfSupport.AndList.cons
        (Term.Apply (Term.Apply Term.eq a) b)
        (Term.Boolean true)
        CnfSupport.AndList.true
    exact concat_preserves_andList hLeftList hRightList
  · subst_vars
    exact mk_dt_cons_eq_base_andList _ _ (by simpa [__mk_dt_cons_eq] using h)
termination_by sizeOf t + sizeOf s
decreasing_by
  all_goals subst_vars; simp_wf

private theorem mk_dt_cons_eq_eval_eq
    (M : SmtModel) (t s : Term) :
    __mk_dt_cons_eq t s ≠ Term.Stuck ->
    __smtx_model_eval M (__eo_to_smt (__mk_dt_cons_eq t s)) =
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t))
        (__smtx_model_eval M (__eo_to_smt s)) := by
  intro h
  fun_cases __mk_dt_cons_eq t s
  · simp [__mk_dt_cons_eq] at h
  · simp [__mk_dt_cons_eq] at h
  · rename_i a as b bs
    subst_vars
    have hTail : __mk_dt_cons_eq as bs ≠ Term.Stuck := by
      intro hTailStuck
      apply h
      exact by simp [__mk_dt_cons_eq, __eo_mk_apply, hTailStuck]
    have hTailEval := mk_dt_cons_eq_eval_eq M as bs hTail
    rcases eval_eo_eq_is_boolean M a b with ⟨b1, hEqABEval⟩
    have hMkApply :
        __eo_mk_apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
          (__mk_dt_cons_eq as bs) =
        Term.Apply (Term.Apply (Term.UOp UserOp.and)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b))
          (__mk_dt_cons_eq as bs) := by
      cases hTailEq : __mk_dt_cons_eq as bs
      · exact False.elim (hTail hTailEq)
      all_goals simp [__eo_mk_apply]
    rw [hMkApply]
    rw [__eo_to_smt.eq_def, __smtx_model_eval.eq_8, hEqABEval, hTailEval]
    simp [__smtx_model_eval_and, __smtx_model_eval_eq, native_veq,
      SmtEval.native_and]
  · rename_i f a g b _hNotTuple
    subst_vars
    let left := __mk_dt_cons_eq f g
    let right :=
      Term.Apply (Term.Apply (Term.UOp UserOp.and)
        (Term.Apply (Term.Apply Term.eq a) b))
        (Term.Boolean true)
    change __smtx_model_eval M
        (__eo_to_smt (__eo_list_concat (Term.UOp UserOp.and) left right)) =
      __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt (Term.Apply f a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply g b)))
    have hConcat :
        __eo_list_concat (Term.UOp UserOp.and) left right ≠ Term.Stuck := by
      simpa [left, right, __mk_dt_cons_eq] using h
    have hLeft : left ≠ Term.Stuck :=
      list_concat_nonstuck_left hConcat
    have hLeftList : CnfSupport.AndList left :=
      mk_dt_cons_eq_andList_of_not_stuck f g hLeft
    have hRightList : CnfSupport.AndList right :=
      CnfSupport.AndList.cons
        (Term.Apply (Term.Apply Term.eq a) b)
        (Term.Boolean true)
        CnfSupport.AndList.true
    have hLeftEval := mk_dt_cons_eq_eval_eq M f g hLeft
    have hLeftEvalBool :
        ∃ bl : Bool, __smtx_model_eval M (__eo_to_smt left) = SmtValue.Boolean bl := by
      rw [hLeftEval]
      exact model_eval_eq_is_boolean
        (__smtx_model_eval M (__eo_to_smt f))
        (__smtx_model_eval M (__eo_to_smt g))
    rcases eval_eo_eq_is_boolean M a b with ⟨br, hEqABEval⟩
    have hRightEvalBool :
        ∃ br' : Bool, __smtx_model_eval M (__eo_to_smt right) = SmtValue.Boolean br' := by
      refine ⟨br, ?_⟩
      rw [__eo_to_smt.eq_def, __smtx_model_eval.eq_8, hEqABEval]
      rw [__eo_to_smt.eq_def, __smtx_model_eval.eq_1]
      simp [__smtx_model_eval_and, SmtEval.native_and]
    rw [concat_eval_eq_and M hLeftList hRightList hLeftEvalBool hRightEvalBool]
    rw [hLeftEval, __eo_to_smt.eq_def, __smtx_model_eval.eq_8, hEqABEval]
    simp [__smtx_model_eval_and, __smtx_model_eval_eq, native_veq,
      SmtEval.native_and]
  · subst_vars
    exact mk_dt_cons_eq_base_eval_eq M _ _ (by simpa [__mk_dt_cons_eq] using h)
termination_by sizeOf t + sizeOf s
decreasing_by
  all_goals subst_vars; simp_wf

private theorem dt_cons_eq_condition_rel
    (M : SmtModel) (t s : Term) :
    __eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s) ≠ Term.Stuck ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (Term.Apply (Term.Apply Term.eq t) s)))
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s)))) := by
  intro hCond
  have hMk : __mk_dt_cons_eq t s ≠ Term.Stuck := by
    cases hMk' : __mk_dt_cons_eq t s <;>
      simp [__eo_list_singleton_elim, hMk', __eo_requires, native_ite, native_teq,
        native_not, SmtEval.native_not] at hCond ⊢
    case Stuck =>
      simp [__eo_list_singleton_elim, __eo_is_list, __eo_is_ok, __eo_get_nil_rec,
        __eo_requires, hMk', native_ite, native_teq, native_not, SmtEval.native_not] at hCond
  have hList : CnfSupport.AndList (__mk_dt_cons_eq t s) :=
    mk_dt_cons_eq_andList_of_not_stuck t s hMk
  have hMkEval := mk_dt_cons_eq_eval_eq M t s hMk
  have hMkEvalBool :
      ∃ b : Bool,
        __smtx_model_eval M (__eo_to_smt (__mk_dt_cons_eq t s)) = SmtValue.Boolean b := by
    rw [hMkEval]
    exact model_eval_eq_is_boolean
      (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M (__eo_to_smt s))
  have hCondEval :
      __smtx_model_eval M
          (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.and) (__mk_dt_cons_eq t s))) =
        __smtx_model_eval M (__eo_to_smt (__mk_dt_cons_eq t s)) :=
    singleton_elim_eval_eq M hList hMkEvalBool
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  rw [hCondEval, hMkEval, __eo_to_smt.eq_def, __smtx_model_eval.eq_133]
  exact RuleProofs.smt_value_rel_refl
    (__smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M (__eo_to_smt s)))

theorem cmd_step_dt_cons_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_cons_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_cons_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_cons_eq args premises) := by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_cons_eq args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hATransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              have hProgRule : __eo_prog_dt_cons_eq a1 ≠ Term.Stuck := by
                simpa using hProg
              cases a1 with
              | Apply f B =>
                  cases f with
                  | Apply g lhs =>
                      cases g with
                      | UOp op =>
                          cases op with
                          | eq =>
                              cases lhs with
                              | Apply f' s' =>
                                  cases f' with
                                  | Apply g' t' =>
                                      cases g' with
                                      | UOp op' =>
                                          cases op' with
                                          | eq =>
                                              let cond :=
                                                __eo_list_singleton_elim
                                                  (Term.UOp UserOp.and) (__mk_dt_cons_eq t' s')
                                              have hCondData :=
                                                prog_dt_cons_eq_condition_of_not_stuck t' s' B hProgRule
                                              have hCondEq : cond = B := hCondData.1
                                              have hCondNe : cond ≠ Term.Stuck := hCondData.2
                                              have hProgEq :
                                                  __eo_prog_dt_cons_eq
                                                      (Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply (Term.Apply Term.eq t') s'))
                                                        B) =
                                                    Term.Apply
                                                      (Term.Apply Term.eq
                                                        (Term.Apply (Term.Apply Term.eq t') s'))
                                                      B :=
                                                prog_dt_cons_eq_eq_input_of_not_stuck t' s' B hProgRule
                                              have hAType :
                                                  __eo_typeof
                                                      (Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply (Term.Apply Term.eq t') s'))
                                                        B) = Term.Bool := by
                                                have hResultTy' := hResultTy
                                                change __eo_typeof
                                                    (__eo_prog_dt_cons_eq
                                                      (Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply (Term.Apply Term.eq t') s'))
                                                        B)) = Term.Bool at hResultTy'
                                                rw [hProgEq] at hResultTy'
                                                exact hResultTy'
                                              have hABool :
                                                  RuleProofs.eo_has_bool_type
                                                    (Term.Apply
                                                      (Term.Apply Term.eq
                                                        (Term.Apply (Term.Apply Term.eq t') s'))
                                                      B) :=
                                                RuleProofs.eo_typeof_bool_implies_has_bool_type
                                                  _ hATrans hAType
                                              refine ⟨?_, ?_⟩
                                              · intro _hTrue
                                                change eo_interprets M
                                                  (__eo_prog_dt_cons_eq
                                                    (Term.Apply
                                                      (Term.Apply Term.eq
                                                        (Term.Apply (Term.Apply Term.eq t') s'))
                                                      B)) true
                                                rw [hProgEq]
                                                have hCondRel :
                                                    RuleProofs.smt_value_rel
                                                      (__smtx_model_eval M
                                                        (__eo_to_smt
                                                          (Term.Apply
                                                            (Term.Apply Term.eq t') s')))
                                                      (__smtx_model_eval M (__eo_to_smt cond)) :=
                                                  dt_cons_eq_condition_rel M t' s' hCondNe
                                                subst B
                                                simpa using
                                                  RuleProofs.eo_interprets_eq_of_rel M
                                                    (Term.Apply (Term.Apply Term.eq t') s')
                                                    cond
                                                    hABool
                                                    hCondRel
                                              · change RuleProofs.eo_has_smt_translation
                                                  (__eo_prog_dt_cons_eq
                                                    (Term.Apply
                                                      (Term.Apply Term.eq
                                                        (Term.Apply (Term.Apply Term.eq t') s'))
                                                      B))
                                                rw [hProgEq]
                                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                  _ hABool
                                          | _ =>
                                              simp [__eo_prog_dt_cons_eq] at hProgRule
                                      | _ =>
                                          simp [__eo_prog_dt_cons_eq] at hProgRule
                                  | _ =>
                                      simp [__eo_prog_dt_cons_eq] at hProgRule
                              | _ =>
                                  simp [__eo_prog_dt_cons_eq] at hProgRule
                          | _ =>
                              simp [__eo_prog_dt_cons_eq] at hProgRule
                      | _ =>
                          simp [__eo_prog_dt_cons_eq] at hProgRule
                  | _ =>
                      simp [__eo_prog_dt_cons_eq] at hProgRule
              | _ =>
                  simp [__eo_prog_dt_cons_eq] at hProgRule
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
