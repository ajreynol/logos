import Cpc.Proofs.Translation.Full

open Eo
open SmtEval
open Smtm
open TranslationProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

def native_eo_to_smt_uop_indices_safe : Term -> native_Bool
  | Term.Apply f x =>
    native_and (native_eo_to_smt_uop_indices_safe f) (native_eo_to_smt_uop_indices_safe x)
  | Term.UOp1 _ x =>
    native_and (native_eo_to_smt_closed x) (native_eo_to_smt_uop_indices_safe x)
  | Term.UOp2 _ x y =>
    native_and
      (native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y))
      (native_and (native_eo_to_smt_uop_indices_safe x) (native_eo_to_smt_uop_indices_safe y))
  | Term.UOp3 _ x y z =>
    native_and
      (native_and (native_and (native_eo_to_smt_closed x) (native_eo_to_smt_closed y)) (native_eo_to_smt_closed z))
      (native_and
        (native_and (native_eo_to_smt_uop_indices_safe x) (native_eo_to_smt_uop_indices_safe y))
        (native_eo_to_smt_uop_indices_safe z))
  | _ => true

def NativeEoToSmtUOpIndicesSafe (x : Term) : Prop :=
  native_eo_to_smt_uop_indices_safe x = true

private theorem native_and_eq_true_intro {a b : native_Bool} :
    a = true ->
    b = true ->
    native_and a b = true := by
  intro ha hb
  cases a <;> cases b <;> simp [native_and] at ha hb ⊢

private theorem native_and_left_eq_true {a b : native_Bool} :
    native_and a b = true -> a = true := by
  intro h
  cases a <;> cases b <;> simp [native_and] at h ⊢

private theorem native_and_right_eq_true {a b : native_Bool} :
    native_and a b = true -> b = true := by
  intro h
  cases a <;> cases b <;> simp [native_and] at h ⊢

private theorem native_eo_to_smt_uop_indices_safe_apply_intro
    {f x : Term}
    (hf : native_eo_to_smt_uop_indices_safe f = true)
    (hx : native_eo_to_smt_uop_indices_safe x = true) :
    native_eo_to_smt_uop_indices_safe (Term.Apply f x) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hf, hx, native_and]

private theorem native_eo_to_smt_uop_indices_safe_uop1_intro
    {op : UserOp1} {x : Term}
    (hc : native_eo_to_smt_closed x = true)
    (hs : native_eo_to_smt_uop_indices_safe x = true) :
    native_eo_to_smt_uop_indices_safe (Term.UOp1 op x) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hc, hs, native_and]

private theorem native_eo_to_smt_uop_indices_safe_uop2_intro
    {op : UserOp2} {x y : Term}
    (hxc : native_eo_to_smt_closed x = true)
    (hyc : native_eo_to_smt_closed y = true)
    (hxs : native_eo_to_smt_uop_indices_safe x = true)
    (hys : native_eo_to_smt_uop_indices_safe y = true) :
    native_eo_to_smt_uop_indices_safe (Term.UOp2 op x y) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hxc, hyc, hxs, hys,
    native_and]

private theorem native_eo_to_smt_uop_indices_safe_uop3_intro
    {op : UserOp3} {x y z : Term}
    (hxc : native_eo_to_smt_closed x = true)
    (hyc : native_eo_to_smt_closed y = true)
    (hzc : native_eo_to_smt_closed z = true)
    (hxs : native_eo_to_smt_uop_indices_safe x = true)
    (hys : native_eo_to_smt_uop_indices_safe y = true)
    (hzs : native_eo_to_smt_uop_indices_safe z = true) :
    native_eo_to_smt_uop_indices_safe (Term.UOp3 op x y z) = true := by
  simp [native_eo_to_smt_uop_indices_safe, hxc, hyc, hzc, hxs, hys, hzs,
    native_and]

private theorem native_eo_to_smt_closed_of_guard_type_non_none
    {x : Term} {body : SmtTerm}
    (h :
      __smtx_typeof (native_eo_to_smt_guard_closed x body) ≠
        SmtType.None) :
    native_eo_to_smt_closed x = true := by
  cases hx : native_eo_to_smt_closed x
  · exfalso
    apply h
    simp [native_eo_to_smt_guard_closed, native_ite, hx,
      TranslationProofs.smtx_typeof_none]
  · rfl

private theorem guard_body_type_non_none_of_guard_type_non_none
    {x : Term} {body : SmtTerm}
    (h :
      __smtx_typeof (native_eo_to_smt_guard_closed x body) ≠
        SmtType.None) :
    __smtx_typeof body ≠ SmtType.None := by
  intro hBody
  cases hx : native_eo_to_smt_closed x
  · exact h (by
      simp [native_eo_to_smt_guard_closed, native_ite, hx,
        TranslationProofs.smtx_typeof_none])
  · exact h (by
      simpa [native_eo_to_smt_guard_closed, native_ite, hx] using hBody)

private theorem native_eo_to_smt_closed_of_nat_valid
    {x : Term}
    (h : __eo_to_smt_nat_is_valid x = true) :
    native_eo_to_smt_closed x = true := by
  cases x <;> simp [__eo_to_smt_nat_is_valid, native_eo_to_smt_closed,
    native_eo_to_smt_closed_rec] at h ⊢

private theorem native_eo_to_smt_uop_indices_safe_of_nat_valid
    {x : Term}
    (h : __eo_to_smt_nat_is_valid x = true) :
    native_eo_to_smt_uop_indices_safe x = true := by
  cases x <;> simp [__eo_to_smt_nat_is_valid,
    native_eo_to_smt_uop_indices_safe] at h ⊢

private theorem native_eo_to_smt_closed_rec_nil_of_closed
    {x : Term}
    (h : native_eo_to_smt_closed x = true) :
    native_eo_to_smt_closed_rec x [] = true := by
  simpa [native_eo_to_smt_closed] using h

private theorem native_eo_to_smt_closed_of_smt_numeral
    {x : Term} {n : native_Int}
    (h : __eo_to_smt x = SmtTerm.Numeral n) :
    native_eo_to_smt_closed x = true := by
  have hx : x = Term.Numeral n := eo_to_smt_eq_numeral x n h
  subst x
  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec]

private theorem native_eo_to_smt_uop_indices_safe_of_smt_numeral
    {x : Term} {n : native_Int}
    (h : __eo_to_smt x = SmtTerm.Numeral n) :
    native_eo_to_smt_uop_indices_safe x = true := by
  have hx : x = Term.Numeral n := eo_to_smt_eq_numeral x n h
  subst x
  simp [native_eo_to_smt_uop_indices_safe]

private theorem smt_typeof_non_none_of_eq_non_none
    {x : Term} {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hNone
  exact hT (h.symm.trans hNone)

private theorem smt_term_typeof_non_none_of_eq_non_none
    {x : SmtTerm} {T : SmtType}
    (h : __smtx_typeof x = T)
    (hT : T ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  intro hNone
  exact hT (h.symm.trans hNone)

private theorem smtx_typeof_at_purify_arg_non_none
    {x : SmtTerm}
    (h : __smtx_typeof (SmtTerm._at_purify x) ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  intro hx
  exact h (by simpa [__smtx_typeof] using hx)

private theorem smtx_typeof_guard_body_non_none_of_non_none
    {T U : SmtType}
    (h : __smtx_typeof_guard T U ≠ SmtType.None) :
    U ≠ SmtType.None := by
  intro hU
  cases T <;> simp [__smtx_typeof_guard, native_ite, hU] at h

private theorem smtx_typeof_guard_wf_body_non_none_of_non_none
    {T U : SmtType}
    (h : __smtx_typeof_guard_wf T U ≠ SmtType.None) :
  U ≠ SmtType.None := by
  intro hU
  have hEq := Smtm.smtx_typeof_guard_wf_of_non_none T U h
  exact h (by simpa [hEq] using hU)

private theorem smtx_apply_arg_non_none_of_any_non_none
    {f x : SmtTerm}
    (h : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  cases f
  case DtSel s d i j =>
    let R := __smtx_ret_typeof_sel s d i j
    have hBody :
        __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R)
            (__smtx_typeof x) ≠ SmtType.None :=
      smtx_typeof_guard_wf_body_non_none_of_non_none (T := R) (by
        simpa [__smtx_typeof, R] using h)
    rcases typeof_apply_non_none_cases hBody with
      ⟨A, _B, _hHead, hArg, hA, _hB⟩
    rw [hArg]
    exact hA
  case DtTester s d i =>
    let D := SmtType.Datatype s d
    let C := __smtx_typeof_dt_cons_rec D (__smtx_dt_substitute s d d) i
    have hBody :
        __smtx_typeof_apply (SmtType.FunType D SmtType.Bool)
            (__smtx_typeof x) ≠ SmtType.None :=
      smtx_typeof_guard_body_non_none_of_non_none (T := C) (by
        simpa [__smtx_typeof, D, C] using h)
    rcases typeof_apply_non_none_cases hBody with
      ⟨A, _B, _hHead, hArg, hA, _hB⟩
    rw [hArg]
    exact hA
  all_goals
    exact smtx_apply_arg_non_none_of_non_special_non_none
      _ _ (by intro s d i j hSel; cases hSel)
      (by intro s d i hTester; cases hTester) h

private theorem smt_select_args_non_none
    {t1 t2 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.select t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases select_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨A, B, h1, h2⟩
  have ht1 : __smtx_typeof t1 ≠ SmtType.None :=
    smt_term_typeof_non_none_of_eq_non_none h1 (by simp)
  have hMapTy :=
    term_type_has_no_none_components_of_non_none t1 (by
      unfold term_has_non_none_type
      exact ht1)
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  have hA : A ≠ SmtType.None :=
    type_has_no_none_components_non_none hMapTy'.1
  exact ⟨ht1, smt_term_typeof_non_none_of_eq_non_none h2 hA⟩

private theorem smt_bv_concat_args_non_none
    {t1 t2 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.concat t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases bv_concat_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨w1, w2, h1, h2⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1
        (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2
        (by simp)⟩

private theorem smt_bv_binop_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_bv_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases bv_binop_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h) with
    ⟨w, h1, h2⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1
        (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2
        (by simp)⟩

private theorem smt_bv_binop_ret_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases bv_binop_ret_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h) with
    ⟨w, h1, h2⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1
        (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2
        (by simp)⟩

private theorem smt_arith_binop_ret_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases arith_binop_ret_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h) with hArgs | hArgs
  · exact
      ⟨smt_term_typeof_non_none_of_eq_non_none hArgs.1 (by simp),
        smt_term_typeof_non_none_of_eq_non_none hArgs.2 (by simp)⟩
  · exact
      ⟨smt_term_typeof_non_none_of_eq_non_none hArgs.1 (by simp),
        smt_term_typeof_non_none_of_eq_non_none hArgs.2 (by simp)⟩

private theorem smt_seq_binop_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_seq_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases seq_binop_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, h1, h2⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp)⟩

private theorem smt_seq_binop_ret_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_seq_op_2_ret
          (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases seq_binop_args_of_non_none_ret hTy (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, h1, h2⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp)⟩

private theorem smt_seq_char_binop_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) (SmtType.Seq SmtType.Char))
            ret SmtType.None)
          SmtType.None)
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  have hArgs :=
    seq_char_binop_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h)
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none hArgs.1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none hArgs.2 (by simp)⟩

private theorem smt_reglan_binop_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) SmtType.RegLan)
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  have hArgs :=
    reglan_binop_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h)
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none hArgs.1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none hArgs.2 (by simp)⟩

private theorem smt_seq_char_reglan_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
            ret SmtType.None)
          SmtType.None)
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  have hArgs :=
    seq_char_reglan_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h)
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none hArgs.1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none hArgs.2 (by simp)⟩

private theorem smt_str_at_args_non_none
    {t1 t2 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.str_at t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases str_at_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, h1, h2⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp)⟩

private theorem smt_seq_nth_args_non_none
    {t1 t2 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.seq_nth t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases seq_nth_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, h1, h2⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp)⟩

private theorem smt_set_binop_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_sets_op_2 (__smtx_typeof t1) (__smtx_typeof t2))
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases set_binop_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h) with
    ⟨A, h1, h2⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp)⟩

private theorem smt_set_binop_ret_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    {ret : SmtType}
    (hTy :
      __smtx_typeof (op t1 t2) =
        __smtx_typeof_sets_op_2_ret
          (__smtx_typeof t1) (__smtx_typeof t2) ret)
    (h : __smtx_typeof (op t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases set_binop_ret_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h) with
    ⟨A, h1, h2⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp)⟩

private theorem smt_set_member_args_non_none
    {t1 t2 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.set_member t1 t2) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases set_member_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨A, h1, h2⟩
  have ht2 : __smtx_typeof t2 ≠ SmtType.None :=
    smt_term_typeof_non_none_of_eq_non_none h2 (by simp)
  have hSetTy :=
    term_type_has_no_none_components_of_non_none t2 (by
      unfold term_has_non_none_type
      exact ht2)
  have hSetTy' : type_has_no_none_components (SmtType.Set A) := by
    simpa [h2] using hSetTy
  have hA : A ≠ SmtType.None :=
    type_has_no_none_components_non_none hSetTy'
  exact ⟨smt_term_typeof_non_none_of_eq_non_none h1 hA, ht2⟩

private theorem smt_bv_cmp_to_bv1_args_non_none
    {cmp : SmtTerm -> SmtTerm -> SmtTerm} {t1 t2 : SmtTerm}
    (hTy :
      __smtx_typeof (cmp t1 t2) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof t1) (__smtx_typeof t2) SmtType.Bool)
    (h :
      __smtx_typeof
          (SmtTerm.ite (cmp t1 t2) (SmtTerm.Binary 1 1)
            (SmtTerm.Binary 1 0)) ≠
        SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases ite_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, hCond, _hThen, _hElse, _hT⟩
  have hCmp : __smtx_typeof (cmp t1 t2) ≠ SmtType.None :=
    smt_term_typeof_non_none_of_eq_non_none hCond (by simp)
  exact smt_bv_binop_ret_args_non_none hTy hCmp

private theorem smt_from_bools_args_non_none
    {t1 t2 : SmtTerm}
    (h :
      __smtx_typeof
          (SmtTerm.concat
            (SmtTerm.ite t1 (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
            t2) ≠
        SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None := by
  rcases smt_bv_concat_args_non_none h with ⟨hIte, ht2⟩
  rcases ite_args_of_non_none (by
      unfold term_has_non_none_type
      exact hIte) with
    ⟨T, hCond, _hThen, _hElse, _hT⟩
  exact ⟨smt_term_typeof_non_none_of_eq_non_none hCond (by simp), ht2⟩

private theorem smt_ite_args_non_none
    {c t1 t2 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.ite c t1 t2) ≠ SmtType.None) :
    __smtx_typeof c ≠ SmtType.None ∧
      __smtx_typeof t1 ≠ SmtType.None ∧
        __smtx_typeof t2 ≠ SmtType.None := by
  rcases ite_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, hc, h1, h2, hT⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none hc (by simp),
      smt_term_typeof_non_none_of_eq_non_none h1 hT,
      smt_term_typeof_non_none_of_eq_non_none h2 hT⟩

private theorem smt_store_args_non_none
    {t1 t2 t3 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.store t1 t2 t3) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None ∧
        __smtx_typeof t3 ≠ SmtType.None := by
  rcases store_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨A, B, h1, h2, h3⟩
  have ht1 : __smtx_typeof t1 ≠ SmtType.None :=
    smt_term_typeof_non_none_of_eq_non_none h1 (by simp)
  have hMapTy :=
    term_type_has_no_none_components_of_non_none t1 (by
      unfold term_has_non_none_type
      exact ht1)
  have hMapTy' : type_has_no_none_components (SmtType.Map A B) := by
    simpa [h1] using hMapTy
  have hA : A ≠ SmtType.None :=
    type_has_no_none_components_non_none hMapTy'.1
  have hB : B ≠ SmtType.None :=
    type_has_no_none_components_non_none hMapTy'.2
  exact
    ⟨ht1,
      smt_term_typeof_non_none_of_eq_non_none h2 hA,
      smt_term_typeof_non_none_of_eq_non_none h3 hB⟩

private theorem smt_str_substr_args_non_none
    {t1 t2 t3 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.str_substr t1 t2 t3) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None ∧
        __smtx_typeof t3 ≠ SmtType.None := by
  rcases str_substr_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, h1, h2, h3⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h3 (by simp)⟩

private theorem smt_str_indexof_args_non_none
    {t1 t2 t3 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.str_indexof t1 t2 t3) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None ∧
        __smtx_typeof t3 ≠ SmtType.None := by
  rcases str_indexof_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, h1, h2, h3⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h3 (by simp)⟩

private theorem smt_str_update_args_non_none
    {t1 t2 t3 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.str_update t1 t2 t3) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None ∧
        __smtx_typeof t3 ≠ SmtType.None := by
  rcases str_update_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, h1, h2, h3⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h3 (by simp)⟩

private theorem smt_seq_triop_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2 t3) =
        __smtx_typeof_seq_op_3
          (__smtx_typeof t1) (__smtx_typeof t2) (__smtx_typeof t3))
    (h : __smtx_typeof (op t1 t2 t3) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None ∧
        __smtx_typeof t3 ≠ SmtType.None := by
  rcases seq_triop_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h) with
    ⟨T, h1, h2, h3⟩
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none h1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h2 (by simp),
      smt_term_typeof_non_none_of_eq_non_none h3 (by simp)⟩

private theorem smt_str_replace_re_args_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {t1 t2 t3 : SmtTerm}
    (hTy :
      __smtx_typeof (op t1 t2 t3) =
        native_ite (native_Teq (__smtx_typeof t1) (SmtType.Seq SmtType.Char))
          (native_ite (native_Teq (__smtx_typeof t2) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof t3) (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (h : __smtx_typeof (op t1 t2 t3) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None ∧
        __smtx_typeof t3 ≠ SmtType.None := by
  have hArgs :=
    str_replace_re_args_of_non_none hTy (by
      unfold term_has_non_none_type
      exact h)
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none hArgs.1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none hArgs.2.1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none hArgs.2.2 (by simp)⟩

private theorem smt_str_indexof_re_args_non_none
    {t1 t2 t3 : SmtTerm}
    (h : __smtx_typeof (SmtTerm.str_indexof_re t1 t2 t3) ≠ SmtType.None) :
    __smtx_typeof t1 ≠ SmtType.None ∧
      __smtx_typeof t2 ≠ SmtType.None ∧
        __smtx_typeof t3 ≠ SmtType.None := by
  have hArgs :=
    str_indexof_re_args_of_non_none (by
      unfold term_has_non_none_type
      exact h)
  exact
    ⟨smt_term_typeof_non_none_of_eq_non_none hArgs.1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none hArgs.2.1 (by simp),
      smt_term_typeof_non_none_of_eq_non_none hArgs.2.2 (by simp)⟩

private theorem smt_bvite_args_non_none
    {c t1 t2 : SmtTerm}
    (h :
      __smtx_typeof
          (SmtTerm.ite (SmtTerm.eq c (SmtTerm.Binary 1 1)) t1 t2) ≠
        SmtType.None) :
    __smtx_typeof c ≠ SmtType.None ∧
      __smtx_typeof t1 ≠ SmtType.None ∧
        __smtx_typeof t2 ≠ SmtType.None := by
  rcases smt_ite_args_non_none h with ⟨hEq, ht1, ht2⟩
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof c)
          (__smtx_typeof (SmtTerm.Binary 1 1)) ≠
        SmtType.None := by
    simpa [typeof_eq_eq] using hEq
  have hEqArgs := smtx_typeof_eq_non_none hEqNN
  exact ⟨hEqArgs.2, ht1, ht2⟩

private theorem smt_strings_num_occur_args_non_none
    {haystack needle : SmtTerm}
    (h :
      __smtx_typeof
          (SmtTerm.div
            (SmtTerm.neg (SmtTerm.str_len haystack)
              (SmtTerm.str_len
                (SmtTerm.str_replace_all haystack needle
                  (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
            (SmtTerm.str_len needle)) ≠
        SmtType.None) :
    __smtx_typeof haystack ≠ SmtType.None ∧
      __smtx_typeof needle ≠ SmtType.None := by
  let replaced :=
    SmtTerm.str_replace_all haystack needle
      (SmtTerm.seq_empty (SmtType.Seq SmtType.Char))
  let num := SmtTerm.neg (SmtTerm.str_len haystack) (SmtTerm.str_len replaced)
  let den := SmtTerm.str_len needle
  have hDivNN : term_has_non_none_type (SmtTerm.div num den) := by
    unfold term_has_non_none_type
    simpa [num, den, replaced] using h
  have hDivArgs :=
    int_binop_args_of_non_none (op := SmtTerm.div) (R := SmtType.Int)
      (typeof_div_eq num den) hDivNN
  have hNumNN : term_has_non_none_type num := by
    unfold term_has_non_none_type
    rw [hDivArgs.1]
    simp
  have hDenNN : term_has_non_none_type den := by
    unfold term_has_non_none_type
    rw [hDivArgs.2]
    simp
  rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
      (typeof_str_len_eq needle) hDenNN with
    ⟨Tn, hNeedleSeq⟩
  have hNeedleNN : __smtx_typeof needle ≠ SmtType.None :=
    smt_term_typeof_non_none_of_eq_non_none hNeedleSeq (by simp)
  rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
      (typeof_neg_eq (SmtTerm.str_len haystack) (SmtTerm.str_len replaced))
      hNumNN with hArgs | hArgs
  · have hHaystackLenNN : term_has_non_none_type (SmtTerm.str_len haystack) := by
      unfold term_has_non_none_type
      rw [hArgs.1]
      simp
    rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
        (typeof_str_len_eq haystack) hHaystackLenNN with
      ⟨Th, hHaystackSeq⟩
    exact
      ⟨smt_term_typeof_non_none_of_eq_non_none hHaystackSeq (by simp),
        hNeedleNN⟩
  · have hHaystackLenNN : term_has_non_none_type (SmtTerm.str_len haystack) := by
      unfold term_has_non_none_type
      rw [hArgs.1]
      simp
    rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
        (typeof_str_len_eq haystack) hHaystackLenNN with
      ⟨Th, hHaystackSeq⟩
    exact
      ⟨smt_term_typeof_non_none_of_eq_non_none hHaystackSeq (by simp),
        hNeedleNN⟩

private theorem smt_tuple_prepend_args_non_none
    {head tail : SmtTerm}
    (h :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend head (__smtx_typeof head) tail) ≠
        SmtType.None) :
    __smtx_typeof head ≠ SmtType.None ∧
      __smtx_typeof tail ≠ SmtType.None := by
  cases hTail : __smtx_typeof tail
  case Datatype s d =>
    cases d
    case sum c dTail =>
      cases dTail
      case null =>
        by_cases hs : s = (native_string_lit "@Tuple")
        · subst s
          exact
            ⟨TranslationProofs.smtx_tuple_prepend_head_non_none_of_tail_tuple_type
                tail head (__smtx_typeof head) c hTail h,
              by simp⟩
        · exact False.elim (h (by
            simp [__eo_to_smt_tuple_prepend,
              __eo_to_smt_tuple_prepend_of_type, hTail, hs, native_streq,
              native_and, native_ite, smtx_typeof_none]))
      all_goals
        exact False.elim (h (by
          simp [__eo_to_smt_tuple_prepend, __eo_to_smt_tuple_prepend_of_type,
            hTail, smtx_typeof_none]))
    all_goals
      exact False.elim (h (by
        simp [__eo_to_smt_tuple_prepend, __eo_to_smt_tuple_prepend_of_type,
          hTail, smtx_typeof_none]))
  all_goals
    exact False.elim (h (by
      simp [__eo_to_smt_tuple_prepend, __eo_to_smt_tuple_prepend_of_type,
        hTail, smtx_typeof_none]))

private theorem smt_set_singleton_arg_non_none
    {a : SmtTerm}
    (h : __smtx_typeof (SmtTerm.set_singleton a) ≠ SmtType.None) :
    __smtx_typeof a ≠ SmtType.None := by
  have hGuardNN :
      __smtx_typeof_guard_wf
          (SmtType.Set (__smtx_typeof a))
          (SmtType.Set (__smtx_typeof a)) ≠
        SmtType.None := by
    simpa [__smtx_typeof] using h
  have hSetWf :
      __smtx_type_wf (SmtType.Set (__smtx_typeof a)) = true :=
    smtx_typeof_guard_wf_wf_of_non_none
      (SmtType.Set (__smtx_typeof a))
      (SmtType.Set (__smtx_typeof a)) hGuardNN
  have hSetComponent :
      __smtx_type_wf_component (SmtType.Set (__smtx_typeof a)) = true := by
    simpa [__smtx_type_wf] using hSetWf
  have hSetWfRec :
      __smtx_type_wf_rec (SmtType.Set (__smtx_typeof a))
        native_reflist_nil = true :=
    (smtx_type_wf_component_parts hSetComponent).2
  have hArgWfRec :
      __smtx_type_wf_rec (__smtx_typeof a) native_reflist_nil = true :=
    TranslationProofs.set_type_wf_rec_component_of_wf hSetWfRec
  intro hNone
  rw [hNone] at hArgWfRec
  simp [__smtx_type_wf_rec] at hArgWfRec

private theorem smt_updater_args_non_none
    {idx y x : SmtTerm}
    (h :
      __smtx_typeof (__eo_to_smt_updater idx y x) ≠
        SmtType.None) :
    (∃ s d i j, idx = SmtTerm.DtSel s d i j) ∧
      __smtx_typeof y ≠ SmtType.None ∧
        __smtx_typeof x ≠ SmtType.None := by
  cases idx
  case DtSel s d i j =>
    have hIdx :=
      eo_to_smt_updater_dt_sel_guard_of_non_none s d i j y x h
    have hIteNN :
        term_has_non_none_type
          (SmtTerm.ite
            (SmtTerm.Apply (SmtTerm.DtTester s d i) y)
            (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
              (__smtx_dt_num_sels d i) y x (SmtTerm.DtCons s d i))
            y) := by
      unfold term_has_non_none_type
      simpa [__eo_to_smt_updater, native_ite, hIdx] using h
    rcases ite_args_of_non_none hIteNN with
      ⟨T, hCond, hThen, hElse, hT⟩
    have hYNN : __smtx_typeof y ≠ SmtType.None :=
      smt_term_typeof_non_none_of_eq_non_none hElse hT
    have hRecNN :
        __smtx_typeof
            (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i j)
              (__smtx_dt_num_sels d i) y x (SmtTerm.DtCons s d i)) ≠
          SmtType.None :=
      smt_term_typeof_non_none_of_eq_non_none hThen hT
    have hXNN : __smtx_typeof x ≠ SmtType.None :=
      eo_to_smt_updater_rec_update_arg_non_none_of_non_none
        s d i j (__smtx_dt_num_sels d i) y x (SmtTerm.DtCons s d i)
        (by intro s d i j h; cases h)
        (by intro s d i h; cases h)
        hIdx hRecNN
    exact ⟨⟨s, d, i, j, rfl⟩, hYNN, hXNN⟩
  all_goals
    exact False.elim (h (by
      simp [__eo_to_smt_updater, smtx_typeof_none]))

private theorem smt_tuple_update_args_non_none
    {idx y x : SmtTerm}
    (h :
      __smtx_typeof
          (__eo_to_smt_tuple_update (__smtx_typeof y) idx y x) ≠
        SmtType.None) :
    (∃ n, idx = SmtTerm.Numeral n) ∧
      __smtx_typeof y ≠ SmtType.None ∧
        __smtx_typeof x ≠ SmtType.None := by
  cases hYTy : __smtx_typeof y
  case Datatype s d =>
    cases idx
    case Numeral n =>
      by_cases hs : s = (native_string_lit "@Tuple")
      · subst s
        cases hNonneg : native_zleq 0 n
        · exact False.elim (h (by
            simp [__eo_to_smt_tuple_update, hYTy, hNonneg, native_and,
              native_ite, smtx_typeof_none]))
        · have hUpdaterNN :
              __smtx_typeof
                  (__eo_to_smt_updater
                    (SmtTerm.DtSel (native_string_lit "@Tuple") d
                      native_nat_zero (native_int_to_nat n))
                    y x) ≠
                SmtType.None := by
            simpa [__eo_to_smt_tuple_update, hYTy, hNonneg, native_and,
              native_ite] using h
          rcases smt_updater_args_non_none hUpdaterNN with
            ⟨_hIdx, hYNN, hXNN⟩
          exact ⟨⟨n, rfl⟩, by simp, hXNN⟩
      · exact False.elim (h (by
          simp [__eo_to_smt_tuple_update, hYTy, hs, native_streq,
            native_and, native_ite, smtx_typeof_none]))
    all_goals
      exact False.elim (h (by
        simp [__eo_to_smt_tuple_update, hYTy, smtx_typeof_none]))
  all_goals
    exact False.elim (h (by
      simp [__eo_to_smt_tuple_update, hYTy, smtx_typeof_none]))

private theorem native_eo_to_smt_closed_of_dt_sel_translation
    {x : Term} {s : native_String} {d : SmtDatatype}
    {i j : native_Nat}
    (h : __eo_to_smt x = SmtTerm.DtSel s d i j) :
    native_eo_to_smt_closed x = true := by
  rcases eo_to_smt_eq_dt_sel_cases x s d i j h with hSel | hPurify
  · rcases hSel with ⟨d0, _hd, hx, _hReserved⟩
    subst x
    simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec]
  · rcases hPurify with ⟨z, hx, _hz⟩
    subst x
    exfalso
    change
      native_eo_to_smt_guard_closed z
          (SmtTerm._at_purify (__eo_to_smt z)) =
        SmtTerm.DtSel s d i j at h
    cases hzClosed : native_eo_to_smt_closed z <;>
      simp [native_eo_to_smt_guard_closed, native_ite, hzClosed] at h

private theorem native_eo_to_smt_uop_indices_safe_of_dt_sel_translation
    {x : Term} {s : native_String} {d : SmtDatatype}
    {i j : native_Nat}
    (h : __eo_to_smt x = SmtTerm.DtSel s d i j) :
    native_eo_to_smt_uop_indices_safe x = true := by
  rcases eo_to_smt_eq_dt_sel_cases x s d i j h with hSel | hPurify
  · rcases hSel with ⟨d0, _hd, hx, _hReserved⟩
    subst x
    simp [native_eo_to_smt_uop_indices_safe]
  · rcases hPurify with ⟨z, hx, _hz⟩
    subst x
    exfalso
    change
      native_eo_to_smt_guard_closed z
          (SmtTerm._at_purify (__eo_to_smt z)) =
        SmtTerm.DtSel s d i j at h
    cases hzClosed : native_eo_to_smt_closed z <;>
      simp [native_eo_to_smt_guard_closed, native_ite, hzClosed] at h

private theorem native_eo_to_smt_closed_of_dt_cons_translation
    {x : Term} {s : native_String} {d : SmtDatatype} {i : native_Nat}
    (h : __eo_to_smt x = SmtTerm.DtCons s d i) :
    native_eo_to_smt_closed x = true := by
  rcases eo_to_smt_eq_dt_cons_cases x s d i h with hCons | hTuple
  · rcases hCons with ⟨d0, _hd, hx, _hReserved⟩
    subst x
    simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec]
  · rcases hTuple with ⟨_hs, _hd, _hi, hx⟩
    subst x
    simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec]

private theorem native_eo_to_smt_uop_indices_safe_of_dt_cons_translation
    {x : Term} {s : native_String} {d : SmtDatatype} {i : native_Nat}
    (h : __eo_to_smt x = SmtTerm.DtCons s d i) :
    native_eo_to_smt_uop_indices_safe x = true := by
  rcases eo_to_smt_eq_dt_cons_cases x s d i h with hCons | hTuple
  · rcases hCons with ⟨d0, _hd, hx, _hReserved⟩
    subst x
    simp [native_eo_to_smt_uop_indices_safe]
  · rcases hTuple with ⟨_hs, _hd, _hi, hx⟩
    subst x
    simp [native_eo_to_smt_uop_indices_safe]

private theorem native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
    {f x : Term}
    (ihf :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe f = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.Apply f x) = true := by
  by_cases hSelWitness :
      ∃ s d i j, __eo_to_smt f = SmtTerm.DtSel s d i j
  · rcases hSelWitness with ⟨s, d, i, j, hSel⟩
    exact native_eo_to_smt_uop_indices_safe_apply_intro
      (native_eo_to_smt_uop_indices_safe_of_dt_sel_translation hSel)
      (ihx (smtx_apply_arg_non_none_of_any_non_none h))
  · have hSel :
        ∀ s d i j, __eo_to_smt f ≠ SmtTerm.DtSel s d i j := by
      intro s d i j hEq
      exact hSelWitness ⟨s, d, i, j, hEq⟩
    have hTester :
        ∀ s d i, __eo_to_smt f ≠ SmtTerm.DtTester s d i := by
      intro s d i hEq
      exact eo_to_smt_ne_dt_tester f s d i hEq
    exact native_eo_to_smt_uop_indices_safe_apply_intro
      (ihf
        (smtx_apply_head_non_none_of_non_special_non_none
          (__eo_to_smt f) (__eo_to_smt x) hSel hTester h))
      (ihx
        (smtx_apply_arg_non_none_of_non_special_non_none
          (__eo_to_smt f) (__eo_to_smt x) hSel hTester h))

private theorem native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
    {f x : Term}
    (ihf :
      __smtx_typeof (__eo_to_smt f) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe f = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (h :
      __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.Apply f x) = true := by
  have hApply :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) ≠
        SmtType.None := by
    simpa [hTranslate] using h
  exact native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
    (f := f) (x := x) ihf ihx hApply

private theorem native_eo_to_smt_uop_indices_safe_of_apply_uop_arg_non_none
    {op : UserOp} {x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (hx : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.Apply (Term.UOp op) x) = true := by
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (by simp [native_eo_to_smt_uop_indices_safe])
    (ihx hx)

private theorem native_eo_to_smt_uop_indices_safe_of_apply_uop_body_non_none
    {op : UserOp} {x : Term} {body : SmtTerm}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (hBodyArgs :
      __smtx_typeof body ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hTranslate : __eo_to_smt (Term.Apply (Term.UOp op) x) = body)
    (h :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.Apply (Term.UOp op) x) = true := by
  have hBody : __smtx_typeof body ≠ SmtType.None := by
    simpa [hTranslate] using h
  exact native_eo_to_smt_uop_indices_safe_of_apply_uop_arg_non_none
    (op := op) (x := x) ihx (hBodyArgs hBody)

private theorem native_eo_to_smt_uop_indices_safe_of_apply_apply_uop_body_non_none
    {op : UserOp} {y x : Term} {body : SmtTerm}
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (hBodyArgs :
      __smtx_typeof body ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ∧
          __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x) = body)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) y) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.Apply (Term.UOp op) y) x) = true := by
  have hBody : __smtx_typeof body ≠ SmtType.None := by
    simpa [hTranslate] using h
  rcases hBodyArgs hBody with ⟨hy, hx⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_of_apply_uop_arg_non_none
      (op := op) (x := y) ihy hy)
    (ihx hx)

private theorem native_eo_to_smt_uop_indices_safe_of_apply_apply_apply_uop_body_non_none
    {op : UserOp} {z y x : Term} {body : SmtTerm}
    (ihz :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe z = true)
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (hBodyArgs :
      __smtx_typeof body ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ∧
          __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ∧
            __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        body)
    (h :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) z) y) x) =
        true := by
  have hBody : __smtx_typeof body ≠ SmtType.None := by
    simpa [hTranslate] using h
  rcases hBodyArgs hBody with ⟨hz, hy, hx⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_apply_intro
      (native_eo_to_smt_uop_indices_safe_of_apply_uop_arg_non_none
        (op := op) (x := z) ihz hz)
      (ihy hy))
    (ihx hx)

private theorem native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
    {op : UserOp1} {x : Term} {n : native_Int}
    (hx : __eo_to_smt x = SmtTerm.Numeral n) :
    native_eo_to_smt_uop_indices_safe (Term.UOp1 op x) = true :=
  native_eo_to_smt_uop_indices_safe_uop1_intro
    (native_eo_to_smt_closed_of_smt_numeral hx)
    (native_eo_to_smt_uop_indices_safe_of_smt_numeral hx)

private theorem native_eo_to_smt_uop_indices_safe_uop2_of_smt_numerals
    {op : UserOp2} {x y : Term} {m n : native_Int}
    (hx : __eo_to_smt x = SmtTerm.Numeral m)
    (hy : __eo_to_smt y = SmtTerm.Numeral n) :
    native_eo_to_smt_uop_indices_safe (Term.UOp2 op x y) = true :=
  native_eo_to_smt_uop_indices_safe_uop2_intro
    (native_eo_to_smt_closed_of_smt_numeral hx)
    (native_eo_to_smt_closed_of_smt_numeral hy)
    (native_eo_to_smt_uop_indices_safe_of_smt_numeral hx)
    (native_eo_to_smt_uop_indices_safe_of_smt_numeral hy)

private theorem native_eo_to_smt_uop_indices_safe_of_apply_apply_update_non_none
    {idx y x : Term}
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) y) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.update idx) y) x) = true := by
  have hBody :
      __smtx_typeof
          (__eo_to_smt_updater (__eo_to_smt idx)
            (__eo_to_smt y) (__eo_to_smt x)) ≠
        SmtType.None := by
    simpa using h
  rcases smt_updater_args_non_none hBody with
    ⟨⟨s, d, i, j, hIdx⟩, hYNN, hXNN⟩
  have hIdxSafe :
      native_eo_to_smt_uop_indices_safe (Term.UOp1 UserOp1.update idx) =
        true :=
    native_eo_to_smt_uop_indices_safe_uop1_intro
      (op := UserOp1.update)
      (native_eo_to_smt_closed_of_dt_sel_translation hIdx)
      (native_eo_to_smt_uop_indices_safe_of_dt_sel_translation hIdx)
  exact
    native_eo_to_smt_uop_indices_safe_apply_intro
      (native_eo_to_smt_uop_indices_safe_apply_intro
        hIdxSafe (ihy hYNN))
      (ihx hXNN)

private theorem native_eo_to_smt_uop_indices_safe_of_apply_apply_tuple_update_non_none
    {idx y x : Term}
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) y) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) y) x) = true := by
  have hBody :
      __smtx_typeof
          (__eo_to_smt_tuple_update
            (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt idx)
            (__eo_to_smt y) (__eo_to_smt x)) ≠
        SmtType.None := by
    simpa using h
  rcases smt_tuple_update_args_non_none hBody with
    ⟨⟨n, hIdx⟩, hYNN, hXNN⟩
  have hIdxSafe :
      native_eo_to_smt_uop_indices_safe
          (Term.UOp1 UserOp1.tuple_update idx) =
        true :=
    native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.tuple_update) hIdx
  exact
    native_eo_to_smt_uop_indices_safe_apply_intro
      (native_eo_to_smt_uop_indices_safe_apply_intro
        hIdxSafe (ihy hYNN))
      (ihx hXNN)

private theorem native_eo_to_smt_uop_indices_safe_of_type_valid_rec :
    ∀ {refs : List native_String} {T : Term},
      eo_type_valid_rec refs T ->
      native_eo_to_smt_closed T = true ∧
        native_eo_to_smt_uop_indices_safe T = true
  | refs, Term.Bool, _ => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.USort i, _ => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.UOp op, h => by
      cases op <;> simp [eo_type_valid_rec,
        native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe] at h ⊢
  | refs, Term.DatatypeType s d, h => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.DatatypeTypeRef s, h => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe]
  | refs, Term.DtcAppType T U, h => by
      rcases h with ⟨hT, hU⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hUc', hTs, hUs,
        native_and]
  | refs, Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral n), h => by
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, native_and]
  | refs, Term.Apply (Term.UOp UserOp.Seq) T, h => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using h
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, native_and]
  | refs, Term.Apply (Term.UOp UserOp.Set) T, h => by
      have hT : eo_type_valid_rec [] T := by
        simpa [eo_type_valid_rec] using h
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, native_and]
  | refs, Term.Apply (Term.Apply Term.FunType T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U) with ⟨hT, hU⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, hUc', hUs,
        native_and]
  | refs, Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U) with ⟨hT, hU⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, hUc', hUs,
        native_and]
  | refs, Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U, h => by
      rcases (by simpa [eo_type_valid_rec] using h :
        eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U ∧
          __smtx_type_wf
            (__eo_to_smt_type_tuple (__eo_to_smt_type T)
              (__eo_to_smt_type U)) = true) with ⟨hT, hU, _⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hT with
        ⟨hTc, hTs⟩
      rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hU with
        ⟨hUc, hUs⟩
      have hTc' := native_eo_to_smt_closed_rec_nil_of_closed hTc
      have hUc' := native_eo_to_smt_closed_rec_nil_of_closed hUc
      simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe, hTc', hTs, hUc', hUs,
        native_and]
  | refs, Term.Apply f x, h => by
      cases f with
      | UOp op =>
          cases op with
          | Int =>
              exfalso
              simp [eo_type_valid_rec] at h
          | Real =>
              exfalso
              simp [eo_type_valid_rec] at h
          | Char =>
              exfalso
              simp [eo_type_valid_rec] at h
          | UnitTuple =>
              exfalso
              simp [eo_type_valid_rec] at h
          | BitVec =>
              cases x with
              | Numeral n =>
                  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                    native_eo_to_smt_uop_indices_safe, native_and]
              | _ =>
                  exfalso
                  simp [eo_type_valid_rec] at h
          | Seq =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using h
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                ⟨hxc, hxs⟩
              have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
              simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                native_eo_to_smt_uop_indices_safe, hxc', hxs, native_and]
          | Set =>
              have hx : eo_type_valid_rec [] x := by
                simpa [eo_type_valid_rec] using h
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                ⟨hxc, hxs⟩
              have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
              simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                native_eo_to_smt_uop_indices_safe, hxc', hxs, native_and]
          | _ =>
              exfalso
              simp [eo_type_valid_rec] at h
      | Apply g y =>
          cases g with
          | FunType =>
              rcases (by simpa [eo_type_valid_rec] using h :
                eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hy with
                ⟨hyc, hys⟩
              rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                ⟨hxc, hxs⟩
              have hyc' := native_eo_to_smt_closed_rec_nil_of_closed hyc
              have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
              simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                native_eo_to_smt_uop_indices_safe, hyc', hys, hxc', hxs,
                native_and]
          | UOp op =>
              cases op with
              | Array =>
                  rcases (by simpa [eo_type_valid_rec] using h :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with
                    ⟨hy, hx⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hy with
                    ⟨hyc, hys⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                    ⟨hxc, hxs⟩
                  have hyc' := native_eo_to_smt_closed_rec_nil_of_closed hyc
                  have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
                  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                    native_eo_to_smt_uop_indices_safe, hyc', hys, hxc', hxs,
                    native_and]
              | Tuple =>
                  rcases (by simpa [eo_type_valid_rec] using h :
                    eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x ∧
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y)
                          (__eo_to_smt_type x)) = true) with
                    ⟨hy, hx, _⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hy with
                    ⟨hyc, hys⟩
                  rcases native_eo_to_smt_uop_indices_safe_of_type_valid_rec hx with
                    ⟨hxc, hxs⟩
                  have hyc' := native_eo_to_smt_closed_rec_nil_of_closed hyc
                  have hxc' := native_eo_to_smt_closed_rec_nil_of_closed hxc
                  simp [native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
                    native_eo_to_smt_uop_indices_safe, hyc', hys, hxc', hxs,
                    native_and]
              | _ =>
                  exfalso
                  simp [eo_type_valid_rec] at h
          | _ =>
              exfalso
              simp [eo_type_valid_rec] at h
      | _ =>
          exfalso
          simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_nil, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_cons, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Boolean b, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Numeral n, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Rational q, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.String s, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Binary w n, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Type, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Stuck, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.FunType, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.Var name T, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.DtCons s d i, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.DtSel s d i j, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.UConst i T, h => by
      exfalso
      simp [eo_type_valid_rec] at h
  | refs, Term.UOp1 op x, h => by
      cases op <;> exfalso <;> simp [eo_type_valid_rec] at h
  | refs, Term.UOp2 op x y, h => by
      cases op <;> exfalso <;> simp [eo_type_valid_rec] at h
  | refs, Term.UOp3 op x y z, h => by
      cases op <;> exfalso <;> simp [eo_type_valid_rec] at h

private theorem native_eo_to_smt_uop_indices_safe_of_type_valid
    {T : Term} :
    eo_type_valid T ->
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true := by
  intro h
  cases T with
  | UOp op =>
      cases op <;> simp [eo_type_valid, eo_type_valid_rec,
        native_eo_to_smt_closed, native_eo_to_smt_closed_rec,
        native_eo_to_smt_uop_indices_safe] at h ⊢
  | _ =>
      exact native_eo_to_smt_uop_indices_safe_of_type_valid_rec
        (refs := []) h

private theorem native_eo_to_smt_uop_indices_safe_of_smt_type_wf
    {T : Term}
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true :=
  native_eo_to_smt_uop_indices_safe_of_type_valid
    (eo_type_valid_of_smt_wf T hWf)

private theorem native_eo_to_smt_uop_indices_safe_of_typed_list_elem_type_non_none
    (root : Term)
    (ih :
      ∀ x : Term,
        sizeOf x < sizeOf root ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe x = true) :
    ∀ xs : Term,
      sizeOf xs < sizeOf root ->
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe xs = true := by
  let rec go : ∀ xs : Term,
      sizeOf xs < sizeOf root ->
      __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe xs = true
    | xs, hLt, h => by
        cases xs
        case Apply f tail =>
          cases f
          case UOp op =>
            cases op
            case _at__at_TypedList_nil =>
              have hWf : __smtx_type_wf (__eo_to_smt_type tail) = true := by
                by_cases hWf : __smtx_type_wf (__eo_to_smt_type tail) = true
                · exact hWf
                · exfalso
                  apply h
                  simp [__eo_to_smt_typed_list_elem_type, native_ite, hWf]
              rcases native_eo_to_smt_uop_indices_safe_of_smt_type_wf
                  (T := tail) hWf with
                ⟨_tailClosed, tailSafe⟩
              exact native_eo_to_smt_uop_indices_safe_apply_intro
                (by simp [native_eo_to_smt_uop_indices_safe]) tailSafe
            all_goals
              exfalso
              apply h
              simp [__eo_to_smt_typed_list_elem_type]
          case Apply g head =>
            cases g
            case UOp op =>
              cases op
              case _at__at_TypedList_cons =>
                let headTy := __smtx_typeof (__eo_to_smt head)
                let tailTy := __eo_to_smt_typed_list_elem_type tail
                have hGuard : native_Teq headTy tailTy = true := by
                  by_cases hGuard : native_Teq headTy tailTy = true
                  · exact hGuard
                  · exfalso
                    apply h
                    simp [__eo_to_smt_typed_list_elem_type, headTy, tailTy,
                      native_ite, hGuard]
                have hHeadTyNN : headTy ≠ SmtType.None := by
                  change
                    (native_ite (native_Teq headTy tailTy) headTy
                        SmtType.None) ≠
                      SmtType.None at h
                  rw [hGuard] at h
                  exact h
                have hTailTyNN : tailTy ≠ SmtType.None := by
                  intro hTailNone
                  have hHeadEqTail : headTy = tailTy := by
                    simpa [native_Teq] using hGuard
                  exact hHeadTyNN (by rw [hHeadEqTail, hTailNone])
                have hHeadLt : sizeOf head < sizeOf root := by
                  simp at hLt
                  omega
                have hTailLt : sizeOf tail < sizeOf root := by
                  simp at hLt
                  omega
                exact native_eo_to_smt_uop_indices_safe_apply_intro
                  (native_eo_to_smt_uop_indices_safe_apply_intro
                    (by simp [native_eo_to_smt_uop_indices_safe])
                    (ih head hHeadLt (by simpa [headTy] using hHeadTyNN)))
                  (go tail hTailLt (by simpa [tailTy] using hTailTyNN))
              all_goals
                exfalso
                apply h
                simp [__eo_to_smt_typed_list_elem_type]
            all_goals
              exfalso
              apply h
              simp [__eo_to_smt_typed_list_elem_type]
          all_goals
            exfalso
            apply h
            simp [__eo_to_smt_typed_list_elem_type]
        all_goals
          exfalso
          apply h
          simp [__eo_to_smt_typed_list_elem_type]
  exact go

private theorem native_eo_to_smt_uop_indices_safe_of_set_insert_non_none
    (root : Term)
    (ih :
      ∀ x : Term,
        sizeOf x < sizeOf root ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe x = true)
    (base : Term)
    (hBaseLt : sizeOf base < sizeOf root) :
    ∀ xs : Term,
      sizeOf xs < sizeOf root ->
      __smtx_typeof (__eo_to_smt_set_insert xs (__eo_to_smt base)) ≠
        SmtType.None ->
        native_eo_to_smt_uop_indices_safe xs = true ∧
          native_eo_to_smt_uop_indices_safe base = true := by
  let rec go : ∀ xs : Term,
      sizeOf xs < sizeOf root ->
      __smtx_typeof (__eo_to_smt_set_insert xs (__eo_to_smt base)) ≠
        SmtType.None ->
        native_eo_to_smt_uop_indices_safe xs = true ∧
          native_eo_to_smt_uop_indices_safe base = true
    | xs, hLt, h => by
        cases xs
        case __eo_List_nil =>
          exact
            ⟨by simp [native_eo_to_smt_uop_indices_safe],
              ih base hBaseLt (by
                simpa [__eo_to_smt_set_insert] using h)⟩
        case Apply f tail =>
          cases f
          case Apply g head =>
            cases g
            case __eo_List_cons =>
              have hUnionNN :
                  __smtx_typeof
                      (SmtTerm.set_union
                        (SmtTerm.set_singleton (__eo_to_smt head))
                        (__eo_to_smt_set_insert tail (__eo_to_smt base))) ≠
                    SmtType.None := by
                simpa [__eo_to_smt_set_insert] using h
              rcases smt_set_binop_args_non_none
                  (op := SmtTerm.set_union)
                  (typeof_set_union_eq
                    (SmtTerm.set_singleton (__eo_to_smt head))
                    (__eo_to_smt_set_insert tail (__eo_to_smt base)))
                  hUnionNN with
                ⟨hSingletonNN, hTailNN⟩
              have hHeadNN :
                  __smtx_typeof (__eo_to_smt head) ≠ SmtType.None :=
                smt_set_singleton_arg_non_none hSingletonNN
              have hHeadLt : sizeOf head < sizeOf root := by
                simp at hLt
                omega
              have hTailLt : sizeOf tail < sizeOf root := by
                simp at hLt
                omega
              rcases go tail hTailLt hTailNN with
                ⟨hTailSafe, hBaseSafe⟩
              exact
                ⟨native_eo_to_smt_uop_indices_safe_apply_intro
                    (native_eo_to_smt_uop_indices_safe_apply_intro
                      (by simp [native_eo_to_smt_uop_indices_safe])
                      (ih head hHeadLt hHeadNN))
                    hTailSafe,
                  hBaseSafe⟩
            all_goals
              exfalso
              apply h
              simp [__eo_to_smt_set_insert, smtx_typeof_none]
          all_goals
            exfalso
            apply h
            simp [__eo_to_smt_set_insert, smtx_typeof_none]
        all_goals
          exfalso
          apply h
          simp [__eo_to_smt_set_insert, smtx_typeof_none]
  exact go

private theorem native_eo_to_smt_uop_indices_safe_of_apply_apply_set_insert_non_none
    {y x : Term}
    (root : Term)
    (ih :
      ∀ z : Term,
        sizeOf z < sizeOf root ->
        __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe z = true)
    (hYLt : sizeOf y < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x) = true := by
  have hArgs :
      native_eo_to_smt_uop_indices_safe y = true ∧
        native_eo_to_smt_uop_indices_safe x = true := by
    cases y
    case __eo_List_nil =>
      exfalso
      exact h (by
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact smtx_typeof_none)
    all_goals
      change
        __smtx_typeof (__eo_to_smt_set_insert _ (__eo_to_smt x)) ≠
          SmtType.None at h
      exact native_eo_to_smt_uop_indices_safe_of_set_insert_non_none
        root ih x hXLt _ hYLt h
  exact
    native_eo_to_smt_uop_indices_safe_apply_intro
      (native_eo_to_smt_uop_indices_safe_apply_intro
        (by simp [native_eo_to_smt_uop_indices_safe])
        hArgs.1)
      hArgs.2

private theorem native_eo_to_smt_uop_indices_safe_of_apply_apply_set_insert_non_none_unfolded
    {y x : Term}
    (root : Term)
    (ih :
      ∀ z : Term,
        sizeOf z < sizeOf root ->
        __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe z = true)
    (hYLt : sizeOf y < sizeOf root)
    (hXLt : sizeOf x < sizeOf root)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)) ≠
        SmtType.None) :
    native_and
      (native_eo_to_smt_uop_indices_safe
        (Term.Apply (Term.UOp UserOp.set_insert) y))
      (native_eo_to_smt_uop_indices_safe x) = true := by
  simpa [native_eo_to_smt_uop_indices_safe] using
    native_eo_to_smt_uop_indices_safe_of_apply_apply_set_insert_non_none
      root ih hYLt hXLt h

private theorem native_eo_to_smt_uop_indices_safe_of_apply_distinct_non_none
    {xs : Term}
    (root : Term)
    (ih :
      ∀ x : Term,
        sizeOf x < sizeOf root ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe x = true)
    (hLt : sizeOf xs < sizeOf root)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp UserOp.distinct) xs)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp UserOp.distinct) xs) = true := by
  change
    __smtx_typeof
        (native_ite
          (native_Teq (__eo_to_smt_typed_list_elem_type xs) SmtType.None)
          SmtTerm.None (__eo_to_smt_distinct xs)) ≠
      SmtType.None at h
  have hElemNN : __eo_to_smt_typed_list_elem_type xs ≠ SmtType.None := by
    intro hElemNone
    apply h
    simp [native_ite, hElemNone, native_Teq,
      TranslationProofs.smtx_typeof_none]
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (by simp [native_eo_to_smt_uop_indices_safe])
    (native_eo_to_smt_uop_indices_safe_of_typed_list_elem_type_non_none
      root ih xs hLt hElemNN)

private theorem smtx_typeof_not_arg_bool_of_non_none
    {t : SmtTerm}
    (h : __smtx_typeof (SmtTerm.not t) ≠ SmtType.None) :
    __smtx_typeof t = SmtType.Bool := by
  have hNotBool : __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
    rw [typeof_not_eq]
    by_cases hArg : native_Teq (__smtx_typeof t) SmtType.Bool = true
    · simp [native_ite, hArg]
    · exfalso
      apply h
      rw [typeof_not_eq]
      simp [native_ite, hArg, TranslationProofs.smtx_typeof_none]
  exact smtx_typeof_not_arg_bool t hNotBool

private theorem native_eo_to_smt_uop_indices_safe_of_var_list_exists_bool
    (root : Term) :
    ∀ xs body,
      sizeOf xs < sizeOf root ->
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
        native_eo_to_smt_uop_indices_safe xs = true := by
  let rec go : ∀ xs body,
      sizeOf xs < sizeOf root ->
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
        native_eo_to_smt_uop_indices_safe xs = true
    | xs, body, hLt, hBool => by
        cases xs
        case __eo_List_nil =>
          simp [native_eo_to_smt_uop_indices_safe]
        case Apply f tail =>
          cases f
          case Apply g head =>
            cases g
            case __eo_List_cons =>
              cases head
              case Var name T =>
                cases name
                case String s =>
                  have hExistsTy :
                      __smtx_typeof
                          (SmtTerm.exists s (__eo_to_smt_type T)
                            (__eo_to_smt_exists tail body)) =
                        SmtType.Bool := by
                    simpa [__eo_to_smt_exists] using hBool
                  have hExistsNN :
                      term_has_non_none_type
                        (SmtTerm.exists s (__eo_to_smt_type T)
                          (__eo_to_smt_exists tail body)) := by
                    unfold term_has_non_none_type
                    rw [hExistsTy]
                    simp
                  have hTailBool :
                      __smtx_typeof (__eo_to_smt_exists tail body) =
                        SmtType.Bool := by
                    simpa using exists_body_bool_of_non_none hExistsNN
                  have hTailLt : sizeOf tail < sizeOf root := by
                    simp at hLt
                    omega
                  exact native_eo_to_smt_uop_indices_safe_apply_intro
                    (native_eo_to_smt_uop_indices_safe_apply_intro
                      (by simp [native_eo_to_smt_uop_indices_safe])
                      (by simp [native_eo_to_smt_uop_indices_safe]))
                    (go tail body hTailLt hTailBool)
                all_goals
                  exfalso
                  have hNone := hBool
                  simp [__eo_to_smt_exists,
                    TranslationProofs.smtx_typeof_none] at hNone
              all_goals
                exfalso
                have hNone := hBool
                simp [__eo_to_smt_exists,
                  TranslationProofs.smtx_typeof_none] at hNone
            all_goals
              exfalso
              have hNone := hBool
              simp [__eo_to_smt_exists,
                TranslationProofs.smtx_typeof_none] at hNone
          all_goals
            exfalso
            have hNone := hBool
            simp [__eo_to_smt_exists,
              TranslationProofs.smtx_typeof_none] at hNone
        all_goals
          exfalso
          have hNone := hBool
          simp [__eo_to_smt_exists,
            TranslationProofs.smtx_typeof_none] at hNone
  exact go

private theorem native_eo_to_smt_uop_indices_safe_of_apply_exists_non_none
    {xs F : Term}
    (root : Term)
    (ih :
      ∀ x : Term,
        sizeOf x < sizeOf root ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe x = true)
    (hXsLt : sizeOf xs < sizeOf root)
    (hFLt : sizeOf F < sizeOf root)
    (h :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) F)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) F) = true := by
  cases xs
  case __eo_List_nil =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            have hChain :
                __smtx_typeof
                    (__eo_to_smt_exists
                      (Term.Apply
                        (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T)) tail)
                      (__eo_to_smt F)) =
                  SmtType.Bool := by
              have hExistsNN :
                  term_has_non_none_type
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt F))) := by
                unfold term_has_non_none_type
                change
                  __smtx_typeof
                      (SmtTerm.exists s (__eo_to_smt_type T)
                        (__eo_to_smt_exists tail (__eo_to_smt F))) ≠
                    SmtType.None at h
                exact h
              simpa [__eo_to_smt_exists] using
                exists_term_typeof_of_non_none hExistsNN
            have hFBool :
                __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
              eo_to_smt_exists_body_bool_of_bool
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) tail)
                (__eo_to_smt F) hChain
            have hFNN : __smtx_typeof (__eo_to_smt F) ≠ SmtType.None := by
              rw [hFBool]
              simp
            exact native_eo_to_smt_uop_indices_safe_apply_intro
              (native_eo_to_smt_uop_indices_safe_apply_intro
                (by simp [native_eo_to_smt_uop_indices_safe])
                (native_eo_to_smt_uop_indices_safe_of_var_list_exists_bool
                  root
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) tail)
                  (__eo_to_smt F) hXsLt hChain))
              (ih F hFLt hFNN)
          all_goals
            exfalso
            apply h
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none
        all_goals
          exfalso
          apply h
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      all_goals
        exfalso
        apply h
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    all_goals
      exfalso
      apply h
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  all_goals
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem native_eo_to_smt_uop_indices_safe_of_apply_forall_non_none
    {xs F : Term}
    (root : Term)
    (ih :
      ∀ x : Term,
        sizeOf x < sizeOf root ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
          native_eo_to_smt_uop_indices_safe x = true)
    (hXsLt : sizeOf xs < sizeOf root)
    (hFLt : sizeOf F < sizeOf root)
    (h :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) = true := by
  cases xs
  case __eo_List_nil =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            have hChain :
                __smtx_typeof
                    (__eo_to_smt_exists
                      (Term.Apply
                        (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T)) tail)
                      (SmtTerm.not (__eo_to_smt F))) =
                  SmtType.Bool := by
              apply smtx_typeof_not_arg_bool_of_non_none
              change
                __smtx_typeof
                    (SmtTerm.not
                      (SmtTerm.exists s (__eo_to_smt_type T)
                        (__eo_to_smt_exists tail
                          (SmtTerm.not (__eo_to_smt F))))) ≠
                  SmtType.None at h
              simpa [__eo_to_smt_exists] using h
            have hNotF :
                __smtx_typeof (SmtTerm.not (__eo_to_smt F)) =
                  SmtType.Bool :=
              eo_to_smt_exists_body_bool_of_bool
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) tail)
                (SmtTerm.not (__eo_to_smt F)) hChain
            have hFBool : __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
              smtx_typeof_not_arg_bool (__eo_to_smt F) hNotF
            have hFNN : __smtx_typeof (__eo_to_smt F) ≠ SmtType.None := by
              rw [hFBool]
              simp
            exact native_eo_to_smt_uop_indices_safe_apply_intro
              (native_eo_to_smt_uop_indices_safe_apply_intro
                (by simp [native_eo_to_smt_uop_indices_safe])
                (native_eo_to_smt_uop_indices_safe_of_var_list_exists_bool
                  root
                  (Term.Apply
                    (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) tail)
                  (SmtTerm.not (__eo_to_smt F)) hXsLt hChain))
              (ih F hFLt hFNN)
          all_goals
            exfalso
            apply h
            change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
            rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
            simp [native_ite, native_Teq]
        all_goals
          exfalso
          apply h
          change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
          rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
          simp [native_ite, native_Teq]
      all_goals
        exfalso
        apply h
        change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
        rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
        simp [native_ite, native_Teq]
    all_goals
      exfalso
      apply h
      change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
      rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
      simp [native_ite, native_Teq]
  all_goals
    exfalso
    apply h
    change __smtx_typeof (SmtTerm.not SmtTerm.None) = SmtType.None
    rw [typeof_not_eq, TranslationProofs.smtx_typeof_none]
    simp [native_ite, native_Teq]

private theorem native_eo_to_smt_uop_indices_safe_of_seq_empty_non_none
    {T : Term}
    (h :
      __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) ≠
        SmtType.None) :
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true := by
  cases hTy : __eo_to_smt_type T
  case Seq A =>
    have hSeqNN : __smtx_typeof (SmtTerm.seq_empty A) ≠ SmtType.None := by
      intro hNone
      apply h
      simpa [__eo_to_smt_seq_empty, hTy] using hNone
    have hGuard :
        __smtx_typeof_guard_wf (SmtType.Seq A) (SmtType.Seq A) ≠
          SmtType.None := by
      unfold __smtx_typeof at hSeqNN
      exact hSeqNN
    have hWfSeq :=
      smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Seq A) (SmtType.Seq A) hGuard
    have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
      simpa [hTy] using hWfSeq
    exact native_eo_to_smt_uop_indices_safe_of_smt_type_wf hWf
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_seq_empty, hTy, TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_uop_indices_safe_of_set_empty_non_none
    {T : Term}
    (h :
      __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) ≠
        SmtType.None) :
    native_eo_to_smt_closed T = true ∧
      native_eo_to_smt_uop_indices_safe T = true := by
  cases hTy : __eo_to_smt_type T
  case Set A =>
    have hSetNN : __smtx_typeof (SmtTerm.set_empty A) ≠ SmtType.None := by
      intro hNone
      apply h
      simpa [__eo_to_smt_set_empty, hTy] using hNone
    have hGuard :
        __smtx_typeof_guard_wf (SmtType.Set A) (SmtType.Set A) ≠
          SmtType.None := by
      unfold __smtx_typeof at hSetNN
      exact hSetNN
    have hWfSet :=
      smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Set A) (SmtType.Set A) hGuard
    have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
      simpa [hTy] using hWfSet
    exact native_eo_to_smt_uop_indices_safe_of_smt_type_wf hWf
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_set_empty, hTy, TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_uop_indices_safe_of_uop1_non_none
    {op : UserOp1} {x : Term}
    (ih :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h : __smtx_typeof (__eo_to_smt (Term.UOp1 op x)) ≠ SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.UOp1 op x) = true := by
  cases op
  case _at_purify =>
    have hxClosed :
        native_eo_to_smt_closed x = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hBody :
        __smtx_typeof (SmtTerm._at_purify (__eo_to_smt x)) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None :=
      smtx_typeof_at_purify_arg_non_none hBody
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed (ih hxNN)
  case seq_empty =>
    rcases native_eo_to_smt_uop_indices_safe_of_seq_empty_non_none h with
      ⟨hxClosed, hxSafe⟩
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed hxSafe
  case _at_strings_stoi_non_digit =>
    have hxClosed :
        native_eo_to_smt_closed x = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hBody :
        __smtx_typeof
            (SmtTerm.str_indexof_re (__eo_to_smt x)
              (SmtTerm.re_comp
                (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
                  (SmtTerm.String (native_string_lit "9"))))
              (SmtTerm.Numeral 0)) ≠ SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hArgs :=
      str_indexof_re_args_of_non_none
        (t1 := __eo_to_smt x)
        (t2 :=
          SmtTerm.re_comp
            (SmtTerm.re_range (SmtTerm.String (native_string_lit "0"))
              (SmtTerm.String (native_string_lit "9"))))
        (t3 := SmtTerm.Numeral 0) hBody
    have hxNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None :=
      smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp)
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed (ih hxNN)
  case set_empty =>
    rcases native_eo_to_smt_uop_indices_safe_of_set_empty_non_none h with
      ⟨hxClosed, hxSafe⟩
    exact native_eo_to_smt_uop_indices_safe_uop1_intro hxClosed hxSafe
  all_goals
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem native_eo_to_smt_uop_indices_safe_of_apply_repeat_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.repeat idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.repeat idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases repeat_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.repeat) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_zero_extend_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases zero_extend_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.zero_extend) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_sign_extend_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases sign_extend_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.sign_extend) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_rotate_left_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases rotate_left_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.rotate_left) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_rotate_right_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases rotate_right_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, w, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.rotate_right) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_int_to_bv_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases int_to_bv_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨n, hIdx, hxTy, _hn⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.int_to_bv) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem smt_re_exp_args_of_non_none
    {a x : SmtTerm}
    (h : __smtx_typeof (SmtTerm.re_exp a x) ≠ SmtType.None) :
    ∃ n : native_Int,
      a = SmtTerm.Numeral n ∧ __smtx_typeof x = SmtType.RegLan := by
  rw [typeof_re_exp_eq] at h
  cases a <;> simp [__smtx_typeof_re_exp] at h
  case Numeral n =>
    cases hx : __smtx_typeof x <;> simp [hx] at h
    by_cases hn : native_zleq 0 n = true
    · exact ⟨n, rfl, rfl⟩
    · exfalso
      cases hz : native_zleq 0 n <;> simp [hz] at hn h
      exact h rfl

private theorem native_eo_to_smt_uop_indices_safe_of_apply_re_exp_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x) = true := by
  change __smtx_typeof
      (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases smt_re_exp_args_of_non_none h with ⟨n, hIdx, hxTy⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1.re_exp) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_apply_at_bit_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x) = true := by
  change
    __smtx_typeof
        (SmtTerm.eq
          (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
            (__eo_to_smt x))
          (SmtTerm.Binary 1 1)) ≠
      SmtType.None at h
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x)))
          (__smtx_typeof (SmtTerm.Binary 1 1)) ≠
        SmtType.None := by
    simpa [typeof_eq_eq] using h
  have hEqArgs := smtx_typeof_eq_non_none hEqNN
  have hExtNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
          (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hEqArgs.2
  rcases extract_args_of_non_none hExtNN with
    ⟨i, _j, w, hIdx, _hIdx', hxTy, _hj0, _hji, _hiw⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
      (op := UserOp1._at_bit) hIdx)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_guarded_uop1_apply_non_none
    {op : UserOp1} {idx x : Term} {body : SmtTerm}
    (ihIdx :
      __smtx_typeof (__eo_to_smt idx) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe idx = true)
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (hBodyArgs :
      __smtx_typeof body ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt idx) ≠ SmtType.None ∧
          __smtx_typeof (__eo_to_smt x) ≠ SmtType.None)
    (h :
      __smtx_typeof (native_eo_to_smt_guard_closed idx body) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 op idx) x) = true := by
  have hIdxClosed :
      native_eo_to_smt_closed idx = true :=
    native_eo_to_smt_closed_of_guard_type_non_none h
  have hBody :
      __smtx_typeof body ≠ SmtType.None :=
    guard_body_type_non_none_of_guard_type_non_none h
  rcases hBodyArgs hBody with ⟨hIdxNN, hxNN⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop1_intro
      hIdxClosed (ihIdx hIdxNN))
    (ihx hxNN)

private theorem native_eo_to_smt_strings_stoi_result_args_non_none
    {idx x : Term}
    (h :
      __smtx_typeof
          (SmtTerm.str_to_int
            (SmtTerm.str_substr (__eo_to_smt idx) (SmtTerm.Numeral 0)
              (__eo_to_smt x))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt idx) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  let sub :=
    SmtTerm.str_substr (__eo_to_smt idx) (SmtTerm.Numeral 0)
      (__eo_to_smt x)
  have hSubSeq :
      __smtx_typeof sub = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
      (typeof_str_to_int_eq sub) (by
        unfold term_has_non_none_type
        simpa [sub] using h)
  have hSubNN : term_has_non_none_type sub := by
    unfold term_has_non_none_type
    rw [hSubSeq]
    simp
  rcases str_substr_args_of_non_none hSubNN with
    ⟨T, hIdxSeq, _hStart, hxInt⟩
  exact
    ⟨smt_typeof_non_none_of_eq_non_none hIdxSeq (by simp),
      smt_typeof_non_none_of_eq_non_none hxInt (by simp)⟩

private theorem native_eo_to_smt_strings_itos_result_args_non_none
    {idx x : Term}
    (h :
      __smtx_typeof
          (SmtTerm.mod (__eo_to_smt idx)
            (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt idx) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  have hModNN :
      term_has_non_none_type
        (SmtTerm.mod (__eo_to_smt idx)
          (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x))) := by
    unfold term_has_non_none_type
    exact h
  have hArgs :=
    int_binop_args_of_non_none (op := SmtTerm.mod) (R := SmtType.Int)
      (typeof_mod_eq (__eo_to_smt idx)
        (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x)))
      hModNN
  have hMulNN :
      term_has_non_none_type
        (SmtTerm.multmult (SmtTerm.Numeral 10) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hArgs.2]
    simp
  have hMulArgs :=
    int_binop_args_of_non_none (op := SmtTerm.multmult) (R := SmtType.Int)
      (typeof_multmult_eq (SmtTerm.Numeral 10) (__eo_to_smt x))
      hMulNN
  exact
    ⟨smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp),
      smt_typeof_non_none_of_eq_non_none hMulArgs.2 (by simp)⟩

private theorem native_eo_to_smt_uop_indices_safe_of_apply_is_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.is idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.is idx) x) = true := by
  change
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt_tester (__eo_to_smt idx))
          (__eo_to_smt x)) ≠
      SmtType.None at h
  cases hIdx : __eo_to_smt idx
  case DtCons s d i =>
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt x)) := by
      unfold term_has_non_none_type
      simpa [__eo_to_smt_tester, hIdx] using h
    have hxTy :
        __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s d :=
      dt_tester_arg_datatype_of_non_none hApplyNN
    exact native_eo_to_smt_uop_indices_safe_apply_intro
      (native_eo_to_smt_uop_indices_safe_uop1_intro
        (native_eo_to_smt_closed_of_dt_cons_translation hIdx)
        (native_eo_to_smt_uop_indices_safe_of_dt_cons_translation hIdx))
      (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_tester, hIdx, typeof_apply_none_eq]

private theorem native_eo_to_smt_uop_indices_safe_of_apply_tuple_select_non_none
    {idx x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) = true := by
  change
    __smtx_typeof
        (__eo_to_smt_tuple_select (__smtx_typeof (__eo_to_smt x))
          (__eo_to_smt idx) (__eo_to_smt x)) ≠
      SmtType.None at h
  cases hxTy : __smtx_typeof (__eo_to_smt x)
  case Datatype s d =>
    cases hIdx : __eo_to_smt idx
    case Numeral n =>
      by_cases hGuard :
          native_and (native_streq s (native_string_lit "@Tuple"))
              (native_zleq 0 n) =
            true
      · exact native_eo_to_smt_uop_indices_safe_apply_intro
          (native_eo_to_smt_uop_indices_safe_uop1_of_smt_numeral
            (op := UserOp1.tuple_select) hIdx)
          (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))
      · exfalso
        apply h
        simp [__eo_to_smt_tuple_select, hxTy, hIdx, native_ite, hGuard]
    all_goals
      exfalso
      apply h
      simp [__eo_to_smt_tuple_select, hxTy, hIdx,
        TranslationProofs.smtx_typeof_none]
  all_goals
    exfalso
    apply h
    simp [__eo_to_smt_tuple_select, hxTy,
      TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_uop_indices_safe_of_guarded_uop2_non_none
    {op : UserOp2} {x y : Term} {body : SmtTerm}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (hBodyArgs :
      __smtx_typeof body ≠ SmtType.None ->
        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
          __smtx_typeof (__eo_to_smt y) ≠ SmtType.None)
    (h :
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y body)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.UOp2 op x y) = true := by
  have hxClosed :
      native_eo_to_smt_closed x = true :=
    native_eo_to_smt_closed_of_guard_type_non_none h
  have hInner :
      __smtx_typeof (native_eo_to_smt_guard_closed y body) ≠
        SmtType.None :=
    guard_body_type_non_none_of_guard_type_non_none h
  have hyClosed :
      native_eo_to_smt_closed y = true :=
    native_eo_to_smt_closed_of_guard_type_non_none hInner
  have hBody :
      __smtx_typeof body ≠ SmtType.None :=
    guard_body_type_non_none_of_guard_type_non_none hInner
  rcases hBodyArgs hBody with ⟨hxNN, hyNN⟩
  exact native_eo_to_smt_uop_indices_safe_uop2_intro
    hxClosed hyClosed (ihx hxNN) (ihy hyNN)

private theorem native_eo_to_smt_array_deq_diff_args_non_none
    {x y : Term}
    (h :
      __smtx_typeof
          (__eo_to_smt_array_deq_diff (__eo_to_smt x)
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
            (__smtx_typeof (__eo_to_smt y))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
  constructor
  · intro hxNone
    apply h
    simp [__eo_to_smt_array_deq_diff, hxNone,
      TranslationProofs.smtx_typeof_none]
  · intro hyNone
    apply h
    cases hx : __smtx_typeof (__eo_to_smt x) <;>
      simp [__eo_to_smt_array_deq_diff, hyNone,
        TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_sets_deq_diff_args_non_none
    {x y : Term}
    (h :
      __smtx_typeof
          (__eo_to_smt_sets_deq_diff (__eo_to_smt x)
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
            (__smtx_typeof (__eo_to_smt y))) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
  constructor
  · intro hxNone
    apply h
    simp [__eo_to_smt_sets_deq_diff, hxNone,
      TranslationProofs.smtx_typeof_none]
  · intro hyNone
    apply h
    cases hx : __smtx_typeof (__eo_to_smt x) <;>
      simp [__eo_to_smt_sets_deq_diff, hyNone,
        TranslationProofs.smtx_typeof_none]

private theorem native_eo_to_smt_strings_deq_diff_args_non_none
    {x y : Term}
    (h :
      __smtx_typeof
          (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int
            (SmtTerm.not
              (SmtTerm.eq
                (SmtTerm.str_substr (__eo_to_smt x)
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1))
                (SmtTerm.str_substr (__eo_to_smt y)
                  (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                  (SmtTerm.Numeral 1))))
            native_nat_zero) ≠
        SmtType.None) :
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ∧
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
  let one := SmtTerm.Numeral 1
  let idx := SmtTerm.Var (native_string_lit "@x") SmtType.Int
  let xSub := SmtTerm.str_substr (__eo_to_smt x) idx one
  let ySub := SmtTerm.str_substr (__eo_to_smt y) idx one
  let body := SmtTerm.not (SmtTerm.eq xSub ySub)
  have hChoiceNN :
      term_has_non_none_type
        (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int body 0) := by
    unfold term_has_non_none_type
    simpa [one, idx, xSub, ySub, body] using h
  have hBodyBool : __smtx_typeof body = SmtType.Bool :=
    choice_nth_body_bool_of_non_none hChoiceNN
  have hEqBool : __smtx_typeof (SmtTerm.eq xSub ySub) = SmtType.Bool :=
    smtx_typeof_not_arg_bool _ hBodyBool
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof xSub) (__smtx_typeof ySub) ≠
        SmtType.None := by
    intro hNone
    rw [typeof_eq_eq xSub ySub] at hEqBool
    rw [hNone] at hEqBool
    cases hEqBool
  have hEqArgs := smtx_typeof_eq_non_none hEqNN
  have hXSubNN : term_has_non_none_type xSub := by
    unfold term_has_non_none_type
    exact hEqArgs.2
  have hYSubNN : term_has_non_none_type ySub := by
    unfold term_has_non_none_type
    intro hNone
    exact hEqArgs.2 (by rw [hEqArgs.1, hNone])
  rcases str_substr_args_of_non_none hXSubNN with
    ⟨A, hXSeq, _hIdxX, _hOneX⟩
  rcases str_substr_args_of_non_none hYSubNN with
    ⟨B, hYSeq, _hIdxY, _hOneY⟩
  exact
    ⟨smt_typeof_non_none_of_eq_non_none hXSeq (by simp),
      smt_typeof_non_none_of_eq_non_none hYSeq (by simp)⟩

private theorem native_eo_to_smt_uop_indices_safe_of_skolemize_forall_non_none
    {xs F idx : Term}
    (ihForall :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) ≠
        SmtType.None ->
      native_eo_to_smt_uop_indices_safe
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) = true)
    (h :
      __smtx_typeof
          (__eo_to_smt
            (Term.UOp2 UserOp2._at_quantifiers_skolemize
              (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)
              idx)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) idx) =
      true := by
  change
    __smtx_typeof
        (native_eo_to_smt_guard_closed
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_quantifiers_skolemize
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))
              (__eo_to_smt_nat idx))
            SmtTerm.None)) ≠
      SmtType.None at h
  have hForallClosed :
      native_eo_to_smt_closed
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F) =
        true :=
    native_eo_to_smt_closed_of_guard_type_non_none h
  have hGuardBody :
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_quantifiers_skolemize
              (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))
              (__eo_to_smt_nat idx))
            SmtTerm.None) ≠
        SmtType.None :=
    guard_body_type_non_none_of_guard_type_non_none h
  have hIdxValid : __eo_to_smt_nat_is_valid idx = true := by
    cases hIdx : __eo_to_smt_nat_is_valid idx
    · exfalso
      apply hGuardBody
      simp [native_ite, hIdx, TranslationProofs.smtx_typeof_none]
    · rfl
  have hSkolNN :
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize
            (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F)))
            (__eo_to_smt_nat idx)) ≠
        SmtType.None := by
    simpa [native_ite, hIdxValid] using hGuardBody
  have hBodyNoExists :
      ∀ s T body, SmtTerm.not (__eo_to_smt F) ≠ SmtTerm.exists s T body := by
    intro s T body hEq
    cases hEq
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists xs (SmtTerm.not (__eo_to_smt F))) =
        SmtType.Bool :=
    smtx_typeof_eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
      xs (SmtTerm.not (__eo_to_smt F)) (__eo_to_smt_nat idx)
      hBodyNoExists hSkolNN
  have hForallNN :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F)) ≠
        SmtType.None := by
    cases xs
    case __eo_List_nil =>
      exfalso
      apply hSkolNN
      simp [__eo_to_smt_exists, __eo_to_smt_quantifiers_skolemize,
        TranslationProofs.smtx_typeof_none]
    all_goals
      change
        __smtx_typeof
            (SmtTerm.not
              (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt F)))) ≠
          SmtType.None
      rw [typeof_not_eq, hExistsBool]
      simp [native_Teq, native_ite]
  exact native_eo_to_smt_uop_indices_safe_uop2_intro
    hForallClosed
    (native_eo_to_smt_closed_of_nat_valid hIdxValid)
    (ihForall hForallNN)
    (native_eo_to_smt_uop_indices_safe_of_nat_valid hIdxValid)

private theorem native_eo_to_smt_uop_indices_safe_of_uop2_non_none
    {op : UserOp2} {x y : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (h : __smtx_typeof (__eo_to_smt (Term.UOp2 op x y)) ≠ SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.UOp2 op x y) = true := by
  cases op
  case _at_array_deq_diff =>
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y
              (__eo_to_smt_array_deq_diff (__eo_to_smt x)
                (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                (__smtx_typeof (__eo_to_smt y))))) ≠
        SmtType.None at h
    exact native_eo_to_smt_uop_indices_safe_of_guarded_uop2_non_none
      (op := UserOp2._at_array_deq_diff) ihx ihy
      native_eo_to_smt_array_deq_diff_args_non_none h
  case _at_bv =>
    rcases eo_to_smt_at_bv_of_non_none
        (a := __eo_to_smt x) (b := __eo_to_smt y) (by simpa using h) with
      ⟨n, w, hxNum, hyNum, _hw, _hTy⟩
    exact native_eo_to_smt_uop_indices_safe_uop2_intro
      (native_eo_to_smt_closed_of_smt_numeral hxNum)
      (native_eo_to_smt_closed_of_smt_numeral hyNum)
      (native_eo_to_smt_uop_indices_safe_of_smt_numeral hxNum)
      (native_eo_to_smt_uop_indices_safe_of_smt_numeral hyNum)
  case _at_strings_deq_diff =>
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y
              (SmtTerm.choice_nth (native_string_lit "@x") SmtType.Int
                (SmtTerm.not
                  (SmtTerm.eq
                    (SmtTerm.str_substr (__eo_to_smt x)
                      (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                      (SmtTerm.Numeral 1))
                    (SmtTerm.str_substr (__eo_to_smt y)
                      (SmtTerm.Var (native_string_lit "@x") SmtType.Int)
                      (SmtTerm.Numeral 1))))
                native_nat_zero))) ≠
        SmtType.None at h
    exact native_eo_to_smt_uop_indices_safe_of_guarded_uop2_non_none
      (op := UserOp2._at_strings_deq_diff) ihx ihy
      native_eo_to_smt_strings_deq_diff_args_non_none h
  case _at_sets_deq_diff =>
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y
              (__eo_to_smt_sets_deq_diff (__eo_to_smt x)
                (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt y)
                (__smtx_typeof (__eo_to_smt y))))) ≠
        SmtType.None at h
    exact native_eo_to_smt_uop_indices_safe_of_guarded_uop2_non_none
      (op := UserOp2._at_sets_deq_diff) ihx ihy
      native_eo_to_smt_sets_deq_diff_args_non_none h
  case _at_quantifiers_skolemize =>
    cases x
    case Apply f F =>
      cases f
      case Apply q xs =>
        cases q
        case UOp op =>
          cases op
          case «forall» =>
            exact
              native_eo_to_smt_uop_indices_safe_of_skolemize_forall_non_none
                (xs := xs) (F := F) (idx := y) ihx h
          all_goals
            exfalso
            apply h
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none
        all_goals
          exfalso
          apply h
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      all_goals
        exfalso
        apply h
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    all_goals
      exfalso
      apply h
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case extract =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case re_loop =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case _at_strings_num_occur_re =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case _at_strings_occur_index_re =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case _at_const =>
    exfalso
    apply h
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem native_eo_to_smt_uop_indices_safe_of_apply_extract_non_none
    {hi lo x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) = true := by
  change __smtx_typeof
      (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases extract_args_of_non_none (by
      unfold term_has_non_none_type
      exact h) with
    ⟨i, j, w, hHi, hLo, hxTy, _hj0, _hji, _hiw⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop2_of_smt_numerals
      (op := UserOp2.extract) hHi hLo)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem smt_re_loop_args_of_non_none
    {a b x : SmtTerm}
    (h : __smtx_typeof (SmtTerm.re_loop a b x) ≠ SmtType.None) :
    ∃ i j : native_Int,
      a = SmtTerm.Numeral i ∧ b = SmtTerm.Numeral j ∧
        __smtx_typeof x = SmtType.RegLan := by
  cases a
  case Numeral aN =>
    cases b
    case Numeral bN =>
      have hTerm :
          term_has_non_none_type
            (SmtTerm.re_loop (SmtTerm.Numeral aN) (SmtTerm.Numeral bN) x) := by
        unfold term_has_non_none_type
        exact h
      exact ⟨aN, bN, rfl, rfl, (re_loop_arg_of_non_none hTerm).2.2⟩
    all_goals
      exfalso
      apply h
      rw [typeof_re_loop_eq]
      simp [__smtx_typeof_re_loop]
  all_goals
    exfalso
    apply h
    rw [typeof_re_loop_eq]
    simp [__smtx_typeof_re_loop]

private theorem native_eo_to_smt_uop_indices_safe_of_apply_re_loop_non_none
    {lo hi x : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (h :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x)) ≠
        SmtType.None) :
    native_eo_to_smt_uop_indices_safe
      (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) = true := by
  change __smtx_typeof
      (SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi) (__eo_to_smt x)) ≠
    SmtType.None at h
  rcases smt_re_loop_args_of_non_none h with
    ⟨i, j, hLo, hHi, hxTy⟩
  exact native_eo_to_smt_uop_indices_safe_apply_intro
    (native_eo_to_smt_uop_indices_safe_uop2_of_smt_numerals
      (op := UserOp2.re_loop) hLo hHi)
    (ihx (smt_typeof_non_none_of_eq_non_none hxTy (by simp)))

private theorem native_eo_to_smt_uop_indices_safe_of_uop3_non_none
    {op : UserOp3} {x y z : Term}
    (ihx :
      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe x = true)
    (ihy :
      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe y = true)
    (ihz :
      __smtx_typeof (__eo_to_smt z) ≠ SmtType.None ->
        native_eo_to_smt_uop_indices_safe z = true)
    (h : __smtx_typeof (__eo_to_smt (Term.UOp3 op x y z)) ≠ SmtType.None) :
    native_eo_to_smt_uop_indices_safe (Term.UOp3 op x y z) = true := by
  cases op
  case _at_re_unfold_pos_component =>
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed x
            (native_eo_to_smt_guard_closed y
              (native_ite (__eo_to_smt_nat_is_valid z)
                (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
                  (__eo_to_smt y) (__eo_to_smt_nat z))
                SmtTerm.None))) ≠
        SmtType.None at h
    have hxClosed :
        native_eo_to_smt_closed x = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hInner :
        __smtx_typeof
            (native_eo_to_smt_guard_closed y
              (native_ite (__eo_to_smt_nat_is_valid z)
                (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
                  (__eo_to_smt y) (__eo_to_smt_nat z))
                SmtTerm.None)) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hyClosed :
        native_eo_to_smt_closed y = true :=
      native_eo_to_smt_closed_of_guard_type_non_none hInner
    have hBody :
        __smtx_typeof
            (native_ite (__eo_to_smt_nat_is_valid z)
              (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
                (__eo_to_smt y) (__eo_to_smt_nat z))
              SmtTerm.None) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none hInner
    have hzValid : __eo_to_smt_nat_is_valid z = true := by
      cases hz : __eo_to_smt_nat_is_valid z
      · exfalso
        apply hBody
        simp [native_ite, hz, TranslationProofs.smtx_typeof_none]
      · rfl
    have hReNN :
        term_has_non_none_type
          (__eo_to_smt_re_unfold_pos_component (__eo_to_smt x)
            (__eo_to_smt y) (__eo_to_smt_nat z)) := by
      unfold term_has_non_none_type
      simpa [native_ite, hzValid] using hBody
    have hArgs :=
      smtx_typeof_re_unfold_pos_component_args_of_non_none
        (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt_nat z) hReNN
    exact native_eo_to_smt_uop_indices_safe_uop3_intro
      hxClosed hyClosed (native_eo_to_smt_closed_of_nat_valid hzValid)
      (ihx (smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp)))
      (ihy (smt_typeof_non_none_of_eq_non_none hArgs.2 (by simp)))
      (native_eo_to_smt_uop_indices_safe_of_nat_valid hzValid)
  case _at_witness_string_length =>
    let ST := __eo_to_smt_type x
    let body :=
      SmtTerm.eq
        (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") ST))
        (__eo_to_smt y)
    change
      __smtx_typeof
          (native_eo_to_smt_guard_closed y
            (native_eo_to_smt_guard_closed z
              (native_ite (native_Teq (__smtx_typeof (__eo_to_smt z)) SmtType.Int)
                (SmtTerm.choice_nth (native_string_lit "@x") ST body native_nat_zero)
                SmtTerm.None))) ≠
        SmtType.None at h
    have hyClosed :
        native_eo_to_smt_closed y = true :=
      native_eo_to_smt_closed_of_guard_type_non_none h
    have hInner :
        __smtx_typeof
            (native_eo_to_smt_guard_closed z
              (native_ite (native_Teq (__smtx_typeof (__eo_to_smt z)) SmtType.Int)
                (SmtTerm.choice_nth (native_string_lit "@x") ST body native_nat_zero)
                SmtTerm.None)) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none h
    have hzClosed :
        native_eo_to_smt_closed z = true :=
      native_eo_to_smt_closed_of_guard_type_non_none hInner
    have hBody :
        __smtx_typeof
            (native_ite (native_Teq (__smtx_typeof (__eo_to_smt z)) SmtType.Int)
              (SmtTerm.choice_nth (native_string_lit "@x") ST body native_nat_zero)
              SmtTerm.None) ≠
          SmtType.None :=
      guard_body_type_non_none_of_guard_type_non_none hInner
    have hzInt : __smtx_typeof (__eo_to_smt z) = SmtType.Int := by
      cases hTest : native_Teq (__smtx_typeof (__eo_to_smt z)) SmtType.Int
      · exfalso
        apply hBody
        simp [native_ite, hTest, TranslationProofs.smtx_typeof_none]
      · simpa [native_Teq] using hTest
    have hChoiceNN :
        term_has_non_none_type
          (SmtTerm.choice_nth (native_string_lit "@x") ST body 0) := by
      unfold term_has_non_none_type
      simpa [native_ite, hzInt, native_Teq] using hBody
    have hBodyBool : __smtx_typeof body = SmtType.Bool :=
      choice_nth_body_bool_of_non_none hChoiceNN
    have hEqNN :
        __smtx_typeof_eq
            (__smtx_typeof
              (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") ST)))
            (__smtx_typeof (__eo_to_smt y)) ≠
          SmtType.None := by
      have hBodyNN : __smtx_typeof body ≠ SmtType.None := by
        rw [hBodyBool]
        simp
      simpa [body, typeof_eq_eq] using hBodyNN
    have hEqArgs := smtx_typeof_eq_non_none hEqNN
    have hyNN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
      intro hyNone
      exact hEqArgs.2 (by rw [hEqArgs.1, hyNone])
    have hChoiceGuard :
        __smtx_typeof (SmtTerm.choice_nth (native_string_lit "@x") ST body 0) =
          __smtx_typeof_guard_wf ST ST :=
      choice_term_guard_type_of_non_none hChoiceNN
    have hGuardNN : __smtx_typeof_guard_wf ST ST ≠ SmtType.None := by
      intro hNone
      unfold term_has_non_none_type at hChoiceNN
      exact hChoiceNN (by rw [hChoiceGuard, hNone])
    have hTWF : __smtx_type_wf (__eo_to_smt_type x) = true := by
      simpa [ST] using smtx_typeof_guard_wf_wf_of_non_none ST ST hGuardNN
    rcases native_eo_to_smt_uop_indices_safe_of_smt_type_wf
        (T := x) hTWF with
      ⟨hxClosed, hxSafe⟩
    exact native_eo_to_smt_uop_indices_safe_uop3_intro
      hxClosed hyClosed hzClosed hxSafe (ihy hyNN)
      (ihz (smt_typeof_non_none_of_eq_non_none hzInt (by simp)))

/--
If a term translates to a well-typed SMT term, then every indexed EO operator
occurrence in it has standalone-closed immediate indices.

The guarded branches in `__eo_to_smt` should discharge the opaque term-index
cases; the numeric-index branches are intended to be discharged from the SMT
typing rules that require their indices to translate to `SmtTerm.Numeral`.
-/
theorem eo_to_smt_well_typed_implies_uop_indices_safe
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    NativeEoToSmtUOpIndicesSafe t := by
  let rec go : (u : Term) ->
      __smtx_typeof (__eo_to_smt u) ≠ SmtType.None ->
      NativeEoToSmtUOpIndicesSafe u
    | u, h => by
        cases u <;>
          simp [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] at h ⊢
        case UOp1 op x =>
          simpa [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] using
            native_eo_to_smt_uop_indices_safe_of_uop1_non_none
              (x := x) (op := op) (fun hx => go x hx) h
        case UOp2 op x y =>
          simpa [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] using
            native_eo_to_smt_uop_indices_safe_of_uop2_non_none
              (x := x) (y := y) (op := op)
              (fun hx => go x hx) (fun hy => go y hy) h
        case UOp3 op x y z =>
          simpa [NativeEoToSmtUOpIndicesSafe,
            native_eo_to_smt_uop_indices_safe] using
            native_eo_to_smt_uop_indices_safe_of_uop3_non_none
              (x := x) (y := y) (z := z) (op := op)
              (fun hx => go x hx) (fun hy => go y hy)
              (fun hz => go z hz) h
        case Apply f x =>
          by_cases hfDistinct : f = Term.UOp UserOp.distinct
          · subst f
            simpa [NativeEoToSmtUOpIndicesSafe,
              native_eo_to_smt_uop_indices_safe] using
              native_eo_to_smt_uop_indices_safe_of_apply_distinct_non_none
                (xs := x) (Term.Apply (Term.UOp UserOp.distinct) x)
                (fun y _hyLt hy => go y hy) (by simp) h
          by_cases hfExists :
              ∃ xs, f = Term.Apply (Term.UOp UserOp.exists) xs
          · rcases hfExists with ⟨xs, rfl⟩
            simpa [NativeEoToSmtUOpIndicesSafe,
              native_eo_to_smt_uop_indices_safe] using
              native_eo_to_smt_uop_indices_safe_of_apply_exists_non_none
                (xs := xs) (F := x)
                (Term.Apply (Term.Apply (Term.UOp UserOp.exists) xs) x)
                (fun y _hyLt hy => go y hy) (by simp; omega)
                (by simp; omega) h
          by_cases hfForall :
              ∃ xs, f = Term.Apply (Term.UOp UserOp.forall) xs
          · rcases hfForall with ⟨xs, rfl⟩
            simpa [NativeEoToSmtUOpIndicesSafe,
              native_eo_to_smt_uop_indices_safe] using
              native_eo_to_smt_uop_indices_safe_of_apply_forall_non_none
                (xs := xs) (F := x)
                (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) x)
                (fun y _hyLt hy => go y hy) (by simp; omega)
                (by simp; omega) h
          have generic :
              ∀ f0 : Term,
                native_eo_to_smt_uop_indices_safe f0 = true ->
                __eo_to_smt (Term.Apply f0 x) =
                    SmtTerm.Apply (__eo_to_smt f0) (__eo_to_smt x) ->
                  __smtx_typeof (__eo_to_smt (Term.Apply f0 x)) ≠
                      SmtType.None ->
                    NativeEoToSmtUOpIndicesSafe (Term.Apply f0 x) := by
            intro f0 hfSafe hTranslate h0
            simpa [NativeEoToSmtUOpIndicesSafe] using
              native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                (f := f0) (x := x)
                (fun _hf => hfSafe)
                (fun hx => by
                  simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                hTranslate h0
          have directUOpBody :
              ∀ (op0 : UserOp) (body : SmtTerm),
                (__smtx_typeof body ≠ SmtType.None ->
                  __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) ->
                __eo_to_smt (Term.Apply (Term.UOp op0) x) = body ->
                __smtx_typeof
                    (__eo_to_smt (Term.Apply (Term.UOp op0) x)) ≠
                  SmtType.None ->
                NativeEoToSmtUOpIndicesSafe
                  (Term.Apply (Term.UOp op0) x) := by
            intro op0 body hBodyArgs hTranslate h0
            simpa [NativeEoToSmtUOpIndicesSafe] using
              native_eo_to_smt_uop_indices_safe_of_apply_uop_body_non_none
                (op := op0) (x := x)
                (fun hx => by
                  simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                hBodyArgs hTranslate h0
          cases f with
          | UOp1 op idx =>
            cases op with
            | «repeat» =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_repeat_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | zero_extend =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_zero_extend_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | sign_extend =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_sign_extend_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | rotate_left =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_rotate_left_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | rotate_right =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_rotate_right_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | _at_bit =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_at_bit_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | re_exp =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_re_exp_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | _at_strings_stoi_result =>
              change
                __smtx_typeof
                    (native_eo_to_smt_guard_closed idx
                      (SmtTerm.str_to_int
                        (SmtTerm.str_substr (__eo_to_smt idx)
                          (SmtTerm.Numeral 0) (__eo_to_smt x)))) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_guarded_uop1_apply_non_none
                  (op := UserOp1._at_strings_stoi_result)
                  (idx := idx) (x := x)
                  (body :=
                    SmtTerm.str_to_int
                      (SmtTerm.str_substr (__eo_to_smt idx)
                        (SmtTerm.Numeral 0) (__eo_to_smt x)))
                  (fun hidx => go idx hidx) (fun hx => go x hx)
                  native_eo_to_smt_strings_stoi_result_args_non_none h
            | _at_strings_itos_result =>
              change
                __smtx_typeof
                    (native_eo_to_smt_guard_closed idx
                      (SmtTerm.mod (__eo_to_smt idx)
                        (SmtTerm.multmult (SmtTerm.Numeral 10)
                          (__eo_to_smt x)))) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_guarded_uop1_apply_non_none
                  (op := UserOp1._at_strings_itos_result)
                  (idx := idx) (x := x)
                  (body :=
                    SmtTerm.mod (__eo_to_smt idx)
                      (SmtTerm.multmult (SmtTerm.Numeral 10)
                        (__eo_to_smt x)))
                  (fun hidx => go idx hidx) (fun hx => go x hx)
                  native_eo_to_smt_strings_itos_result_args_non_none h
            | int_to_bv =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_int_to_bv_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | _at_purify =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1._at_purify idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1._at_purify idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1._at_purify idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | seq_empty =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1.seq_empty idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1.seq_empty idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1.seq_empty idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | _at_strings_stoi_non_digit =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt
                        (Term.UOp1 UserOp1._at_strings_stoi_non_digit idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1._at_strings_stoi_non_digit idx)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1._at_strings_stoi_non_digit idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | _at_strings_replace_all_result =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt
                        (Term.UOp1 UserOp1._at_strings_replace_all_result idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1._at_strings_replace_all_result idx)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1._at_strings_replace_all_result idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | is =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_is_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | update =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1.update idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1.update idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1.update idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | tuple_select =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_tuple_select_non_none
                  (idx := idx) (x := x) (fun hx => go x hx) h
            | tuple_update =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1.tuple_update idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1.tuple_update idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1.tuple_update idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
            | set_empty =>
              change
                __smtx_typeof
                    (SmtTerm.Apply
                      (__eo_to_smt (Term.UOp1 UserOp1.set_empty idx))
                      (__eo_to_smt x)) ≠
                  SmtType.None at h
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_generic_apply_non_none
                  (f := Term.UOp1 UserOp1.set_empty idx) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp1 UserOp1.set_empty idx) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  h
          | UOp2 op idx1 idx2 =>
            cases op with
            | extract =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_extract_non_none
                  (hi := idx1) (lo := idx2) (x := x)
                  (fun hx => go x hx) h
            | re_loop =>
              simpa [NativeEoToSmtUOpIndicesSafe,
                native_eo_to_smt_uop_indices_safe] using
                native_eo_to_smt_uop_indices_safe_of_apply_re_loop_non_none
                  (lo := idx1) (hi := idx2) (x := x)
                  (fun hx => go x hx) h
            | _at_array_deq_diff =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_array_deq_diff idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_array_deq_diff idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_bv =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_bv idx1 idx2) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_bv idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_strings_deq_diff =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_strings_deq_diff idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_strings_deq_diff idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_strings_num_occur_re =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_strings_num_occur_re idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_strings_num_occur_re idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_strings_occur_index_re =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_strings_occur_index_re idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_strings_occur_index_re idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_sets_deq_diff =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_sets_deq_diff idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_sets_deq_diff idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_quantifiers_skolemize =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_quantifiers_skolemize idx1 idx2)
                  (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_quantifiers_skolemize idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
            | _at_const =>
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.UOp2 UserOp2._at_const idx1 idx2) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.UOp2 UserOp2._at_const idx1 idx2) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  (by rfl) h
          | UOp3 op idx1 idx2 idx3 =>
            simpa [NativeEoToSmtUOpIndicesSafe] using
              native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                (f := Term.UOp3 op idx1 idx2 idx3) (x := x)
                (fun hf => by
                  simpa [NativeEoToSmtUOpIndicesSafe] using
                    go (Term.UOp3 op idx1 idx2 idx3) hf)
                (fun hx => by
                  simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                (by rfl) h
          | UOp op =>
            by_cases hopDistinct : op = UserOp.distinct
            · subst op
              exact False.elim (hfDistinct rfl)
            cases op
            all_goals
              first
              | exact False.elim (hopDistinct rfl)
              | exact generic _ (by simp [native_eo_to_smt_uop_indices_safe])
                  (by rfl) h
              | exact directUOpBody UserOp.not
                  (SmtTerm.not (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (smtx_typeof_not_arg_bool_of_non_none hBody) (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.to_real
                  (SmtTerm.to_real (__eo_to_smt x))
                  (fun hBody => by
                    rcases to_real_arg_of_non_none (t := __eo_to_smt x) (by
                        unfold term_has_non_none_type
                        exact hBody) with hArg | hArg
                    · exact smt_typeof_non_none_of_eq_non_none hArg (by simp)
                    · exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.to_int
                  (SmtTerm.to_int (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (real_arg_of_non_none (op := SmtTerm.to_int)
                        (typeof_to_int_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.is_int
                  (SmtTerm.is_int (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (real_arg_of_non_none (op := SmtTerm.is_int)
                        (typeof_is_int_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.abs
                  (SmtTerm.abs (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (int_arg_of_non_none (t := __eo_to_smt x) (by
                        unfold term_has_non_none_type
                        exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.__eoo_neg_2
                  (SmtTerm.uneg (__eo_to_smt x))
                  (fun hBody => by
                    rcases arith_unop_arg_of_non_none (op := SmtTerm.uneg)
                        (typeof_uneg_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody) with hArg | hArg
                    · exact smt_typeof_non_none_of_eq_non_none hArg (by simp)
                    · exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.int_pow2
                  (SmtTerm.int_pow2 (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (int_ret_arg_of_non_none (op := SmtTerm.int_pow2)
                        (typeof_int_pow2_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.int_log2
                  (SmtTerm.int_log2 (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (int_ret_arg_of_non_none (op := SmtTerm.int_log2)
                        (typeof_int_log2_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp._at_int_div_by_zero
                  (SmtTerm.div (__eo_to_smt x) (SmtTerm.Numeral 0))
                  (fun hBody => by
                    have hArgs := int_binop_args_of_non_none
                      (op := SmtTerm.div) (R := SmtType.Int)
                      (typeof_div_eq (__eo_to_smt x) (SmtTerm.Numeral 0))
                      (by
                        unfold term_has_non_none_type
                        exact hBody)
                    exact smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp._at_mod_by_zero
                  (SmtTerm.mod (__eo_to_smt x) (SmtTerm.Numeral 0))
                  (fun hBody => by
                    have hArgs := int_binop_args_of_non_none
                      (op := SmtTerm.mod) (R := SmtType.Int)
                      (typeof_mod_eq (__eo_to_smt x) (SmtTerm.Numeral 0))
                      (by
                        unfold term_has_non_none_type
                        exact hBody)
                    exact smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.bvnot
                  (SmtTerm.bvnot (__eo_to_smt x))
                  (fun hBody => by
                    rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
                        (by simp [__smtx_typeof]) (by
                          unfold term_has_non_none_type
                          exact hBody) with ⟨w, hArg⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.bvneg
                  (SmtTerm.bvneg (__eo_to_smt x))
                  (fun hBody => by
                    rcases bv_unop_arg_of_non_none (op := SmtTerm.bvneg)
                        (by simp [__smtx_typeof]) (by
                          unfold term_has_non_none_type
                          exact hBody) with ⟨w, hArg⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.bvnego
                  (SmtTerm.bvnego (__eo_to_smt x))
                  (fun hBody => by
                    rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.bvnego)
                        (ret := SmtType.Bool) (by simp [__smtx_typeof]) (by
                          unfold term_has_non_none_type
                          exact hBody) with ⟨w, hArg⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_len
                  (SmtTerm.str_len (__eo_to_smt x))
                  (fun hBody => by
                    rcases seq_arg_of_non_none_ret (op := SmtTerm.str_len)
                        (R := SmtType.Int) (typeof_str_len_eq (__eo_to_smt x))
                        (by
                          unfold term_has_non_none_type
                          exact hBody) with ⟨T, hArg⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_rev
                  (SmtTerm.str_rev (__eo_to_smt x))
                  (fun hBody => by
                    rcases seq_arg_of_non_none (op := SmtTerm.str_rev)
                        (typeof_str_rev_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody) with ⟨T, hArg⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_to_lower
                  (SmtTerm.str_to_lower (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (seq_char_arg_of_non_none (op := SmtTerm.str_to_lower)
                        (typeof_str_to_lower_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_to_upper
                  (SmtTerm.str_to_upper (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (seq_char_arg_of_non_none (op := SmtTerm.str_to_upper)
                        (typeof_str_to_upper_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_to_code
                  (SmtTerm.str_to_code (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (seq_char_arg_of_non_none (op := SmtTerm.str_to_code)
                        (typeof_str_to_code_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_from_code
                  (SmtTerm.str_from_code (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (int_arg_of_non_none_ret (op := SmtTerm.str_from_code)
                        (ret := SmtType.Seq SmtType.Char)
                        (typeof_str_from_code_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_is_digit
                  (SmtTerm.str_is_digit (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (seq_char_arg_of_non_none (op := SmtTerm.str_is_digit)
                        (typeof_str_is_digit_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_to_int
                  (SmtTerm.str_to_int (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (seq_char_arg_of_non_none (op := SmtTerm.str_to_int)
                        (typeof_str_to_int_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_from_int
                  (SmtTerm.str_from_int (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
                        (ret := SmtType.Seq SmtType.Char)
                        (typeof_str_from_int_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.str_to_re
                  (SmtTerm.str_to_re (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (seq_char_arg_of_non_none (op := SmtTerm.str_to_re)
                        (typeof_str_to_re_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.re_mult
                  (SmtTerm.re_mult (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (reglan_arg_of_non_none (op := SmtTerm.re_mult)
                        (typeof_re_mult_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.re_plus
                  (SmtTerm.re_plus (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (reglan_arg_of_non_none (op := SmtTerm.re_plus)
                        (typeof_re_plus_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.re_opt
                  (SmtTerm.re_opt (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (reglan_arg_of_non_none (op := SmtTerm.re_opt)
                        (typeof_re_opt_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.re_comp
                  (SmtTerm.re_comp (__eo_to_smt x))
                  (fun hBody => by
                    exact smt_typeof_non_none_of_eq_non_none
                      (reglan_arg_of_non_none (op := SmtTerm.re_comp)
                        (typeof_re_comp_eq (__eo_to_smt x)) (by
                          unfold term_has_non_none_type
                          exact hBody))
                      (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.seq_unit
                  (SmtTerm.seq_unit (__eo_to_smt x))
                  (fun hBody => by
                    have hWf :=
                      smtx_typeof_guard_wf_wf_of_non_none
                        (SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
                        (SmtType.Seq (__smtx_typeof (__eo_to_smt x)))
                        (by simpa [__smtx_typeof] using hBody)
                    exact type_wf_non_none (seq_type_wf_component_of_wf hWf))
                  (by rfl) h
              | exact directUOpBody UserOp.set_singleton
                  (SmtTerm.set_singleton (__eo_to_smt x))
                  (fun hBody => by
                    have hWf :=
                      smtx_typeof_guard_wf_wf_of_non_none
                        (SmtType.Set (__smtx_typeof (__eo_to_smt x)))
                        (SmtType.Set (__smtx_typeof (__eo_to_smt x)))
                        (by simpa [__smtx_typeof] using hBody)
                    exact type_wf_non_none (set_type_wf_component_of_wf hWf))
                  (by rfl) h
              | exact directUOpBody UserOp._at_div_by_zero
                  (SmtTerm.qdiv (__eo_to_smt x)
                    (SmtTerm.Rational (native_mk_rational 0 1)))
                  (fun hBody => by
                    rcases arith_binop_ret_args_of_non_none
                        (op := SmtTerm.qdiv) (R := SmtType.Real)
                        (typeof_qdiv_eq (__eo_to_smt x)
                          (SmtTerm.Rational (native_mk_rational 0 1)))
                        (by
                          unfold term_has_non_none_type
                          exact hBody) with hArgs | hArgs
                    · exact smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp)
                    · exact smt_typeof_non_none_of_eq_non_none hArgs.1 (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.ubv_to_int
                  (SmtTerm.ubv_to_int (__eo_to_smt x))
                  (fun hBody => by
                    rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.ubv_to_int)
                        (ret := SmtType.Int) (by simp [__smtx_typeof]) (by
                          unfold term_has_non_none_type
                          exact hBody) with ⟨w, hArg⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.sbv_to_int
                  (SmtTerm.sbv_to_int (__eo_to_smt x))
                  (fun hBody => by
                    rcases bv_unop_ret_arg_of_non_none (op := SmtTerm.sbv_to_int)
                        (ret := SmtType.Int) (by simp [__smtx_typeof]) (by
                          unfold term_has_non_none_type
                          exact hBody) with ⟨w, hArg⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.int_ispow2
                  (SmtTerm.and
                    (SmtTerm.geq (__eo_to_smt x) (SmtTerm.Numeral 0))
                    (SmtTerm.eq (__eo_to_smt x)
                      (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt x)))))
                  (fun hBody => by
                    let geqTerm :=
                      SmtTerm.geq (__eo_to_smt x) (SmtTerm.Numeral 0)
                    let eqTerm :=
                      SmtTerm.eq (__eo_to_smt x)
                        (SmtTerm.int_pow2 (SmtTerm.int_log2 (__eo_to_smt x)))
                    have hArgs :
                        __smtx_typeof geqTerm = SmtType.Bool ∧
                          __smtx_typeof eqTerm = SmtType.Bool :=
                      bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                        (typeof_and_eq geqTerm eqTerm) (by
                          unfold term_has_non_none_type
                          simpa [geqTerm, eqTerm] using hBody)
                    have hGeqNN : term_has_non_none_type geqTerm := by
                      unfold term_has_non_none_type
                      rw [hArgs.1]
                      simp
                    have hGeqArgs :=
                      arith_binop_ret_bool_args_of_non_none (op := SmtTerm.geq)
                        (typeof_geq_eq (__eo_to_smt x) (SmtTerm.Numeral 0))
                        hGeqNN
                    rcases hGeqArgs with hInt | hReal
                    · exact smt_typeof_non_none_of_eq_non_none hInt.1 (by simp)
                    · exact smt_typeof_non_none_of_eq_non_none hReal.1 (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp._at_bvsize
                  (let w :=
                    __smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))
                   native_ite (native_zleq 0 w)
                     (SmtTerm._at_purify (SmtTerm.Numeral w))
                     SmtTerm.None)
                  (fun hBody => by
                    rcases smtx_bv_sizeof_term_non_none
                        (__eo_to_smt x) hBody with ⟨w, hArg⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.bvredand
                  (SmtTerm.bvcomp (__eo_to_smt x)
                    (SmtTerm.bvnot
                      (SmtTerm.Binary
                        (__smtx_bv_sizeof_type
                          (__smtx_typeof (__eo_to_smt x))) 0)))
                  (fun hBody => by
                    rcases bv_binop_ret_args_of_non_none
                        (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1)
                        (by simp [__smtx_typeof]) (by
                          unfold term_has_non_none_type
                          exact hBody) with ⟨w, hArg, _hOther⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.bvredor
                  (SmtTerm.bvnot
                    (SmtTerm.bvcomp (__eo_to_smt x)
                      (SmtTerm.Binary
                        (__smtx_bv_sizeof_type
                          (__smtx_typeof (__eo_to_smt x))) 0)))
                  (fun hBody => by
                    let cmp :=
                      SmtTerm.bvcomp (__eo_to_smt x)
                        (SmtTerm.Binary
                          (__smtx_bv_sizeof_type
                            (__smtx_typeof (__eo_to_smt x))) 0)
                    rcases bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
                        (by simp [__smtx_typeof]) (by
                          unfold term_has_non_none_type
                          simpa [cmp] using hBody) with ⟨_w, hCmp⟩
                    have hCmpNN : term_has_non_none_type cmp := by
                      unfold term_has_non_none_type
                      rw [hCmp]
                      simp
                    rcases bv_binop_ret_args_of_non_none
                        (op := SmtTerm.bvcomp) (ret := SmtType.BitVec 1)
                        (by simp [cmp, __smtx_typeof]) hCmpNN with
                      ⟨w, hArg, _hOther⟩
                    exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.set_choose
                  (SmtTerm.map_diff (__eo_to_smt x)
                    (SmtTerm.set_empty
                      (__eo_to_smt_set_elem_type
                        (__smtx_typeof (__eo_to_smt x)))))
                  (fun hBody => by
                    have hMapNN :
                        term_has_non_none_type
                          (SmtTerm.map_diff (__eo_to_smt x)
                            (SmtTerm.set_empty
                              (__eo_to_smt_set_elem_type
                                (__smtx_typeof (__eo_to_smt x))))) := by
                      unfold term_has_non_none_type
                      exact hBody
                    rcases map_diff_args_of_non_none hMapNN with hMap | hSet
                    · rcases hMap with ⟨A, B, hArg, _hEmpty, _hRet⟩
                      exact smt_typeof_non_none_of_eq_non_none hArg (by simp)
                    · rcases hSet with ⟨A, hArg, _hEmpty, _hRet⟩
                      exact smt_typeof_non_none_of_eq_non_none hArg (by simp))
                  (by rfl) h
              | exact directUOpBody UserOp.set_is_empty
                  (SmtTerm.eq (__eo_to_smt x)
                    (SmtTerm.set_empty (__smtx_typeof (__eo_to_smt x))))
                  (fun hBody => by
                    have hEqNN :
                        __smtx_typeof_eq
                            (__smtx_typeof (__eo_to_smt x))
                            (__smtx_typeof
                              (SmtTerm.set_empty
                                (__smtx_typeof (__eo_to_smt x)))) ≠
                          SmtType.None := by
                      simpa [typeof_eq_eq] using hBody
                    exact (smtx_typeof_eq_non_none hEqNN).2)
                  (by rfl) h
              | exact directUOpBody UserOp.set_is_singleton
                  (SmtTerm.eq (__eo_to_smt x)
                    (SmtTerm.set_singleton
                      (SmtTerm.map_diff (__eo_to_smt x)
                        (SmtTerm.set_empty
                          (__eo_to_smt_set_elem_type
                            (__smtx_typeof (__eo_to_smt x)))))))
                  (fun hBody => by
                    let diff :=
                      SmtTerm.map_diff (__eo_to_smt x)
                        (SmtTerm.set_empty
                          (__eo_to_smt_set_elem_type
                            (__smtx_typeof (__eo_to_smt x))))
                    have hEqNN :
                        __smtx_typeof_eq
                            (__smtx_typeof (__eo_to_smt x))
                            (__smtx_typeof (SmtTerm.set_singleton diff)) ≠
                          SmtType.None := by
                      simpa [diff, typeof_eq_eq] using hBody
                    exact (smtx_typeof_eq_non_none hEqNN).2)
                  (by rfl) h
          | Apply g y =>
            have genericNested :
                __eo_to_smt (Term.Apply (Term.Apply g y) x) =
                    SmtTerm.Apply
                      (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x) ->
                  __smtx_typeof
                      (__eo_to_smt (Term.Apply (Term.Apply g y) x)) ≠
                    SmtType.None ->
                  NativeEoToSmtUOpIndicesSafe
                    (Term.Apply (Term.Apply g y) x) := by
              intro hTranslate h0
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_eo_generic_apply_non_none
                  (f := Term.Apply g y) (x := x)
                  (fun hf => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using
                      go (Term.Apply g y) hf)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  hTranslate h0
            have binaryUOpBody :
                ∀ (op0 : UserOp) (body : SmtTerm),
                  (__smtx_typeof body ≠ SmtType.None ->
                    __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ∧
                      __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) ->
                  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op0) y) x) =
                    body ->
                  __smtx_typeof
                      (__eo_to_smt
                        (Term.Apply (Term.Apply (Term.UOp op0) y) x)) ≠
                    SmtType.None ->
                  NativeEoToSmtUOpIndicesSafe
                    (Term.Apply (Term.Apply (Term.UOp op0) y) x) := by
              intro op0 body hBodyArgs hTranslate h0
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_apply_apply_uop_body_non_none
                  (op := op0) (y := y) (x := x)
                  (fun hy => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go y hy)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  hBodyArgs hTranslate h0
            have ternaryUOpBody :
                ∀ (op0 : UserOp) (z0 : Term) (body : SmtTerm),
                  (__smtx_typeof (__eo_to_smt z0) ≠ SmtType.None ->
                    NativeEoToSmtUOpIndicesSafe z0) ->
                  (__smtx_typeof body ≠ SmtType.None ->
                    __smtx_typeof (__eo_to_smt z0) ≠ SmtType.None ∧
                      __smtx_typeof (__eo_to_smt y) ≠ SmtType.None ∧
                        __smtx_typeof (__eo_to_smt x) ≠ SmtType.None) ->
                  __eo_to_smt
                      (Term.Apply
                        (Term.Apply (Term.Apply (Term.UOp op0) z0) y) x) =
                    body ->
                  __smtx_typeof
                      (__eo_to_smt
                        (Term.Apply
                          (Term.Apply (Term.Apply (Term.UOp op0) z0) y)
                          x)) ≠
                    SmtType.None ->
                  NativeEoToSmtUOpIndicesSafe
                    (Term.Apply
                      (Term.Apply (Term.Apply (Term.UOp op0) z0) y) x) := by
              intro op0 z0 body ihz0 hBodyArgs hTranslate h0
              simpa [NativeEoToSmtUOpIndicesSafe] using
                native_eo_to_smt_uop_indices_safe_of_apply_apply_apply_uop_body_non_none
                  (op := op0) (z := z0) (y := y) (x := x)
                  (fun hz => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using ihz0 hz)
                  (fun hy => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go y hy)
                  (fun hx => by
                    simpa [NativeEoToSmtUOpIndicesSafe] using go x hx)
                  hBodyArgs hTranslate h0
            have bvBinaryUOpBody :
                ∀ (op0 : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm),
                  __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
                      __smtx_typeof_bv_op_2
                        (__smtx_typeof (__eo_to_smt y))
                        (__smtx_typeof (__eo_to_smt x)) ->
                  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op0) y) x) =
                    smtOp (__eo_to_smt y) (__eo_to_smt x) ->
                  __smtx_typeof
                      (__eo_to_smt
                        (Term.Apply (Term.Apply (Term.UOp op0) y) x)) ≠
                    SmtType.None ->
                  NativeEoToSmtUOpIndicesSafe
                    (Term.Apply (Term.Apply (Term.UOp op0) y) x) := by
              intro op0 smtOp hTy hTranslate h0
              exact binaryUOpBody op0
                (smtOp (__eo_to_smt y) (__eo_to_smt x))
                (fun hBody => smt_bv_binop_args_non_none hTy hBody)
                hTranslate h0
            have bvBinaryRetUOpBody :
                ∀ (op0 : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
                  (ret : SmtType),
                  __smtx_typeof (smtOp (__eo_to_smt y) (__eo_to_smt x)) =
                      __smtx_typeof_bv_op_2_ret
                        (__smtx_typeof (__eo_to_smt y))
                        (__smtx_typeof (__eo_to_smt x)) ret ->
                  __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op0) y) x) =
                    smtOp (__eo_to_smt y) (__eo_to_smt x) ->
                  __smtx_typeof
                      (__eo_to_smt
                        (Term.Apply (Term.Apply (Term.UOp op0) y) x)) ≠
                    SmtType.None ->
                  NativeEoToSmtUOpIndicesSafe
                    (Term.Apply (Term.Apply (Term.UOp op0) y) x) := by
              intro op0 smtOp ret hTy hTranslate h0
              exact binaryUOpBody op0
                (smtOp (__eo_to_smt y) (__eo_to_smt x))
                (fun hBody => smt_bv_binop_ret_args_non_none hTy hBody)
                hTranslate h0
            cases g with
            | UOp op =>
              by_cases hopSetInsert : op = UserOp.set_insert
              · subst op
                simpa [NativeEoToSmtUOpIndicesSafe,
                  native_eo_to_smt_uop_indices_safe] using
                  native_eo_to_smt_uop_indices_safe_of_apply_apply_set_insert_non_none
                    (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)
                    (fun z _hzLt hz => by
                      simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                    (by simp; omega)
                    (by simp; omega)
                    h
              cases op
              all_goals
                first
                | exact False.elim (hopSetInsert rfl)
                | exact False.elim (hfExists ⟨y, rfl⟩)
                | exact False.elim (hfForall ⟨y, rfl⟩)
                | exact binaryUOpBody UserOp.or
                    (SmtTerm.or (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        bool_binop_args_bool_of_non_none (op := SmtTerm.or)
                          (typeof_or_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.and
                    (SmtTerm.and (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        bool_binop_args_bool_of_non_none (op := SmtTerm.and)
                          (typeof_and_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.imp
                    (SmtTerm.imp (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
                          (typeof_imp_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.xor
                    (SmtTerm.xor (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
                          (typeof_xor_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.eq
                    (SmtTerm.eq (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hEqNN :
                          __smtx_typeof_eq
                              (__smtx_typeof (__eo_to_smt y))
                              (__smtx_typeof (__eo_to_smt x)) ≠
                            SmtType.None := by
                        simpa [typeof_eq_eq] using hBody
                      have hEqArgs := smtx_typeof_eq_non_none hEqNN
                      exact ⟨hEqArgs.2, by
                        rw [← hEqArgs.1]
                        exact hEqArgs.2⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.plus
                    (SmtTerm.plus (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      rcases arith_binop_args_of_non_none (op := SmtTerm.plus)
                          (typeof_plus_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody) with hArgs | hArgs
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.neg
                    (SmtTerm.neg (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      rcases arith_binop_args_of_non_none (op := SmtTerm.neg)
                          (typeof_neg_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody) with hArgs | hArgs
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.mult
                    (SmtTerm.mult (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      rcases arith_binop_args_of_non_none (op := SmtTerm.mult)
                          (typeof_mult_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody) with hArgs | hArgs
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.lt
                    (SmtTerm.lt (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      rcases arith_binop_ret_bool_args_of_non_none
                          (op := SmtTerm.lt)
                          (typeof_lt_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody) with hArgs | hArgs
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.leq
                    (SmtTerm.leq (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      rcases arith_binop_ret_bool_args_of_non_none
                          (op := SmtTerm.leq)
                          (typeof_leq_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody) with hArgs | hArgs
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.gt
                    (SmtTerm.gt (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      rcases arith_binop_ret_bool_args_of_non_none
                          (op := SmtTerm.gt)
                          (typeof_gt_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody) with hArgs | hArgs
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.geq
                    (SmtTerm.geq (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      rcases arith_binop_ret_bool_args_of_non_none
                          (op := SmtTerm.geq)
                          (typeof_geq_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody) with hArgs | hArgs
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩
                      · exact
                          ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                              (by simp),
                            smt_typeof_non_none_of_eq_non_none hArgs.2
                              (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.div
                    (SmtTerm.div (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        int_binop_args_of_non_none (op := SmtTerm.div)
                          (typeof_div_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.mod
                    (SmtTerm.mod (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        int_binop_args_of_non_none (op := SmtTerm.mod)
                          (typeof_mod_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.multmult
                    (SmtTerm.multmult (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        int_binop_args_of_non_none (op := SmtTerm.multmult)
                          (typeof_multmult_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.divisible
                    (SmtTerm.divisible (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        int_binop_args_of_non_none (op := SmtTerm.divisible)
                          (typeof_divisible_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.div_total
                    (SmtTerm.div_total (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        int_binop_args_of_non_none (op := SmtTerm.div_total)
                          (typeof_div_total_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.mod_total
                    (SmtTerm.mod_total (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        int_binop_args_of_non_none (op := SmtTerm.mod_total)
                          (typeof_mod_total_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.multmult_total
                    (SmtTerm.multmult_total (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => by
                      have hArgs :=
                        int_binop_args_of_non_none (op := SmtTerm.multmult_total)
                          (typeof_multmult_total_eq (__eo_to_smt y) (__eo_to_smt x))
                          (by
                            unfold term_has_non_none_type
                            exact hBody)
                      exact
                        ⟨smt_typeof_non_none_of_eq_non_none hArgs.1
                            (by simp),
                          smt_typeof_non_none_of_eq_non_none hArgs.2
                            (by simp)⟩)
                    (by rfl) h
                | exact binaryUOpBody UserOp.select
                    (SmtTerm.select (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_select_args_non_none hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.concat
                    (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_bv_concat_args_non_none hBody)
                    (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvand SmtTerm.bvand
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvor SmtTerm.bvor
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvnand SmtTerm.bvnand
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvnor SmtTerm.bvnor
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvxor SmtTerm.bvxor
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvxnor SmtTerm.bvxnor
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvcomp SmtTerm.bvcomp
                    (SmtType.BitVec 1) (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvadd SmtTerm.bvadd
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvmul SmtTerm.bvmul
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvudiv SmtTerm.bvudiv
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvurem SmtTerm.bvurem
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvsub SmtTerm.bvsub
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvsdiv SmtTerm.bvsdiv
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvsrem SmtTerm.bvsrem
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvsmod SmtTerm.bvsmod
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvult SmtTerm.bvult
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvule SmtTerm.bvule
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvugt SmtTerm.bvugt
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvuge SmtTerm.bvuge
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvslt SmtTerm.bvslt
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvsle SmtTerm.bvsle
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvsgt SmtTerm.bvsgt
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvsge SmtTerm.bvsge
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvshl SmtTerm.bvshl
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvlshr SmtTerm.bvlshr
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryUOpBody UserOp.bvashr SmtTerm.bvashr
                    (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvuaddo SmtTerm.bvuaddo
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvsaddo SmtTerm.bvsaddo
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvumulo SmtTerm.bvumulo
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvsmulo SmtTerm.bvsmulo
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvusubo SmtTerm.bvusubo
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvssubo SmtTerm.bvssubo
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact bvBinaryRetUOpBody UserOp.bvsdivo SmtTerm.bvsdivo
                    SmtType.Bool (by simp [__smtx_typeof]) (by rfl) h
                | exact binaryUOpBody UserOp.bvultbv
                    (SmtTerm.ite
                      (SmtTerm.bvult (__eo_to_smt y) (__eo_to_smt x))
                      (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
                    (fun hBody => smt_bv_cmp_to_bv1_args_non_none
                      (cmp := SmtTerm.bvult) (by simp [__smtx_typeof])
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.bvsltbv
                    (SmtTerm.ite
                      (SmtTerm.bvslt (__eo_to_smt y) (__eo_to_smt x))
                      (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
                    (fun hBody => smt_bv_cmp_to_bv1_args_non_none
                      (cmp := SmtTerm.bvslt) (by simp [__smtx_typeof])
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp._at_from_bools
                    (SmtTerm.concat
                      (SmtTerm.ite (__eo_to_smt y) (SmtTerm.Binary 1 1)
                        (SmtTerm.Binary 1 0))
                      (__eo_to_smt x))
                    (fun hBody => smt_from_bools_args_non_none hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.str_concat
                    (SmtTerm.str_concat (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_seq_binop_args_non_none
                      (op := SmtTerm.str_concat)
                      (typeof_str_concat_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.str_contains
                    (SmtTerm.str_contains (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_seq_binop_ret_args_non_none
                      (op := SmtTerm.str_contains) (ret := SmtType.Bool)
                      (typeof_str_contains_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.str_at
                    (SmtTerm.str_at (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_str_at_args_non_none hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.str_prefixof
                    (SmtTerm.str_prefixof (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_seq_char_binop_args_non_none
                      (op := SmtTerm.str_prefixof) (ret := SmtType.Bool)
                      (typeof_str_prefixof_eq (__eo_to_smt y)
                        (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.str_suffixof
                    (SmtTerm.str_suffixof (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_seq_char_binop_args_non_none
                      (op := SmtTerm.str_suffixof) (ret := SmtType.Bool)
                      (typeof_str_suffixof_eq (__eo_to_smt y)
                        (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.str_lt
                    (SmtTerm.str_lt (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_seq_char_binop_args_non_none
                      (op := SmtTerm.str_lt) (ret := SmtType.Bool)
                      (typeof_str_lt_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.str_leq
                    (SmtTerm.str_leq (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_seq_char_binop_args_non_none
                      (op := SmtTerm.str_leq) (ret := SmtType.Bool)
                      (typeof_str_leq_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.re_range
                    (SmtTerm.re_range (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_seq_char_binop_args_non_none
                      (op := SmtTerm.re_range) (ret := SmtType.RegLan)
                      (typeof_re_range_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.re_concat
                    (SmtTerm.re_concat (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_reglan_binop_args_non_none
                      (op := SmtTerm.re_concat)
                      (typeof_re_concat_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.re_inter
                    (SmtTerm.re_inter (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_reglan_binop_args_non_none
                      (op := SmtTerm.re_inter)
                      (typeof_re_inter_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.re_union
                    (SmtTerm.re_union (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_reglan_binop_args_non_none
                      (op := SmtTerm.re_union)
                      (typeof_re_union_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.re_diff
                    (SmtTerm.re_diff (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_reglan_binop_args_non_none
                      (op := SmtTerm.re_diff)
                      (typeof_re_diff_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.str_in_re
                    (SmtTerm.str_in_re (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_seq_char_reglan_args_non_none
                      (op := SmtTerm.str_in_re) (ret := SmtType.Bool)
                      (typeof_str_in_re_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.seq_nth
                    (SmtTerm.seq_nth (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_seq_nth_args_non_none hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.set_union
                    (SmtTerm.set_union (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_set_binop_args_non_none
                      (op := SmtTerm.set_union)
                      (typeof_set_union_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.set_inter
                    (SmtTerm.set_inter (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_set_binop_args_non_none
                      (op := SmtTerm.set_inter)
                      (typeof_set_inter_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.set_minus
                    (SmtTerm.set_minus (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_set_binop_args_non_none
                      (op := SmtTerm.set_minus)
                      (typeof_set_minus_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.set_member
                    (SmtTerm.set_member (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_set_member_args_non_none hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.set_subset
                    (SmtTerm.set_subset (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_set_binop_ret_args_non_none
                      (op := SmtTerm.set_subset) (ret := SmtType.Bool)
                      (typeof_set_subset_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.qdiv
                    (SmtTerm.qdiv (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_arith_binop_ret_args_non_none
                      (op := SmtTerm.qdiv) (ret := SmtType.Real)
                      (typeof_qdiv_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.qdiv_total
                    (SmtTerm.qdiv_total (__eo_to_smt y) (__eo_to_smt x))
                    (fun hBody => smt_arith_binop_ret_args_non_none
                      (op := SmtTerm.qdiv_total) (ret := SmtType.Real)
                      (typeof_qdiv_total_eq (__eo_to_smt y) (__eo_to_smt x))
                      hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp._at_strings_num_occur
                    (SmtTerm.div
                      (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt y))
                        (SmtTerm.str_len
                          (SmtTerm.str_replace_all (__eo_to_smt y)
                            (__eo_to_smt x)
                            (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
                      (SmtTerm.str_len (__eo_to_smt x)))
                    (fun hBody => smt_strings_num_occur_args_non_none hBody)
                    (by rfl) h
                | exact binaryUOpBody UserOp.tuple
                    (__eo_to_smt_tuple_prepend (__eo_to_smt y)
                      (__smtx_typeof (__eo_to_smt y)) (__eo_to_smt x))
                    (fun hBody => smt_tuple_prepend_args_non_none hBody)
                    (by rfl) h
                | simpa [NativeEoToSmtUOpIndicesSafe,
                    native_eo_to_smt_uop_indices_safe] using
                    native_eo_to_smt_uop_indices_safe_of_apply_apply_set_insert_non_none
                      (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) y) x)
                      (fun z _hzLt hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (by simp; omega)
                      (by simp; omega)
                      h
                | exact genericNested (by rfl) h
            | Apply k z =>
              cases k with
              | UOp op =>
                cases op
                all_goals
                  first
                  | exact ternaryUOpBody UserOp.ite z
                      (SmtTerm.ite (__eo_to_smt z) (__eo_to_smt y)
                        (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_ite_args_non_none hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.store z
                      (SmtTerm.store (__eo_to_smt z) (__eo_to_smt y)
                        (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_store_args_non_none hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.bvite z
                      (SmtTerm.ite
                        (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1))
                        (__eo_to_smt y) (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_bvite_args_non_none hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.str_substr z
                      (SmtTerm.str_substr (__eo_to_smt z) (__eo_to_smt y)
                        (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_str_substr_args_non_none hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.str_replace z
                      (SmtTerm.str_replace (__eo_to_smt z) (__eo_to_smt y)
                        (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_seq_triop_args_non_none
                        (op := SmtTerm.str_replace)
                        (typeof_str_replace_eq (__eo_to_smt z)
                          (__eo_to_smt y) (__eo_to_smt x))
                        hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.str_indexof z
                      (SmtTerm.str_indexof (__eo_to_smt z) (__eo_to_smt y)
                        (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_str_indexof_args_non_none hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.str_update z
                      (SmtTerm.str_update (__eo_to_smt z) (__eo_to_smt y)
                        (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_str_update_args_non_none hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.str_replace_all z
                      (SmtTerm.str_replace_all (__eo_to_smt z)
                        (__eo_to_smt y) (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_seq_triop_args_non_none
                        (op := SmtTerm.str_replace_all)
                        (typeof_str_replace_all_eq (__eo_to_smt z)
                          (__eo_to_smt y) (__eo_to_smt x))
                        hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.str_replace_re z
                      (SmtTerm.str_replace_re (__eo_to_smt z)
                        (__eo_to_smt y) (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_str_replace_re_args_non_none
                        (op := SmtTerm.str_replace_re)
                        (typeof_str_replace_re_eq (__eo_to_smt z)
                          (__eo_to_smt y) (__eo_to_smt x))
                        hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.str_replace_re_all z
                      (SmtTerm.str_replace_re_all (__eo_to_smt z)
                        (__eo_to_smt y) (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_str_replace_re_args_non_none
                        (op := SmtTerm.str_replace_re_all)
                        (typeof_str_replace_re_all_eq (__eo_to_smt z)
                          (__eo_to_smt y) (__eo_to_smt x))
                        hBody)
                      (by rfl) h
                  | exact ternaryUOpBody UserOp.str_indexof_re z
                      (SmtTerm.str_indexof_re (__eo_to_smt z)
                        (__eo_to_smt y) (__eo_to_smt x))
                      (fun hz => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go z hz)
                      (fun hBody => smt_str_indexof_re_args_non_none hBody)
                      (by rfl) h
                  | exact genericNested (by rfl) h
              | _ =>
                exact genericNested (by rfl) h
            | __eo_List =>
              exact genericNested (by rfl) h
            | __eo_List_nil =>
              exact genericNested (by rfl) h
            | __eo_List_cons =>
              exact genericNested (by rfl) h
            | Bool =>
              exact genericNested (by rfl) h
            | Boolean b =>
              exact genericNested (by rfl) h
            | Numeral n =>
              exact genericNested (by rfl) h
            | Rational r =>
              exact genericNested (by rfl) h
            | String s =>
              exact genericNested (by rfl) h
            | Binary w n =>
              exact genericNested (by rfl) h
            | «Type» =>
              exact genericNested (by rfl) h
            | Stuck =>
              exact genericNested (by rfl) h
            | FunType =>
              exact genericNested (by rfl) h
            | Var name T =>
              exact genericNested (by rfl) h
            | DatatypeType s d =>
              exact genericNested (by rfl) h
            | DatatypeTypeRef s =>
              exact genericNested (by rfl) h
            | DtcAppType T U =>
              exact genericNested (by rfl) h
            | DtCons s d i =>
              exact genericNested (by rfl) h
            | DtSel s d i j =>
              exact genericNested (by rfl) h
            | USort i =>
              exact genericNested (by rfl) h
            | UConst i T =>
              exact genericNested (by rfl) h
            | UOp1 op idx =>
              cases op
              all_goals
                first
                | exact
                    native_eo_to_smt_uop_indices_safe_of_apply_apply_update_non_none
                      (fun ht => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go y ht)
                      (fun ht => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go x ht)
                      h
                | exact
                    native_eo_to_smt_uop_indices_safe_of_apply_apply_tuple_update_non_none
                      (fun ht => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go y ht)
                      (fun ht => by
                        simpa [NativeEoToSmtUOpIndicesSafe] using go x ht)
                      h
                | exact genericNested (by rfl) h
            | UOp2 op idx1 idx2 =>
              cases op
              all_goals
                first
                | exact genericNested (by rfl) h
            | UOp3 op idx1 idx2 idx3 =>
              cases op
              all_goals
                first
                | exact genericNested (by rfl) h
          | __eo_List =>
            exact generic Term.__eo_List (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | __eo_List_nil =>
            exact generic Term.__eo_List_nil (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | __eo_List_cons =>
            exact generic Term.__eo_List_cons (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | Bool =>
            exact generic Term.Bool (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | Boolean b =>
            exact generic (Term.Boolean b) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | Numeral n =>
            exact generic (Term.Numeral n) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | Rational r =>
            exact generic (Term.Rational r) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | String s =>
            exact generic (Term.String s) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | Binary w n =>
            exact generic (Term.Binary w n) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | «Type» =>
            exact generic Term.Type (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | Stuck =>
            exact generic Term.Stuck (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | FunType =>
            exact generic Term.FunType (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | Var name T =>
            exact generic (Term.Var name T) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | DatatypeType s d =>
            exact generic (Term.DatatypeType s d) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | DatatypeTypeRef s =>
            exact generic (Term.DatatypeTypeRef s) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | DtcAppType T U =>
            exact generic (Term.DtcAppType T U) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | DtCons s d i =>
            exact generic (Term.DtCons s d i) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | DtSel s d i j =>
            exact generic (Term.DtSel s d i j) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | USort i =>
            exact generic (Term.USort i) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
          | UConst i T =>
            exact generic (Term.UConst i T) (by simp [native_eo_to_smt_uop_indices_safe]) (by rfl) h
        all_goals
          trivial
  exact go t
