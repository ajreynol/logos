import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.DatatypeSupport
import Cpc.Proofs.Translation.Apply
import Cpc.Proofs.Rules.Dt_collapse_selector

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

attribute [local simp] native_ite native_teq native_not native_and native_zlt

private theorem eo_requires_eq_of_ne_stuck_local
    (T U V : Term) :
    __eo_requires T U V ≠ Term.Stuck ->
    T = U := by
  intro hReq
  by_cases hEq : T = U
  · exact hEq
  · exfalso
    apply hReq
    simp [__eo_requires, native_teq, hEq]

private theorem eo_requires_eq_result_of_ne_stuck_local
    (T U V : Term) :
    __eo_requires T U V ≠ Term.Stuck ->
    __eo_requires T U V = V := by
  intro hReq
  have hEq : T = U := eo_requires_eq_of_ne_stuck_local T U V hReq
  subst U
  have hT : T ≠ Term.Stuck := by
    intro hStuck
    apply hReq
    simp [__eo_requires, native_teq, hStuck]
  simp [__eo_requires, native_teq, hT]

private theorem eq_args_of_prog_dt_collapse_updater_ne_stuck
    (a1 : Term) :
  __eo_prog_dt_collapse_updater a1 ≠ Term.Stuck ->
  ∃ t s,
    a1 = Term.Apply (Term.Apply (Term.UOp UserOp.eq) t) s ∧
    __mk_dt_collapse_updater_rhs t = s ∧
    __eo_prog_dt_collapse_updater a1 = a1 := by
  intro hProg
  cases a1 with
  | Apply f rhs =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  let body := Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs
                  have hReq :
                      __eo_requires (__mk_dt_collapse_updater_rhs lhs) rhs body ≠
                        Term.Stuck := by
                    simpa [__eo_prog_dt_collapse_updater, body] using hProg
                  have hGuard :
                      __mk_dt_collapse_updater_rhs lhs = rhs :=
                    eo_requires_eq_of_ne_stuck_local
                      (__mk_dt_collapse_updater_rhs lhs) rhs body hReq
                  have hProgEq :
                      __eo_prog_dt_collapse_updater body = body := by
                    simpa [__eo_prog_dt_collapse_updater, body] using
                      eo_requires_eq_result_of_ne_stuck_local
                        (__mk_dt_collapse_updater_rhs lhs) rhs body hReq
                  exact ⟨lhs, rhs, rfl, hGuard, hProgEq⟩
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem prog_dt_collapse_updater_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_dt_collapse_updater a1) = Term.Bool ->
  __eo_prog_dt_collapse_updater a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_dt_collapse_updater a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases eq_args_of_prog_dt_collapse_updater_ne_stuck a1 hProg with
    ⟨_t, _s, _hEq, _hGuard, hProgEq⟩
  exact hProgEq

private theorem typed___eo_prog_dt_collapse_updater_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_updater a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_dt_collapse_updater a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_dt_collapse_updater a1 = a1 :=
    prog_dt_collapse_updater_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem eq_rhs_stuck_not_bool (lhs : Term) :
    ¬ RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) Term.Stuck) := by
  intro h
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      lhs Term.Stuck h
  have hNone : __smtx_typeof (__eo_to_smt lhs) = SmtType.None := by
    rw [hTypes.1]
    native_decide
  exact hTypes.2 hNone

private theorem smt_model_eval_ne_notvalue_of_non_none
    (M : SmtModel) (hM : model_total_typed M) (x : SmtTerm) :
    __smtx_typeof x ≠ SmtType.None ->
    __smtx_model_eval M x ≠ SmtValue.NotValue := by
  intro hNN hEval
  have hPres := smt_model_eval_preserves_type_of_non_none M hM x hNN
  have hNone : __smtx_typeof_value (__smtx_model_eval M x) = SmtType.None := by
    simp [hEval, __smtx_typeof_value]
  rw [hPres] at hNone
  exact hNN hNone

private theorem vsm_apply_ext_aux :
    ∀ (n : Nat) (v w : SmtValue),
      vsm_num_apply_args v = n ->
      __vsm_apply_head v = __vsm_apply_head w ->
      vsm_num_apply_args v = vsm_num_apply_args w ->
      (∀ j, j < vsm_num_apply_args v ->
        __vsm_apply_arg_nth v j (vsm_num_apply_args v) =
          __vsm_apply_arg_nth w j (vsm_num_apply_args w)) ->
      v = w := by
  intro n
  induction n with
  | zero =>
      intro v w hv hHead hCount _hArgs
      cases v <;> simp [vsm_num_apply_args] at hv
      all_goals
        cases w <;> simp [vsm_num_apply_args] at hCount
        simp [__vsm_apply_head] at hHead ⊢
        all_goals try exact hHead
  | succ n ih =>
      intro v w hv hHead hCount hArgs
      cases v <;> simp [vsm_num_apply_args] at hv
      case Apply f a =>
        cases w <;> simp [vsm_num_apply_args] at hCount
        case Apply g b =>
          have hCountFG : vsm_num_apply_args f = vsm_num_apply_args g := hCount
          have hLast :
              __vsm_apply_arg_nth (SmtValue.Apply f a) (vsm_num_apply_args f)
                  (vsm_num_apply_args (SmtValue.Apply f a)) =
                __vsm_apply_arg_nth (SmtValue.Apply g b) (vsm_num_apply_args f)
                  (vsm_num_apply_args (SmtValue.Apply g b)) :=
            hArgs (vsm_num_apply_args f) (by simp [vsm_num_apply_args])
          have hab : a = b := by
            simpa [__vsm_apply_arg_nth, vsm_num_apply_args, hCountFG,
              SmtEval.native_nateq] using hLast
          have hfg : f = g := by
            apply ih f g hv
            · simpa [__vsm_apply_head] using hHead
            · exact hCountFG
            · intro j hj
              have hjTop : j < vsm_num_apply_args (SmtValue.Apply f a) := by
                simp [vsm_num_apply_args]
                exact Nat.lt_succ_of_lt hj
              have hArg := hArgs j hjTop
              have hNeF : j ≠ vsm_num_apply_args f := by omega
              have hNeG : j ≠ vsm_num_apply_args g := by
                intro hEq
                apply hNeF
                rw [hCountFG, hEq]
              simpa [__vsm_apply_arg_nth, vsm_num_apply_args, hCountFG,
                SmtEval.native_nateq, hNeF, hNeG] using hArg
          subst hfg
          subst hab
          rfl

private theorem vsm_apply_ext
    (v w : SmtValue)
    (hHead : __vsm_apply_head v = __vsm_apply_head w)
    (hCount : vsm_num_apply_args v = vsm_num_apply_args w)
    (hArgs : ∀ j, j < vsm_num_apply_args v ->
      __vsm_apply_arg_nth v j (vsm_num_apply_args v) =
        __vsm_apply_arg_nth w j (vsm_num_apply_args w)) :
    v = w :=
  vsm_apply_ext_aux (vsm_num_apply_args v) v w rfl hHead hCount hArgs

private theorem smtx_model_eval_apply_of_dt_chain
    (M : SmtModel) (v x : SmtValue)
    (hHead : ∃ s d i, __vsm_apply_head v = SmtValue.DtCons s d i)
    (hx : x ≠ SmtValue.NotValue) :
    __smtx_model_eval_apply M v x = SmtValue.Apply v x := by
  cases x <;> simp [__smtx_model_eval_apply] at hx ⊢
  all_goals
    cases v <;> simp [__smtx_model_eval_apply, __vsm_apply_head] at hHead ⊢

private theorem smtx_ite_then_non_none
    (c x y : SmtTerm) :
    __smtx_typeof (SmtTerm.ite c x y) ≠ SmtType.None ->
    __smtx_typeof x ≠ SmtType.None := by
  intro hNN hX
  apply hNN
  cases hc : __smtx_typeof c <;>
    cases hx : __smtx_typeof x <;>
    cases hy : __smtx_typeof y <;>
    simp [__smtx_typeof, __smtx_typeof_ite, native_ite, native_Teq,
      hc, hx, hy] at hX ⊢

private theorem smtx_ite_else_non_none
    (c x y : SmtTerm) :
    __smtx_typeof (SmtTerm.ite c x y) ≠ SmtType.None ->
    __smtx_typeof y ≠ SmtType.None := by
  intro hNN hY
  apply hNN
  cases hc : __smtx_typeof c <;>
    cases hx : __smtx_typeof x <;>
    cases hy : __smtx_typeof y <;>
    simp [__smtx_typeof, __smtx_typeof_ite, native_ite, native_Teq,
      hc, hx, hy] at hY ⊢

private theorem smtx_apply_arg_non_none_of_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    cases f with
    | DtSel s d i j =>
        exact False.elim (hSel s d i j rfl)
    | DtTester s d i =>
        exact False.elim (hTester s d i rfl)
    | _ =>
        simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with ⟨A, _B, _hHead, hArg, hA, _hB⟩
  rw [hArg]
  exact hA

private theorem smtx_apply_head_non_none_of_non_none
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i)
    (hNN : __smtx_typeof (SmtTerm.Apply f x) ≠ SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  have hApply :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    cases f with
    | DtSel s d i j =>
        exact False.elim (hSel s d i j rfl)
    | DtTester s d i =>
        exact False.elim (hTester s d i rfl)
    | _ =>
        simpa [__smtx_typeof] using hNN
  rcases typeof_apply_non_none_cases hApply with ⟨A, B, hHead, _hArg, _hA, _hB⟩
  rcases hHead with hHead | hHead <;> rw [hHead] <;> simp

private theorem eo_to_smt_updater_rec_ne_dt_sel_local
    (s : native_String) (d : SmtDatatype) (i j n : native_Nat) (t u acc : SmtTerm)
    (hAccSel : ∀ s d i j, acc ≠ SmtTerm.DtSel s d i j)
    (s0 : native_String) (d0 : SmtDatatype) (i0 j0 : native_Nat) :
    __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc ≠
      SmtTerm.DtSel s0 d0 i0 j0 := by
  intro h
  cases n with
  | zero =>
      simpa [__eo_to_smt_updater_rec] using hAccSel s0 d0 i0 j0 h
  | succ _ =>
      cases h

private theorem eo_to_smt_updater_rec_ne_dt_tester_local
    (s : native_String) (d : SmtDatatype) (i j n : native_Nat) (t u acc : SmtTerm)
    (hAccTester : ∀ s d i, acc ≠ SmtTerm.DtTester s d i)
    (s0 : native_String) (d0 : SmtDatatype) (i0 : native_Nat) :
    __eo_to_smt_updater_rec (SmtTerm.DtSel s d i j) n t u acc ≠
      SmtTerm.DtTester s0 d0 i0 := by
  intro h
  cases n with
  | zero =>
      simpa [__eo_to_smt_updater_rec] using hAccTester s0 d0 i0 h
  | succ _ =>
      cases h

private theorem smtx_model_eval_apply_eq_apply_of_not_dt_ops
    (M : SmtModel) (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x) := by
  cases f <;> simp [__smtx_model_eval]

private theorem updater_rec_eval_components
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : SmtDatatype) (i m n : native_Nat)
    (t u : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) n t u
          (SmtTerm.DtCons s d i)) ≠
      SmtType.None ->
    __vsm_apply_head
        (__smtx_model_eval M
          (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) n t u
            (SmtTerm.DtCons s d i))) =
        SmtValue.DtCons s d i ∧
      vsm_num_apply_args
          (__smtx_model_eval M
            (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) n t u
              (SmtTerm.DtCons s d i))) =
        n ∧
      ∀ q, q < n ->
        __vsm_apply_arg_nth
            (__smtx_model_eval M
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) n t u
                (SmtTerm.DtCons s d i)))
            q n =
          __smtx_model_eval M
            (native_ite (native_nateq m q) u
              (SmtTerm.Apply (SmtTerm.DtSel s d i q) t)) := by
  induction n with
  | zero =>
      intro _hNN
      constructor
      · simp [__eo_to_smt_updater_rec, __smtx_model_eval, __vsm_apply_head]
      constructor
      · simp [__eo_to_smt_updater_rec, __smtx_model_eval, vsm_num_apply_args]
      · intro q hq
        exact False.elim (Nat.not_lt_zero q hq)
  | succ k ih =>
      intro hNN
      let recTerm :=
        __eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) k t u
          (SmtTerm.DtCons s d i)
      let argTerm :=
        native_ite (native_nateq m k) u
          (SmtTerm.Apply (SmtTerm.DtSel s d i k) t)
      have hTermNN :
          __smtx_typeof (SmtTerm.Apply recTerm argTerm) ≠ SmtType.None := by
        simpa [__eo_to_smt_updater_rec, recTerm, argTerm] using hNN
      have hRecSel :
          ∀ s0 d0 i0 j0, recTerm ≠ SmtTerm.DtSel s0 d0 i0 j0 :=
        eo_to_smt_updater_rec_ne_dt_sel_local s d i m k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 j0 h; cases h)
      have hRecTester :
          ∀ s0 d0 i0, recTerm ≠ SmtTerm.DtTester s0 d0 i0 :=
        eo_to_smt_updater_rec_ne_dt_tester_local s d i m k t u
          (SmtTerm.DtCons s d i) (by intro s0 d0 i0 h; cases h)
      have hRecNN : __smtx_typeof recTerm ≠ SmtType.None :=
        smtx_apply_head_non_none_of_non_none recTerm argTerm hRecSel hRecTester
          hTermNN
      have hArgNN : __smtx_typeof argTerm ≠ SmtType.None :=
        smtx_apply_arg_non_none_of_non_none recTerm argTerm hRecSel hRecTester
          hTermNN
      rcases ih hRecNN with ⟨hHeadRec, hCountRec, hArgsRec⟩
      have hArgNot :
          __smtx_model_eval M argTerm ≠ SmtValue.NotValue :=
        smt_model_eval_ne_notvalue_of_non_none M hM argTerm hArgNN
      have hEvalApply :
          __smtx_model_eval M (SmtTerm.Apply recTerm argTerm) =
            SmtValue.Apply (__smtx_model_eval M recTerm)
              (__smtx_model_eval M argTerm) := by
        rw [smtx_model_eval_apply_eq_apply_of_not_dt_ops
          M recTerm argTerm hRecSel hRecTester]
        rw [smtx_model_eval_apply_of_dt_chain M
          (__smtx_model_eval M recTerm) (__smtx_model_eval M argTerm)
          ⟨s, d, i, hHeadRec⟩ hArgNot]
      have hEval :
          __smtx_model_eval M
              (__eo_to_smt_updater_rec (SmtTerm.DtSel s d i m) (Nat.succ k)
                t u (SmtTerm.DtCons s d i)) =
            SmtValue.Apply (__smtx_model_eval M recTerm)
              (__smtx_model_eval M argTerm) := by
        simpa [__eo_to_smt_updater_rec, recTerm, argTerm] using hEvalApply
      constructor
      · rw [hEval]
        simpa [__vsm_apply_head] using hHeadRec
      constructor
      · rw [hEval]
        simp [vsm_num_apply_args]
        simpa [recTerm] using hCountRec
      · intro q hq
        by_cases hLast : q = k
        · subst q
          have hEqBool : native_nateq k k = true := by
            simp [native_nateq, SmtEval.native_nateq]
          rw [hEval]
          simp [__vsm_apply_arg_nth, vsm_num_apply_args, hCountRec,
            hEqBool, argTerm]
        · have hqk : q < k := by
            exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hq) hLast
          have hNeBool : native_nateq q k = false := by
            simp [native_nateq, SmtEval.native_nateq, hLast]
          rw [hEval]
          simp [__vsm_apply_arg_nth, vsm_num_apply_args, hCountRec,
            hNeBool]
          exact hArgsRec q hqk

private theorem tuple_update_shape_of_non_none
    (idx t a : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    ∃ (d : SmtDatatype) (n : native_Int),
      __smtx_typeof (__eo_to_smt t) =
          SmtType.Datatype (native_string_lit "@Tuple") d ∧
        idx = Term.Numeral n ∧
        0 ≤ n ∧
        native_int_to_nat n < __smtx_dt_num_sels d native_nat_zero := by
  intro hNN
  change
      __smtx_typeof
          (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
            (__eo_to_smt idx) (__eo_to_smt t) (__eo_to_smt a)) ≠
        SmtType.None at hNN
  cases hTy : __smtx_typeof (__eo_to_smt t) with
  | Datatype s d =>
      cases hIdx : __eo_to_smt idx with
      | Numeral n =>
          by_cases hs : s = native_string_lit "@Tuple"
          · subst s
            have hGe : native_zleq 0 n = true := by
              cases hTest : native_zleq 0 n
              · simp [__eo_to_smt_tuple_update, hTy, hIdx, hTest,
                  native_streq, native_and, native_ite] at hNN
              · rfl
            have hUpdaterNN :
                __smtx_typeof
                    (__eo_to_smt_updater
                      (SmtTerm.DtSel (native_string_lit "@Tuple") d
                        native_nat_zero (native_int_to_nat n))
                      (__eo_to_smt t) (__eo_to_smt a)) ≠
                  SmtType.None := by
              simpa [__eo_to_smt_tuple_update, hTy, hIdx, hGe,
                native_streq, native_and, native_ite] using hNN
            have hIdxBoundBool :
                native_zlt
                    (native_nat_to_int (native_int_to_nat n))
                    (native_nat_to_int (__smtx_dt_num_sels d native_nat_zero)) =
                  true :=
              TranslationProofs.eo_to_smt_updater_dt_sel_guard_of_non_none
                (native_string_lit "@Tuple") d native_nat_zero
                (native_int_to_nat n) (__eo_to_smt t) (__eo_to_smt a)
                hUpdaterNN
            have hIdxEq : idx = Term.Numeral n :=
              TranslationProofs.eo_to_smt_eq_numeral idx n hIdx
            have hNonneg : 0 ≤ n := by
              simpa [native_zleq, SmtEval.native_zleq] using hGe
            have hLt : native_int_to_nat n <
                __smtx_dt_num_sels d native_nat_zero := by
              have hInt :
                  (native_int_to_nat n : Int) <
                    (__smtx_dt_num_sels d native_nat_zero : Int) := by
                apply of_decide_eq_true
                simpa [native_zlt, SmtEval.native_zlt, native_nat_to_int,
                  SmtEval.native_nat_to_int] using hIdxBoundBool
              exact Int.ofNat_lt.mp hInt
            exact ⟨d, n, rfl, hIdxEq, hNonneg, hLt⟩
          · exfalso
            apply hNN
            simp [__eo_to_smt_tuple_update, hTy, hIdx, hs, native_streq,
              native_and, native_ite]
      | _ =>
          exfalso
          apply hNN
          simp [__eo_to_smt_tuple_update, hTy, hIdx]
  | _ =>
      exfalso
      apply hNN
      simp [__eo_to_smt_tuple_update, hTy]

private theorem tuple_update_rec_non_none_of_shape
    (idx t a : Term) (d : SmtDatatype) (n : native_Int) :
    __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype (native_string_lit "@Tuple") d ->
    idx = Term.Numeral n ->
    0 ≤ n ->
    native_int_to_nat n < __smtx_dt_num_sels d native_nat_zero ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_updater_rec
          (SmtTerm.DtSel (native_string_lit "@Tuple") d native_nat_zero
            (native_int_to_nat n))
          (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt t)
          (__eo_to_smt a)
          (SmtTerm.DtCons (native_string_lit "@Tuple") d native_nat_zero)) ≠
      SmtType.None := by
  intro hT hIdx hNonneg hLt hNN
  subst idx
  have hGe : native_zleq 0 n = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hNonneg
  have hIdxProp :
      (native_int_to_nat n : Int) <
        (__smtx_dt_num_sels d native_nat_zero : Int) :=
    Int.ofNat_lt.mpr hLt
  have hIdxBool :
      native_zlt
          (native_nat_to_int (native_int_to_nat n))
          (native_nat_to_int (__smtx_dt_num_sels d native_nat_zero)) =
        true := by
    apply decide_eq_true hIdxProp
  have hUpdaterNN :
      __smtx_typeof
          (__eo_to_smt_updater
            (SmtTerm.DtSel (native_string_lit "@Tuple") d native_nat_zero
              (native_int_to_nat n))
            (__eo_to_smt t) (__eo_to_smt a)) ≠
        SmtType.None := by
    change
        __smtx_typeof
            (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
              (SmtTerm.Numeral n) (__eo_to_smt t) (__eo_to_smt a)) ≠
          SmtType.None at hNN
    simpa [__eo_to_smt_tuple_update, hT, hGe, native_streq,
      native_and, native_ite] using hNN
  have hIteNN :
      __smtx_typeof
          (SmtTerm.ite
            (SmtTerm.Apply
              (SmtTerm.DtTester (native_string_lit "@Tuple") d native_nat_zero)
              (__eo_to_smt t))
            (__eo_to_smt_updater_rec
              (SmtTerm.DtSel (native_string_lit "@Tuple") d native_nat_zero
                (native_int_to_nat n))
              (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt t)
              (__eo_to_smt a)
              (SmtTerm.DtCons (native_string_lit "@Tuple") d native_nat_zero))
            (__eo_to_smt t)) ≠
        SmtType.None := by
    simpa [__eo_to_smt_updater, native_ite, hIdxBool, native_zlt,
      SmtEval.native_zlt, native_nat_to_int, SmtEval.native_nat_to_int,
      hIdxProp] using hUpdaterNN
  exact smtx_ite_then_non_none _ _ _ hIteNN

private theorem tuple_update_arg_type_of_non_none
    (idx t a : Term) (d : SmtDatatype) (n : native_Int) :
    __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype (native_string_lit "@Tuple") d ->
    idx = Term.Numeral n ->
    0 ≤ n ->
    native_int_to_nat n < __smtx_dt_num_sels d native_nat_zero ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt a) =
      __smtx_ret_typeof_sel (native_string_lit "@Tuple") d native_nat_zero
        (native_int_to_nat n) := by
  intro hT hIdx hNonneg hLt hNN
  have hRecNN :=
    tuple_update_rec_non_none_of_shape idx t a d n hT hIdx hNonneg hLt hNN
  have hIdxBool :
      native_zlt
          (native_nat_to_int (native_int_to_nat n))
          (native_nat_to_int (__smtx_dt_num_sels d native_nat_zero)) =
        true := by
    have hInt :
        (native_int_to_nat n : Int) <
          (__smtx_dt_num_sels d native_nat_zero : Int) :=
      Int.ofNat_lt.mpr hLt
    apply decide_eq_true hInt
  exact
    TranslationProofs.eo_to_smt_updater_rec_update_arg_type_of_non_none
      (native_string_lit "@Tuple") d native_nat_zero (native_int_to_nat n)
      (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt t) (__eo_to_smt a)
      hIdxBool hRecNN

private theorem tuple_value_count_of_type_local
    {v : SmtValue} {c : SmtDatatypeCons}
    (hTy :
      __smtx_typeof_value v =
        SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum c SmtDatatype.null))
    (hHead :
      __vsm_apply_head v =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (SmtDatatype.sum c SmtDatatype.null) native_nat_zero) :
    vsm_num_apply_args v =
      __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
        native_nat_zero := by
  have hCount :=
    vsm_num_apply_args_eq_dt_num_sels_of_datatype hHead hTy
  simpa [dt_num_sels_substitute] using hCount

private theorem tuple_update_eval_eq_rec_of_tuple_type
    (M : SmtModel) (hM : model_total_typed M)
    (idx t a : Term) (c : SmtDatatypeCons) (n : native_Int) :
    __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum c SmtDatatype.null) ->
    idx = Term.Numeral n ->
    0 ≤ n ->
    native_int_to_nat n <
      __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
        native_nat_zero ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      __smtx_model_eval M
        (__eo_to_smt_updater_rec
          (SmtTerm.DtSel (native_string_lit "@Tuple")
            (SmtDatatype.sum c SmtDatatype.null) native_nat_zero
            (native_int_to_nat n))
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero)
          (__eo_to_smt t) (__eo_to_smt a)
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (SmtDatatype.sum c SmtDatatype.null) native_nat_zero)) := by
  intro hT hIdx hNonneg hLt
  subst idx
  have hGe : native_zleq 0 n = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hNonneg
  have hIdxProp :
      (native_int_to_nat n : Int) <
        (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
          native_nat_zero : Int) :=
    Int.ofNat_lt.mpr hLt
  have hIdxBool :
      native_zlt
          (native_nat_to_int (native_int_to_nat n))
          (native_nat_to_int
            (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
              native_nat_zero)) =
        true := by
    apply decide_eq_true hIdxProp
  have hIdxLt :
      native_nat_to_int (native_int_to_nat n) <
        native_nat_to_int
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hIdxProp
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [hT]
    simp
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum c SmtDatatype.null) := by
    rw [smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hTNN,
      hT]
  have hHead :
      __vsm_apply_head (__smtx_model_eval M (__eo_to_smt t)) =
        SmtValue.DtCons (native_string_lit "@Tuple")
          (SmtDatatype.sum c SmtDatatype.null) native_nat_zero :=
    tuple_datatype_value_head_zero hEvalTy
  change
    __smtx_model_eval M
        (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
          (SmtTerm.Numeral n) (__eo_to_smt t) (__eo_to_smt a)) =
      __smtx_model_eval M
        (__eo_to_smt_updater_rec
          (SmtTerm.DtSel (native_string_lit "@Tuple")
            (SmtDatatype.sum c SmtDatatype.null) native_nat_zero
            (native_int_to_nat n))
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero)
          (__eo_to_smt t) (__eo_to_smt a)
          (SmtTerm.DtCons (native_string_lit "@Tuple")
            (SmtDatatype.sum c SmtDatatype.null) native_nat_zero))
  rw [hT]
  simp [__eo_to_smt_tuple_update, __eo_to_smt_updater, native_ite,
    native_and, hGe, hIdxBool, hIdxLt, native_streq, __smtx_model_eval,
    __smtx_model_eval_dt_tester, hHead, native_veq,
    __smtx_model_eval_ite]

private theorem tuple_update_type_eq_tuple_type_of_shape
    (idx t a : Term) (d : SmtDatatype) (n : native_Int) :
    __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype (native_string_lit "@Tuple") d ->
    idx = Term.Numeral n ->
    0 ≤ n ->
    native_int_to_nat n < __smtx_dt_num_sels d native_nat_zero ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      SmtType.Datatype (native_string_lit "@Tuple") d := by
  intro hT hIdx hNonneg hLt hNN
  subst idx
  have hGe : native_zleq 0 n = true := by
    simpa [native_zleq, SmtEval.native_zleq] using hNonneg
  have hIdxProp :
      (native_int_to_nat n : Int) <
        (__smtx_dt_num_sels d native_nat_zero : Int) :=
    Int.ofNat_lt.mpr hLt
  have hIdxBool :
      native_zlt
          (native_nat_to_int (native_int_to_nat n))
          (native_nat_to_int (__smtx_dt_num_sels d native_nat_zero)) =
        true := by
    apply decide_eq_true hIdxProp
  have hIdxLt :
      native_nat_to_int (native_int_to_nat n) <
        native_nat_to_int (__smtx_dt_num_sels d native_nat_zero) := by
    simpa [native_nat_to_int, SmtEval.native_nat_to_int] using hIdxProp
  have hRecNN :=
    tuple_update_rec_non_none_of_shape (Term.Numeral n) t a d n
      hT rfl hNonneg hLt hNN
  let recTerm :=
    __eo_to_smt_updater_rec
      (SmtTerm.DtSel (native_string_lit "@Tuple") d native_nat_zero
        (native_int_to_nat n))
      (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt t)
      (__eo_to_smt a)
      (SmtTerm.DtCons (native_string_lit "@Tuple") d native_nat_zero)
  have hRecTyRaw :
      __smtx_typeof recTerm =
        dt_cons_applied_type_rec (native_string_lit "@Tuple") d
          (__smtx_dt_substitute (native_string_lit "@Tuple") d d)
          native_nat_zero (__smtx_dt_num_sels d native_nat_zero) := by
    simpa [recTerm] using
      TranslationProofs.eo_to_smt_updater_rec_type_of_non_none
        (native_string_lit "@Tuple") d native_nat_zero (native_int_to_nat n)
        (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt t) (__eo_to_smt a)
        hRecNN
  have hNumSub :
      __smtx_dt_num_sels
          (__smtx_dt_substitute (native_string_lit "@Tuple") d d)
          native_nat_zero =
        __smtx_dt_num_sels d native_nat_zero :=
    dt_num_sels_substitute (native_string_lit "@Tuple") d d native_nat_zero
  have hFullNN :
      dt_cons_applied_type_rec (native_string_lit "@Tuple") d
          (__smtx_dt_substitute (native_string_lit "@Tuple") d d)
          native_nat_zero
          (__smtx_dt_num_sels
            (__smtx_dt_substitute (native_string_lit "@Tuple") d d)
            native_nat_zero) ≠
        SmtType.None := by
    rw [hNumSub]
    rw [← hRecTyRaw]
    exact hRecNN
  have hRecTy :
      __smtx_typeof recTerm = SmtType.Datatype (native_string_lit "@Tuple") d := by
    rw [hRecTyRaw]
    rw [← hNumSub]
    exact
      dt_cons_applied_type_rec_full_arity (native_string_lit "@Tuple") d
        (__smtx_dt_substitute (native_string_lit "@Tuple") d d)
        native_nat_zero hFullNN
  let cond :=
    SmtTerm.Apply
      (SmtTerm.DtTester (native_string_lit "@Tuple") d native_nat_zero)
      (__eo_to_smt t)
  have hIteNN :
      __smtx_typeof (SmtTerm.ite cond recTerm (__eo_to_smt t)) ≠
        SmtType.None := by
    change
      __smtx_typeof
          (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
            (SmtTerm.Numeral n) (__eo_to_smt t) (__eo_to_smt a)) ≠
        SmtType.None at hNN
    rw [hT] at hNN
    simpa [__eo_to_smt_tuple_update, __eo_to_smt_updater, native_ite,
      native_and, hGe, hIdxBool, hIdxLt, native_streq, cond, recTerm] using hNN
  rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, _hTNN⟩
  have hTEq : T = SmtType.Datatype (native_string_lit "@Tuple") d := by
    exact hElse.symm.trans hT
  change
    __smtx_typeof
        (__eo_to_smt_tuple_update (__smtx_typeof (__eo_to_smt t))
          (SmtTerm.Numeral n) (__eo_to_smt t) (__eo_to_smt a)) =
      SmtType.Datatype (native_string_lit "@Tuple") d
  rw [hT]
  simp [__eo_to_smt_tuple_update, __eo_to_smt_updater, native_ite,
    native_and, hGe, hIdxBool, hIdxLt, native_streq, hT, hRecTy,
    typeof_ite_eq, hCond, hThen, hElse, hTEq, __smtx_typeof_ite,
    native_Teq, cond, recTerm]

private theorem tuple_collapse_updater_rhs_ne_stuck_shape
    (t a idx : Term) :
    __tuple_collapse_updater_rhs t a idx ≠ Term.Stuck ->
    t = Term.UOp UserOp.tuple_unit ∨
      ∃ head tail,
        t = Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail := by
  intro h
  have hA : a ≠ Term.Stuck := by
    intro hStuck
    apply h
    simp [__tuple_collapse_updater_rhs, hStuck]
  have hIdx : idx ≠ Term.Stuck := by
    intro hStuck
    apply h
    simp [__tuple_collapse_updater_rhs, hStuck]
  cases t with
  | UOp op =>
      cases op with
      | tuple_unit =>
          left
          rfl
      | _ =>
          exfalso
          apply h
          simp [__tuple_collapse_updater_rhs, hA, hIdx]
  | Apply f tail =>
      cases f with
      | Apply g head =>
          cases g with
          | UOp op =>
              cases op with
              | tuple =>
                  right
                  exact ⟨head, tail, rfl⟩
              | _ =>
                  exfalso
                  apply h
                  simp [__tuple_collapse_updater_rhs, hA, hIdx]
          | _ =>
              exfalso
              apply h
              simp [__tuple_collapse_updater_rhs, hA, hIdx]
      | _ =>
          exfalso
          apply h
          simp [__tuple_collapse_updater_rhs, hA, hIdx]
  | _ =>
      exfalso
      apply h
      simp [__tuple_collapse_updater_rhs, hA, hIdx]

private theorem tuple_collapse_updater_eval_eq
    (M : SmtModel) (hM : model_total_typed M)
    (idx t a : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      __smtx_typeof (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)) ≠
      SmtType.None ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      (__smtx_model_eval M
        (__eo_to_smt (__tuple_collapse_updater_rhs t a idx))) := by
  intro hTypeEq hLhsNN hRhsNN
  have hRhsTermNN :
      __tuple_collapse_updater_rhs t a idx ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation
      (__tuple_collapse_updater_rhs t a idx) hRhsNN
  rcases tuple_collapse_updater_rhs_ne_stuck_shape t a idx hRhsTermNN with
    hUnit | hTuple
  · subst t
    rcases tuple_update_shape_of_non_none idx (Term.UOp UserOp.tuple_unit) a
        hLhsNN with
      ⟨d, n, hT, hIdx, _hNonneg, hLt⟩
    subst idx
    have hD :
        d = SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null := by
      change
        __smtx_typeof
            (SmtTerm.DtCons (native_string_lit "@Tuple")
              (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) 0) =
          SmtType.Datatype (native_string_lit "@Tuple") d at hT
      rw [TranslationProofs.smtx_typeof_tuple_unit_translation] at hT
      injection hT with _ hD'
      exact hD'.symm
    subst d
    simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at hLt
  · rcases hTuple with ⟨head, tail, hTupleEq⟩
    subst t
    let tupleTerm := Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail
    let headSmt := __eo_to_smt head
    let tailSmt := __eo_to_smt tail
    let aSmt := __eo_to_smt a
    let headTy := __smtx_typeof headSmt
    rcases tuple_update_shape_of_non_none idx tupleTerm a hLhsNN with
      ⟨d, n, hT, hIdx, hNonneg, hLt⟩
    subst idx
    have hTupleNN : __smtx_typeof (__eo_to_smt tupleTerm) ≠ SmtType.None := by
      rw [hT]
      simp
    rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
        tail head hTupleNN with
      ⟨c, hTailTy⟩
    let tailD := SmtDatatype.sum c SmtDatatype.null
    let fullC := SmtDatatypeCons.cons headTy c
    let fullD := SmtDatatype.sum fullC SmtDatatype.null
    have hTupleTyFull :
        __smtx_typeof (__eo_to_smt tupleTerm) =
          SmtType.Datatype (native_string_lit "@Tuple") fullD := by
      change
        __smtx_typeof
            (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) =
          SmtType.Datatype (native_string_lit "@Tuple") fullD
      exact
        TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
          tailSmt headSmt headTy c
          (by simpa [tailSmt, tailD] using hTailTy)
          (by
            change
              __smtx_typeof
                  (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) ≠
                SmtType.None
            simpa [tupleTerm, headSmt, tailSmt, headTy] using hTupleNN)
    have hD : d = fullD := by
      rw [hT] at hTupleTyFull
      injection hTupleTyFull with _ hD'
    subst d
    by_cases hn0 : n = 0
    · subst n
      have hNonneg0 : (0 : native_Int) ≤ 0 := by decide
      have hLhsEval :=
        tuple_update_eval_eq_rec_of_tuple_type M hM (Term.Numeral 0)
          tupleTerm a fullC 0 hTupleTyFull rfl hNonneg0 hLt
      have hRecNN :=
        tuple_update_rec_non_none_of_shape (Term.Numeral 0) tupleTerm a
          fullD 0 hTupleTyFull rfl hNonneg0 hLt hLhsNN
      have hComp :=
        updater_rec_eval_components M hM (native_string_lit "@Tuple") fullD
          native_nat_zero native_nat_zero
          (__smtx_dt_num_sels fullD native_nat_zero)
          (__eo_to_smt tupleTerm) aSmt hRecNN
      have hCompHead := hComp.1
      have hCompCount := hComp.2.1
      have hCompArgs := hComp.2.2
      have hLhsEval' :
          __smtx_model_eval M
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral 0))
                    tupleTerm) a)) =
            __smtx_model_eval M
              (__eo_to_smt_updater_rec
                (SmtTerm.DtSel (native_string_lit "@Tuple") fullD
                  native_nat_zero native_nat_zero)
                (__smtx_dt_num_sels fullD native_nat_zero)
                (__eo_to_smt tupleTerm) aSmt
                (SmtTerm.DtCons (native_string_lit "@Tuple") fullD
                  native_nat_zero)) := by
        simpa [fullD, aSmt] using hLhsEval
      have hANe : a ≠ Term.Stuck := by
        intro hA
        apply hRhsTermNN
        simp [__tuple_collapse_updater_rhs, hA]
      have hRhsEq :
          __tuple_collapse_updater_rhs tupleTerm a (Term.Numeral 0) =
            Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail := by
        cases a <;> simp [tupleTerm, __tuple_collapse_updater_rhs] at hANe ⊢
      have hRhsNNBase :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) ≠
            SmtType.None := by
        rw [← hRhsEq]
        simpa [tupleTerm] using hRhsNN
      have hLhsTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral 0))
                    tupleTerm) a)) =
            SmtType.Datatype (native_string_lit "@Tuple") fullD :=
        tuple_update_type_eq_tuple_type_of_shape (Term.Numeral 0) tupleTerm a
          fullD 0 hTupleTyFull rfl hNonneg0 hLt hLhsNN
      have hTypeEqBase :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp1 UserOp1.tuple_update (Term.Numeral 0))
                    tupleTerm) a)) =
            __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) := by
        rw [← hRhsEq]
        simpa [tupleTerm] using hTypeEq
      have hRhsTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) =
            SmtType.Datatype (native_string_lit "@Tuple") fullD := by
        rw [← hTypeEqBase]
        exact hLhsTy
      have hRhsPrependTy :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail)) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (SmtDatatype.sum (SmtDatatypeCons.cons (__smtx_typeof aSmt) c)
                SmtDatatype.null) := by
        change
          __smtx_typeof
              (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt) tailSmt) =
            SmtType.Datatype (native_string_lit "@Tuple")
              (SmtDatatype.sum (SmtDatatypeCons.cons (__smtx_typeof aSmt) c)
                SmtDatatype.null)
        exact
          TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
            tailSmt aSmt (__smtx_typeof aSmt) c
            (by simpa [tailSmt, tailD] using hTailTy)
            (by
              change
                __smtx_typeof
                    (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt)
                      tailSmt) ≠ SmtType.None
              simpa [aSmt, tailSmt] using hRhsNNBase)
      have hFullArgEq :
          SmtDatatype.sum (SmtDatatypeCons.cons (__smtx_typeof aSmt) c)
              SmtDatatype.null =
            fullD := by
        have h := hRhsPrependTy.symm.trans hRhsTy
        injection h with _ hD'
      have hRhsEvalTy :
          __smtx_typeof_value
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail))) =
            SmtType.Datatype (native_string_lit "@Tuple") fullD := by
        rw [smt_model_eval_preserves_type_of_non_none M hM
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail))
          hRhsNNBase, hRhsTy]
      have hRhsHead :
          __vsm_apply_head
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail))) =
            SmtValue.DtCons (native_string_lit "@Tuple") fullD native_nat_zero :=
        tuple_datatype_value_head_zero (by simpa [fullD] using hRhsEvalTy)
      have hRhsCount :
          vsm_num_apply_args
              (__smtx_model_eval M
                (__eo_to_smt
                  (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) a) tail))) =
            __smtx_dt_num_sels fullD native_nat_zero :=
        tuple_value_count_of_type_local (by simpa [fullD] using hRhsEvalTy)
          (by simpa [fullD] using hRhsHead)
      rw [hLhsEval']
      rw [hRhsEq]
      apply vsm_apply_ext
      · rw [hCompHead, hRhsHead]
      · rw [hCompCount, hRhsCount]
      · intro q hq
        have hqFull : q < __smtx_dt_num_sels fullD native_nat_zero := by
          simpa [hCompCount] using hq
        cases q with
        | zero =>
            have hLhsArg := hCompArgs native_nat_zero hqFull
            have hRhsArg :=
              tuple_prepend_zero_projection M hM aSmt tailSmt
                (__smtx_typeof aSmt) c
                (by simpa [tailSmt, tailD] using hTailTy)
                (by
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt)
                          tailSmt) ≠ SmtType.None
                  simpa [aSmt, tailSmt] using hRhsNNBase)
            simpa [hCompCount, hRhsCount, hFullArgEq, native_nateq,
              SmtEval.native_nateq, aSmt] using hLhsArg.trans hRhsArg.symm
        | succ j =>
            have hjTail :
                j < __smtx_dt_num_sels tailD native_nat_zero := by
              simpa [fullD, fullC, tailD, __smtx_dt_num_sels,
                __smtx_dtc_num_sels] using hqFull
            have hLhsArg := hCompArgs (Nat.succ j) hqFull
            have hSelEval :
                __smtx_model_eval M
                    (SmtTerm.Apply
                      (SmtTerm.DtSel (native_string_lit "@Tuple") fullD
                        native_nat_zero (Nat.succ j))
                      (__eo_to_smt tupleTerm)) =
                  __vsm_apply_arg_nth
                    (__smtx_model_eval M (__eo_to_smt tupleTerm))
                    (Nat.succ j)
                    (__smtx_dt_num_sels fullD native_nat_zero) := by
              simpa [fullD, tupleTerm] using
                smt_tuple_dt_sel_eval_uses_constructor M hM
                  (__eo_to_smt tupleTerm) fullC (Nat.succ j)
                  (by simpa [fullD] using hTupleTyFull)
            have hOrigSucc :=
              tuple_prepend_succ_projection M hM headSmt tailSmt headTy c j
                (by simpa [tailSmt, tailD] using hTailTy)
                (by
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_prepend headSmt headTy tailSmt) ≠
                      SmtType.None
                  simpa [tupleTerm, headSmt, tailSmt, headTy] using hTupleNN)
                (by simpa [tailD] using hjTail)
            have hRhsSucc :=
              tuple_prepend_succ_projection M hM aSmt tailSmt
                (__smtx_typeof aSmt) c j
                (by simpa [tailSmt, tailD] using hTailTy)
                (by
                  change
                    __smtx_typeof
                        (__eo_to_smt_tuple_prepend aSmt (__smtx_typeof aSmt)
                          tailSmt) ≠ SmtType.None
                  simpa [aSmt, tailSmt] using hRhsNNBase)
                (by simpa [tailD] using hjTail)
            have hLhsArg' :
                __vsm_apply_arg_nth
                    (__smtx_model_eval M
                      (__eo_to_smt_updater_rec
                        (SmtTerm.DtSel (native_string_lit "@Tuple") fullD
                          native_nat_zero native_nat_zero)
                        (__smtx_dt_num_sels fullD native_nat_zero)
                        (__eo_to_smt tupleTerm) aSmt
                        (SmtTerm.DtCons (native_string_lit "@Tuple") fullD
                          native_nat_zero)))
                    (Nat.succ j) (__smtx_dt_num_sels fullD native_nat_zero) =
                  __vsm_apply_arg_nth
                    (__smtx_model_eval M tailSmt) j
                    (__smtx_dt_num_sels tailD native_nat_zero) := by
              have hNe : native_nateq native_nat_zero (Nat.succ j) = false := by
                simp [native_nateq, SmtEval.native_nateq]
              have hLhsSel :
                  __vsm_apply_arg_nth
                      (__smtx_model_eval M
                        (__eo_to_smt_updater_rec
                          (SmtTerm.DtSel (native_string_lit "@Tuple") fullD
                            native_nat_zero native_nat_zero)
                          (__smtx_dt_num_sels fullD native_nat_zero)
                          (__eo_to_smt tupleTerm) aSmt
                          (SmtTerm.DtCons (native_string_lit "@Tuple") fullD
                            native_nat_zero)))
                      (Nat.succ j) (__smtx_dt_num_sels fullD native_nat_zero) =
                    __smtx_model_eval M
                      (SmtTerm.Apply
                        (SmtTerm.DtSel (native_string_lit "@Tuple") fullD
                          native_nat_zero (Nat.succ j))
                        (__eo_to_smt tupleTerm)) := by
                simpa [hNe, tupleTerm] using hLhsArg
              exact hLhsSel.trans (hSelEval.trans hOrigSucc)
            simpa [hCompCount, hRhsCount, hFullArgEq, hLhsArg', tailD] using
              hRhsSucc.symm
    · sorry

private theorem tuple_collapse_updater_eval_rel
    (M : SmtModel) (hM : model_total_typed M)
    (idx t a : Term) :
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) =
      __smtx_typeof (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)) ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt (__tuple_collapse_updater_rhs t a idx)) ≠
      SmtType.None ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp1 UserOp1.tuple_update idx) t) a)))
      (__smtx_model_eval M
        (__eo_to_smt (__tuple_collapse_updater_rhs t a idx))) := by
  intro hTypeEq hLhsNN hRhsNN
  rw [tuple_collapse_updater_eval_eq M hM idx t a hTypeEq hLhsNN hRhsNN]
  exact RuleProofs.smt_value_rel_refl _

private theorem facts___eo_prog_dt_collapse_updater_impl
    (M : SmtModel) (hM : model_total_typed M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_updater a1) = Term.Bool ->
  eo_interprets M (__eo_prog_dt_collapse_updater a1) true := by
  intro hA1Trans hResultTy
  have hProg : __eo_prog_dt_collapse_updater a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases eq_args_of_prog_dt_collapse_updater_ne_stuck a1 hProg with
    ⟨lhs, rhs, hA1Eq, hGuard, hProgEq⟩
  have hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) := by
    subst hA1Eq
    have hA1Ty :
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs) =
          Term.Bool := by
      simpa [hProgEq] using hResultTy
    exact RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) lhs) rhs)
      hA1Trans hA1Ty
  rw [hProgEq]
  rw [hA1Eq]
  apply RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBool
  cases lhs with
  | Apply f a =>
      cases f with
      | Apply g t =>
          cases g with
          | UOp1 op sel =>
              cases op with
              | update =>
                  simp [__mk_dt_collapse_updater_rhs] at hGuard
                  sorry
              | tuple_update =>
                  simp [__mk_dt_collapse_updater_rhs] at hGuard
                  subst rhs
                  have hTypes :=
                    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                      (((Term.UOp1 UserOp1.tuple_update sel).Apply t).Apply a)
                      (__tuple_collapse_updater_rhs t a sel) hBool
                  exact tuple_collapse_updater_eval_rel M hM sel t a
                    hTypes.1
                    hTypes.2
                    (by
                      rw [← hTypes.1]
                      exact hTypes.2)
              | _ =>
                  simp [__mk_dt_collapse_updater_rhs] at hGuard
                  subst rhs
                  exact False.elim (eq_rhs_stuck_not_bool _ hBool)
          | _ =>
              simp [__mk_dt_collapse_updater_rhs] at hGuard
              subst rhs
              exact False.elim (eq_rhs_stuck_not_bool _ hBool)
      | _ =>
          simp [__mk_dt_collapse_updater_rhs] at hGuard
          subst rhs
          exact False.elim (eq_rhs_stuck_not_bool _ hBool)
  | _ =>
      simp [__mk_dt_collapse_updater_rhs] at hGuard
      subst rhs
      exact False.elim (eq_rhs_stuck_not_bool _ hBool)

theorem cmd_step_dt_collapse_updater_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_collapse_updater args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_collapse_updater args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_collapse_updater args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.dt_collapse_updater args premises ≠
        Term.Stuck :=
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
              have hA1TransPair :
                  RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                hA1TransPair.1
              change __eo_typeof (__eo_prog_dt_collapse_updater a1) =
                Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_dt_collapse_updater a1) true
                exact facts___eo_prog_dt_collapse_updater_impl
                  M hM a1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_dt_collapse_updater a1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_dt_collapse_updater a1)
                  (typed___eo_prog_dt_collapse_updater_impl a1
                    hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
