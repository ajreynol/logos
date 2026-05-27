import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.Translation.Apply
import Cpc.Proofs.Translation.EoTypeofCore
import Cpc.Proofs.Translation.Inversions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem eo_eq_true_eq {x y : Term} :
    __eo_eq x y = Term.Boolean true -> x = y := by
  intro h
  cases x <;> cases y <;>
    simp [__eo_eq, native_teq] at h ⊢
  all_goals
    simpa [eq_comm, and_left_comm, and_assoc] using h

private theorem eq_args_of_prog_dt_inst_ne_stuck
    (a1 : Term) :
    __eo_prog_dt_inst a1 ≠ Term.Stuck ->
    ∃ c x t,
      a1 =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.is c) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) t) ∧
      __mk_dt_inst (__eo_typeof x) c x = t ∧
      __eo_prog_dt_inst a1 = a1 := by
  intro hProg
  cases a1 with
  | Apply f rhs =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhs with
                  | Apply isHead x =>
                      cases isHead with
                      | UOp1 isOp c =>
                          cases isOp with
                          | is =>
                              cases rhs with
                              | Apply rhsF t =>
                                  cases rhsF with
                                  | Apply rhsG x2 =>
                                      cases rhsG with
                                      | UOp rhsOp =>
                                          cases rhsOp with
                                          | eq =>
                                              let body :=
                                                Term.Apply
                                                  (Term.Apply (Term.UOp UserOp.eq)
                                                    (Term.Apply (Term.UOp1 UserOp1.is c) x))
                                                  (Term.Apply
                                                    (Term.Apply (Term.UOp UserOp.eq) x) t)
                                              let req :=
                                                __eo_requires
                                                  (__mk_dt_inst (__eo_typeof x) c x) t body
                                              have hOuter :
                                                  __eo_requires (__eo_eq x x2)
                                                    (Term.Boolean true) req ≠
                                                    Term.Stuck := by
                                                simpa [__eo_prog_dt_inst, req, body] using hProg
                                              have hReq : req ≠ Term.Stuck := by
                                                exact eo_requires_result_ne_stuck_of_ne_stuck
                                                  (__eo_eq x x2) (Term.Boolean true) req hOuter
                                              have hXX : x = x2 := by
                                                have hEqReq :
                                                    __eo_eq x x2 = Term.Boolean true :=
                                                  eo_requires_eq_of_ne_stuck
                                                    (__eo_eq x x2) (Term.Boolean true) req
                                                    hOuter
                                                exact eo_eq_true_eq hEqReq
                                              subst x2
                                              have hMk : __mk_dt_inst (__eo_typeof x) c x = t :=
                                                eo_requires_eq_of_ne_stuck
                                                  (__mk_dt_inst (__eo_typeof x) c x) t body hReq
                                              have hReqEq : req = body :=
                                                eo_requires_eq_result_of_ne_stuck
                                                  (__mk_dt_inst (__eo_typeof x) c x) t body hReq
                                              have hProgEq :
                                                  __eo_prog_dt_inst
                                                    (Term.Apply
                                                      (Term.Apply (Term.UOp UserOp.eq)
                                                        (Term.Apply (Term.UOp1 UserOp1.is c) x))
                                                      (Term.Apply
                                                        (Term.Apply (Term.UOp UserOp.eq) x) t)) =
                                                    Term.Apply
                                                      (Term.Apply (Term.UOp UserOp.eq)
                                                        (Term.Apply (Term.UOp1 UserOp1.is c) x))
                                                      (Term.Apply
                                                        (Term.Apply (Term.UOp UserOp.eq) x) t) := by
                                                have hOuterEq :
                                                    __eo_requires (__eo_eq x x)
                                                      (Term.Boolean true) req = req :=
                                                  eo_requires_eq_result_of_ne_stuck
                                                    (__eo_eq x x) (Term.Boolean true) req
                                                    (by simpa using hOuter)
                                                simpa [__eo_prog_dt_inst, req, body, hReqEq]
                                                  using hOuterEq.trans hReqEq
                                              exact ⟨c, x, t, rfl, hMk, hProgEq⟩
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
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem prog_dt_inst_eq_arg_of_typeof_bool
    (a1 : Term) :
    __eo_typeof (__eo_prog_dt_inst a1) = Term.Bool ->
    __eo_prog_dt_inst a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_dt_inst a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases eq_args_of_prog_dt_inst_ne_stuck a1 hProg with
    ⟨_c, _x, _t, _hEq, _hMk, hProgEq⟩
  exact hProgEq

private theorem typed___eo_prog_dt_inst_impl
    (a1 : Term) :
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_typeof (__eo_prog_dt_inst a1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_dt_inst a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_dt_inst a1 = a1 :=
    prog_dt_inst_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private def smtDatatypeNumCtorsLocal : SmtDatatype -> Nat
  | SmtDatatype.null => 0
  | SmtDatatype.sum _ d => Nat.succ (smtDatatypeNumCtorsLocal d)

private theorem smtDatatypeNumCtorsLocal_substitute
    (s : native_String) (d0 : SmtDatatype) :
    ∀ d : SmtDatatype,
      smtDatatypeNumCtorsLocal (__smtx_dt_substitute s d0 d) =
        smtDatatypeNumCtorsLocal d
  | SmtDatatype.null => by
      simp [smtDatatypeNumCtorsLocal, __smtx_dt_substitute]
  | SmtDatatype.sum c d => by
      simp [smtDatatypeNumCtorsLocal, __smtx_dt_substitute,
        smtDatatypeNumCtorsLocal_substitute s d0 d]

private theorem smt_typeof_dt_cons_rec_non_none_implies_lt
    (T : SmtType) :
    ∀ {d : SmtDatatype} {i : Nat},
      __smtx_typeof_dt_cons_rec T d i ≠ SmtType.None ->
      i < smtDatatypeNumCtorsLocal d
  | SmtDatatype.null, i, h => by
      cases i <;> simp [smtDatatypeNumCtorsLocal, __smtx_typeof_dt_cons_rec] at h
  | SmtDatatype.sum c d, 0, h => by
      simp [smtDatatypeNumCtorsLocal]
  | SmtDatatype.sum c d, Nat.succ i, h => by
      have h' : __smtx_typeof_dt_cons_rec T d i ≠ SmtType.None := by
        simpa [__smtx_typeof_dt_cons_rec] using h
      have ih := smt_typeof_dt_cons_rec_non_none_implies_lt T (d := d) (i := i) h'
      simpa [smtDatatypeNumCtorsLocal] using Nat.succ_lt_succ ih

private theorem eo_mk_apply_of_ne_stuck {f x : Term}
    (hf : f ≠ Term.Stuck) (hx : x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem datatype_constructors_rec_ne_stuck
    (s : native_String) (root : Datatype) :
    ∀ current start,
      __eo_datatype_constructors_rec s root current start ≠ Term.Stuck
  | Datatype.null, start => by
      simp [__eo_datatype_constructors_rec]
  | Datatype.sum c d, start => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTail : tail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      change
        __eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail ≠
          Term.Stuck
      rw [eo_mk_apply_of_ne_stuck (by simp) hTail]
      simp

private theorem datatype_constructors_rec_is_list
    (s : native_String) (root : Datatype) :
    ∀ current start,
      __eo_is_list Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start) =
        Term.Boolean true
  | Datatype.null, start => by
      simp [__eo_datatype_constructors_rec, __eo_is_list, __eo_get_nil_rec,
        __eo_is_list_nil, __eo_is_ok, __eo_requires, __eo_eq, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | Datatype.sum c d, start => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      have hTailList :
          __eo_is_list Term.__eo_List_cons tail = Term.Boolean true :=
        datatype_constructors_rec_is_list s root d (Nat.succ start)
      have hTailGet : __eo_get_nil_rec Term.__eo_List_cons tail ≠ Term.Stuck := by
        cases hGet : __eo_get_nil_rec Term.__eo_List_cons tail <;>
          simp [__eo_is_list, __eo_is_ok, hGet, native_teq, native_not,
            SmtEval.native_not] at hTailList ⊢
      change
        __eo_is_list Term.__eo_List_cons
          (__eo_mk_apply (Term.Apply Term.__eo_List_cons (Term.DtCons s root start))
            tail) =
          Term.Boolean true
      rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
      simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil, __eo_is_ok,
        __eo_requires, __eo_eq, native_ite, native_teq, native_not,
        SmtEval.native_not, hTailList, hTailGet]

private theorem datatype_constructors_find_rec_self
    (s : native_String) (root : Datatype) :
    ∀ current start rel k,
      rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype current) ->
      __eo_list_find_rec
        (__eo_datatype_constructors_rec s root current start)
        (Term.DtCons s root (start + rel)) (Term.Numeral k) =
        Term.Numeral (k + rel)
  | Datatype.null, start, rel, k, hlt => by
      simp [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] at hlt
  | Datatype.sum c d, start, rel, k, hlt => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      cases rel with
      | zero =>
          change
            __eo_list_find_rec
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.DtCons s root (start + 0)) (Term.Numeral k) =
              Term.Numeral (k + 0)
          rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
          simp [__eo_list_find_rec, __eo_eq, native_ite, native_teq,
            native_not, SmtEval.native_not]
      | succ rel =>
          have hltTail : rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype d) := by
            simpa [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] using
              Nat.succ_lt_succ_iff.mp hlt
          have ih :=
            datatype_constructors_find_rec_self
              s root d (Nat.succ start) rel (k + 1) hltTail
          have hIdx :
              start + Nat.succ rel = Nat.succ start + rel := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          have hIdxNe : ¬ Nat.succ start + rel = start := by
            intro h
            have hltStart : start < Nat.succ start + rel :=
              Nat.lt_of_lt_of_le (Nat.lt_succ_self start)
                (Nat.le_add_right (Nat.succ start) rel)
            exact (Nat.ne_of_lt hltStart) h.symm
          change
            __eo_list_find_rec
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.DtCons s root (start + Nat.succ rel)) (Term.Numeral k) =
              Term.Numeral (k + Nat.succ rel)
          rw [hIdx]
          rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
          simp [__eo_list_find_rec, __eo_add, __eo_eq, native_ite,
            native_teq, native_not, SmtEval.native_not, hIdxNe]
          simpa [native_zplus, Int.add_assoc, Int.add_comm, Int.add_left_comm]
            using ih

private theorem datatype_constructors_find_self
    (s : native_String) (root : Datatype) (current : Datatype)
    (start rel : Nat)
    (hlt : rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype current)) :
    __eo_list_find Term.__eo_List_cons
      (__eo_datatype_constructors_rec s root current start)
      (Term.DtCons s root (start + rel)) =
      Term.Numeral rel := by
  have hList :
      __eo_is_list Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start) =
        Term.Boolean true :=
    datatype_constructors_rec_is_list s root current start
  simp [__eo_list_find, hList, __eo_requires,
    datatype_constructors_find_rec_self s root current start rel 0 hlt,
    native_ite, native_teq, native_not, SmtEval.native_not]

private theorem assoc_nil_nth_cons_succ
    (x xs : Term) (rel : Nat) :
    __assoc_nil_nth Term.__eo_List_cons
      ((Term.Apply Term.__eo_List_cons x).Apply xs)
      (Term.Numeral (Nat.succ rel)) =
    __assoc_nil_nth Term.__eo_List_cons xs (Term.Numeral rel) := by
  have hRelNe : ((Nat.succ rel : Nat) : Int) ≠ 0 :=
    Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero rel)
  rw [__assoc_nil_nth.eq_5]
  · rw [__eo_l_1___assoc_nil_nth.eq_3]
    · simp [__eo_requires, __eo_eq, __eo_add, native_zplus, native_ite,
        native_teq, native_not, SmtEval.native_not]
      congr
      exact Int.add_neg_cancel_right (rel : Int) (1 : Int)
    · intro h
      cases h
    · intro h
      cases h
  · intro h
    cases h
  · intro h
    cases h
  · intro h
    cases h
  · intro f y ys hList hZero
    injection hZero with hInt
    exact hRelNe hInt

private theorem assoc_nil_nth_datatype_constructors_nth
    (s : native_String) (root : Datatype) :
    ∀ current start rel,
      rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype current) ->
      __assoc_nil_nth Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start)
        (Term.Numeral rel) =
        Term.DtCons s root (start + rel)
  | Datatype.null, start, rel, hlt => by
      simp [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] at hlt
  | Datatype.sum c d, start, rel, hlt => by
      let tail := __eo_datatype_constructors_rec s root d (Nat.succ start)
      have hTailNe : tail ≠ Term.Stuck :=
        datatype_constructors_rec_ne_stuck s root d (Nat.succ start)
      cases rel with
      | zero =>
          change
            __assoc_nil_nth Term.__eo_List_cons
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.Numeral 0) =
              Term.DtCons s root (start + 0)
          rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
          simp [__assoc_nil_nth, __eo_eq, native_ite, native_teq,
            native_not, SmtEval.native_not]
      | succ rel =>
          have hltTail : rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype d) := by
            simpa [smtDatatypeNumCtorsLocal, __eo_to_smt_datatype] using
              Nat.succ_lt_succ_iff.mp hlt
          have ih :=
            assoc_nil_nth_datatype_constructors_nth
              s root d (Nat.succ start) rel hltTail
          have hIdx :
              start + Nat.succ rel = Nat.succ start + rel := by
            simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          change
            __assoc_nil_nth Term.__eo_List_cons
              (__eo_mk_apply
                (Term.Apply Term.__eo_List_cons (Term.DtCons s root start)) tail)
              (Term.Numeral (Nat.succ rel)) =
              Term.DtCons s root (start + Nat.succ rel)
          rw [hIdx]
          rw [eo_mk_apply_of_ne_stuck (by simp) hTailNe]
          rw [assoc_nil_nth_cons_succ (Term.DtCons s root start) tail rel]
          exact ih

private theorem assoc_nil_nth_datatype_constructors_find_self
    (s : native_String) (root : Datatype) (current : Datatype)
    (start rel : Nat)
    (hlt : rel < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype current)) :
    __assoc_nil_nth Term.__eo_List_cons
      (__eo_datatype_constructors_rec s root current start)
      (__eo_list_find Term.__eo_List_cons
        (__eo_datatype_constructors_rec s root current start)
        (Term.DtCons s root (start + rel))) =
      Term.DtCons s root (start + rel) := by
  rw [datatype_constructors_find_self s root current start rel hlt]
  exact assoc_nil_nth_datatype_constructors_nth s root current start rel hlt

private theorem assoc_nil_nth_dt_constructors_find_self
    (s : native_String) (d : Datatype) (i : Nat)
    (hlt : i < smtDatatypeNumCtorsLocal (__eo_to_smt_datatype d)) :
    __assoc_nil_nth Term.__eo_List_cons
      (__eo_dt_constructors (Term.DatatypeType s d))
      (__eo_list_find Term.__eo_List_cons
        (__dt_get_constructors (Term.DatatypeType s d))
        (Term.DtCons s d i)) =
      Term.DtCons s d i := by
  simpa [__eo_dt_constructors, __dt_get_constructors] using
    assoc_nil_nth_datatype_constructors_find_self s d d 0 i hlt

private theorem smt_value_eq_head_of_no_apply_args
    (v : SmtValue) :
    vsm_num_apply_args v = 0 ->
    v = __vsm_apply_head v := by
  intro h
  cases v <;> simp [vsm_num_apply_args, __vsm_apply_head] at h ⊢

private theorem dt_inst_bare_dtcons_interprets
    (M : SmtModel) (hM : model_total_typed M)
    (x : Term) (s : native_String) (d : Datatype) (i : Nat)
    (hReserved : native_reserved_datatype_name s = false)
    (hXTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Datatype s (__eo_to_smt_datatype d))
    (hNum : __smtx_dt_num_sels (__eo_to_smt_datatype d) i = 0)
    (hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x))
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
            (Term.DtCons s d i)))) :
    eo_interprets M
      (Term.Apply
        (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x))
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
          (Term.DtCons s d i))) true := by
  apply RuleProofs.eo_interprets_of_bool_eval M
  · exact hBool
  · let D := __eo_to_smt_datatype d
    let X := __eo_to_smt x
    have hTranslate :
        __eo_to_smt
            (Term.Apply
              (Term.Apply (Term.UOp UserOp.eq)
                (Term.Apply (Term.UOp1 UserOp1.is (Term.DtCons s d i)) x))
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x)
                (Term.DtCons s d i))) =
          SmtTerm.eq (SmtTerm.Apply (SmtTerm.DtTester s D i) X)
            (SmtTerm.eq X (SmtTerm.DtCons s D i)) := by
      change
        SmtTerm.eq
          (SmtTerm.Apply
            (__eo_to_smt_tester
              (native_ite (native_reserved_datatype_name s) SmtTerm.None
                (SmtTerm.DtCons s D i))) X)
          (SmtTerm.eq X
            (native_ite (native_reserved_datatype_name s) SmtTerm.None
              (SmtTerm.DtCons s D i))) =
          SmtTerm.eq (SmtTerm.Apply (SmtTerm.DtTester s D i) X)
            (SmtTerm.eq X (SmtTerm.DtCons s D i))
      rw [hReserved]
      rfl
    have hXNN : __smtx_typeof X ≠ SmtType.None := by
      rw [show __smtx_typeof X =
          SmtType.Datatype s D by simpa [X, D] using hXTy]
      simp
    have hEvalTy :
        __smtx_typeof_value (__smtx_model_eval M X) = SmtType.Datatype s D := by
      rw [smt_model_eval_preserves_type_of_non_none M hM X hXNN]
      simpa [X, D] using hXTy
    rw [hTranslate]
    simp [__smtx_model_eval, __smtx_model_eval_dt_tester]
    by_cases hHead :
        __vsm_apply_head (__smtx_model_eval M X) =
          SmtValue.DtCons s D i
    · have hCount :
          vsm_num_apply_args (__smtx_model_eval M X) = 0 := by
        have hCountSub :=
          vsm_num_apply_args_eq_dt_num_sels_of_datatype
            (v := __smtx_model_eval M X) hHead hEvalTy
        rw [dt_num_sels_substitute s D D i] at hCountSub
        simpa [D] using hCountSub.trans hNum
      have hVal :
          __smtx_model_eval M X = SmtValue.DtCons s D i := by
        calc
          __smtx_model_eval M X =
              __vsm_apply_head (__smtx_model_eval M X) :=
            smt_value_eq_head_of_no_apply_args _ hCount
          _ = SmtValue.DtCons s D i := hHead
      simp [hHead, hVal, native_veq, __smtx_model_eval_eq]
      simp [__vsm_apply_head]
    · have hNe :
          __smtx_model_eval M X ≠ SmtValue.DtCons s D i := by
        intro hVal
        apply hHead
        rw [hVal]
        simp [__vsm_apply_head]
      simp [hHead, hNe, native_veq, __smtx_model_eval_eq]

private theorem facts___eo_prog_dt_inst_impl
    (M : SmtModel) (hM : model_total_typed M) (a1 : Term) :
    RuleProofs.eo_has_smt_translation a1 ->
    __eo_typeof (__eo_prog_dt_inst a1) = Term.Bool ->
    eo_interprets M (__eo_prog_dt_inst a1) true := by
  sorry

theorem cmd_step_dt_inst_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_inst args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_inst args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_inst args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_inst args premises ≠ Term.Stuck :=
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
              have hA1TransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                hA1TransPair.1
              change __eo_typeof (__eo_prog_dt_inst a1) = Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_dt_inst a1) true
                exact facts___eo_prog_dt_inst_impl M hM a1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_dt_inst a1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_dt_inst a1)
                  (typed___eo_prog_dt_inst_impl a1 hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
