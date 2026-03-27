import CpcMini.Proofs.TypePreservation.Helpers

open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace Smtm

theorem typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero
    (T : SmtType) :
    ∀ c d,
      __smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) smt_lit_nat_zero =
        __smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) smt_lit_nat_zero
  | SmtDatatypeCons.unit, d => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec]
  | SmtDatatypeCons.cons U c, d => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec,
        typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero T c d]

theorem typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec
    (T : SmtType) :
    ∀ d n,
      __smtx_typeof_dt_cons_value_rec T d n =
        __smtx_typeof_dt_cons_rec T d n
  | SmtDatatype.null, n => by
      cases n <;> simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec]
  | SmtDatatype.sum c d, smt_lit_nat_zero =>
      typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero T c d
  | SmtDatatype.sum c d, smt_lit_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec] using
        typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec T d n

theorem typeof_value_model_eval_dt_cons
    (M : SmtModel)
    (s : smt_lit_String)
    (d : SmtDatatype)
    (i : smt_lit_Nat) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s d i) := by
  change
    __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i =
      __smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i
  exact typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec (SmtType.Datatype s d)
    (__smtx_dt_substitute s d d) i

def dt_cons_type_num_args : SmtType -> Nat
  | SmtType.DtConsType _ U => Nat.succ (dt_cons_type_num_args U)
  | _ => 0

def dt_cons_applied_type_rec
    (s : smt_lit_String)
    (d0 : SmtDatatype) :
    SmtDatatype -> Nat -> Nat -> SmtType
  | d, i, 0 => __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i
  | SmtDatatype.sum (SmtDatatypeCons.cons _ c) d, 0, Nat.succ n =>
      dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n
  | SmtDatatype.sum c d, Nat.succ i, n =>
      dt_cons_applied_type_rec s d0 d i n
  | _, _, _ => SmtType.None

theorem dt_cons_type_num_args_typeof_dt_cons_value_rec
    (s : smt_lit_String)
    (d0 : SmtDatatype) :
    ∀ d i,
      dt_cons_type_num_args (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i) =
        __smtx_dt_num_sels d i
  | SmtDatatype.null, i => by
      cases i <;>
        simp [dt_cons_type_num_args, __smtx_typeof_dt_cons_value_rec, __smtx_dt_num_sels]
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0 => by
      simp [dt_cons_type_num_args, __smtx_typeof_dt_cons_value_rec, __smtx_dt_num_sels,
        __smtx_dtc_num_sels]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0 => by
      simp [dt_cons_type_num_args, __smtx_typeof_dt_cons_value_rec, __smtx_dt_num_sels,
        __smtx_dtc_num_sels,
        dt_cons_type_num_args_typeof_dt_cons_value_rec s d0 (SmtDatatype.sum c d) 0]
  | SmtDatatype.sum c d, Nat.succ i => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_dt_num_sels,
        dt_cons_type_num_args_typeof_dt_cons_value_rec s d0 d i]

theorem dt_cons_type_num_args_dt_cons_applied_type_rec
    (s : smt_lit_String)
    (d0 : SmtDatatype) :
    ∀ d i n,
      dt_cons_type_num_args (dt_cons_applied_type_rec s d0 d i n) = __smtx_dt_num_sels d i - n
  | d, i, 0 => by
      simp [dt_cons_applied_type_rec, dt_cons_type_num_args_typeof_dt_cons_value_rec]
  | SmtDatatype.null, i, Nat.succ n => by
      cases i <;>
        simp [dt_cons_applied_type_rec, dt_cons_type_num_args, __smtx_dt_num_sels]
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, Nat.succ n => by
      simp [dt_cons_applied_type_rec, dt_cons_type_num_args, __smtx_dt_num_sels,
        __smtx_dtc_num_sels]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n => by
      have ih := dt_cons_type_num_args_dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n
      simpa [dt_cons_applied_type_rec, __smtx_dt_num_sels, __smtx_dtc_num_sels] using ih
  | SmtDatatype.sum c d, Nat.succ i, n => by
      cases n with
      | zero =>
          simp [dt_cons_applied_type_rec, dt_cons_type_num_args_typeof_dt_cons_value_rec,
            __smtx_dt_num_sels]
      | succ n =>
          have ih := dt_cons_type_num_args_dt_cons_applied_type_rec s d0 d i (Nat.succ n)
          simpa [dt_cons_applied_type_rec, __smtx_dt_num_sels] using ih

theorem dt_cons_applied_type_rec_step
    (s : smt_lit_String)
    (d0 : SmtDatatype) :
    ∀ d i n,
      n < __smtx_dt_num_sels d i ->
      dt_cons_applied_type_rec s d0 d i n =
        SmtType.DtConsType (__smtx_ret_typeof_sel_rec d i n) (dt_cons_applied_type_rec s d0 d i (Nat.succ n))
  | SmtDatatype.null, i, n, hlt => by
      cases i <;> simp [__smtx_dt_num_sels] at hlt
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, n, hlt => by
      simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at hlt
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, 0, hlt => by
      simp [dt_cons_applied_type_rec, __smtx_ret_typeof_sel_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n, hlt => by
      have hlt' : n < __smtx_dt_num_sels (SmtDatatype.sum c d) 0 := by
        simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using hlt
      simpa [dt_cons_applied_type_rec, __smtx_ret_typeof_sel_rec] using
        dt_cons_applied_type_rec_step s d0 (SmtDatatype.sum c d) 0 n hlt'
  | SmtDatatype.sum c d, Nat.succ i, n, hlt => by
      have hlt' : n < __smtx_dt_num_sels d i := by
        simpa [__smtx_dt_num_sels] using hlt
      cases n with
      | zero =>
          simpa [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec,
            __smtx_ret_typeof_sel_rec] using
            dt_cons_applied_type_rec_step s d0 d i 0 hlt'
      | succ n =>
          simpa [dt_cons_applied_type_rec, __smtx_ret_typeof_sel_rec] using
            dt_cons_applied_type_rec_step s d0 d i (Nat.succ n) hlt'

theorem dt_cons_applied_type_rec_non_none_implies_le
    (s : smt_lit_String)
    (d0 : SmtDatatype) :
    ∀ d i n,
      dt_cons_applied_type_rec s d0 d i n ≠ SmtType.None ->
      n ≤ __smtx_dt_num_sels d i
  | d, i, 0, h => by
      simp
  | SmtDatatype.null, i, Nat.succ n, h => by
      cases i <;> simp [dt_cons_applied_type_rec] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, Nat.succ n, h => by
      simp [dt_cons_applied_type_rec] at h
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n, h => by
      have ih := dt_cons_applied_type_rec_non_none_implies_le s d0 (SmtDatatype.sum c d) 0 n
      have h' : dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n ≠ SmtType.None := by
        simpa [dt_cons_applied_type_rec] using h
      have hle : n ≤ __smtx_dt_num_sels (SmtDatatype.sum c d) 0 := ih h'
      simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using Nat.succ_le_succ hle
  | SmtDatatype.sum c d, Nat.succ i, n, h => by
      cases n with
      | zero =>
          simp [__smtx_dt_num_sels]
      | succ n =>
          have ih := dt_cons_applied_type_rec_non_none_implies_le s d0 d i (Nat.succ n)
          have h' : dt_cons_applied_type_rec s d0 d i (Nat.succ n) ≠ SmtType.None := by
            simpa [dt_cons_applied_type_rec] using h
          have hle : Nat.succ n ≤ __smtx_dt_num_sels d i := ih h'
          simpa [__smtx_dt_num_sels] using hle

theorem dt_cons_applied_type_rec_eq_bare_type_implies_zero
    {s : smt_lit_String}
    {d0 : SmtDatatype}
    {i n : Nat}
    (hEq :
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) (__smtx_dt_substitute s d0 d0) i =
        dt_cons_applied_type_rec s d0 (__smtx_dt_substitute s d0 d0) i n)
    (hNN : dt_cons_applied_type_rec s d0 (__smtx_dt_substitute s d0 d0) i n ≠ SmtType.None) :
    n = 0 := by
  have hArgs := congrArg dt_cons_type_num_args hEq
  rw [dt_cons_type_num_args_typeof_dt_cons_value_rec,
    dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
  have hle :
      n ≤ __smtx_dt_num_sels (__smtx_dt_substitute s d0 d0) i :=
    dt_cons_applied_type_rec_non_none_implies_le s d0 (__smtx_dt_substitute s d0 d0) i n hNN
  omega

def vsm_num_apply_args : SmtValue -> Nat
  | SmtValue.Apply f _ => Nat.succ (vsm_num_apply_args f)
  | _ => 0

theorem dtc_num_sels_substitute
    (s : smt_lit_String)
    (d : SmtDatatype) :
    ∀ c, __smtx_dtc_num_sels (__smtx_dtc_substitute s d c) = __smtx_dtc_num_sels c
  | SmtDatatypeCons.unit => by
      simp [__smtx_dtc_substitute, __smtx_dtc_num_sels]
  | SmtDatatypeCons.cons T c => by
      cases T <;>
        simp [__smtx_dtc_substitute, __smtx_dtc_num_sels,
          dtc_num_sels_substitute s d c, smt_lit_ite, smt_lit_Teq, smt_lit_streq]

theorem dt_num_sels_substitute
    (s : smt_lit_String)
    (d0 : SmtDatatype) :
    ∀ d i, __smtx_dt_num_sels (__smtx_dt_substitute s d0 d) i = __smtx_dt_num_sels d i
  | SmtDatatype.null, i => by
      cases i <;> simp [__smtx_dt_substitute, __smtx_dt_num_sels]
  | SmtDatatype.sum c d, 0 => by
      simp [__smtx_dt_substitute, __smtx_dt_num_sels, dtc_num_sels_substitute]
  | SmtDatatype.sum c d, Nat.succ i => by
      simp [__smtx_dt_substitute, __smtx_dt_num_sels, dt_num_sels_substitute s d0 d i]

theorem ret_typeof_sel_rec_non_none_implies_lt :
    ∀ d i j,
      __smtx_ret_typeof_sel_rec d i j ≠ SmtType.None ->
      j < __smtx_dt_num_sels d i
  | SmtDatatype.null, i, j, h => by
      cases i <;> cases j <;> simp [__smtx_ret_typeof_sel_rec] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, j, h => by
      cases j <;> simp [__smtx_ret_typeof_sel_rec] at h
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, 0, 0, h => by
      simp [__smtx_dt_num_sels, __smtx_dtc_num_sels]
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) d, 0, Nat.succ j, h => by
      have h' : __smtx_ret_typeof_sel_rec (SmtDatatype.sum c d) 0 j ≠ SmtType.None := by
        simpa [__smtx_ret_typeof_sel_rec] using h
      have ih := ret_typeof_sel_rec_non_none_implies_lt (SmtDatatype.sum c d) 0 j h'
      simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using Nat.succ_lt_succ ih
  | SmtDatatype.sum c d, Nat.succ i, j, h => by
      have h' : __smtx_ret_typeof_sel_rec d i j ≠ SmtType.None := by
        simpa [__smtx_ret_typeof_sel_rec] using h
      have ih := ret_typeof_sel_rec_non_none_implies_lt d i j h'
      simpa [__smtx_dt_num_sels] using ih

theorem typeof_apply_value_non_none_cases
    {F X : SmtType}
    (h : __smtx_typeof_apply_value F X ≠ SmtType.None) :
    ∃ A B,
      F = SmtType.DtConsType A B ∧
      X = A ∧
      A ≠ SmtType.None ∧
      B ≠ SmtType.None := by
  cases F with
  | DtConsType A B =>
      cases X <;>
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at h
      all_goals first | contradiction | exact ⟨A, B, rfl, h.2.1.symm, h.1, h.2.2⟩
  | _ =>
      simp [__smtx_typeof_apply_value] at h

theorem dt_cons_chain_type_of_non_none :
    ∀ {v : SmtValue} {s : smt_lit_String} {d : SmtDatatype} {i : smt_lit_Nat},
      __vsm_apply_head v = SmtValue.DtCons s d i ->
      __smtx_typeof_value v ≠ SmtType.None ->
      __smtx_typeof_value v =
        dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (vsm_num_apply_args v)
  | SmtValue.NotValue, s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean b, s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral n, s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational q, s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary w n, s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map m, s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq ss, s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char c, s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan r, s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.DtCons s' d' i', s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
      rcases hHead with ⟨rfl, hEq⟩
      rcases hEq with ⟨rfl, rfl⟩
      simp [__smtx_typeof_value, dt_cons_applied_type_rec, vsm_num_apply_args]
  | SmtValue.Apply f x, s, d, i, hHead, hNN => by
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons s d i := by
        simpa [__vsm_apply_head] using hHead
      have hFunNN : __smtx_typeof_value f ≠ SmtType.None := by
        intro hNone
        apply hNN
        simp [__smtx_typeof_value, hNone, __smtx_typeof_apply_value]
      have ihEq := dt_cons_chain_type_of_non_none hHeadF hFunNN
      have hApplyNN :
          __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value x) ≠ SmtType.None := by
        simpa [__smtx_typeof_value] using hNN
      rcases typeof_apply_value_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
      have hFunEq :
          dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (vsm_num_apply_args f) =
            SmtType.DtConsType A B := by
        simpa [ihEq] using hF
      have hArgs :
          Nat.succ (dt_cons_type_num_args B) =
            __smtx_dt_num_sels (__smtx_dt_substitute s d d) i - vsm_num_apply_args f := by
        have hArgs := congrArg dt_cons_type_num_args hFunEq
        rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
        simpa [dt_cons_type_num_args] using hArgs.symm
      have hlt :
          vsm_num_apply_args f < __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
        omega
      have hStep := dt_cons_applied_type_rec_step s d (__smtx_dt_substitute s d d) i
        (vsm_num_apply_args f) hlt
      have hB' :
          B =
            dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f)) := by
        have hCmp :
            SmtType.DtConsType A B =
              SmtType.DtConsType
                (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                (dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f))) := by
          calc
            SmtType.DtConsType A B =
                dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (vsm_num_apply_args f) := hFunEq.symm
            _ =
                SmtType.DtConsType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                  (dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f))) := hStep
        injection hCmp with _ hB''
      rw [__smtx_typeof_value, hF, hX]
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq,
        hA, vsm_num_apply_args, hB']

theorem vsm_num_apply_args_eq_dt_num_sels_of_datatype
    {v : SmtValue}
    {s : smt_lit_String}
    {d : SmtDatatype}
    {i : smt_lit_Nat}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    vsm_num_apply_args v = __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
  have hChain := dt_cons_chain_type_of_non_none hHead (by simp [hTy])
  have hEq :
      dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (vsm_num_apply_args v) =
        SmtType.Datatype s d := by
    calc
      dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (vsm_num_apply_args v) =
          __smtx_typeof_value v := by symm; exact hChain
      _ = SmtType.Datatype s d := hTy
  have hArgs := congrArg dt_cons_type_num_args hEq
  rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
  simp [dt_cons_type_num_args] at hArgs
  have hle :
      vsm_num_apply_args v ≤ __smtx_dt_num_sels (__smtx_dt_substitute s d d) i :=
    dt_cons_applied_type_rec_non_none_implies_le s d (__smtx_dt_substitute s d d) i
      (vsm_num_apply_args v) (by rw [hEq]; simp)
  omega

theorem apply_arg_nth_type_of_non_none :
    ∀ {v : SmtValue} {s : smt_lit_String} {d : SmtDatatype} {i j : Nat},
      __vsm_apply_head v = SmtValue.DtCons s d i ->
      __smtx_typeof_value v ≠ SmtType.None ->
      j < vsm_num_apply_args v ->
      __smtx_typeof_value (__vsm_apply_arg_nth v j (vsm_num_apply_args v)) =
        __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i j
  | SmtValue.NotValue, s, d, i, j, hHead, hNN, hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean b, s, d, i, j, hHead, hNN, hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral n, s, d, i, j, hHead, hNN, hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational q, s, d, i, j, hHead, hNN, hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary w n, s, d, i, j, hHead, hNN, hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map m, s, d, i, j, hHead, hNN, hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq ss, s, d, i, j, hHead, hNN, hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char c, s, d, i, j, hHead, hNN, hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan r, s, d, i, j, hHead, hNN, hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.DtCons s' d' i', s, d, i, j, hHead, hNN, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Apply f a, s, d, i, j, hHead, hNN, hj => by
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons s d i := by
        simpa [__vsm_apply_head] using hHead
      have hFunNN : __smtx_typeof_value f ≠ SmtType.None := by
        intro hfNone
        apply hNN
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hfNone]
      have hChainF := dt_cons_chain_type_of_non_none hHeadF hFunNN
      have hChainV := dt_cons_chain_type_of_non_none hHead hNN
      have hSuccNN :
          dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f)) ≠
            SmtType.None := by
        intro hNone
        apply hNN
        rw [hChainV]
        simpa [vsm_num_apply_args] using hNone
      have hle :
          Nat.succ (vsm_num_apply_args f) ≤ __smtx_dt_num_sels (__smtx_dt_substitute s d d) i :=
        dt_cons_applied_type_rec_non_none_implies_le s d (__smtx_dt_substitute s d d) i
          (Nat.succ (vsm_num_apply_args f)) hSuccNN
      have hlt :
          vsm_num_apply_args f < __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
        omega
      have hStepF := dt_cons_applied_type_rec_step s d (__smtx_dt_substitute s d d) i
        (vsm_num_apply_args f) hlt
      by_cases hLast : j = vsm_num_apply_args f
      · subst hLast
        have hTyEq :
            __smtx_typeof_apply_value
                (SmtType.DtConsType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                  (dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f))))
                (__smtx_typeof_value a) =
              dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f)) := by
          calc
            __smtx_typeof_apply_value
                (SmtType.DtConsType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                  (dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f))))
                (__smtx_typeof_value a) =
              __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value a) := by
                rw [hChainF, hStepF]
            _ = __smtx_typeof_value (SmtValue.Apply f a) := by rfl
            _ = dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f)) := by
                simpa [vsm_num_apply_args] using hChainV
        have hArgTy :
            __smtx_typeof_value a =
              __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f) := by
          by_cases hRNone :
              smt_lit_Teq
                (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                SmtType.None
          · simp [__smtx_typeof_apply_value, __smtx_typeof_guard, smt_lit_ite, hRNone] at hTyEq
            exact (hSuccNN hTyEq.symm).elim
          · by_cases hEq :
                smt_lit_Teq
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                  (__smtx_typeof_value a)
            · have hEq' :
                  __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f) =
                    __smtx_typeof_value a := by
                simpa [smt_lit_Teq] using hEq
              exact hEq'.symm
            · simp [__smtx_typeof_apply_value, __smtx_typeof_guard, smt_lit_ite, hRNone, hEq] at hTyEq
              exact (hSuccNN hTyEq.symm).elim
        have hcond : SmtEval.smt_lit_nateq (vsm_num_apply_args f) (vsm_num_apply_args f) = true := by
          simp [SmtEval.smt_lit_nateq]
        simpa [__vsm_apply_arg_nth, vsm_num_apply_args, hcond] using hArgTy
      · have hjSucc : j < Nat.succ (vsm_num_apply_args f) := by
          simpa [vsm_num_apply_args] using hj
        have hj' : j < vsm_num_apply_args f := by
          have hle : j ≤ vsm_num_apply_args f := Nat.lt_succ_iff.mp hjSucc
          cases Nat.eq_or_lt_of_le hle with
          | inl hEq' =>
              exact False.elim (hLast hEq')
          | inr hLt =>
              exact hLt
        have hcond : SmtEval.smt_lit_nateq j (vsm_num_apply_args f) = false := by
          simp [SmtEval.smt_lit_nateq, hLast]
        simpa [__vsm_apply_arg_nth, vsm_num_apply_args, hcond] using
          apply_arg_nth_type_of_non_none hHeadF hFunNN hj'

theorem dt_sel_arg_datatype_of_non_none
    {s : smt_lit_String}
    {d : SmtDatatype}
    {i j : smt_lit_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    __smtx_typeof x = SmtType.Datatype s d := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof x <;>
    simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite,
      smt_lit_Teq, h] at ht ⊢
  constructor
  · simpa using ht.1.symm
  · simpa using ht.2.1.symm

theorem dt_sel_term_typeof_of_non_none
    {s : smt_lit_String}
    {d : SmtDatatype}
    {i j : smt_lit_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) = __smtx_ret_typeof_sel s d i j := by
  have hx : __smtx_typeof x = SmtType.Datatype s d := dt_sel_arg_datatype_of_non_none ht
  simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx]

theorem typeof_value_model_eval_dt_sel_wrong
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (d : SmtDatatype)
    (i j : smt_lit_Nat)
    (v : SmtValue)
    (hT : type_inhabited (__smtx_ret_typeof_sel s d i j))
    (hv : __smtx_typeof_value v = SmtType.Datatype s d) :
    __smtx_typeof_value
      (__smtx_map_select
        (__smtx_map_select
          (__smtx_map_select
            (__smtx_model_lookup M smt_lit_wrong_apply_sel_id
              (SmtType.Map SmtType.Int
                (SmtType.Map SmtType.Int
                  (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))))
            (SmtValue.Numeral (smt_lit_nat_to_int i)))
          (SmtValue.Numeral (smt_lit_nat_to_int j)))
        v) = __smtx_ret_typeof_sel s d i j := by
  have hLookup :
      __smtx_typeof_value
        (__smtx_model_lookup M smt_lit_wrong_apply_sel_id
          (SmtType.Map SmtType.Int
            (SmtType.Map SmtType.Int
              (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))))) =
        SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))) :=
    model_total_typed_lookup hM smt_lit_wrong_apply_sel_id
      (SmtType.Map SmtType.Int
        (SmtType.Map SmtType.Int
          (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))))
      (type_inhabited_map (type_inhabited_map (type_inhabited_map hT)))
  rcases map_value_canonical
      (A := SmtType.Int)
      (B := SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))
      hLookup with ⟨m0, hm0⟩
  rw [hm0]
  have hInner0 :
      __smtx_typeof_value
        (__smtx_map_select (SmtValue.Map m0) (SmtValue.Numeral (smt_lit_nat_to_int i))) =
        SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)) := by
    simpa [__smtx_map_select] using
      map_lookup_typed
        (m := m0)
        (A := SmtType.Int)
        (B := SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))
        (i := SmtValue.Numeral (smt_lit_nat_to_int i))
        (by simpa [hm0] using hLookup)
        rfl
  rcases map_value_canonical
      (A := SmtType.Int)
      (B := SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
      hInner0 with ⟨m1, hm1⟩
  rw [hm1]
  have hInner1 :
      __smtx_typeof_value
        (__smtx_map_select (SmtValue.Map m1) (SmtValue.Numeral (smt_lit_nat_to_int j))) =
        SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j) := by
    simpa [__smtx_map_select] using
      map_lookup_typed
        (m := m1)
        (A := SmtType.Int)
        (B := SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
        (i := SmtValue.Numeral (smt_lit_nat_to_int j))
        (by simpa [hm1] using hInner0)
        rfl
  rcases map_value_canonical
      (A := SmtType.Datatype s d)
      (B := __smtx_ret_typeof_sel s d i j)
      hInner1 with ⟨m2, hm2⟩
  rw [hm2]
  simpa [__smtx_map_select] using
    map_lookup_typed
      (m := m2)
      (A := SmtType.Datatype s d)
      (B := __smtx_ret_typeof_sel s d i j)
      (i := v)
      (by simpa [hm2] using hInner1)
      hv

theorem typeof_value_model_eval_dt_sel
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : smt_lit_String)
    (d : SmtDatatype)
    (i j : smt_lit_Nat)
    (x : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
    (hT : type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)))
    (hpresx : __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) := by
  have hx : __smtx_typeof x = SmtType.Datatype s d := dt_sel_arg_datatype_of_non_none ht
  have hResTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) =
        __smtx_ret_typeof_sel s d i j :=
    dt_sel_term_typeof_of_non_none ht
  have hResInh : type_inhabited (__smtx_ret_typeof_sel s d i j) := by
    rw [← hResTy]
    exact hT
  change
    __smtx_typeof_value (__smtx_model_eval_dt_sel M s d i j (__smtx_model_eval M x)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)
  rw [hResTy]
  let v := __smtx_model_eval M x
  have hv : __smtx_typeof_value v = SmtType.Datatype s d := by
    unfold v
    rw [hpresx, hx]
  unfold __smtx_model_eval_dt_sel
  by_cases hHead :
      smt_lit_veq (__vsm_apply_head v) (SmtValue.DtCons s d i)
  · have hHeadEq : __vsm_apply_head v = SmtValue.DtCons s d i := by
      simpa [smt_lit_veq] using hHead
    have hCountSub :
        vsm_num_apply_args v = __smtx_dt_num_sels (__smtx_dt_substitute s d d) i :=
      vsm_num_apply_args_eq_dt_num_sels_of_datatype hHeadEq hv
    have hCount : vsm_num_apply_args v = __smtx_dt_num_sels d i := by
      rw [dt_num_sels_substitute s d d i] at hCountSub
      exact hCountSub
    have hSelNN : __smtx_ret_typeof_sel s d i j ≠ SmtType.None := by
      rw [← hResTy]
      exact ht
    have hltSel :
        j < __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
      exact ret_typeof_sel_rec_non_none_implies_lt
        (__smtx_dt_substitute s d d) i j (by simpa [__smtx_ret_typeof_sel] using hSelNN)
    have hj : j < vsm_num_apply_args v := by
      simpa [hCountSub] using hltSel
    have hArgTy :
        __smtx_typeof_value (__vsm_apply_arg_nth v j (vsm_num_apply_args v)) =
          __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i j :=
      apply_arg_nth_type_of_non_none hHeadEq (by simp [hv]) hj
    have hArgTy' :
        __smtx_typeof_value (__vsm_apply_arg_nth v j (__smtx_dt_num_sels d i)) =
          __smtx_ret_typeof_sel s d i j := by
      simpa [__smtx_ret_typeof_sel, hCount] using hArgTy
    simpa [v, smt_lit_ite, hHead] using hArgTy'
  · simpa [v, smt_lit_ite, hHead] using
      typeof_value_model_eval_dt_sel_wrong M hM s d i j v hResInh hv

theorem dt_tester_arg_datatype_of_non_none
    {s : smt_lit_String}
    {d : SmtDatatype}
    {i : smt_lit_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof x = SmtType.Datatype s d := by
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof x <;>
    simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite,
      smt_lit_Teq, h] at ht ⊢
  rcases ht with ⟨rfl, rfl⟩
  simp

theorem dt_tester_term_typeof_of_non_none
    {s : smt_lit_String}
    {d : SmtDatatype}
    {i : smt_lit_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) = SmtType.Bool := by
  have hx : __smtx_typeof x = SmtType.Datatype s d := dt_tester_arg_datatype_of_non_none ht
  simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx]

theorem typeof_value_model_eval_dt_tester
    (M : SmtModel)
    (s : smt_lit_String)
    (d : SmtDatatype)
    (i : smt_lit_Nat)
    (x : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) := by
  rw [dt_tester_term_typeof_of_non_none ht]
  change
    __smtx_typeof_value (__smtx_model_eval_dt_tester s d i (__smtx_model_eval M x)) =
      SmtType.Bool
  simp [__smtx_model_eval_dt_tester, __smtx_typeof_value]

theorem typeof_apply_non_none_cases
    {F X : SmtType}
    (h : __smtx_typeof_apply F X ≠ SmtType.None) :
    ∃ A B,
      (F = SmtType.Map A B ∨ F = SmtType.DtConsType A B) ∧
      X = A ∧
      A ≠ SmtType.None ∧
      B ≠ SmtType.None := by
  cases F with
  | None => simp [__smtx_typeof_apply] at h
  | Bool => simp [__smtx_typeof_apply] at h
  | Int => simp [__smtx_typeof_apply] at h
  | Real => simp [__smtx_typeof_apply] at h
  | RegLan => simp [__smtx_typeof_apply] at h
  | BitVec w => simp [__smtx_typeof_apply] at h
  | Seq T => simp [__smtx_typeof_apply] at h
  | Char => simp [__smtx_typeof_apply] at h
  | Datatype s d => simp [__smtx_typeof_apply] at h
  | TypeRef s => simp [__smtx_typeof_apply] at h
  | USort n => simp [__smtx_typeof_apply] at h
  | Map A B =>
      cases X <;> simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at h
      all_goals first | contradiction | exact ⟨A, B, Or.inl rfl, h.2.1.symm, h.1, h.2.2⟩
  | DtConsType A B =>
      cases X <;> simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at h
      all_goals first | contradiction | exact ⟨A, B, Or.inr rfl, h.2.1.symm, h.1, h.2.2⟩

theorem typeof_value_model_eval_apply_map
    {f i : SmtValue}
    {A B : SmtType}
    (hf : __smtx_typeof_value f = SmtType.Map A B)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_model_eval_apply f i) = B := by
  rcases map_value_canonical hf with ⟨m, rfl⟩
  simpa [__smtx_model_eval_apply, __smtx_map_select] using
    map_lookup_typed (m := m) (A := A) (B := B) (i := i)
      (by simp [__smtx_typeof_value] at hf; simpa using hf) hi

theorem typeof_value_model_eval_apply_dt
    {f i : SmtValue}
    {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value f = SmtType.DtConsType A B)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_model_eval_apply f i) = B := by
  cases f with
  | NotValue => simp [__smtx_typeof_value] at hf
  | Boolean b => simp [__smtx_typeof_value] at hf
  | Numeral n => simp [__smtx_typeof_value] at hf
  | Rational q => simp [__smtx_typeof_value] at hf
  | Binary w n =>
      cases hWidth : smt_lit_zleq 0 w <;>
        simp [__smtx_typeof_value, smt_lit_ite, hWidth] at hf
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, hMap] at hf
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hf
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at hf
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hf
  | Char c => simp [__smtx_typeof_value] at hf
  | RegLan r => simp [__smtx_typeof_value] at hf
  | DtCons s d n =>
      rw [__smtx_model_eval_apply, __smtx_typeof_value, hf, hi]
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA]
  | Apply f v =>
      rw [__smtx_model_eval_apply, __smtx_typeof_value, hf, hi]
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA]

theorem typeof_value_model_eval_apply_generic
    (M : SmtModel)
    (f x : SmtTerm)
    (hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hpresf : __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f)
    (hpresx : __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x) :
    __smtx_typeof_value (__smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x)) =
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
  rcases typeof_apply_non_none_cases hNN with ⟨A, B, hF, hX, hA, hB⟩
  have hArg : __smtx_typeof_value (__smtx_model_eval M x) = A := by
    simpa [hX] using hpresx
  cases hF with
  | inl hMap =>
      rw [hMap, hX]
      have hFun : __smtx_typeof_value (__smtx_model_eval M f) = SmtType.Map A B := by
        simpa [hMap] using hpresf
      simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA] using
        typeof_value_model_eval_apply_map hFun hArg
  | inr hDt =>
      rw [hDt, hX]
      have hFun : __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtConsType A B := by
        simpa [hDt] using hpresf
      simpa [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hA] using
        typeof_value_model_eval_apply_dt hA hFun hArg

end Smtm
