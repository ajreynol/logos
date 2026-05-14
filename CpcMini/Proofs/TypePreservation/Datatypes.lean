import CpcMini.Proofs.TypePreservation.CoreArith

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Establishes an equality relating `typeof_dt_cons_value_rec` and `typeof_dt_cons_rec_zero`. -/
theorem typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero
    (T : SmtType) :
    ∀ c d,
      __smtx_typeof_dt_cons_value_rec T (SmtDatatype.sum c d) native_nat_zero =
        __smtx_typeof_dt_cons_rec T (SmtDatatype.sum c d) native_nat_zero
  | SmtDatatypeCons.unit, d => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec]
  | SmtDatatypeCons.cons U c, d => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec,
        typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero T c d]

/-- Establishes an equality relating `typeof_dt_cons_value_rec` and `typeof_dt_cons_rec`. -/
theorem typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec
    (T : SmtType) :
    ∀ d n,
      __smtx_typeof_dt_cons_value_rec T d n =
        __smtx_typeof_dt_cons_rec T d n
  | SmtDatatype.null, n => by
      cases n <;> simp [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec]
  | SmtDatatype.sum c d, native_nat_zero =>
      typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec_zero T c d
  | SmtDatatype.sum c d, native_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec, __smtx_typeof_dt_cons_rec] using
        typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec T d n

/-- Shows that evaluating `dt_cons` terms produces values of the expected type. -/
theorem typeof_value_model_eval_dt_cons
    (M : SmtModel)
    (s : native_String)
    (d : SmtDatatype)
    (i : native_Nat)
    (ht : term_has_non_none_type (SmtTerm.DtCons s d i)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s d i) := by
  cases hInh : native_inhabited_type (SmtType.Datatype s d) <;>
  cases hwf : __smtx_type_wf (SmtType.Datatype s d) <;>
    simp [__smtx_model_eval, __smtx_typeof_value, __smtx_typeof, __smtx_typeof_guard_wf,
      term_has_non_none_type, native_ite, hwf, typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec] at ht ⊢

/-- Definition used in the proof development for `dt_cons_type_num_args`. -/
def dt_cons_type_num_args : SmtType -> Nat
  | SmtType.DtcAppType _ U => Nat.succ (dt_cons_type_num_args U)
  | _ => 0

/-- Definition used in the proof development for `dt_cons_applied_type_rec`. -/
def dt_cons_applied_type_rec
    (s : native_String)
    (d0 : SmtDatatype) :
    SmtDatatype -> Nat -> Nat -> SmtType
  | d, i, 0 => __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i
  | SmtDatatype.sum (SmtDatatypeCons.cons _ c) d, 0, Nat.succ n =>
      dt_cons_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n
  | SmtDatatype.sum c d, Nat.succ i, n =>
      dt_cons_applied_type_rec s d0 d i n
  | _, _, _ => SmtType.None

/-- Lemma about `dt_cons_type_num_args_typeof_dt_cons_value_rec`. -/
theorem dt_cons_type_num_args_typeof_dt_cons_value_rec
    (s : native_String)
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

/-- Lemma about `dt_cons_type_num_args_dt_cons_applied_type_rec`. -/
theorem dt_cons_type_num_args_dt_cons_applied_type_rec
    (s : native_String)
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

/-- Lemma about `dt_cons_applied_type_rec_step`. -/
theorem dt_cons_applied_type_rec_step
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i n,
      n < __smtx_dt_num_sels d i ->
      dt_cons_applied_type_rec s d0 d i n =
        SmtType.DtcAppType (__smtx_ret_typeof_sel_rec d i n) (dt_cons_applied_type_rec s d0 d i (Nat.succ n))
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

/-- Shows that `dt_cons_applied_type_rec_non_none` implies `le`. -/
theorem dt_cons_applied_type_rec_non_none_implies_le
    (s : native_String)
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

/-- Shows that `dt_cons_applied_type_rec_eq_bare_type` implies `zero`. -/
theorem dt_cons_applied_type_rec_eq_bare_type_implies_zero
    {s : native_String}
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

/-- Definition used in the proof development for `vsm_num_apply_args`. -/
def vsm_num_apply_args : SmtValue -> Nat
  | SmtValue.Apply f _ => Nat.succ (vsm_num_apply_args f)
  | _ => 0

/-- Lemma about `dtc_num_sels_substitute`. -/
theorem dtc_num_sels_substitute
    (s : native_String)
    (d : SmtDatatype) :
    ∀ c, __smtx_dtc_num_sels (__smtx_dtc_substitute s d c) = __smtx_dtc_num_sels c
  | SmtDatatypeCons.unit => by
      simp [__smtx_dtc_substitute, __smtx_dtc_num_sels]
  | SmtDatatypeCons.cons T c => by
      cases T <;>
        simp [__smtx_dtc_substitute, __smtx_dtc_num_sels,
          dtc_num_sels_substitute s d c, native_ite, native_Teq, native_streq]

/-- Lemma about `dt_num_sels_substitute`. -/
theorem dt_num_sels_substitute
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i, __smtx_dt_num_sels (__smtx_dt_substitute s d0 d) i = __smtx_dt_num_sels d i
  | SmtDatatype.null, i => by
      cases i <;> simp [__smtx_dt_substitute, __smtx_dt_num_sels]
  | SmtDatatype.sum c d, 0 => by
      simp [__smtx_dt_substitute, __smtx_dt_num_sels, dtc_num_sels_substitute]
  | SmtDatatype.sum c d, Nat.succ i => by
      simp [__smtx_dt_substitute, __smtx_dt_num_sels, dt_num_sels_substitute s d0 d i]

/-- Shows that `ret_typeof_sel_rec_non_none` implies `lt`. -/
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

/-- Extracts recursive datatype well-formedness from public type well-formedness. -/
theorem datatype_wf_rec_of_type_wf
    {s : native_String}
    {d : SmtDatatype}
    (h : __smtx_type_wf (SmtType.Datatype s d) = true) :
    __smtx_dt_wf_rec d (native_reflist_insert native_reflist_nil s) = true := by
  have hPair :
      native_inhabited_type (SmtType.Datatype s d) = true ∧
        __smtx_dt_wf_rec d (native_reflist_insert native_reflist_nil s) = true := by
    simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
  exact hPair.2

/-- Enumerates the cases for `typeof_apply_value_non_none`. -/
theorem typeof_apply_value_non_none_cases
    {F X : SmtType}
    (h : __smtx_typeof_apply_value F X ≠ SmtType.None) :
    ∃ A B,
      F = SmtType.DtcAppType A B ∧
      X = A ∧
      A ≠ SmtType.None ∧
      B ≠ SmtType.None := by
  cases F with
  | DtcAppType A B =>
      cases X <;>
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, native_Teq] at h
      all_goals first | contradiction | exact ⟨A, B, rfl, h.2.1.symm, h.1, h.2.2⟩
  | _ =>
      simp [__smtx_typeof_apply_value] at h

/-- Enumerates the cases for `typeof_apply_non_none`. -/
theorem typeof_apply_non_none_cases
    {F X : SmtType}
    (h : __smtx_typeof_apply F X ≠ SmtType.None) :
    ∃ A B,
      (F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B) ∧
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
  | Set T => simp [__smtx_typeof_apply] at h
  | Seq T => simp [__smtx_typeof_apply] at h
  | Char => simp [__smtx_typeof_apply] at h
  | Datatype s d => simp [__smtx_typeof_apply] at h
  | TypeRef s => simp [__smtx_typeof_apply] at h
  | USort n => simp [__smtx_typeof_apply] at h
  | Map A B =>
      simp [__smtx_typeof_apply] at h
  | FunType A B =>
      cases X <;> simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq] at h
      all_goals first | contradiction | exact ⟨A, B, Or.inl rfl, h.2.1.symm, h.1, h.2.2⟩
  | DtcAppType A B =>
      cases X <;> simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq] at h
      all_goals first | contradiction | exact ⟨A, B, Or.inr rfl, h.2.1.symm, h.1, h.2.2⟩

/-- Derives `dt_cons_chain_type` from `non_none`. -/
theorem dt_cons_chain_type_of_non_none :
    ∀ {v : SmtValue} {s : native_String} {d : SmtDatatype} {i : native_Nat},
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
      have hTy :
          __smtx_typeof_value (SmtValue.DtCons s' d' i') =
            __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s' d') (__smtx_dt_substitute s' d' d') i' := by
        symm
        exact typeof_value_dt_cons_inner_eq_of_eq_non_none rfl hNN
      rw [hTy]
      simp [dt_cons_applied_type_rec, vsm_num_apply_args]
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
        intro hNone
        apply hNN
        simp [__smtx_typeof_value, hNone]
      rcases typeof_apply_value_non_none_cases hApplyNN with ⟨A, B, hF, hX, hA, hB⟩
      have hFunEq :
          dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (vsm_num_apply_args f) =
            SmtType.DtcAppType A B := by
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
            SmtType.DtcAppType A B =
              SmtType.DtcAppType
                (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                (dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f))) := by
          calc
            SmtType.DtcAppType A B =
                dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (vsm_num_apply_args f) := hFunEq.symm
            _ =
                SmtType.DtcAppType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                  (dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f))) := hStep
        injection hCmp with _ hB''
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, native_Teq,
        __smtx_typeof_value, hF, hX, hA, vsm_num_apply_args, hB']

/-- Derives `vsm_num_apply_args_eq_dt_num_sels` from `datatype`. -/
theorem vsm_num_apply_args_eq_dt_num_sels_of_datatype
    {v : SmtValue}
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
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

/-- Derives `apply_arg_nth_type` from `non_none`. -/
theorem apply_arg_nth_type_of_non_none :
    ∀ {v : SmtValue} {s : native_String} {d : SmtDatatype} {i j : Nat},
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
                (SmtType.DtcAppType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                  (dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f))))
                (__smtx_typeof_value a) =
              dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f)) := by
          calc
            __smtx_typeof_apply_value
                (SmtType.DtcAppType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                  (dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f))))
                (__smtx_typeof_value a) =
              __smtx_typeof_apply_value (__smtx_typeof_value f) (__smtx_typeof_value a) := by
                rw [hChainF, hStepF]
            _ = __smtx_typeof_value (SmtValue.Apply f a) := by
                simp [__smtx_typeof_value]
            _ = dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i (Nat.succ (vsm_num_apply_args f)) := by
                simpa [vsm_num_apply_args] using hChainV
        have hArgTy :
            __smtx_typeof_value a =
              __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f) := by
          by_cases hRNone :
              native_Teq
                (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                SmtType.None
          · simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hRNone] at hTyEq
            exact (hSuccNN hTyEq.symm).elim
          · by_cases hEq :
                native_Teq
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f))
                  (__smtx_typeof_value a)
            · have hEq' :
                  __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i (vsm_num_apply_args f) =
                    __smtx_typeof_value a := by
                simpa [native_Teq] using hEq
              exact hEq'.symm
            · simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, hRNone, hEq] at hTyEq
              exact (hSuccNN hTyEq.symm).elim
        have hcond : SmtEval.native_nateq (vsm_num_apply_args f) (vsm_num_apply_args f) = true := by
          simp [SmtEval.native_nateq]
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
        have hcond : SmtEval.native_nateq j (vsm_num_apply_args f) = false := by
          simp [SmtEval.native_nateq, hLast]
        simpa [__vsm_apply_arg_nth, vsm_num_apply_args, hcond] using
          apply_arg_nth_type_of_non_none hHeadF hFunNN hj'

/-- Derives `dt_sel_arg_datatype` from `non_none`. -/
theorem dt_sel_arg_datatype_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    __smtx_typeof x = SmtType.Datatype s d := by
  let R := __smtx_ret_typeof_sel s d i j
  let inner := __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R) (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    simpa [term_has_non_none_type, __smtx_typeof, R, inner] using ht
  have hGuard : __smtx_typeof_guard_wf R inner = inner :=
    smtx_typeof_guard_wf_of_non_none R inner hGuardNN
  have hInnerNN : inner ≠ SmtType.None := by
    intro hNone
    apply hGuardNN
    rw [hGuard, hNone]
  by_cases hTypeEq : SmtType.Datatype s d = __smtx_typeof x
  · exact hTypeEq.symm
  · exfalso
    apply hInnerNN
    simp [inner, __smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hTypeEq]

/-- Derives `dt_sel_term_typeof` from `non_none`. -/
theorem dt_sel_term_typeof_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) = __smtx_ret_typeof_sel s d i j := by
  have hx : __smtx_typeof x = SmtType.Datatype s d := dt_sel_arg_datatype_of_non_none ht
  let R := __smtx_ret_typeof_sel s d i j
  let inner := __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R) (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    simpa [term_has_non_none_type, __smtx_typeof, R, inner] using ht
  have hGuard : __smtx_typeof_guard_wf R inner = inner :=
    smtx_typeof_guard_wf_of_non_none R inner hGuardNN
  calc
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) =
        inner := by
      simpa [__smtx_typeof, R, inner] using hGuard
    _ = __smtx_ret_typeof_sel s d i j := by
      simp [inner, R, __smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hx]

/-- Turns a computed type equality into a non-`None` fact. -/
private theorem term_has_non_none_of_type_eq
    {t : SmtTerm}
    {T : SmtType}
    (h : __smtx_typeof t = T)
    (hT : T ≠ SmtType.None) :
    term_has_non_none_type t := by
  unfold term_has_non_none_type
  rw [h]
  exact hT

private def result_datatype_components_wf : SmtType -> Prop
  | SmtType.Datatype s d => __smtx_type_wf (SmtType.Datatype s d) = true
  | SmtType.Map _ B => result_datatype_components_wf B
  | SmtType.FunType _ B => result_datatype_components_wf B
  | SmtType.DtcAppType _ B => result_datatype_components_wf B
  | _ => True

private theorem result_datatype_components_wf_of_type_wf
    {T : SmtType} (h : __smtx_type_wf T = true) :
    result_datatype_components_wf T := by
  let rec go (T : SmtType) (h : __smtx_type_wf T = true) :
      result_datatype_components_wf T := by
    cases T
    case Datatype s d =>
      exact h
    case Map A B =>
      exact go B (map_type_wf_components_of_wf h).2
    case FunType A B =>
      exact go B (fun_type_wf_components_of_wf h).2
    case DtcAppType A B =>
      simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at h
    all_goals
      simp [result_datatype_components_wf]
  exact go T h

private theorem result_datatype_components_wf_typeof_eq
    (T U : SmtType) :
    result_datatype_components_wf (__smtx_typeof_eq T U) := by
  cases T <;> cases U <;>
    (simp [__smtx_typeof_eq, __smtx_typeof_guard,
      result_datatype_components_wf, native_ite, native_Teq] <;>
      repeat split <;>
      simp [result_datatype_components_wf])

private theorem result_datatype_components_wf_dt_tester_apply
    (s : native_String) (d : SmtDatatype) (i : native_Nat) (x : SmtTerm) :
    result_datatype_components_wf
      (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) := by
  rw [__smtx_typeof.eq_17]
  by_cases hCons :
      __smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i =
        SmtType.None
  · simp [__smtx_typeof_apply, __smtx_typeof_guard,
      result_datatype_components_wf, native_ite, native_Teq, hCons]
  cases __smtx_typeof x <;>
    (simp [__smtx_typeof_apply, __smtx_typeof_guard,
      result_datatype_components_wf, native_ite, native_Teq, hCons] <;>
      repeat split <;>
      simp [result_datatype_components_wf])

private theorem result_datatype_components_wf_dt_cons_rec
    (T : SmtType) (hT : result_datatype_components_wf T) :
    ∀ (d : SmtDatatype) (i : native_Nat),
      result_datatype_components_wf (__smtx_typeof_dt_cons_rec T d i)
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero => by
      simpa [__smtx_typeof_dt_cons_rec] using hT
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero => by
      simpa [__smtx_typeof_dt_cons_rec, result_datatype_components_wf] using
        result_datatype_components_wf_dt_cons_rec T hT
          (SmtDatatype.sum c d) native_nat_zero
  | SmtDatatype.sum c d, native_nat_succ i => by
      simpa [__smtx_typeof_dt_cons_rec] using
        result_datatype_components_wf_dt_cons_rec T hT d i
  | SmtDatatype.null, i => by
      cases i <;> simp [__smtx_typeof_dt_cons_rec, result_datatype_components_wf]

private theorem generic_apply_type_of_not_special
    {f x : SmtTerm}
    (hNoSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hNoTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x :=
  __smtx_typeof.eq_18 f x
    (by intro s d i j hEq; exact hNoSel s d i j hEq)
    (by intro s d i hEq; exact hNoTester s d i hEq)

private theorem term_result_datatype_components_wf_of_non_none
    (x : SmtTerm) (hxNN : term_has_non_none_type x) :
    result_datatype_components_wf (__smtx_typeof x) := by
  let rec go (x : SmtTerm) (hxNN : term_has_non_none_type x) :
      result_datatype_components_wf (__smtx_typeof x) := by
    cases x
    case Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof, result_datatype_components_wf, native_and,
            native_ite, hWidth, hMod]
    case Var s T =>
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      rw [show __smtx_typeof (SmtTerm.Var s T) = T by
        simpa [__smtx_typeof] using smtx_typeof_guard_wf_of_non_none T T hGuardNN]
      exact result_datatype_components_wf_of_type_wf hWf
    case UConst s T =>
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof] using hxNN
      have hWf : __smtx_type_wf T = true :=
        smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
      rw [show __smtx_typeof (SmtTerm.UConst s T) = T by
        simpa [__smtx_typeof] using smtx_typeof_guard_wf_of_non_none T T hGuardNN]
      exact result_datatype_components_wf_of_type_wf hWf
    case ite c t1 t2 =>
      rcases ite_args_of_non_none hxNN with ⟨T, hc, h1, h2, hTNN⟩
      have ht1NN : term_has_non_none_type t1 :=
        term_has_non_none_of_type_eq h1 hTNN
      have ht1Good := go t1 ht1NN
      rw [typeof_ite_eq]
      simp [__smtx_typeof_ite, native_ite, native_Teq, hc, h1, h2]
      simpa [h1] using ht1Good
    case eq t1 t2 =>
      rw [typeof_eq_eq]
      exact result_datatype_components_wf_typeof_eq (__smtx_typeof t1) (__smtx_typeof t2)
    case «exists» s T body =>
      cases h : __smtx_typeof body <;>
        simp [__smtx_typeof, result_datatype_components_wf, native_ite, native_Teq, h]
    case «forall» s T body =>
      cases h : __smtx_typeof body <;>
        simp [__smtx_typeof, result_datatype_components_wf, native_ite, native_Teq, h]
    case choice_nth s T body n =>
      induction n generalizing s T body with
      | zero =>
          have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
            unfold term_has_non_none_type at hxNN
            cases hBody : __smtx_typeof body <;>
              simp [__smtx_typeof, __smtx_typeof_choice_nth, native_ite,
                native_Teq, hBody] at hxNN ⊢
            exact hxNN
          have hWf : __smtx_type_wf T = true :=
            smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
          rw [choice_nth_zero_typeof_of_non_none hxNN]
          exact result_datatype_components_wf_of_type_wf hWf
      | succ n ih =>
          cases body with
          | «exists» s' U body' =>
              have hTyEq :
                  __smtx_typeof
                      (SmtTerm.choice_nth s T
                        (SmtTerm.exists s' U body') (Nat.succ n)) =
                    __smtx_typeof (SmtTerm.choice_nth s' U body' n) := by
                simp [__smtx_typeof, __smtx_typeof_choice_nth]
              have hNN' : term_has_non_none_type
                  (SmtTerm.choice_nth s' U body' n) := by
                unfold term_has_non_none_type at hxNN ⊢
                rw [← hTyEq]
                exact hxNN
              simpa [hTyEq] using ih s' U body' hNN'
          | _ =>
              exfalso
              unfold term_has_non_none_type at hxNN
              simp [__smtx_typeof, __smtx_typeof_choice_nth] at hxNN
    case DtCons s d i =>
      let raw :=
        __smtx_typeof_dt_cons_rec (SmtType.Datatype s d)
          (__smtx_dt_substitute s d d) i
      have hGuardNN : __smtx_typeof_guard_wf (SmtType.Datatype s d) raw ≠
          SmtType.None := by
        unfold term_has_non_none_type at hxNN
        simpa [__smtx_typeof, raw] using hxNN
      rw [show __smtx_typeof (SmtTerm.DtCons s d i) = raw by
        simpa [__smtx_typeof, raw] using
          smtx_typeof_guard_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN]
      have hBaseWf : __smtx_type_wf (SmtType.Datatype s d) = true :=
        smtx_typeof_guard_wf_wf_of_non_none (SmtType.Datatype s d) raw hGuardNN
      exact result_datatype_components_wf_dt_cons_rec (SmtType.Datatype s d)
        (by simpa [result_datatype_components_wf] using hBaseWf)
        (__smtx_dt_substitute s d d) i
    case Apply f x =>
      by_cases hSelWitness : ∃ s d i j, f = SmtTerm.DtSel s d i j
      · rcases hSelWitness with ⟨s, d, i, j, rfl⟩
        let R := __smtx_ret_typeof_sel s d i j
        let inner :=
          __smtx_typeof_apply (SmtType.FunType (SmtType.Datatype s d) R)
            (__smtx_typeof x)
        have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
          unfold term_has_non_none_type at hxNN
          simpa [__smtx_typeof, R, inner] using hxNN
        have hWf : __smtx_type_wf R = true :=
          smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
        rw [dt_sel_term_typeof_of_non_none hxNN]
        exact result_datatype_components_wf_of_type_wf hWf
      · by_cases hTesterWitness : ∃ s d i, f = SmtTerm.DtTester s d i
        · rcases hTesterWitness with ⟨s, d, i, rfl⟩
          exact result_datatype_components_wf_dt_tester_apply s d i x
        · have hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j := by
            intro s d i j hEq
            exact hSelWitness ⟨s, d, i, j, hEq⟩
          have hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i := by
            intro s d i hEq
            exact hTesterWitness ⟨s, d, i, hEq⟩
          have hTy : generic_apply_type f x :=
            generic_apply_type_of_not_special hSel hTester
          have hTyEq :
              __smtx_typeof (SmtTerm.Apply f x) =
                __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := hTy
          have hApplyNN :
              __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
                SmtType.None := by
            intro hNone
            unfold term_has_non_none_type at hxNN
            rw [hTyEq, hNone] at hxNN
            exact hxNN rfl
          rcases typeof_apply_non_none_cases hApplyNN with
            ⟨A, B, hHead, hX, hA, _hB⟩
          have hfNN : term_has_non_none_type f := by
            unfold term_has_non_none_type
            rcases hHead with hF | hF <;> rw [hF] <;> simp
          have hfGood := go f hfNN
          have hApplyTy :
              __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) = B := by
            rcases hHead with hF | hF
            · rw [hF, hX]
              simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
                native_Teq, hA]
            · rw [hF, hX]
              simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite,
                native_Teq, hA]
          rw [hTyEq, hApplyTy]
          rcases hHead with hF | hF
          · simpa [hF, result_datatype_components_wf] using hfGood
          · simpa [hF, result_datatype_components_wf] using hfGood
    case not t =>
      cases h : __smtx_typeof t <;>
        simp [__smtx_typeof, result_datatype_components_wf, native_ite, native_Teq, h]
    case or t1 t2 =>
      cases h1 : __smtx_typeof t1 <;>
        cases h2 : __smtx_typeof t2 <;>
          simp [__smtx_typeof, result_datatype_components_wf, native_ite, native_Teq, h1, h2]
    case and t1 t2 =>
      cases h1 : __smtx_typeof t1 <;>
        cases h2 : __smtx_typeof t2 <;>
          simp [__smtx_typeof, result_datatype_components_wf, native_ite, native_Teq, h1, h2]
    case imp t1 t2 =>
      cases h1 : __smtx_typeof t1 <;>
        cases h2 : __smtx_typeof t2 <;>
          simp [__smtx_typeof, result_datatype_components_wf, native_ite, native_Teq, h1, h2]
    all_goals
      repeat split
      all_goals
      simp [result_datatype_components_wf, __smtx_typeof, __smtx_typeof_eq,
        __smtx_typeof_guard, native_ite, native_Teq]
  exact go x hxNN

/-- Extracts well-formedness of a datatype-typed term. -/
private theorem smt_datatype_wf_of_non_none_type
    (x : SmtTerm) (s : native_String) (d : SmtDatatype)
    (hxTy : __smtx_typeof x = SmtType.Datatype s d) :
    __smtx_type_wf (SmtType.Datatype s d) = true := by
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    simp
  have hGood := term_result_datatype_components_wf_of_non_none x hxNN
  rw [hxTy] at hGood
  simpa [result_datatype_components_wf] using hGood

/-- Extracts well-formedness of the tail of a well-formed datatype constructor. -/
private theorem dt_cons_wf_rec_tail_of_true
    {T : SmtType} {c : SmtDatatypeCons} {refs : RefList}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases T <;> simp [__smtx_dt_cons_wf_rec, native_ite] at h ⊢
  all_goals first | exact h.2 | exact h.2.2

/-- Extracts constructor well-formedness from datatype well-formedness. -/
private theorem dt_wf_cons_of_wf
    {c : SmtDatatypeCons} {d : SmtDatatype} {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases d with
  | null =>
      simpa [__smtx_dt_wf_rec] using h
  | sum cTail dTail =>
      cases hc : __smtx_dt_cons_wf_rec c refs <;>
        simp [__smtx_dt_wf_rec, native_ite, hc] at h ⊢

/-- Extracts tail well-formedness from nonempty datatype well-formedness. -/
private theorem dt_wf_tail_of_nonempty_tail_wf
    {c cTail : SmtDatatypeCons}
    {dTail : SmtDatatype}
    {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c (SmtDatatype.sum cTail dTail)) refs = true) :
    __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true := by
  have hc : __smtx_dt_cons_wf_rec c refs = true :=
    dt_wf_cons_of_wf h
  simpa [__smtx_dt_wf_rec, native_ite, hc] using h

/-- Selector return types of well-formed datatypes are never `RegLan`. -/
private theorem ret_typeof_sel_rec_substitute_ne_reglan_of_cons_wf
    (sub : native_String) (base : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (d : SmtDatatype) (j : native_Nat) {refs : RefList},
      __smtx_dt_cons_wf_rec c refs = true ->
        __smtx_ret_typeof_sel_rec
            (SmtDatatype.sum (__smtx_dtc_substitute sub base c)
              (__smtx_dt_substitute sub base d)) native_nat_zero j ≠
          SmtType.RegLan
  | SmtDatatypeCons.unit, d, j, refs, _hWf => by
      cases j <;> simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec]
  | SmtDatatypeCons.cons T c, d, native_nat_zero, refs, hWf => by
      cases T
      case TypeRef r =>
        by_cases hEq : r = sub <;>
          simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
            __smtx_type_wf_rec, __smtx_ret_typeof_sel_rec, native_ite,
            native_Teq, native_streq, hEq] at hWf ⊢
      all_goals
        simp [__smtx_dtc_substitute, __smtx_dt_cons_wf_rec,
          __smtx_type_wf_rec, __smtx_ret_typeof_sel_rec, native_ite,
          native_Teq, native_streq] at hWf ⊢
  | SmtDatatypeCons.cons T c, d, native_nat_succ j, refs, hWf => by
      have hTail : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWf
      cases T <;>
        simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec] using
          ret_typeof_sel_rec_substitute_ne_reglan_of_cons_wf sub base
            c d j hTail

private theorem ret_typeof_sel_rec_substitute_ne_reglan_of_dt_wf
    (sub : native_String) (base : SmtDatatype) :
    ∀ (d : SmtDatatype) (i j : native_Nat) {refs : RefList},
      __smtx_dt_wf_rec d refs = true ->
        __smtx_ret_typeof_sel_rec (__smtx_dt_substitute sub base d) i j ≠
          SmtType.RegLan
  | SmtDatatype.null, i, j, refs, _hWf => by
      cases i <;> cases j <;>
        simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec]
  | SmtDatatype.sum c d, native_nat_zero, j, refs, hWf => by
      have hCons : __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWf
      simpa [__smtx_dt_substitute] using
        ret_typeof_sel_rec_substitute_ne_reglan_of_cons_wf sub base
          c d j hCons
  | SmtDatatype.sum c d, native_nat_succ i, j, refs, hWf => by
      cases d with
      | null =>
          simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec]
      | sum cTail dTail =>
          have hTail :
              __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true :=
            dt_wf_tail_of_nonempty_tail_wf hWf
          simpa [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec] using
            ret_typeof_sel_rec_substitute_ne_reglan_of_dt_wf sub base
              (SmtDatatype.sum cTail dTail) i j hTail

private theorem ret_typeof_sel_ne_reglan_of_datatype_wf
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    (hWf : __smtx_type_wf (SmtType.Datatype s d) = true) :
    __smtx_ret_typeof_sel s d i j ≠ SmtType.RegLan := by
  have hDtWf : __smtx_dt_wf_rec d (native_reflist_insert native_reflist_nil s) = true :=
    datatype_wf_rec_of_type_wf hWf
  simpa [__smtx_ret_typeof_sel] using
    ret_typeof_sel_rec_substitute_ne_reglan_of_dt_wf s d d i j hDtWf

private theorem type_wf_parts_of_wf_ne_reglan
    {T : SmtType}
    (hWf : __smtx_type_wf T = true)
    (hNe : T ≠ SmtType.RegLan) :
    native_inhabited_type T = true ∧
      __smtx_type_wf_rec T native_reflist_nil = true := by
  cases T <;> simp [__smtx_type_wf, native_and] at hWf hNe ⊢
  all_goals first | contradiction | exact hWf | exact ⟨hWf, rfl⟩

private theorem int_inhabited_bool :
    native_inhabited_type SmtType.Int = true :=
  native_inhabited_type_of_type_inhabited
    (T := SmtType.Int) ⟨SmtValue.Numeral 0, rfl⟩

/-- The model fallback used for wrong datatype-selector applications is well-formed. -/
theorem dt_sel_wrong_map_type_wf_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    __smtx_type_wf
      (SmtType.Map SmtType.Int
        (SmtType.Map SmtType.Int
          (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true := by
  let R := __smtx_ret_typeof_sel s d i j
  let D := SmtType.Datatype s d
  let M3 := SmtType.Map D R
  let M2 := SmtType.Map SmtType.Int M3
  let M1 := SmtType.Map SmtType.Int M2
  have hxTy : __smtx_typeof x = D := by
    simpa [D] using dt_sel_arg_datatype_of_non_none ht
  have hDTWf : __smtx_type_wf D = true := by
    simpa [D] using smt_datatype_wf_of_non_none_type x s d hxTy
  let inner :=
    __smtx_typeof_apply (SmtType.FunType D R) (__smtx_typeof x)
  have hGuardNN : __smtx_typeof_guard_wf R inner ≠ SmtType.None := by
    unfold term_has_non_none_type at ht
    simpa [R, D, inner, __smtx_typeof] using ht
  have hRWf : __smtx_type_wf R = true :=
    smtx_typeof_guard_wf_wf_of_non_none R inner hGuardNN
  have hRNe : R ≠ SmtType.RegLan := by
    simpa [R, D] using
      ret_typeof_sel_ne_reglan_of_datatype_wf
        (s := s) (d := d) (i := i) (j := j) hDTWf
  have hRParts :
      native_inhabited_type R = true ∧
        __smtx_type_wf_rec R native_reflist_nil = true :=
    type_wf_parts_of_wf_ne_reglan hRWf hRNe
  have hDTParts :
      native_inhabited_type D = true ∧
        __smtx_type_wf_rec D native_reflist_nil = true :=
    type_wf_parts_of_wf_ne_reglan hDTWf (by simp [D])
  have hRInh : type_inhabited R :=
    type_inhabited_of_type_wf R hRWf
  have hM3Inh : type_inhabited M3 := by
    exact type_inhabited_map (A := D) (B := R) hRInh
  have hM3InhBool : native_inhabited_type M3 = true :=
    native_inhabited_type_of_type_inhabited hM3Inh
  have hM3Rec : __smtx_type_wf_rec M3 native_reflist_nil = true := by
    simp [M3, __smtx_type_wf_rec, native_and, hDTParts.1,
      hDTParts.2, hRParts.1, hRParts.2]
  have hM2Inh : type_inhabited M2 := by
    exact type_inhabited_map (A := SmtType.Int) (B := M3) hM3Inh
  have hM2InhBool : native_inhabited_type M2 = true :=
    native_inhabited_type_of_type_inhabited hM2Inh
  have hM2Rec : __smtx_type_wf_rec M2 native_reflist_nil = true := by
    simp [M2, __smtx_type_wf_rec, native_and, int_inhabited_bool,
      hM3InhBool, hM3Rec]
  have hM1Inh : type_inhabited M1 := by
    exact type_inhabited_map (A := SmtType.Int) (B := M2) hM2Inh
  have hM1InhBool : native_inhabited_type M1 = true :=
    native_inhabited_type_of_type_inhabited hM1Inh
  have hM1Rec : __smtx_type_wf_rec M1 native_reflist_nil = true := by
    simp [M1, __smtx_type_wf_rec, native_and, int_inhabited_bool,
      hM2InhBool, hM2Rec]
  simpa [M1, M2, M3, D, R] using
    type_wf_of_inhabited_and_wf_rec hM1InhBool hM1Rec

/-- Shows that evaluating `dt_sel_wrong` terms produces values of the expected type. -/
theorem typeof_value_model_eval_dt_sel_wrong
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (d : SmtDatatype)
    (i j : native_Nat)
    (v : SmtValue)
    (hT : type_inhabited (__smtx_ret_typeof_sel s d i j))
    (hMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true)
    (hv : __smtx_typeof_value v = SmtType.Datatype s d) :
    __smtx_typeof_value
      (__smtx_map_select
        (__smtx_map_select
          (__smtx_map_select
            (__smtx_model_lookup M native_wrong_apply_sel_id
              (SmtType.Map SmtType.Int
                (SmtType.Map SmtType.Int
                  (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))))
            (SmtValue.Numeral (native_nat_to_int i)))
          (SmtValue.Numeral (native_nat_to_int j)))
        v) = __smtx_ret_typeof_sel s d i j := by
  have hLookup :
      __smtx_typeof_value
        (__smtx_model_lookup M native_wrong_apply_sel_id
          (SmtType.Map SmtType.Int
            (SmtType.Map SmtType.Int
              (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))))) =
        SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))) :=
    model_total_typed_lookup hM native_wrong_apply_sel_id
      (SmtType.Map SmtType.Int
        (SmtType.Map SmtType.Int
          (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))))
      hMapWF
  rcases map_value_canonical
      (A := SmtType.Int)
      (B := SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))
      hLookup with ⟨m0, hm0⟩
  rw [hm0]
  have hInner0 :
      __smtx_typeof_value
        (__smtx_map_select (SmtValue.Map m0) (SmtValue.Numeral (native_nat_to_int i))) =
        SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)) := by
    simpa [__smtx_map_select] using
      map_lookup_typed
        (m := m0)
        (A := SmtType.Int)
        (B := SmtType.Map SmtType.Int (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))
        (i := SmtValue.Numeral (native_nat_to_int i))
        (by simpa [hm0] using hLookup)
        rfl
  rcases map_value_canonical
      (A := SmtType.Int)
      (B := SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
      hInner0 with ⟨m1, hm1⟩
  rw [hm1]
  have hInner1 :
      __smtx_typeof_value
        (__smtx_map_select (SmtValue.Map m1) (SmtValue.Numeral (native_nat_to_int j))) =
        SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j) := by
    simpa [__smtx_map_select] using
      map_lookup_typed
        (m := m1)
        (A := SmtType.Int)
        (B := SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
        (i := SmtValue.Numeral (native_nat_to_int j))
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

/-- Shows that evaluating `dt_sel` terms produces values of the expected type. -/
theorem typeof_value_model_eval_dt_sel
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (d : SmtDatatype)
    (i j : native_Nat)
    (x : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x))
    (hWrongMapWF :
      __smtx_type_wf
        (SmtType.Map SmtType.Int
          (SmtType.Map SmtType.Int
            (SmtType.Map (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j)))) = true)
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
  rw [show __smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) =
      __smtx_model_eval_dt_sel M s d i j (__smtx_model_eval M x) by
    simp [__smtx_model_eval]]
  rw [hResTy]
  let v := __smtx_model_eval M x
  have hv : __smtx_typeof_value v = SmtType.Datatype s d := by
    unfold v
    rw [hpresx, hx]
  unfold __smtx_model_eval_dt_sel
  by_cases hHead :
      native_veq (__vsm_apply_head v) (SmtValue.DtCons s d i)
  · have hHeadEq : __vsm_apply_head v = SmtValue.DtCons s d i := by
      simpa [native_veq] using hHead
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
    simpa [v, native_ite, hHead] using hArgTy'
  · simpa [v, native_ite, hHead] using
      typeof_value_model_eval_dt_sel_wrong M hM s d i j v hResInh hWrongMapWF hv

/-- Derives that the tested constructor index is valid from `non_none`. -/
theorem dt_tester_constructor_type_non_none_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof_dt_cons_rec (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i ≠
      SmtType.None := by
  intro hCons
  unfold term_has_non_none_type at ht
  apply ht
  rw [__smtx_typeof.eq_17]
  simp [__smtx_typeof_guard, native_ite, native_Teq, hCons]

/-- Derives `dt_tester_arg_datatype` from `non_none`. -/
theorem dt_tester_arg_datatype_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof x = SmtType.Datatype s d := by
  have hCons : __smtx_typeof_dt_cons_rec
      (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i ≠ SmtType.None :=
    dt_tester_constructor_type_non_none_of_non_none ht
  unfold term_has_non_none_type at ht
  cases h : __smtx_typeof x <;>
    simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, native_ite,
      native_Teq, h, hCons] at ht ⊢
  exact ⟨ht.1.symm, ht.2.symm⟩

/-- Derives `dt_tester_term_typeof` from `non_none`. -/
theorem dt_tester_term_typeof_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) = SmtType.Bool := by
  have hCons : __smtx_typeof_dt_cons_rec
      (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i ≠ SmtType.None :=
    dt_tester_constructor_type_non_none_of_non_none ht
  have hx : __smtx_typeof x = SmtType.Datatype s d := dt_tester_arg_datatype_of_non_none ht
  simp [__smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq,
    hx, hCons]

/-- Shows that evaluating `dt_tester` terms produces values of the expected type. -/
theorem typeof_value_model_eval_dt_tester
    (M : SmtModel)
    (s : native_String)
    (d : SmtDatatype)
    (i : native_Nat)
    (x : SmtTerm)
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) :
    __smtx_typeof_value (__smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtTester s d i) x)) =
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) := by
  rw [dt_tester_term_typeof_of_non_none ht]
  rw [show __smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtTester s d i) x) =
      __smtx_model_eval_dt_tester s d i (__smtx_model_eval M x) by
    simp [__smtx_model_eval]]
  simp [__smtx_model_eval_dt_tester, __smtx_typeof_value]

/-- Shows that evaluating `apply_fun` terms produces values of the expected type. -/
theorem typeof_value_model_eval_apply_fun
    {m : SmtMap}
    {i : SmtValue}
    {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value (SmtValue.Fun m) = SmtType.FunType A B)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_model_eval_apply (SmtValue.Fun m) i) = B := by
  have hiNN : i ≠ SmtValue.NotValue := by
    intro h
    cases h
    simp [__smtx_typeof_value] at hi
    exact hA hi.symm
  cases typeof_map_value_shape m with
  | inl hMap =>
      rcases hMap with ⟨T, U, hMap⟩
      have hFun : SmtType.FunType T U = SmtType.FunType A B := by
        simpa [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] using hf
      cases hFun
      cases i <;> first
        | exact (hiNN rfl).elim
        | simpa [__smtx_model_eval_apply, __smtx_map_select] using
            map_lookup_typed (m := m) (A := A) (B := B) (by simpa using hMap) hi
  | inr hNone =>
      simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at hf

/-- Shows that applying any function-typed value produces a value of the codomain type. -/
theorem typeof_value_model_eval_apply_fun_value
    {f i : SmtValue}
    {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value f = SmtType.FunType A B)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_model_eval_apply f i) = B := by
  rcases fun_value_canonical hf with ⟨m, rfl⟩
  exact typeof_value_model_eval_apply_fun hA hf hi

/-- Shows that evaluating `apply_dt` terms produces values of the expected type. -/
theorem typeof_value_model_eval_apply_dt
    {f i : SmtValue}
    {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value f = SmtType.DtcAppType A B)
    (hi : __smtx_typeof_value i = A) :
    __smtx_typeof_value (__smtx_model_eval_apply f i) = B := by
  have hiNN : i ≠ SmtValue.NotValue := by
    intro h
    cases h
    simp [__smtx_typeof_value] at hi
    exact hA hi.symm
  have hDtConsApply :
      ∀ {s : native_String} {d : SmtDatatype} {n : native_Nat} {j : SmtValue},
        j ≠ SmtValue.NotValue ->
        __smtx_model_eval_apply (SmtValue.DtCons s d n) j =
          SmtValue.Apply (SmtValue.DtCons s d n) j := by
    intro s d n j hj
    cases j <;> simp [__smtx_model_eval_apply] at hj ⊢
  have hApplyApply :
      ∀ {f v j : SmtValue},
        j ≠ SmtValue.NotValue ->
        __smtx_model_eval_apply (SmtValue.Apply f v) j =
          SmtValue.Apply (SmtValue.Apply f v) j := by
    intro f v j hj
    cases j <;> simp [__smtx_model_eval_apply] at hj ⊢
  cases f with
  | NotValue => simp [__smtx_typeof_value] at hf
  | Boolean b => simp [__smtx_typeof_value] at hf
  | Numeral n => simp [__smtx_typeof_value] at hf
  | Rational q => simp [__smtx_typeof_value] at hf
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and, hWidth, hMod] at hf
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, hMap] at hf
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hf
  | Fun m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hMap] at hf
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_fun_type, hNone] at hf
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          cases U <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at hf
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at hf
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at hf
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at hf
  | Char c => simp [__smtx_typeof_value] at hf
  | UValue k e => simp [__smtx_typeof_value] at hf
  | RegLan r => simp [__smtx_typeof_value] at hf
  | DtCons s d n =>
      have hOuter :
          __smtx_typeof_value (SmtValue.Apply (SmtValue.DtCons s d n) i) =
            __smtx_typeof_apply_value
              (__smtx_typeof_value (SmtValue.DtCons s d n)) (__smtx_typeof_value i) := by
        simp [__smtx_typeof_value]
      rw [hDtConsApply hiNN, hOuter, hf, hi]
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, native_Teq, hA]
  | Apply f v =>
      have hOuter :
          __smtx_typeof_value (SmtValue.Apply (SmtValue.Apply f v) i) =
            __smtx_typeof_apply_value
              (__smtx_typeof_value (SmtValue.Apply f v)) (__smtx_typeof_value i) := by
        rfl
      rw [hApplyApply hiNN, hOuter, hf, hi]
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, native_Teq, hA]

/-- Shows that evaluating `apply_generic` terms produces values of the expected type. -/
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
  | inl hFunTy =>
      rw [hFunTy, hX]
      have hFun : __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B := by
        simpa [hFunTy] using hpresf
      simpa [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA] using
        typeof_value_model_eval_apply_fun_value hA hFun hArg
  | inr hDtcTy =>
      rw [hDtcTy, hX]
      have hDtc : __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
        simpa [hDtcTy] using hpresf
      simpa [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA] using
        typeof_value_model_eval_apply_dt hA hDtc hArg

end Smtm
