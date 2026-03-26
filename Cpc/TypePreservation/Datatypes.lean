import Cpc.TypePreservation.Helpers

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

def dt_sel_counterexample_datatype : SmtDatatype :=
  SmtDatatype.sum
    (SmtDatatypeCons.cons (SmtType.TypeRef "R") SmtDatatypeCons.unit)
    (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)

def dt_sel_counterexample_arg : SmtTerm :=
  SmtTerm.DtCons "R" dt_sel_counterexample_datatype (smt_lit_nat_succ smt_lit_nat_zero)

def dt_sel_counterexample : SmtTerm :=
  SmtTerm.Apply
    (SmtTerm.DtSel "R" dt_sel_counterexample_datatype smt_lit_nat_zero smt_lit_nat_zero)
    dt_sel_counterexample_arg

theorem dt_sel_counterexample_typeof :
    __smtx_typeof dt_sel_counterexample = SmtType.Datatype "R" dt_sel_counterexample_datatype := by
  simp [dt_sel_counterexample, dt_sel_counterexample_arg, dt_sel_counterexample_datatype,
    __smtx_typeof, __smtx_typeof_apply, __smtx_typeof_guard, __smtx_typeof_dt_cons_rec,
    __smtx_ret_typeof_sel, __smtx_ret_typeof_sel_rec, __smtx_dt_substitute,
    __smtx_dtc_substitute, smt_lit_ite, smt_lit_Teq]

theorem dt_sel_counterexample_has_non_none_type :
    term_has_non_none_type dt_sel_counterexample := by
  simp [term_has_non_none_type, dt_sel_counterexample_typeof]

theorem dt_sel_counterexample_arg_eval :
    __smtx_model_eval SmtModel.empty dt_sel_counterexample_arg =
      SmtValue.DtCons "R" dt_sel_counterexample_datatype (smt_lit_nat_succ smt_lit_nat_zero) := by
  rfl

theorem dt_sel_counterexample_eval :
    __smtx_model_eval SmtModel.empty dt_sel_counterexample = SmtValue.NotValue := by
  change
    __smtx_model_eval_dt_sel SmtModel.empty "R" dt_sel_counterexample_datatype
      smt_lit_nat_zero smt_lit_nat_zero
      (__smtx_model_eval SmtModel.empty dt_sel_counterexample_arg) =
        SmtValue.NotValue
  rw [dt_sel_counterexample_arg_eval]
  simp [SmtModel.empty, __smtx_model_eval_dt_sel, __smtx_map_select, __smtx_model_lookup,
    __vsm_apply_head, smt_lit_ite, smt_lit_veq]

theorem dt_sel_counterexample_value_typeof :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty dt_sel_counterexample) = SmtType.None := by
  rw [dt_sel_counterexample_eval]
  rfl

theorem dt_sel_counterexample_not_preserved :
    __smtx_typeof_value (__smtx_model_eval SmtModel.empty dt_sel_counterexample) ≠
      __smtx_typeof dt_sel_counterexample := by
  rw [dt_sel_counterexample_value_typeof, dt_sel_counterexample_typeof]
  simp

end Smtm
