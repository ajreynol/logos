import Cpc.Proofs.RuleSupport.CnfSupport

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

private theorem prog_dt_cycle_condition_of_not_stuck
    (s t : Term) :
    __eo_prog_dt_cycle
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false)) ≠ Term.Stuck ->
    __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) = Term.Boolean true := by
  intro hProg
  have h :
      __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) = Term.Boolean true ∧
        __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) ≠ Term.Stuck := by
    simpa [__eo_prog_dt_cycle, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] using hProg
  exact h.1

private theorem prog_dt_cycle_eq_input_of_not_stuck
    (s t : Term) :
    __eo_prog_dt_cycle
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false)) ≠ Term.Stuck ->
    __eo_prog_dt_cycle
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false)) =
      Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
        (Term.Boolean false) := by
  intro hProg
  have hCond : __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
      Term.Boolean true :=
    prog_dt_cycle_condition_of_not_stuck s t hProg
  have hCondNe :
      __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) ≠ Term.Stuck := by
    rw [hCond]
    simp
  simpa [__eo_prog_dt_cycle, hCond] using
    eo_requires_self_of_non_stuck
      (__dt_find_cycle t s (__is_cons_app t) (Term.Boolean false))
      (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
        (Term.Boolean false))
      hCondNe

private theorem prog_dt_cycle_shape_of_not_stuck
    (a : Term) :
    __eo_prog_dt_cycle a ≠ Term.Stuck ->
      ∃ s t,
        a =
          Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
            (Term.Boolean false) := by
  intro hProg
  cases a with
  | Apply outer b =>
      cases outer with
      | Apply eqOuter inner =>
          cases eqOuter with
          | UOp op =>
              cases op
              case eq =>
                cases inner with
                | Apply innerOuter t =>
                    cases innerOuter with
                    | Apply eqInner s =>
                        cases eqInner with
                        | UOp op2 =>
                            cases op2
                            case eq =>
                              cases b
                              case Boolean bb =>
                                cases bb
                                · exact ⟨s, t, rfl⟩
                                · simp [__eo_prog_dt_cycle] at hProg
                              all_goals simp [__eo_prog_dt_cycle] at hProg
                            all_goals simp [__eo_prog_dt_cycle] at hProg
                        | _ =>
                            simp [__eo_prog_dt_cycle] at hProg
                    | _ =>
                        simp [__eo_prog_dt_cycle] at hProg
                | _ =>
                    simp [__eo_prog_dt_cycle] at hProg
              all_goals simp [__eo_prog_dt_cycle] at hProg
          | _ =>
              simp [__eo_prog_dt_cycle] at hProg
      | _ =>
          simp [__eo_prog_dt_cycle] at hProg
  | _ =>
      simp [__eo_prog_dt_cycle] at hProg

private def smtValueSize : SmtValue -> Nat
  | SmtValue.Apply f x => smtValueSize f + smtValueSize x + 1
  | _ => 1

private theorem smtValueSize_apply_left_lt (f x : SmtValue) :
    smtValueSize f < smtValueSize (SmtValue.Apply f x) := by
  simp [smtValueSize]
  omega

private theorem smtValueSize_apply_right_lt (f x : SmtValue) :
    smtValueSize x < smtValueSize (SmtValue.Apply f x) := by
  simp [smtValueSize]
  omega

private theorem smtValueSize_apply_arg_nth_lt :
    ∀ (v : SmtValue) (j : native_Nat),
      j < vsm_num_apply_args v ->
      smtValueSize (__vsm_apply_arg_nth v j (vsm_num_apply_args v)) <
        smtValueSize v
  | SmtValue.Apply f a, j, hj => by
      by_cases hLast : j = vsm_num_apply_args f
      · subst j
        have hEq :
            SmtEval.native_nateq (vsm_num_apply_args f) (vsm_num_apply_args f) =
              true := by
          simp [SmtEval.native_nateq]
        simpa [__vsm_apply_arg_nth, vsm_num_apply_args, hEq] using
          smtValueSize_apply_right_lt f a
      · have hj' : j < vsm_num_apply_args f := by
          have hjSucc : j < Nat.succ (vsm_num_apply_args f) := by
            simpa [vsm_num_apply_args] using hj
          have hle : j ≤ vsm_num_apply_args f := Nat.lt_succ_iff.mp hjSucc
          cases Nat.eq_or_lt_of_le hle with
          | inl hEq =>
              exact False.elim (hLast hEq)
          | inr hLt =>
              exact hLt
        have hEq :
            SmtEval.native_nateq j (vsm_num_apply_args f) = false := by
          simp [SmtEval.native_nateq, hLast]
        have hArgLt :
            smtValueSize (__vsm_apply_arg_nth f j (vsm_num_apply_args f)) <
              smtValueSize f :=
          smtValueSize_apply_arg_nth_lt f j hj'
        have hFLt : smtValueSize f < smtValueSize (SmtValue.Apply f a) :=
          smtValueSize_apply_left_lt f a
        simpa [__vsm_apply_arg_nth, vsm_num_apply_args, hEq] using
          Nat.lt_trans hArgLt hFLt
  | SmtValue.NotValue, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Boolean b, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Numeral n, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Rational q, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Binary w n, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Map m, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Fun s T U, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Set m, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Seq ss, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.Char c, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.UValue k e, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.RegLan r, j, hj => by
      simp [vsm_num_apply_args] at hj
  | SmtValue.DtCons s d i, j, hj => by
      simp [vsm_num_apply_args] at hj

private def smtValueApplyAllArgs : SmtValue -> SmtValue -> SmtValue
  | SmtValue.Apply f a, acc => SmtValue.Apply (smtValueApplyAllArgs f acc) a
  | _, acc => acc

private theorem smtValueSize_applyAllArgs_eq_succ :
    ∀ (v acc : SmtValue),
      smtValueSize (smtValueApplyAllArgs v acc) + 1 =
        smtValueSize acc + smtValueSize v
  | SmtValue.Apply f a, acc => by
      have ih := smtValueSize_applyAllArgs_eq_succ f acc
      simp [smtValueApplyAllArgs, smtValueSize]
      omega
  | SmtValue.NotValue, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.Boolean b, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.Numeral n, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.Rational q, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.Binary w n, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.Map m, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.Fun s T U, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.Set m, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.Seq ss, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.Char c, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.UValue k e, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.RegLan r, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]
  | SmtValue.DtCons s d i, acc => by
      simp [smtValueApplyAllArgs, smtValueSize]

private theorem smtValueSize_lt_applyAllArgs_of_seed_nontrivial
    (v acc : SmtValue)
    (hAcc : 1 < smtValueSize acc) :
    smtValueSize v < smtValueSize (smtValueApplyAllArgs v acc) := by
  have hEq := smtValueSize_applyAllArgs_eq_succ v acc
  omega

private theorem smt_tuple_head_type_ne_self
    (U : SmtType) (c : SmtDatatypeCons) :
    U ≠
      SmtType.Datatype "@Tuple"
        (SmtDatatype.sum (SmtDatatypeCons.cons U c) SmtDatatype.null) := by
  intro h
  have hSize := congrArg sizeOf h
  simp at hSize
  omega

private theorem smt_tuple_tail_type_size_lt
    (U : SmtType) (c : SmtDatatypeCons) :
    sizeOf (SmtType.Datatype "@Tuple" (SmtDatatype.sum c SmtDatatype.null)) <
      sizeOf
        (SmtType.Datatype "@Tuple"
          (SmtDatatype.sum (SmtDatatypeCons.cons U c) SmtDatatype.null)) := by
  simp
  omega

private theorem smt_tuple_tail_type_ne_self
    (U : SmtType) (c : SmtDatatypeCons) :
    SmtType.Datatype "@Tuple" (SmtDatatype.sum c SmtDatatype.null) ≠
      SmtType.Datatype "@Tuple"
        (SmtDatatype.sum (SmtDatatypeCons.cons U c) SmtDatatype.null) := by
  intro h
  have hLt := smt_tuple_tail_type_size_lt U c
  rw [h] at hLt
  exact Nat.lt_irrefl _ hLt

private theorem smt_tuple_selector_type_size_lt :
    ∀ (c : SmtDatatypeCons) (j : native_Nat),
      j < __smtx_dt_num_sels
          (SmtDatatype.sum c SmtDatatype.null) native_nat_zero ->
      sizeOf
          (__smtx_ret_typeof_sel_rec
            (SmtDatatype.sum c SmtDatatype.null) native_nat_zero j) <
        sizeOf
          (SmtType.Datatype "@Tuple"
            (SmtDatatype.sum c SmtDatatype.null))
  | SmtDatatypeCons.unit, j, hj => by
      simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at hj
  | SmtDatatypeCons.cons T c, native_nat_zero, _hj => by
      simp [__smtx_ret_typeof_sel_rec]
      omega
  | SmtDatatypeCons.cons T c, native_nat_succ j, hj => by
      have hj' :
          j <
            __smtx_dt_num_sels
              (SmtDatatype.sum c SmtDatatype.null) native_nat_zero := by
        simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using
          Nat.succ_lt_succ_iff.mp hj
      have ih := smt_tuple_selector_type_size_lt c j hj'
      simp [__smtx_ret_typeof_sel_rec] at ih ⊢
      omega

private theorem smt_tuple_selector_type_ne_self
    (c : SmtDatatypeCons) (j : native_Nat)
    (hj :
      j < __smtx_dt_num_sels
          (SmtDatatype.sum c SmtDatatype.null) native_nat_zero) :
    __smtx_ret_typeof_sel_rec
        (SmtDatatype.sum c SmtDatatype.null) native_nat_zero j ≠
      SmtType.Datatype "@Tuple" (SmtDatatype.sum c SmtDatatype.null) := by
  intro h
  have hLt := smt_tuple_selector_type_size_lt c j hj
  rw [h] at hLt
  exact Nat.lt_irrefl _ hLt

private theorem datatype_value_head_of_type
    {v : SmtValue} {s : native_String} {d : SmtDatatype}
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    ∃ i, __vsm_apply_head v = SmtValue.DtCons s d i := by
  by_cases hHead : ∃ s0 d0 i0, __vsm_apply_head v = SmtValue.DtCons s0 d0 i0
  · rcases hHead with ⟨s0, d0, i0, hHead⟩
    have hChain :=
      dt_cons_chain_type_of_non_none hHead (by rw [hTy]; simp)
    have hEq :
        dt_cons_applied_type_rec s0 d0 (__smtx_dt_substitute s0 d0 d0) i0
            (vsm_num_apply_args v) =
          SmtType.Datatype s d := by
      exact hChain.symm.trans hTy
    have hArgsZero :
        __smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0 -
            vsm_num_apply_args v =
          0 := by
      have hArgs := congrArg dt_cons_type_num_args hEq
      rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
      simpa [dt_cons_type_num_args] using hArgs
    have hle :
        vsm_num_apply_args v ≤
          __smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0 :=
      dt_cons_applied_type_rec_non_none_implies_le s0 d0
        (__smtx_dt_substitute s0 d0 d0) i0
        (vsm_num_apply_args v) (by rw [hEq]; simp)
    have hCount :
        vsm_num_apply_args v =
          __smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0 := by
      have hge :
          __smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0 ≤
            vsm_num_apply_args v :=
        (Nat.sub_eq_zero_iff_le).1 hArgsZero
      exact Nat.le_antisymm hle hge
    have hFull :
        dt_cons_applied_type_rec s0 d0 (__smtx_dt_substitute s0 d0 d0) i0
            (__smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0) =
          SmtType.Datatype s0 d0 :=
      dt_cons_applied_type_rec_full_arity s0 d0
        (__smtx_dt_substitute s0 d0 d0) i0
        (by rw [← hCount, hEq]; simp)
    have hBase : SmtType.Datatype s0 d0 = SmtType.Datatype s d := by
      calc
        SmtType.Datatype s0 d0 =
            dt_cons_applied_type_rec s0 d0 (__smtx_dt_substitute s0 d0 d0) i0
              (__smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0) := by
          exact hFull.symm
        _ =
            dt_cons_applied_type_rec s0 d0 (__smtx_dt_substitute s0 d0 d0) i0
              (vsm_num_apply_args v) := by rw [hCount]
        _ = SmtType.Datatype s d := hEq
    injection hBase with hs hd
    subst hs
    subst hd
    exact ⟨i0, hHead⟩
  · cases v with
    | NotValue => simp [__smtx_typeof_value] at hTy
    | Boolean _ => simp [__smtx_typeof_value] at hTy
    | Numeral _ => simp [__smtx_typeof_value] at hTy
    | Rational _ => simp [__smtx_typeof_value] at hTy
    | Binary w n =>
        cases hWidth : native_zleq 0 w <;>
          cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and,
            hWidth, hMod] at hTy
    | Map m =>
        cases typeof_map_value_shape m with
        | inl hMap =>
            rcases hMap with ⟨A, B, hMap⟩
            simp [__smtx_typeof_value, hMap] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, hNone] at hTy
    | Fun _ _ _ => simp [__smtx_typeof_value] at hTy
    | Set m =>
        cases typeof_map_value_shape m with
        | inl hMap =>
            rcases hMap with ⟨A, B, hMap⟩
            cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at hTy
    | Seq ss =>
        cases typeof_seq_value_shape ss with
        | inl hSeq =>
            rcases hSeq with ⟨A, hSeq⟩
            simp [__smtx_typeof_value, hSeq] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, hNone] at hTy
    | Char _ => simp [__smtx_typeof_value] at hTy
    | UValue _ _ => simp [__smtx_typeof_value] at hTy
    | RegLan _ => simp [__smtx_typeof_value] at hTy
    | DtCons s0 d0 i0 =>
        exact False.elim (hHead ⟨s0, d0, i0, by simp [__vsm_apply_head]⟩)
    | Apply f a =>
        have hNone :
            __smtx_typeof_value (SmtValue.Apply f a) = SmtType.None :=
          typeof_value_apply_of_head_ne_dt_cons f a
            (by
              intro s0 d0 i0 hf
              exact hHead ⟨s0, d0, i0, by simpa [__vsm_apply_head] using hf⟩)
        rw [hNone] at hTy
        cases hTy

private theorem dt_cons_applied_type_tuple_non_none_implies_index_zero
    (c : SmtDatatypeCons) (i n : native_Nat)
    (hNN :
      dt_cons_applied_type_rec "@Tuple" (SmtDatatype.sum c SmtDatatype.null)
          (__smtx_dt_substitute "@Tuple" (SmtDatatype.sum c SmtDatatype.null)
            (SmtDatatype.sum c SmtDatatype.null)) i n ≠
        SmtType.None) :
    i = 0 := by
  cases i with
  | zero => rfl
  | succ i =>
      cases n <;>
        simp [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec,
          __smtx_dt_substitute] at hNN

private theorem tuple_value_head_zero_of_type
    {v : SmtValue} {c : SmtDatatypeCons}
    (hTy :
      __smtx_typeof_value v =
        SmtType.Datatype "@Tuple" (SmtDatatype.sum c SmtDatatype.null)) :
    __vsm_apply_head v =
      SmtValue.DtCons "@Tuple" (SmtDatatype.sum c SmtDatatype.null) 0 := by
  rcases datatype_value_head_of_type hTy with ⟨i, hHead⟩
  have hChain :=
    dt_cons_chain_type_of_non_none hHead (by rw [hTy]; simp)
  have hNN :
      dt_cons_applied_type_rec "@Tuple" (SmtDatatype.sum c SmtDatatype.null)
          (__smtx_dt_substitute "@Tuple" (SmtDatatype.sum c SmtDatatype.null)
            (SmtDatatype.sum c SmtDatatype.null)) i (vsm_num_apply_args v) ≠
        SmtType.None := by
    rw [← hChain, hTy]
    simp
  have hi : i = 0 :=
    dt_cons_applied_type_tuple_non_none_implies_index_zero c i
      (vsm_num_apply_args v) hNN
  subst hi
  exact hHead

private theorem smt_eval_tuple_selector_size_lt
    (M : SmtModel) (hM : model_total_typed M)
    (tail : SmtTerm) (c : SmtDatatypeCons) (j : native_Nat)
    (hTailTy :
      __smtx_typeof tail =
        SmtType.Datatype "@Tuple" (SmtDatatype.sum c SmtDatatype.null))
    (hj : j < __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null) 0) :
    smtValueSize
        (__smtx_model_eval M
          (SmtTerm.Apply
            (SmtTerm.DtSel "@Tuple" (SmtDatatype.sum c SmtDatatype.null) 0 j)
            tail)) <
      smtValueSize (__smtx_model_eval M tail) := by
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let v := __smtx_model_eval M tail
  have hTailNN : term_has_non_none_type tail := by
    unfold term_has_non_none_type
    rw [hTailTy]
    simp
  have hvTy :
      __smtx_typeof_value v = SmtType.Datatype "@Tuple" tailD := by
    simpa [v, tailD, hTailTy] using
      smt_model_eval_preserves_type_of_non_none M hM tail hTailNN
  have hHead : __vsm_apply_head v = SmtValue.DtCons "@Tuple" tailD 0 :=
    tuple_value_head_zero_of_type hvTy
  have hCountSub :
      vsm_num_apply_args v =
        __smtx_dt_num_sels (__smtx_dt_substitute "@Tuple" tailD tailD) 0 :=
    vsm_num_apply_args_eq_dt_num_sels_of_datatype hHead hvTy
  have hCount :
      vsm_num_apply_args v = __smtx_dt_num_sels tailD 0 := by
    rw [dt_num_sels_substitute "@Tuple" tailD tailD 0] at hCountSub
    exact hCountSub
  have hjV : j < vsm_num_apply_args v := by
    rw [hCount]
    exact hj
  have hVeq :
      native_veq (__vsm_apply_head v) (SmtValue.DtCons "@Tuple" tailD 0) =
        true := by
    rw [hHead]
    simp [native_veq]
  simpa [tailD, v, __smtx_model_eval, __smtx_model_eval_dt_sel, hVeq, hCount] using
    smtValueSize_apply_arg_nth_lt v j hjV

private theorem eo_ite_true_true_cases
    (c e : Term) :
    __eo_ite c (Term.Boolean true) e = Term.Boolean true ->
      c = Term.Boolean true ∨
        (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_ite, native_teq] at h ⊢
  case Boolean b =>
    cases b <;> simp at h ⊢
    exact h

private theorem dt_find_cycle_self_false_ne_true
    (t isC : Term) :
    __dt_find_cycle t t isC (Term.Boolean false) ≠ Term.Boolean true := by
  intro h
  cases t <;> cases isC <;>
    simp [__dt_find_cycle, __eo_eq, __eo_ite, native_ite, native_teq] at h

private theorem smt_type_ne_none_of_apply_head
    {F A B : SmtType}
    (hHead :
      F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B) :
    F ≠ SmtType.None := by
  rcases hHead with hHead | hHead <;> rw [hHead] <;> simp

private theorem smt_apply_head_non_none_of_apply_non_none
    {f x : SmtTerm}
    (hAppNN :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
        SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  rcases typeof_apply_non_none_cases hAppNN with
    ⟨A, B, hHead, _hX, _hA, _hB⟩
  exact smt_type_ne_none_of_apply_head hHead

private theorem smt_apply_arg_non_none_of_apply_non_none
    {f x : SmtTerm}
    (hAppNN :
      __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠
        SmtType.None) :
    __smtx_typeof x ≠ SmtType.None := by
  rcases typeof_apply_non_none_cases hAppNN with
    ⟨A, _B, _hHead, hX, hA, _hB⟩
  rw [hX]
  exact hA

private theorem model_eval_eq_false_of_ne_not_reglan_pair
    {v₁ v₂ : SmtValue}
    (hNe : v₁ ≠ v₂)
    (hReg :
      ¬ ∃ r₁ r₂, v₁ = SmtValue.RegLan r₁ ∧ v₂ = SmtValue.RegLan r₂) :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false := by
  cases v₁ <;> cases v₂ <;>
    simp [__smtx_model_eval_eq, native_veq] at hNe hReg ⊢
  all_goals
    first
    | exact False.elim hReg
    | simpa using hNe

private theorem smt_type_ne_reglan_of_same_type_and_size_lt
    {v₁ v₂ : SmtValue} {T : SmtType}
    (hTy₁ : __smtx_typeof_value v₁ = T)
    (hTy₂ : __smtx_typeof_value v₂ = T)
    (hSize : smtValueSize v₁ < smtValueSize v₂) :
    T ≠ SmtType.RegLan := by
  intro hT
  subst hT
  rcases reglan_value_canonical hTy₁ with ⟨r₁, rfl⟩
  rcases reglan_value_canonical hTy₂ with ⟨r₂, rfl⟩
  simp [smtValueSize] at hSize

private theorem smt_value_dtc_shape
    {v : SmtValue} {A B : SmtType}
    (h : __smtx_typeof_value v = SmtType.DtcAppType A B) :
    (∃ s d i, v = SmtValue.DtCons s d i) ∨
      ∃ f x, v = SmtValue.Apply f x := by
  cases v with
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and,
            hWidth, hMod] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun _ _ _ =>
      simp [__smtx_typeof_value] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          cases U <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exact Or.inl ⟨s, d, i, rfl⟩
  | Apply f x =>
      exact Or.inr ⟨f, x, rfl⟩

private theorem smt_eval_apply_dt_size_gt_fun
    (M : SmtModel)
    {f x : SmtTerm} {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof_value (__smtx_model_eval M x) = A) :
    smtValueSize (__smtx_model_eval M f) <
      smtValueSize (__smtx_model_eval M (SmtTerm.Apply f x)) := by
  have hxNe : __smtx_model_eval M x ≠ SmtValue.NotValue := by
    intro hxNV
    rw [hxNV] at hx
    simp [__smtx_typeof_value] at hx
    exact hA hx.symm
  rw [__smtx_model_eval.eq_142 M f x
    (by
      intro s d i j hfEq
      subst hfEq
      simp [__smtx_model_eval, __smtx_typeof_value] at hf)
    (by
      intro s d i hfEq
      subst hfEq
      simp [__smtx_model_eval, __smtx_typeof_value] at hf)]
  rcases smt_value_dtc_shape hf with hShape | hShape
  · rcases hShape with ⟨s, d, i, hF⟩
    rw [hF]
    cases hxv : __smtx_model_eval M x <;>
      simp [hxv, __smtx_model_eval_apply, smtValueSize] at hxNe ⊢ <;>
      omega
  · rcases hShape with ⟨g, y, hF⟩
    rw [hF]
    cases hxv : __smtx_model_eval M x <;>
      simp [hxv, __smtx_model_eval_apply, smtValueSize] at hxNe ⊢ <;>
      omega

private theorem smt_eval_apply_dt_size_gt_arg
    (M : SmtModel)
    {f x : SmtTerm} {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof_value (__smtx_model_eval M x) = A) :
    smtValueSize (__smtx_model_eval M x) <
      smtValueSize (__smtx_model_eval M (SmtTerm.Apply f x)) := by
  have hxNe : __smtx_model_eval M x ≠ SmtValue.NotValue := by
    intro hxNV
    rw [hxNV] at hx
    simp [__smtx_typeof_value] at hx
    exact hA hx.symm
  rw [__smtx_model_eval.eq_142 M f x
    (by
      intro s d i j hfEq
      subst hfEq
      simp [__smtx_model_eval, __smtx_typeof_value] at hf)
    (by
      intro s d i hfEq
      subst hfEq
      simp [__smtx_model_eval, __smtx_typeof_value] at hf)]
  rcases smt_value_dtc_shape hf with hShape | hShape
  · rcases hShape with ⟨s, d, i, hF⟩
    rw [hF]
    cases hxv : __smtx_model_eval M x <;>
      simp [hxv, __smtx_model_eval_apply, smtValueSize] at hxNe ⊢ <;>
      omega
  · rcases hShape with ⟨g, y, hF⟩
    rw [hF]
    cases hxv : __smtx_model_eval M x <;>
      simp [hxv, __smtx_model_eval_apply, smtValueSize] at hxNe ⊢ <;>
      omega

private theorem smt_eval_apply_dt_size_gt_fun_of_term_type
    (M : SmtModel) (hM : model_total_typed M)
    {f x : SmtTerm} {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof f = SmtType.DtcAppType A B)
    (hx : __smtx_typeof x = A) :
    smtValueSize (__smtx_model_eval M f) <
      smtValueSize (__smtx_model_eval M (SmtTerm.Apply f x)) := by
  have hfNN : term_has_non_none_type f := by
    unfold term_has_non_none_type
    rw [hf]
    simp
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hx]
    exact hA
  have hfVal :
      __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
    simpa [hf] using
      smt_model_eval_preserves_type_of_non_none M hM f hfNN
  have hxVal :
      __smtx_typeof_value (__smtx_model_eval M x) = A := by
    simpa [hx] using
      smt_model_eval_preserves_type_of_non_none M hM x hxNN
  exact smt_eval_apply_dt_size_gt_fun M hA hfVal hxVal

private theorem smt_eval_apply_dt_size_gt_arg_of_term_type
    (M : SmtModel) (hM : model_total_typed M)
    {f x : SmtTerm} {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof f = SmtType.DtcAppType A B)
    (hx : __smtx_typeof x = A) :
    smtValueSize (__smtx_model_eval M x) <
      smtValueSize (__smtx_model_eval M (SmtTerm.Apply f x)) := by
  have hfNN : term_has_non_none_type f := by
    unfold term_has_non_none_type
    rw [hf]
    simp
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hx]
    exact hA
  have hfVal :
      __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
    simpa [hf] using
      smt_model_eval_preserves_type_of_non_none M hM f hfNN
  have hxVal :
      __smtx_typeof_value (__smtx_model_eval M x) = A := by
    simpa [hx] using
      smt_model_eval_preserves_type_of_non_none M hM x hxNN
  exact smt_eval_apply_dt_size_gt_arg M hA hfVal hxVal

private theorem smt_eval_dt_cons_apply_seed_size_gt_one
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (head : SmtTerm)
    (hHeadNN : __smtx_typeof head ≠ SmtType.None) :
    1 <
      smtValueSize
        (__smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.DtCons s d i) head)) := by
  have hHeadTermNN : term_has_non_none_type head := by
    unfold term_has_non_none_type
    exact hHeadNN
  have hHeadNotValue :
      __smtx_model_eval M head ≠ SmtValue.NotValue := by
    intro hEval
    have hTy :=
      smt_model_eval_preserves_type_of_non_none M hM head hHeadTermNN
    rw [hEval] at hTy
    simp [__smtx_typeof_value] at hTy
    exact hHeadNN hTy.symm
  cases hEval : __smtx_model_eval M head <;>
    simp [__smtx_model_eval, hEval, __smtx_model_eval_apply, smtValueSize]
      at hHeadNotValue ⊢ <;>
    omega

private theorem eo_interprets_eq_false_of_size_lt
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term)
    (hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq s) t))
    (hSize :
      smtValueSize (__smtx_model_eval M (__eo_to_smt s)) <
        smtValueSize (__smtx_model_eval M (__eo_to_smt t))) :
    eo_interprets M (Term.Apply (Term.Apply Term.eq s) t) false := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t hEqBool with
    ⟨hTyEq, hSNN⟩
  let T := __smtx_typeof (__eo_to_smt s)
  have hSTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = T := by
    simpa [T] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
        (by
          unfold term_has_non_none_type
          exact hSNN)
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    simpa [hTyEq] using hSNN
  have hTTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = T := by
    simpa [T, hTyEq] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by
          unfold term_has_non_none_type
          exact hTNN)
  have hTNeReg : T ≠ SmtType.RegLan :=
    smt_type_ne_reglan_of_same_type_and_size_lt hSTy hTTy hSize
  have hNe :
      __smtx_model_eval M (__eo_to_smt s) ≠
        __smtx_model_eval M (__eo_to_smt t) := by
    intro hEq
    rw [hEq] at hSize
    exact Nat.lt_irrefl _ hSize
  have hNoReg :
      ¬ ∃ r₁ r₂,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.RegLan r₁ ∧
          __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r₂ := by
    rintro ⟨r₁, r₂, hS, _hT⟩
    have hReg : T = SmtType.RegLan := by
      rw [← hSTy, hS]
      rfl
    exact hTNeReg hReg
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  change smt_interprets M (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt t)) false
  refine smt_interprets.intro_false M _ ?_ ?_
  · simpa [RuleProofs.eo_has_bool_type] using hEqBool
  · rw [__smtx_model_eval.eq_134]
    exact model_eval_eq_false_of_ne_not_reglan_pair hNe hNoReg

private theorem eo_has_bool_type_eq_left_of_eq_false_bool
    (s t : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
        (Term.Boolean false)) ->
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) := by
  intro hOuter
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.Apply Term.eq s) t) (Term.Boolean false) hOuter with
    ⟨hTy, _hNN⟩
  have hFalseTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean false)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
    rw [__smtx_typeof.eq_1]
  exact hTy.trans hFalseTy

private theorem dt_find_cycle_size_lt_of_same_type
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term)
    (hCycle :
      __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
        Term.Boolean true)
    (hEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t)) :
    smtValueSize (__smtx_model_eval M (__eo_to_smt s)) <
      smtValueSize (__smtx_model_eval M (__eo_to_smt t)) := by
  sorry

private theorem dt_cycle_inner_eq_false
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term)
    (hCycle :
      __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
        Term.Boolean true)
    (hEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t)) :
    eo_interprets M (Term.Apply (Term.Apply Term.eq s) t) false := by
  exact eo_interprets_eq_false_of_size_lt M hM s t hEqBool
    (dt_find_cycle_size_lt_of_same_type M hM s t hCycle hEqBool)

theorem cmd_step_dt_cycle_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_cycle args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_cycle args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_cycle args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_cycle args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | cons a1 argsTail =>
      cases argsTail with
      | cons _ _ =>
          cases premises <;> change Term.Stuck ≠ Term.Stuck at hProg <;>
            exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans
              have hProgA1 : __eo_prog_dt_cycle a1 ≠ Term.Stuck := by
                change __eo_prog_dt_cycle a1 ≠ Term.Stuck at hProg
                exact hProg
              rcases prog_dt_cycle_shape_of_not_stuck a1 hProgA1 with
                ⟨sArg, t, rfl⟩
              let result :=
                Term.Apply
                  (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq sArg) t))
                  (Term.Boolean false)
              have hProgEq :
                  __eo_cmd_step_proven s CRule.dt_cycle
                      (CArgList.cons result CArgList.nil) CIndexList.nil =
                    result := by
                change __eo_prog_dt_cycle result = result
                exact prog_dt_cycle_eq_input_of_not_stuck sArg t hProgA1
              have hResultTy' : __eo_typeof result = Term.Bool := by
                change
                  __eo_typeof
                      (__eo_cmd_step_proven s CRule.dt_cycle
                        (CArgList.cons result CArgList.nil) CIndexList.nil) =
                    Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hResultBool : RuleProofs.eo_has_bool_type result :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  result hA1Trans hResultTy'
              have hInnerBool :
                  RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply Term.eq sArg) t) :=
                eo_has_bool_type_eq_left_of_eq_false_bool sArg t hResultBool
              have hCycle :
                  __dt_find_cycle t sArg (__is_cons_app t) (Term.Boolean false) =
                    Term.Boolean true :=
                prog_dt_cycle_condition_of_not_stuck sArg t hProgA1
              refine ⟨?_, ?_⟩
              · intro _hPremisesTrue
                rw [hProgEq]
                change eo_interprets M result true
                apply CnfSupport.eo_interprets_eq_true_of_false_false
                · exact dt_cycle_inner_eq_false M hM sArg t hCycle hInnerBool
                · exact CnfSupport.eo_interprets_false M
              · rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  result hResultBool
