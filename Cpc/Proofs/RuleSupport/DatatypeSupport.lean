import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

def smtDatatypeNumCtors : SmtDatatype -> Nat
  | SmtDatatype.null => 0
  | SmtDatatype.sum _ d => Nat.succ (smtDatatypeNumCtors d)

theorem smtDatatypeNumCtors_substitute
    (s : native_String) (d0 : SmtDatatype) :
    ∀ d : SmtDatatype,
      smtDatatypeNumCtors (__smtx_dt_substitute s d0 d) =
        smtDatatypeNumCtors d
  | SmtDatatype.null => by
      simp [smtDatatypeNumCtors, __smtx_dt_substitute]
  | SmtDatatype.sum c d => by
      simp [smtDatatypeNumCtors, __smtx_dt_substitute,
        smtDatatypeNumCtors_substitute s d0 d]

theorem dt_cons_applied_type_rec_non_none_implies_lt_ctors
    (s : native_String) (d0 : SmtDatatype) :
    ∀ {d : SmtDatatype} {i n : Nat},
      dt_cons_applied_type_rec s d0 d i n ≠ SmtType.None ->
      i < smtDatatypeNumCtors d
  | SmtDatatype.null, i, n, h => by
      cases i <;> cases n <;>
        simp [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec] at h
  | SmtDatatype.sum c d, 0, n, h => by
      simp [smtDatatypeNumCtors]
  | SmtDatatype.sum c d, Nat.succ i, n, h => by
      have h' : dt_cons_applied_type_rec s d0 d i n ≠ SmtType.None := by
        cases n <;>
          simpa [dt_cons_applied_type_rec, __smtx_typeof_dt_cons_value_rec,
            Nat.succ_eq_add_one] using h
      have hlt := dt_cons_applied_type_rec_non_none_implies_lt_ctors
        s d0 (d := d) (i := i) (n := n) h'
      simpa [smtDatatypeNumCtors] using Nat.succ_lt_succ hlt

theorem datatype_value_head_of_type
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
    | Set m =>
        cases typeof_map_value_shape m with
        | inl hMap =>
            rcases hMap with ⟨A, B, hMap⟩
            cases B <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at hTy
    | Fun _ _ _ => simp [__smtx_typeof_value] at hTy
    | Seq ss =>
        cases typeof_seq_value_shape ss with
        | inl hSeq =>
            rcases hSeq with ⟨A, hSeq⟩
            simp [__smtx_typeof_value, hSeq] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, hNone] at hTy
    | Char c =>
        cases hValid : native_char_valid c <;>
          simp [__smtx_typeof_value, SmtEval.native_ite, hValid] at hTy
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

theorem datatype_head_index_lt
    {v : SmtValue} {s : native_String} {d : SmtDatatype} {i : Nat}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    i < smtDatatypeNumCtors d := by
  have hChain := dt_cons_chain_type_of_non_none hHead (by rw [hTy]; simp)
  have hNN :
      dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (vsm_num_apply_args v) ≠ SmtType.None := by
    rw [← hChain, hTy]
    simp
  have hltSub := dt_cons_applied_type_rec_non_none_implies_lt_ctors
    s d (d := __smtx_dt_substitute s d d) (i := i)
    (n := vsm_num_apply_args v) hNN
  simpa [smtDatatypeNumCtors_substitute s d d] using hltSub

theorem unit_tuple_value_head_zero_of_type
    {v : SmtValue}
    (hTy :
      __smtx_typeof_value v =
        SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) :
    __vsm_apply_head v =
      SmtValue.DtCons (native_string_lit "@Tuple")
        (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)
        native_nat_zero := by
  rcases datatype_value_head_of_type hTy with ⟨i, hHead⟩
  have hlt := datatype_head_index_lt hHead hTy
  have hi : i = native_nat_zero := by
    simpa [smtDatatypeNumCtors] using hlt
  subst i
  exact hHead
