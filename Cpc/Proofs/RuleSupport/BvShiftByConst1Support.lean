import Cpc.Proofs.RuleSupport.BvShiftByConst2Support

/-! Shared support for the in-range constant `bvshl` and `bvlshr` rewrites. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvShiftByConst1LtPrem (x amount : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) amount)
        (bvShiftByConst2Bvsize x)))
    (Term.Boolean true)

def bvShlByConst1EnPrem (x amount en : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) en)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg) (bvShiftByConst2Bvsize x))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) amount)
          (Term.Numeral 0))))

def bvLshrByConst1NmPrem (x nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nm)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvShiftByConst2Bvsize x)) (Term.Numeral 1))

def bvShiftByConst1Zero (amount : Term) : Term :=
  bvShiftByConst2Const (Term.Numeral 0) amount

def bvShlByConst1Rhs (x amount en : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x en (Term.Numeral 0)))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) (bvShiftByConst1Zero amount))
      (Term.Binary 0 0))

def bvLshrByConst1Rhs (x amount nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.concat) (bvShiftByConst1Zero amount))
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.concat) (bvExtractTerm x nm amount))
      (Term.Binary 0 0))

def bvShlByConst1Term (x amount sz en : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvShlByConst2Lhs x amount sz)) (bvShlByConst1Rhs x amount en)

def bvLshrByConst1Term (x amount sz nm : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvLshrByConst2Lhs x amount sz)) (bvLshrByConst1Rhs x amount nm)

private theorem typeof_bvand_arg_types_of_ne_stuck_local1
    {A B : Term}
    (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    exists width,
      A = Term.Apply (Term.UOp UserOp.BitVec) width /\
        B = Term.Apply (Term.UOp UserOp.BitVec) width := by
  cases A <;> cases B <;> simp [__eo_typeof_bvand] at h |-
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_bvand] at h |-
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_bvand] at h |-
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
            Term.Stuck := by
        simpa [__eo_typeof_bvand] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

private theorem shift_operand_context1
    (x amount sz : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)) ≠ Term.Stuck ->
    exists W : native_Int,
      sz = Term.Numeral W /\ native_zleq 0 W = true /\
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) /\
      __eo_typeof amount = Term.UOp UserOp.Int /\
      __eo_typeof (bvShiftByConst2Const amount sz) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) /\
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) /\
      __smtx_typeof (__eo_to_smt amount) = SmtType.Int := by
  intro hXTrans hAmountTrans hSzTrans hLeftNe
  rcases typeof_bvand_arg_types_of_ne_stuck_local1 hLeftNe with
    ⟨width, hXTy, hConstTy⟩
  have hAmountNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  have hSzNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation sz hSzTrans
  rcases bv_all_ones_const_context amount sz width hAmountNe hSzNe
      (by simpa [bvAllOnesConst, bvShiftByConst2Const] using hConstTy) with
    ⟨W, hSz, hWidth, hW0, hAmountTy⟩
  subst width
  have hXSmtTy :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) := by
    have h :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        x (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt x) rfl hXTrans hXTy
    simpa [__eo_to_smt_type, hW0, native_ite] using h
  have hAmountSmtTy :
      __smtx_typeof (__eo_to_smt amount) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      amount (Term.UOp UserOp.Int) (__eo_to_smt amount) rfl
      hAmountTrans hAmountTy
  exact ⟨W, hSz, hW0, hXTy, hAmountTy, hConstTy,
    hXSmtTy, hAmountSmtTy⟩

private theorem eo_typeof_concat_args_bitvec_of_ne_stuck_local
    {A B : Term} (h : __eo_typeof_concat A B ≠ Term.Stuck) :
    exists wa wb,
      A = Term.Apply (Term.UOp UserOp.BitVec) wa /\
      B = Term.Apply (Term.UOp UserOp.BitVec) wb := by
  cases A <;> cases B <;> simp [__eo_typeof_concat] at h |-
  case Apply.Apply f a g b =>
    cases f <;> cases g <;> simp [__eo_typeof_concat] at h |-
    case UOp.UOp op op' =>
      cases op <;> cases op' <;> simp [__eo_typeof_concat] at h |-

private theorem smt_typeof_concat_bitvec
    (a b : Term) (wa wb : native_Nat) :
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec wa ->
    __smtx_typeof (__eo_to_smt b) = SmtType.BitVec wb ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) a) b)) =
      SmtType.BitVec
        (native_int_to_nat
          (native_zplus (native_nat_to_int wa) (native_nat_to_int wb))) := by
  intro hA hB
  change __smtx_typeof (SmtTerm.concat (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [typeof_concat_eq]
  simp [__smtx_typeof_concat, hA, hB]

private theorem smt_typeof_empty_bitvec :
    __smtx_typeof (__eo_to_smt (Term.Binary 0 0)) = SmtType.BitVec 0 := by
  native_decide

private theorem shift_lhs_eo_type
    (x amount : Term) (W : native_Int) :
    __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    __eo_typeof (bvShiftByConst2Const amount (Term.Numeral W)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount (Term.Numeral W))) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
  intro hXTy hConstTy
  rw [hXTy, hConstTy]
  simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
    native_teq, native_not]

private theorem smt_typeof_bvshl_same1
    (x amount : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt amount) = SmtType.Int ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt (bvShlByConst2Lhs x amount
      (Term.Numeral W))) = SmtType.BitVec (native_int_to_nat W) := by
  intro hXTy hAmountTy hW0
  have hConstTy := smt_typeof_bv_const_of_int_type amount W hAmountTy hW0
  have hConstTy' :
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount)) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [bvShiftByConst2Const] using hConstTy
  change __smtx_typeof
      (SmtTerm.bvshl (__eo_to_smt x)
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount))) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hConstTy',
    native_nateq, native_ite]

private theorem smt_typeof_bvlshr_same1
    (x amount : Term) (W : native_Int) :
    __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt amount) = SmtType.Int ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt (bvLshrByConst2Lhs x amount
      (Term.Numeral W))) = SmtType.BitVec (native_int_to_nat W) := by
  intro hXTy hAmountTy hW0
  have hConstTy := smt_typeof_bv_const_of_int_type amount W hAmountTy hW0
  have hConstTy' :
      __smtx_typeof
          (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount)) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [bvShiftByConst2Const] using hConstTy
  change __smtx_typeof
      (SmtTerm.bvlshr (__eo_to_smt x)
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount))) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hConstTy',
    native_nateq, native_ite]

private theorem rhs_smt_type_of_eo_bitvec_type
    (rhs : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation rhs ->
    __eo_typeof rhs =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt rhs) =
      SmtType.BitVec (native_int_to_nat W) := by
  intro hTrans hEoTy hW0
  have h := RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    rhs (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
    (__eo_to_smt rhs) rfl hTrans hEoTy
  simpa [__eo_to_smt_type, hW0, native_ite] using h

private theorem bv_lshr_by_const_1_context
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool ->
    exists W A N : native_Int,
      sz = Term.Numeral W /\ amount = Term.Numeral A /\
      nm = Term.Numeral N /\
      native_zleq 0 W = true /\ native_zleq 0 A = true /\
      native_zlt N W = true /\
      native_zleq 0
        (native_zplus (native_zplus N 1) (native_zneg A)) = true /\
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) /\
      __smtx_typeof (__eo_to_smt (bvLshrByConst1Rhs x amount nm)) =
        SmtType.BitVec (native_int_to_nat W) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)))
      (__eo_typeof (bvLshrByConst1Rhs x amount nm)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases shift_operand_context1 x amount sz hXTrans hAmountTrans
      hSzTrans hLhsNe with
    ⟨W, rfl, hW0, hXTy, _hAmountTy, hConstTy, hXSmtTy, hAmountSmtTy⟩
  change __eo_typeof_concat (__eo_typeof (bvShiftByConst1Zero amount))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
          (bvExtractTerm x nm amount)) (Term.Binary 0 0))) ≠
      Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hRhsNe with
    ⟨wz, wi, hZeroTy, hInnerTy⟩
  have hAmountNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) amount wz
      (by simp) hAmountNe
      (by simpa [bvAllOnesConst, bvShiftByConst1Zero,
          bvShiftByConst2Const] using hZeroTy) with
    ⟨A, hAmount, hWz, hA0, _hZeroValueTy⟩
  subst wz
  subst amount
  have hInnerNe :
      __eo_typeof_concat
          (__eo_typeof (bvExtractTerm x nm (Term.Numeral A)))
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    simpa using (show
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvExtractTerm x nm (Term.Numeral A))) (Term.Binary 0 0)) ≠
        Term.Stuck by
      rw [hInnerTy]
      intro h
      cases h)
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hInnerNe with
    ⟨we, w0, hExtractTy, _hEmptyTy⟩
  have hExtractNe :
      __eo_typeof (bvExtractTerm x nm (Term.Numeral A)) ≠ Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x nm (Term.Numeral A)
      hXTrans hExtractNe with
    ⟨W', N, A', hXTy', hNm, hAmount', _hW'0, _hA'0, hNW', hD0,
      _hXSmtTy'⟩
  have hWW' : W' = W := by
    rw [hXTy] at hXTy'
    injection hXTy' with _ hNum
    injection hNum with hEq
    exact hEq.symm
  subst W'
  have hAA' : A' = A := by
    injection hAmount' with hEq
    exact hEq.symm
  subst A'
  subst nm
  have hExtSmtTy := smt_typeof_extract_of_context x W N A hXSmtTy
    hW0 hA0 hNW' hD0
  have hZeroSmtTy :=
    smt_typeof_bv_const_of_int_type (Term.Numeral 0) A rfl hA0
  have hInnerSmtTy := smt_typeof_concat_bitvec
    (bvExtractTerm x (Term.Numeral N) (Term.Numeral A))
    (Term.Binary 0 0)
    _ _
    hExtSmtTy smt_typeof_empty_bitvec
  have hRhsRawTy := smt_typeof_concat_bitvec
    (bvShiftByConst1Zero (Term.Numeral A))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x (Term.Numeral N) (Term.Numeral A)))
      (Term.Binary 0 0))
    _ _
    hZeroSmtTy hInnerSmtTy
  have hRhsTrans : RuleProofs.eo_has_smt_translation
      (bvLshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N)) := by
    unfold RuleProofs.eo_has_smt_translation bvLshrByConst1Rhs
    rw [hRhsRawTy]
    intro h
    cases h
  have hLhsTy := shift_lhs_eo_type x (Term.Numeral A) W hXTy hConstTy
  have hTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hRhsEoTy :
      __eo_typeof (bvLshrByConst1Rhs x (Term.Numeral A)
          (Term.Numeral N)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hLhsTy] at hTypes
    exact hTypes.symm
  have hRhsSmtTy := rhs_smt_type_of_eo_bitvec_type
    (bvLshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N)) W
    hRhsTrans hRhsEoTy hW0
  have hD0' := native_zleq_of_zlt_true 0 _ hD0
  exact ⟨W, A, N, rfl, rfl, rfl, hW0, hA0, hNW', hD0',
    hXSmtTy, hRhsSmtTy⟩

private theorem bv_shl_by_const_1_context
    (x amount sz en : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool ->
    exists W A E : native_Int,
      sz = Term.Numeral W /\ amount = Term.Numeral A /\
      en = Term.Numeral E /\
      native_zleq 0 W = true /\ native_zleq 0 A = true /\
      native_zlt E W = true /\
      native_zleq 0 (native_zplus E 1) = true /\
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) /\
      __smtx_typeof (__eo_to_smt (bvShlByConst1Rhs x amount en)) =
        SmtType.BitVec (native_int_to_nat W) := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)))
      (__eo_typeof (bvShlByConst1Rhs x amount en)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  rcases shift_operand_context1 x amount sz hXTrans hAmountTrans
      hSzTrans hLhsNe with
    ⟨W, rfl, hW0, hXTy, _hAmountTy, hConstTy, hXSmtTy, hAmountSmtTy⟩
  change __eo_typeof_concat (__eo_typeof (bvExtractTerm x en (Term.Numeral 0)))
      (__eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
          (bvShiftByConst1Zero amount)) (Term.Binary 0 0))) ≠
      Term.Stuck at hRhsNe
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hRhsNe with
    ⟨we, wi, hExtractTy, hInnerTy⟩
  have hInnerNe :
      __eo_typeof_concat (__eo_typeof (bvShiftByConst1Zero amount))
          (__eo_typeof (Term.Binary 0 0)) ≠ Term.Stuck := by
    simpa using (show
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
            (bvShiftByConst1Zero amount)) (Term.Binary 0 0)) ≠
        Term.Stuck by
      rw [hInnerTy]
      intro h
      cases h)
  rcases eo_typeof_concat_args_bitvec_of_ne_stuck_local hInnerNe with
    ⟨wz, w0, hZeroTy, _hEmptyTy⟩
  have hAmountNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) amount wz
      (by simp) hAmountNe
      (by simpa [bvAllOnesConst, bvShiftByConst1Zero,
          bvShiftByConst2Const] using hZeroTy) with
    ⟨A, hAmount, hWz, hA0, _hZeroValueTy⟩
  subst wz
  subst amount
  have hExtractNe :
      __eo_typeof (bvExtractTerm x en (Term.Numeral 0)) ≠ Term.Stuck := by
    rw [hExtractTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck x en (Term.Numeral 0)
      hXTrans hExtractNe with
    ⟨W', E, Z, hXTy', hEn, hZero, _hW'0, hZ0, hEW', hD0,
      _hXSmtTy'⟩
  have hWW' : W' = W := by
    rw [hXTy] at hXTy'
    injection hXTy' with _ hNum
    injection hNum with hEq
    exact hEq.symm
  subst W'
  have hZ : Z = 0 := by
    injection hZero with hEq
    exact hEq.symm
  subst Z
  subst en
  have hD0' : native_zleq 0 (native_zplus E 1) = true := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg] using
      (native_zleq_of_zlt_true 0 _ hD0)
  have hExtSmtTy := smt_typeof_extract_of_context x W E 0 hXSmtTy
    hW0 hZ0 hEW' hD0
  have hZeroSmtTy :=
    smt_typeof_bv_const_of_int_type (Term.Numeral 0) A rfl hA0
  have hInnerSmtTy := smt_typeof_concat_bitvec
    (bvShiftByConst1Zero (Term.Numeral A)) (Term.Binary 0 0)
    _ _ hZeroSmtTy smt_typeof_empty_bitvec
  have hRhsRawTy := smt_typeof_concat_bitvec
    (bvExtractTerm x (Term.Numeral E) (Term.Numeral 0))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvShiftByConst1Zero (Term.Numeral A))) (Term.Binary 0 0))
    _ _ hExtSmtTy hInnerSmtTy
  have hRhsTrans : RuleProofs.eo_has_smt_translation
      (bvShlByConst1Rhs x (Term.Numeral A) (Term.Numeral E)) := by
    unfold RuleProofs.eo_has_smt_translation bvShlByConst1Rhs
    rw [hRhsRawTy]
    intro h
    cases h
  have hLhsTy := shift_lhs_eo_type x (Term.Numeral A) W hXTy hConstTy
  have hTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hRhsEoTy :
      __eo_typeof (bvShlByConst1Rhs x (Term.Numeral A)
          (Term.Numeral E)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hLhsTy] at hTypes
    exact hTypes.symm
  have hRhsSmtTy := rhs_smt_type_of_eo_bitvec_type
    (bvShlByConst1Rhs x (Term.Numeral A) (Term.Numeral E)) W
    hRhsTrans hRhsEoTy hW0
  exact ⟨W, A, E, rfl, rfl, rfl, hW0, hA0, hEW', hD0',
    hXSmtTy, hRhsSmtTy⟩

private theorem typed_bv_lshr_by_const_1_term
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvLshrByConst1Term x amount sz nm) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  rcases bv_lshr_by_const_1_context x amount sz nm hXTrans hAmountTrans
      hSzTrans hNmTrans hResultTy with
    ⟨W, A, N, rfl, rfl, rfl, hW0, _hA0, _hNW, _hD0,
      hXSmtTy, hRhsSmtTy⟩
  have hLhsSmtTy := smt_typeof_bvlshr_same1 x (Term.Numeral A) W
    hXSmtTy rfl hW0
  unfold bvLshrByConst1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsSmtTy.trans hRhsSmtTy.symm)
    (by rw [hLhsSmtTy]; intro h; cases h)

private theorem typed_bv_shl_by_const_1_term
    (x amount sz en : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvShlByConst1Term x amount sz en) := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy
  rcases bv_shl_by_const_1_context x amount sz en hXTrans hAmountTrans
      hSzTrans hEnTrans hResultTy with
    ⟨W, A, E, rfl, rfl, rfl, hW0, _hA0, _hEW, _hD0,
      hXSmtTy, hRhsSmtTy⟩
  have hLhsSmtTy := smt_typeof_bvshl_same1 x (Term.Numeral A) W
    hXSmtTy rfl hW0
  unfold bvShlByConst1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsSmtTy.trans hRhsSmtTy.symm)
    (by rw [hLhsSmtTy]; intro h; cases h)

private theorem eval_bv_term_local1
    (M : SmtModel) (hM : model_total_typed M)
    (t : Term) (W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt t) =
      SmtType.BitVec (native_int_to_nat W) ->
    exists p : native_Int,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary W p /\
      native_zeq p (native_mod_total p (native_int_pow2 W)) = true := by
  intro hW0 hTy
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt t)
      (native_int_to_nat W) hTy with
    ⟨p, hEval, hCanonical⟩
  have hRound := native_int_to_nat_roundtrip W hW0
  have hEval' :
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary W p := by
    simpa [hRound] using hEval
  have hCanonical' :
      native_zeq p (native_mod_total p (native_int_pow2 W)) = true := by
    simpa [hRound] using hCanonical
  exact ⟨p, hEval', hCanonical'⟩

private theorem eval_bvsize_local1
    (M : SmtModel) (x : Term) (W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M (__eo_to_smt (bvShiftByConst2Bvsize x)) =
      SmtValue.Numeral W := by
  intro hW0 hXTy
  have hRound := native_int_to_nat_roundtrip W hW0
  have hSize :
      __smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x)) = W := by
    rw [hXTy]
    exact hRound
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0
          (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral W
  rw [hSize]
  simp [native_ite, hW0, __smtx_model_eval,
    __smtx_model_eval__at_purify]

private theorem model_eval_eq_true_of_eo_eq_true1
    (M : SmtModel) (x y : Term) :
    eo_interprets M
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) =
        SmtValue.Boolean true := by
  intro h
  rw [RuleProofs.eo_interprets_iff_smt_interprets,
    RuleProofs.eo_to_smt_eq_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [smtx_eval_eq_term_eq] at hEval
      exact hEval

private theorem eval_lt_width_local1
    (M : SmtModel) (x : Term) (A W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral A))
            (bvShiftByConst2Bvsize x))) =
      SmtValue.Boolean (native_zlt A W) := by
  intro hW0 hXTy
  change __smtx_model_eval M
      (SmtTerm.lt (SmtTerm.Numeral A)
        (__eo_to_smt (bvShiftByConst2Bvsize x))) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bvsize_local1 M x W hW0 hXTy]
  simp [__smtx_model_eval, __smtx_model_eval_lt]

private theorem eval_bvsize_minus_one1
    (M : SmtModel) (x : Term) (W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
            (bvShiftByConst2Bvsize x)) (Term.Numeral 1))) =
      SmtValue.Numeral (native_zplus W (native_zneg 1)) := by
  intro hW0 hXTy
  change __smtx_model_eval M
      (SmtTerm.neg (__eo_to_smt (bvShiftByConst2Bvsize x))
        (SmtTerm.Numeral 1)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bvsize_local1 M x W hW0 hXTy]
  simp [__smtx_model_eval, __smtx_model_eval__, native_zplus, native_zneg]

private theorem eval_shl_end_local1
    (M : SmtModel) (x : Term) (A W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.neg) (bvShiftByConst2Bvsize x))
            (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
              (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
                (Term.Numeral A)) (Term.Numeral 0))))) =
      SmtValue.Numeral
        (native_zplus W
          (native_zneg (native_zplus 1 (native_zplus A 0)))) := by
  intro hW0 hXTy
  change __smtx_model_eval M
      (SmtTerm.neg (__eo_to_smt (bvShiftByConst2Bvsize x))
        (SmtTerm.plus (SmtTerm.Numeral 1)
          (SmtTerm.plus (SmtTerm.Numeral A) (SmtTerm.Numeral 0)))) = _
  have hInner :
      __smtx_model_eval M
          (SmtTerm.plus (SmtTerm.Numeral A) (SmtTerm.Numeral 0)) =
        SmtValue.Numeral (native_zplus A 0) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    simp [__smtx_model_eval, __smtx_model_eval_plus]
  have hOuter :
      __smtx_model_eval M
          (SmtTerm.plus (SmtTerm.Numeral 1)
            (SmtTerm.plus (SmtTerm.Numeral A) (SmtTerm.Numeral 0))) =
        SmtValue.Numeral (native_zplus 1 (native_zplus A 0)) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hInner]
    simp [__smtx_model_eval, __smtx_model_eval_plus]
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bvsize_local1 M x W hW0 hXTy, hOuter]
  simp [__smtx_model_eval, __smtx_model_eval__, native_zplus, native_zneg]

private theorem bv_lshr_by_const_1_premises_numeric
    (M : SmtModel) (x : Term) (A N W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    eo_interprets M
      (bvShiftByConst1LtPrem x (Term.Numeral A)) true ->
    eo_interprets M
      (bvLshrByConst1NmPrem x (Term.Numeral N)) true ->
    native_zlt A W = true /\
      N = native_zplus W (native_zneg 1) := by
  intro hW0 hXSmtTy hLtPrem hNmPrem
  have hLtEq := model_eval_eq_true_of_eo_eq_true1 M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral A))
      (bvShiftByConst2Bvsize x)) (Term.Boolean true)
    (by simpa [bvShiftByConst1LtPrem] using hLtPrem)
  have hNmEq := model_eval_eq_true_of_eo_eq_true1 M
    (Term.Numeral N)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvShiftByConst2Bvsize x)) (Term.Numeral 1))
    (by simpa [bvLshrByConst1NmPrem] using hNmPrem)
  rw [eval_lt_width_local1 M x A W hW0 hXSmtTy] at hLtEq
  rw [eval_bvsize_minus_one1 M x W hW0 hXSmtTy] at hNmEq
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by rfl
  rw [hTrueEval] at hLtEq
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral N))
      (SmtValue.Numeral (native_zplus W (native_zneg 1))) =
    SmtValue.Boolean true at hNmEq
  rw [__smtx_model_eval.eq_def] at hNmEq
  simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] at hLtEq hNmEq
  exact ⟨hLtEq, hNmEq⟩

private theorem bv_shl_by_const_1_premises_numeric
    (M : SmtModel) (x : Term) (A E W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    eo_interprets M
      (bvShiftByConst1LtPrem x (Term.Numeral A)) true ->
    eo_interprets M
      (bvShlByConst1EnPrem x (Term.Numeral A) (Term.Numeral E)) true ->
    native_zlt A W = true /\
      E = native_zplus W
        (native_zneg (native_zplus 1 (native_zplus A 0))) := by
  intro hW0 hXSmtTy hLtPrem hEnPrem
  have hLtEq := model_eval_eq_true_of_eo_eq_true1 M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) (Term.Numeral A))
      (bvShiftByConst2Bvsize x)) (Term.Boolean true)
    (by simpa [bvShiftByConst1LtPrem] using hLtPrem)
  have hEnEq := model_eval_eq_true_of_eo_eq_true1 M
    (Term.Numeral E)
    (Term.Apply
      (Term.Apply (Term.UOp UserOp.neg) (bvShiftByConst2Bvsize x))
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus)
          (Term.Numeral A)) (Term.Numeral 0))))
    (by simpa [bvShlByConst1EnPrem] using hEnPrem)
  rw [eval_lt_width_local1 M x A W hW0 hXSmtTy] at hLtEq
  rw [eval_shl_end_local1 M x A W hW0 hXSmtTy] at hEnEq
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by rfl
  rw [hTrueEval] at hLtEq
  change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.Numeral E))
      (SmtValue.Numeral
        (native_zplus W
          (native_zneg (native_zplus 1 (native_zplus A 0))))) =
    SmtValue.Boolean true at hEnEq
  rw [__smtx_model_eval.eq_def] at hEnEq
  simp [__smtx_model_eval, __smtx_model_eval_eq, native_veq,
    SmtEval.native_zeq] at hLtEq hEnEq
  exact ⟨hLtEq, hEnEq⟩

private theorem native_int_pow2_add_of_nonneg_local1
    {a b : native_Int} (ha : 0 <= a) (hb : 0 <= b) :
    native_int_pow2 (a + b) =
      native_int_pow2 a * native_int_pow2 b := by
  have hna : ¬ a < 0 := Int.not_lt_of_ge ha
  have hnb : ¬ b < 0 := Int.not_lt_of_ge hb
  have hab : ¬ a + b < 0 := Int.not_lt_of_ge (Int.add_nonneg ha hb)
  have hto : Int.toNat (a + b) = Int.toNat a + Int.toNat b :=
    Int.toNat_add ha hb
  rw [native_int_pow2, native_int_pow2, native_int_pow2,
    native_zexp_total, native_zexp_total, native_zexp_total]
  simp [hna, hnb, hab, hto]
  exact Int.pow_add 2 (Int.toNat a) (Int.toNat b)

private theorem int_lt_native_int_pow2_of_nonneg_lt
    {A W : native_Int} (hA0 : 0 <= A) (hAW : A < W) :
    A < native_int_pow2 W := by
  have hW0 : 0 <= W := Int.le_trans hA0 (Int.le_of_lt hAW)
  have hWNotNeg : ¬ W < 0 := Int.not_lt_of_ge hW0
  have hWCast : (Int.toNat W : Int) = W := Int.toNat_of_nonneg hW0
  have hNat : Int.toNat W < 2 ^ Int.toNat W := Nat.lt_two_pow_self
  have hInt :
      (Int.toNat W : Int) < ((2 ^ Int.toNat W : Nat) : Int) := by
    exact_mod_cast hNat
  have hWPow : W < native_int_pow2 W := by
    rw [native_int_pow2, native_zexp_total, if_neg hWNotNeg]
    rw [← hWCast]
    exact_mod_cast hNat
  exact Int.lt_trans hAW hWPow

private theorem eval_shift_amount_numeral1
    (M : SmtModel) (A W : native_Int) :
    native_zleq 0 A = true ->
    native_zlt A W = true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvShiftByConst2Const (Term.Numeral A) (Term.Numeral W))) =
      SmtValue.Binary W A := by
  intro hA0 hAW
  have ha0 : (0 : Int) <= A := by
    simpa [SmtEval.native_zleq] using hA0
  have haw : A < W := by
    simpa [SmtEval.native_zlt] using hAW
  have hAPow : A < native_int_pow2 W :=
    int_lt_native_int_pow2_of_nonneg_lt ha0 haw
  have hMod : native_mod_total A (native_int_pow2 W) = A := by
    simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt ha0 hAPow
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral W) (SmtTerm.Numeral A)) = _
  rw [smtx_eval_int_to_bv_term_eq]
  change __smtx_model_eval_int_to_bv
      (SmtValue.Numeral W) (SmtValue.Numeral A) = _
  simp [__smtx_model_eval_int_to_bv, hMod]

private theorem eval_shift_zero_numeral1
    (M : SmtModel) (A : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvShiftByConst1Zero (Term.Numeral A))) =
      SmtValue.Binary A 0 := by
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral A) (SmtTerm.Numeral 0)) = _
  simp [native_mod_total]

private theorem native_int_pow2_pos_of_nonneg_local1
    {w : native_Int} (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

private theorem lshr_const1_value_local
    (W A N p : native_Int)
    (hW0 : 0 <= W) (hA0 : 0 <= A) (hAW : A < W)
    (hN : N = W - 1)
    (hp0 : 0 <= p) (hpW : p < native_int_pow2 W) :
    __smtx_model_eval_bvlshr
        (SmtValue.Binary W p) (SmtValue.Binary W A) =
      __smtx_model_eval_concat
        (SmtValue.Binary A 0)
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral A)
            (SmtValue.Binary W p))
          (SmtValue.Binary 0 0)) := by
  let D : native_Int := W - A
  let q : native_Int := native_div_total p (native_int_pow2 A)
  have hD0 : 0 <= D := by
    dsimp [D]
    exact Int.sub_nonneg.mpr (Int.le_of_lt hAW)
  have hDW : D <= W := by
    dsimp [D]
    exact Int.sub_le_self W hA0
  have hWidthExtract : N + 1 + -A = D := by
    dsimp [D]
    rw [hN]
    have hCancel : W - 1 + 1 = W := Int.sub_add_cancel W 1
    rw [hCancel]
    rfl
  have hWidthTotal : A + D = W := by
    dsimp [D]
    calc
      A + (W - A) = A + W - A := by rw [Int.add_sub_assoc]
      _ = W + A - A := by rw [Int.add_comm A W]
      _ = W := Int.add_sub_cancel W A
  have hPow : native_int_pow2 W =
      native_int_pow2 A * native_int_pow2 D := by
    rw [← hWidthTotal]
    exact native_int_pow2_add_of_nonneg_local1 hA0 hD0
  have hPowA0 : 0 < native_int_pow2 A :=
    native_int_pow2_pos_of_nonneg_local1 hA0
  have hq0 : 0 <= q := by
    dsimp [q, native_div_total]
    exact Int.ediv_nonneg hp0 (Int.le_of_lt hPowA0)
  have hqD : q < native_int_pow2 D := by
    dsimp [q, native_div_total]
    apply Int.ediv_lt_of_lt_mul hPowA0
    rw [Int.mul_comm, ← hPow]
    exact hpW
  have hqW : q < native_int_pow2 W := by
    exact Int.lt_of_lt_of_le hqD
      (native_int_pow2_le_of_le_nonneg hD0 hDW)
  have hqModD : native_mod_total q (native_int_pow2 D) = q := by
    simpa [native_mod_total] using Int.emod_eq_of_lt hq0 hqD
  have hqModW : native_mod_total q (native_int_pow2 W) = q := by
    simpa [native_mod_total] using Int.emod_eq_of_lt hq0 hqW
  have hPowZero : native_int_pow2 0 = 1 := by native_decide
  simp only [__smtx_model_eval_bvlshr, __smtx_model_eval_concat,
    __smtx_model_eval_extract, native_binary_extract, native_binary_concat]
  simp [native_zplus, native_zneg, native_zmult, hWidthExtract,
    hWidthTotal, hPowZero, hqModD, hqModW]
  change native_mod_total q (native_int_pow2 W) =
    native_mod_total
      (native_mod_total (native_mod_total q (native_int_pow2 D))
        (native_int_pow2 D)) (native_int_pow2 W)
  simp [hqModD]

private theorem eval_bv_lshr_by_const_1_term
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvLshrByConst1NmPrem x nm) true ->
    __smtx_model_eval M (__eo_to_smt (bvLshrByConst2Lhs x amount sz)) =
      __smtx_model_eval M (__eo_to_smt (bvLshrByConst1Rhs x amount nm)) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy hLtPrem hNmPrem
  rcases bv_lshr_by_const_1_context x amount sz nm hXTrans hAmountTrans
      hSzTrans hNmTrans hResultTy with
    ⟨W, A, N, rfl, rfl, rfl, hW0, hA0, _hNW, _hD0,
      hXSmtTy, _hRhsSmtTy⟩
  rcases bv_lshr_by_const_1_premises_numeric M x A N W hW0 hXSmtTy
      hLtPrem hNmPrem with ⟨hAW, hN⟩
  have hw0 : (0 : Int) <= W := by
    simpa [SmtEval.native_zleq] using hW0
  have ha0 : (0 : Int) <= A := by
    simpa [SmtEval.native_zleq] using hA0
  have haw : A < W := by
    simpa [SmtEval.native_zlt] using hAW
  have hn : N = W - 1 := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hN
  rcases eval_bv_term_local1 M hM x W hW0 hXSmtTy with
    ⟨p, hXEval, hCanonical⟩
  have hRange := bitvec_payload_range_of_canonical hW0 hCanonical
  have hAmountEval := eval_shift_amount_numeral1 M A W hA0 hAW
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvLshrByConst2Lhs x (Term.Numeral A) (Term.Numeral W))) =
        __smtx_model_eval_bvlshr
          (SmtValue.Binary W p) (SmtValue.Binary W A) := by
    change __smtx_model_eval M
        (SmtTerm.bvlshr (__eo_to_smt x)
          (__eo_to_smt
            (bvShiftByConst2Const (Term.Numeral A) (Term.Numeral W)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hXEval, hAmountEval]
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral N) (Term.Numeral A))) =
        __smtx_model_eval_extract
          (SmtValue.Numeral N) (SmtValue.Numeral A)
          (SmtValue.Binary W p) := by
    rw [eval_extract_term, hXEval]
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := by rfl
  have hInnerEval := eval_concat_term M
    (bvExtractTerm x (Term.Numeral N) (Term.Numeral A))
    (Term.Binary 0 0)
    (__smtx_model_eval_extract
      (SmtValue.Numeral N) (SmtValue.Numeral A)
      (SmtValue.Binary W p))
    (SmtValue.Binary 0 0) hExtractEval hEmptyEval
  have hZeroEval := eval_shift_zero_numeral1 M A
  have hRhsEval := eval_concat_term M
    (bvShiftByConst1Zero (Term.Numeral A))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvExtractTerm x (Term.Numeral N) (Term.Numeral A)))
      (Term.Binary 0 0))
    (SmtValue.Binary A 0)
    (__smtx_model_eval_concat
      (__smtx_model_eval_extract
        (SmtValue.Numeral N) (SmtValue.Numeral A)
        (SmtValue.Binary W p))
      (SmtValue.Binary 0 0)) hZeroEval hInnerEval
  rw [hLhsEval]
  change __smtx_model_eval_bvlshr
      (SmtValue.Binary W p) (SmtValue.Binary W A) =
    __smtx_model_eval M
      (__eo_to_smt
        (bvLshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N)))
  rw [show __smtx_model_eval M
        (__eo_to_smt
          (bvLshrByConst1Rhs x (Term.Numeral A) (Term.Numeral N))) =
      __smtx_model_eval_concat
        (SmtValue.Binary A 0)
        (__smtx_model_eval_concat
          (__smtx_model_eval_extract
            (SmtValue.Numeral N) (SmtValue.Numeral A)
            (SmtValue.Binary W p))
          (SmtValue.Binary 0 0)) by
      simpa [bvLshrByConst1Rhs] using hRhsEval]
  exact lshr_const1_value_local W A N p hw0 ha0 haw hn
    hRange.1 hRange.2

private theorem facts_bv_lshr_by_const_1_term
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz nm : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvLshrByConst1NmPrem x nm) true ->
    eo_interprets M (bvLshrByConst1Term x amount sz nm) true := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy hLtPrem hNmPrem
  have hBool := typed_bv_lshr_by_const_1_term x amount sz nm
    hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  unfold bvLshrByConst1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvLshrByConst1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvLshrByConst2Lhs x amount sz)))
      (__smtx_model_eval M (__eo_to_smt (bvLshrByConst1Rhs x amount nm)))
    rw [eval_bv_lshr_by_const_1_term M hM x amount sz nm hXTrans
      hAmountTrans hSzTrans hNmTrans hResultTy hLtPrem hNmPrem]
    exact RuleProofs.smt_value_rel_refl _

private theorem shl_mod_extract_local
    (p D A : native_Int) :
    native_int_pow2 (D + A) =
        native_int_pow2 D * native_int_pow2 A ->
    native_mod_total
        (native_zmult (native_mod_total p (native_int_pow2 D))
          (native_int_pow2 A))
        (native_int_pow2 (D + A)) =
      native_mod_total (native_zmult p (native_int_pow2 A))
        (native_int_pow2 (D + A)) := by
  intro hPow
  let d := native_int_pow2 D
  let a := native_int_pow2 A
  let q := p / d
  let r := p % d
  have hDivMod : d * q + r = p := by
    simpa [d, q, r] using Int.mul_ediv_add_emod p d
  have hDistrib : (d * q + r) * a = (d * a) * q + r * a := by
    rw [Int.add_mul]
    congr 1
    ac_rfl
  have hCong : (p * a) % (d * a) = (r * a) % (d * a) := by
    calc
      (p * a) % (d * a) = ((d * q + r) * a) % (d * a) := by
        rw [hDivMod]
      _ = ((d * a) * q + r * a) % (d * a) := by rw [hDistrib]
      _ = (r * a) % (d * a) := by
        rw [Int.add_emod]
        simp [Int.mul_emod_right]
  change
    (p % native_int_pow2 D * native_int_pow2 A) %
        native_int_pow2 (D + A) =
      (p * native_int_pow2 A) % native_int_pow2 (D + A)
  rw [hPow]
  simpa [d, a, r] using hCong.symm

private theorem shl_const1_value_local
    (W A E p : native_Int)
    (hW0 : 0 <= W) (hA0 : 0 <= A) (hAW : A < W)
    (hE : E = W - (1 + A)) :
    __smtx_model_eval_bvshl
        (SmtValue.Binary W p) (SmtValue.Binary W A) =
      __smtx_model_eval_concat
        (__smtx_model_eval_extract
          (SmtValue.Numeral E) (SmtValue.Numeral 0)
          (SmtValue.Binary W p))
        (__smtx_model_eval_concat
          (SmtValue.Binary A 0) (SmtValue.Binary 0 0)) := by
  let D : native_Int := W - A
  have hD0 : 0 <= D := by
    dsimp [D]
    exact Int.sub_nonneg.mpr (Int.le_of_lt hAW)
  have hWidthExtract : E + 1 = D := by
    dsimp [D]
    rw [hE]
    calc
      W - (1 + A) + 1 = W + (-(1 + A)) + 1 := by
        rw [Int.sub_eq_add_neg]
      _ = W + (-A) + (-1 + 1) := by
        rw [Int.neg_add]
        ac_rfl
      _ = W - A := by simp [Int.sub_eq_add_neg]
  have hWidthTotal : D + A = W := by
    dsimp [D]
    exact Int.sub_add_cancel W A
  have hPow : native_int_pow2 (D + A) =
      native_int_pow2 D * native_int_pow2 A :=
    native_int_pow2_add_of_nonneg_local1 hD0 hA0
  have hPowZero : native_int_pow2 0 = 1 := by native_decide
  have hDivZero : native_div_total p (native_int_pow2 0) = p := by
    simp [native_div_total, hPowZero]
  have hDivOne : native_div_total p 1 = p := by
    simp [native_div_total]
  have hZeroModA : native_mod_total 0 (native_int_pow2 A) = 0 := by
    simp [native_mod_total]
  have hResidueCanonical :
      native_mod_total
          (native_mod_total p (native_int_pow2 D))
          (native_int_pow2 D) =
        native_mod_total p (native_int_pow2 D) := by
    simp [native_mod_total]
  have hLift := shl_mod_extract_local p D A hPow
  simp only [__smtx_model_eval_bvshl, __smtx_model_eval_concat,
    __smtx_model_eval_extract, native_binary_extract, native_binary_concat]
  simp [native_zplus, native_zneg, native_zmult, hWidthExtract,
    hWidthTotal, hPowZero, hDivZero, hResidueCanonical]
  rw [hDivOne, hZeroModA, Int.add_zero]
  change native_mod_total (native_zmult p (native_int_pow2 A))
      (native_int_pow2 W) =
    native_mod_total
      (native_zmult (native_mod_total p (native_int_pow2 D))
        (native_int_pow2 A)) (native_int_pow2 W)
  rw [← hWidthTotal]
  exact hLift.symm

private theorem eval_bv_shl_by_const_1_term
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz en : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvShlByConst1EnPrem x amount en) true ->
    __smtx_model_eval M (__eo_to_smt (bvShlByConst2Lhs x amount sz)) =
      __smtx_model_eval M (__eo_to_smt (bvShlByConst1Rhs x amount en)) := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy hLtPrem hEnPrem
  rcases bv_shl_by_const_1_context x amount sz en hXTrans hAmountTrans
      hSzTrans hEnTrans hResultTy with
    ⟨W, A, E, rfl, rfl, rfl, hW0, hA0, _hEW, _hD0,
      hXSmtTy, _hRhsSmtTy⟩
  rcases bv_shl_by_const_1_premises_numeric M x A E W hW0 hXSmtTy
      hLtPrem hEnPrem with ⟨hAW, hE⟩
  have hw0 : (0 : Int) <= W := by
    simpa [SmtEval.native_zleq] using hW0
  have ha0 : (0 : Int) <= A := by
    simpa [SmtEval.native_zleq] using hA0
  have haw : A < W := by
    simpa [SmtEval.native_zlt] using hAW
  have he : E = W - (1 + A) := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg,
      Int.sub_eq_add_neg] using hE
  rcases eval_bv_term_local1 M hM x W hW0 hXSmtTy with
    ⟨p, hXEval, _hCanonical⟩
  have hAmountEval := eval_shift_amount_numeral1 M A W hA0 hAW
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvShlByConst2Lhs x (Term.Numeral A) (Term.Numeral W))) =
        __smtx_model_eval_bvshl
          (SmtValue.Binary W p) (SmtValue.Binary W A) := by
    change __smtx_model_eval M
        (SmtTerm.bvshl (__eo_to_smt x)
          (__eo_to_smt
            (bvShiftByConst2Const (Term.Numeral A) (Term.Numeral W)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hXEval, hAmountEval]
  have hExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvExtractTerm x (Term.Numeral E) (Term.Numeral 0))) =
        __smtx_model_eval_extract
          (SmtValue.Numeral E) (SmtValue.Numeral 0)
          (SmtValue.Binary W p) := by
    rw [eval_extract_term, hXEval]
  have hEmptyEval :
      __smtx_model_eval M (__eo_to_smt (Term.Binary 0 0)) =
        SmtValue.Binary 0 0 := by rfl
  have hZeroEval := eval_shift_zero_numeral1 M A
  have hInnerEval := eval_concat_term M
    (bvShiftByConst1Zero (Term.Numeral A)) (Term.Binary 0 0)
    (SmtValue.Binary A 0) (SmtValue.Binary 0 0)
    hZeroEval hEmptyEval
  have hRhsEval := eval_concat_term M
    (bvExtractTerm x (Term.Numeral E) (Term.Numeral 0))
    (Term.Apply (Term.Apply (Term.UOp UserOp.concat)
      (bvShiftByConst1Zero (Term.Numeral A))) (Term.Binary 0 0))
    (__smtx_model_eval_extract
      (SmtValue.Numeral E) (SmtValue.Numeral 0)
      (SmtValue.Binary W p))
    (__smtx_model_eval_concat
      (SmtValue.Binary A 0) (SmtValue.Binary 0 0))
    hExtractEval hInnerEval
  rw [hLhsEval]
  change __smtx_model_eval_bvshl
      (SmtValue.Binary W p) (SmtValue.Binary W A) =
    __smtx_model_eval M
      (__eo_to_smt
        (bvShlByConst1Rhs x (Term.Numeral A) (Term.Numeral E)))
  rw [show __smtx_model_eval M
        (__eo_to_smt
          (bvShlByConst1Rhs x (Term.Numeral A) (Term.Numeral E))) =
      __smtx_model_eval_concat
        (__smtx_model_eval_extract
          (SmtValue.Numeral E) (SmtValue.Numeral 0)
          (SmtValue.Binary W p))
        (__smtx_model_eval_concat
          (SmtValue.Binary A 0) (SmtValue.Binary 0 0)) by
      simpa [bvShlByConst1Rhs] using hRhsEval]
  exact shl_const1_value_local W A E p hw0 ha0 haw he

private theorem facts_bv_shl_by_const_1_term
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz en : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool ->
    eo_interprets M (bvShiftByConst1LtPrem x amount) true ->
    eo_interprets M (bvShlByConst1EnPrem x amount en) true ->
    eo_interprets M (bvShlByConst1Term x amount sz en) true := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy hLtPrem hEnPrem
  have hBool := typed_bv_shl_by_const_1_term x amount sz en
    hXTrans hAmountTrans hSzTrans hEnTrans hResultTy
  unfold bvShlByConst1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvShlByConst1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (bvShlByConst2Lhs x amount sz)))
      (__smtx_model_eval M (__eo_to_smt (bvShlByConst1Rhs x amount en)))
    rw [eval_bv_shl_by_const_1_term M hM x amount sz en hXTrans
      hAmountTrans hSzTrans hEnTrans hResultTy hLtPrem hEnPrem]
    exact RuleProofs.smt_value_rel_refl _

def bvShlByConst1Program
    (x amount sz en P1 P2 : Term) : Term :=
  __eo_prog_bv_shl_by_const_1 x amount sz en (Proof.pf P1) (Proof.pf P2)

def bvLshrByConst1Program
    (x amount sz nm P1 P2 : Term) : Term :=
  __eo_prog_bv_lshr_by_const_1 x amount sz nm (Proof.pf P1) (Proof.pf P2)

private theorem shift_and_true1 {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true /\ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h |-
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h |-

private def bvShlByConst1Guard
    (x amount en amountRef1 xRef1 enRef xRef2 amountRef2 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and (__eo_eq amount amountRef1) (__eo_eq x xRef1))
        (__eo_eq en enRef))
      (__eo_eq x xRef2))
    (__eo_eq amount amountRef2)

private def bvLshrByConst1Guard
    (x amount nm amountRef xRef1 nmRef xRef2 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and (__eo_eq amount amountRef) (__eo_eq x xRef1))
      (__eo_eq nm nmRef))
    (__eo_eq x xRef2)

private theorem bv_shl_by_const_1_guard_refs
    {x amount en amountRef1 xRef1 enRef xRef2 amountRef2 body : Term} :
    __eo_requires
        (bvShlByConst1Guard x amount en amountRef1 xRef1 enRef xRef2
          amountRef2)
        (Term.Boolean true) body ≠ Term.Stuck ->
    amountRef1 = amount /\ xRef1 = x /\ enRef = en /\
      xRef2 = x /\ amountRef2 = amount := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvShlByConst1Guard at hGuard
  rcases shift_and_true1 hGuard with ⟨hG4, hAmount2⟩
  rcases shift_and_true1 hG4 with ⟨hG3, hX2⟩
  rcases shift_and_true1 hG3 with ⟨hG2, hEn⟩
  rcases shift_and_true1 hG2 with ⟨hAmount1, hX1⟩
  exact ⟨support_eq_of_eo_eq_true amount amountRef1 hAmount1,
    support_eq_of_eo_eq_true x xRef1 hX1,
    support_eq_of_eo_eq_true en enRef hEn,
    support_eq_of_eo_eq_true x xRef2 hX2,
    support_eq_of_eo_eq_true amount amountRef2 hAmount2⟩

private theorem bv_lshr_by_const_1_guard_refs
    {x amount nm amountRef xRef1 nmRef xRef2 body : Term} :
    __eo_requires
        (bvLshrByConst1Guard x amount nm amountRef xRef1 nmRef xRef2)
        (Term.Boolean true) body ≠ Term.Stuck ->
    amountRef = amount /\ xRef1 = x /\ nmRef = nm /\ xRef2 = x := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvLshrByConst1Guard at hGuard
  rcases shift_and_true1 hGuard with ⟨hG3, hX2⟩
  rcases shift_and_true1 hG3 with ⟨hG2, hNm⟩
  rcases shift_and_true1 hG2 with ⟨hAmount, hX1⟩
  exact ⟨support_eq_of_eo_eq_true amount amountRef hAmount,
    support_eq_of_eo_eq_true x xRef1 hX1,
    support_eq_of_eo_eq_true nm nmRef hNm,
    support_eq_of_eo_eq_true x xRef2 hX2⟩

private theorem bv_shl_by_const_1_premise_shape
    (x amount sz en P1 P2 : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    en ≠ Term.Stuck ->
    bvShlByConst1Program x amount sz en P1 P2 ≠ Term.Stuck ->
    exists amountRef1 xRef1 enRef xRef2 amountRef2,
      P1 = bvShiftByConst1LtPrem xRef1 amountRef1 /\
      P2 = bvShlByConst1EnPrem xRef2 amountRef2 enRef := by
  intro hX hAmount hSz hEn hProg
  by_cases hShape :
      exists amountRef1 xRef1 enRef xRef2 amountRef2,
        P1 = bvShiftByConst1LtPrem xRef1 amountRef1 /\
        P2 = bvShlByConst1EnPrem xRef2 amountRef2 enRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_shl_by_const_1.eq_6 x amount sz en
      (Proof.pf P1) (Proof.pf P2) hX hAmount hSz hEn (by
        intro amountRef1 xRef1 enRef xRef2 amountRef2 hP1 hP2
        cases hP1
        cases hP2
        exact hShape
          ⟨amountRef1, xRef1, enRef, xRef2, amountRef2, rfl, rfl⟩)

private theorem bv_lshr_by_const_1_premise_shape
    (x amount sz nm P1 P2 : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    nm ≠ Term.Stuck ->
    bvLshrByConst1Program x amount sz nm P1 P2 ≠ Term.Stuck ->
    exists amountRef xRef1 nmRef xRef2,
      P1 = bvShiftByConst1LtPrem xRef1 amountRef /\
      P2 = bvLshrByConst1NmPrem xRef2 nmRef := by
  intro hX hAmount hSz hNm hProg
  by_cases hShape :
      exists amountRef xRef1 nmRef xRef2,
        P1 = bvShiftByConst1LtPrem xRef1 amountRef /\
        P2 = bvLshrByConst1NmPrem xRef2 nmRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_lshr_by_const_1.eq_6 x amount sz nm
      (Proof.pf P1) (Proof.pf P2) hX hAmount hSz hNm (by
        intro amountRef xRef1 nmRef xRef2 hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨amountRef, xRef1, nmRef, xRef2, rfl, rfl⟩)

private theorem bv_shl_by_const_1_program_canonical
    (x amount sz en : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    en ≠ Term.Stuck ->
    bvShlByConst1Program x amount sz en
        (bvShiftByConst1LtPrem x amount)
        (bvShlByConst1EnPrem x amount en) =
      bvShlByConst1Term x amount sz en := by
  intro hX hAmount hSz hEn
  unfold bvShlByConst1Program bvShiftByConst1LtPrem
    bvShlByConst1EnPrem bvShiftByConst2Bvsize
  rw [__eo_prog_bv_shl_by_const_1.eq_5 x amount sz en
    amount x en x amount hX hAmount hSz hEn]
  simp [bvShlByConst1Term, bvShlByConst2Lhs, bvShlByConst1Rhs,
    bvShiftByConst1Zero, bvShiftByConst2Const, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount, hEn]

private theorem bv_lshr_by_const_1_program_canonical
    (x amount sz nm : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    nm ≠ Term.Stuck ->
    bvLshrByConst1Program x amount sz nm
        (bvShiftByConst1LtPrem x amount)
        (bvLshrByConst1NmPrem x nm) =
      bvLshrByConst1Term x amount sz nm := by
  intro hX hAmount hSz hNm
  unfold bvLshrByConst1Program bvShiftByConst1LtPrem
    bvLshrByConst1NmPrem bvShiftByConst2Bvsize
  rw [__eo_prog_bv_lshr_by_const_1.eq_5 x amount sz nm
    amount x nm x hX hAmount hSz hNm]
  simp [bvLshrByConst1Term, bvLshrByConst2Lhs, bvLshrByConst1Rhs,
    bvShiftByConst1Zero, bvShiftByConst2Const, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount, hNm]

private theorem bvShlByConst1Program_normalize
    (x amount sz en P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    bvShlByConst1Program x amount sz en P1 P2 ≠ Term.Stuck ->
    P1 = bvShiftByConst1LtPrem x amount /\
      P2 = bvShlByConst1EnPrem x amount en /\
      bvShlByConst1Program x amount sz en P1 P2 =
        bvShlByConst1Term x amount sz en := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hAmount :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  have hSz := RuleProofs.term_ne_stuck_of_has_smt_translation sz hSzTrans
  have hEn := RuleProofs.term_ne_stuck_of_has_smt_translation en hEnTrans
  rcases bv_shl_by_const_1_premise_shape x amount sz en P1 P2
      hX hAmount hSz hEn hProg with
    ⟨amountRef1, xRef1, enRef, xRef2, amountRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvShlByConst1Program bvShiftByConst1LtPrem
    bvShlByConst1EnPrem bvShiftByConst2Bvsize at hReq
  rw [__eo_prog_bv_shl_by_const_1.eq_5 x amount sz en
    amountRef1 xRef1 enRef xRef2 amountRef2
    hX hAmount hSz hEn] at hReq
  have hRefs := bv_shl_by_const_1_guard_refs
    (x := x) (amount := amount) (en := en)
    (amountRef1 := amountRef1) (xRef1 := xRef1) (enRef := enRef)
    (xRef2 := xRef2) (amountRef2 := amountRef2)
    (by simpa [bvShlByConst1Guard] using hReq)
  rcases hRefs with
    ⟨hAmountRef1, hXRef1, hEnRef, hXRef2, hAmountRef2⟩
  subst amountRef1
  subst xRef1
  subst enRef
  subst xRef2
  subst amountRef2
  refine ⟨hP1, hP2, ?_⟩
  rw [hP1, hP2]
  exact bv_shl_by_const_1_program_canonical x amount sz en
    hX hAmount hSz hEn

private theorem bvLshrByConst1Program_normalize
    (x amount sz nm P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    bvLshrByConst1Program x amount sz nm P1 P2 ≠ Term.Stuck ->
    P1 = bvShiftByConst1LtPrem x amount /\
      P2 = bvLshrByConst1NmPrem x nm /\
      bvLshrByConst1Program x amount sz nm P1 P2 =
        bvLshrByConst1Term x amount sz nm := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hAmount :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  have hSz := RuleProofs.term_ne_stuck_of_has_smt_translation sz hSzTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_lshr_by_const_1_premise_shape x amount sz nm P1 P2
      hX hAmount hSz hNm hProg with
    ⟨amountRef, xRef1, nmRef, xRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvLshrByConst1Program bvShiftByConst1LtPrem
    bvLshrByConst1NmPrem bvShiftByConst2Bvsize at hReq
  rw [__eo_prog_bv_lshr_by_const_1.eq_5 x amount sz nm
    amountRef xRef1 nmRef xRef2 hX hAmount hSz hNm] at hReq
  have hRefs := bv_lshr_by_const_1_guard_refs
    (x := x) (amount := amount) (nm := nm)
    (amountRef := amountRef) (xRef1 := xRef1) (nmRef := nmRef)
    (xRef2 := xRef2)
    (by simpa [bvLshrByConst1Guard] using hReq)
  rcases hRefs with ⟨hAmountRef, hXRef1, hNmRef, hXRef2⟩
  subst amountRef
  subst xRef1
  subst nmRef
  subst xRef2
  refine ⟨hP1, hP2, ?_⟩
  rw [hP1, hP2]
  exact bv_lshr_by_const_1_program_canonical x amount sz nm
    hX hAmount hSz hNm

theorem typed_bv_shl_by_const_1_program
    (x amount sz en P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Program x amount sz en P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvShlByConst1Program x amount sz en P1 P2) := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvShlByConst1Program_normalize x amount sz en P1 P2
      hXTrans hAmountTrans hSzTrans hEnTrans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_shl_by_const_1_term x amount sz en
    hXTrans hAmountTrans hSzTrans hEnTrans hTermTy

theorem typed_bv_lshr_by_const_1_program
    (x amount sz nm P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Program x amount sz nm P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvLshrByConst1Program x amount sz nm P1 P2) := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvLshrByConst1Program_normalize x amount sz nm P1 P2
      hXTrans hAmountTrans hSzTrans hNmTrans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_lshr_by_const_1_term x amount sz nm
    hXTrans hAmountTrans hSzTrans hNmTrans hTermTy

theorem facts_bv_shl_by_const_1_program
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz en P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation en ->
    __eo_typeof (bvShlByConst1Program x amount sz en P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M (bvShlByConst1Program x amount sz en P1 P2) true := by
  intro hXTrans hAmountTrans hSzTrans hEnTrans hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvShlByConst1Program_normalize x amount sz en P1 P2
      hXTrans hAmountTrans hSzTrans hEnTrans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvShlByConst1Term x amount sz en) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hLtPrem : eo_interprets M (bvShiftByConst1LtPrem x amount) true := by
    simpa [hP1] using hP1True
  have hEnPrem : eo_interprets M (bvShlByConst1EnPrem x amount en) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_shl_by_const_1_term M hM x amount sz en
    hXTrans hAmountTrans hSzTrans hEnTrans hTermTy hLtPrem hEnPrem

theorem facts_bv_lshr_by_const_1_program
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz nm P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvLshrByConst1Program x amount sz nm P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M (bvLshrByConst1Program x amount sz nm P1 P2) true := by
  intro hXTrans hAmountTrans hSzTrans hNmTrans hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvLshrByConst1Program_normalize x amount sz nm P1 P2
      hXTrans hAmountTrans hSzTrans hNmTrans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvLshrByConst1Term x amount sz nm) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hLtPrem : eo_interprets M (bvShiftByConst1LtPrem x amount) true := by
    simpa [hP1] using hP1True
  have hNmPrem : eo_interprets M (bvLshrByConst1NmPrem x nm) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_lshr_by_const_1_term M hM x amount sz nm
    hXTrans hAmountTrans hSzTrans hNmTrans hTermTy hLtPrem hNmPrem
