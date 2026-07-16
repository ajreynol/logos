import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport

/-! Shared support for the out-of-range constant `bvshl` and `bvlshr` rewrites. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvShiftByConst2Bvsize (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_bvsize) x

def bvShiftByConst2GePrem (x amount : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) amount)
        (bvShiftByConst2Bvsize x)))
    (Term.Boolean true)

def bvShiftByConst2LtPrem (x amount : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) amount)
        (Term.Apply (Term.UOp UserOp.int_pow2)
          (bvShiftByConst2Bvsize x))))
    (Term.Boolean true)

def bvShiftByConst2WidthPrem (x w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) w)
    (bvShiftByConst2Bvsize x)

def bvShiftByConst2Const (amount sz : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv sz) amount

def bvShiftByConst2Zero (w : Term) : Term :=
  bvShiftByConst2Const (Term.Numeral 0) w

def bvShlByConst2Lhs (x amount sz : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) x)
    (bvShiftByConst2Const amount sz)

def bvLshrByConst2Lhs (x amount sz : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) x)
    (bvShiftByConst2Const amount sz)

def bvShlByConst2Term (x amount sz w : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvShlByConst2Lhs x amount sz)) (bvShiftByConst2Zero w)

def bvLshrByConst2Term (x amount sz : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq)
    (bvLshrByConst2Lhs x amount sz)) (bvShiftByConst2Zero sz)

private theorem typeof_bvand_arg_types_of_ne_stuck_local
    {A B : Term}
    (h : __eo_typeof_bvand A B ≠ Term.Stuck) :
    ∃ width,
      A = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) width := by
  cases A <;> cases B <;> simp [__eo_typeof_bvand] at h ⊢
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_bvand] at h ⊢
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_bvand] at h ⊢
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.BitVec) n) ≠
            Term.Stuck := by
        simpa [__eo_typeof_bvand] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

private theorem shift_operand_context
    (x amount sz : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    __eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)) ≠ Term.Stuck ->
    ∃ W : native_Int,
      sz = Term.Numeral W ∧ native_zleq 0 W = true ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __eo_typeof amount = Term.UOp UserOp.Int ∧
      __eo_typeof (bvShiftByConst2Const amount sz) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt amount) = SmtType.Int := by
  intro hXTrans hAmountTrans hSzTrans hLeftNe
  rcases typeof_bvand_arg_types_of_ne_stuck_local hLeftNe with
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

private theorem bv_lshr_by_const_2_context
    (x amount sz : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    __eo_typeof (bvLshrByConst2Term x amount sz) = Term.Bool ->
    ∃ W : native_Int,
      sz = Term.Numeral W ∧ native_zleq 0 W = true ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __eo_typeof amount = Term.UOp UserOp.Int ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt amount) = SmtType.Int := by
  intro hXTrans hAmountTrans hSzTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)))
      (__eo_typeof (bvShiftByConst2Zero sz)) = Term.Bool at hResultTy
  have hLeftNe :=
    (RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy).1
  rcases shift_operand_context x amount sz hXTrans hAmountTrans
      hSzTrans hLeftNe with
    ⟨W, hSz, hW0, hXTy, hAmountTy, _hConstTy,
      hXSmtTy, hAmountSmtTy⟩
  exact ⟨W, hSz, hW0, hXTy, hAmountTy, hXSmtTy, hAmountSmtTy⟩

private theorem bv_shl_by_const_2_context
    (x amount sz w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvShlByConst2Term x amount sz w) = Term.Bool ->
    ∃ W : native_Int,
      sz = Term.Numeral W ∧ w = Term.Numeral W ∧
      native_zleq 0 W = true ∧
      __eo_typeof x =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) ∧
      __eo_typeof amount = Term.UOp UserOp.Int ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt amount) = SmtType.Int := by
  intro hXTrans hAmountTrans hSzTrans hWTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvand (__eo_typeof x)
        (__eo_typeof (bvShiftByConst2Const amount sz)))
      (__eo_typeof (bvShiftByConst2Zero w)) = Term.Bool at hResultTy
  have hSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy
  rcases shift_operand_context x amount sz hXTrans hAmountTrans
      hSzTrans hSides.1 with
    ⟨W, hSz, hW0, hXTy, hAmountTy, hConstTy,
      hXSmtTy, hAmountSmtTy⟩
  have hTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hResultTy
  have hLeftTy :
      __eo_typeof_bvand (__eo_typeof x)
          (__eo_typeof (bvShiftByConst2Const amount sz)) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [hXTy, hConstTy]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hZeroTy :
      __eo_typeof (bvShiftByConst2Zero w) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W) := by
    rw [← hTypes]
    exact hLeftTy
  have hWNe :=
    RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  rcases bv_all_ones_const_context (Term.Numeral 0) w
      (Term.Numeral W) (by simp) hWNe
      (by simpa [bvAllOnesConst, bvShiftByConst2Zero,
          bvShiftByConst2Const] using hZeroTy) with
    ⟨W', hW, hWidth, _hW'0, _hZeroTy⟩
  have hWW' : W = W' := by
    injection hWidth
  subst W'
  exact ⟨W, hSz, hW, hW0, hXTy, hAmountTy,
    hXSmtTy, hAmountSmtTy⟩

private theorem smt_typeof_bvshl_same
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
          (__eo_to_smt
            (bvShiftByConst2Const amount (Term.Numeral W))) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [bvShiftByConst2Const] using hConstTy
  change __smtx_typeof
      (SmtTerm.bvshl (__eo_to_smt x)
        (__eo_to_smt
          (bvShiftByConst2Const amount (Term.Numeral W)))) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hConstTy',
    native_nateq, native_ite]

private theorem smt_typeof_bvlshr_same
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
          (__eo_to_smt
            (bvShiftByConst2Const amount (Term.Numeral W))) =
        SmtType.BitVec (native_int_to_nat W) := by
    simpa [bvShiftByConst2Const] using hConstTy
  change __smtx_typeof
      (SmtTerm.bvlshr (__eo_to_smt x)
        (__eo_to_smt
          (bvShiftByConst2Const amount (Term.Numeral W)))) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2, hXTy, hConstTy',
    native_nateq, native_ite]

private theorem smt_typeof_shift_zero (W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof
        (__eo_to_smt (bvShiftByConst2Zero (Term.Numeral W))) =
      SmtType.BitVec (native_int_to_nat W) := by
  intro hW0
  exact smt_typeof_bv_const_of_int_type (Term.Numeral 0) W rfl hW0

private theorem typed_bv_shl_by_const_2_term
    (x amount sz w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvShlByConst2Term x amount sz w) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvShlByConst2Term x amount sz w) := by
  intro hXTrans hAmountTrans hSzTrans hWTrans hResultTy
  rcases bv_shl_by_const_2_context x amount sz w hXTrans hAmountTrans
      hSzTrans hWTrans hResultTy with
    ⟨W, rfl, rfl, hW0, _hXTy, _hAmountTy, hXSmtTy, hAmountSmtTy⟩
  have hLhsTy := smt_typeof_bvshl_same x amount W
    hXSmtTy hAmountSmtTy hW0
  have hZeroTy := smt_typeof_shift_zero W hW0
  unfold bvShlByConst2Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hZeroTy.symm)
    (by rw [hLhsTy]; intro h; cases h)

private theorem typed_bv_lshr_by_const_2_term
    (x amount sz : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    __eo_typeof (bvLshrByConst2Term x amount sz) = Term.Bool ->
    RuleProofs.eo_has_bool_type (bvLshrByConst2Term x amount sz) := by
  intro hXTrans hAmountTrans hSzTrans hResultTy
  rcases bv_lshr_by_const_2_context x amount sz hXTrans hAmountTrans
      hSzTrans hResultTy with
    ⟨W, rfl, hW0, _hXTy, _hAmountTy, hXSmtTy, hAmountSmtTy⟩
  have hLhsTy := smt_typeof_bvlshr_same x amount W
    hXSmtTy hAmountSmtTy hW0
  have hZeroTy := smt_typeof_shift_zero W hW0
  unfold bvLshrByConst2Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsTy.trans hZeroTy.symm)
    (by rw [hLhsTy]; intro h; cases h)

private theorem eval_int_term_local
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Int ->
    ∃ k : native_Int,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Numeral k := by
  intro hTy
  have hEvalTy :=
    smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
      (by simp [term_has_non_none_type, hTy])
  exact int_value_canonical (by simpa [hTy] using hEvalTy)

private theorem eval_bv_term_local
    (M : SmtModel) (hM : model_total_typed M)
    (t : Term) (W : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt t) =
      SmtType.BitVec (native_int_to_nat W) ->
    ∃ p : native_Int,
      __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary W p ∧
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

private theorem eval_bvsize_local
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

private theorem model_eval_eq_true_of_eo_eq_true
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

private theorem eval_ge_width_local
    (M : SmtModel) (x amount : Term) (A W : native_Int) :
    __smtx_model_eval M (__eo_to_smt amount) = SmtValue.Numeral A ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.geq) amount)
            (bvShiftByConst2Bvsize x))) =
      SmtValue.Boolean (native_zleq W A) := by
  intro hAmountEval hW0 hXTy
  change __smtx_model_eval M
      (SmtTerm.geq (__eo_to_smt amount)
        (__eo_to_smt (bvShiftByConst2Bvsize x))) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hAmountEval, eval_bvsize_local M x W hW0 hXTy]
  simp [__smtx_model_eval_geq, __smtx_model_eval_leq]

private theorem eval_lt_pow_width_local
    (M : SmtModel) (x amount : Term) (A W : native_Int) :
    __smtx_model_eval M (__eo_to_smt amount) = SmtValue.Numeral A ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.lt) amount)
            (Term.Apply (Term.UOp UserOp.int_pow2)
              (bvShiftByConst2Bvsize x)))) =
      SmtValue.Boolean (native_zlt A (native_int_pow2 W)) := by
  intro hAmountEval hW0 hXTy
  change __smtx_model_eval M
      (SmtTerm.lt (__eo_to_smt amount)
        (SmtTerm.int_pow2
          (__eo_to_smt (bvShiftByConst2Bvsize x)))) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [hAmountEval]
  have hPowEval :
      __smtx_model_eval M
          (SmtTerm.int_pow2
            (__eo_to_smt (bvShiftByConst2Bvsize x))) =
        SmtValue.Numeral (native_int_pow2 W) := by
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [eval_bvsize_local M x W hW0 hXTy]
    rfl
  rw [hPowEval]
  rfl

private theorem shift_premises_numeric
    (M : SmtModel) (x amount : Term) (A W : native_Int) :
    __smtx_model_eval M (__eo_to_smt amount) = SmtValue.Numeral A ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    eo_interprets M (bvShiftByConst2GePrem x amount) true ->
    eo_interprets M (bvShiftByConst2LtPrem x amount) true ->
    native_zleq W A = true ∧
      native_zlt A (native_int_pow2 W) = true := by
  intro hAmountEval hW0 hXTy hGePrem hLtPrem
  have hGeEq := model_eval_eq_true_of_eo_eq_true M
    (Term.Apply (Term.Apply (Term.UOp UserOp.geq) amount)
      (bvShiftByConst2Bvsize x)) (Term.Boolean true)
    (by simpa [bvShiftByConst2GePrem] using hGePrem)
  have hLtEq := model_eval_eq_true_of_eo_eq_true M
    (Term.Apply (Term.Apply (Term.UOp UserOp.lt) amount)
      (Term.Apply (Term.UOp UserOp.int_pow2)
        (bvShiftByConst2Bvsize x))) (Term.Boolean true)
    (by simpa [bvShiftByConst2LtPrem] using hLtPrem)
  rw [eval_ge_width_local M x amount A W hAmountEval hW0 hXTy] at hGeEq
  rw [eval_lt_pow_width_local M x amount A W hAmountEval hW0 hXTy] at hLtEq
  have hTrueEval :
      __smtx_model_eval M (__eo_to_smt (Term.Boolean true)) =
        SmtValue.Boolean true := by rfl
  rw [hTrueEval] at hGeEq hLtEq
  simpa [__smtx_model_eval_eq, native_veq, SmtEval.native_zeq] using
    And.intro hGeEq hLtEq

private theorem native_int_pow2_add_of_nonneg_local
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

private theorem native_mod_zmult_pow2_eq_zero_of_le
    {w k x : native_Int} (hw : 0 <= w) (hle : w <= k) :
    native_mod_total (native_zmult x (native_int_pow2 k))
        (native_int_pow2 w) = 0 := by
  let d : native_Int := k - w
  have hd : 0 <= d := by
    dsimp [d]
    exact Int.sub_nonneg.mpr hle
  have hkEq : k = w + d := by
    dsimp [d]
    symm
    calc
      w + (k - w) = w + k - w := by
        rw [Int.add_sub_assoc]
      _ = k + w - w := by
        rw [Int.add_comm w k]
      _ = k := by
        rw [Int.add_sub_cancel]
  have hPow : native_int_pow2 k =
      native_int_pow2 w * native_int_pow2 d := by
    rw [hkEq]
    exact native_int_pow2_add_of_nonneg_local hw hd
  rw [hPow]
  simp [native_mod_total, native_zmult]
  have hAssoc :
      x * (native_int_pow2 w * native_int_pow2 d) =
        native_int_pow2 w * (x * native_int_pow2 d) := by
    calc
      x * (native_int_pow2 w * native_int_pow2 d) =
          (x * native_int_pow2 w) * native_int_pow2 d := by
        rw [← Int.mul_assoc]
      _ = (native_int_pow2 w * x) * native_int_pow2 d := by
        rw [Int.mul_comm x (native_int_pow2 w)]
      _ = native_int_pow2 w * (x * native_int_pow2 d) := by
        rw [Int.mul_assoc]
  rw [hAssoc]
  exact Int.mul_emod_right (native_int_pow2 w)
    (x * native_int_pow2 d)

private theorem native_mod_div_pow2_eq_zero_of_le
    {w k x : native_Int} (hw : 0 <= w) (hle : w <= k)
    (hx0 : 0 <= x) (hxlt : x < native_int_pow2 w) :
    native_mod_total (native_div_total x (native_int_pow2 k))
        (native_int_pow2 w) = 0 := by
  have hPowLe : native_int_pow2 w <= native_int_pow2 k :=
    native_int_pow2_le_of_le_nonneg hw hle
  have hDivZero : native_div_total x (native_int_pow2 k) = 0 := by
    rw [native_div_total]
    exact Int.ediv_eq_zero_of_lt hx0 (Int.lt_of_lt_of_le hxlt hPowLe)
  rw [hDivZero]
  simp [native_mod_total]

private theorem eval_shift_const_local
    (M : SmtModel) (hM : model_total_typed M)
    (x amount : Term) (W : native_Int) :
    RuleProofs.eo_has_smt_translation x ->
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof (__eo_to_smt amount) = SmtType.Int ->
    eo_interprets M (bvShiftByConst2GePrem x amount) true ->
    eo_interprets M (bvShiftByConst2LtPrem x amount) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvShlByConst2Lhs x amount (Term.Numeral W))) =
      SmtValue.Binary W 0 ∧
    __smtx_model_eval M
        (__eo_to_smt
          (bvLshrByConst2Lhs x amount (Term.Numeral W))) =
      SmtValue.Binary W 0 := by
  intro hXTrans hW0 hXTy hAmountTy hGePrem hLtPrem
  rcases eval_int_term_local M hM amount hAmountTy with
    ⟨A, hAmountEval⟩
  rcases shift_premises_numeric M x amount A W hAmountEval hW0 hXTy
      hGePrem hLtPrem with ⟨hWA, hAPow⟩
  have hw : (0 : Int) <= W := by
    simpa [SmtEval.native_zleq] using hW0
  have hle : W <= A := by
    simpa [SmtEval.native_zleq] using hWA
  have hA0 : (0 : Int) <= A := Int.le_trans hw hle
  have hAlt : A < native_int_pow2 W := by
    simpa [SmtEval.native_zlt] using hAPow
  have hAmountMod :
      native_mod_total A (native_int_pow2 W) = A := by
    simpa [SmtEval.native_mod_total] using Int.emod_eq_of_lt hA0 hAlt
  have hBvAmountEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvShiftByConst2Const amount (Term.Numeral W))) =
        SmtValue.Binary W A := by
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral W) (__eo_to_smt amount)) = _
    rw [smtx_eval_int_to_bv_term_eq]
    have hWidthEval :
        __smtx_model_eval M (SmtTerm.Numeral W) =
          SmtValue.Numeral W := by rfl
    rw [hWidthEval, hAmountEval]
    simp [__smtx_model_eval_int_to_bv, hAmountMod]
  rcases eval_bv_term_local M hM x W hW0 hXTy with
    ⟨p, hXEval, hCanonical⟩
  have hRange := bitvec_payload_range_of_canonical hW0 hCanonical
  have hShlZero :
      native_mod_total (native_zmult p (native_int_pow2 A))
          (native_int_pow2 W) = 0 :=
    native_mod_zmult_pow2_eq_zero_of_le hw hle
  have hLshrZero :
      native_mod_total (native_div_total p (native_int_pow2 A))
          (native_int_pow2 W) = 0 :=
    native_mod_div_pow2_eq_zero_of_le hw hle hRange.1 hRange.2
  constructor
  · change __smtx_model_eval M
        (SmtTerm.bvshl (__eo_to_smt x)
          (__eo_to_smt
            (bvShiftByConst2Const amount (Term.Numeral W)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hXEval, hBvAmountEval]
    simp [__smtx_model_eval_bvshl, hShlZero]
  · change __smtx_model_eval M
        (SmtTerm.bvlshr (__eo_to_smt x)
          (__eo_to_smt
            (bvShiftByConst2Const amount (Term.Numeral W)))) = _
    rw [__smtx_model_eval.eq_def] <;> simp only
    rw [hXEval, hBvAmountEval]
    simp [__smtx_model_eval_bvlshr, hLshrZero]

private theorem eval_shift_zero_local
    (M : SmtModel) (W : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvShiftByConst2Zero (Term.Numeral W))) =
      SmtValue.Binary W 0 := by
  change __smtx_model_eval M
      (SmtTerm.int_to_bv (SmtTerm.Numeral W) (SmtTerm.Numeral 0)) = _
  simp [native_mod_total]

private theorem facts_bv_shl_by_const_2_term
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz w : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvShlByConst2Term x amount sz w) = Term.Bool ->
    eo_interprets M (bvShiftByConst2GePrem x amount) true ->
    eo_interprets M (bvShiftByConst2LtPrem x amount) true ->
    eo_interprets M (bvShiftByConst2WidthPrem x w) true ->
    eo_interprets M (bvShlByConst2Term x amount sz w) true := by
  intro hXTrans hAmountTrans hSzTrans hWTrans hResultTy
    hGePrem hLtPrem _hWidthPrem
  rcases bv_shl_by_const_2_context x amount sz w hXTrans hAmountTrans
      hSzTrans hWTrans hResultTy with
    ⟨W, rfl, rfl, hW0, _hXTy, _hAmountTy, hXTy, hAmountTy⟩
  have hBool := typed_bv_shl_by_const_2_term x amount
    (Term.Numeral W) (Term.Numeral W) hXTrans hAmountTrans
    hSzTrans hWTrans hResultTy
  have hShiftEval := (eval_shift_const_local M hM x amount W hXTrans
    hW0 hXTy hAmountTy hGePrem hLtPrem).1
  unfold bvShlByConst2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvShlByConst2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvShlByConst2Lhs x amount (Term.Numeral W))))
      (__smtx_model_eval M
        (__eo_to_smt (bvShiftByConst2Zero (Term.Numeral W))))
    rw [hShiftEval, eval_shift_zero_local M W]
    exact RuleProofs.smt_value_rel_refl _

private theorem facts_bv_lshr_by_const_2_term
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    __eo_typeof (bvLshrByConst2Term x amount sz) = Term.Bool ->
    eo_interprets M (bvShiftByConst2GePrem x amount) true ->
    eo_interprets M (bvShiftByConst2LtPrem x amount) true ->
    eo_interprets M (bvLshrByConst2Term x amount sz) true := by
  intro hXTrans hAmountTrans hSzTrans hResultTy hGePrem hLtPrem
  rcases bv_lshr_by_const_2_context x amount sz hXTrans hAmountTrans
      hSzTrans hResultTy with
    ⟨W, rfl, hW0, _hXTy, _hAmountTy, hXTy, hAmountTy⟩
  have hBool := typed_bv_lshr_by_const_2_term x amount
    (Term.Numeral W) hXTrans hAmountTrans hSzTrans hResultTy
  have hShiftEval := (eval_shift_const_local M hM x amount W hXTrans
    hW0 hXTy hAmountTy hGePrem hLtPrem).2
  unfold bvLshrByConst2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvLshrByConst2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvLshrByConst2Lhs x amount (Term.Numeral W))))
      (__smtx_model_eval M
        (__eo_to_smt (bvShiftByConst2Zero (Term.Numeral W))))
    rw [hShiftEval, eval_shift_zero_local M W]
    exact RuleProofs.smt_value_rel_refl _

def bvShlByConst2Program
    (x amount sz w P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_shl_by_const_2 x amount sz w
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

def bvLshrByConst2Program
    (x amount sz P1 P2 : Term) : Term :=
  __eo_prog_bv_lshr_by_const_2 x amount sz
    (Proof.pf P1) (Proof.pf P2)

private theorem shift_and_true {a b : Term} :
    __eo_and a b = Term.Boolean true ->
    a = Term.Boolean true ∧ b = Term.Boolean true := by
  intro h
  cases a <;> cases b <;>
    simp [__eo_and, __eo_requires, native_teq, native_ite, native_not,
      SmtEval.native_not, SmtEval.native_and] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hw : w1 = w2 <;> simp [hw] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢

private def bvShlByConst2Guard
    (x amount w amountRef1 xRef1 amountRef2 xRef2 wRef xRef3 : Term) :
    Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and (__eo_eq amount amountRef1) (__eo_eq x xRef1))
          (__eo_eq amount amountRef2))
        (__eo_eq x xRef2))
      (__eo_eq w wRef))
    (__eo_eq x xRef3)

private def bvLshrByConst2Guard
    (x amount amountRef1 xRef1 amountRef2 xRef2 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and (__eo_eq amount amountRef1) (__eo_eq x xRef1))
      (__eo_eq amount amountRef2))
    (__eo_eq x xRef2)

private theorem bv_shl_by_const_2_guard_refs
    {x amount w amountRef1 xRef1 amountRef2 xRef2 wRef xRef3 body : Term} :
    __eo_requires
        (bvShlByConst2Guard x amount w amountRef1 xRef1 amountRef2
          xRef2 wRef xRef3)
        (Term.Boolean true) body ≠ Term.Stuck ->
    amountRef1 = amount ∧ xRef1 = x ∧ amountRef2 = amount ∧
      xRef2 = x ∧ wRef = w ∧ xRef3 = x := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvShlByConst2Guard at hGuard
  rcases shift_and_true hGuard with ⟨hG5, hX3⟩
  rcases shift_and_true hG5 with ⟨hG4, hW⟩
  rcases shift_and_true hG4 with ⟨hG3, hX2⟩
  rcases shift_and_true hG3 with ⟨hG2, hAmount2⟩
  rcases shift_and_true hG2 with ⟨hAmount1, hX1⟩
  exact ⟨support_eq_of_eo_eq_true amount amountRef1 hAmount1,
    support_eq_of_eo_eq_true x xRef1 hX1,
    support_eq_of_eo_eq_true amount amountRef2 hAmount2,
    support_eq_of_eo_eq_true x xRef2 hX2,
    support_eq_of_eo_eq_true w wRef hW,
    support_eq_of_eo_eq_true x xRef3 hX3⟩

private theorem bv_lshr_by_const_2_guard_refs
    {x amount amountRef1 xRef1 amountRef2 xRef2 body : Term} :
    __eo_requires
        (bvLshrByConst2Guard x amount amountRef1 xRef1 amountRef2 xRef2)
        (Term.Boolean true) body ≠ Term.Stuck ->
    amountRef1 = amount ∧ xRef1 = x ∧ amountRef2 = amount ∧
      xRef2 = x := by
  intro hReq
  have hGuard := support_eo_requires_cond_eq_of_non_stuck hReq
  unfold bvLshrByConst2Guard at hGuard
  rcases shift_and_true hGuard with ⟨hG3, hX2⟩
  rcases shift_and_true hG3 with ⟨hG2, hAmount2⟩
  rcases shift_and_true hG2 with ⟨hAmount1, hX1⟩
  exact ⟨support_eq_of_eo_eq_true amount amountRef1 hAmount1,
    support_eq_of_eo_eq_true x xRef1 hX1,
    support_eq_of_eo_eq_true amount amountRef2 hAmount2,
    support_eq_of_eo_eq_true x xRef2 hX2⟩

private theorem bv_shl_by_const_2_premise_shape
    (x amount sz w P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    bvShlByConst2Program x amount sz w P1 P2 P3 ≠ Term.Stuck ->
    ∃ amountRef1 xRef1 amountRef2 xRef2 wRef xRef3,
      P1 = bvShiftByConst2GePrem xRef1 amountRef1 ∧
      P2 = bvShiftByConst2LtPrem xRef2 amountRef2 ∧
      P3 = bvShiftByConst2WidthPrem xRef3 wRef := by
  intro hX hAmount hSz hW hProg
  by_cases hShape :
      ∃ amountRef1 xRef1 amountRef2 xRef2 wRef xRef3,
        P1 = bvShiftByConst2GePrem xRef1 amountRef1 ∧
        P2 = bvShiftByConst2LtPrem xRef2 amountRef2 ∧
        P3 = bvShiftByConst2WidthPrem xRef3 wRef
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_shl_by_const_2.eq_6 x amount sz w
      (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)
      hX hAmount hSz hW (by
        intro amountRef1 xRef1 amountRef2 xRef2 wRef xRef3
          hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨amountRef1, xRef1, amountRef2, xRef2, wRef, xRef3,
            rfl, rfl, rfl⟩)

private theorem bv_lshr_by_const_2_premise_shape
    (x amount sz P1 P2 : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    bvLshrByConst2Program x amount sz P1 P2 ≠ Term.Stuck ->
    ∃ amountRef1 xRef1 amountRef2 xRef2,
      P1 = bvShiftByConst2GePrem xRef1 amountRef1 ∧
      P2 = bvShiftByConst2LtPrem xRef2 amountRef2 := by
  intro hX hAmount hSz hProg
  by_cases hShape :
      ∃ amountRef1 xRef1 amountRef2 xRef2,
        P1 = bvShiftByConst2GePrem xRef1 amountRef1 ∧
        P2 = bvShiftByConst2LtPrem xRef2 amountRef2
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_lshr_by_const_2.eq_5 x amount sz
      (Proof.pf P1) (Proof.pf P2) hX hAmount hSz (by
        intro amountRef1 xRef1 amountRef2 xRef2 hP1 hP2
        cases hP1
        cases hP2
        exact hShape
          ⟨amountRef1, xRef1, amountRef2, xRef2, rfl, rfl⟩)

private theorem bv_shl_by_const_2_program_canonical
    (x amount sz w : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    w ≠ Term.Stuck ->
    bvShlByConst2Program x amount sz w
        (bvShiftByConst2GePrem x amount)
        (bvShiftByConst2LtPrem x amount)
        (bvShiftByConst2WidthPrem x w) =
      bvShlByConst2Term x amount sz w := by
  intro hX hAmount hSz hW
  unfold bvShlByConst2Program bvShiftByConst2GePrem
    bvShiftByConst2LtPrem bvShiftByConst2WidthPrem
    bvShiftByConst2Bvsize
  rw [__eo_prog_bv_shl_by_const_2.eq_5 x amount sz w
    amount x amount x w x hX hAmount hSz hW]
  simp [bvShlByConst2Term, bvShlByConst2Lhs,
    bvShiftByConst2Zero, bvShiftByConst2Const,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount, hW]

private theorem bv_lshr_by_const_2_program_canonical
    (x amount sz : Term) :
    x ≠ Term.Stuck -> amount ≠ Term.Stuck -> sz ≠ Term.Stuck ->
    bvLshrByConst2Program x amount sz
        (bvShiftByConst2GePrem x amount)
        (bvShiftByConst2LtPrem x amount) =
      bvLshrByConst2Term x amount sz := by
  intro hX hAmount hSz
  unfold bvLshrByConst2Program bvShiftByConst2GePrem
    bvShiftByConst2LtPrem bvShiftByConst2Bvsize
  rw [__eo_prog_bv_lshr_by_const_2.eq_4 x amount sz
    amount x amount x hX hAmount hSz]
  simp [bvLshrByConst2Term, bvLshrByConst2Lhs,
    bvShiftByConst2Zero, bvShiftByConst2Const,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hAmount]

private theorem bvShlByConst2Program_normalize
    (x amount sz w P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation w ->
    bvShlByConst2Program x amount sz w P1 P2 P3 ≠ Term.Stuck ->
    P1 = bvShiftByConst2GePrem x amount ∧
      P2 = bvShiftByConst2LtPrem x amount ∧
      P3 = bvShiftByConst2WidthPrem x w ∧
      bvShlByConst2Program x amount sz w P1 P2 P3 =
        bvShlByConst2Term x amount sz w := by
  intro hXTrans hAmountTrans hSzTrans hWTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hAmount :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  have hSz := RuleProofs.term_ne_stuck_of_has_smt_translation sz hSzTrans
  have hW := RuleProofs.term_ne_stuck_of_has_smt_translation w hWTrans
  rcases bv_shl_by_const_2_premise_shape x amount sz w P1 P2 P3
      hX hAmount hSz hW hProg with
    ⟨amountRef1, xRef1, amountRef2, xRef2, wRef, xRef3,
      hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvShlByConst2Program bvShiftByConst2GePrem
    bvShiftByConst2LtPrem bvShiftByConst2WidthPrem
    bvShiftByConst2Bvsize at hReq
  rw [__eo_prog_bv_shl_by_const_2.eq_5 x amount sz w
    amountRef1 xRef1 amountRef2 xRef2 wRef xRef3
    hX hAmount hSz hW] at hReq
  have hRefs := bv_shl_by_const_2_guard_refs
    (x := x) (amount := amount) (w := w)
    (amountRef1 := amountRef1) (xRef1 := xRef1)
    (amountRef2 := amountRef2) (xRef2 := xRef2)
    (wRef := wRef) (xRef3 := xRef3)
    (by simpa [bvShlByConst2Guard] using hReq)
  rcases hRefs with
    ⟨hAmountRef1, hXRef1, hAmountRef2, hXRef2, hWRef, hXRef3⟩
  subst amountRef1
  subst xRef1
  subst amountRef2
  subst xRef2
  subst wRef
  subst xRef3
  refine ⟨hP1, hP2, hP3, ?_⟩
  rw [hP1, hP2, hP3]
  exact bv_shl_by_const_2_program_canonical x amount sz w
    hX hAmount hSz hW

private theorem bvLshrByConst2Program_normalize
    (x amount sz P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    bvLshrByConst2Program x amount sz P1 P2 ≠ Term.Stuck ->
    P1 = bvShiftByConst2GePrem x amount ∧
      P2 = bvShiftByConst2LtPrem x amount ∧
      bvLshrByConst2Program x amount sz P1 P2 =
        bvLshrByConst2Term x amount sz := by
  intro hXTrans hAmountTrans hSzTrans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hAmount :=
    RuleProofs.term_ne_stuck_of_has_smt_translation amount hAmountTrans
  have hSz := RuleProofs.term_ne_stuck_of_has_smt_translation sz hSzTrans
  rcases bv_lshr_by_const_2_premise_shape x amount sz P1 P2
      hX hAmount hSz hProg with
    ⟨amountRef1, xRef1, amountRef2, xRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvLshrByConst2Program bvShiftByConst2GePrem
    bvShiftByConst2LtPrem bvShiftByConst2Bvsize at hReq
  rw [__eo_prog_bv_lshr_by_const_2.eq_4 x amount sz
    amountRef1 xRef1 amountRef2 xRef2 hX hAmount hSz] at hReq
  have hRefs := bv_lshr_by_const_2_guard_refs
    (x := x) (amount := amount)
    (amountRef1 := amountRef1) (xRef1 := xRef1)
    (amountRef2 := amountRef2) (xRef2 := xRef2)
    (by simpa [bvLshrByConst2Guard] using hReq)
  rcases hRefs with ⟨hAmountRef1, hXRef1, hAmountRef2, hXRef2⟩
  subst amountRef1
  subst xRef1
  subst amountRef2
  subst xRef2
  refine ⟨hP1, hP2, ?_⟩
  rw [hP1, hP2]
  exact bv_lshr_by_const_2_program_canonical x amount sz
    hX hAmount hSz

theorem typed_bv_shl_by_const_2_program
    (x amount sz w P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvShlByConst2Program x amount sz w P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvShlByConst2Program x amount sz w P1 P2 P3) := by
  intro hXTrans hAmountTrans hSzTrans hWTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvShlByConst2Program_normalize x amount sz w P1 P2 P3
      hXTrans hAmountTrans hSzTrans hWTrans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvShlByConst2Term x amount sz w) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_shl_by_const_2_term x amount sz w
    hXTrans hAmountTrans hSzTrans hWTrans hTermTy

theorem typed_bv_lshr_by_const_2_program
    (x amount sz P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    __eo_typeof (bvLshrByConst2Program x amount sz P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvLshrByConst2Program x amount sz P1 P2) := by
  intro hXTrans hAmountTrans hSzTrans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvLshrByConst2Program_normalize x amount sz P1 P2
      hXTrans hAmountTrans hSzTrans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvLshrByConst2Term x amount sz) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_lshr_by_const_2_term x amount sz
    hXTrans hAmountTrans hSzTrans hTermTy

theorem facts_bv_shl_by_const_2_program
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz w P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    RuleProofs.eo_has_smt_translation w ->
    __eo_typeof (bvShlByConst2Program x amount sz w P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M (bvShlByConst2Program x amount sz w P1 P2 P3) true := by
  intro hXTrans hAmountTrans hSzTrans hWTrans hResultTy
    hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvShlByConst2Program_normalize x amount sz w P1 P2 P3
      hXTrans hAmountTrans hSzTrans hWTrans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvShlByConst2Term x amount sz w) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hGePrem :
      eo_interprets M (bvShiftByConst2GePrem x amount) true := by
    simpa [hP1] using hP1True
  have hLtPrem :
      eo_interprets M (bvShiftByConst2LtPrem x amount) true := by
    simpa [hP2] using hP2True
  have hWidthPrem :
      eo_interprets M (bvShiftByConst2WidthPrem x w) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_shl_by_const_2_term M hM x amount sz w
    hXTrans hAmountTrans hSzTrans hWTrans hTermTy
    hGePrem hLtPrem hWidthPrem

theorem facts_bv_lshr_by_const_2_program
    (M : SmtModel) (hM : model_total_typed M)
    (x amount sz P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation amount ->
    RuleProofs.eo_has_smt_translation sz ->
    __eo_typeof (bvLshrByConst2Program x amount sz P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M (bvLshrByConst2Program x amount sz P1 P2) true := by
  intro hXTrans hAmountTrans hSzTrans hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvLshrByConst2Program_normalize x amount sz P1 P2
      hXTrans hAmountTrans hSzTrans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvLshrByConst2Term x amount sz) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hGePrem :
      eo_interprets M (bvShiftByConst2GePrem x amount) true := by
    simpa [hP1] using hP1True
  have hLtPrem :
      eo_interprets M (bvShiftByConst2LtPrem x amount) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_lshr_by_const_2_term M hM x amount sz
    hXTrans hAmountTrans hSzTrans hTermTy hGePrem hLtPrem
