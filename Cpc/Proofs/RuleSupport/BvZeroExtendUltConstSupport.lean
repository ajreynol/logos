module

public import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import all Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
public import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport
import all Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport

public section

/-! Shared support for the `bv_zero_extend_{ult,eq}_const` rewrites. -/

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

def bvZeroExtendUltConstBvsize (x : Term) : Term :=
  Term.Apply (Term.UOp UserOp._at_bvsize) x

def bvZeroExtendUltConstConst (c nm : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.int_to_bv nm) c

def bvZeroExtendUltConstZero (x m : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.zero_extend m) x

def bvZeroExtendUltConstLow (c nm nm2 : Term) : Term :=
  bvExtractTerm (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)

def bvZeroExtendUltConstWidthPrem (x nm2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nm2)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
      (bvZeroExtendUltConstBvsize x)) (Term.Numeral 1))

def bvZeroExtendUltConstValuePremRefs
    (m cLeft nmLeft nm2 cRight nmRight : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvZeroExtendUltConstConst cLeft nmLeft))
    (bvZeroExtendUltConstZero
      (bvZeroExtendUltConstLow cRight nmRight nm2) m)

def bvZeroExtendUltConstValuePrem
    (_x m c nm nm2 : Term) : Term :=
  bvZeroExtendUltConstValuePremRefs m c nm nm2 c nm

def bvZeroExtendUltConst1Lhs
    (x m c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult)
      (bvZeroExtendUltConstZero x m))
    (bvZeroExtendUltConstConst c nm)

def bvZeroExtendUltConst1Rhs
    (x c nm nm2 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x)
    (bvZeroExtendUltConstLow c nm nm2)

def bvZeroExtendUltConst1Term
    (x m c nm nm2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvZeroExtendUltConst1Lhs x m c nm))
    (bvZeroExtendUltConst1Rhs x c nm nm2)

def bvZeroExtendUltConst2Lhs
    (x m c nm : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult)
      (bvZeroExtendUltConstConst c nm))
    (bvZeroExtendUltConstZero x m)

def bvZeroExtendUltConst2Rhs
    (x c nm nm2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.bvult)
      (bvZeroExtendUltConstLow c nm nm2)) x

def bvZeroExtendUltConst2Term
    (x m c nm nm2 : Term) : Term :=
  Term.Apply
    (Term.Apply (Term.UOp UserOp.eq)
      (bvZeroExtendUltConst2Lhs x m c nm))
    (bvZeroExtendUltConst2Rhs x c nm nm2)

def bvZeroExtendEqConstNmm1Prem (nm nmm1 : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) nmm1)
    (Term.Apply (Term.Apply (Term.UOp UserOp.neg) nm) (Term.Numeral 1))

def bvZeroExtendEqConstHigh
    (c nm nm2 nmm1 : Term) : Term :=
  bvExtractTerm (bvZeroExtendUltConstConst c nm) nmm1 nm2

def bvZeroExtendEqConstZero (m : Term) : Term :=
  bvZeroExtendUltConstConst (Term.Numeral 0) m

def bvZeroExtendEqConstEq (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b

def bvZeroExtendEqConstAnd (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b

def bvZeroExtendEqConstUpper
    (m c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvZeroExtendEqConstHigh c nm nm2 nmm1)
    (bvZeroExtendEqConstZero m)

def bvZeroExtendEqConstLower
    (x c nm nm2 : Term) : Term :=
  bvZeroExtendEqConstEq x (bvZeroExtendUltConstLow c nm nm2)

def bvZeroExtendEqConstRhs
    (x m c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstAnd
    (bvZeroExtendEqConstUpper m c nm nm2 nmm1)
    (bvZeroExtendEqConstAnd
      (bvZeroExtendEqConstLower x c nm nm2) (Term.Boolean true))

def bvZeroExtendEqConst1Lhs
    (x m c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvZeroExtendUltConstZero x m)
    (bvZeroExtendUltConstConst c nm)

def bvZeroExtendEqConst2Lhs
    (x m c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvZeroExtendUltConstConst c nm)
    (bvZeroExtendUltConstZero x m)

def bvZeroExtendEqConst1Term
    (x m c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq (bvZeroExtendEqConst1Lhs x m c nm)
    (bvZeroExtendEqConstRhs x m c nm nm2 nmm1)

def bvZeroExtendEqConst2Term
    (x m c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq (bvZeroExtendEqConst2Lhs x m c nm)
    (bvZeroExtendEqConstRhs x m c nm nm2 nmm1)

private theorem eo_typeof_eq_bool_of_ne_stuck_zero_extend_local
    (A B : Term) (h : __eo_typeof_eq A B ≠ Term.Stuck) :
    __eo_typeof_eq A B = Term.Bool := by
  cases A <;> cases B <;>
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not] at h ⊢
  all_goals
    assumption

private theorem typeof_or_bool_args_zero_extend_local (A B : Term) :
    __eo_typeof_or A B = Term.Bool -> A = Term.Bool ∧ B = Term.Bool := by
  intro h
  cases A <;> cases B <;> simp [__eo_typeof_or] at h ⊢

private theorem typeof_or_args_bool_of_ne_stuck_zero_extend_local
    (A B : Term) (h : __eo_typeof_or A B ≠ Term.Stuck) :
    A = Term.Bool ∧ B = Term.Bool := by
  have hBool : __eo_typeof_or A B = Term.Bool := by
    cases A <;> cases B <;> simp [__eo_typeof_or] at h ⊢
  exact typeof_or_bool_args_zero_extend_local A B hBool

private theorem mk_apply_bitvec_shape_of_ne_stuck_local
    (width : Term)
    (h : __eo_mk_apply (Term.UOp UserOp.BitVec) width ≠ Term.Stuck) :
    ∃ width',
      __eo_mk_apply (Term.UOp UserOp.BitVec) width =
        Term.Apply (Term.UOp UserOp.BitVec) width' := by
  cases width <;> simp [__eo_mk_apply] at h ⊢

private theorem typeof_zero_extend_result_bitvec_of_ne_stuck_local
    (x m : Term)
    (h : __eo_typeof (bvZeroExtendUltConstZero x m) ≠ Term.Stuck) :
    ∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
  change __eo_typeof_zero_extend (__eo_typeof m) m (__eo_typeof x) ≠
    Term.Stuck at h
  change ∃ width,
    __eo_typeof_zero_extend (__eo_typeof m) m (__eo_typeof x) =
      Term.Apply (Term.UOp UserOp.BitVec) width
  unfold __eo_typeof_zero_extend at h ⊢
  split at h <;> simp_all [__eo_requires, __eo_mk_apply, native_ite,
    native_teq, native_not]
  exact mk_apply_bitvec_shape_of_ne_stuck_local _ h.2

private theorem typeof_extract_result_bitvec_of_ne_stuck_local
    (x hi lo : Term)
    (h : __eo_typeof (bvExtractTerm x hi lo) ≠ Term.Stuck) :
    ∃ width,
      __eo_typeof (bvExtractTerm x hi lo) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
  change __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
    (__eo_typeof x) ≠ Term.Stuck at h
  change ∃ width,
    __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
      (__eo_typeof x) = Term.Apply (Term.UOp UserOp.BitVec) width
  unfold __eo_typeof_extract at h ⊢
  split at h <;> simp_all [__eo_requires, __eo_mk_apply, native_ite,
    native_teq, native_not]
  exact mk_apply_bitvec_shape_of_ne_stuck_local _ h

private theorem typeof_bvult_arg_types_of_ne_stuck_local
    {A B : Term}
    (h : __eo_typeof_bvult A B ≠ Term.Stuck) :
    ∃ width,
      A = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        B = Term.Apply (Term.UOp UserOp.BitVec) width := by
  cases A <;> cases B <;> simp [__eo_typeof_bvult] at h ⊢
  case Apply.Apply f n g m =>
    cases f <;> cases g <;> simp [__eo_typeof_bvult] at h ⊢
    case UOp.UOp opA opB =>
      cases opA <;> cases opB <;> simp [__eo_typeof_bvult] at h ⊢
      have hReq :
          __eo_requires (__eo_eq n m) (Term.Boolean true) Term.Bool ≠
            Term.Stuck := by
        simpa [__eo_typeof_bvult] using h
      have hm : m = n :=
        support_eq_of_eo_eq_true n m
          (support_eo_requires_cond_eq_of_non_stuck hReq)
      exact hm.symm

private theorem smt_typeof_zero_extend_of_context_local
    (x : Term) (w a : native_Int) :
    __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat w) ->
    native_zleq 0 w = true ->
    native_zleq 0 a = true ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.UOp1 UserOp1.zero_extend (Term.Numeral a)) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus w a)) := by
  intro hXTy hw0 ha0
  have hRound := native_int_to_nat_roundtrip w hw0
  have hComm : native_zplus a w = native_zplus w a := by
    simp [SmtEval.native_zplus, Int.add_comm]
  change __smtx_typeof
      (SmtTerm.zero_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [typeof_zero_extend_eq, hXTy]
  simp [__smtx_typeof_zero_extend, native_ite, ha0, hRound, hComm]

private theorem bv_zero_extend_ult_const_context_of_types
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    (∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
      __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    ∃ W A : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
  intro hXTrans hMTrans hCTrans hNmTrans hWideTypes hLowTypes
  rcases hLowTypes with ⟨widthW, hXTy, hLowTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width
      x widthW hXTrans hXTy with
    ⟨W, hWidthW, hW0, hXSmtTy⟩
  subst widthW
  rcases hWideTypes with ⟨widthWide, hZeroTy, hConstTy⟩
  have hSignTy :
      __eo_typeof
          (Term.Apply (Term.UOp1 UserOp1.sign_extend m) x) =
        Term.Apply (Term.UOp UserOp.BitVec) widthWide := by
    simpa [bvZeroExtendUltConstZero] using hZeroTy
  rcases sign_extend_index_context x m widthWide W hXTy hSignTy with
    ⟨A, hM, hA0, hWidthWide⟩
  subst m
  subst widthWide
  have hCNe := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_all_ones_const_context c nm
      (Term.Numeral (native_zplus W A)) hCNe hNmNe
      (by simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using hConstTy) with
    ⟨N, hNm, hWidthN, hN0, hCTy⟩
  have hN : N = native_zplus W A := by
    injection hWidthN with h
    exact h.symm
  subst N
  subst nm
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c (Term.UOp UserOp.Int) (__eo_to_smt c) rfl hCTrans hCTy
  have hConstSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type c (native_zplus W A)
        hCSmtTy hN0
  have hConstTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConstSmtTy]
    intro h
    cases h
  have hLowNe :
      __eo_typeof
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2) ≠ Term.Stuck := by
    rw [hLowTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nm2 (Term.Numeral 0) hConstTrans hLowNe with
    ⟨wide, high, low, _hConstEoTy, hNm2, hLow,
      hWide0, hLow0, hHighWide, hExtractWidth0, hConstSmtTy'⟩
  have hLowEq : low = 0 := by
    injection hLow with h
    exact h.symm
  subst low
  have hLowSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) nm2)) =
        SmtType.BitVec
          (native_int_to_nat
            (native_zplus (native_zplus high 1) (native_zneg 0))) := by
    rw [hNm2]
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wide high 0 hConstSmtTy' hWide0 hLow0 hHighWide hExtractWidth0
  have hLowTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) nm2) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLowSmtTyRaw]
    intro h
    cases h
  have hLowSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) nm2)) =
        SmtType.BitVec (native_int_to_nat W) := by
    have h :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) nm2)
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2))
        rfl hLowTrans hLowTy
    simpa [__eo_to_smt_type, hW0, native_ite] using h
  have hZeroSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstZero x (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    simpa [bvZeroExtendUltConstZero] using
      smt_typeof_zero_extend_of_context_local x W A hXSmtTy hW0 hA0
  exact ⟨W, A, rfl, rfl, hW0, hA0, hXSmtTy,
    hConstSmtTy, hLowSmtTy, hZeroSmtTy⟩

private theorem bv_zero_extend_ult_const_1_context
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool ->
    ∃ W A : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult
        (__eo_typeof (bvZeroExtendUltConstZero x m))
        (__eo_typeof (bvZeroExtendUltConstConst c nm)))
      (__eo_typeof_bvult (__eo_typeof x)
        (__eo_typeof (bvZeroExtendUltConstLow c nm nm2))) =
      Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hWideNe, hLowNe⟩
  exact bv_zero_extend_ult_const_context_of_types x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans
    (typeof_bvult_arg_types_of_ne_stuck_local hWideNe)
    (typeof_bvult_arg_types_of_ne_stuck_local hLowNe)

private theorem bv_zero_extend_ult_const_2_context
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool ->
    ∃ W A : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  change __eo_typeof_eq
      (__eo_typeof_bvult
        (__eo_typeof (bvZeroExtendUltConstConst c nm))
        (__eo_typeof (bvZeroExtendUltConstZero x m)))
      (__eo_typeof_bvult
        (__eo_typeof (bvZeroExtendUltConstLow c nm nm2))
        (__eo_typeof x)) = Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hWideNe, hLowNe⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hWideNe with
    ⟨wide, hConstTy, hZeroTy⟩
  rcases typeof_bvult_arg_types_of_ne_stuck_local hLowNe with
    ⟨low, hLowTy, hXTy⟩
  exact bv_zero_extend_ult_const_context_of_types x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans
    ⟨wide, hZeroTy, hConstTy⟩ ⟨low, hXTy, hLowTy⟩

private theorem smt_typeof_bvult_of_same_bitvec_local
    (a b : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt b) = SmtType.BitVec w ->
    __smtx_typeof
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) a) b)) =
      SmtType.Bool := by
  intro hA hB
  change __smtx_typeof (SmtTerm.bvult (__eo_to_smt a) (__eo_to_smt b)) = _
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_2_ret, hA, hB, native_nateq, native_ite]

private theorem typed_bv_zero_extend_ult_const_1_term
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendUltConst1Term x m c nm nm2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_ult_const_1_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, rfl, rfl, _hW0, _hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, hZeroSmtTy⟩
  have hLhsTy := smt_typeof_bvult_of_same_bitvec_local
    (bvZeroExtendUltConstZero x (Term.Numeral A))
    (bvZeroExtendUltConstConst c
      (Term.Numeral (native_zplus W A)))
    (native_int_to_nat (native_zplus W A)) hZeroSmtTy hConstSmtTy
  have hRhsTy := smt_typeof_bvult_of_same_bitvec_local
    x
    (bvZeroExtendUltConstLow c
      (Term.Numeral (native_zplus W A)) nm2)
    (native_int_to_nat W) hXSmtTy hLowSmtTy
  unfold bvZeroExtendUltConst1Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by simpa [bvZeroExtendUltConst1Lhs, bvZeroExtendUltConst1Rhs] using
      hLhsTy.trans hRhsTy.symm)
    (by
      have h :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvult)
                    (bvZeroExtendUltConstZero x (Term.Numeral A)))
                  (bvZeroExtendUltConstConst c
                    (Term.Numeral (native_zplus W A))))) ≠
            SmtType.None := by
        rw [hLhsTy]
        intro h
        cases h
      simpa [bvZeroExtendUltConst1Lhs] using h)

private theorem typed_bv_zero_extend_ult_const_2_term
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendUltConst2Term x m c nm nm2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_ult_const_2_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, rfl, rfl, _hW0, _hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, hZeroSmtTy⟩
  have hLhsTy := smt_typeof_bvult_of_same_bitvec_local
    (bvZeroExtendUltConstConst c
      (Term.Numeral (native_zplus W A)))
    (bvZeroExtendUltConstZero x (Term.Numeral A))
    (native_int_to_nat (native_zplus W A)) hConstSmtTy hZeroSmtTy
  have hRhsTy := smt_typeof_bvult_of_same_bitvec_local
    (bvZeroExtendUltConstLow c
      (Term.Numeral (native_zplus W A)) nm2) x
    (native_int_to_nat W) hLowSmtTy hXSmtTy
  unfold bvZeroExtendUltConst2Term
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (by simpa [bvZeroExtendUltConst2Lhs, bvZeroExtendUltConst2Rhs] using
      hLhsTy.trans hRhsTy.symm)
    (by
      have h :
          __smtx_typeof
              (__eo_to_smt
                (Term.Apply
                  (Term.Apply (Term.UOp UserOp.bvult)
                    (bvZeroExtendUltConstConst c
                      (Term.Numeral (native_zplus W A))))
                  (bvZeroExtendUltConstZero x (Term.Numeral A)))) ≠
            SmtType.None := by
        rw [hLhsTy]
        intro h
        cases h
      simpa [bvZeroExtendUltConst2Lhs] using h)

private theorem eval_zero_extend_term_local
    (M : SmtModel) (x : Term) (a : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConstZero x (Term.Numeral a))) =
      __smtx_model_eval_zero_extend (SmtValue.Numeral a)
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M
      (SmtTerm.zero_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  simp [__smtx_model_eval]

private theorem eval_bvult_term_local
    (M : SmtModel) (x y : Term) :
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) x) y)) =
      __smtx_model_eval_bvult
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y)) := by
  change __smtx_model_eval M
      (SmtTerm.bvult (__eo_to_smt x) (__eo_to_smt y)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_bv_zero_extend_ult_const_both
    (M : SmtModel) (hM : model_total_typed M)
    (x c nm2 : Term) (W A : native_Int) :
    native_zleq 0 W = true ->
    native_zleq 0 A = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2)) =
      SmtType.BitVec (native_int_to_nat W) ->
    eo_interprets M
      (bvZeroExtendUltConstValuePrem x (Term.Numeral A) c
        (Term.Numeral (native_zplus W A)) nm2) true ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst1Rhs x c
            (Term.Numeral (native_zplus W A)) nm2)) ∧
    __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst2Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst2Rhs x c
            (Term.Numeral (native_zplus W A)) nm2)) := by
  intro hW0 hA0 hXSmtTy hConstSmtTy hLowSmtTy hValuePrem
  have hWide0 : native_zleq 0 (native_zplus W A) = true := by
    have hW : (0 : Int) ≤ W := by
      simpa [SmtEval.native_zleq] using hW0
    have hA : (0 : Int) ≤ A := by
      simpa [SmtEval.native_zleq] using hA0
    simpa [SmtEval.native_zleq, SmtEval.native_zplus] using
      Int.add_nonneg hW hA
  have hWRound := native_int_to_nat_roundtrip W hW0
  have hWideRound :=
    native_int_to_nat_roundtrip (native_zplus W A) hWide0
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x)
      (native_int_to_nat W) hXSmtTy with
    ⟨xPayload, hXEval, _hXCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary W xPayload := by
    simpa [hWRound] using hXEval
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) nm2))
      (native_int_to_nat W) hLowSmtTy with
    ⟨lowPayload, hLowEval, _hLowCan⟩
  have hLowEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) nm2)) =
        SmtValue.Binary W lowPayload := by
    simpa [hWRound] using hLowEval
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))))
      (native_int_to_nat (native_zplus W A)) hConstSmtTy with
    ⟨constPayload, hConstEval, _hConstCan⟩
  have hConstEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (native_zplus W A) constPayload := by
    simpa [hWideRound] using hConstEval
  have hZeroXEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstZero x (Term.Numeral A))) =
        SmtValue.Binary (native_zplus W A) xPayload := by
    rw [eval_zero_extend_term_local, hXEval']
    simp [__smtx_model_eval_zero_extend, SmtEval.native_zplus,
      Int.add_comm]
  have hZeroLowEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstZero
              (bvZeroExtendUltConstLow c
                (Term.Numeral (native_zplus W A)) nm2)
              (Term.Numeral A))) =
        SmtValue.Binary (native_zplus W A) lowPayload := by
    rw [eval_zero_extend_term_local, hLowEval']
    simp [__smtx_model_eval_zero_extend, SmtEval.native_zplus,
      Int.add_comm]
  have hValueRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))))
        (__smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstZero
              (bvZeroExtendUltConstLow c
                (Term.Numeral (native_zplus W A)) nm2)
              (Term.Numeral A)))) := by
    exact RuleProofs.eo_interprets_eq_rel M _ _
      (by simpa [bvZeroExtendUltConstValuePrem] using hValuePrem)
  rw [hConstEval', hZeroLowEval] at hValueRel
  have hValueEq :
      SmtValue.Binary (native_zplus W A) constPayload =
        SmtValue.Binary (native_zplus W A) lowPayload :=
    (RuleProofs.smt_value_rel_iff_eq _ _ (by
      rintro ⟨r1, r2, h, _⟩
      cases h)).mp hValueRel
  have hPayloadEq : constPayload = lowPayload := by
    injection hValueEq
  constructor
  · unfold bvZeroExtendUltConst1Lhs bvZeroExtendUltConst1Rhs
    rw [eval_bvult_term_local, hZeroXEval, hConstEval',
      eval_bvult_term_local, hXEval', hLowEval', hPayloadEq]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt]
  · unfold bvZeroExtendUltConst2Lhs bvZeroExtendUltConst2Rhs
    rw [eval_bvult_term_local, hConstEval', hZeroXEval,
      eval_bvult_term_local, hLowEval', hXEval', hPayloadEq]
    simp [__smtx_model_eval_bvult, __smtx_model_eval_bvugt]

private theorem facts_bv_zero_extend_ult_const_1_term
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool ->
    eo_interprets M (bvZeroExtendUltConstValuePrem x m c nm nm2) true ->
    eo_interprets M (bvZeroExtendUltConst1Term x m c nm nm2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy hValuePrem
  have hBool := typed_bv_zero_extend_ult_const_1_term
    x m c nm nm2 hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_ult_const_1_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, rfl, rfl, hW0, hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, _hZeroSmtTy⟩
  unfold bvZeroExtendUltConst1Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvZeroExtendUltConst1Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst1Rhs x c
            (Term.Numeral (native_zplus W A)) nm2)))
    rw [(eval_bv_zero_extend_ult_const_both M hM x c nm2 W A
      hW0 hA0 hXSmtTy hConstSmtTy hLowSmtTy
      (by simpa using hValuePrem)).1]
    exact RuleProofs.smt_value_rel_refl _

private theorem facts_bv_zero_extend_ult_const_2_term
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm nm2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool ->
    eo_interprets M (bvZeroExtendUltConstValuePrem x m c nm nm2) true ->
    eo_interprets M (bvZeroExtendUltConst2Term x m c nm nm2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy hValuePrem
  have hBool := typed_bv_zero_extend_ult_const_2_term
    x m c nm nm2 hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_ult_const_2_context x m c nm nm2
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, rfl, rfl, hW0, hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, _hZeroSmtTy⟩
  unfold bvZeroExtendUltConst2Term
  apply RuleProofs.eo_interprets_eq_of_rel M
  · simpa [bvZeroExtendUltConst2Term] using hBool
  · change RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst2Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))))
      (__smtx_model_eval M
        (__eo_to_smt
          (bvZeroExtendUltConst2Rhs x c
            (Term.Numeral (native_zplus W A)) nm2)))
    rw [(eval_bv_zero_extend_ult_const_both M hM x c nm2 W A
      hW0 hA0 hXSmtTy hConstSmtTy hLowSmtTy
      (by simpa using hValuePrem)).2]
    exact RuleProofs.smt_value_rel_refl _

def bvZeroExtendUltConst1Program
    (x m c nm nm2 P1 P2 : Term) : Term :=
  __eo_prog_bv_zero_extend_ult_const_1 x m c nm nm2
    (Proof.pf P1) (Proof.pf P2)

def bvZeroExtendUltConst2Program
    (x m c nm nm2 P1 P2 : Term) : Term :=
  __eo_prog_bv_zero_extend_ult_const_2 x m c nm nm2
    (Proof.pf P1) (Proof.pf P2)

private def bvZeroExtendUltConstGuard
    (x m c nm nm2 nm2Ref1 xRef nmRef1 cRef1 mRef
      nm2Ref2 nmRef2 cRef2 : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and
            (__eo_and
              (__eo_and (__eo_eq nm2 nm2Ref1) (__eo_eq x xRef))
              (__eo_eq nm nmRef1))
            (__eo_eq c cRef1))
          (__eo_eq m mRef))
        (__eo_eq nm2 nm2Ref2))
      (__eo_eq nm nmRef2))
    (__eo_eq c cRef2)

private theorem bv_zero_extend_ult_const_guard_refs
    {x m c nm nm2 nm2Ref1 xRef nmRef1 cRef1 mRef
      nm2Ref2 nmRef2 cRef2 body : Term} :
    __eo_requires
        (bvZeroExtendUltConstGuard x m c nm nm2 nm2Ref1 xRef
          nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2)
        (Term.Boolean true) body ≠ Term.Stuck ->
    nm2Ref1 = nm2 ∧ xRef = x ∧ nmRef1 = nm ∧ cRef1 = c ∧
      mRef = m ∧ nm2Ref2 = nm2 ∧ nmRef2 = nm ∧ cRef2 = c := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  unfold bvZeroExtendUltConstGuard at hGuard
  rcases bv_extract_support_and_true hGuard with ⟨hG7, hC2⟩
  rcases bv_extract_support_and_true hG7 with ⟨hG6, hNm2⟩
  rcases bv_extract_support_and_true hG6 with ⟨hG5, hNm22⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hM⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hC1⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hNm1⟩
  rcases bv_extract_support_and_true hG2 with ⟨hNm21, hX⟩
  exact ⟨(bv_extract_support_eq_true hNm21).symm,
    (bv_extract_support_eq_true hX).symm,
    (bv_extract_support_eq_true hNm1).symm,
    (bv_extract_support_eq_true hC1).symm,
    (bv_extract_support_eq_true hM).symm,
    (bv_extract_support_eq_true hNm22).symm,
    (bv_extract_support_eq_true hNm2).symm,
    (bv_extract_support_eq_true hC2).symm⟩

private theorem bv_zero_extend_ult_const_1_premise_shape
    (x m c nm nm2 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvZeroExtendUltConst1Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    ∃ nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2,
      P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref1 ∧
      P2 = bvZeroExtendUltConstValuePremRefs
        mRef cRef1 nmRef1 nm2Ref2 cRef2 nmRef2 := by
  intro hX hM hC hNm hNm2 hProg
  by_cases hShape :
      ∃ nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2,
        P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref1 ∧
        P2 = bvZeroExtendUltConstValuePremRefs
          mRef cRef1 nmRef1 nm2Ref2 cRef2 nmRef2
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_zero_extend_ult_const_1.eq_7
      x m c nm nm2 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 (by
        intro nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2
          hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨nm2Ref1, xRef, nmRef1, cRef1, mRef,
          nm2Ref2, nmRef2, cRef2, rfl, rfl⟩)

private theorem bv_zero_extend_ult_const_2_premise_shape
    (x m c nm nm2 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvZeroExtendUltConst2Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    ∃ nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2,
      P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref1 ∧
      P2 = bvZeroExtendUltConstValuePremRefs
        mRef cRef1 nmRef1 nm2Ref2 cRef2 nmRef2 := by
  intro hX hM hC hNm hNm2 hProg
  by_cases hShape :
      ∃ nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2,
        P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref1 ∧
        P2 = bvZeroExtendUltConstValuePremRefs
          mRef cRef1 nmRef1 nm2Ref2 cRef2 nmRef2
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_zero_extend_ult_const_2.eq_7
      x m c nm nm2 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 (by
        intro nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2 nmRef2 cRef2
          hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨nm2Ref1, xRef, nmRef1, cRef1, mRef,
          nm2Ref2, nmRef2, cRef2, rfl, rfl⟩)

private theorem bv_zero_extend_ult_const_1_program_canonical
    (x m c nm nm2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvZeroExtendUltConst1Program x m c nm nm2
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendUltConstValuePrem x m c nm nm2) =
      bvZeroExtendUltConst1Term x m c nm nm2 := by
  intro hX hM hC hNm hNm2
  unfold bvZeroExtendUltConst1Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendUltConstValuePrem bvZeroExtendUltConstValuePremRefs
    bvZeroExtendUltConstBvsize bvZeroExtendUltConstZero
    bvZeroExtendUltConstLow bvZeroExtendUltConstConst bvExtractTerm
  rw [__eo_prog_bv_zero_extend_ult_const_1.eq_6
    x m c nm nm2 nm2 x nm c m nm2 nm c hX hM hC hNm hNm2]
  simp [bvZeroExtendUltConstGuard, bvZeroExtendUltConst1Term,
    bvZeroExtendUltConst1Lhs, bvZeroExtendUltConst1Rhs,
    bvZeroExtendUltConstZero, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2]

private theorem bv_zero_extend_ult_const_2_program_canonical
    (x m c nm nm2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    bvZeroExtendUltConst2Program x m c nm nm2
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendUltConstValuePrem x m c nm nm2) =
      bvZeroExtendUltConst2Term x m c nm nm2 := by
  intro hX hM hC hNm hNm2
  unfold bvZeroExtendUltConst2Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendUltConstValuePrem bvZeroExtendUltConstValuePremRefs
    bvZeroExtendUltConstBvsize bvZeroExtendUltConstZero
    bvZeroExtendUltConstLow bvZeroExtendUltConstConst bvExtractTerm
  rw [__eo_prog_bv_zero_extend_ult_const_2.eq_6
    x m c nm nm2 nm2 x nm c m nm2 nm c hX hM hC hNm hNm2]
  simp [bvZeroExtendUltConstGuard, bvZeroExtendUltConst2Term,
    bvZeroExtendUltConst2Lhs, bvZeroExtendUltConst2Rhs,
    bvZeroExtendUltConstZero, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2]

private theorem bvZeroExtendUltConst1Program_normalize
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    bvZeroExtendUltConst1Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    P1 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P2 = bvZeroExtendUltConstValuePrem x m c nm nm2 ∧
      bvZeroExtendUltConst1Program x m c nm nm2 P1 P2 =
        bvZeroExtendUltConst1Term x m c nm nm2 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  rcases bv_zero_extend_ult_const_1_premise_shape
      x m c nm nm2 P1 P2 hX hM hC hNm hNm2 hProg with
    ⟨nm2Ref1, xRef, nmRef1, cRef1, mRef, nm2Ref2, nmRef2,
      cRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvZeroExtendUltConst1Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendUltConstValuePremRefs bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstZero bvZeroExtendUltConstLow
    bvZeroExtendUltConstConst bvExtractTerm at hReq
  rw [__eo_prog_bv_zero_extend_ult_const_1.eq_6
    x m c nm nm2 nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2
    nmRef2 cRef2 hX hM hC hNm hNm2] at hReq
  rcases bv_zero_extend_ult_const_guard_refs
      (by simpa [bvZeroExtendUltConstGuard] using hReq) with
    ⟨hNm2Ref1, hXRef, hNmRef1, hCRef1, hMRef, hNm2Ref2,
      hNmRef2, hCRef2⟩
  subst nm2Ref1
  subst xRef
  subst nmRef1
  subst cRef1
  subst mRef
  subst nm2Ref2
  subst nmRef2
  subst cRef2
  have hP1Canonical : P1 = bvZeroExtendUltConstWidthPrem x nm2 := by
    simpa using hP1
  have hP2Canonical :
      P2 = bvZeroExtendUltConstValuePrem x m c nm nm2 := by
    simpa [bvZeroExtendUltConstValuePrem] using hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_zero_extend_ult_const_1_program_canonical
    x m c nm nm2 hX hM hC hNm hNm2

private theorem bvZeroExtendUltConst2Program_normalize
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    bvZeroExtendUltConst2Program x m c nm nm2 P1 P2 ≠ Term.Stuck ->
    P1 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P2 = bvZeroExtendUltConstValuePrem x m c nm nm2 ∧
      bvZeroExtendUltConst2Program x m c nm nm2 P1 P2 =
        bvZeroExtendUltConst2Term x m c nm nm2 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  rcases bv_zero_extend_ult_const_2_premise_shape
      x m c nm nm2 P1 P2 hX hM hC hNm hNm2 hProg with
    ⟨nm2Ref1, xRef, nmRef1, cRef1, mRef, nm2Ref2, nmRef2,
      cRef2, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvZeroExtendUltConst2Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendUltConstValuePremRefs bvZeroExtendUltConstBvsize
    bvZeroExtendUltConstZero bvZeroExtendUltConstLow
    bvZeroExtendUltConstConst bvExtractTerm at hReq
  rw [__eo_prog_bv_zero_extend_ult_const_2.eq_6
    x m c nm nm2 nm2Ref1 xRef nmRef1 cRef1 mRef nm2Ref2
    nmRef2 cRef2 hX hM hC hNm hNm2] at hReq
  rcases bv_zero_extend_ult_const_guard_refs
      (by simpa [bvZeroExtendUltConstGuard] using hReq) with
    ⟨hNm2Ref1, hXRef, hNmRef1, hCRef1, hMRef, hNm2Ref2,
      hNmRef2, hCRef2⟩
  subst nm2Ref1
  subst xRef
  subst nmRef1
  subst cRef1
  subst mRef
  subst nm2Ref2
  subst nmRef2
  subst cRef2
  have hP1Canonical : P1 = bvZeroExtendUltConstWidthPrem x nm2 := by
    simpa using hP1
  have hP2Canonical :
      P2 = bvZeroExtendUltConstValuePrem x m c nm nm2 := by
    simpa [bvZeroExtendUltConstValuePrem] using hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_zero_extend_ult_const_2_program_canonical
    x m c nm nm2 hX hM hC hNm hNm2

theorem typed_bv_zero_extend_ult_const_1_program
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvZeroExtendUltConst1Program x m c nm nm2 P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendUltConst1Program x m c nm nm2 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendUltConst1Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_zero_extend_ult_const_1_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem typed_bv_zero_extend_ult_const_2_program
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvZeroExtendUltConst2Program x m c nm nm2 P1 P2) = Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendUltConst2Program x m c nm nm2 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendUltConst2Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_zero_extend_ult_const_2_term x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem facts_bv_zero_extend_ult_const_1_program
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvZeroExtendUltConst1Program x m c nm nm2 P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvZeroExtendUltConst1Program x m c nm nm2 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
    _hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendUltConst1Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendUltConst1Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hValuePrem :
      eo_interprets M
        (bvZeroExtendUltConstValuePrem x m c nm nm2) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_zero_extend_ult_const_1_term M hM x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy hValuePrem

theorem facts_bv_zero_extend_ult_const_2_program
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm nm2 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    __eo_typeof
        (bvZeroExtendUltConst2Program x m c nm nm2 P1 P2) = Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvZeroExtendUltConst2Program x m c nm nm2 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hResultTy
    _hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendUltConst2Program_normalize x m c nm nm2 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hProg with
    ⟨_hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendUltConst2Term x m c nm nm2) = Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hValuePrem :
      eo_interprets M
        (bvZeroExtendUltConstValuePrem x m c nm nm2) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_zero_extend_ult_const_2_term M hM x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hTermTy hValuePrem

private theorem bv_zero_extend_eq_const_rhs_types
    (x m c nm nm2 nmm1 : Term) :
    __eo_typeof (bvZeroExtendEqConstRhs x m c nm nm2 nmm1) ≠
      Term.Stuck ->
    __eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1) =
        Term.Bool ∧
      __eo_typeof (bvZeroExtendEqConstLower x c nm nm2) = Term.Bool := by
  intro hRhsNe
  change __eo_typeof_or
      (__eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1))
      (__eo_typeof
        (bvZeroExtendEqConstAnd
          (bvZeroExtendEqConstLower x c nm nm2) (Term.Boolean true))) ≠
    Term.Stuck at hRhsNe
  rcases typeof_or_args_bool_of_ne_stuck_zero_extend_local _ _ hRhsNe with
    ⟨hUpperTy, hTailTy⟩
  have hTailTy' :
      __eo_typeof_or
          (__eo_typeof (bvZeroExtendEqConstLower x c nm nm2))
          Term.Bool = Term.Bool := by
    simpa [bvZeroExtendEqConstAnd] using hTailTy
  exact ⟨hUpperTy,
    (typeof_or_bool_args_zero_extend_local _ _ hTailTy').1⟩

private theorem bv_zero_extend_eq_const_1_type_parts
    (x m c nm nm2 nmm1 : Term) :
    __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
      Term.Bool ->
    (∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    __eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1) =
      Term.Bool := by
  intro hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvZeroExtendEqConst1Lhs x m c nm))
      (__eo_typeof (bvZeroExtendEqConstRhs x m c nm nm2 nmm1)) =
    Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hWideNe :
      __eo_typeof_eq
          (__eo_typeof (bvZeroExtendUltConstZero x m))
          (__eo_typeof (bvZeroExtendUltConstConst c nm)) ≠ Term.Stuck := by
    simpa [bvZeroExtendEqConst1Lhs, bvZeroExtendEqConstEq] using hLhsNe
  have hWideTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hWideNe
  have hWideTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hWideTy
  have hWideSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hWideTy
  rcases typeof_zero_extend_result_bitvec_of_ne_stuck_local x m
      hWideSides.1 with ⟨wide, hZeroTy⟩
  have hConstTy :
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
        Term.Apply (Term.UOp UserOp.BitVec) wide :=
    hWideTypesEq.symm.trans hZeroTy
  rcases bv_zero_extend_eq_const_rhs_types x m c nm nm2 nmm1 hRhsNe with
    ⟨hUpperTy, hLowerTy⟩
  have hLowerTy' :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof (bvZeroExtendUltConstLow c nm nm2)) = Term.Bool := by
    simpa [bvZeroExtendEqConstLower, bvZeroExtendEqConstEq] using hLowerTy
  have hLowTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLowerTy'
  have hLowSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLowerTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)
      hLowSides.2 with ⟨low, hLowTy⟩
  have hXTy :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) low :=
    hLowTypesEq.trans hLowTy
  exact ⟨⟨wide, hZeroTy, hConstTy⟩,
    ⟨low, hXTy, hLowTy⟩, hUpperTy⟩

private theorem bv_zero_extend_eq_const_2_type_parts
    (x m c nm nm2 nmm1 : Term) :
    __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
      Term.Bool ->
    (∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    __eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1) =
      Term.Bool := by
  intro hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvZeroExtendEqConst2Lhs x m c nm))
      (__eo_typeof (bvZeroExtendEqConstRhs x m c nm nm2 nmm1)) =
    Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hWideNe :
      __eo_typeof_eq
          (__eo_typeof (bvZeroExtendUltConstConst c nm))
          (__eo_typeof (bvZeroExtendUltConstZero x m)) ≠ Term.Stuck := by
    simpa [bvZeroExtendEqConst2Lhs, bvZeroExtendEqConstEq] using hLhsNe
  have hWideTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hWideNe
  have hWideTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hWideTy
  have hWideSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hWideTy
  rcases typeof_zero_extend_result_bitvec_of_ne_stuck_local x m
      hWideSides.2 with ⟨wide, hZeroTy⟩
  have hConstTy :
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
        Term.Apply (Term.UOp UserOp.BitVec) wide :=
    hWideTypesEq.trans hZeroTy
  rcases bv_zero_extend_eq_const_rhs_types x m c nm nm2 nmm1 hRhsNe with
    ⟨hUpperTy, hLowerTy⟩
  have hLowerTy' :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof (bvZeroExtendUltConstLow c nm nm2)) = Term.Bool := by
    simpa [bvZeroExtendEqConstLower, bvZeroExtendEqConstEq] using hLowerTy
  have hLowTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLowerTy'
  have hLowSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLowerTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)
      hLowSides.2 with ⟨low, hLowTy⟩
  have hXTy :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) low :=
    hLowTypesEq.trans hLowTy
  exact ⟨⟨wide, hZeroTy, hConstTy⟩,
    ⟨low, hXTy, hLowTy⟩, hUpperTy⟩

private theorem bv_zero_extend_eq_const_context_of_types
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    (∃ width,
      __eo_typeof (bvZeroExtendUltConstZero x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    __eo_typeof (bvZeroExtendEqConstUpper m c nm nm2 nmm1) =
      Term.Bool ->
    ∃ W A L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = A ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvZeroExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat A) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendEqConstZero m)) =
        SmtType.BitVec (native_int_to_nat A) := by
  intro hXTrans hMTrans hCTrans hNmTrans hWideTypes hLowTypes hUpperTy
  have hBase := bv_zero_extend_ult_const_context_of_types x m c nm nm2
    hXTrans hMTrans hCTrans hNmTrans hWideTypes hLowTypes
  rcases hBase with
    ⟨W, A, hM, hNm, hW0, hA0, hXSmtTy, hConstSmtTy,
      hLowSmtTy, hZeroSmtTy⟩
  subst m
  subst nm
  have hConstTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConstSmtTy]
    intro h
    cases h
  rcases hLowTypes with ⟨_lowWidth, _hXEoTy, hLowEoTy⟩
  have hLowNe :
      __eo_typeof
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2) ≠ Term.Stuck := by
    rw [hLowEoTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nm2 (Term.Numeral 0) hConstTrans hLowNe with
    ⟨wideLow, L, lowIndex, _hConstEoTyLow, hNm2, hLowIndex,
      hWideLow0, hLowIndex0, hLWide, hDLow0, hConstSmtTyLow⟩
  have hLowIndexEq : lowIndex = 0 := by
    injection hLowIndex with h
    exact h.symm
  subst lowIndex
  subst nm2
  let dLow := native_zplus (native_zplus L 1) (native_zneg 0)
  have hLowSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        SmtType.BitVec (native_int_to_nat dLow) := by
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wideLow L 0 hConstSmtTyLow hWideLow0 hLowIndex0 hLWide hDLow0
  have hDLowNat : native_int_to_nat dLow = native_int_to_nat W := by
    rw [hLowSmtTyRaw] at hLowSmtTy
    injection hLowSmtTy
  have hDLowEq : dLow = W :=
    nonneg_int_eq_of_toNat_eq dLow W
      (native_zleq_of_zlt_true _ _ hDLow0) hW0 hDLowNat
  have hLWidth : native_zplus L 1 = W := by
    simpa [dLow, SmtEval.native_zplus, SmtEval.native_zneg] using hDLowEq
  have hUpperTy' :
      __eo_typeof_eq
          (__eo_typeof
            (bvZeroExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L) nmm1))
          (__eo_typeof
            (bvZeroExtendEqConstZero (Term.Numeral A))) = Term.Bool := by
    simpa [bvZeroExtendEqConstUpper, bvZeroExtendEqConstEq] using hUpperTy
  have hUpperSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hUpperTy'
  have hUpperTypes := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hUpperTy'
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nmm1 (Term.Numeral L) hConstTrans hUpperSides.1 with
    ⟨wideHigh, H, lowHigh, _hConstEoTyHigh, hNmm1, hLowHigh,
      hWideHigh0, hLowHigh0, hHWide, hDHigh0, hConstSmtTyHigh⟩
  have hLowHighEq : lowHigh = L := by
    injection hLowHigh with h
    exact h.symm
  subst lowHigh
  subst nmm1
  let dHigh := native_zplus (native_zplus H 1) (native_zneg L)
  have hHighSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) =
        SmtType.BitVec (native_int_to_nat dHigh) := by
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wideHigh H L hConstSmtTyHigh hWideHigh0 hLowHigh0 hHWide hDHigh0
  have hHighTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hHighSmtTyRaw]
    intro h
    cases h
  have hZeroASmtTy :
      __smtx_typeof
          (__eo_to_smt (bvZeroExtendEqConstZero (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat A) := by
    simpa [bvZeroExtendEqConstZero, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type (Term.Numeral 0) A rfl hA0
  have hZeroATrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendEqConstZero (Term.Numeral A)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hZeroASmtTy]
    intro h
    cases h
  have hHighBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvZeroExtendEqConstHigh c
        (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H))
      (__eo_typeof
        (bvZeroExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H)))
      (__eo_to_smt
        (bvZeroExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H))) rfl hHighTrans rfl
  have hZeroABridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvZeroExtendEqConstZero (Term.Numeral A))
      (__eo_typeof (bvZeroExtendEqConstZero (Term.Numeral A)))
      (__eo_to_smt (bvZeroExtendEqConstZero (Term.Numeral A)))
      rfl hZeroATrans rfl
  have hHighSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) =
        SmtType.BitVec (native_int_to_nat A) := by
    calc
      _ = __eo_to_smt_type
          (__eo_typeof
            (bvZeroExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) := hHighBridge
      _ = __eo_to_smt_type
          (__eo_typeof (bvZeroExtendEqConstZero (Term.Numeral A))) := by
            rw [hUpperTypes]
      _ = __smtx_typeof
          (__eo_to_smt (bvZeroExtendEqConstZero (Term.Numeral A))) :=
            hZeroABridge.symm
      _ = SmtType.BitVec (native_int_to_nat A) := hZeroASmtTy
  have hDHighNat : native_int_to_nat dHigh = native_int_to_nat A := by
    rw [hHighSmtTyRaw] at hHighSmtTy
    injection hHighSmtTy
  have hDHighEq : dHigh = A :=
    nonneg_int_eq_of_toNat_eq dHigh A
      (native_zleq_of_zlt_true _ _ hDHigh0) hA0 hDHighNat
  have hHWidth :
      native_zplus (native_zplus H 1) (native_zneg L) = A := by
    simpa [dHigh] using hDHighEq
  exact ⟨W, A, L, H, rfl, rfl, rfl, rfl, hW0, hA0, hLWidth,
    hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy, hZeroSmtTy,
    hHighSmtTy, hZeroASmtTy⟩

private theorem bv_zero_extend_eq_const_1_context
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
      Term.Bool ->
    ∃ W A L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = A ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvZeroExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat A) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendEqConstZero m)) =
        SmtType.BitVec (native_int_to_nat A) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_eq_const_1_type_parts x m c nm nm2 nmm1
      hResultTy with ⟨hWide, hLow, hUpper⟩
  exact bv_zero_extend_eq_const_context_of_types x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hWide hLow hUpper

private theorem bv_zero_extend_eq_const_2_context
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
      Term.Bool ->
    ∃ W A L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = A ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstZero x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvZeroExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat A) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendEqConstZero m)) =
        SmtType.BitVec (native_int_to_nat A) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_eq_const_2_type_parts x m c nm nm2 nmm1
      hResultTy with ⟨hWide, hLow, hUpper⟩
  exact bv_zero_extend_eq_const_context_of_types x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hWide hLow hUpper

private theorem typed_bv_zero_extend_eq_const_1_term
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_eq_const_1_context x m c nm nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, L, H, rfl, rfl, rfl, rfl, _hW0, _hA0, _hLWidth,
      _hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy, hZeroSmtTy,
      hHighSmtTy, hZeroASmtTy⟩
  have hLhsBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConst1Lhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A))) := by
    unfold bvZeroExtendEqConst1Lhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hZeroSmtTy.trans hConstSmtTy.symm)
      (by rw [hZeroSmtTy]; intro h; cases h)
  have hUpperBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstUpper (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvZeroExtendEqConstUpper bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hZeroASmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hLowerBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstLower x c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold bvZeroExtendEqConstLower bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hXSmtTy.trans hLowSmtTy.symm)
      (by rw [hXSmtTy]; intro h; cases h)
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstAnd
          (bvZeroExtendEqConstLower x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L))
          (Term.Boolean true)) := by
    unfold bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hLowerBool
      RuleProofs.eo_has_bool_type_true
  have hRhsBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstRhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvZeroExtendEqConstRhs bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hUpperBool hTailBool
  unfold bvZeroExtendEqConst1Term bvZeroExtendEqConstEq
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

private theorem typed_bv_zero_extend_eq_const_2_term
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy
  rcases bv_zero_extend_eq_const_2_context x m c nm nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, L, H, rfl, rfl, rfl, rfl, _hW0, _hA0, _hLWidth,
      _hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy, hZeroSmtTy,
      hHighSmtTy, hZeroASmtTy⟩
  have hLhsBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConst2Lhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A))) := by
    unfold bvZeroExtendEqConst2Lhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hConstSmtTy.trans hZeroSmtTy.symm)
      (by rw [hConstSmtTy]; intro h; cases h)
  have hUpperBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstUpper (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvZeroExtendEqConstUpper bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hZeroASmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hLowerBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstLower x c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold bvZeroExtendEqConstLower bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hXSmtTy.trans hLowSmtTy.symm)
      (by rw [hXSmtTy]; intro h; cases h)
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstAnd
          (bvZeroExtendEqConstLower x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L))
          (Term.Boolean true)) := by
    unfold bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hLowerBool
      RuleProofs.eo_has_bool_type_true
  have hRhsBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstRhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvZeroExtendEqConstRhs bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hUpperBool hTailBool
  unfold bvZeroExtendEqConst2Term bvZeroExtendEqConstEq
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

private theorem bv_zero_extend_eq_const_nmm1_numeric
    (M : SmtModel) (N H : native_Int) :
    eo_interprets M
      (bvZeroExtendEqConstNmm1Prem (Term.Numeral N) (Term.Numeral H))
      true ->
    H = native_zplus N (native_zneg 1) := by
  intro hPrem
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq (SmtTerm.Numeral H)
            (SmtTerm.neg (SmtTerm.Numeral N) (SmtTerm.Numeral 1))) =
        SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq] at hEval
      simpa [__smtx_model_eval, __smtx_model_eval_eq,
        __smtx_model_eval__, native_veq] using hEval

/--
The generated rule's low extraction forces `L + 1 = W`, while its upper
extraction has width `H + 1 - L = A`.  The second premise fixes
`H = W + A - 1`, making the upper extraction one bit too wide.  Thus a
well-typed result cannot coexist with true premises.
-/
private theorem bv_zero_extend_eq_const_widths_false
    (W A L H : Int)
    (hLWidth : L + 1 = W)
    (hHWidth : H + 1 + -L = A)
    (hNmm1 : H = W + A + -1) : False := by
  omega

private theorem facts_bv_zero_extend_eq_const_1_term
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
      Term.Bool ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true ->
    eo_interprets M
      (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy _hP1True hP2True
  rcases bv_zero_extend_eq_const_1_context x m c nm nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, L, H, rfl, rfl, rfl, rfl, _hW0, _hA0, hLWidth,
      hHWidth, _hXSmtTy, _hConstSmtTy, _hLowSmtTy, _hZeroSmtTy,
      _hHighSmtTy, _hZeroASmtTy⟩
  have hNmm1 := bv_zero_extend_eq_const_nmm1_numeric M
    (native_zplus W A) H hP2True
  simp only [SmtEval.native_zplus, SmtEval.native_zneg] at hLWidth hHWidth hNmm1
  exact False.elim
    (bv_zero_extend_eq_const_widths_false W A L H hLWidth hHWidth hNmm1)

private theorem facts_bv_zero_extend_eq_const_2_term
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
      Term.Bool ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true ->
    eo_interprets M
      (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hResultTy _hP1True hP2True
  rcases bv_zero_extend_eq_const_2_context x m c nm nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hResultTy with
    ⟨W, A, L, H, rfl, rfl, rfl, rfl, _hW0, _hA0, hLWidth,
      hHWidth, _hXSmtTy, _hConstSmtTy, _hLowSmtTy, _hZeroSmtTy,
      _hHighSmtTy, _hZeroASmtTy⟩
  have hNmm1 := bv_zero_extend_eq_const_nmm1_numeric M
    (native_zplus W A) H hP2True
  simp only [SmtEval.native_zplus, SmtEval.native_zneg] at hLWidth hHWidth hNmm1
  exact False.elim
    (bv_zero_extend_eq_const_widths_false W A L H hLWidth hHWidth hNmm1)

def bvZeroExtendEqConst1Program
    (x m c nm nm2 nmm1 P1 P2 : Term) : Term :=
  __eo_prog_bv_zero_extend_eq_const_1 x m c nm nm2 nmm1
    (Proof.pf P1) (Proof.pf P2)

def bvZeroExtendEqConst2Program
    (x m c nm nm2 nmm1 P1 P2 : Term) : Term :=
  __eo_prog_bv_zero_extend_eq_const_2 x m c nm nm2 nmm1
    (Proof.pf P1) (Proof.pf P2)

private def bvZeroExtendEqConstGuard
    (x nm nm2 nmm1 nm2Ref xRef nmm1Ref nmRef : Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and (__eo_eq nm2 nm2Ref) (__eo_eq x xRef))
      (__eo_eq nmm1 nmm1Ref))
    (__eo_eq nm nmRef)

private theorem bv_zero_extend_eq_const_guard_refs
    {x nm nm2 nmm1 nm2Ref xRef nmm1Ref nmRef body : Term} :
    __eo_requires
        (bvZeroExtendEqConstGuard x nm nm2 nmm1 nm2Ref xRef
          nmm1Ref nmRef)
        (Term.Boolean true) body ≠ Term.Stuck ->
    nm2Ref = nm2 ∧ xRef = x ∧ nmm1Ref = nmm1 ∧ nmRef = nm := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  unfold bvZeroExtendEqConstGuard at hGuard
  rcases bv_extract_support_and_true hGuard with ⟨hG3, hNm⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hNmm1⟩
  rcases bv_extract_support_and_true hG2 with ⟨hNm2, hX⟩
  exact ⟨(bv_extract_support_eq_true hNm2).symm,
    (bv_extract_support_eq_true hX).symm,
    (bv_extract_support_eq_true hNmm1).symm,
    (bv_extract_support_eq_true hNm).symm⟩

private theorem bv_zero_extend_eq_const_1_premise_shape
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck -> nmm1 ≠ Term.Stuck ->
    bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2 ≠
      Term.Stuck ->
    ∃ nm2Ref xRef nmm1Ref nmRef,
      P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
      P2 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref := by
  intro hX hM hC hNm hNm2 hNmm1 hProg
  by_cases hShape :
      ∃ nm2Ref xRef nmm1Ref nmRef,
        P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
        P2 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_zero_extend_eq_const_1.eq_8
      x m c nm nm2 nmm1 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 hNmm1 (by
        intro nm2Ref xRef nmm1Ref nmRef hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨nm2Ref, xRef, nmm1Ref, nmRef, rfl, rfl⟩)

private theorem bv_zero_extend_eq_const_2_premise_shape
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck -> nmm1 ≠ Term.Stuck ->
    bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2 ≠
      Term.Stuck ->
    ∃ nm2Ref xRef nmm1Ref nmRef,
      P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
      P2 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref := by
  intro hX hM hC hNm hNm2 hNmm1 hProg
  by_cases hShape :
      ∃ nm2Ref xRef nmm1Ref nmRef,
        P1 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
        P2 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_zero_extend_eq_const_2.eq_8
      x m c nm nm2 nmm1 (Proof.pf P1) (Proof.pf P2)
      hX hM hC hNm hNm2 hNmm1 (by
        intro nm2Ref xRef nmm1Ref nmRef hP1 hP2
        cases hP1
        cases hP2
        exact hShape ⟨nm2Ref, xRef, nmm1Ref, nmRef, rfl, rfl⟩)

private theorem bv_zero_extend_eq_const_1_program_canonical
    (x m c nm nm2 nmm1 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck -> nmm1 ≠ Term.Stuck ->
    bvZeroExtendEqConst1Program x m c nm nm2 nmm1
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendEqConstNmm1Prem nm nmm1) =
      bvZeroExtendEqConst1Term x m c nm nm2 nmm1 := by
  intro hX hM hC hNm hNm2 hNmm1
  unfold bvZeroExtendEqConst1Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendEqConstNmm1Prem bvZeroExtendUltConstBvsize
  rw [__eo_prog_bv_zero_extend_eq_const_1.eq_7
    x m c nm nm2 nmm1 nm2 x nmm1 nm hX hM hC hNm hNm2 hNmm1]
  simp [bvZeroExtendEqConstGuard, bvZeroExtendEqConst1Term,
    bvZeroExtendEqConst1Lhs, bvZeroExtendEqConstRhs,
    bvZeroExtendEqConstUpper, bvZeroExtendEqConstLower,
    bvZeroExtendEqConstEq, bvZeroExtendEqConstAnd,
    bvZeroExtendEqConstHigh, bvZeroExtendEqConstZero,
    bvZeroExtendUltConstZero, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2, hNmm1]

private theorem bv_zero_extend_eq_const_2_program_canonical
    (x m c nm nm2 nmm1 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> nm2 ≠ Term.Stuck -> nmm1 ≠ Term.Stuck ->
    bvZeroExtendEqConst2Program x m c nm nm2 nmm1
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendEqConstNmm1Prem nm nmm1) =
      bvZeroExtendEqConst2Term x m c nm nm2 nmm1 := by
  intro hX hM hC hNm hNm2 hNmm1
  unfold bvZeroExtendEqConst2Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendEqConstNmm1Prem bvZeroExtendUltConstBvsize
  rw [__eo_prog_bv_zero_extend_eq_const_2.eq_7
    x m c nm nm2 nmm1 nm2 x nmm1 nm hX hM hC hNm hNm2 hNmm1]
  simp [bvZeroExtendEqConstGuard, bvZeroExtendEqConst2Term,
    bvZeroExtendEqConst2Lhs, bvZeroExtendEqConstRhs,
    bvZeroExtendEqConstUpper, bvZeroExtendEqConstLower,
    bvZeroExtendEqConstEq, bvZeroExtendEqConstAnd,
    bvZeroExtendEqConstHigh, bvZeroExtendEqConstZero,
    bvZeroExtendUltConstZero, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hNm2, hNmm1]

private theorem bvZeroExtendEqConst1Program_normalize
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2 ≠
      Term.Stuck ->
    P1 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P2 = bvZeroExtendEqConstNmm1Prem nm nmm1 ∧
      bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2 =
        bvZeroExtendEqConst1Term x m c nm nm2 nmm1 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  have hNmm1 :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nmm1 hNmm1Trans
  rcases bv_zero_extend_eq_const_1_premise_shape
      x m c nm nm2 nmm1 P1 P2 hX hM hC hNm hNm2 hNmm1 hProg with
    ⟨nm2Ref, xRef, nmm1Ref, nmRef, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvZeroExtendEqConst1Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendEqConstNmm1Prem bvZeroExtendUltConstBvsize at hReq
  rw [__eo_prog_bv_zero_extend_eq_const_1.eq_7
    x m c nm nm2 nmm1 nm2Ref xRef nmm1Ref nmRef
    hX hM hC hNm hNm2 hNmm1] at hReq
  rcases bv_zero_extend_eq_const_guard_refs
      (by simpa [bvZeroExtendEqConstGuard] using hReq) with
    ⟨hNm2Ref, hXRef, hNmm1Ref, hNmRef⟩
  subst nm2Ref
  subst xRef
  subst nmm1Ref
  subst nmRef
  have hP1Canonical : P1 = bvZeroExtendUltConstWidthPrem x nm2 := hP1
  have hP2Canonical : P2 = bvZeroExtendEqConstNmm1Prem nm nmm1 := hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_zero_extend_eq_const_1_program_canonical
    x m c nm nm2 nmm1 hX hM hC hNm hNm2 hNmm1

private theorem bvZeroExtendEqConst2Program_normalize
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2 ≠
      Term.Stuck ->
    P1 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P2 = bvZeroExtendEqConstNmm1Prem nm nmm1 ∧
      bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2 =
        bvZeroExtendEqConst2Term x m c nm nm2 nmm1 := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  have hNmm1 :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nmm1 hNmm1Trans
  rcases bv_zero_extend_eq_const_2_premise_shape
      x m c nm nm2 nmm1 P1 P2 hX hM hC hNm hNm2 hNmm1 hProg with
    ⟨nm2Ref, xRef, nmm1Ref, nmRef, hP1, hP2⟩
  have hReq := hProg
  rw [hP1, hP2] at hReq
  unfold bvZeroExtendEqConst2Program bvZeroExtendUltConstWidthPrem
    bvZeroExtendEqConstNmm1Prem bvZeroExtendUltConstBvsize at hReq
  rw [__eo_prog_bv_zero_extend_eq_const_2.eq_7
    x m c nm nm2 nmm1 nm2Ref xRef nmm1Ref nmRef
    hX hM hC hNm hNm2 hNmm1] at hReq
  rcases bv_zero_extend_eq_const_guard_refs
      (by simpa [bvZeroExtendEqConstGuard] using hReq) with
    ⟨hNm2Ref, hXRef, hNmm1Ref, hNmRef⟩
  subst nm2Ref
  subst xRef
  subst nmm1Ref
  subst nmRef
  have hP1Canonical : P1 = bvZeroExtendUltConstWidthPrem x nm2 := hP1
  have hP2Canonical : P2 = bvZeroExtendEqConstNmm1Prem nm nmm1 := hP2
  refine ⟨hP1Canonical, hP2Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical]
  exact bv_zero_extend_eq_const_2_program_canonical
    x m c nm nm2 nmm1 hX hM hC hNm hNm2 hNmm1

theorem typed_bv_zero_extend_eq_const_1_program
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendEqConst1Program_normalize x m c nm nm2 nmm1 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_zero_extend_eq_const_1_term x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem typed_bv_zero_extend_eq_const_2_program
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2) := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendEqConst2Program_normalize x m c nm nm2 nmm1 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg with
    ⟨_hP1, _hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_zero_extend_eq_const_2_term x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hTermTy

theorem facts_bv_zero_extend_eq_const_1_program
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvZeroExtendEqConst1Program x m c nm nm2 nmm1 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans
    hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendEqConst1Program_normalize x m c nm nm2 nmm1 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendEqConst1Term x m c nm nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP1] using hP1True
  have hNmm1Prem :
      eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_zero_extend_eq_const_1_term M hM x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hTermTy hWidthPrem hNmm1Prem

theorem facts_bv_zero_extend_eq_const_2_program
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm nm2 nmm1 P1 P2 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M
      (bvZeroExtendEqConst2Program x m c nm nm2 nmm1 P1 P2) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans
    hResultTy hP1True hP2True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvZeroExtendEqConst2Program_normalize x m c nm nm2 nmm1 P1 P2
      hXTrans hMTrans hCTrans hNmTrans hNm2Trans hNmm1Trans hProg with
    ⟨hP1, hP2, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvZeroExtendEqConst2Term x m c nm nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP1] using hP1True
  have hNmm1Prem :
      eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true := by
    simpa [hP2] using hP2True
  rw [hProgramEq]
  exact facts_bv_zero_extend_eq_const_2_term M hM x m c nm nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hTermTy hWidthPrem hNmm1Prem

/-! Support for the `bv_sign_extend_eq_const` rewrites. -/

def bvSignExtendEqConstMpPrem (m mp : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) mp)
    (Term.Apply (Term.Apply (Term.UOp UserOp.plus) m)
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) (Term.Numeral 1))
        (Term.Numeral 0)))

def bvSignExtendEqConstSign (x m : Term) : Term :=
  Term.Apply (Term.UOp1 UserOp1.sign_extend m) x

def bvSignExtendEqConstZero (mp : Term) : Term :=
  bvZeroExtendUltConstConst (Term.Numeral 0) mp

def bvSignExtendEqConstNotZero (mp : Term) : Term :=
  Term.Apply (Term.UOp UserOp.bvnot) (bvSignExtendEqConstZero mp)

def bvSignExtendEqConstOr (a b : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b

def bvSignExtendEqConstHigh
    (c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstHigh c nm nm2 nmm1

def bvSignExtendEqConstUpperZero
    (mp c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConstHigh c nm nm2 nmm1)
    (bvSignExtendEqConstZero mp)

def bvSignExtendEqConstUpperOnes
    (mp c nm nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConstHigh c nm nm2 nmm1)
    (bvSignExtendEqConstNotZero mp)

def bvSignExtendEqConstUpper
    (mp c nm nm2 nmm1 : Term) : Term :=
  bvSignExtendEqConstOr
    (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1)
    (bvSignExtendEqConstOr
      (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1)
      (Term.Boolean false))

def bvSignExtendEqConstLower
    (x c nm nm2 : Term) : Term :=
  bvZeroExtendEqConstLower x c nm nm2

def bvSignExtendEqConstRhs
    (x m c nm mp nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstAnd
    (bvSignExtendEqConstUpper mp c nm nm2 nmm1)
    (bvZeroExtendEqConstAnd
      (bvSignExtendEqConstLower x c nm nm2) (Term.Boolean true))

def bvSignExtendEqConst1Lhs
    (x m c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConstSign x m)
    (bvZeroExtendUltConstConst c nm)

def bvSignExtendEqConst2Lhs
    (x m c nm : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvZeroExtendUltConstConst c nm)
    (bvSignExtendEqConstSign x m)

def bvSignExtendEqConst1Term
    (x m c nm mp nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConst1Lhs x m c nm)
    (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1)

def bvSignExtendEqConst2Term
    (x m c nm mp nm2 nmm1 : Term) : Term :=
  bvZeroExtendEqConstEq
    (bvSignExtendEqConst2Lhs x m c nm)
    (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1)

private theorem signExtend_eq_iff_low_upper
    (x : BitVec W) (c : BitVec (W + A)) (hW : 0 < W) :
    x.signExtend (W + A) = c ↔
      x = c.extractLsb' 0 W ∧
        (c.extractLsb' (W - 1) (A + 1) = 0#(A + 1) ∨
          c.extractLsb' (W - 1) (A + 1) = BitVec.allOnes (A + 1)) := by
  constructor
  · intro h
    subst c
    constructor
    · apply BitVec.eq_of_getElem_eq
      intro i hi
      rw [BitVec.getElem_extractLsb' hi,
        BitVec.getLsbD_eq_getElem (by omega),
        BitVec.getElem_signExtend (by omega)]
      simp [hi]
    · cases hx : x.msb
      · left
        apply BitVec.eq_of_getElem_eq
        intro i hi
        rw [BitVec.getElem_extractLsb' hi,
          BitVec.getLsbD_eq_getElem (by omega),
          BitVec.getElem_signExtend (by omega)]
        simp [BitVec.getElem_zero, hx]
        intro h
        have hi0 : i = 0 := by omega
        subst i
        simpa [BitVec.msb_eq_getLsbD_last,
          BitVec.getLsbD_eq_getElem (by omega)] using hx
      · right
        apply BitVec.eq_of_getElem_eq
        intro i hi
        rw [BitVec.getElem_extractLsb' hi,
          BitVec.getLsbD_eq_getElem (by omega),
          BitVec.getElem_signExtend (by omega)]
        simp [BitVec.getElem_allOnes, hx]
        intro h
        have hi0 : i = 0 := by omega
        subst i
        simpa [BitVec.msb_eq_getLsbD_last,
          BitVec.getLsbD_eq_getElem (by omega)] using hx
  · rintro ⟨hLow, hUpper⟩
    apply BitVec.eq_of_getElem_eq
    intro i hi
    rw [BitVec.getElem_signExtend hi]
    split
    · rename_i hiW
      have hBit := congrArg (fun z : BitVec W => z[i]) hLow
      simpa [BitVec.getElem_extractLsb',
        BitVec.getLsbD_eq_getElem hiW] using hBit
    · rename_i hiW
      have hIdx : i - (W - 1) < A + 1 := by omega
      have hFull : W - 1 + (i - (W - 1)) = i := by omega
      rcases hUpper with hZero | hOnes
      · have hUpperBit := congrArg
            (fun z : BitVec (A + 1) => z[i - (W - 1)]'hIdx) hZero
        have hMsbIdx : W - 1 < W := by omega
        have hCMsbIdx : W - 1 < W + A := by omega
        have hLowMsb := congrArg
          (fun z : BitVec W => z[W - 1]'hMsbIdx) hLow
        have hCMsb : c[W - 1] = x.msb := by
          calc
            c[W - 1] = c.getLsbD (W - 1) :=
              (BitVec.getLsbD_eq_getElem hCMsbIdx).symm
            _ = x[W - 1] := by
              simpa [BitVec.getElem_extractLsb'] using hLowMsb.symm
            _ = x.getLsbD (W - 1) :=
              (BitVec.getLsbD_eq_getElem hMsbIdx).symm
            _ = x.msb := (BitVec.msb_eq_getLsbD_last x).symm
        have hCi : c[i] = false := by
          simpa [BitVec.getElem_extractLsb', hFull,
            BitVec.getLsbD_eq_getElem hi, BitVec.getElem_zero] using hUpperBit
        have hCBase : c[W - 1] = false := by
          have hBaseIdx : (0 : Nat) < A + 1 := by omega
          have hBase := congrArg
            (fun z : BitVec (A + 1) => z[0]'hBaseIdx) hZero
          simpa [BitVec.getElem_extractLsb',
            BitVec.getLsbD_eq_getElem hMsbIdx, BitVec.getElem_zero] using hBase
        rw [hCMsb] at hCBase
        rw [hCBase, hCi]
      · have hUpperBit := congrArg
            (fun z : BitVec (A + 1) => z[i - (W - 1)]'hIdx) hOnes
        have hMsbIdx : W - 1 < W := by omega
        have hCMsbIdx : W - 1 < W + A := by omega
        have hLowMsb := congrArg
          (fun z : BitVec W => z[W - 1]'hMsbIdx) hLow
        have hCMsb : c[W - 1] = x.msb := by
          calc
            c[W - 1] = c.getLsbD (W - 1) :=
              (BitVec.getLsbD_eq_getElem hCMsbIdx).symm
            _ = x[W - 1] := by
              simpa [BitVec.getElem_extractLsb'] using hLowMsb.symm
            _ = x.getLsbD (W - 1) :=
              (BitVec.getLsbD_eq_getElem hMsbIdx).symm
            _ = x.msb := (BitVec.msb_eq_getLsbD_last x).symm
        have hCi : c[i] = true := by
          simpa [BitVec.getElem_extractLsb', hFull,
            BitVec.getLsbD_eq_getElem hi, BitVec.getElem_allOnes] using hUpperBit
        have hCBase : c[W - 1] = true := by
          have hBaseIdx : (0 : Nat) < A + 1 := by omega
          have hBase := congrArg
            (fun z : BitVec (A + 1) => z[0]'hBaseIdx) hOnes
          simpa [BitVec.getElem_extractLsb',
            BitVec.getLsbD_eq_getElem hMsbIdx,
            BitVec.getElem_allOnes] using hBase
        rw [hCMsb] at hCBase
        rw [hCBase, hCi]

private theorem smt_eval_eq_bitvec_values (x y : BitVec W) :
    __smtx_model_eval_eq
        (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
        (SmtValue.Binary (↑W : Int) (↑y.toNat : Int)) =
      SmtValue.Boolean (decide (x = y)) := by
  simp only [__smtx_model_eval_eq, native_veq]
  congr 1
  simp only [decide_eq_decide]
  constructor
  · intro h
    injection h with _ hp
    apply BitVec.eq_of_toNat_eq
    exact_mod_cast hp
  · intro h
    subst y
    rfl

private theorem smt_eval_bvnot_zero_value (W : Nat) :
    __smtx_model_eval_bvnot (SmtValue.Binary (↑W : Int) 0) =
      SmtValue.Binary (↑W : Int) (↑(BitVec.allOnes W).toNat : Int) := by
  have hPowPos : (0 : Int) < (2 : Int) ^ W := by
    exact_mod_cast Nat.two_pow_pos W
  have hLower : 0 ≤ (2 : Int) ^ W - 1 := by omega
  have hUpper : (2 : Int) ^ W - 1 < (2 : Int) ^ W := by omega
  have hMod : ((2 : Int) ^ W - 1) % (2 : Int) ^ W =
      (2 : Int) ^ W - 1 :=
    Int.emod_eq_of_lt hLower hUpper
  simp only [__smtx_model_eval_bvnot, native_mod_total, native_binary_not,
    native_zplus, native_zneg, BitVec.toNat_allOnes]
  rw [natpow2_eq W]
  rw [show (2 : Int) ^ W + -(0 + 1) = (2 : Int) ^ W - 1 by omega]
  rw [hMod]
  congr 2
  exact (Int.ofNat_sub Nat.one_le_two_pow).symm

private theorem eval_sign_extend_eq_characterization
    (x : BitVec W) (c : BitVec (W + A)) (hW : 0 < W) :
    __smtx_model_eval_eq
        (SmtValue.Binary (↑(W + A) : Int)
          (↑(x.signExtend (W + A)).toNat : Int))
        (SmtValue.Binary (↑(W + A) : Int) (↑c.toNat : Int)) =
      __smtx_model_eval_and
        (__smtx_model_eval_or
          (__smtx_model_eval_eq
            (SmtValue.Binary (↑(A + 1) : Int)
              (↑(c.extractLsb' (W - 1) (A + 1)).toNat : Int))
            (SmtValue.Binary (↑(A + 1) : Int)
              (↑(0#(A + 1)).toNat : Int)))
          (__smtx_model_eval_or
            (__smtx_model_eval_eq
              (SmtValue.Binary (↑(A + 1) : Int)
                (↑(c.extractLsb' (W - 1) (A + 1)).toNat : Int))
              (__smtx_model_eval_bvnot
                (SmtValue.Binary (↑(A + 1) : Int) 0)))
            (SmtValue.Boolean false)))
        (__smtx_model_eval_and
          (__smtx_model_eval_eq
            (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
            (SmtValue.Binary (↑W : Int)
              (↑(c.extractLsb' 0 W).toNat : Int)))
          (SmtValue.Boolean true)) := by
  rw [smt_eval_eq_bitvec_values,
    smt_eval_eq_bitvec_values,
    smt_eval_bvnot_zero_value,
    smt_eval_eq_bitvec_values,
    smt_eval_eq_bitvec_values]
  simp only [__smtx_model_eval_or, __smtx_model_eval_and,
    native_or, native_and]
  have hIff :
    (x.signExtend (W + A) = c) ↔
      x = c.extractLsb' 0 W ∧
        (c.extractLsb' (W - 1) (A + 1) = 0#(A + 1) ∨
          c.extractLsb' (W - 1) (A + 1) = BitVec.allOnes (A + 1))
      := signExtend_eq_iff_low_upper x c hW
  by_cases hLow : x = c.extractLsb' 0 W
  · by_cases hZero :
        c.extractLsb' (W - 1) (A + 1) = 0#(A + 1)
    · have hSign : x.signExtend (W + A) = c :=
        hIff.mpr ⟨hLow, Or.inl hZero⟩
      have hSign' : (c.extractLsb' 0 W).signExtend (W + A) = c := by
        simpa [hLow] using hSign
      simp [hLow, hZero, hSign']
    · by_cases hOnes :
          c.extractLsb' (W - 1) (A + 1) = BitVec.allOnes (A + 1)
      · have hSign : x.signExtend (W + A) = c :=
          hIff.mpr ⟨hLow, Or.inr hOnes⟩
        have hSign' : (c.extractLsb' 0 W).signExtend (W + A) = c := by
          simpa [hLow] using hSign
        simp [hLow, hOnes, hSign']
      · have hSign : x.signExtend (W + A) ≠ c := by
          intro h
          rcases (hIff.mp h).2 with hUpper | hUpper
          · exact hZero hUpper
          · exact hOnes hUpper
        have hSign' :
            (c.extractLsb' 0 W).signExtend (W + A) ≠ c := by
          simpa [hLow] using hSign
        simp [hLow, hZero, hOnes, hSign']
  · have hSign : x.signExtend (W + A) ≠ c := by
      intro h
      exact hLow (hIff.mp h).1
    simp [hLow, hSign]

private theorem typeof_sign_extend_result_bitvec_of_ne_stuck_local
    (x m : Term)
    (h : __eo_typeof (bvSignExtendEqConstSign x m) ≠ Term.Stuck) :
    ∃ width,
      __eo_typeof (bvSignExtendEqConstSign x m) =
        Term.Apply (Term.UOp UserOp.BitVec) width := by
  change __eo_typeof_zero_extend (__eo_typeof m) m (__eo_typeof x) ≠
    Term.Stuck at h
  change ∃ width,
    __eo_typeof_zero_extend (__eo_typeof m) m (__eo_typeof x) =
      Term.Apply (Term.UOp UserOp.BitVec) width
  unfold __eo_typeof_zero_extend at h ⊢
  split at h <;> simp_all [__eo_requires, __eo_mk_apply, native_ite,
    native_teq, native_not]
  exact mk_apply_bitvec_shape_of_ne_stuck_local _ h.2

private theorem smt_typeof_bvnot_same_local
    (a : SmtTerm) (n : native_Int) :
    __smtx_typeof a = SmtType.BitVec (native_int_to_nat n) ->
    __smtx_typeof (SmtTerm.bvnot a) =
      SmtType.BitVec (native_int_to_nat n) := by
  intro ha
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [__smtx_typeof_bv_op_1, ha]

private theorem eo_has_bool_type_or_of_bool_args_local (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) := by
  intro hA hB
  unfold RuleProofs.eo_has_bool_type at hA hB ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [hA, hB, native_ite, native_Teq]

private theorem eo_has_bool_type_false_local :
    RuleProofs.eo_has_bool_type (Term.Boolean false) := by
  unfold RuleProofs.eo_has_bool_type
  rw [show __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false by rfl]
  rw [__smtx_typeof.eq_def] <;> simp only

private theorem bv_sign_extend_eq_const_rhs_types
    (x m c nm mp nm2 nmm1 : Term) :
    __eo_typeof (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1) ≠
      Term.Stuck ->
    __eo_typeof (bvSignExtendEqConstUpper mp c nm nm2 nmm1) =
        Term.Bool ∧
      __eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1) =
        Term.Bool ∧
      __eo_typeof (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1) =
        Term.Bool ∧
      __eo_typeof (bvSignExtendEqConstLower x c nm nm2) = Term.Bool := by
  intro hRhsNe
  change __eo_typeof_or
      (__eo_typeof (bvSignExtendEqConstUpper mp c nm nm2 nmm1))
      (__eo_typeof
        (bvZeroExtendEqConstAnd
          (bvSignExtendEqConstLower x c nm nm2) (Term.Boolean true))) ≠
    Term.Stuck at hRhsNe
  rcases typeof_or_args_bool_of_ne_stuck_zero_extend_local _ _ hRhsNe with
    ⟨hUpperTy, hTailTy⟩
  have hTailTy' :
      __eo_typeof_or
          (__eo_typeof (bvSignExtendEqConstLower x c nm nm2))
          Term.Bool = Term.Bool := by
    simpa [bvZeroExtendEqConstAnd] using hTailTy
  have hLowerTy := (typeof_or_bool_args_zero_extend_local _ _ hTailTy').1
  have hUpperTy' :
      __eo_typeof_or
          (__eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1))
          (__eo_typeof
            (bvSignExtendEqConstOr
              (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1)
              (Term.Boolean false))) = Term.Bool := by
    simpa [bvSignExtendEqConstUpper, bvSignExtendEqConstOr] using hUpperTy
  rcases typeof_or_bool_args_zero_extend_local _ _ hUpperTy' with
    ⟨hUpperZeroTy, hUpperTailTy⟩
  have hUpperTailTy' :
      __eo_typeof_or
          (__eo_typeof (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1))
          Term.Bool = Term.Bool := by
    simpa [bvSignExtendEqConstOr] using hUpperTailTy
  have hUpperOnesTy :=
    (typeof_or_bool_args_zero_extend_local _ _ hUpperTailTy').1
  exact ⟨hUpperTy, hUpperZeroTy, hUpperOnesTy, hLowerTy⟩

private theorem bv_sign_extend_eq_const_1_type_parts
    (x m c nm mp nm2 nmm1 : Term) :
    __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    (∃ width,
      __eo_typeof (bvSignExtendEqConstSign x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    __eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1) =
      Term.Bool ∧
    __eo_typeof (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1) =
      Term.Bool := by
  intro hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvSignExtendEqConst1Lhs x m c nm))
      (__eo_typeof (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1)) =
    Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hWideNe :
      __eo_typeof_eq
          (__eo_typeof (bvSignExtendEqConstSign x m))
          (__eo_typeof (bvZeroExtendUltConstConst c nm)) ≠ Term.Stuck := by
    simpa [bvSignExtendEqConst1Lhs, bvZeroExtendEqConstEq] using hLhsNe
  have hWideTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hWideNe
  have hWideTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hWideTy
  have hWideSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hWideTy
  rcases typeof_sign_extend_result_bitvec_of_ne_stuck_local x m
      hWideSides.1 with ⟨wide, hSignTy⟩
  have hConstTy :
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
        Term.Apply (Term.UOp UserOp.BitVec) wide :=
    hWideTypesEq.symm.trans hSignTy
  rcases bv_sign_extend_eq_const_rhs_types x m c nm mp nm2 nmm1 hRhsNe with
    ⟨_hUpperTy, hUpperZeroTy, hUpperOnesTy, hLowerTy⟩
  have hLowerTy' :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof (bvZeroExtendUltConstLow c nm nm2)) = Term.Bool := by
    simpa [bvSignExtendEqConstLower, bvZeroExtendEqConstLower,
      bvZeroExtendEqConstEq] using hLowerTy
  have hLowTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLowerTy'
  have hLowSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLowerTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)
      hLowSides.2 with ⟨low, hLowTy⟩
  have hXTy :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) low :=
    hLowTypesEq.trans hLowTy
  exact ⟨⟨wide, hSignTy, hConstTy⟩,
    ⟨low, hXTy, hLowTy⟩, hUpperZeroTy, hUpperOnesTy⟩

private theorem bv_sign_extend_eq_const_2_type_parts
    (x m c nm mp nm2 nmm1 : Term) :
    __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    (∃ width,
      __eo_typeof (bvSignExtendEqConstSign x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ∧
    __eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1) =
      Term.Bool ∧
    __eo_typeof (bvSignExtendEqConstUpperOnes mp c nm nm2 nmm1) =
      Term.Bool := by
  intro hResultTy
  change __eo_typeof_eq
      (__eo_typeof (bvSignExtendEqConst2Lhs x m c nm))
      (__eo_typeof (bvSignExtendEqConstRhs x m c nm mp nm2 nmm1)) =
    Term.Bool at hResultTy
  rcases RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hResultTy with
    ⟨hLhsNe, hRhsNe⟩
  have hWideNe :
      __eo_typeof_eq
          (__eo_typeof (bvZeroExtendUltConstConst c nm))
          (__eo_typeof (bvSignExtendEqConstSign x m)) ≠ Term.Stuck := by
    simpa [bvSignExtendEqConst2Lhs, bvZeroExtendEqConstEq] using hLhsNe
  have hWideTy := eo_typeof_eq_bool_of_ne_stuck_zero_extend_local _ _ hWideNe
  have hWideTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hWideTy
  have hWideSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hWideTy
  rcases typeof_sign_extend_result_bitvec_of_ne_stuck_local x m
      hWideSides.2 with ⟨wide, hSignTy⟩
  have hConstTy :
      __eo_typeof (bvZeroExtendUltConstConst c nm) =
        Term.Apply (Term.UOp UserOp.BitVec) wide :=
    hWideTypesEq.trans hSignTy
  rcases bv_sign_extend_eq_const_rhs_types x m c nm mp nm2 nmm1 hRhsNe with
    ⟨_hUpperTy, hUpperZeroTy, hUpperOnesTy, hLowerTy⟩
  have hLowerTy' :
      __eo_typeof_eq (__eo_typeof x)
          (__eo_typeof (bvZeroExtendUltConstLow c nm nm2)) = Term.Bool := by
    simpa [bvSignExtendEqConstLower, bvZeroExtendEqConstLower,
      bvZeroExtendEqConstEq] using hLowerTy
  have hLowTypesEq := RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hLowerTy'
  have hLowSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hLowerTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c nm) nm2 (Term.Numeral 0)
      hLowSides.2 with ⟨low, hLowTy⟩
  have hXTy :
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) low :=
    hLowTypesEq.trans hLowTy
  exact ⟨⟨wide, hSignTy, hConstTy⟩,
    ⟨low, hXTy, hLowTy⟩, hUpperZeroTy, hUpperOnesTy⟩

private theorem bv_sign_extend_eq_const_context_of_types
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    (∃ width,
      __eo_typeof (bvSignExtendEqConstSign x m) =
          Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstConst c nm) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    (∃ width,
      __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) width ∧
        __eo_typeof (bvZeroExtendUltConstLow c nm nm2) =
          Term.Apply (Term.UOp UserOp.BitVec) width) ->
    __eo_typeof (bvSignExtendEqConstUpperZero mp c nm nm2 nmm1) =
      Term.Bool ->
    ∃ W A P L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      mp = Term.Numeral P ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 P = true ∧
      native_zleq 0 L = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = P ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvSignExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstZero mp)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstNotZero mp)) =
        SmtType.BitVec (native_int_to_nat P) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hWideTypes hLowTypes
    hUpperZeroTy
  rcases hLowTypes with ⟨widthW, hXTy, hLowTy⟩
  rcases smt_bitvec_type_of_eo_bitvec_type_with_width
      x widthW hXTrans hXTy with
    ⟨W, hWidthW, hW0, hXSmtTy⟩
  subst widthW
  rcases hWideTypes with ⟨widthWide, hSignTy, hConstTy⟩
  rcases sign_extend_index_context x m widthWide W hXTy hSignTy with
    ⟨A, hM, hA0, hWidthWide⟩
  subst m
  subst widthWide
  have hCNe := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNmNe := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  rcases bv_all_ones_const_context c nm
      (Term.Numeral (native_zplus W A)) hCNe hNmNe
      (by simpa [bvZeroExtendUltConstConst] using hConstTy) with
    ⟨N, hNm, hWidthN, hN0, hCTy⟩
  have hN : N = native_zplus W A := by
    injection hWidthN with h
    exact h.symm
  subst N
  subst nm
  have hCSmtTy : __smtx_typeof (__eo_to_smt c) = SmtType.Int :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c (Term.UOp UserOp.Int) (__eo_to_smt c) rfl hCTrans hCTy
  have hConstSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    simpa [bvAllOnesConst, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type c (native_zplus W A)
        hCSmtTy hN0
  have hConstTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A))) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hConstSmtTy]
    intro h
    cases h
  have hLowNe :
      __eo_typeof
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) nm2) ≠ Term.Stuck := by
    rw [hLowTy]
    intro h
    cases h
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nm2 (Term.Numeral 0) hConstTrans hLowNe with
    ⟨wideLow, L, lowIndex, _hConstEoTyLow, hNm2, hLowIndex,
      hWideLow0, hLowIndex0, hLWide, hDLow0, hConstSmtTyLow⟩
  have hLowIndexEq : lowIndex = 0 := by
    injection hLowIndex with h
    exact h.symm
  subst lowIndex
  subst nm2
  let dLow := native_zplus (native_zplus L 1) (native_zneg 0)
  have hLowSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        SmtType.BitVec (native_int_to_nat dLow) := by
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wideLow L 0 hConstSmtTyLow hWideLow0 hLowIndex0 hLWide hDLow0
  have hLowTrans :
      RuleProofs.eo_has_smt_translation
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hLowSmtTyRaw]
    intro h
    cases h
  have hLowSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        SmtType.BitVec (native_int_to_nat W) := by
    have h :=
      RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
        (bvZeroExtendUltConstLow c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L))
        (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral W))
        (__eo_to_smt
          (bvZeroExtendUltConstLow c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L)))
        rfl hLowTrans hLowTy
    simpa [__eo_to_smt_type, hW0, native_ite] using h
  have hDLowNat : native_int_to_nat dLow = native_int_to_nat W := by
    rw [hLowSmtTyRaw] at hLowSmtTy
    injection hLowSmtTy
  have hDLowEq : dLow = W :=
    nonneg_int_eq_of_toNat_eq dLow W
      (native_zleq_of_zlt_true _ _ hDLow0) hW0 hDLowNat
  have hLWidth : native_zplus L 1 = W := by
    simpa [dLow, SmtEval.native_zplus, SmtEval.native_zneg] using hDLowEq
  have hSignSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) := by
    have hRaw := smt_typeof_sign_extend_of_context x W A
      hXSmtTy hW0 hA0
    have hComm : native_zplus A W = native_zplus W A := by
      simp [SmtEval.native_zplus, Int.add_comm]
    simpa [bvSignExtendEqConstSign, hComm] using hRaw
  have hUpperZeroTy' :
      __eo_typeof_eq
          (__eo_typeof
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L) nmm1))
          (__eo_typeof (bvSignExtendEqConstZero mp)) = Term.Bool := by
    simpa [bvSignExtendEqConstUpperZero, bvSignExtendEqConstHigh,
      bvZeroExtendEqConstEq] using hUpperZeroTy
  have hUpperZeroSides :=
    RuleProofs.eo_typeof_eq_bool_operands_not_stuck _ _ hUpperZeroTy'
  have hUpperZeroTypes :=
    RuleProofs.eo_typeof_eq_bool_operands_eq _ _ hUpperZeroTy'
  rcases typeof_extract_result_bitvec_of_ne_stuck_local
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A))) nmm1 (Term.Numeral L)
      hUpperZeroSides.1 with ⟨upperWidth, hHighEoTy⟩
  rcases bv_extract_context_of_non_stuck
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      nmm1 (Term.Numeral L) hConstTrans hUpperZeroSides.1 with
    ⟨wideHigh, H, lowHigh, _hConstEoTyHigh, hNmm1, hLowHigh,
      hWideHigh0, hLowHigh0, hHWide, hDHigh0, hConstSmtTyHigh⟩
  have hLowHighEq : lowHigh = L := by
    injection hLowHigh with h
    exact h.symm
  subst lowHigh
  subst nmm1
  let dHigh := native_zplus (native_zplus H 1) (native_zneg L)
  have hHighSmtTyRaw :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) =
        SmtType.BitVec (native_int_to_nat dHigh) := by
    exact smt_typeof_extract_of_context
      (bvZeroExtendUltConstConst c
        (Term.Numeral (native_zplus W A)))
      wideHigh H L hConstSmtTyHigh hWideHigh0 hLowHigh0 hHWide hDHigh0
  have hMpNe := RuleProofs.term_ne_stuck_of_has_smt_translation mp hMpTrans
  have hZeroEoTy :
      __eo_typeof (bvSignExtendEqConstZero mp) =
        Term.Apply (Term.UOp UserOp.BitVec) upperWidth :=
    hUpperZeroTypes.symm.trans hHighEoTy
  rcases bv_all_ones_const_context (Term.Numeral 0) mp upperWidth
      (by intro h; cases h) hMpNe
      (by simpa [bvSignExtendEqConstZero, bvZeroExtendUltConstConst,
        bvAllOnesConst] using hZeroEoTy) with
    ⟨P, hMp, hUpperWidth, hP0, _hZeroValTy⟩
  subst mp
  subst upperWidth
  have hHighTrans :
      RuleProofs.eo_has_smt_translation
        (bvSignExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hHighSmtTyRaw]
    intro h
    cases h
  have hZeroSmtTy :
      __smtx_typeof
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P))) =
        SmtType.BitVec (native_int_to_nat P) := by
    simpa [bvSignExtendEqConstZero, bvZeroExtendUltConstConst] using
      smt_typeof_bv_const_of_int_type (Term.Numeral 0) P rfl hP0
  have hZeroTrans :
      RuleProofs.eo_has_smt_translation
        (bvSignExtendEqConstZero (Term.Numeral P)) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hZeroSmtTy]
    intro h
    cases h
  have hHighBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvSignExtendEqConstHigh c
        (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H))
      (__eo_typeof
        (bvSignExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H)))
      (__eo_to_smt
        (bvSignExtendEqConstHigh c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H))) rfl hHighTrans rfl
  have hZeroBridge :=
    RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      (bvSignExtendEqConstZero (Term.Numeral P))
      (__eo_typeof (bvSignExtendEqConstZero (Term.Numeral P)))
      (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P)))
      rfl hZeroTrans rfl
  have hHighSmtTy :
      __smtx_typeof
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) =
        SmtType.BitVec (native_int_to_nat P) := by
    calc
      _ = __eo_to_smt_type
          (__eo_typeof
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H))) := hHighBridge
      _ = __eo_to_smt_type
          (__eo_typeof (bvSignExtendEqConstZero (Term.Numeral P))) := by
            rw [hUpperZeroTypes]
      _ = __smtx_typeof
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P))) :=
            hZeroBridge.symm
      _ = SmtType.BitVec (native_int_to_nat P) := hZeroSmtTy
  have hDHighNat : native_int_to_nat dHigh = native_int_to_nat P := by
    rw [hHighSmtTyRaw] at hHighSmtTy
    injection hHighSmtTy
  have hDHighEq : dHigh = P :=
    nonneg_int_eq_of_toNat_eq dHigh P
      (native_zleq_of_zlt_true _ _ hDHigh0) hP0 hDHighNat
  have hHWidth :
      native_zplus (native_zplus H 1) (native_zneg L) = P := by
    simpa [dHigh] using hDHighEq
  have hNotZeroSmtTy :
      __smtx_typeof
          (__eo_to_smt (bvSignExtendEqConstNotZero (Term.Numeral P))) =
        SmtType.BitVec (native_int_to_nat P) := by
    change __smtx_typeof
        (SmtTerm.bvnot
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P)))) = _
    exact smt_typeof_bvnot_same_local
      (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P))) P
      hZeroSmtTy
  exact ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl,
    hW0, hA0, hP0, hLowHigh0, hLWidth, hHWidth, hXSmtTy, hConstSmtTy,
    hLowSmtTy, hSignSmtTy, hHighSmtTy, hZeroSmtTy, hNotZeroSmtTy⟩

private theorem bv_sign_extend_eq_const_1_context
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    ∃ W A P L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      mp = Term.Numeral P ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 P = true ∧
      native_zleq 0 L = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = P ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvSignExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstZero mp)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstNotZero mp)) =
        SmtType.BitVec (native_int_to_nat P) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_1_type_parts x m c nm mp nm2 nmm1
      hResultTy with ⟨hWide, hLow, hUpperZero, _hUpperOnes⟩
  exact bv_sign_extend_eq_const_context_of_types x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hWide hLow hUpperZero

private theorem bv_sign_extend_eq_const_2_context
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    ∃ W A P L H : native_Int,
      m = Term.Numeral A ∧
      nm = Term.Numeral (native_zplus W A) ∧
      mp = Term.Numeral P ∧
      nm2 = Term.Numeral L ∧ nmm1 = Term.Numeral H ∧
      native_zleq 0 W = true ∧ native_zleq 0 A = true ∧
      native_zleq 0 P = true ∧
      native_zleq 0 L = true ∧
      native_zplus L 1 = W ∧
      native_zplus (native_zplus H 1) (native_zneg L) = P ∧
      __smtx_typeof (__eo_to_smt x) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstConst c nm)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt (bvZeroExtendUltConstLow c nm nm2)) =
        SmtType.BitVec (native_int_to_nat W) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstSign x m)) =
        SmtType.BitVec (native_int_to_nat (native_zplus W A)) ∧
      __smtx_typeof (__eo_to_smt
        (bvSignExtendEqConstHigh c nm nm2 nmm1)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstZero mp)) =
        SmtType.BitVec (native_int_to_nat P) ∧
      __smtx_typeof (__eo_to_smt (bvSignExtendEqConstNotZero mp)) =
        SmtType.BitVec (native_int_to_nat P) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_2_type_parts x m c nm mp nm2 nmm1
      hResultTy with ⟨hWide, hLow, hUpperZero, _hUpperOnes⟩
  exact bv_sign_extend_eq_const_context_of_types x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hWide hLow hUpperZero

private theorem typed_bv_sign_extend_eq_const_1_term
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_1_context x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy with
    ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl, _hW0, _hA0, _hP0,
      _hL0, _hLWidth, _hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy,
      hSignSmtTy, hHighSmtTy, hZeroSmtTy, hNotZeroSmtTy⟩
  have hLhsBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A))) := by
    unfold bvSignExtendEqConst1Lhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hSignSmtTy.trans hConstSmtTy.symm)
      (by rw [hSignSmtTy]; intro h; cases h)
  have hUpperZeroBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpperZero (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpperZero bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hZeroSmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hUpperOnesBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpperOnes bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hNotZeroSmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hUpperTailBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstOr
          (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H))
          (Term.Boolean false)) := by
    unfold bvSignExtendEqConstOr
    exact eo_has_bool_type_or_of_bool_args_local _ _
      hUpperOnesBool eo_has_bool_type_false_local
  have hUpperBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpper (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpper bvSignExtendEqConstOr
    exact eo_has_bool_type_or_of_bool_args_local _ _
      hUpperZeroBool hUpperTailBool
  have hLowerBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstLower x c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold bvSignExtendEqConstLower bvZeroExtendEqConstLower
      bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hXSmtTy.trans hLowSmtTy.symm)
      (by rw [hXSmtTy]; intro h; cases h)
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstAnd
          (bvSignExtendEqConstLower x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L))
          (Term.Boolean true)) := by
    unfold bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hLowerBool RuleProofs.eo_has_bool_type_true
  have hRhsBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstRhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral P)
          (Term.Numeral L) (Term.Numeral H)) := by
    unfold bvSignExtendEqConstRhs bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hUpperBool hTailBool
  unfold bvSignExtendEqConst1Term bvZeroExtendEqConstEq
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

private theorem typed_bv_sign_extend_eq_const_2_term
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_2_context x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy with
    ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl, _hW0, _hA0, _hP0,
      _hL0, _hLWidth, _hHWidth, hXSmtTy, hConstSmtTy, hLowSmtTy,
      hSignSmtTy, hHighSmtTy, hZeroSmtTy, hNotZeroSmtTy⟩
  have hLhsBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConst2Lhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A))) := by
    unfold bvSignExtendEqConst2Lhs bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hConstSmtTy.trans hSignSmtTy.symm)
      (by rw [hConstSmtTy]; intro h; cases h)
  have hUpperZeroBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpperZero (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpperZero bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hZeroSmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hUpperOnesBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpperOnes bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hHighSmtTy.trans hNotZeroSmtTy.symm)
      (by rw [hHighSmtTy]; intro h; cases h)
  have hUpperTailBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstOr
          (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L)
            (Term.Numeral H))
          (Term.Boolean false)) := by
    unfold bvSignExtendEqConstOr
    exact eo_has_bool_type_or_of_bool_args_local _ _
      hUpperOnesBool eo_has_bool_type_false_local
  have hUpperBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstUpper (Term.Numeral P) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)
          (Term.Numeral H)) := by
    unfold bvSignExtendEqConstUpper bvSignExtendEqConstOr
    exact eo_has_bool_type_or_of_bool_args_local _ _
      hUpperZeroBool hUpperTailBool
  have hLowerBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstLower x c
          (Term.Numeral (native_zplus W A)) (Term.Numeral L)) := by
    unfold bvSignExtendEqConstLower bvZeroExtendEqConstLower
      bvZeroExtendEqConstEq
    exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
      (hXSmtTy.trans hLowSmtTy.symm)
      (by rw [hXSmtTy]; intro h; cases h)
  have hTailBool :
      RuleProofs.eo_has_bool_type
        (bvZeroExtendEqConstAnd
          (bvSignExtendEqConstLower x c
            (Term.Numeral (native_zplus W A)) (Term.Numeral L))
          (Term.Boolean true)) := by
    unfold bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hLowerBool RuleProofs.eo_has_bool_type_true
  have hRhsBool :
      RuleProofs.eo_has_bool_type
        (bvSignExtendEqConstRhs x (Term.Numeral A) c
          (Term.Numeral (native_zplus W A)) (Term.Numeral P)
          (Term.Numeral L) (Term.Numeral H)) := by
    unfold bvSignExtendEqConstRhs bvZeroExtendEqConstAnd
    exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _
      hUpperBool hTailBool
  unfold bvSignExtendEqConst2Term bvZeroExtendEqConstEq
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type _ _
    (hLhsBool.trans hRhsBool.symm)
    (by rw [hLhsBool]; intro h; cases h)

private theorem eval_bvsize_bv_sign_extend_eq_const
    (M : SmtModel) (x : Term) (w : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x)) =
      SmtValue.Numeral w := by
  intro hw0 hXTy
  have hRound := native_int_to_nat_roundtrip w hw0
  have hSize :
      __smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x)) = w := by
    rw [hXTy]
    exact hRound
  change __smtx_model_eval M
      (native_ite
        (native_zleq 0
          (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x))))
        (SmtTerm._at_purify
          (SmtTerm.Numeral
            (__smtx_bv_sizeof_type (__smtx_typeof (__eo_to_smt x)))))
        SmtTerm.None) = SmtValue.Numeral w
  rw [hSize]
  simp [native_ite, hw0, __smtx_model_eval,
    __smtx_model_eval__at_purify]

private theorem eval_width_minus_one_bv_sign_extend_eq_const
    (M : SmtModel) (x : Term) (w : native_Int) :
    native_zleq 0 w = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat w) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
            (Term.Apply (Term.UOp UserOp._at_bvsize) x))
            (Term.Numeral 1))) =
      SmtValue.Numeral (native_zplus w (native_zneg 1)) := by
  intro hw0 hXTy
  change __smtx_model_eval M
      (SmtTerm.neg
        (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
        (SmtTerm.Numeral 1)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only
  rw [eval_bvsize_bv_sign_extend_eq_const M x w hw0 hXTy]
  simp [__smtx_model_eval, __smtx_model_eval__, native_zplus,
    native_zneg]

private theorem bv_sign_extend_eq_const_mp_numeric
    (M : SmtModel) (A P : native_Int) :
    eo_interprets M
      (bvSignExtendEqConstMpPrem (Term.Numeral A) (Term.Numeral P))
      true ->
    P = native_zplus A 1 := by
  intro hPrem
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq (SmtTerm.Numeral P)
            (SmtTerm.plus (SmtTerm.Numeral A)
              (SmtTerm.plus (SmtTerm.Numeral 1) (SmtTerm.Numeral 0)))) =
        SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq] at hEval
      simpa [__smtx_model_eval, __smtx_model_eval_eq,
        __smtx_model_eval__, __smtx_model_eval_plus, native_veq,
        native_zplus] using hEval

private theorem bv_sign_extend_eq_const_nm2_numeric
    (M : SmtModel) (x : Term) (W L : native_Int) :
    native_zleq 0 W = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    eo_interprets M
      (bvZeroExtendUltConstWidthPrem x (Term.Numeral L)) true ->
    L = native_zplus W (native_zneg 1) := by
  intro hW0 hXSmtTy hPrem
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hPrem
  cases hPrem with
  | intro_true _ hEval =>
      change __smtx_model_eval M
          (SmtTerm.eq (SmtTerm.Numeral L)
            (SmtTerm.neg
              (__eo_to_smt (Term.Apply (Term.UOp UserOp._at_bvsize) x))
              (SmtTerm.Numeral 1))) =
        SmtValue.Boolean true at hEval
      rw [smtx_eval_eq_term_eq] at hEval
      change __smtx_model_eval_eq (SmtValue.Numeral L)
          (__smtx_model_eval M
            (__eo_to_smt
              (Term.Apply (Term.Apply (Term.UOp UserOp.neg)
                (Term.Apply (Term.UOp UserOp._at_bvsize) x))
                (Term.Numeral 1)))) =
        SmtValue.Boolean true at hEval
      rw [eval_width_minus_one_bv_sign_extend_eq_const
        M x W hW0 hXSmtTy] at hEval
      simpa [__smtx_model_eval, __smtx_model_eval_eq,
        __smtx_model_eval__, native_veq] using hEval

private theorem eval_sign_extend_term_local
    (M : SmtModel) (x : Term) (a : native_Int) :
    __smtx_model_eval M
        (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral a))) =
      __smtx_model_eval_sign_extend (SmtValue.Numeral a)
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M
      (SmtTerm.sign_extend (SmtTerm.Numeral a) (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp [__smtx_model_eval]

private theorem eval_bvnot_term_local (M : SmtModel) (x : Term) :
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.bvnot) x)) =
      __smtx_model_eval_bvnot
        (__smtx_model_eval M (__eo_to_smt x)) := by
  change __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt x)) = _
  rw [__smtx_model_eval.eq_def] <;> simp only

private theorem eval_sign_extend_eq_characterization_rev
    (x : BitVec W) (c : BitVec (W + A)) (hW : 0 < W) :
    __smtx_model_eval_eq
        (SmtValue.Binary (↑(W + A) : Int) (↑c.toNat : Int))
        (SmtValue.Binary (↑(W + A) : Int)
          (↑(x.signExtend (W + A)).toNat : Int)) =
      __smtx_model_eval_and
        (__smtx_model_eval_or
          (__smtx_model_eval_eq
            (SmtValue.Binary (↑(A + 1) : Int)
              (↑(c.extractLsb' (W - 1) (A + 1)).toNat : Int))
            (SmtValue.Binary (↑(A + 1) : Int)
              (↑(0#(A + 1)).toNat : Int)))
          (__smtx_model_eval_or
            (__smtx_model_eval_eq
              (SmtValue.Binary (↑(A + 1) : Int)
                (↑(c.extractLsb' (W - 1) (A + 1)).toNat : Int))
              (__smtx_model_eval_bvnot
                (SmtValue.Binary (↑(A + 1) : Int) 0)))
            (SmtValue.Boolean false)))
        (__smtx_model_eval_and
          (__smtx_model_eval_eq
            (SmtValue.Binary (↑W : Int) (↑x.toNat : Int))
            (SmtValue.Binary (↑W : Int)
              (↑(c.extractLsb' 0 W).toNat : Int)))
          (SmtValue.Boolean true)) := by
  rw [smt_eval_eq_bitvec_values]
  have hDec :
      decide (c = x.signExtend (W + A)) =
        decide (x.signExtend (W + A) = c) := by
    by_cases h : c = x.signExtend (W + A)
    · subst c
      simp
    · have h' : x.signExtend (W + A) ≠ c := by
        intro hc
        exact h hc.symm
      simp [h, h']
  rw [hDec]
  rw [← smt_eval_eq_bitvec_values (x.signExtend (W + A)) c]
  exact eval_sign_extend_eq_characterization x c hW

private theorem eval_bv_sign_extend_eq_const_1_lhs_eq_rhs
    (M : SmtModel) (hM : model_total_typed M)
    (x c : Term) (W A P L H : native_Int) :
    native_zleq 0 W = true ->
    native_zleq 0 A = true ->
    native_zleq 0 P = true ->
    native_zleq 0 L = true ->
    native_zplus L 1 = W ->
    native_zplus (native_zplus H 1) (native_zneg L) = P ->
    P = native_zplus A 1 ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendEqConstRhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)) (Term.Numeral P)
            (Term.Numeral L) (Term.Numeral H))) := by
  intro hW0 hA0 hP0 hL0 hLWidth hHWidth hMp hXSmtTy hConstSmtTy
  have hWNonneg : (0 : Int) ≤ W := by
    simpa [SmtEval.native_zleq] using hW0
  have hANonneg : (0 : Int) ≤ A := by
    simpa [SmtEval.native_zleq] using hA0
  have hPNonneg : (0 : Int) ≤ P := by
    simpa [SmtEval.native_zleq] using hP0
  have hLNonneg : (0 : Int) ≤ L := by
    simpa [SmtEval.native_zleq] using hL0
  have hLWidthInt : L + 1 = W := by
    simpa [SmtEval.native_zplus] using hLWidth
  have hHWidthInt : H + 1 + -L = P := by
    simpa [SmtEval.native_zplus, SmtEval.native_zneg] using hHWidth
  have hMpInt : P = A + 1 := by
    simpa [SmtEval.native_zplus] using hMp
  have hWPosInt : (0 : Int) < W := by
    rw [← hLWidthInt]
    omega
  let WN : Nat := native_int_to_nat W
  let AN : Nat := native_int_to_nat A
  have hWCast : (↑WN : Int) = W := by
    have h := native_int_to_nat_roundtrip W hW0
    simpa [WN, SmtEval.native_nat_to_int, native_nat_to_int] using h
  have hACast : (↑AN : Int) = A := by
    have h := native_int_to_nat_roundtrip A hA0
    simpa [AN, SmtEval.native_nat_to_int, native_nat_to_int] using h
  have hWNatPos : 0 < WN := by
    apply Int.ofNat_lt.mp
    change (0 : Int) < (↑WN : Int)
    rw [hWCast]
    exact hWPosInt
  have hWide0 : native_zleq 0 (native_zplus W A) = true := by
    have hwa : (0 : Int) ≤ W + A := by omega
    simpa [SmtEval.native_zleq, SmtEval.native_zplus] using hwa
  have hWideNat :
      native_int_to_nat (native_zplus W A) = WN + AN := by
    apply Int.ofNat.inj
    have h := native_int_to_nat_roundtrip (native_zplus W A) hWide0
    simpa [SmtEval.native_nat_to_int, native_nat_to_int,
      SmtEval.native_zplus, WN, AN, hWCast, hACast] using h
  have hPCastA1 : P = (↑(AN + 1) : Int) := by
    calc
      P = A + 1 := hMpInt
      _ = (↑(AN + 1) : Int) := by
        rw [← hACast]
        norm_cast
  have hLowStart : (0 : Int) = (↑(0 : Nat) : Int) := rfl
  have hLowLen : L + 1 + -0 = (↑WN : Int) := by
    simpa using hLWidthInt.trans hWCast.symm
  have hHighStart : L = (↑(WN - 1) : Int) := by
    calc
      L = W - 1 := by
        rw [← hLWidthInt]
        simp
      _ = (↑WN : Int) - 1 := by rw [← hWCast]
      _ = (↑(WN - 1) : Int) :=
          (Int.ofNat_sub (by omega : 1 ≤ WN)).symm
  have hHighLen : H + 1 + -L = (↑(AN + 1) : Int) := by
    calc
      H + 1 + -L = P := hHWidthInt
      _ = (↑(AN + 1) : Int) := hPCastA1
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) WN
      (by simpa [WN] using hXSmtTy) with
    ⟨px, hXEval, hXCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑WN : Int) px := by
    simpa [SmtEval.native_nat_to_int, native_nat_to_int] using hXEval
  have hXRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int WN) (n := px)
    (by simp [SmtEval.native_zleq, SmtEval.native_nat_to_int,
      native_nat_to_int]) hXCan
  have hPx0 : (0 : Int) ≤ px := hXRange.1
  have hPx1 : px < (2 : Int) ^ WN := by
    simpa [natpow2_eq, SmtEval.native_nat_to_int, native_nat_to_int]
      using hXRange.2
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A)))) (WN + AN)
      (by simpa [hWideNat] using hConstSmtTy) with
    ⟨pc, hConstEval, hConstCan⟩
  have hConstEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (↑(WN + AN) : Int) pc := by
    simpa [SmtEval.native_nat_to_int, native_nat_to_int] using hConstEval
  have hConstRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int (WN + AN)) (n := pc)
    (by
      have hnn : (0 : Int) ≤ (↑(WN + AN) : Int) :=
        Int.natCast_nonneg _
      simpa [SmtEval.native_zleq, SmtEval.native_nat_to_int,
        native_nat_to_int] using hnn) hConstCan
  have hPc0 : (0 : Int) ≤ pc := hConstRange.1
  have hPc1 : pc < (2 : Int) ^ (WN + AN) := by
    simpa [natpow2_eq, SmtEval.native_nat_to_int, native_nat_to_int]
      using hConstRange.2
  let xBV : BitVec WN := BitVec.ofInt WN px
  let cBV : BitVec (WN + AN) := BitVec.ofInt (WN + AN) pc
  have hXPayload : (↑xBV.toNat : Int) = px := by
    have hToNat := ofInt_toNat_canonical WN px hPx0 hPx1
    simp [xBV, hToNat, Int.toNat_of_nonneg hPx0]
  have hConstPayload : (↑cBV.toNat : Int) = pc := by
    have hToNat := ofInt_toNat_canonical (WN + AN) pc hPc0 hPc1
    simp [cBV, hToNat, Int.toNat_of_nonneg hPc0]
  have hXEvalBV :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑WN : Int) (↑xBV.toNat : Int) := by
    rw [hXEval']
    rw [hXPayload]
  have hConstEvalBV :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (↑(WN + AN) : Int) (↑cBV.toNat : Int) := by
    rw [hConstEval']
    rw [hConstPayload]
  have hSignEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtValue.Binary (↑(WN + AN) : Int)
          (↑(xBV.signExtend (WN + AN)).toNat : Int) := by
    rw [eval_sign_extend_term_local, hXEval']
    rw [← hACast]
    rw [sign_extend_val_bitvec WN AN px hPx0 hPx1]
    rw [Nat.add_comm AN WN]
  have hLowExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        SmtValue.Binary (↑WN : Int)
          (↑(cBV.extractLsb' 0 WN).toNat : Int) := by
    unfold bvZeroExtendUltConstLow
    change __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))
            (Term.Numeral L) (Term.Numeral 0))) = _
    rw [eval_extract_term, hConstEval']
    rw [extract_val_bitvec_start_len (WN + AN) 0 WN pc L 0
      hPc0 hPc1 hLowStart hLowLen]
  have hHighExtractEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H))) =
        SmtValue.Binary (↑(AN + 1) : Int)
          (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int) := by
    unfold bvSignExtendEqConstHigh bvZeroExtendEqConstHigh
    change __smtx_model_eval M
        (__eo_to_smt
          (bvExtractTerm
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))
            (Term.Numeral H) (Term.Numeral L))) = _
    rw [eval_extract_term, hConstEval']
    rw [extract_val_bitvec_start_len (WN + AN) (WN - 1) (AN + 1)
      pc H L hPc0 hPc1 hHighStart hHighLen]
  have hZeroEval :
      __smtx_model_eval M
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P))) =
        SmtValue.Binary (↑(AN + 1) : Int)
          (↑(0#(AN + 1)).toNat : Int) := by
    unfold bvSignExtendEqConstZero bvZeroExtendUltConstConst
    change __smtx_model_eval M
        (SmtTerm.int_to_bv (SmtTerm.Numeral P) (SmtTerm.Numeral 0)) = _
    rw [hPCastA1]
    have hMod0 :
        native_mod_total 0
            (native_int_pow2 ((↑AN : Int) + 1)) = 0 := by
      simp [native_mod_total]
    simp [smtx_eval_int_to_bv_numerals, hMod0]
  have hNotZeroEval :
      __smtx_model_eval M
          (__eo_to_smt (bvSignExtendEqConstNotZero (Term.Numeral P))) =
        __smtx_model_eval_bvnot
          (SmtValue.Binary (↑(AN + 1) : Int) 0) := by
    unfold bvSignExtendEqConstNotZero
    rw [eval_bvnot_term_local, hZeroEval]
    simp
  have hLhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑(xBV.signExtend (WN + AN)).toNat : Int))
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑cBV.toNat : Int)) := by
    unfold bvSignExtendEqConst1Lhs bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral A)))
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A))))) = _
    rw [smtx_eval_eq_term_eq, hSignEval, hConstEvalBV]
  have hUpperZeroEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstUpperZero (Term.Numeral P) c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(AN + 1) : Int)
            (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int))
          (SmtValue.Binary (↑(AN + 1) : Int)
            (↑(0#(AN + 1)).toNat : Int)) := by
    unfold bvSignExtendEqConstUpperZero bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H)))
          (__eo_to_smt (bvSignExtendEqConstZero (Term.Numeral P)))) = _
    rw [smtx_eval_eq_term_eq, hHighExtractEval, hZeroEval]
  have hUpperOnesEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(AN + 1) : Int)
            (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int))
          (__smtx_model_eval_bvnot
            (SmtValue.Binary (↑(AN + 1) : Int) 0)) := by
    unfold bvSignExtendEqConstUpperOnes bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvSignExtendEqConstHigh c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)
              (Term.Numeral H)))
          (__eo_to_smt (bvSignExtendEqConstNotZero (Term.Numeral P)))) = _
    rw [smtx_eval_eq_term_eq, hHighExtractEval, hNotZeroEval]
  have hLowerEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstLower x c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑WN : Int) (↑xBV.toNat : Int))
          (SmtValue.Binary (↑WN : Int)
            (↑(cBV.extractLsb' 0 WN).toNat : Int)) := by
    unfold bvSignExtendEqConstLower bvZeroExtendEqConstLower
      bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq (__eo_to_smt x)
          (__eo_to_smt
            (bvZeroExtendUltConstLow c
              (Term.Numeral (native_zplus W A)) (Term.Numeral L)))) = _
    rw [smtx_eval_eq_term_eq, hXEvalBV, hLowExtractEval]
  have hRhsEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstRhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)) (Term.Numeral P)
              (Term.Numeral L) (Term.Numeral H))) =
        __smtx_model_eval_and
          (__smtx_model_eval_or
            (__smtx_model_eval_eq
              (SmtValue.Binary (↑(AN + 1) : Int)
                (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int))
              (SmtValue.Binary (↑(AN + 1) : Int)
                (↑(0#(AN + 1)).toNat : Int)))
            (__smtx_model_eval_or
              (__smtx_model_eval_eq
                (SmtValue.Binary (↑(AN + 1) : Int)
                  (↑(cBV.extractLsb' (WN - 1) (AN + 1)).toNat : Int))
                (__smtx_model_eval_bvnot
                  (SmtValue.Binary (↑(AN + 1) : Int) 0)))
              (SmtValue.Boolean false)))
          (__smtx_model_eval_and
            (__smtx_model_eval_eq
              (SmtValue.Binary (↑WN : Int) (↑xBV.toNat : Int))
              (SmtValue.Binary (↑WN : Int)
                (↑(cBV.extractLsb' 0 WN).toNat : Int)))
            (SmtValue.Boolean true)) := by
    unfold bvSignExtendEqConstRhs bvZeroExtendEqConstAnd
      bvSignExtendEqConstUpper bvSignExtendEqConstOr
    change __smtx_model_eval M
        (SmtTerm.and
          (SmtTerm.or
            (__eo_to_smt
              (bvSignExtendEqConstUpperZero (Term.Numeral P) c
                (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                (Term.Numeral H)))
            (SmtTerm.or
              (__eo_to_smt
                (bvSignExtendEqConstUpperOnes (Term.Numeral P) c
                  (Term.Numeral (native_zplus W A)) (Term.Numeral L)
                  (Term.Numeral H)))
              (SmtTerm.Boolean false)))
          (SmtTerm.and
            (__eo_to_smt
              (bvSignExtendEqConstLower x c
                (Term.Numeral (native_zplus W A)) (Term.Numeral L)))
            (SmtTerm.Boolean true))) = _
    rw [smtx_eval_and_term_eq, smtx_eval_or_term_eq,
      smtx_eval_or_term_eq, smtx_eval_and_term_eq]
    rw [hUpperZeroEval, hUpperOnesEval, hLowerEval]
    simp [__smtx_model_eval]
  rw [hLhsEval, hRhsEval]
  exact eval_sign_extend_eq_characterization xBV cBV hWNatPos

private theorem facts_bv_sign_extend_eq_const_1_term
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    eo_interprets M (bvSignExtendEqConstMpPrem m mp) true ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true ->
    eo_interprets M
      (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
    hMpPrem _hWidthPrem _hNmm1Prem
  have hTermBool :=
    typed_bv_sign_extend_eq_const_1_term x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_1_context x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy with
    ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl, hW0, hA0, hP0,
      hL0, hLWidth, hHWidth, hXSmtTy, hConstSmtTy, _hLowSmtTy,
      _hSignSmtTy, _hHighSmtTy, _hZeroSmtTy, _hNotZeroSmtTy⟩
  have hMpEq := bv_sign_extend_eq_const_mp_numeric M A P hMpPrem
  have hEvalEq :=
    eval_bv_sign_extend_eq_const_1_lhs_eq_rhs M hM x c W A P L H
      hW0 hA0 hP0 hL0 hLWidth hHWidth hMpEq hXSmtTy hConstSmtTy
  refine RuleProofs.eo_interprets_eq_of_rel M
    (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
      (Term.Numeral (native_zplus W A)))
    (bvSignExtendEqConstRhs x (Term.Numeral A) c
      (Term.Numeral (native_zplus W A)) (Term.Numeral P)
      (Term.Numeral L) (Term.Numeral H)) ?_ ?_
  · simpa [bvSignExtendEqConst1Term, bvZeroExtendEqConstEq] using hTermBool
  · rw [hEvalEq]
    exact RuleProofs.smt_value_rel_refl _

private theorem eval_bv_sign_extend_eq_const_2_lhs_eq_1_lhs
    (M : SmtModel) (hM : model_total_typed M)
    (x c : Term) (W A : native_Int) :
    native_zleq 0 W = true ->
    native_zleq 0 A = true ->
    __smtx_typeof (__eo_to_smt x) =
      SmtType.BitVec (native_int_to_nat W) ->
    __smtx_typeof
        (__eo_to_smt
          (bvZeroExtendUltConstConst c
            (Term.Numeral (native_zplus W A)))) =
      SmtType.BitVec (native_int_to_nat (native_zplus W A)) ->
    __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendEqConst2Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) =
      __smtx_model_eval M
        (__eo_to_smt
          (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
            (Term.Numeral (native_zplus W A)))) := by
  intro hW0 hA0 hXSmtTy hConstSmtTy
  let WN : Nat := native_int_to_nat W
  let AN : Nat := native_int_to_nat A
  have hWCast : (↑WN : Int) = W := by
    have h := native_int_to_nat_roundtrip W hW0
    simpa [WN, SmtEval.native_nat_to_int, native_nat_to_int] using h
  have hACast : (↑AN : Int) = A := by
    have h := native_int_to_nat_roundtrip A hA0
    simpa [AN, SmtEval.native_nat_to_int, native_nat_to_int] using h
  have hWide0 : native_zleq 0 (native_zplus W A) = true := by
    have hWNonneg : (0 : Int) ≤ W := by
      simpa [SmtEval.native_zleq] using hW0
    have hANonneg : (0 : Int) ≤ A := by
      simpa [SmtEval.native_zleq] using hA0
    have hwa : (0 : Int) ≤ W + A := by omega
    simpa [SmtEval.native_zleq, SmtEval.native_zplus] using hwa
  have hWideNat :
      native_int_to_nat (native_zplus W A) = WN + AN := by
    apply Int.ofNat.inj
    have h := native_int_to_nat_roundtrip (native_zplus W A) hWide0
    simpa [SmtEval.native_nat_to_int, native_nat_to_int,
      SmtEval.native_zplus, WN, AN, hWCast, hACast] using h
  rcases smt_eval_binary_of_smt_type_bitvec M hM (__eo_to_smt x) WN
      (by simpa [WN] using hXSmtTy) with
    ⟨px, hXEval, hXCan⟩
  have hXEval' :
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (↑WN : Int) px := by
    simpa [SmtEval.native_nat_to_int, native_nat_to_int] using hXEval
  have hXRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int WN) (n := px)
    (by simp [SmtEval.native_zleq, SmtEval.native_nat_to_int,
      native_nat_to_int]) hXCan
  have hPx0 : (0 : Int) ≤ px := hXRange.1
  have hPx1 : px < (2 : Int) ^ WN := by
    simpa [natpow2_eq, SmtEval.native_nat_to_int, native_nat_to_int]
      using hXRange.2
  rcases smt_eval_binary_of_smt_type_bitvec M hM
      (__eo_to_smt
        (bvZeroExtendUltConstConst c
          (Term.Numeral (native_zplus W A)))) (WN + AN)
      (by simpa [hWideNat] using hConstSmtTy) with
    ⟨pc, hConstEval, hConstCan⟩
  have hConstEval' :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (↑(WN + AN) : Int) pc := by
    simpa [SmtEval.native_nat_to_int, native_nat_to_int] using hConstEval
  have hConstRange := bitvec_payload_range_of_canonical
    (w := native_nat_to_int (WN + AN)) (n := pc)
    (by
      have hnn : (0 : Int) ≤ (↑(WN + AN) : Int) :=
        Int.natCast_nonneg _
      simpa [SmtEval.native_zleq, SmtEval.native_nat_to_int,
        native_nat_to_int] using hnn) hConstCan
  have hPc0 : (0 : Int) ≤ pc := hConstRange.1
  have hPc1 : pc < (2 : Int) ^ (WN + AN) := by
    simpa [natpow2_eq, SmtEval.native_nat_to_int, native_nat_to_int]
      using hConstRange.2
  let xBV : BitVec WN := BitVec.ofInt WN px
  let cBV : BitVec (WN + AN) := BitVec.ofInt (WN + AN) pc
  have hXPayload : (↑xBV.toNat : Int) = px := by
    have hToNat := ofInt_toNat_canonical WN px hPx0 hPx1
    simp [xBV, hToNat, Int.toNat_of_nonneg hPx0]
  have hConstPayload : (↑cBV.toNat : Int) = pc := by
    have hToNat := ofInt_toNat_canonical (WN + AN) pc hPc0 hPc1
    simp [cBV, hToNat, Int.toNat_of_nonneg hPc0]
  have hConstEvalBV :
      __smtx_model_eval M
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A)))) =
        SmtValue.Binary (↑(WN + AN) : Int) (↑cBV.toNat : Int) := by
    rw [hConstEval']
    rw [hConstPayload]
  have hSignEval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConstSign x (Term.Numeral A))) =
        SmtValue.Binary (↑(WN + AN) : Int)
          (↑(xBV.signExtend (WN + AN)).toNat : Int) := by
    rw [eval_sign_extend_term_local, hXEval']
    rw [← hACast]
    rw [sign_extend_val_bitvec WN AN px hPx0 hPx1]
    rw [Nat.add_comm AN WN]
  have hLhs1Eval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConst1Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑(xBV.signExtend (WN + AN)).toNat : Int))
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑cBV.toNat : Int)) := by
    unfold bvSignExtendEqConst1Lhs bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral A)))
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A))))) = _
    rw [smtx_eval_eq_term_eq, hSignEval, hConstEvalBV]
  have hLhs2Eval :
      __smtx_model_eval M
          (__eo_to_smt
            (bvSignExtendEqConst2Lhs x (Term.Numeral A) c
              (Term.Numeral (native_zplus W A)))) =
        __smtx_model_eval_eq
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑cBV.toNat : Int))
          (SmtValue.Binary (↑(WN + AN) : Int)
            (↑(xBV.signExtend (WN + AN)).toNat : Int)) := by
    unfold bvSignExtendEqConst2Lhs bvZeroExtendEqConstEq
    change __smtx_model_eval M
        (SmtTerm.eq
          (__eo_to_smt
            (bvZeroExtendUltConstConst c
              (Term.Numeral (native_zplus W A))))
          (__eo_to_smt (bvSignExtendEqConstSign x (Term.Numeral A)))) = _
    rw [smtx_eval_eq_term_eq, hSignEval, hConstEvalBV]
  rw [hLhs1Eval, hLhs2Eval]
  rw [smt_eval_eq_bitvec_values, smt_eval_eq_bitvec_values]
  have hDec :
      decide (cBV = xBV.signExtend (WN + AN)) =
        decide (xBV.signExtend (WN + AN) = cBV) := by
    rw [decide_eq_decide]
    exact ⟨fun h => h.symm, fun h => h.symm⟩
  rw [hDec]

private theorem facts_bv_sign_extend_eq_const_2_term
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm mp nm2 nmm1 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
      Term.Bool ->
    eo_interprets M (bvSignExtendEqConstMpPrem m mp) true ->
    eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true ->
    eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true ->
    eo_interprets M
      (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) true := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
    hMpPrem _hWidthPrem _hNmm1Prem
  have hTermBool :=
    typed_bv_sign_extend_eq_const_2_term x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy
  rcases bv_sign_extend_eq_const_2_context x m c nm mp nm2 nmm1
      hXTrans hMTrans hCTrans hNmTrans hMpTrans hResultTy with
    ⟨W, A, P, L, H, rfl, rfl, rfl, rfl, rfl, hW0, hA0, hP0,
      hL0, hLWidth, hHWidth, hXSmtTy, hConstSmtTy, _hLowSmtTy,
      _hSignSmtTy, _hHighSmtTy, _hZeroSmtTy, _hNotZeroSmtTy⟩
  have hMpEq := bv_sign_extend_eq_const_mp_numeric M A P hMpPrem
  have hEvalEq1 :=
    eval_bv_sign_extend_eq_const_1_lhs_eq_rhs M hM x c W A P L H
      hW0 hA0 hP0 hL0 hLWidth hHWidth hMpEq hXSmtTy hConstSmtTy
  have hEvalLhs :=
    eval_bv_sign_extend_eq_const_2_lhs_eq_1_lhs M hM x c W A
      hW0 hA0 hXSmtTy hConstSmtTy
  refine RuleProofs.eo_interprets_eq_of_rel M
    (bvSignExtendEqConst2Lhs x (Term.Numeral A) c
      (Term.Numeral (native_zplus W A)))
    (bvSignExtendEqConstRhs x (Term.Numeral A) c
      (Term.Numeral (native_zplus W A)) (Term.Numeral P)
      (Term.Numeral L) (Term.Numeral H)) ?_ ?_
  · simpa [bvSignExtendEqConst2Term, bvZeroExtendEqConstEq] using hTermBool
  · rw [hEvalLhs, hEvalEq1]
    exact RuleProofs.smt_value_rel_refl _

def bvSignExtendEqConst1Program
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_sign_extend_eq_const_1 x m c nm mp nm2 nmm1
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private def bvSignExtendEqConstGuard
    (x m nm mp nm2 nmm1 mpRef mRef nm2Ref xRef nmm1Ref nmRef :
      Term) : Term :=
  __eo_and
    (__eo_and
      (__eo_and
        (__eo_and
          (__eo_and (__eo_eq mp mpRef) (__eo_eq m mRef))
          (__eo_eq nm2 nm2Ref))
        (__eo_eq x xRef))
      (__eo_eq nmm1 nmm1Ref))
    (__eo_eq nm nmRef)

private theorem bv_sign_extend_eq_const_guard_refs
    {x m nm mp nm2 nmm1 mpRef mRef nm2Ref xRef nmm1Ref nmRef body :
      Term} :
    __eo_requires
        (bvSignExtendEqConstGuard x m nm mp nm2 nmm1 mpRef mRef
          nm2Ref xRef nmm1Ref nmRef)
        (Term.Boolean true) body ≠ Term.Stuck ->
    mpRef = mp ∧ mRef = m ∧ nm2Ref = nm2 ∧ xRef = x ∧
      nmm1Ref = nmm1 ∧ nmRef = nm := by
  intro hReq
  have hGuard := bv_extract_support_requires_guard hReq
  unfold bvSignExtendEqConstGuard at hGuard
  rcases bv_extract_support_and_true hGuard with ⟨hG5, hNm⟩
  rcases bv_extract_support_and_true hG5 with ⟨hG4, hNmm1⟩
  rcases bv_extract_support_and_true hG4 with ⟨hG3, hX⟩
  rcases bv_extract_support_and_true hG3 with ⟨hG2, hNm2⟩
  rcases bv_extract_support_and_true hG2 with ⟨hMp, hM⟩
  exact ⟨(bv_extract_support_eq_true hMp).symm,
    (bv_extract_support_eq_true hM).symm,
    (bv_extract_support_eq_true hNm2).symm,
    (bv_extract_support_eq_true hX).symm,
    (bv_extract_support_eq_true hNmm1).symm,
    (bv_extract_support_eq_true hNm).symm⟩

private theorem bv_sign_extend_eq_const_1_premise_shape
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> mp ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    nmm1 ≠ Term.Stuck ->
    bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3 ≠
      Term.Stuck ->
    ∃ mpRef mRef nm2Ref xRef nmm1Ref nmRef,
      P1 = bvSignExtendEqConstMpPrem mRef mpRef ∧
      P2 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
      P3 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref := by
  intro hX hM hC hNm hMp hNm2 hNmm1 hProg
  by_cases hShape :
      ∃ mpRef mRef nm2Ref xRef nmm1Ref nmRef,
        P1 = bvSignExtendEqConstMpPrem mRef mpRef ∧
        P2 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
        P3 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_sign_extend_eq_const_1.eq_9
      x m c nm mp nm2 nmm1 (Proof.pf P1) (Proof.pf P2)
      (Proof.pf P3)
      hX hM hC hNm hMp hNm2 hNmm1 (by
        intro mpRef mRef nm2Ref xRef nmm1Ref nmRef hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨mpRef, mRef, nm2Ref, xRef, nmm1Ref, nmRef, rfl, rfl, rfl⟩)

private theorem bv_sign_extend_eq_const_1_program_canonical
    (x m c nm mp nm2 nmm1 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> mp ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    nmm1 ≠ Term.Stuck ->
    bvSignExtendEqConst1Program x m c nm mp nm2 nmm1
        (bvSignExtendEqConstMpPrem m mp)
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendEqConstNmm1Prem nm nmm1) =
      bvSignExtendEqConst1Term x m c nm mp nm2 nmm1 := by
  intro hX hM hC hNm hMp hNm2 hNmm1
  unfold bvSignExtendEqConst1Program bvSignExtendEqConstMpPrem
    bvZeroExtendUltConstWidthPrem bvZeroExtendEqConstNmm1Prem
    bvZeroExtendUltConstBvsize
  rw [__eo_prog_bv_sign_extend_eq_const_1.eq_8
    x m c nm mp nm2 nmm1 mp m nm2 x nmm1 nm
    hX hM hC hNm hMp hNm2 hNmm1]
  simp [bvSignExtendEqConstGuard, bvSignExtendEqConst1Term,
    bvSignExtendEqConst1Lhs, bvSignExtendEqConstRhs,
    bvSignExtendEqConstSign, bvSignExtendEqConstUpper,
    bvSignExtendEqConstUpperZero, bvSignExtendEqConstUpperOnes,
    bvSignExtendEqConstOr, bvSignExtendEqConstLower,
    bvSignExtendEqConstHigh, bvSignExtendEqConstZero,
    bvSignExtendEqConstNotZero, bvZeroExtendEqConstEq,
    bvZeroExtendEqConstAnd, bvZeroExtendEqConstHigh,
    bvZeroExtendEqConstLower, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hMp, hNm2, hNmm1]

private theorem bvSignExtendEqConst1Program_normalize
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3 ≠
      Term.Stuck ->
    P1 = bvSignExtendEqConstMpPrem m mp ∧
      P2 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P3 = bvZeroExtendEqConstNmm1Prem nm nmm1 ∧
      bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3 =
        bvSignExtendEqConst1Term x m c nm mp nm2 nmm1 := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
    hNmm1Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hMp := RuleProofs.term_ne_stuck_of_has_smt_translation mp hMpTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  have hNmm1 :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nmm1 hNmm1Trans
  rcases bv_sign_extend_eq_const_1_premise_shape
      x m c nm mp nm2 nmm1 P1 P2 P3 hX hM hC hNm hMp hNm2
      hNmm1 hProg with
    ⟨mpRef, mRef, nm2Ref, xRef, nmm1Ref, nmRef, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvSignExtendEqConst1Program bvSignExtendEqConstMpPrem
    bvZeroExtendUltConstWidthPrem bvZeroExtendEqConstNmm1Prem
    bvZeroExtendUltConstBvsize at hReq
  rw [__eo_prog_bv_sign_extend_eq_const_1.eq_8
    x m c nm mp nm2 nmm1 mpRef mRef nm2Ref xRef nmm1Ref nmRef
    hX hM hC hNm hMp hNm2 hNmm1] at hReq
  rcases bv_sign_extend_eq_const_guard_refs
      (by simpa [bvSignExtendEqConstGuard] using hReq) with
    ⟨hMpRef, hMRef, hNm2Ref, hXRef, hNmm1Ref, hNmRef⟩
  subst mpRef
  subst mRef
  subst nm2Ref
  subst xRef
  subst nmm1Ref
  subst nmRef
  have hP1Canonical : P1 = bvSignExtendEqConstMpPrem m mp := hP1
  have hP2Canonical : P2 = bvZeroExtendUltConstWidthPrem x nm2 := hP2
  have hP3Canonical : P3 = bvZeroExtendEqConstNmm1Prem nm nmm1 := hP3
  refine ⟨hP1Canonical, hP2Canonical, hP3Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical, hP3Canonical]
  exact bv_sign_extend_eq_const_1_program_canonical
    x m c nm mp nm2 nmm1 hX hM hC hNm hMp hNm2 hNmm1

theorem typed_bv_sign_extend_eq_const_1_program
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans hNmm1Trans
    hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendEqConst1Program_normalize x m c nm mp nm2 nmm1
      P1 P2 P3 hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
      hNmm1Trans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_sign_extend_eq_const_1_term x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hTermTy

theorem facts_bv_sign_extend_eq_const_1_program
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M
      (bvSignExtendEqConst1Program x m c nm mp nm2 nmm1 P1 P2 P3)
      true := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans hNmm1Trans
    hResultTy hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendEqConst1Program_normalize x m c nm mp nm2 nmm1
      P1 P2 P3 hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
      hNmm1Trans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendEqConst1Term x m c nm mp nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hMpPrem :
      eo_interprets M (bvSignExtendEqConstMpPrem m mp) true := by
    simpa [hP1] using hP1True
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP2] using hP2True
  have hNmm1Prem :
      eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_sign_extend_eq_const_1_term M hM x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hTermTy
    hMpPrem hWidthPrem hNmm1Prem

def bvSignExtendEqConst2Program
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) : Term :=
  __eo_prog_bv_sign_extend_eq_const_2 x m c nm mp nm2 nmm1
    (Proof.pf P1) (Proof.pf P2) (Proof.pf P3)

private theorem bv_sign_extend_eq_const_2_premise_shape
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> mp ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    nmm1 ≠ Term.Stuck ->
    bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3 ≠
      Term.Stuck ->
    ∃ mpRef mRef nm2Ref xRef nmm1Ref nmRef,
      P1 = bvSignExtendEqConstMpPrem mRef mpRef ∧
      P2 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
      P3 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref := by
  intro hX hM hC hNm hMp hNm2 hNmm1 hProg
  by_cases hShape :
      ∃ mpRef mRef nm2Ref xRef nmm1Ref nmRef,
        P1 = bvSignExtendEqConstMpPrem mRef mpRef ∧
        P2 = bvZeroExtendUltConstWidthPrem xRef nm2Ref ∧
        P3 = bvZeroExtendEqConstNmm1Prem nmRef nmm1Ref
  · exact hShape
  · exfalso
    apply hProg
    exact __eo_prog_bv_sign_extend_eq_const_2.eq_9
      x m c nm mp nm2 nmm1 (Proof.pf P1) (Proof.pf P2)
      (Proof.pf P3)
      hX hM hC hNm hMp hNm2 hNmm1 (by
        intro mpRef mRef nm2Ref xRef nmm1Ref nmRef hP1 hP2 hP3
        cases hP1
        cases hP2
        cases hP3
        exact hShape
          ⟨mpRef, mRef, nm2Ref, xRef, nmm1Ref, nmRef, rfl, rfl, rfl⟩)

private theorem bv_sign_extend_eq_const_2_program_canonical
    (x m c nm mp nm2 nmm1 : Term) :
    x ≠ Term.Stuck -> m ≠ Term.Stuck -> c ≠ Term.Stuck ->
    nm ≠ Term.Stuck -> mp ≠ Term.Stuck -> nm2 ≠ Term.Stuck ->
    nmm1 ≠ Term.Stuck ->
    bvSignExtendEqConst2Program x m c nm mp nm2 nmm1
        (bvSignExtendEqConstMpPrem m mp)
        (bvZeroExtendUltConstWidthPrem x nm2)
        (bvZeroExtendEqConstNmm1Prem nm nmm1) =
      bvSignExtendEqConst2Term x m c nm mp nm2 nmm1 := by
  intro hX hM hC hNm hMp hNm2 hNmm1
  unfold bvSignExtendEqConst2Program bvSignExtendEqConstMpPrem
    bvZeroExtendUltConstWidthPrem bvZeroExtendEqConstNmm1Prem
    bvZeroExtendUltConstBvsize
  rw [__eo_prog_bv_sign_extend_eq_const_2.eq_8
    x m c nm mp nm2 nmm1 mp m nm2 x nmm1 nm
    hX hM hC hNm hMp hNm2 hNmm1]
  simp [bvSignExtendEqConstGuard, bvSignExtendEqConst2Term,
    bvSignExtendEqConst2Lhs, bvSignExtendEqConstRhs,
    bvSignExtendEqConstSign, bvSignExtendEqConstUpper,
    bvSignExtendEqConstUpperZero, bvSignExtendEqConstUpperOnes,
    bvSignExtendEqConstOr, bvSignExtendEqConstLower,
    bvSignExtendEqConstHigh, bvSignExtendEqConstZero,
    bvSignExtendEqConstNotZero, bvZeroExtendEqConstEq,
    bvZeroExtendEqConstAnd, bvZeroExtendEqConstHigh,
    bvZeroExtendEqConstLower, bvZeroExtendUltConstConst,
    bvZeroExtendUltConstLow, bvExtractTerm,
    __eo_requires, __eo_and, __eo_eq, native_ite, native_teq,
    native_not, native_and, hX, hM, hC, hNm, hMp, hNm2, hNmm1]

private theorem bvSignExtendEqConst2Program_normalize
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3 ≠
      Term.Stuck ->
    P1 = bvSignExtendEqConstMpPrem m mp ∧
      P2 = bvZeroExtendUltConstWidthPrem x nm2 ∧
      P3 = bvZeroExtendEqConstNmm1Prem nm nmm1 ∧
      bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3 =
        bvSignExtendEqConst2Term x m c nm mp nm2 nmm1 := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
    hNmm1Trans hProg
  have hX := RuleProofs.term_ne_stuck_of_has_smt_translation x hXTrans
  have hM := RuleProofs.term_ne_stuck_of_has_smt_translation m hMTrans
  have hC := RuleProofs.term_ne_stuck_of_has_smt_translation c hCTrans
  have hNm := RuleProofs.term_ne_stuck_of_has_smt_translation nm hNmTrans
  have hMp := RuleProofs.term_ne_stuck_of_has_smt_translation mp hMpTrans
  have hNm2 := RuleProofs.term_ne_stuck_of_has_smt_translation nm2 hNm2Trans
  have hNmm1 :=
    RuleProofs.term_ne_stuck_of_has_smt_translation nmm1 hNmm1Trans
  rcases bv_sign_extend_eq_const_2_premise_shape
      x m c nm mp nm2 nmm1 P1 P2 P3 hX hM hC hNm hMp hNm2
      hNmm1 hProg with
    ⟨mpRef, mRef, nm2Ref, xRef, nmm1Ref, nmRef, hP1, hP2, hP3⟩
  have hReq := hProg
  rw [hP1, hP2, hP3] at hReq
  unfold bvSignExtendEqConst2Program bvSignExtendEqConstMpPrem
    bvZeroExtendUltConstWidthPrem bvZeroExtendEqConstNmm1Prem
    bvZeroExtendUltConstBvsize at hReq
  rw [__eo_prog_bv_sign_extend_eq_const_2.eq_8
    x m c nm mp nm2 nmm1 mpRef mRef nm2Ref xRef nmm1Ref nmRef
    hX hM hC hNm hMp hNm2 hNmm1] at hReq
  rcases bv_sign_extend_eq_const_guard_refs
      (by simpa [bvSignExtendEqConstGuard] using hReq) with
    ⟨hMpRef, hMRef, hNm2Ref, hXRef, hNmm1Ref, hNmRef⟩
  subst mpRef
  subst mRef
  subst nm2Ref
  subst xRef
  subst nmm1Ref
  subst nmRef
  have hP1Canonical : P1 = bvSignExtendEqConstMpPrem m mp := hP1
  have hP2Canonical : P2 = bvZeroExtendUltConstWidthPrem x nm2 := hP2
  have hP3Canonical : P3 = bvZeroExtendEqConstNmm1Prem nm nmm1 := hP3
  refine ⟨hP1Canonical, hP2Canonical, hP3Canonical, ?_⟩
  rw [hP1Canonical, hP2Canonical, hP3Canonical]
  exact bv_sign_extend_eq_const_2_program_canonical
    x m c nm mp nm2 nmm1 hX hM hC hNm hMp hNm2 hNmm1

theorem typed_bv_sign_extend_eq_const_2_program
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3) =
      Term.Bool ->
    RuleProofs.eo_has_bool_type
      (bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3) := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans hNmm1Trans
    hResultTy
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendEqConst2Program_normalize x m c nm mp nm2 nmm1
      P1 P2 P3 hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
      hNmm1Trans hProg with
    ⟨_hP1, _hP2, _hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  rw [hProgramEq]
  exact typed_bv_sign_extend_eq_const_2_term x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hTermTy

theorem facts_bv_sign_extend_eq_const_2_program
    (M : SmtModel) (hM : model_total_typed M)
    (x m c nm mp nm2 nmm1 P1 P2 P3 : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation m ->
    RuleProofs.eo_has_smt_translation c ->
    RuleProofs.eo_has_smt_translation nm ->
    RuleProofs.eo_has_smt_translation mp ->
    RuleProofs.eo_has_smt_translation nm2 ->
    RuleProofs.eo_has_smt_translation nmm1 ->
    __eo_typeof
        (bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3) =
      Term.Bool ->
    eo_interprets M P1 true -> eo_interprets M P2 true ->
    eo_interprets M P3 true ->
    eo_interprets M
      (bvSignExtendEqConst2Program x m c nm mp nm2 nmm1 P1 P2 P3)
      true := by
  intro hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans hNmm1Trans
    hResultTy hP1True hP2True hP3True
  have hProg := term_ne_stuck_of_typeof_bool hResultTy
  rcases bvSignExtendEqConst2Program_normalize x m c nm mp nm2 nmm1
      P1 P2 P3 hXTrans hMTrans hCTrans hNmTrans hMpTrans hNm2Trans
      hNmm1Trans hProg with
    ⟨hP1, hP2, hP3, hProgramEq⟩
  have hTermTy :
      __eo_typeof (bvSignExtendEqConst2Term x m c nm mp nm2 nmm1) =
        Term.Bool := by
    rw [← hProgramEq]
    exact hResultTy
  have hMpPrem :
      eo_interprets M (bvSignExtendEqConstMpPrem m mp) true := by
    simpa [hP1] using hP1True
  have hWidthPrem :
      eo_interprets M (bvZeroExtendUltConstWidthPrem x nm2) true := by
    simpa [hP2] using hP2True
  have hNmm1Prem :
      eo_interprets M (bvZeroExtendEqConstNmm1Prem nm nmm1) true := by
    simpa [hP3] using hP3True
  rw [hProgramEq]
  exact facts_bv_sign_extend_eq_const_2_term M hM x m c nm mp nm2 nmm1
    hXTrans hMTrans hCTrans hNmTrans hMpTrans hTermTy
    hMpPrem hWidthPrem hNmm1Prem
