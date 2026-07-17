import Cpc.Proofs.RuleSupport.BvAllOnesCmpSupport
import Cpc.Proofs.RuleSupport.BvExtractSignExtendSupport

/-! Shared support for the two `bv_zero_extend_ult_const` rewrites. -/

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
