module

public import Cpc.Proofs.RuleSupport.CoreSupport
import all Cpc.Proofs.RuleSupport.CoreSupport
public import Cpc.Proofs.TypePreservation.BitVecCmp
import all Cpc.Proofs.TypePreservation.BitVecCmp

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

def bvIte (c t e : Term) : Term :=
  Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) c) t) e

theorem typeof_bvite_args_of_ne_stuck
    (C T E : Term) :
    __eo_typeof_bvite C T E ≠ Term.Stuck ->
      C = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ∧
        T = E ∧ T ≠ Term.Stuck := by
  intro h
  by_cases hT : T = Term.Stuck
  · subst T
    exact False.elim (h (__eo_typeof_bvite.eq_1 C E))
  by_cases hE : E = Term.Stuck
  · subst E
    exact False.elim (h (__eo_typeof_bvite.eq_2 C T hT))
  by_cases hC : C = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)
  · subst C
    rw [__eo_typeof_bvite.eq_3 T E hT hE] at h
    have hCond := support_eo_requires_cond_eq_of_non_stuck h
    have hEq : E = T := support_eq_of_eo_eq_true T E hCond
    exact ⟨rfl, hEq.symm, hT⟩
  · exact False.elim (h (__eo_typeof_bvite.eq_4 C T E hC hT hE))

theorem smt_typeof_binary_one_one :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    native_decide
  simpa using TranslationProofs.smtx_typeof_binary_of_non_none 1 1 hNN

theorem smt_typeof_c1_bitvec_one
    (c1 : Term) :
    RuleProofs.eo_has_smt_translation c1 ->
    __eo_typeof c1 = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1) ->
    __smtx_typeof (__eo_to_smt c1) = SmtType.BitVec 1 := by
  intro hC1Trans hC1Type
  have hSmtType :
      __smtx_typeof (__eo_to_smt c1) =
        __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      c1 (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) (__eo_to_smt c1) rfl
      hC1Trans hC1Type
  simpa [__eo_to_smt_type, SmtEval.native_zleq] using hSmtType

theorem smt_type_eq_of_same_eo_type
    (x y T : Term) :
    RuleProofs.eo_has_smt_translation x ->
    RuleProofs.eo_has_smt_translation y ->
    __eo_typeof x = T ->
    __eo_typeof y = T ->
    __smtx_typeof (__eo_to_smt y) = __smtx_typeof (__eo_to_smt x) := by
  intro hXTrans hYTrans hXType hYType
  have hXSmtType :
      __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type T := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      x T (__eo_to_smt x) rfl hXTrans hXType
  have hYSmtType :
      __smtx_typeof (__eo_to_smt y) = __eo_to_smt_type T := by
    exact RuleProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      y T (__eo_to_smt y) rfl hYTrans hYType
  rw [hYSmtType, hXSmtType]

theorem smt_typeof_bvite_of_smt_types
    (c t e : Term) (T : SmtType) :
    __smtx_typeof (__eo_to_smt c) = SmtType.BitVec 1 ->
    __smtx_typeof (__eo_to_smt t) = T ->
    __smtx_typeof (__eo_to_smt e) = T ->
    __smtx_typeof (__eo_to_smt (bvIte c t e)) = T := by
  intro hC hT hE
  have hCondTy :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt c) (SmtTerm.Binary 1 1)) =
        SmtType.Bool := by
    rw [typeof_eq_eq]
    simp [__smtx_typeof_eq, __smtx_typeof_guard, hC,
      smt_typeof_binary_one_one, native_Teq, native_ite]
  change __smtx_typeof
      (SmtTerm.ite (SmtTerm.eq (__eo_to_smt c) (SmtTerm.Binary 1 1))
        (__eo_to_smt t) (__eo_to_smt e)) = T
  rw [typeof_ite_eq]
  simp [__smtx_typeof_ite, hCondTy, hT, hE, native_Teq, native_ite]
