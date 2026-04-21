import CpcMini.Proofs.Checker

open Eo
open SmtEval
open Smtm

namespace CpcMini.Examples.TestSimpleCheckerAssumptions

deriving instance DecidableEq for CIndexList, CArgList, CStateObj, CState, CRule, CCmd, CCmdList

def t1 := Term.UConst 1 (Term.UOp UserOp.Int)
def t2 := Term.UConst 2 (Term.UOp UserOp.Int)
def t3 := Term.Apply (Term.UOp UserOp.eq) t2
def t4 := Term.Apply t3 t1
def t5 := Term.Apply (Term.UOp UserOp.eq) t1
def t6 := Term.Apply t5 t2
def t7 := Term.Apply (Term.UOp UserOp.not) t6

def s0 : CState := logos_init_state
def s1 : CState := logos_invoke_assume s0 t4
def s2 : CState := logos_invoke_assume s1 t7

def symmStep : CCmd :=
  CCmd.step CRule.symm CArgList.nil (CIndexList.cons 0 CIndexList.nil)

def contraStep : CCmd :=
  CCmd.step CRule.contra CArgList.nil (CIndexList.cons 2 (CIndexList.cons 0 CIndexList.nil))

def s3 : CState := logos_invoke_cmd s2 symmStep
def s4 : CState := logos_invoke_cmd s3 contraStep

def assumptions : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) t7)
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) t4) (Term.Boolean true))

def proof : CCmdList :=
  CCmdList.cons symmStep (CCmdList.cons contraStep CCmdList.nil)

#eval! decide (__eo_invoke_assume_list CState.nil assumptions = s2)
#eval! decide (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil assumptions) proof = s4)
#eval! __eo_typeof t7
#eval! __eo_to_smt_type (__eo_typeof t7)
#eval! __eo_to_smt t7
#eval! __eo_typeof t4
#eval! __eo_to_smt_type (__eo_typeof t4)
#eval! __eo_to_smt t4
#eval! __eo_checker_is_refutation assumptions proof

private theorem uconst_int_smt_type (i : native_Nat) :
    __smtx_typeof (__eo_to_smt (Term.UConst i (Term.UOp UserOp.Int))) = SmtType.Int := by
  have hInh : native_inhabited_type SmtType.Int = true :=
    (smtx_inhabited_type_eq_true_iff SmtType.Int).2 type_inhabited_int
  have hWf : __smtx_type_wf SmtType.Int = true := by
    simp [__smtx_type_wf, __smtx_type_wf_rec]
  have hNonNone :
      __smtx_typeof (SmtTerm.UConst (native_uconst_id i) SmtType.Int) ≠ SmtType.None := by
    simp [__smtx_typeof, __smtx_typeof_guard_wf, native_ite, hInh, hWf]
  simpa [__eo_to_smt, __eo_to_smt_type] using
    TranslationProofs.smtx_typeof_uconst_of_non_none (native_uconst_id i) SmtType.Int hNonNone

private theorem t4_has_bool_type : RuleProofs.eo_has_bool_type t4 := by
  have h1 : __smtx_typeof (__eo_to_smt t1) = SmtType.Int := by
    simpa [t1] using uconst_int_smt_type 1
  have h2 : __smtx_typeof (__eo_to_smt t2) = SmtType.Int := by
    simpa [t2] using uconst_int_smt_type 2
  simpa [t4, t3] using
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type t2 t1
      (by simpa [h1, h2])
      (by simpa [h2])

private theorem t7_has_bool_type : RuleProofs.eo_has_bool_type t7 := by
  have t6_has_bool_type : RuleProofs.eo_has_bool_type t6 := by
    have hT4 :
        RuleProofs.eo_has_bool_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) t2) t1) := by
      simpa [t4, t3] using t4_has_bool_type
    simpa [t6, t5] using RuleProofs.eo_has_bool_type_eq_symm t2 t1 hT4
  simpa [t7] using RuleProofs.eo_has_bool_type_not_of_bool_arg t6 t6_has_bool_type

example : TypedAssumptionList assumptions := by
  unfold assumptions
  apply TypedAssumptionList.step
  · native_decide
  · native_decide
  · apply TypedAssumptionList.step
    · native_decide
    · native_decide
    · exact TypedAssumptionList.base

example : TranslatableAssumptionList assumptions := by
  unfold assumptions
  apply TranslatableAssumptionList.step
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ t7_has_bool_type
  · apply TranslatableAssumptionList.step
    · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ t4_has_bool_type
    · exact TranslatableAssumptionList.base

example : CmdListTranslationOk proof := by
  apply CmdListTranslationOk.cons
  · simp [symmStep, cmdTranslationOk, cArgListTranslationOk]
  · apply CmdListTranslationOk.cons
    · simp [contraStep, cmdTranslationOk, cArgListTranslationOk]
    · exact CmdListTranslationOk.nil

example : eo_is_refutation assumptions proof := by
  apply eo_is_refutation.intro
  native_decide

end CpcMini.Examples.TestSimpleCheckerAssumptions
