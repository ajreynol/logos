import CpcMicro.Proofs.Checker

open Eo
open Smtm

namespace CpcMicro.Examples.TestSimpleCheckerAssumptions

deriving instance DecidableEq for CIndexList, CArgList, CStateObj, CState, CRule, CCmd, CCmdList

def t1 := Term.UConst 1 Term.Int
def t2 := Term.UConst 2 Term.Int
def t3 := Term.Apply Term.eq t2
def t4 := Term.Apply t3 t1
def t5 := Term.Apply Term.eq t1
def t6 := Term.Apply t5 t2
def t7 := Term.Apply Term.not t6

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
  Term.Apply (Term.Apply Term.and t7)
    (Term.Apply (Term.Apply Term.and t4) (Term.Boolean true))

def proof : CCmdList :=
  CCmdList.cons symmStep (CCmdList.cons contraStep CCmdList.nil)

#eval decide (__eo_invoke_assume_list CState.nil assumptions = s2)
#eval decide (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil assumptions) proof = s4)
#eval __eo_typeof t7
#eval __eo_to_smt_type (__eo_typeof t7)
#eval __eo_to_smt t7
#eval __eo_typeof t4
#eval __eo_to_smt_type (__eo_typeof t4)
#eval __eo_to_smt t4
#eval __eo_checker_is_refutation assumptions proof

private theorem uconst_int_smt_type (i : eo_lit_Nat) :
    __smtx_typeof (__eo_to_smt (Term.UConst i Term.Int)) = SmtType.Int := by
  have hInh : smt_lit_inhabited_type SmtType.Int = true :=
    (smtx_inhabited_type_eq_true_iff SmtType.Int).2 type_inhabited_int
  have hNonNone :
      __smtx_typeof (SmtTerm.UConst (smt_lit_uconst_id i) SmtType.Int) ≠ SmtType.None := by
    simp [__smtx_typeof, __smtx_typeof_guard_inhabited, smt_lit_ite, hInh]
  simpa [__eo_to_smt, __eo_to_smt_type] using
    TranslationProofs.smtx_typeof_uconst_of_non_none (smt_lit_uconst_id i) SmtType.Int hNonNone

private theorem t4_has_bool_type : RuleProofs.eo_has_bool_type t4 := by
  have h1 : __smtx_typeof (__eo_to_smt t1) = SmtType.Int := by
    simpa [t1] using uconst_int_smt_type 1
  have h2 : __smtx_typeof (__eo_to_smt t2) = SmtType.Int := by
    simpa [t2] using uconst_int_smt_type 2
  apply RuleProofs.eo_has_bool_type_eq_of_same_smt_type
  · simp [h1, h2]
  · simp [h2]

private theorem t7_has_bool_type : RuleProofs.eo_has_bool_type t7 := by
  exact RuleProofs.eo_has_bool_type_not_of_bool_arg t4 t4_has_bool_type

example : TypedAssumptionList assumptions := by
  apply TypedAssumptionList.step
  · native_decide
  · native_decide
  · apply TypedAssumptionList.step
    · native_decide
    · native_decide
    · exact TypedAssumptionList.base

example : TranslatableAssumptionList assumptions := by
  apply TranslatableAssumptionList.step
  · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ t7_has_bool_type
  · apply TranslatableAssumptionList.step
    · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ t4_has_bool_type
    · exact TranslatableAssumptionList.base

example : CmdListTranslationOk proof := by
  apply CmdListTranslationOk.cons
  · simp [symmStep, cmdTranslationOk]
  · apply CmdListTranslationOk.cons
    · simp [contraStep, cmdTranslationOk]
    · exact CmdListTranslationOk.nil

example : eo_is_refutation assumptions proof := by
  apply eo_is_refutation.intro
  native_decide

end CpcMicro.Examples.TestSimpleCheckerAssumptions
