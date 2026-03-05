import Cpc.Logos
open Eo
def t1 : Term := (Term.UConst 1 Term.Int)
def t2 : Term := (Term.UConst 2 Term.Int)
def t3 : Term := (Term.Apply Term.eq t2)
def t4 : Term := (Term.Apply t3 t1)
def t5 : Term := (Term.Apply Term.eq t1)
def t6 : Term := (Term.Apply t5 t2)
def t7 : Term := (Term.Apply Term.not t6)
def s0 : CState := CState.nil
def s1 : CState := (CState.cons (CStateObj.assume t4) s0)
def s2 : CState := (CState.cons (CStateObj.assume t7) s1)
def s3 : CState := (__eo_invoke_cmd s2 (CCmd.step CRule.symm CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s4 : CState := (__eo_invoke_cmd s3 (CCmd.step CRule.contra CArgList.nil (CIndexList.cons 2 (CIndexList.cons 0 CIndexList.nil))))
#eval!
(__eo_state_is_refutation s4)
