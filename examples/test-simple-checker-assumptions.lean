import CpcMicro.Spec

open Eo

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

-- Executable shadow of the translation side-condition for the constructors
-- that appear in `examples/test-simple.cpc.lean`.
def typeTranslationCheck : Term -> Bool
  | Term.Bool => true
  | Term.Int => true
  | Term.Real => true
  | Term.Char => true
  | Term.USort _ => true
  | Term.Apply Term.BitVec (Term.Numeral _) => true
  | Term.Apply Term.Seq T => typeTranslationCheck T
  | Term.Apply (Term.Apply Term.FunType T1) T2 =>
      typeTranslationCheck T1 && typeTranslationCheck T2
  | _ => false

def hasSmtTranslationCheck : Term -> Bool
  | Term.Boolean _ => true
  | Term.Numeral _ => true
  | Term.Rational _ => true
  | Term.String _ => true
  | Term.Binary _ _ => true
  | Term.Var _ T => typeTranslationCheck T
  | Term.UConst _ T => typeTranslationCheck T
  | Term.Apply Term.not x => hasSmtTranslationCheck x
  | Term.Apply (Term.Apply Term.or x) y =>
      hasSmtTranslationCheck x && hasSmtTranslationCheck y
  | Term.Apply (Term.Apply Term.and x) y =>
      hasSmtTranslationCheck x && hasSmtTranslationCheck y
  | Term.Apply (Term.Apply Term.imp x) y =>
      hasSmtTranslationCheck x && hasSmtTranslationCheck y
  | Term.Apply (Term.Apply Term.eq x) y =>
      hasSmtTranslationCheck x && hasSmtTranslationCheck y
  | _ => false

def typedAssumptionListCheck : Term -> Bool
  | Term.Boolean true => true
  | Term.Apply (Term.Apply Term.and A) rest =>
      decide (A ≠ Term.Stuck) &&
      decide (__eo_typeof A = Term.Bool) &&
      typedAssumptionListCheck rest
  | _ => false

def translatableAssumptionListCheck : Term -> Bool
  | Term.Boolean true => true
  | Term.Apply (Term.Apply Term.and A) rest =>
      hasSmtTranslationCheck A &&
      translatableAssumptionListCheck rest
  | _ => false

def cmdTranslationOkCheck : CCmd -> Bool
  | CCmd.assume_push A => hasSmtTranslationCheck A
  | CCmd.step CRule.refl (CArgList.cons a1 CArgList.nil) CIndexList.nil =>
      hasSmtTranslationCheck a1
  | _ => true

def cmdListTranslationOkCheck : CCmdList -> Bool
  | CCmdList.nil => true
  | CCmdList.cons c cs => cmdTranslationOkCheck c && cmdListTranslationOkCheck cs

#eval decide (__eo_invoke_assume_list CState.nil assumptions = s2)
#eval decide (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil assumptions) proof = s4)
#eval decide (__eo_typeof t7 = Term.Bool)
#eval hasSmtTranslationCheck t7
#eval decide (__eo_typeof t4 = Term.Bool)
#eval hasSmtTranslationCheck t4
#eval typedAssumptionListCheck assumptions
#eval translatableAssumptionListCheck assumptions
#eval cmdListTranslationOkCheck proof
#eval __eo_checker_is_refutation assumptions proof
