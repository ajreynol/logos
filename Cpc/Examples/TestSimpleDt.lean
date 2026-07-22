module

public import Cpc.Proofs.Assumptions
import all Cpc.Proofs.Assumptions

public section

open Eo
open SmtEval
open Smtm

namespace Cpc.Examples.TestSimpleDt

deriving instance DecidableEq for CIndexList, CArgList, CStateObj, CState, CRule, CCmd, CCmdList

/-
Self-recursive datatype `List := nil | cons(Int, List)`, with a refutation that
the value `@u.1 : List` is neither `cons` nor `nil`. The recursive occurrence of
the datatype is encoded with `Term.DatatypeTypeRef "List"` (the canonical
cvc5/Ethos encoding), and the datatype itself is carried as a one-entry
declaration list (`DatatypeDecl.cons "List" … DatatypeDecl.nil`), so the
tester/selector terms translate to SMT correctly.

In the spirit of `CpcMini/Examples/TestSimpleCheckerAssumptions.lean`: besides
`#eval!`-checking the checker, we prove this example meets the side conditions in
`Cpc/Proofs/Assumptions.lean` (`TranslatableAssumptionList`,
`CmdListTranslationOk`) and that the checker accepts it (`eo_is_refutation`).
-/

def t1 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t2 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "List"))
def t3 := (DatatypeCons.cons t2 DatatypeCons.unit)
def t4 := (DatatypeCons.cons (Term.UOp UserOp.Int) t3)
def t5 := (Datatype.sum t4 t1)
def t6 := (DatatypeDecl.cons (SmtEval.native_string_lit "List") t5 DatatypeDecl.nil)
def t7 := (Term.DatatypeType (SmtEval.native_string_lit "List") t6)
def t8 := (Term.UConst 1 t7)
def t9 := (Term.DtCons (SmtEval.native_string_lit "List") t6 0)
def t10 := (Term.UOp1 UserOp1.is t9)
def t11 := (Term.Apply t10 t8)
def t12 := (Term.Apply (Term.UOp UserOp.not) t11)
def t13 := (Term.DtCons (SmtEval.native_string_lit "List") t6 1)
def t14 := (Term.UOp1 UserOp1.is t13)
def t15 := (Term.Apply t14 t8)
def t16 := (Term.Apply (Term.UOp UserOp.not) t15)
def t17 := (Term.DtCons (SmtEval.native_string_lit "List") t6 1)
def t18 := (Term.Apply (Term.UOp UserOp.eq) t8)
def t19 := (Term.Apply t18 t17)
def t20 := (Term.Apply (Term.UOp UserOp.eq) t15)
def t21 := (Term.Apply t20 t19)
def t22 := (Term.Apply (Term.UOp UserOp.eq) t17)
def t23 := (Term.Apply t22 t8)
def t24 := (Term.Apply (Term.UOp UserOp.or) t23)
def t25 := (Term.Apply t24 (Term.Boolean false))
def t26 := (Term.Apply (Term.UOp UserOp.not) t12)
def t27 := (Term.Apply (Term.UOp UserOp.or) t26)
def t28 := (Term.Apply t27 t25)
def t29 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t30 := (Term.Apply t29 Term.__eo_List_nil)
def t31 := (Term.Apply Term.__eo_List_cons t11)
def t32 := (Term.Apply t31 Term.__eo_List_nil)
def t33 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t34 := (Term.Apply t33 Term.__eo_List_nil)
def t35 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t36 := (Term.Apply t35 t34)
def t37 := (Term.Apply Term.__eo_List_cons t11)
def t38 := (Term.Apply t37 Term.__eo_List_nil)
def t39 := (Term.Apply Term.__eo_List_cons t23)
def t40 := (Term.Apply t39 t38)

def s0 : CState := logos_init_state
def s1 : CState := (logos_invoke_assume s0 t12)
def s2 : CState := (logos_invoke_assume s1 t16)
def s3 : CState := (logos_invoke_cmd s2 (CCmd.step CRule.eq_symm (CArgList.cons t8 (CArgList.cons t17 CArgList.nil)) CIndexList.nil))
def s4 : CState := (logos_invoke_cmd s3 (CCmd.step CRule.dt_inst (CArgList.cons t21 CArgList.nil) CIndexList.nil))
def s5 : CState := (logos_invoke_cmd s4 (CCmd.step CRule.trans CArgList.nil (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))))
def s6 : CState := (logos_invoke_cmd s5 (CCmd.step CRule.cong (CArgList.cons t16 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s7 : CState := (logos_invoke_cmd s6 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 4 (CIndexList.cons 0 CIndexList.nil))))
def s8 : CState := (logos_invoke_cmd s7 (CCmd.step CRule.refl (CArgList.cons t23 CArgList.nil) CIndexList.nil))
def s9 : CState := (logos_invoke_cmd s8 (CCmd.step CRule.bool_double_not_elim (CArgList.cons t11 CArgList.nil) CIndexList.nil))
def s10 : CState := (logos_invoke_cmd s9 (CCmd.step CRule.nary_cong (CArgList.cons t28 CArgList.nil) (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))))
def s11 : CState := (logos_invoke_cmd s10 (CCmd.assume_push t12))
def s12 : CState := (logos_invoke_cmd s11 (CCmd.assume_push t15))
def s13 : CState := (logos_invoke_cmd s12 (CCmd.step CRule.dt_split (CArgList.cons t8 CArgList.nil) CIndexList.nil))
def s14 : CState := (logos_invoke_cmd s13 (CCmd.step CRule.chain_resolution (CArgList.cons t30 (CArgList.cons t32 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 12 CIndexList.nil))))
def s15 : CState := (logos_invoke_cmd s14 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 10 CIndexList.nil))))
def s16 : CState := (logos_invoke_cmd s15 (CCmd.step CRule.symm CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s17 : CState := (logos_invoke_cmd s16 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s18 : CState := (logos_invoke_cmd s17 (CCmd.step CRule.process_scope (CArgList.cons t23 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s19 : CState := (logos_invoke_cmd s18 (CCmd.step CRule.dt_split (CArgList.cons t8 CArgList.nil) CIndexList.nil))
def s20 : CState := (logos_invoke_cmd s19 (CCmd.step CRule.chain_resolution (CArgList.cons t30 (CArgList.cons t32 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 13 CIndexList.nil))))
def s21 : CState := (logos_invoke_cmd s20 (CCmd.step CRule.modus_ponens CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))))
def s22 : CState := (logos_invoke_cmd s21 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s23 : CState := (logos_invoke_cmd s22 (CCmd.step CRule.process_scope (CArgList.cons t23 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s24 : CState := (logos_invoke_cmd s23 (CCmd.step CRule.implies_elim CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s25 : CState := (logos_invoke_cmd s24 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))))
def s26 : CState := (logos_invoke_cmd s25 (CCmd.step CRule.chain_m_resolution (CArgList.cons (Term.Boolean false) (CArgList.cons t36 (CArgList.cons t40 CArgList.nil))) (CIndexList.cons 0 (CIndexList.cons 7 (CIndexList.cons 13 CIndexList.nil)))))

/-- The two assumptions of the example, conjoined most-recent-first (matching the
checker's assumption stack). -/
def assumptions : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) t16)
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) t12) (Term.Boolean true))

/-- The proof: every checker command after the two assumptions, in order. -/
def proof : CCmdList :=
  CCmdList.cons (CCmd.step CRule.eq_symm (CArgList.cons t8 (CArgList.cons t17 CArgList.nil)) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.dt_inst (CArgList.cons t21 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.trans CArgList.nil (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.cong (CArgList.cons t16 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 4 (CIndexList.cons 0 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.refl (CArgList.cons t23 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.bool_double_not_elim (CArgList.cons t11 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.nary_cong (CArgList.cons t28 CArgList.nil) (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))) <|
  CCmdList.cons (CCmd.assume_push t12) <|
  CCmdList.cons (CCmd.assume_push t15) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t8 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.chain_resolution (CArgList.cons t30 (CArgList.cons t32 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 12 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 10 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.symm CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.process_scope (CArgList.cons t23 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t8 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.chain_resolution (CArgList.cons t30 (CArgList.cons t32 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 13 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.modus_ponens CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.process_scope (CArgList.cons t23 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.implies_elim CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.chain_m_resolution (CArgList.cons (Term.Boolean false) (CArgList.cons t36 (CArgList.cons t40 CArgList.nil))) (CIndexList.cons 0 (CIndexList.cons 7 (CIndexList.cons 13 CIndexList.nil)))) <|
  CCmdList.nil

#eval! decide (__eo_invoke_assume_list CState.nil assumptions = s2)
#eval! decide (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil assumptions) proof = s26)
#eval! __eo_checker_is_refutation assumptions proof
#eval! logos_state_is_refutation s26

example : TranslatableAssumptionList assumptions := by
  unfold assumptions
  repeat' first
    | apply TranslatableAssumptionList.step
    | apply TranslatableAssumptionList.base
  all_goals (unfold eoHasSmtTranslation; native_decide)

example : CmdListTranslationOk proof := by
  unfold proof
  repeat' first
    | apply CmdListTranslationOk.cons
    | apply CmdListTranslationOk.nil
  all_goals
    simp only [cmdTranslationOk, cArgListTranslationOk, cArgListTranslationOkMask,
      argTranslationOkMasked, eoHasSmtTranslation, EoListAllHaveSmtTranslation,
      t29, t30, t31, t32, t33, t34, t35, t36, t37, t38, t39, t40]
  all_goals native_decide

example : eo_is_refutation assumptions proof := by
  apply eo_is_refutation.intro
  native_decide

end Cpc.Examples.TestSimpleDt
