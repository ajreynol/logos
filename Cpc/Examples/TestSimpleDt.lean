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
cvc5/Ethos encoding), so the tester/selector terms translate to SMT correctly.

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
def t6 := (Term.DatatypeType (SmtEval.native_string_lit "List") t5)
def t7 := (Term.UConst 1 t6)
def t8 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t9 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "List"))
def t10 := (DatatypeCons.cons t9 DatatypeCons.unit)
def t11 := (DatatypeCons.cons (Term.UOp UserOp.Int) t10)
def t12 := (Datatype.sum t11 t8)
def t13 := (Term.DtCons (SmtEval.native_string_lit "List") t12 0)
def t14 := (Term.UOp1 UserOp1.is t13)
def t15 := (Term.Apply t14 t7)
def t16 := (Term.Apply (Term.UOp UserOp.not) t15)
def t17 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t18 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "List"))
def t19 := (DatatypeCons.cons t18 DatatypeCons.unit)
def t20 := (DatatypeCons.cons (Term.UOp UserOp.Int) t19)
def t21 := (Datatype.sum t20 t17)
def t22 := (Term.DtCons (SmtEval.native_string_lit "List") t21 1)
def t23 := (Term.UOp1 UserOp1.is t22)
def t24 := (Term.Apply t23 t7)
def t25 := (Term.Apply (Term.UOp UserOp.not) t24)
def t26 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t27 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "List"))
def t28 := (DatatypeCons.cons t27 DatatypeCons.unit)
def t29 := (DatatypeCons.cons (Term.UOp UserOp.Int) t28)
def t30 := (Datatype.sum t29 t26)
def t31 := (Term.DtCons (SmtEval.native_string_lit "List") t30 1)
def t32 := (Term.Apply (Term.UOp UserOp.eq) t7)
def t33 := (Term.Apply t32 t31)
def t34 := (Term.Apply (Term.UOp UserOp.eq) t24)
def t35 := (Term.Apply t34 t33)
def t36 := (Term.Apply (Term.UOp UserOp.eq) t31)
def t37 := (Term.Apply t36 t7)
def t38 := (Term.Apply (Term.UOp UserOp.or) t37)
def t39 := (Term.Apply t38 (Term.Boolean false))
def t40 := (Term.Apply (Term.UOp UserOp.not) t16)
def t41 := (Term.Apply (Term.UOp UserOp.or) t40)
def t42 := (Term.Apply t41 t39)
def t43 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t44 := (Term.Apply t43 Term.__eo_List_nil)
def t45 := (Term.Apply Term.__eo_List_cons t15)
def t46 := (Term.Apply t45 Term.__eo_List_nil)
def t47 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t48 := (Term.Apply t47 Term.__eo_List_nil)
def t49 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t50 := (Term.Apply t49 t48)
def t51 := (Term.Apply Term.__eo_List_cons t15)
def t52 := (Term.Apply t51 Term.__eo_List_nil)
def t53 := (Term.Apply Term.__eo_List_cons t37)
def t54 := (Term.Apply t53 t52)

def s0 : CState := logos_init_state
def s1 : CState := (logos_invoke_assume s0 t16)
def s2 : CState := (logos_invoke_assume s1 t25)
def s3 : CState := (logos_invoke_cmd s2 (CCmd.step CRule.eq_symm (CArgList.cons t7 (CArgList.cons t31 CArgList.nil)) CIndexList.nil))
def s4 : CState := (logos_invoke_cmd s3 (CCmd.step CRule.dt_inst (CArgList.cons t35 CArgList.nil) CIndexList.nil))
def s5 : CState := (logos_invoke_cmd s4 (CCmd.step CRule.trans CArgList.nil (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))))
def s6 : CState := (logos_invoke_cmd s5 (CCmd.step CRule.cong (CArgList.cons t25 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s7 : CState := (logos_invoke_cmd s6 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 4 (CIndexList.cons 0 CIndexList.nil))))
def s8 : CState := (logos_invoke_cmd s7 (CCmd.step CRule.refl (CArgList.cons t37 CArgList.nil) CIndexList.nil))
def s9 : CState := (logos_invoke_cmd s8 (CCmd.step CRule.bool_double_not_elim (CArgList.cons t15 CArgList.nil) CIndexList.nil))
def s10 : CState := (logos_invoke_cmd s9 (CCmd.step CRule.nary_cong (CArgList.cons t42 CArgList.nil) (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))))
def s11 : CState := (logos_invoke_cmd s10 (CCmd.assume_push t16))
def s12 : CState := (logos_invoke_cmd s11 (CCmd.assume_push t24))
def s13 : CState := (logos_invoke_cmd s12 (CCmd.step CRule.dt_split (CArgList.cons t7 CArgList.nil) CIndexList.nil))
def s14 : CState := (logos_invoke_cmd s13 (CCmd.step CRule.chain_resolution (CArgList.cons t44 (CArgList.cons t46 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 12 CIndexList.nil))))
def s15 : CState := (logos_invoke_cmd s14 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 10 CIndexList.nil))))
def s16 : CState := (logos_invoke_cmd s15 (CCmd.step CRule.symm CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s17 : CState := (logos_invoke_cmd s16 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s18 : CState := (logos_invoke_cmd s17 (CCmd.step CRule.process_scope (CArgList.cons t37 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s19 : CState := (logos_invoke_cmd s18 (CCmd.step CRule.dt_split (CArgList.cons t7 CArgList.nil) CIndexList.nil))
def s20 : CState := (logos_invoke_cmd s19 (CCmd.step CRule.chain_resolution (CArgList.cons t44 (CArgList.cons t46 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 13 CIndexList.nil))))
def s21 : CState := (logos_invoke_cmd s20 (CCmd.step CRule.modus_ponens CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))))
def s22 : CState := (logos_invoke_cmd s21 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s23 : CState := (logos_invoke_cmd s22 (CCmd.step CRule.process_scope (CArgList.cons t37 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s24 : CState := (logos_invoke_cmd s23 (CCmd.step CRule.implies_elim CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s25 : CState := (logos_invoke_cmd s24 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))))
def s26 : CState := (logos_invoke_cmd s25 (CCmd.step CRule.chain_m_resolution (CArgList.cons (Term.Boolean false) (CArgList.cons t50 (CArgList.cons t54 CArgList.nil))) (CIndexList.cons 0 (CIndexList.cons 7 (CIndexList.cons 13 CIndexList.nil)))))

/-- The two assumptions of the example, conjoined most-recent-first (matching the
checker's assumption stack). -/
def assumptions : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.and) t25)
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) t16) (Term.Boolean true))

/-- The proof: every checker command after the two assumptions, in order. -/
def proof : CCmdList :=
  CCmdList.cons (CCmd.step CRule.eq_symm (CArgList.cons t7 (CArgList.cons t31 CArgList.nil)) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.dt_inst (CArgList.cons t35 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.trans CArgList.nil (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.cong (CArgList.cons t25 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 4 (CIndexList.cons 0 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.refl (CArgList.cons t37 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.bool_double_not_elim (CArgList.cons t15 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.nary_cong (CArgList.cons t42 CArgList.nil) (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))) <|
  CCmdList.cons (CCmd.assume_push t16) <|
  CCmdList.cons (CCmd.assume_push t24) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t7 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.chain_resolution (CArgList.cons t44 (CArgList.cons t46 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 12 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 10 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.symm CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.process_scope (CArgList.cons t37 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t7 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.chain_resolution (CArgList.cons t44 (CArgList.cons t46 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 13 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.modus_ponens CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.process_scope (CArgList.cons t37 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.implies_elim CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.chain_m_resolution (CArgList.cons (Term.Boolean false) (CArgList.cons t50 (CArgList.cons t54 CArgList.nil))) (CIndexList.cons 0 (CIndexList.cons 7 (CIndexList.cons 13 CIndexList.nil)))) <|
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
      t43, t44, t45, t46, t47, t48, t49, t50, t51, t52, t53, t54]
  all_goals native_decide

example : eo_is_refutation assumptions proof := by
  apply eo_is_refutation.intro
  native_decide

end Cpc.Examples.TestSimpleDt
