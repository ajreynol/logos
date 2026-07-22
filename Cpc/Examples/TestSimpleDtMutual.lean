module

public import Cpc.Proofs.Assumptions
import all Cpc.Proofs.Assumptions

public section

open Eo
open SmtEval
open Smtm

namespace Cpc.Examples.TestSimpleDtMutual

deriving instance DecidableEq for CIndexList, CArgList, CStateObj, CState, CRule, CCmd, CCmdList

/-
Mutually recursive datatypes `A` and `B` (canonical cvc5/Ethos encoding, taken
verbatim from `examples/test-simple-dt-mutual.cpc.lean`): `A` has one constructor
storing a `B`; `B` has one nullary constructor and one constructor storing an `A`.
Sibling occurrences inside the mutual block are encoded with
`Term.DatatypeTypeRef <name>`, and the whole block is carried as a two-entry
declaration list (`DatatypeDecl.cons "B" … (DatatypeDecl.cons "A" … nil)`).

The mutual analogue of `TestSimpleDt.lean`, in the spirit of
`CpcMini/Examples/TestSimpleCheckerAssumptions.lean`: we `#eval!`-check the checker
and prove the example meets all three side conditions in `Cpc/Proofs/Assumptions.lean`
(`TranslatableAssumptionList`, `CmdListTranslationOk`, `eo_is_refutation`).
-/

def t1 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "B"))
def t2 := (DatatypeCons.cons t1 DatatypeCons.unit)
def t3 := (Datatype.sum t2 Datatype.null)
def t4 := (DatatypeDecl.cons (SmtEval.native_string_lit "A") t3 DatatypeDecl.nil)
def t5 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t6 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "A"))
def t7 := (DatatypeCons.cons t6 DatatypeCons.unit)
def t8 := (Datatype.sum t7 t5)
def t9 := (DatatypeDecl.cons (SmtEval.native_string_lit "B") t8 t4)
def t10 := (Term.DtCons (SmtEval.native_string_lit "B") t9 1)
def t11 := (Term.DtCons (SmtEval.native_string_lit "A") t9 0)
def t12 := (Term.Apply t11 t10)
def t13 := (Term.DatatypeType (SmtEval.native_string_lit "A") t9)
def t14 := (Term.UConst 1 t13)
def t15 := (Term.Apply (Term.UOp UserOp.eq) t14)
def t16 := (Term.Apply t15 t12)
def t17 := (Term.Apply (Term.UOp UserOp.not) t16)
def t18 := (Term.DtSel (SmtEval.native_string_lit "A") t9 0 0)
def t19 := (Term.Apply t18 t14)
def t20 := (Term.DtCons (SmtEval.native_string_lit "B") t9 0)
def t21 := (Term.UOp1 UserOp1.is t20)
def t22 := (Term.Apply t21 t19)
def t23 := (Term.Apply (Term.UOp UserOp.not) t22)
def t24 := (Term.Apply (Term.UOp UserOp.or) t16)
def t25 := (Term.Apply t24 (Term.Boolean false))
def t26 := (Term.Apply (Term.UOp UserOp.not) t23)
def t27 := (Term.Apply (Term.UOp UserOp.or) t26)
def t28 := (Term.Apply t27 t25)
def t29 := (Term.DtCons (SmtEval.native_string_lit "B") t9 1)
def t30 := (Term.UOp1 UserOp1.is t29)
def t31 := (Term.Apply t30 t19)
def t32 := (Term.DtCons (SmtEval.native_string_lit "A") t9 0)
def t33 := (Term.UOp1 UserOp1.is t32)
def t34 := (Term.Apply t33 t14)
def t35 := (Term.Apply (Term.UOp UserOp.eq) t19)
def t36 := (Term.Apply t35 t10)
def t37 := (Term.Apply (Term.UOp UserOp.eq) t31)
def t38 := (Term.Apply t37 t36)
def t39 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t40 := (Term.Apply t39 Term.__eo_List_nil)
def t41 := (Term.Apply Term.__eo_List_cons t22)
def t42 := (Term.Apply t41 Term.__eo_List_nil)
def t43 := (Term.DtCons (SmtEval.native_string_lit "A") t9 0)
def t44 := (Term.Apply t43 t19)
def t45 := (Term.Apply (Term.UOp UserOp.eq) t14)
def t46 := (Term.Apply t45 t44)
def t47 := (Term.Apply (Term.UOp UserOp.eq) t34)
def t48 := (Term.Apply t47 t46)
def t49 := (Term.Apply (Term.UOp UserOp.or) t22)
def t50 := (Term.Apply t49 (Term.Boolean false))
def t51 := (Term.Apply (Term.UOp UserOp.or) t16)
def t52 := (Term.Apply t51 t50)
def t53 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t54 := (Term.Apply t53 Term.__eo_List_nil)
def t55 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t56 := (Term.Apply t55 t54)
def t57 := (Term.Apply Term.__eo_List_cons t16)
def t58 := (Term.Apply t57 Term.__eo_List_nil)
def t59 := (Term.Apply Term.__eo_List_cons t22)
def t60 := (Term.Apply t59 t58)

def s0 : CState := logos_init_state
def s1 : CState := (logos_invoke_assume s0 t17)
def s2 : CState := (logos_invoke_assume s1 t23)
def s3 : CState := (logos_invoke_cmd s2 (CCmd.step CRule.refl (CArgList.cons t16 CArgList.nil) CIndexList.nil))
def s4 : CState := (logos_invoke_cmd s3 (CCmd.step CRule.bool_double_not_elim (CArgList.cons t22 CArgList.nil) CIndexList.nil))
def s5 : CState := (logos_invoke_cmd s4 (CCmd.step CRule.nary_cong (CArgList.cons t28 CArgList.nil) (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))))
def s6 : CState := (logos_invoke_cmd s5 (CCmd.assume_push t23))
def s7 : CState := (logos_invoke_cmd s6 (CCmd.assume_push t31))
def s8 : CState := (logos_invoke_cmd s7 (CCmd.assume_push t34))
def s9 : CState := (logos_invoke_cmd s8 (CCmd.step CRule.dt_inst (CArgList.cons t38 CArgList.nil) CIndexList.nil))
def s10 : CState := (logos_invoke_cmd s9 (CCmd.step CRule.dt_split (CArgList.cons t19 CArgList.nil) CIndexList.nil))
def s11 : CState := (logos_invoke_cmd s10 (CCmd.step CRule.chain_resolution (CArgList.cons t40 (CArgList.cons t42 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 8 CIndexList.nil))))
def s12 : CState := (logos_invoke_cmd s11 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))))
def s13 : CState := (logos_invoke_cmd s12 (CCmd.step CRule.cong (CArgList.cons t44 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s14 : CState := (logos_invoke_cmd s13 (CCmd.step CRule.dt_inst (CArgList.cons t48 CArgList.nil) CIndexList.nil))
def s15 : CState := (logos_invoke_cmd s14 (CCmd.step CRule.dt_split (CArgList.cons t14 CArgList.nil) CIndexList.nil))
def s16 : CState := (logos_invoke_cmd s15 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))))
def s17 : CState := (logos_invoke_cmd s16 (CCmd.step CRule.trans CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))))
def s18 : CState := (logos_invoke_cmd s17 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s19 : CState := (logos_invoke_cmd s18 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s20 : CState := (logos_invoke_cmd s19 (CCmd.step CRule.process_scope (CArgList.cons t16 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s21 : CState := (logos_invoke_cmd s20 (CCmd.step CRule.dt_split (CArgList.cons t14 CArgList.nil) CIndexList.nil))
def s22 : CState := (logos_invoke_cmd s21 (CCmd.step CRule.dt_split (CArgList.cons t19 CArgList.nil) CIndexList.nil))
def s23 : CState := (logos_invoke_cmd s22 (CCmd.step CRule.chain_resolution (CArgList.cons t40 (CArgList.cons t42 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 8 CIndexList.nil))))
def s24 : CState := (logos_invoke_cmd s23 (CCmd.step CRule.and_intro CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))))
def s25 : CState := (logos_invoke_cmd s24 (CCmd.step CRule.modus_ponens CArgList.nil (CIndexList.cons 0 (CIndexList.cons 4 CIndexList.nil))))
def s26 : CState := (logos_invoke_cmd s25 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s27 : CState := (logos_invoke_cmd s26 (CCmd.step CRule.process_scope (CArgList.cons t16 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s28 : CState := (logos_invoke_cmd s27 (CCmd.step CRule.implies_elim CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s29 : CState := (logos_invoke_cmd s28 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))))
def s30 : CState := (logos_invoke_cmd s29 (CCmd.step CRule.reordering (CArgList.cons t52 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s31 : CState := (logos_invoke_cmd s30 (CCmd.step CRule.chain_m_resolution (CArgList.cons (Term.Boolean false) (CArgList.cons t56 (CArgList.cons t60 CArgList.nil))) (CIndexList.cons 0 (CIndexList.cons 8 (CIndexList.cons 9 CIndexList.nil)))))

/-- The two assumptions of the example, conjoined most-recent-first (matching the
checker's assumption stack). -/
def assumptions : Term :=
  (Term.Apply (Term.Apply (Term.UOp UserOp.and) t23) (Term.Apply (Term.Apply (Term.UOp UserOp.and) t17) (Term.Boolean true)))

/-- The proof: every checker command after the two assumptions, in order. -/
def proof : CCmdList :=
  CCmdList.cons (CCmd.step CRule.refl (CArgList.cons t16 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.bool_double_not_elim (CArgList.cons t22 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.nary_cong (CArgList.cons t28 CArgList.nil) (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))) <|
  CCmdList.cons (CCmd.assume_push t23) <|
  CCmdList.cons (CCmd.assume_push t31) <|
  CCmdList.cons (CCmd.assume_push t34) <|
  CCmdList.cons (CCmd.step CRule.dt_inst (CArgList.cons t38 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t19 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.chain_resolution (CArgList.cons t40 (CArgList.cons t42 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 8 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.cong (CArgList.cons t44 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.dt_inst (CArgList.cons t48 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t14 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.trans CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.process_scope (CArgList.cons t16 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t14 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t19 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.chain_resolution (CArgList.cons t40 (CArgList.cons t42 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 8 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.and_intro CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.modus_ponens CArgList.nil (CIndexList.cons 0 (CIndexList.cons 4 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.process_scope (CArgList.cons t16 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.implies_elim CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.reordering (CArgList.cons t52 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.chain_m_resolution (CArgList.cons (Term.Boolean false) (CArgList.cons t56 (CArgList.cons t60 CArgList.nil))) (CIndexList.cons 0 (CIndexList.cons 8 (CIndexList.cons 9 CIndexList.nil)))) <|
  CCmdList.nil

#eval! decide (__eo_invoke_assume_list CState.nil assumptions = s2)
#eval! decide (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil assumptions) proof = s31)
#eval! __eo_checker_is_refutation assumptions proof
#eval! logos_state_is_refutation s31

/- KNOWN GAP (dtDecl refactor): the two SMT-translation obligations below are
currently FALSE under the declaration-list model. `__smtx_datatype_cons_default`
checks constructor fields against the *unresolved* declaration entry, so a sibling
reference (`TypeRef "B"`) forces `NotValue`; datatype `A`, whose only constructor
stores a `B`, therefore has no default value, `native_inhabited_type` is `false`,
`__smtx_type_wf` rejects it, and every `A`-typed term translates to `None`
(`native_decide` refutes the obligations). The pre-dtDecl substitution-based
default builder unfolded one level of the sibling and accepted this example.
Restoring these obligations needs a model-level decision on how the default
builder should unfold sibling references (e.g. defaulting against the resolved
entry with a different termination measure).

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
      t39, t40, t41, t42, t53, t54, t55, t56, t57, t58, t59, t60]
  all_goals native_decide
-/

example : eo_is_refutation assumptions proof := by
  apply eo_is_refutation.intro
  native_decide

end Cpc.Examples.TestSimpleDtMutual
