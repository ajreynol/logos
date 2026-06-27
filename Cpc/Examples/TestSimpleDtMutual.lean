import Cpc.Proofs.Assumptions

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
`Term.DatatypeTypeRef <name>`.

This file is the mutual analogue of `TestSimpleDt.lean`, written in the spirit of
`CpcMini/Examples/TestSimpleCheckerAssumptions.lean`. It records the current state
of mutual-datatype support against the side conditions in `Cpc/Proofs/Assumptions.lean`:

  * `eo_is_refutation assumptions proof`  -- HOLDS: the checker accepts the proof.
  * `TranslatableAssumptionList assumptions`  -- DOES NOT HOLD (yet).
  * `CmdListTranslationOk proof`  -- DOES NOT HOLD (yet).

The two translation obligations fail because of a *sibling* `Term.DatatypeTypeRef`
translation gap: while a bare value of a mutual type translates fine, every
constructor application, selector application, and tester over a mutual datatype
translates to `SmtType.None` (its result/argument type needs the sibling binding,
which `__eo_to_smt` does not yet supply). The `#eval!`s below isolate exactly which
terms are affected; the two obligations become provable (by the same tactic used in
`TestSimpleDt.lean`) once mutual-datatype translation is implemented.
-/

def t1 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t2 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "B"))
def t3 := (DatatypeCons.cons t2 DatatypeCons.unit)
def t4 := (Datatype.sum t3 Datatype.null)
def t5 := (Term.DatatypeType (SmtEval.native_string_lit "A") t4)
def t6 := (DatatypeCons.cons t5 DatatypeCons.unit)
def t7 := (Datatype.sum t6 t1)
def t8 := (Term.DtCons (SmtEval.native_string_lit "B") t7 1)
def t9 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t10 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "A"))
def t11 := (DatatypeCons.cons t10 DatatypeCons.unit)
def t12 := (Datatype.sum t11 t9)
def t13 := (Term.DatatypeType (SmtEval.native_string_lit "B") t12)
def t14 := (DatatypeCons.cons t13 DatatypeCons.unit)
def t15 := (Datatype.sum t14 Datatype.null)
def t16 := (Term.DtCons (SmtEval.native_string_lit "A") t15 0)
def t17 := (Term.Apply t16 t8)
def t18 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t19 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "A"))
def t20 := (DatatypeCons.cons t19 DatatypeCons.unit)
def t21 := (Datatype.sum t20 t18)
def t22 := (Term.DatatypeType (SmtEval.native_string_lit "B") t21)
def t23 := (DatatypeCons.cons t22 DatatypeCons.unit)
def t24 := (Datatype.sum t23 Datatype.null)
def t25 := (Term.DatatypeType (SmtEval.native_string_lit "A") t24)
def t26 := (Term.UConst 1 t25)
def t27 := (Term.Apply (Term.UOp UserOp.eq) t26)
def t28 := (Term.Apply t27 t17)
def t29 := (Term.Apply (Term.UOp UserOp.not) t28)
def t30 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t31 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "A"))
def t32 := (DatatypeCons.cons t31 DatatypeCons.unit)
def t33 := (Datatype.sum t32 t30)
def t34 := (Term.DatatypeType (SmtEval.native_string_lit "B") t33)
def t35 := (DatatypeCons.cons t34 DatatypeCons.unit)
def t36 := (Datatype.sum t35 Datatype.null)
def t37 := (Term.DtSel (SmtEval.native_string_lit "A") t36 0 0)
def t38 := (Term.Apply t37 t26)
def t39 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t40 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "B"))
def t41 := (DatatypeCons.cons t40 DatatypeCons.unit)
def t42 := (Datatype.sum t41 Datatype.null)
def t43 := (Term.DatatypeType (SmtEval.native_string_lit "A") t42)
def t44 := (DatatypeCons.cons t43 DatatypeCons.unit)
def t45 := (Datatype.sum t44 t39)
def t46 := (Term.DtCons (SmtEval.native_string_lit "B") t45 0)
def t47 := (Term.UOp1 UserOp1.is t46)
def t48 := (Term.Apply t47 t38)
def t49 := (Term.Apply (Term.UOp UserOp.not) t48)
def t50 := (Term.Apply (Term.UOp UserOp.or) t28)
def t51 := (Term.Apply t50 (Term.Boolean false))
def t52 := (Term.Apply (Term.UOp UserOp.not) t49)
def t53 := (Term.Apply (Term.UOp UserOp.or) t52)
def t54 := (Term.Apply t53 t51)
def t55 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t56 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "B"))
def t57 := (DatatypeCons.cons t56 DatatypeCons.unit)
def t58 := (Datatype.sum t57 Datatype.null)
def t59 := (Term.DatatypeType (SmtEval.native_string_lit "A") t58)
def t60 := (DatatypeCons.cons t59 DatatypeCons.unit)
def t61 := (Datatype.sum t60 t55)
def t62 := (Term.DtCons (SmtEval.native_string_lit "B") t61 1)
def t63 := (Term.UOp1 UserOp1.is t62)
def t64 := (Term.Apply t63 t38)
def t65 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t66 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "A"))
def t67 := (DatatypeCons.cons t66 DatatypeCons.unit)
def t68 := (Datatype.sum t67 t65)
def t69 := (Term.DatatypeType (SmtEval.native_string_lit "B") t68)
def t70 := (DatatypeCons.cons t69 DatatypeCons.unit)
def t71 := (Datatype.sum t70 Datatype.null)
def t72 := (Term.DtCons (SmtEval.native_string_lit "A") t71 0)
def t73 := (Term.UOp1 UserOp1.is t72)
def t74 := (Term.Apply t73 t26)
def t75 := (Term.Apply (Term.UOp UserOp.eq) t38)
def t76 := (Term.Apply t75 t8)
def t77 := (Term.Apply (Term.UOp UserOp.eq) t64)
def t78 := (Term.Apply t77 t76)
def t79 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t80 := (Term.Apply t79 Term.__eo_List_nil)
def t81 := (Term.Apply Term.__eo_List_cons t48)
def t82 := (Term.Apply t81 Term.__eo_List_nil)
def t83 := (Datatype.sum DatatypeCons.unit Datatype.null)
def t84 := (Term.DatatypeTypeRef (SmtEval.native_string_lit "A"))
def t85 := (DatatypeCons.cons t84 DatatypeCons.unit)
def t86 := (Datatype.sum t85 t83)
def t87 := (Term.DatatypeType (SmtEval.native_string_lit "B") t86)
def t88 := (DatatypeCons.cons t87 DatatypeCons.unit)
def t89 := (Datatype.sum t88 Datatype.null)
def t90 := (Term.DtCons (SmtEval.native_string_lit "A") t89 0)
def t91 := (Term.Apply t90 t38)
def t92 := (Term.Apply (Term.UOp UserOp.eq) t26)
def t93 := (Term.Apply t92 t91)
def t94 := (Term.Apply (Term.UOp UserOp.eq) t74)
def t95 := (Term.Apply t94 t93)
def t96 := (Term.Apply (Term.UOp UserOp.or) t48)
def t97 := (Term.Apply t96 (Term.Boolean false))
def t98 := (Term.Apply (Term.UOp UserOp.or) t28)
def t99 := (Term.Apply t98 t97)
def t100 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t101 := (Term.Apply t100 Term.__eo_List_nil)
def t102 := (Term.Apply Term.__eo_List_cons (Term.Boolean true))
def t103 := (Term.Apply t102 t101)
def t104 := (Term.Apply Term.__eo_List_cons t28)
def t105 := (Term.Apply t104 Term.__eo_List_nil)
def t106 := (Term.Apply Term.__eo_List_cons t48)
def t107 := (Term.Apply t106 t105)

def s0 : CState := logos_init_state
def s1 : CState := (logos_invoke_assume s0 t29)
def s2 : CState := (logos_invoke_assume s1 t49)
def s3 : CState := (logos_invoke_cmd s2 (CCmd.step CRule.refl (CArgList.cons t28 CArgList.nil) CIndexList.nil))
def s4 : CState := (logos_invoke_cmd s3 (CCmd.step CRule.bool_double_not_elim (CArgList.cons t48 CArgList.nil) CIndexList.nil))
def s5 : CState := (logos_invoke_cmd s4 (CCmd.step CRule.nary_cong (CArgList.cons t54 CArgList.nil) (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))))
def s6 : CState := (logos_invoke_cmd s5 (CCmd.assume_push t49))
def s7 : CState := (logos_invoke_cmd s6 (CCmd.assume_push t64))
def s8 : CState := (logos_invoke_cmd s7 (CCmd.assume_push t74))
def s9 : CState := (logos_invoke_cmd s8 (CCmd.step CRule.dt_inst (CArgList.cons t78 CArgList.nil) CIndexList.nil))
def s10 : CState := (logos_invoke_cmd s9 (CCmd.step CRule.dt_split (CArgList.cons t38 CArgList.nil) CIndexList.nil))
def s11 : CState := (logos_invoke_cmd s10 (CCmd.step CRule.chain_resolution (CArgList.cons t80 (CArgList.cons t82 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 8 CIndexList.nil))))
def s12 : CState := (logos_invoke_cmd s11 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))))
def s13 : CState := (logos_invoke_cmd s12 (CCmd.step CRule.cong (CArgList.cons t91 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s14 : CState := (logos_invoke_cmd s13 (CCmd.step CRule.dt_inst (CArgList.cons t95 CArgList.nil) CIndexList.nil))
def s15 : CState := (logos_invoke_cmd s14 (CCmd.step CRule.dt_split (CArgList.cons t26 CArgList.nil) CIndexList.nil))
def s16 : CState := (logos_invoke_cmd s15 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))))
def s17 : CState := (logos_invoke_cmd s16 (CCmd.step CRule.trans CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))))
def s18 : CState := (logos_invoke_cmd s17 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s19 : CState := (logos_invoke_cmd s18 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s20 : CState := (logos_invoke_cmd s19 (CCmd.step CRule.process_scope (CArgList.cons t28 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s21 : CState := (logos_invoke_cmd s20 (CCmd.step CRule.dt_split (CArgList.cons t26 CArgList.nil) CIndexList.nil))
def s22 : CState := (logos_invoke_cmd s21 (CCmd.step CRule.dt_split (CArgList.cons t38 CArgList.nil) CIndexList.nil))
def s23 : CState := (logos_invoke_cmd s22 (CCmd.step CRule.chain_resolution (CArgList.cons t80 (CArgList.cons t82 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 8 CIndexList.nil))))
def s24 : CState := (logos_invoke_cmd s23 (CCmd.step CRule.and_intro CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))))
def s25 : CState := (logos_invoke_cmd s24 (CCmd.step CRule.modus_ponens CArgList.nil (CIndexList.cons 0 (CIndexList.cons 4 CIndexList.nil))))
def s26 : CState := (logos_invoke_cmd s25 (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s27 : CState := (logos_invoke_cmd s26 (CCmd.step CRule.process_scope (CArgList.cons t28 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s28 : CState := (logos_invoke_cmd s27 (CCmd.step CRule.implies_elim CArgList.nil (CIndexList.cons 0 CIndexList.nil)))
def s29 : CState := (logos_invoke_cmd s28 (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))))
def s30 : CState := (logos_invoke_cmd s29 (CCmd.step CRule.reordering (CArgList.cons t99 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)))
def s31 : CState := (logos_invoke_cmd s30 (CCmd.step CRule.chain_m_resolution (CArgList.cons (Term.Boolean false) (CArgList.cons t103 (CArgList.cons t107 CArgList.nil))) (CIndexList.cons 0 (CIndexList.cons 8 (CIndexList.cons 9 CIndexList.nil)))))

/-- The two assumptions of the example, conjoined most-recent-first (matching the
checker's assumption stack). -/
def assumptions : Term :=
  (Term.Apply (Term.Apply (Term.UOp UserOp.and) t49) (Term.Apply (Term.Apply (Term.UOp UserOp.and) t29) (Term.Boolean true)))

/-- The proof: every checker command after the two assumptions, in order. -/
def proof : CCmdList :=
  CCmdList.cons (CCmd.step CRule.refl (CArgList.cons t28 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.bool_double_not_elim (CArgList.cons t48 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.nary_cong (CArgList.cons t54 CArgList.nil) (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))) <|
  CCmdList.cons (CCmd.assume_push t49) <|
  CCmdList.cons (CCmd.assume_push t64) <|
  CCmdList.cons (CCmd.assume_push t74) <|
  CCmdList.cons (CCmd.step CRule.dt_inst (CArgList.cons t78 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t38 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.chain_resolution (CArgList.cons t80 (CArgList.cons t82 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 8 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.cong (CArgList.cons t91 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.dt_inst (CArgList.cons t95 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t26 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 1 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.trans CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.process_scope (CArgList.cons t28 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t26 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.dt_split (CArgList.cons t38 CArgList.nil) CIndexList.nil) <|
  CCmdList.cons (CCmd.step CRule.chain_resolution (CArgList.cons t80 (CArgList.cons t82 CArgList.nil)) (CIndexList.cons 0 (CIndexList.cons 8 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.and_intro CArgList.nil (CIndexList.cons 0 (CIndexList.cons 2 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.modus_ponens CArgList.nil (CIndexList.cons 0 (CIndexList.cons 4 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step_pop CRule.scope CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.process_scope (CArgList.cons t28 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.implies_elim CArgList.nil (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.eq_resolve CArgList.nil (CIndexList.cons 0 (CIndexList.cons 3 CIndexList.nil))) <|
  CCmdList.cons (CCmd.step CRule.reordering (CArgList.cons t99 CArgList.nil) (CIndexList.cons 0 CIndexList.nil)) <|
  CCmdList.cons (CCmd.step CRule.chain_m_resolution (CArgList.cons (Term.Boolean false) (CArgList.cons t103 (CArgList.cons t107 CArgList.nil))) (CIndexList.cons 0 (CIndexList.cons 8 (CIndexList.cons 9 CIndexList.nil)))) <|
  CCmdList.nil

-- Sanity checks: the hand-built state chain agrees with `assumptions`/`proof`, and
-- the checker accepts the refutation.
#eval! decide (__eo_invoke_assume_list CState.nil assumptions = s2)
#eval! decide (__eo_invoke_cmd_list (__eo_invoke_assume_list CState.nil assumptions) proof = s31)
#eval! __eo_checker_is_refutation assumptions proof
#eval! logos_state_is_refutation s31

-- The checker accepts the proof: `eo_is_refutation` holds, exactly as in the
-- self-recursive case.
example : eo_is_refutation assumptions proof := by
  apply eo_is_refutation.intro
  native_decide

/-
The translation side conditions, by contrast, do NOT hold. A bare value of a mutual
type translates, but constructor/selector/tester terms over it translate to `None`.
These `#eval!`s witness the gap (every entry but `t26` is `SmtType.None`):
-/
#eval! ("t26  value of A", __smtx_typeof (__eo_to_smt t26))   -- Datatype ... (ok)
#eval! ("t8   ctor app b1(A)", __smtx_typeof (__eo_to_smt t8))    -- None
#eval! ("t17  ctor app mkA(B)", __smtx_typeof (__eo_to_smt t17))  -- None
#eval! ("t38  selector app", __smtx_typeof (__eo_to_smt t38))     -- None
#eval! ("t48  tester is-b0", __smtx_typeof (__eo_to_smt t48))     -- None
#eval! ("t29  assumption #1", __smtx_typeof (__eo_to_smt t29))    -- None
#eval! ("t49  assumption #2", __smtx_typeof (__eo_to_smt t49))    -- None

-- Both translation obligations are currently false (the leaves above are
-- decidably `None`). They are stated here, blocked on the sibling-`DatatypeTypeRef`
-- translation gap described in the header comment. Once mutual-datatype translation
-- is implemented, replace each `sorry` with the tactic block from `TestSimpleDt.lean`.
example : TranslatableAssumptionList assumptions := by
  sorry

example : CmdListTranslationOk proof := by
  sorry

end Cpc.Examples.TestSimpleDtMutual
