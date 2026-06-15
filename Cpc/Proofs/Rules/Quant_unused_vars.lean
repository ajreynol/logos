import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def qterm (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private theorem eq_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hEq : native_teq x y = true
  · simpa [native_teq] using hEq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    unfold __eo_requires at hReq
    simp [hEqFalse, native_ite] at hReq

private theorem body_ne_stuck_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    B ≠ Term.Stuck := by
  intro hReq hB
  subst B
  unfold __eo_requires at hReq
  by_cases hEq : native_teq x y = true
  · by_cases hStuck : native_teq x Term.Stuck = true
    · simp [hEq, hStuck, native_ite] at hReq
    · have hStuckFalse : native_teq x Term.Stuck = false := by
        cases h : native_teq x Term.Stuck <;> simp [h] at hStuck ⊢
      simp [hEq, hStuckFalse, native_ite] at hReq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    simp [hEqFalse, native_ite] at hReq

private theorem eo_or_eq_true_cases_local (x y : Term) :
    __eo_or x y = Term.Boolean true ->
    x = Term.Boolean true ∨ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_or] at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [native_or] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [__eo_requires, hNumNe, native_ite, native_teq] at h

private theorem eo_and_eq_true_cases_local (x y : Term) :
    __eo_and x y = Term.Boolean true ->
    x = Term.Boolean true ∧ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_and, __eo_requires, native_ite,
    native_teq, native_and, native_not, SmtEval.native_not] at h
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [hW] at h

private theorem contains_atomic_term_list_free_rec_vars_ne_stuck_of_false
    {t xs bvs : Term} :
    __contains_atomic_term_list_free_rec t xs bvs = Term.Boolean false ->
    xs ≠ Term.Stuck := by
  intro h hxs
  subst xs
  cases t <;> cases bvs <;>
    simp [__contains_atomic_term_list_free_rec] at h

private theorem get_unused_vars_ne_stuck_of_contains_false
    {Q x F G : Term} :
    __contains_atomic_term_list_free_rec G
        (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
      Term.Boolean false ->
    __get_unused_vars (qterm Q x F) G ≠ Term.Stuck :=
  contains_atomic_term_list_free_rec_vars_ne_stuck_of_false

private theorem get_unused_vars_fallback_shape_of_not_stuck
    (Q x F G : Term) :
    __eo_l_1___get_unused_vars (qterm Q x F) G ≠ Term.Stuck ->
    G = F ∧
      __eo_l_1___get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x := by
  intro hGet
  by_cases hGStuck : G = Term.Stuck
  · subst G
    simp [__eo_l_1___get_unused_vars] at hGet
  · have hReq :
        __eo_requires (__eo_eq F G) (Term.Boolean true)
            (__eo_list_setof Term.__eo_List_cons x) ≠
          Term.Stuck := by
      cases G <;>
        simp_all [qterm, __eo_l_1___get_unused_vars]
    have hG : G = F :=
      RuleProofs.eq_of_requires_eq_true_not_stuck F G
        (__eo_list_setof Term.__eo_List_cons x) hReq
    subst G
    constructor
    · rfl
    · simp [qterm, __eo_l_1___get_unused_vars, __eo_eq, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]

private theorem get_unused_vars_shape_of_not_stuck
    (Q x F G : Term) :
    __get_unused_vars (qterm Q x F) G ≠ Term.Stuck ->
    (G = F ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x) ∨
    ∃ y,
      G = qterm Q y F ∧
      __eo_list_minclude Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y =
        Term.Boolean true ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_diff Term.__eo_List_cons
          (__eo_list_setof Term.__eo_List_cons x) y := by
  intro hGet
  let G0 := G
  cases G with
  | Apply g F2 =>
      let G1 := Term.Apply g F2
      cases g with
      | Apply Q2 y =>
          let sx := __eo_list_setof Term.__eo_List_cons x
          let guard := __eo_and (__eo_eq Q Q2) (__eo_eq F F2)
          let branch :=
            __eo_requires (__eo_list_minclude Term.__eo_List_cons sx y)
              (Term.Boolean true)
              (__eo_list_diff Term.__eo_List_cons sx y)
          by_cases hGuardTrue : guard = Term.Boolean true
          · have hGetEqBranch :
                __get_unused_vars (qterm Q x F) ((Q2.Apply y).Apply F2) =
                  branch := by
              simp [__get_unused_vars, qterm, sx, guard, branch,
                hGuardTrue, __eo_ite, native_ite, native_teq]
            have hBranchNe : branch ≠ Term.Stuck := by
              intro hBranch
              exact hGet (by rw [hGetEqBranch, hBranch])
            have hIncl :
                __eo_list_minclude Term.__eo_List_cons sx y =
                  Term.Boolean true :=
              eq_of_requires_ne_stuck hBranchNe
            rcases eo_and_eq_true_cases_local
                (__eo_eq Q Q2) (__eo_eq F F2) hGuardTrue with
              ⟨hQ, hF⟩
            have hQ2 : Q2 = Q :=
              RuleProofs.eq_of_eo_eq_true Q Q2 hQ
            have hF2 : F2 = F :=
              RuleProofs.eq_of_eo_eq_true F F2 hF
            subst Q2
            subst F2
            right
            refine ⟨y, rfl, ?_, ?_⟩
            · simpa [sx] using hIncl
            · rw [hGetEqBranch]
              simp [branch, sx, hIncl, __eo_requires, native_ite, native_teq,
                native_not, SmtEval.native_not]
          · by_cases hGuardFalse : guard = Term.Boolean false
            · have hGetEqFallback :
                  __get_unused_vars (qterm Q x F) ((Q2.Apply y).Apply F2) =
                    __eo_l_1___get_unused_vars (qterm Q x F)
                      ((Q2.Apply y).Apply F2) := by
                simp [__get_unused_vars, qterm, guard,
                  hGuardFalse, __eo_ite, native_ite, native_teq]
              have hFallbackNe :
                  __eo_l_1___get_unused_vars (qterm Q x F)
                      ((Q2.Apply y).Apply F2) ≠
                    Term.Stuck := by
                intro hFallback
                exact hGet (by rw [hGetEqFallback, hFallback])
              rcases get_unused_vars_fallback_shape_of_not_stuck
                  Q x F ((Q2.Apply y).Apply F2) hFallbackNe with
                ⟨hGF, hFallbackEq⟩
              left
              refine ⟨hGF, ?_⟩
              rw [hGetEqFallback]
              exact hFallbackEq
            · have hGetStuck :
                  __get_unused_vars (qterm Q x F) ((Q2.Apply y).Apply F2) =
                    Term.Stuck := by
                simp [__get_unused_vars, qterm, guard,
                  hGuardTrue, hGuardFalse, __eo_ite, native_ite, native_teq]
              exact False.elim (hGet hGetStuck)
      | _ =>
          have hFallbackNe :
              __eo_l_1___get_unused_vars (qterm Q x F) G1 ≠
                Term.Stuck := by
            simpa [G1, __get_unused_vars, qterm] using hGet
          rcases get_unused_vars_fallback_shape_of_not_stuck
              Q x F G1 hFallbackNe with
            ⟨hGF, hFallbackEq⟩
          left
          refine ⟨by simpa [G1] using hGF, ?_⟩
          simpa [G1, __get_unused_vars, qterm] using hFallbackEq
  | _ =>
      have hFallbackNe :
          __eo_l_1___get_unused_vars (qterm Q x F) G0 ≠ Term.Stuck := by
        simpa [G0, __get_unused_vars, qterm] using hGet
      rcases get_unused_vars_fallback_shape_of_not_stuck Q x F G0 hFallbackNe with
        ⟨hGF, hFallbackEq⟩
      left
      refine ⟨by simpa [G0] using hGF, ?_⟩
      simpa [G0, __get_unused_vars, qterm] using hFallbackEq

private theorem quant_unused_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = qeq (qterm Q x F) G ∧
      (Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists) ∧
      __contains_atomic_term_list_free_rec G
        (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
          Term.Boolean false ∧
      __eo_prog_quant_unused_vars x1 = qeq (qterm Q x F) G := by
  intro hProg
  cases x1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply qHead F =>
                      cases qHead with
                      | Apply Q x =>
                          let v0 := qterm Q x F
                          let noFree :=
                            __contains_atomic_term_list_free_rec G
                              (__get_unused_vars v0 G) Term.__eo_List_nil
                          let inner :=
                            __eo_requires noFree (Term.Boolean false)
                              (qeq v0 G)
                          have hReq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner ≠ Term.Stuck := by
                            simpa [qeq, qterm, v0, noFree, inner,
                              __eo_prog_quant_unused_vars] using hProg
                          have hGuard :
                              __eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                  (__eo_eq Q (Term.UOp UserOp.exists)) =
                                Term.Boolean true :=
                            eq_of_requires_ne_stuck hReq
                          have hInnerNe : inner ≠ Term.Stuck :=
                            body_ne_stuck_of_requires_ne_stuck hReq
                          have hNoFree :
                              noFree = Term.Boolean false :=
                            eq_of_requires_ne_stuck hInnerNe
                          rcases eo_or_eq_true_cases_local
                              (__eo_eq Q (Term.UOp UserOp.forall))
                              (__eo_eq Q (Term.UOp UserOp.exists)) hGuard with
                            hForall | hExists
                          · have hQ : Q = Term.UOp UserOp.forall :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.forall) hForall).symm
                            subst Q
                            refine ⟨Term.UOp UserOp.forall, x, F, G, rfl,
                              Or.inl rfl, ?_, ?_⟩
                            · simpa [v0, qterm, noFree] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.forall) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.forall) x F) G
                              have hGuard' :
                                  __eo_or
                                      (__eo_eq (Term.UOp UserOp.forall)
                                        (Term.UOp UserOp.forall))
                                      (__eo_eq (Term.UOp UserOp.forall)
                                        (Term.UOp UserOp.exists)) =
                                    Term.Boolean true := by
                                simp [__eo_or, __eo_eq, native_or, native_teq]
                              have hNoFree' :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (qterm (Term.UOp UserOp.forall) x F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [v0, qterm, noFree] using hNoFree
                              have hNoFreeRaw :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (((Term.UOp UserOp.forall).Apply x).Apply F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [qterm] using hNoFree'
                              simp [qeq, qterm, __eo_prog_quant_unused_vars,
                                hGuard', hNoFreeRaw, __eo_requires, native_ite,
                                native_teq, native_not, SmtEval.native_not]
                          · have hQ : Q = Term.UOp UserOp.exists :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.exists) hExists).symm
                            subst Q
                            refine ⟨Term.UOp UserOp.exists, x, F, G, rfl,
                              Or.inr rfl, ?_, ?_⟩
                            · simpa [v0, qterm, noFree] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.exists) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.exists) x F) G
                              have hGuard' :
                                  __eo_or
                                      (__eo_eq (Term.UOp UserOp.exists)
                                        (Term.UOp UserOp.forall))
                                      (__eo_eq (Term.UOp UserOp.exists)
                                        (Term.UOp UserOp.exists)) =
                                    Term.Boolean true := by
                                simp [__eo_or, __eo_eq, native_or, native_teq]
                              have hNoFree' :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (qterm (Term.UOp UserOp.exists) x F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [v0, qterm, noFree] using hNoFree
                              have hNoFreeRaw :
                                  __contains_atomic_term_list_free_rec G
                                      (__get_unused_vars
                                        (((Term.UOp UserOp.exists).Apply x).Apply F) G)
                                      Term.__eo_List_nil =
                                    Term.Boolean false := by
                                simpa [qterm] using hNoFree'
                              simp [qeq, qterm, __eo_prog_quant_unused_vars,
                                hGuard', hNoFreeRaw, __eo_requires, native_ite,
                                native_teq, native_not, SmtEval.native_not]
                      | _ =>
                          simp [__eo_prog_quant_unused_vars] at hProg
                  | _ =>
                      simp [__eo_prog_quant_unused_vars] at hProg
              | _ =>
                  simp [__eo_prog_quant_unused_vars] at hProg
          | _ =>
              simp [__eo_prog_quant_unused_vars] at hProg
      | _ =>
          simp [__eo_prog_quant_unused_vars] at hProg
  | _ =>
      simp [__eo_prog_quant_unused_vars] at hProg

private theorem quant_unused_vars_has_smt_translation
    (A : Term)
    (hTransA : RuleProofs.eo_has_smt_translation A)
    (hTy : __eo_typeof (__eo_prog_quant_unused_vars A) = Term.Bool) :
    RuleProofs.eo_has_smt_translation (__eo_prog_quant_unused_vars A) := by
  have hProg : __eo_prog_quant_unused_vars A ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases quant_unused_shape_of_not_stuck A hProg with
    ⟨Q, x, F, G, hA, _hQ, _hNoFree, hProgEq⟩
  rw [hProgEq]
  simpa [hA] using hTransA

theorem cmd_step_quant_unused_vars_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_unused_vars args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_unused_vars args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_unused_vars args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using hCmdTrans
              have hProgTy :
                  __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool
                  at hResultTy
                exact hResultTy
              refine ⟨?_, ?_⟩
              · sorry
              · simpa [premiseTermList] using
                  quant_unused_vars_has_smt_translation a1 hTransA1 hProgTy
