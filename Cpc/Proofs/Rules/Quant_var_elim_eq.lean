import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CongSupport
import Cpc.Proofs.RuleSupport.CnfSupport
import Cpc.Proofs.Rules.Instantiate

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open SubstitutePreservationSupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace QuantVarElimEqRule

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def qnot (A : Term) : Term :=
  Term.Apply (Term.UOp UserOp.not) A

private def qor (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B

private def qforall (xs F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F

private def qcons (x xs : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons x) xs

private def qsingle (x : Term) : Term :=
  qcons x Term.__eo_List_nil

private def qsubst (body x t : Term) : Term :=
  __substitute_simul_rec (Term.Boolean false) body
    (qsingle x) (qsingle t) Term.__eo_List_nil

private def quantVarElimEqFormula (x F G : Term) : Term :=
  qeq (qforall (qsingle x) F) G

private inductive QuantVarElimEqCase (x F G : Term) : Prop where
  | diseq (t : Term) :
      F = qnot (qeq x t) ->
      __contains_atomic_term_list_free_rec t (qsingle x) Term.__eo_List_nil =
        Term.Boolean false ->
      G = qsubst (Term.Boolean false) x t ->
      QuantVarElimEqCase x F G
  | orTail (t tail : Term) :
      F = qor (qnot (qeq x t)) tail ->
      __contains_atomic_term_list_free_rec t (qsingle x) Term.__eo_List_nil =
        Term.Boolean false ->
      G = qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail) x t ->
      QuantVarElimEqCase x F G

private theorem eo_eq_self_true (x : Term) (hx : x ≠ Term.Stuck) :
    __eo_eq x x = Term.Boolean true := by
  cases x <;> simp [__eo_eq, native_teq] at hx ⊢

private theorem l1_quant_var_elim_eq_or_eq
    (x t tail : Term)
    (hx : x ≠ Term.Stuck)
    (hNoFree :
      __contains_atomic_term_list_free_rec t (qsingle x) Term.__eo_List_nil =
        Term.Boolean false) :
    __eo_l_1___mk_quant_var_elim_eq x (qor (qnot (qeq x t)) tail) =
      qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail) x t := by
  have hEq : __eo_eq x x = Term.Boolean true :=
    eo_eq_self_true x hx
  have hNoFree' :
      __contains_atomic_term_list_free_rec t
          ((Term.__eo_List_cons.Apply x).Apply Term.__eo_List_nil)
          Term.__eo_List_nil =
        Term.Boolean false := by
    simpa [qsingle, qcons] using hNoFree
  simp [__eo_l_1___mk_quant_var_elim_eq, qeq, qnot, qor, qsingle, qcons,
    qsubst, hEq, hNoFree', __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]

private theorem mk_quant_var_elim_eq_diseq_eq
    (x t : Term)
    (hx : x ≠ Term.Stuck)
    (hNoFree :
      __contains_atomic_term_list_free_rec t (qsingle x) Term.__eo_List_nil =
        Term.Boolean false) :
    __mk_quant_var_elim_eq x (qnot (qeq x t)) =
      qsubst (Term.Boolean false) x t := by
  have hEq : __eo_eq x x = Term.Boolean true :=
    eo_eq_self_true x hx
  have hNoFree' :
      __contains_atomic_term_list_free_rec t
          ((Term.__eo_List_cons.Apply x).Apply Term.__eo_List_nil)
          Term.__eo_List_nil =
        Term.Boolean false := by
    simpa [qsingle, qcons] using hNoFree
  simp [__mk_quant_var_elim_eq, qeq, qnot, qsingle, qcons, qsubst, hEq,
    hNoFree', __eo_ite, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]

private theorem mk_quant_var_elim_eq_or_eq
    (x t tail : Term)
    (hx : x ≠ Term.Stuck)
    (hNoFree :
      __contains_atomic_term_list_free_rec t (qsingle x) Term.__eo_List_nil =
        Term.Boolean false) :
    __mk_quant_var_elim_eq x (qor (qnot (qeq x t)) tail) =
      qsubst (__eo_list_singleton_elim (Term.UOp UserOp.or) tail) x t := by
  simpa [__mk_quant_var_elim_eq, qeq, qnot, qor] using
    l1_quant_var_elim_eq_or_eq x t tail hx hNoFree

private theorem singleton_subst_actuals_of_eq_bool
    (x t F : Term)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation (qforall (qsingle x) F))
    (hEqBool : RuleProofs.eo_has_bool_type (qeq x t)) :
    EoListAllHaveSmtTranslation (qsingle t) ∧
      SubstActualsHaveSmtTypes (qsingle x) (qsingle t) := by
  rcases forall_binders_env_of_has_smt_translation
      (qsingle x) F hForallTrans with
    ⟨vars, hEnv⟩
  have hWf :=
    forall_binder_types_wf_of_has_smt_translation hForallTrans hEnv
  change EoVarEnv ((Term.__eo_List_cons.Apply x).Apply Term.__eo_List_nil)
    vars at hEnv
  cases hEnv with
  | cons hTail =>
      rename_i s T tailVars
      cases hTail
      have hHeadWf :
          __smtx_type_wf (__eo_to_smt_type T) = true :=
        hWf s T (by simp)
      have hTypes :=
        RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          (Term.Var (Term.String s) T) t hEqBool
      have hTTrans : RuleProofs.eo_has_smt_translation t := by
        intro hNone
        exact hTypes.2 (by rw [hTypes.1, hNone])
      have hTy :
          __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type T := by
        simpa [smtx_typeof_var_term_eq, __smtx_typeof_guard_wf, hHeadWf,
          native_ite] using hTypes.1.symm
      refine ⟨?_, ?_⟩
      · simpa [qsingle, qcons, EoListAllHaveSmtTranslation] using
          And.intro hTTrans True.intro
      · exact SubstActualsHaveSmtTypes.cons hHeadWf hTTrans hTy
          (SubstActualsHaveSmtTypes.nil Term.__eo_List_nil)

private theorem qsubst_eval_eq_push
    (M : SmtModel) (hM : model_total_typed M)
    (x t F body : Term)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation (qforall (qsingle x) F))
    (hEqBool : RuleProofs.eo_has_bool_type (qeq x t))
    (hBodyTrans : RuleProofs.eo_has_smt_translation body)
    (hSubstTrans :
      RuleProofs.eo_has_smt_translation (qsubst body x t)) :
    __smtx_model_eval M (__eo_to_smt (qsubst body x t)) =
      __smtx_model_eval (InstantiateRule.pushSubstModel M (qsingle x) (qsingle t))
        (__eo_to_smt body) := by
  rcases singleton_subst_actuals_of_eq_bool x t F hForallTrans hEqBool with
    ⟨hTs, hActuals⟩
  simpa [qsubst] using
      InstantiateRule.substitute_simul_eval M hM body (qsingle x) (qsingle t)
        hBodyTrans hTs hActuals hSubstTrans

private theorem qforall_single_has_bool_type_of_has_smt_translation
    (x F : Term)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation (qforall (qsingle x) F)) :
    RuleProofs.eo_has_bool_type (qforall (qsingle x) F) := by
  have hXsNonNil :
      qsingle x ≠ Term.__eo_List_nil :=
    forall_binders_non_nil_of_has_smt_translation (qsingle x) F
      hForallTrans
  have hNN :
      __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists (qsingle x) (SmtTerm.not (__eo_to_smt F)))) ≠
        SmtType.None := by
    simpa [qforall, eo_to_smt_forall_eq_of_non_nil (qsingle x) F hXsNonNil]
      using hForallTrans
  unfold RuleProofs.eo_has_bool_type
  rw [qforall, eo_to_smt_forall_eq_of_non_nil (qsingle x) F hXsNonNil]
  exact smtx_typeof_not_eq_bool_of_non_none
    (__eo_to_smt_exists (qsingle x) (SmtTerm.not (__eo_to_smt F))) hNN

private theorem qeq_true_in_single_subst_model
    (M : SmtModel) (hM : model_total_typed M)
    (x t F : Term)
    (hForallTrans :
      RuleProofs.eo_has_smt_translation (qforall (qsingle x) F))
    (hEqBool : RuleProofs.eo_has_bool_type (qeq x t))
    (hNoFree :
      __contains_atomic_term_list_free_rec t (qsingle x) Term.__eo_List_nil =
        Term.Boolean false) :
    eo_interprets
      (InstantiateRule.pushSubstModel M (qsingle x) (qsingle t))
      (qeq x t) true := by
  rcases forall_binders_env_of_has_smt_translation
      (qsingle x) F hForallTrans with
    ⟨vars, hEnv⟩
  change EoVarEnv ((Term.__eo_List_cons.Apply x).Apply Term.__eo_List_nil)
    vars at hEnv
  cases hEnv with
  | cons hTail =>
      rename_i s T tailVars
      cases hTail
      let N := InstantiateRule.pushSubstModel M
        (qsingle (Term.Var (Term.String s) T)) (qsingle t)
      have hTypes :=
        RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
          (Term.Var (Term.String s) T) t hEqBool
      have hTTrans : RuleProofs.eo_has_smt_translation t := by
        intro hNone
        exact hTypes.2 (by rw [hTypes.1, hNone])
      have hEvalX :
          __smtx_model_eval N
              (__eo_to_smt (Term.Var (Term.String s) T)) =
            __smtx_model_eval M (__eo_to_smt t) := by
        simp [N, InstantiateRule.pushSubstModel, qsingle, qcons,
          native_model_var_lookup, native_model_push]
      have hNoFree' :
          __contains_atomic_term_list_free_rec t
              (qsingle (Term.Var (Term.String s) T)) Term.__eo_List_nil =
            Term.Boolean false := by
        simpa [qsingle, qcons] using hNoFree
      have hEvalT :
          __smtx_model_eval N (__eo_to_smt t) =
            __smtx_model_eval M (__eo_to_smt t) := by
        have hExcept :
            EoVarEnvPerm (qsingle (Term.Var (Term.String s) T))
              ([(s, T)] : List EoVarKey) :=
          EoVarEnvPerm.of_exact (EoVarEnv.cons EoVarEnv.nil)
        have hBound :
            EoVarEnvPerm Term.__eo_List_nil ([] : List EoVarKey) :=
          EoVarEnvPerm.of_exact EoVarEnv.nil
        have hAgree :
            model_agrees_except_on_env
              ([(s, __eo_to_smt_type T)] : List SmtVarKey) []
              N M := by
          simpa [N, qsingle, qcons, EoVarKey.toSmt] using
            InstantiateRule.pushSubstModel_agrees_except M
              (qsingle t) (EoVarEnv.cons EoVarEnv.nil)
        exact
          smt_model_eval_eq_of_contains_atomic_term_list_free_rec_false_mapped
            hExcept hBound hTTrans hNoFree' hAgree
      apply RuleProofs.eo_interprets_eq_of_rel N
        (Term.Var (Term.String s) T) t hEqBool
      rw [hEvalX, hEvalT]
      exact RuleProofs.smt_value_rel_refl
        (__smtx_model_eval M (__eo_to_smt t))

private theorem quant_var_elim_eq_shape_of_not_stuck
    (a1 : Term) :
    __eo_prog_quant_var_elim_eq a1 ≠ Term.Stuck ->
    ∃ x F G,
      a1 = quantVarElimEqFormula x F G ∧
      __mk_quant_var_elim_eq x F = G ∧
      __eo_prog_quant_var_elim_eq a1 = quantVarElimEqFormula x F G := by
  intro hProg
  cases a1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply forallHead F =>
                      cases forallHead with
                      | Apply forallOp xs =>
                          cases forallOp with
                          | UOp opForall =>
                              cases opForall with
                              | «forall» =>
                                  cases xs with
                                  | Apply consHead nilTerm =>
                                      cases consHead with
                                      | Apply consOp x =>
                                          cases consOp <;>
                                            try simp [__eo_prog_quant_var_elim_eq,
                                              quantVarElimEqFormula, qeq, qforall,
                                              qsingle, qcons] at hProg
                                          case __eo_List_cons =>
                                            cases nilTerm <;>
                                              try simp [__eo_prog_quant_var_elim_eq,
                                                quantVarElimEqFormula, qeq, qforall,
                                                qsingle, qcons] at hProg
                                            case __eo_List_nil =>
                                              let formula := quantVarElimEqFormula x F G
                                              let guard := __mk_quant_var_elim_eq x F
                                              have hReqNe :
                                                  __eo_requires guard G formula ≠
                                                    Term.Stuck := by
                                                simpa [formula, guard,
                                                  __eo_prog_quant_var_elim_eq,
                                                  quantVarElimEqFormula, qeq,
                                                  qforall, qsingle, qcons] using hProg
                                              have hGuard : guard = G :=
                                                instantiate_eo_requires_arg_eq_of_ne_stuck
                                                  hReqNe
                                              have hProgEq :
                                                  __eo_prog_quant_var_elim_eq formula =
                                                    formula := by
                                                change __eo_requires guard G formula =
                                                  formula
                                                exact
                                                  instantiate_eo_requires_result_eq_of_ne_stuck
                                                    hReqNe
                                              exact ⟨x, F, G, rfl, by simpa [guard] using hGuard,
                                                hProgEq⟩
                                      | _ =>
                                          simp [__eo_prog_quant_var_elim_eq] at hProg
                                  | _ =>
                                      simp [__eo_prog_quant_var_elim_eq] at hProg
                              | _ =>
                                  simp [__eo_prog_quant_var_elim_eq] at hProg
                          | _ =>
                              simp [__eo_prog_quant_var_elim_eq] at hProg
                      | _ =>
                          simp [__eo_prog_quant_var_elim_eq] at hProg
                  | _ =>
                      simp [__eo_prog_quant_var_elim_eq] at hProg
              | _ =>
                  simp [__eo_prog_quant_var_elim_eq] at hProg
          | _ =>
              simp [__eo_prog_quant_var_elim_eq] at hProg
      | _ =>
          simp [__eo_prog_quant_var_elim_eq] at hProg
  | _ =>
      simp [__eo_prog_quant_var_elim_eq] at hProg

private theorem quant_var_elim_eq_formula_true
    (M : SmtModel) (hM : model_total_typed M)
    (x F G : Term) :
    RuleProofs.eo_has_smt_translation
        (quantVarElimEqFormula x F G) ->
    __eo_typeof (quantVarElimEqFormula x F G) = Term.Bool ->
    __mk_quant_var_elim_eq x F = G ->
    eo_interprets M (quantVarElimEqFormula x F G) true := by
  sorry

end QuantVarElimEqRule

theorem cmd_step_quant_var_elim_eq_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_var_elim_eq args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_var_elim_eq args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_var_elim_eq args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_var_elim_eq args premises ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using
                  hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_var_elim_eq a1 ≠ Term.Stuck := by
                change __eo_prog_quant_var_elim_eq a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases QuantVarElimEqRule.quant_var_elim_eq_shape_of_not_stuck
                  a1 hProgQuant with
                ⟨x, F, G, ha1, hMk, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (QuantVarElimEqRule.quantVarElimEqFormula x F G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof
                      (QuantVarElimEqRule.quantVarElimEqFormula x F G) =
                    Term.Bool := by
                change __eo_typeof (__eo_prog_quant_var_elim_eq a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (QuantVarElimEqRule.quantVarElimEqFormula x F G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (QuantVarElimEqRule.quantVarElimEqFormula x F G)
                  hTransFormula hFormulaType
              have hFact :
                  eo_interprets M
                    (QuantVarElimEqRule.quantVarElimEqFormula x F G) true :=
                QuantVarElimEqRule.quant_var_elim_eq_formula_true M hM x F G
                  hTransFormula hFormulaType hMk
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_var_elim_eq a1) true
                rw [hProgEq]
                exact hFact
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_var_elim_eq a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
