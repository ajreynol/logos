import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem set_singleton_arg_non_none (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hSingleton hNone
  change __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt x)) ≠ SmtType.None at hSingleton
  rw [__smtx_typeof.eq_121] at hSingleton
  exact (Smtm.type_wf_non_none <|
      Smtm.smtx_typeof_guard_wf_wf_of_non_none
        (__smtx_typeof (__eo_to_smt x))
        (SmtType.Set (__smtx_typeof (__eo_to_smt x)))
        hSingleton) hNone

private theorem set_singleton_type_of_non_none (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton x)) =
        SmtType.Set (__smtx_typeof (__eo_to_smt x)) := by
  intro h
  change __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt x)) ≠ SmtType.None at h
  change __smtx_typeof (SmtTerm.set_singleton (__eo_to_smt x)) =
    SmtType.Set (__smtx_typeof (__eo_to_smt x))
  rw [__smtx_typeof.eq_121]
  exact Smtm.smtx_typeof_guard_wf_of_non_none
    (__smtx_typeof (__eo_to_smt x))
    (SmtType.Set (__smtx_typeof (__eo_to_smt x))) (by
      simpa [__smtx_typeof.eq_121] using h)

private theorem singleton_rel_implies_rel
    {v w : SmtValue}
    (h :
      RuleProofs.smt_value_rel
        (__smtx_model_eval_set_singleton v)
        (__smtx_model_eval_set_singleton w)) :
    RuleProofs.smt_value_rel v w := by
  let T := __smtx_typeof_value v
  let mv :=
    SmtMap.cons v (SmtValue.Boolean true)
      (SmtMap.default T (SmtValue.Boolean false))
  let mw :=
    SmtMap.cons w (SmtValue.Boolean true)
      (SmtMap.default (__smtx_typeof_value w) (SmtValue.Boolean false))
  have hExt :
      ∀ x : SmtValue,
        native_veq
          (__smtx_msm_lookup T mv x)
          (__smtx_msm_lookup T mw x) = true := by
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at h
    change __smtx_model_eval_eq (SmtValue.Set mv) (SmtValue.Set mw) =
      SmtValue.Boolean true at h
    simp [__smtx_model_eval_eq, __smtx_value_eq, __smtx_typeof_value,
      __smtx_typeof_map_value, __smtx_map_to_set_type, T, mv, mw,
      native_Teq, native_ite] at h
    by_cases hExt :
        ∀ x : SmtValue,
          native_veq
            (__smtx_msm_lookup T mv x)
            (__smtx_msm_lookup T mw x) = true
    · exact hExt
    · exact False.elim (hExt h)
  have hLookup := hExt v
  have hWV : __smtx_value_eq T w v = true := by
    cases hEq : __smtx_value_eq T w v
    · exfalso
      simpa [__smtx_msm_lookup, RuleProofs.smtx_value_eq_refl_typed,
        hEq, __smtx_value_eq, native_veq, native_ite, T, mv, mw] using hLookup
    · rfl
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  simpa [__smtx_model_eval_eq, T] using
    RuleProofs.smtx_value_eq_symm_typed T hWV

private theorem typed___eo_prog_sets_singleton_inj_impl (x1 : Term) :
    RuleProofs.eo_has_bool_type x1 ->
    __eo_prog_sets_singleton_inj (Proof.pf x1) ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_prog_sets_singleton_inj (Proof.pf x1)) := by
  intro hXBool hProg
  cases x1 with
  | Apply f rhs =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhs with
                  | Apply f1 a =>
                      cases f1 with
                      | UOp op1 =>
                          cases op1 with
                          | set_singleton =>
                              cases rhs with
                              | Apply f2 b =>
                                  cases f2 with
                                  | UOp op2 =>
                                      cases op2 with
                                      | set_singleton =>
                                          have hPremBool :
                                              RuleProofs.eo_has_bool_type
                                                (Term.Apply
                                                  (Term.Apply Term.eq (Term.Apply Term.set_singleton a))
                                                  (Term.Apply Term.set_singleton b)) := by
                                            simpa using hXBool
                                          rcases
                                              RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                                                (Term.Apply Term.set_singleton a)
                                                (Term.Apply Term.set_singleton b)
                                                hPremBool with
                                            ⟨hSingletonTyEq, hSingletonNN⟩
                                          have hSingletonNNB :
                                              __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton b)) ≠
                                                SmtType.None := by
                                            rwa [← hSingletonTyEq]
                                          have hATrans : RuleProofs.eo_has_smt_translation a :=
                                            set_singleton_arg_non_none a hSingletonNN
                                          have hBTrans : RuleProofs.eo_has_smt_translation b :=
                                            set_singleton_arg_non_none b hSingletonNNB
                                          have hSingletonATy :
                                              __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton a)) =
                                                SmtType.Set (__smtx_typeof (__eo_to_smt a)) :=
                                            set_singleton_type_of_non_none a hSingletonNN
                                          have hSingletonBTy :
                                              __smtx_typeof (__eo_to_smt (Term.Apply Term.set_singleton b)) =
                                                SmtType.Set (__smtx_typeof (__eo_to_smt b)) :=
                                            set_singleton_type_of_non_none b hSingletonNNB
                                          have hABTy :
                                              __smtx_typeof (__eo_to_smt a) =
                                                __smtx_typeof (__eo_to_smt b) := by
                                            have hSetTy :
                                                SmtType.Set (__smtx_typeof (__eo_to_smt a)) =
                                                  SmtType.Set (__smtx_typeof (__eo_to_smt b)) := by
                                              rw [← hSingletonATy, ← hSingletonBTy]
                                              exact hSingletonTyEq
                                            injection hSetTy with hABTy
                                          simpa [__eo_prog_sets_singleton_inj] using
                                            RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                              a b hABTy hATrans
                                      | _ =>
                                          simp [__eo_prog_sets_singleton_inj] at hProg
                                  | _ =>
                                      simp [__eo_prog_sets_singleton_inj] at hProg
                              | _ =>
                                  simp [__eo_prog_sets_singleton_inj] at hProg
                          | _ =>
                              simp [__eo_prog_sets_singleton_inj] at hProg
                      | _ =>
                          simp [__eo_prog_sets_singleton_inj] at hProg
                  | _ =>
                      simp [__eo_prog_sets_singleton_inj] at hProg
              | _ =>
                  simp [__eo_prog_sets_singleton_inj] at hProg
          | _ =>
              simp [__eo_prog_sets_singleton_inj] at hProg
      | _ =>
          simp [__eo_prog_sets_singleton_inj] at hProg
  | _ =>
      simp [__eo_prog_sets_singleton_inj] at hProg

private theorem singleton_term_rel_implies_rel
    (M : SmtModel) (a b : Term)
    (h :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.set_singleton a)))
        (__smtx_model_eval M (__eo_to_smt (Term.Apply Term.set_singleton b)))) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt a))
      (__smtx_model_eval M (__eo_to_smt b)) := by
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt a)))
    (__smtx_model_eval M (SmtTerm.set_singleton (__eo_to_smt b))) at h
  rw [__smtx_model_eval.eq_121, __smtx_model_eval.eq_121] at h
  exact singleton_rel_implies_rel h

private theorem facts___eo_prog_sets_singleton_inj_impl
    (M : SmtModel) (x1 : Term) :
    eo_interprets M x1 true ->
    __eo_prog_sets_singleton_inj (Proof.pf x1) ≠ Term.Stuck ->
    eo_interprets M (__eo_prog_sets_singleton_inj (Proof.pf x1)) true := by
  intro hXTrue hProg
  have hXBool : RuleProofs.eo_has_bool_type x1 :=
    RuleProofs.eo_has_bool_type_of_interprets_true M x1 hXTrue
  have hOutBool :
      RuleProofs.eo_has_bool_type (__eo_prog_sets_singleton_inj (Proof.pf x1)) :=
    typed___eo_prog_sets_singleton_inj_impl x1 hXBool hProg
  cases x1 with
  | Apply f rhs =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhs with
                  | Apply f1 a =>
                      cases f1 with
                      | UOp op1 =>
                          cases op1 with
                          | set_singleton =>
                              cases rhs with
                              | Apply f2 b =>
                                  cases f2 with
                                  | UOp op2 =>
                                      cases op2 with
                                      | set_singleton =>
                                          have hPremTrue :
                                              eo_interprets M
                                                (Term.Apply
                                                  (Term.Apply Term.eq (Term.Apply Term.set_singleton a))
                                                  (Term.Apply Term.set_singleton b)) true := by
                                            simpa using hXTrue
                                          have hSetRel :
                                              RuleProofs.smt_value_rel
                                                (__smtx_model_eval M
                                                  (__eo_to_smt (Term.Apply Term.set_singleton a)))
                                                (__smtx_model_eval M
                                                  (__eo_to_smt (Term.Apply Term.set_singleton b))) :=
                                            RuleProofs.eo_interprets_eq_rel M
                                              (Term.Apply Term.set_singleton a)
                                              (Term.Apply Term.set_singleton b)
                                              hPremTrue
                                          have hArgRel :
                                              RuleProofs.smt_value_rel
                                                (__smtx_model_eval M (__eo_to_smt a))
                                                (__smtx_model_eval M (__eo_to_smt b)) :=
                                            singleton_term_rel_implies_rel M a b hSetRel
                                          simpa [__eo_prog_sets_singleton_inj] using
                                            RuleProofs.eo_interprets_eq_of_rel M a b hOutBool hArgRel
                                      | _ =>
                                          simp [__eo_prog_sets_singleton_inj] at hProg
                                  | _ =>
                                      simp [__eo_prog_sets_singleton_inj] at hProg
                              | _ =>
                                  simp [__eo_prog_sets_singleton_inj] at hProg
                          | _ =>
                              simp [__eo_prog_sets_singleton_inj] at hProg
                      | _ =>
                          simp [__eo_prog_sets_singleton_inj] at hProg
                  | _ =>
                      simp [__eo_prog_sets_singleton_inj] at hProg
              | _ =>
                  simp [__eo_prog_sets_singleton_inj] at hProg
          | _ =>
              simp [__eo_prog_sets_singleton_inj] at hProg
      | _ =>
          simp [__eo_prog_sets_singleton_inj] at hProg
  | _ =>
      simp [__eo_prog_sets_singleton_inj] at hProg

theorem cmd_step_sets_singleton_inj_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.sets_singleton_inj args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.sets_singleton_inj args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.sets_singleton_inj args premises) :=
by
  intro _hCmdTrans hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.sets_singleton_inj args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons n1 premises =>
          cases premises with
          | nil =>
              let X1 := __eo_state_proven_nth s n1
              have hProgSingleton :
                  __eo_prog_sets_singleton_inj (Proof.pf X1) ≠ Term.Stuck := by
                change __eo_prog_sets_singleton_inj
                  (Proof.pf (__eo_state_proven_nth s n1)) ≠ Term.Stuck at hProg
                simpa [X1] using hProg
              refine ⟨?_, ?_⟩
              · intro hTrue
                change eo_interprets M (__eo_prog_sets_singleton_inj (Proof.pf X1)) true
                exact facts___eo_prog_sets_singleton_inj_impl M X1
                  (hTrue X1 (by simp [X1, premiseTermList]))
                  hProgSingleton
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (by
                    change RuleProofs.eo_has_bool_type
                      (__eo_prog_sets_singleton_inj (Proof.pf X1))
                    exact typed___eo_prog_sets_singleton_inj_impl X1
                      (hPremisesBool X1 (by simp [X1, premiseTermList]))
                      hProgSingleton)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
  | cons _ _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
