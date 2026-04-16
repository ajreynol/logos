import Cpc.Proofs.ArraySupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem prog_array_read_over_write2_eq
    (t1 i1 j1 e1 i2 j2 : Term)
    (hT1NotStuck : t1 ≠ Term.Stuck)
    (hI1NotStuck : i1 ≠ Term.Stuck)
    (hJ1NotStuck : j1 ≠ Term.Stuck)
    (hE1NotStuck : e1 ≠ Term.Stuck) :
    __eo_prog_array_read_over_write2 t1 i1 j1 e1
      (Proof.pf
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.eq i2) j2))
          (Term.Boolean false))) =
      __eo_requires (__eo_and (__eo_eq i1 i2) (__eo_eq j1 j2)) (Term.Boolean true)
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.select
                (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) j1))
          (Term.Apply (Term.Apply Term.select t1) j1)) := by
  by_cases hT : t1 = Term.Stuck
  · contradiction
  · by_cases hI : i1 = Term.Stuck
    · contradiction
    · by_cases hJ : j1 = Term.Stuck
      · contradiction
      · by_cases hE : e1 = Term.Stuck
        · contradiction
        · simp [__eo_prog_array_read_over_write2]

private theorem typed___eo_prog_array_read_over_write2_impl
    (t1 i1 j1 e1 p1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation j1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  __eo_typeof (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) := by
  intro hT1Trans hI1Trans hJ1Trans hE1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hProg :
      __eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases p1 with
  | Apply f pRhs =>
      cases f with
      | Apply g pLhs =>
          cases g with
          | eq =>
              cases pLhs with
              | Apply f2 j2 =>
                  cases f2 with
                  | Apply g2 i2 =>
                      cases g2 with
                      | eq =>
                          cases pRhs with
                          | Boolean b =>
                              cases b with
                              | false =>
                                  rw [prog_array_read_over_write2_eq
                                        t1 i1 j1 e1 i2 j2
                                        hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck] at hProg hResultTy
                                  let lhs :=
                                    Term.Apply
                                      (Term.Apply Term.select
                                        (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                      j1
                                  let rhs := Term.Apply (Term.Apply Term.select t1) j1
                                  let body := Term.Apply (Term.Apply Term.eq lhs) rhs
                                  have hAlign :
                                      i2 = i1 ∧ j2 = j1 :=
                                    RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                      i1 j1 i2 j2 body hProg
                                  have hi2 : i2 = i1 := hAlign.1
                                  have hj2 : j2 = j1 := hAlign.2
                                  subst i2
                                  subst j2
                                  simp [body, lhs, rhs, __eo_requires, __eo_and, __eo_eq,
                                    native_ite, native_teq, native_not,
                                    SmtEval.native_not] at hResultTy
                                  have hTypesNotStuck :=
                                    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                      (__eo_typeof lhs) (__eo_typeof rhs) hResultTy
                                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                                    hTypesNotStuck.1
                                  have hRhsNotStuck : __eo_typeof rhs ≠ Term.Stuck :=
                                    hTypesNotStuck.2
                                  have hStoreNotStuck :
                                      __eo_typeof
                                        (Term.Apply
                                          (Term.Apply
                                            (Term.Apply Term.store t1) i1) e1) ≠
                                        Term.Stuck := by
                                    intro hStoreStuck
                                    change __eo_typeof_select
                                        (__eo_typeof
                                          (Term.Apply
                                            (Term.Apply
                                              (Term.Apply Term.store t1) i1) e1))
                                        (__eo_typeof j1) ≠ Term.Stuck at hLhsNotStuck
                                    rw [hStoreStuck] at hLhsNotStuck
                                    simp [__eo_typeof_select] at hLhsNotStuck
                                  have hT1TyI :
                                      __eo_typeof t1 =
                                        Term.Apply (Term.Apply Term.Array (__eo_typeof i1))
                                          (__eo_typeof e1) := by
                                    change __eo_typeof_store (__eo_typeof t1) (__eo_typeof i1)
                                        (__eo_typeof e1) ≠ Term.Stuck at hStoreNotStuck
                                    exact RuleProofs.eo_typeof_store_not_stuck_implies_array
                                      (__eo_typeof t1) (__eo_typeof i1) (__eo_typeof e1)
                                      hStoreNotStuck
                                  have hT1TyJ :
                                      ∃ E : Term,
                                        __eo_typeof t1 =
                                          Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) E := by
                                    change __eo_typeof_select (__eo_typeof t1) (__eo_typeof j1) ≠
                                        Term.Stuck at hRhsNotStuck
                                    exact RuleProofs.eo_typeof_select_not_stuck_implies_array
                                      (__eo_typeof t1) (__eo_typeof j1) hRhsNotStuck
                                  rcases hT1TyJ with ⟨E, hT1TyJ⟩
                                  have hSmtT1I :
                                      __smtx_typeof (__eo_to_smt t1) =
                                        SmtType.Map (__eo_to_smt_type (__eo_typeof i1))
                                          (__eo_to_smt_type (__eo_typeof e1)) :=
                                    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
                                      t1 _ (__eo_to_smt t1) rfl hT1Trans hT1TyI
                                  have hSmtT1J :
                                      __smtx_typeof (__eo_to_smt t1) =
                                        SmtType.Map (__eo_to_smt_type (__eo_typeof j1))
                                          (__eo_to_smt_type E) :=
                                    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
                                      t1 _ (__eo_to_smt t1) rfl hT1Trans hT1TyJ
                                  have hSmtI1 :
                                      __smtx_typeof (__eo_to_smt i1) =
                                        __eo_to_smt_type (__eo_typeof i1) :=
                                    TranslationProofs.eo_to_smt_typeof_matches_translation i1 hI1Trans
                                  have hSmtJ1 :
                                      __smtx_typeof (__eo_to_smt j1) =
                                        __eo_to_smt_type (__eo_typeof j1) :=
                                    TranslationProofs.eo_to_smt_typeof_matches_translation j1 hJ1Trans
                                  have hSmtE1 :
                                      __smtx_typeof (__eo_to_smt e1) =
                                        __eo_to_smt_type (__eo_typeof e1) :=
                                    TranslationProofs.eo_to_smt_typeof_matches_translation e1 hE1Trans
                                  have hMapEq :
                                      SmtType.Map (__eo_to_smt_type (__eo_typeof i1))
                                        (__eo_to_smt_type (__eo_typeof e1)) =
                                      SmtType.Map (__eo_to_smt_type (__eo_typeof j1))
                                        (__eo_to_smt_type E) :=
                                    hSmtT1I.symm.trans hSmtT1J
                                  have hIndexTy :
                                      __eo_to_smt_type (__eo_typeof i1) =
                                        __eo_to_smt_type (__eo_typeof j1) := by
                                    injection hMapEq with hIndexTy _
                                    exact hIndexTy
                                  have hSmtJ1I :
                                      __smtx_typeof (__eo_to_smt j1) =
                                        __eo_to_smt_type (__eo_typeof i1) := by
                                    rw [hSmtJ1, hIndexTy.symm]
                                  have hLhsTy :
                                      __smtx_typeof (__eo_to_smt lhs) =
                                        __eo_to_smt_type (__eo_typeof e1) := by
                                    rw [RuleProofs.eo_to_smt_select_eq, RuleProofs.eo_to_smt_store_eq]
                                    simp [lhs, __smtx_typeof, __smtx_typeof_select,
                                      __smtx_typeof_store, __smtx_typeof_guard, native_ite,
                                      native_Teq, hSmtT1I, hSmtI1, hSmtE1, hSmtJ1I]
                                  have hRhsTy :
                                      __smtx_typeof (__eo_to_smt rhs) =
                                        __eo_to_smt_type (__eo_typeof e1) := by
                                    rw [RuleProofs.eo_to_smt_select_eq]
                                    simp [rhs, __smtx_typeof, __smtx_typeof_select,
                                      __smtx_typeof_guard, native_ite, native_Teq,
                                      hSmtT1I, hSmtJ1I]
                                  have hLhsTrans :
                                      RuleProofs.eo_has_smt_translation lhs := by
                                    simpa [RuleProofs.eo_has_smt_translation, lhs, hLhsTy]
                                  rw [prog_array_read_over_write2_eq
                                        t1 i1 j1 e1 i1 j1
                                        hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck]
                                  simp [body, lhs, rhs, __eo_requires, __eo_and, __eo_eq,
                                    native_ite, native_teq, native_not,
                                    SmtEval.native_not]
                                  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                    lhs rhs
                                    (by rw [hLhsTy, hRhsTy])
                                    hLhsTrans
                              | true =>
                                  have : False := by
                                    simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                                      hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                                  exact False.elim this
                          | _ =>
                              have : False := by
                                simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                                  hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                              exact False.elim this
                      | _ =>
                          have : False := by
                            simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                              hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                          exact False.elim this
                  | _ =>
                      have : False := by
                        simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                          hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                      exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                      hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                  hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
              exact False.elim this
      | _ =>
          have : False := by
            simp [__eo_prog_array_read_over_write2, hT1NotStuck,
              hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
          exact False.elim this
  | _ =>
      have : False := by
        simp [__eo_prog_array_read_over_write2, hT1NotStuck,
          hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
      exact False.elim this

private theorem facts___eo_prog_array_read_over_write2_impl
    (M : SmtModel) (hM : model_total_typed M) (t1 i1 j1 e1 p1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation j1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  eo_interprets M p1 true ->
  __eo_typeof (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) = Term.Bool ->
  eo_interprets M (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) true := by
  intro hT1Trans hI1Trans hJ1Trans hE1Trans hP1True hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) :=
    typed___eo_prog_array_read_over_write2_impl
      t1 i1 j1 e1 p1 hT1Trans hI1Trans hJ1Trans hE1Trans hResultTy
  have hProg :
      __eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1) ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _
      hProgBool
  cases p1 with
  | Apply f pRhs =>
      cases f with
      | Apply g pLhs =>
          cases g with
          | eq =>
              cases pLhs with
              | Apply f2 j2 =>
                  cases f2 with
                  | Apply g2 i2 =>
                      cases g2 with
                      | eq =>
                          cases pRhs with
                          | Boolean b =>
                              cases b with
                              | false =>
                                  rw [prog_array_read_over_write2_eq
                                        t1 i1 j1 e1 i2 j2
                                        hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck] at hProg
                                  let lhs :=
                                    Term.Apply
                                      (Term.Apply Term.select
                                        (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                      j1
                                  let rhs := Term.Apply (Term.Apply Term.select t1) j1
                                  let body := Term.Apply (Term.Apply Term.eq lhs) rhs
                                  have hAlign :
                                      i2 = i1 ∧ j2 = j1 :=
                                    RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                      i1 j1 i2 j2 body hProg
                                  have hi2 : i2 = i1 := hAlign.1
                                  have hj2 : j2 = j1 := hAlign.2
                                  subst i2
                                  subst j2
                                  have hij :
                                      native_veq
                                        (__smtx_model_eval M (__eo_to_smt i1))
                                        (__smtx_model_eval M (__eo_to_smt j1)) = false := by
                                    exact RuleProofs.native_veq_false_of_model_eval_eq_false
                                      (RuleProofs.model_eval_eq_false_of_eq_false_eq_true M i1 j1 hP1True)
                                  have hBodyBool :
                                      RuleProofs.eo_has_bool_type body := by
                                    rw [prog_array_read_over_write2_eq
                                          t1 i1 j1 e1 i1 j1
                                          hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck] at hProgBool
                                    simpa [body, lhs, rhs, __eo_requires, __eo_and, __eo_eq,
                                      native_ite, native_teq, native_not,
                                      SmtEval.native_not] using hProgBool
                                  rw [prog_array_read_over_write2_eq
                                        t1 i1 j1 e1 i1 j1
                                        hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck]
                                  simp [body, lhs, rhs, __eo_requires, __eo_and, __eo_eq,
                                    native_ite, native_teq, native_not,
                                    SmtEval.native_not]
                                  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBodyBool <| by
                                    simpa [lhs, rhs, RuleProofs.eo_to_smt_select_eq,
                                      RuleProofs.eo_to_smt_store_eq, __smtx_model_eval] using
                                      (RuleProofs.smt_value_rel_select_store_other_of_native_veq_false
                                        (__smtx_model_eval M (__eo_to_smt t1))
                                        (__smtx_model_eval M (__eo_to_smt i1))
                                        (__smtx_model_eval M (__eo_to_smt j1))
                                        (__smtx_model_eval M (__eo_to_smt e1))
                                        hij)
                              | true =>
                                  have : False := by
                                    simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                                      hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                                  exact False.elim this
                          | _ =>
                              have : False := by
                                simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                                  hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                              exact False.elim this
                      | _ =>
                          have : False := by
                            simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                              hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                          exact False.elim this
                  | _ =>
                      have : False := by
                        simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                          hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                      exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                      hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                  hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
              exact False.elim this
      | _ =>
          have : False := by
            simp [__eo_prog_array_read_over_write2, hT1NotStuck,
              hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
          exact False.elim this
  | _ =>
      have : False := by
        simp [__eo_prog_array_read_over_write2, hT1NotStuck,
          hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
      exact False.elim this

theorem cmd_step_array_read_over_write2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_read_over_write2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.array_read_over_write2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_read_over_write2 args premises) :=
by
  intro hCmdTrans hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.array_read_over_write2 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons n1 premises =>
                          cases premises with
                          | nil =>
                              let T1 := a1
                              let I1 := a2
                              let J1 := a3
                              let E1 := a4
                              let P1 := __eo_state_proven_nth s n1
                              have hTranses :
                                  RuleProofs.eo_has_smt_translation T1 ∧
                                    RuleProofs.eo_has_smt_translation I1 ∧
                                    RuleProofs.eo_has_smt_translation J1 ∧
                                    RuleProofs.eo_has_smt_translation E1 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                              change __eo_typeof
                                  (__eo_prog_array_read_over_write2 T1 I1 J1 E1 (Proof.pf P1)) =
                                Term.Bool at hResultTy
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                change eo_interprets M
                                    (__eo_prog_array_read_over_write2 T1 I1 J1 E1 (Proof.pf P1))
                                    true
                                exact facts___eo_prog_array_read_over_write2_impl M hM
                                  T1 I1 J1 E1 P1
                                  hTranses.1 hTranses.2.1 hTranses.2.2.1 hTranses.2.2.2
                                  (hTrue P1 (by simp [P1, premiseTermList]))
                                  hResultTy
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_array_read_over_write2 T1 I1 J1 E1 (Proof.pf P1))
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                  (__eo_prog_array_read_over_write2 T1 I1 J1 E1 (Proof.pf P1))
                                  (typed___eo_prog_array_read_over_write2_impl
                                    T1 I1 J1 E1 P1
                                    hTranses.1 hTranses.2.1 hTranses.2.2.1 hTranses.2.2.2
                                    hResultTy)
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
