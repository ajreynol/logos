import Cpc.Proofs.RuleSupport.DtConsEqSupport
import Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private inductive SmtValueProperSubterm : SmtValue -> SmtValue -> Prop where
  | app_fun_self {f a : SmtValue} :
      SmtValueProperSubterm f (SmtValue.Apply f a)
  | app_fun {v f a : SmtValue} :
      SmtValueProperSubterm v f ->
      SmtValueProperSubterm v (SmtValue.Apply f a)
  | app_arg {f a : SmtValue} :
      SmtValueProperSubterm a (SmtValue.Apply f a)
  | app_arg_sub {v f a : SmtValue} :
      SmtValueProperSubterm v a ->
      SmtValueProperSubterm v (SmtValue.Apply f a)

private theorem smtValueProperSubterm_size_lt
    {v w : SmtValue} :
    SmtValueProperSubterm v w -> sizeOf v < sizeOf w := by
  intro h
  induction h with
  | app_fun_self =>
      rename_i f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega
  | app_fun h ih =>
      rename_i v f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega
  | app_arg =>
      rename_i f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega
  | app_arg_sub h ih =>
      rename_i v f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega

private theorem smtValueProperSubterm_ne
    {v w : SmtValue} :
    SmtValueProperSubterm v w -> v ≠ w := by
  intro h hEq
  have hLt := smtValueProperSubterm_size_lt h
  subst w
  omega

private theorem smtValueProperSubterm_parent_ne_reglan
    {v w : SmtValue} :
    SmtValueProperSubterm v w -> ∀ r, w ≠ SmtValue.RegLan r := by
  intro h r
  induction h with
  | app_fun_self => simp
  | app_fun => simp
  | app_arg => simp
  | app_arg_sub => simp

private theorem smtx_model_eval_eq_false_of_ne_not_reglan_pair
    {v w : SmtValue}
    (hNe : v ≠ w)
    (hReg : ¬ ∃ r1 r2, v = SmtValue.RegLan r1 ∧ w = SmtValue.RegLan r2) :
    __smtx_model_eval_eq v w = SmtValue.Boolean false := by
  cases v <;> cases w <;>
    simp [__smtx_model_eval_eq, native_veq] at hNe hReg ⊢
  all_goals exact hNe

private theorem smtx_model_eval_eq_false_of_proper_subterm
    {v w : SmtValue}
    (hSub : SmtValueProperSubterm v w) :
    __smtx_model_eval_eq v w = SmtValue.Boolean false := by
  exact smtx_model_eval_eq_false_of_ne_not_reglan_pair
    (smtValueProperSubterm_ne hSub)
    (by
      rintro ⟨r1, r2, hV, hW⟩
      exact smtValueProperSubterm_parent_ne_reglan hSub r2 hW)

private inductive CtorSpineRoot : Term -> Term -> Prop where
  | tuple :
      CtorSpineRoot (Term.UOp UserOp.tuple) (Term.UOp UserOp.tuple)
  | tupleUnit :
      CtorSpineRoot (Term.UOp UserOp.tuple_unit) (Term.UOp UserOp.tuple_unit)
  | dtCons (s : native_String) (d : Datatype) (i : native_Nat) :
      CtorSpineRoot (Term.DtCons s d i) (Term.DtCons s d i)
  | app {t root : Term} (x : Term) :
      CtorSpineRoot t root ->
      CtorSpineRoot (Term.Apply t x) root

private theorem ctorSpineRoot_of_is_cons_app_true
    (t : Term) :
    __is_cons_app t = Term.Boolean true ->
    ∃ root, CtorSpineRoot t root := by
  cases t with
  | UOp op =>
      intro h
      cases op <;>
        simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
          __eo_dt_selectors_main, native_teq, native_ite, native_not,
          SmtEval.native_not, SmtEval.native_and] at h ⊢
      all_goals
        first
        | exact ⟨Term.UOp UserOp.tuple, CtorSpineRoot.tuple⟩
        | exact ⟨Term.UOp UserOp.tuple_unit, CtorSpineRoot.tupleUnit⟩
        | contradiction
  | Apply f a =>
      intro h
      rcases ctorSpineRoot_of_is_cons_app_true f
          (by simpa [__is_cons_app] using h) with
        ⟨root, hRoot⟩
      exact ⟨root, CtorSpineRoot.app a hRoot⟩
  | DtCons s d i =>
      intro _h
      exact ⟨Term.DtCons s d i, CtorSpineRoot.dtCons s d i⟩
  | Stuck =>
      intro h
      simp [__is_cons_app] at h
  | UOp1 op t =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | UOp2 op t u =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | UOp3 op t u v =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | __eo_List =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | __eo_List_nil =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | __eo_List_cons =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Bool =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Boolean b =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Numeral n =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Rational q =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | String str =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Binary w n =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | «Type» =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | FunType =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Var n T =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DatatypeType s d =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DatatypeTypeRef s =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DtcAppType T U =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DtSel s d i j =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | USort n =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | UConst n T =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
termination_by sizeOf t
decreasing_by
  simp_wf
  omega

private theorem prog_dt_cycle_shape_of_not_stuck
    (s t : Term) :
    __eo_prog_dt_cycle
        (Term.Apply
          (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false)) ≠
      Term.Stuck ->
    __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
        Term.Boolean true ∧
      __eo_prog_dt_cycle
          (Term.Apply
            (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
            (Term.Boolean false)) =
        Term.Apply
          (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false) := by
  intro hProg
  let guard := __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false)
  let body :=
    Term.Apply
      (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
      (Term.Boolean false)
  have hReq : __eo_requires guard (Term.Boolean true) body ≠ Term.Stuck := by
    simpa [__eo_prog_dt_cycle, guard, body] using hProg
  constructor
  · exact eo_requires_eq_of_ne_stuck guard (Term.Boolean true) body hReq
  · simpa [__eo_prog_dt_cycle, guard, body] using
      eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true) body hReq

private theorem dt_cycle_inner_eval_false
    (M : SmtModel) (hM : model_total_typed M) (s t : Term) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) ->
    __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
      Term.Boolean true ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply Term.eq s) t)) =
      SmtValue.Boolean false := by
  sorry

theorem cmd_step_dt_cycle_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_cycle args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_cycle args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_cycle args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_cycle args premises ≠ Term.Stuck :=
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
              have hATransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              have hProgRule : __eo_prog_dt_cycle a1 ≠ Term.Stuck := by
                simpa using hProg
              cases a1 with
              | Apply f B =>
                  cases B with
                  | Boolean b =>
                      cases b
                      · cases f with
                        | Apply g lhs =>
                            cases g with
                            | UOp op =>
                                cases op with
                                | eq =>
                                    cases lhs with
                                    | Apply f' s' =>
                                        cases f' with
                                        | Apply g' t' =>
                                            cases g' with
                                            | UOp op' =>
                                                cases op' with
                                                | eq =>
                                                    let proven :=
                                                      Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply
                                                            (Term.Apply Term.eq t') s'))
                                                        (Term.Boolean false)
                                                    have hShape :=
                                                      prog_dt_cycle_shape_of_not_stuck
                                                        t' s' hProgRule
                                                    have hCycle :
                                                        __dt_find_cycle s' t'
                                                            (__is_cons_app s')
                                                            (Term.Boolean false) =
                                                          Term.Boolean true :=
                                                      hShape.1
                                                    have hProgEq :
                                                        __eo_prog_dt_cycle proven = proven := by
                                                      simpa [proven] using hShape.2
                                                    have hAType : __eo_typeof proven = Term.Bool := by
                                                      have hResultTy' := hResultTy
                                                      change __eo_typeof
                                                          (__eo_prog_dt_cycle proven) =
                                                        Term.Bool at hResultTy'
                                                      rw [hProgEq] at hResultTy'
                                                      exact hResultTy'
                                                    have hABool :
                                                        RuleProofs.eo_has_bool_type proven :=
                                                      RuleProofs.eo_typeof_bool_implies_has_bool_type
                                                        _ hATrans hAType
                                                    refine ⟨?_, ?_⟩
                                                    · intro _hTrue
                                                      change eo_interprets M
                                                        (__eo_prog_dt_cycle proven) true
                                                      rw [hProgEq]
                                                      have hInnerBool :
                                                          RuleProofs.eo_has_bool_type
                                                            (Term.Apply
                                                              (Term.Apply Term.eq t') s') :=
                                                        eo_eq_has_bool_type_of_eq_has_bool_type
                                                          t' s' (Term.Boolean false) hABool
                                                      have hInnerEvalFalse :
                                                          __smtx_model_eval M
                                                              (__eo_to_smt
                                                                (Term.Apply
                                                                  (Term.Apply Term.eq t') s')) =
                                                            SmtValue.Boolean false :=
                                                        dt_cycle_inner_eval_false
                                                          M hM t' s' hInnerBool hCycle
                                                      have hFalseEval :
                                                          __smtx_model_eval M
                                                              (__eo_to_smt (Term.Boolean false)) =
                                                            SmtValue.Boolean false := by
                                                        simp [__smtx_model_eval]
                                                      have hRel :
                                                          RuleProofs.smt_value_rel
                                                            (__smtx_model_eval M
                                                              (__eo_to_smt
                                                                (Term.Apply
                                                                  (Term.Apply Term.eq t') s')))
                                                            (__smtx_model_eval M
                                                              (__eo_to_smt (Term.Boolean false))) := by
                                                        rw [hInnerEvalFalse, hFalseEval]
                                                        exact RuleProofs.smt_value_rel_refl
                                                          (SmtValue.Boolean false)
                                                      exact RuleProofs.eo_interprets_eq_of_rel
                                                        M
                                                        (Term.Apply
                                                          (Term.Apply Term.eq t') s')
                                                        (Term.Boolean false)
                                                        hABool hRel
                                                    · change RuleProofs.eo_has_smt_translation
                                                        (__eo_prog_dt_cycle proven)
                                                      rw [hProgEq]
                                                      exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                        _ hABool
                                                | _ =>
                                                    simp [__eo_prog_dt_cycle] at hProgRule
                                            | _ =>
                                                simp [__eo_prog_dt_cycle] at hProgRule
                                        | _ =>
                                            simp [__eo_prog_dt_cycle] at hProgRule
                                    | _ =>
                                        simp [__eo_prog_dt_cycle] at hProgRule
                                | _ =>
                                    simp [__eo_prog_dt_cycle] at hProgRule
                            | _ =>
                                simp [__eo_prog_dt_cycle] at hProgRule
                        | _ =>
                            simp [__eo_prog_dt_cycle] at hProgRule
                      · simp [__eo_prog_dt_cycle] at hProgRule
                  | _ =>
                      simp [__eo_prog_dt_cycle] at hProgRule
              | _ =>
                  simp [__eo_prog_dt_cycle] at hProgRule
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
