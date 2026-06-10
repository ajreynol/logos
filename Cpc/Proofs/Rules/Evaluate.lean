import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_mk_apply_eq_apply_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro h
  cases f <;> cases x <;> simp [__eo_mk_apply] at h ⊢

private theorem eo_prog_evaluate_eq_of_ne_stuck (A : Term) :
    __eo_prog_evaluate A ≠ Term.Stuck ->
    __eo_prog_evaluate A =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) (__run_evaluate A) := by
  intro hProg
  cases A <;> simp [__eo_prog_evaluate] at hProg ⊢
  all_goals
    first
    | contradiction
    | exact eo_mk_apply_eq_apply_of_ne_stuck _ _ hProg

private def RunEvaluateSoundGoal (M : SmtModel) (A : Term) : Prop :=
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof (__eo_prog_evaluate A) = Term.Bool ->
  __smtx_typeof (__eo_to_smt A) =
      __smtx_typeof (__eo_to_smt (__run_evaluate A)) ∧
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt A))
      (__smtx_model_eval M (__eo_to_smt (__run_evaluate A)))

private theorem run_evaluate_sound_of_eq_self
    (M : SmtModel) (A : Term)
    (hRun : __run_evaluate A = A) :
  RunEvaluateSoundGoal M A := by
  intro _hATrans _hEvalTy
  rw [hRun]
  exact ⟨rfl, RuleProofs.smt_value_rel_refl _⟩

private theorem run_evaluate_sound_active_apply_core
    (M : SmtModel) (hM : model_total_typed M)
    (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          RunEvaluateSoundGoal M A) :
  __run_evaluate (Term.Apply f x) ≠ Term.Apply f x ->
  RunEvaluateSoundGoal M (Term.Apply f x) := by
  intro hActive hATrans hEvalTy
  sorry

private theorem run_evaluate_sound_apply
    (M : SmtModel) (hM : model_total_typed M)
    (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply f x) := by
  intro hATrans hEvalTy
  by_cases hRun : __run_evaluate (Term.Apply f x) = Term.Apply f x
  · exact run_evaluate_sound_of_eq_self M _ hRun hATrans hEvalTy
  · exact run_evaluate_sound_active_apply_core M hM f x rec hRun hATrans hEvalTy

private theorem run_evaluate_sound_uop2_at_bv_core
    (M : SmtModel) (hM : model_total_typed M)
    (n m : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.UOp2 UserOp2._at_bv n m) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.UOp2 UserOp2._at_bv n m) := by
  intro hATrans hEvalTy
  have hTranslate :
      __eo_to_smt (Term.UOp2 UserOp2._at_bv n m) =
        __eo_to_smt__at_bv (__eo_to_smt n) (__eo_to_smt m) := by
    rfl
  have hAtNN :
      __smtx_typeof (__eo_to_smt__at_bv (__eo_to_smt n) (__eo_to_smt m)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation, hTranslate] using hATrans
  rcases TranslationProofs.eo_to_smt_at_bv_of_non_none hAtNN with
    ⟨value, width, hn, hm, hWidthNonneg, _hSmtAt⟩
  have hnTerm : n = Term.Numeral value :=
    TranslationProofs.eo_to_smt_eq_numeral n value hn
  have hmTerm : m = Term.Numeral width :=
    TranslationProofs.eo_to_smt_eq_numeral m width hm
  subst n
  subst m
  cases hBound : native_zleq width 4294967296
  · exfalso
    have hRunStuck :
        __run_evaluate
            (Term.UOp2 UserOp2._at_bv (Term.Numeral value)
              (Term.Numeral width)) =
          Term.Stuck := by
      simp [__run_evaluate, __eo_to_bin, hBound, native_ite]
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.UOp2 UserOp2._at_bv (Term.Numeral value)
                (Term.Numeral width)))
            (__run_evaluate
              (Term.UOp2 UserOp2._at_bv (Term.Numeral value)
                (Term.Numeral width)))) =
        Term.Bool at hEvalTy
    rw [hRunStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  · have hRun :
        __run_evaluate
            (Term.UOp2 UserOp2._at_bv (Term.Numeral value)
              (Term.Numeral width)) =
          Term.Binary width
            (native_mod_total value (native_int_pow2 width)) := by
      simp [__run_evaluate, __eo_to_bin, __eo_mk_binary, hWidthNonneg, hBound,
        native_ite]
    rw [hRun]
    change
      __smtx_typeof
          (__eo_to_smt__at_bv (SmtTerm.Numeral value)
            (SmtTerm.Numeral width)) =
          __smtx_typeof
            (SmtTerm.Binary width
              (native_mod_total value (native_int_pow2 width))) ∧
        RuleProofs.smt_value_rel
          (__smtx_model_eval M
            (__eo_to_smt__at_bv (SmtTerm.Numeral value)
              (SmtTerm.Numeral width)))
          (__smtx_model_eval M
            (SmtTerm.Binary width
              (native_mod_total value (native_int_pow2 width))))
    simp [__eo_to_smt__at_bv, hWidthNonneg, native_ite,
      RuleProofs.smt_value_rel_refl]

private theorem run_evaluate_sound_core
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ A : Term, RunEvaluateSoundGoal M A
  | Term.Apply f x =>
      run_evaluate_sound_apply M hM
        f x (fun A _hA => run_evaluate_sound_core M hM A)
  | Term.Stuck => by
      intro hATrans _hEvalTy
      exact False.elim
        (RuleProofs.term_ne_stuck_of_has_smt_translation _ hATrans rfl)
  | Term.UOp _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp1 _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_array_deq_diff _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2.extract _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_bv n m =>
      run_evaluate_sound_uop2_at_bv_core M hM
        n m (fun A _hA => run_evaluate_sound_core M hM A)
  | Term.UOp2 UserOp2.re_loop _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_strings_deq_diff _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_strings_num_occur_re _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_strings_occur_index_re _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_sets_deq_diff _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_quantifiers_skolemize _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_const _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp3 _ _ _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.__eo_List =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.__eo_List_nil =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.__eo_List_cons =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Bool =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Boolean _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Numeral _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Rational _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.String _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Binary _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Type =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.FunType =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.Var _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DatatypeType _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DatatypeTypeRef _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DtcAppType _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DtCons _ _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.DtSel _ _ _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.USort _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UConst _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl

/--
Semantic soundness target for the generated evaluator.

The command-level `evaluate` rule is premise-free and emits
`A = __run_evaluate A`.  The large theorem to prove is that, whenever the
checker accepts that emitted equality as Boolean and the input term has an SMT
translation, `__run_evaluate A` has the same SMT type as `A` and evaluates to
the same SMT value.
-/
theorem run_evaluate_sound
    (M : SmtModel) (hM : model_total_typed M) (A : Term) :
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof (__eo_prog_evaluate A) = Term.Bool ->
  __smtx_typeof (__eo_to_smt A) =
      __smtx_typeof (__eo_to_smt (__run_evaluate A)) ∧
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt A))
      (__smtx_model_eval M (__eo_to_smt (__run_evaluate A))) :=
by
  exact run_evaluate_sound_core M hM A

theorem run_evaluate_properties
    (M : SmtModel) (hM : model_total_typed M) (A : Term) :
  RuleProofs.eo_has_smt_translation A ->
  __eo_typeof (__eo_prog_evaluate A) = Term.Bool ->
  StepRuleProperties M [] (__eo_prog_evaluate A) :=
by
  intro hATrans hEvalTy
  have hProg : __eo_prog_evaluate A ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hEvalTy
  have hProgEq := eo_prog_evaluate_eq_of_ne_stuck A hProg
  rcases run_evaluate_sound M hM A hATrans hEvalTy with
    ⟨hSameTy, hEvalRel⟩
  have hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) A)
          (__run_evaluate A)) :=
    RuleProofs.eo_has_bool_type_eq_of_same_smt_type A (__run_evaluate A)
      hSameTy hATrans
  refine ⟨?_, ?_⟩
  · intro _hTrue
    rw [hProgEq]
    exact RuleProofs.eo_interprets_eq_of_rel M A (__run_evaluate A)
      hEqBool hEvalRel
  · rw [hProgEq]
    exact RuleProofs.eo_has_smt_translation_of_has_bool_type _ hEqBool

theorem cmd_step_evaluate_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.evaluate args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.evaluate args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.evaluate args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.evaluate args premises ≠
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
              have hATransPair : eoHasSmtTranslation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                  using hATransPair.1
              have hEvalTy :
                  __eo_typeof (__eo_prog_evaluate a1) = Term.Bool := by
                change __eo_typeof (__eo_prog_evaluate a1) = Term.Bool
                  at hResultTy
                exact hResultTy
              simpa [premiseTermList] using
                run_evaluate_properties M hM a1 hATrans hEvalTy
