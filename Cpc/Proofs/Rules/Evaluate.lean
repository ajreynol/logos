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

private theorem eo_mk_apply_eq_apply_of_args_ne_stuck (f x : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hf hx
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

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

private theorem eo_prog_evaluate_eq_of_term_and_run_ne_stuck (A : Term) :
    A ≠ Term.Stuck ->
    __run_evaluate A ≠ Term.Stuck ->
    __eo_prog_evaluate A =
      Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) (__run_evaluate A) := by
  intro hA hRun
  cases A
  all_goals
    first
    | exact False.elim (hA rfl)
    | simp only [__eo_prog_evaluate]
      exact eo_mk_apply_eq_apply_of_args_ne_stuck _ _
        (by intro h; cases h) hRun

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

private theorem run_evaluate_rec_apply_fun
    (M : SmtModel) (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M f :=
  rec f (by
    change sizeOf f < 1 + sizeOf f + sizeOf x
    omega)

private theorem run_evaluate_rec_apply_arg
    (M : SmtModel) (f x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply f x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M x :=
  rec x (by
    change sizeOf x < 1 + sizeOf f + sizeOf x
    omega)

private theorem run_evaluate_rec_apply_apply_arg
    (M : SmtModel) (g y x : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.Apply g y) x) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M y :=
  rec y (by
    change sizeOf y < 1 + (1 + sizeOf g + sizeOf y) + sizeOf x
    omega)

private theorem eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool
    (t : Term) :
    t ≠ Term.Stuck ->
    __eo_typeof t = Term.Bool ->
    __eo_typeof (__run_evaluate t) = Term.Bool ->
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  intro hTNe hTy hRunTy
  have hRunNe : __run_evaluate t ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hRunTy
  have hProgEq :=
    eo_prog_evaluate_eq_of_term_and_run_ne_stuck t hTNe hRunNe
  rw [hProgEq]
  change __eo_typeof_eq (__eo_typeof t) (__eo_typeof (__run_evaluate t)) =
    Term.Bool
  rw [hTy, hRunTy]
  simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
    native_not]

private theorem smt_value_rel_model_eval_not_of_rel
    (a b : SmtValue) :
    RuleProofs.smt_value_rel a b ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_not a) (__smtx_model_eval_not b) := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel ⊢
  cases a <;> cases b <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_not, native_veq] at hRel ⊢
  case Boolean b₁ b₂ =>
    cases b₁ <;> cases b₂ <;> simp at hRel ⊢

private theorem smt_value_rel_model_eval_and_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_and a b) (__smtx_model_eval_and c d) := by
  intro hAC hBD
  unfold RuleProofs.smt_value_rel at hAC hBD ⊢
  cases a <;> cases c <;> cases b <;> cases d <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_and, native_veq] at hAC hBD ⊢
  case Boolean b₁ b₂ b₃ b₄ =>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
      simp [native_and] at hAC hBD ⊢

private theorem smt_value_rel_model_eval_or_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_or a b) (__smtx_model_eval_or c d) := by
  intro hAC hBD
  unfold RuleProofs.smt_value_rel at hAC hBD ⊢
  cases a <;> cases c <;> cases b <;> cases d <;>
    simp [__smtx_model_eval_eq, __smtx_model_eval_or, native_veq] at hAC hBD ⊢
  case Boolean b₁ b₂ b₃ b₄ =>
    cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;>
      simp [native_or] at hAC hBD ⊢

private theorem has_bool_type_not_of_has_translation
    (b : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.not) b) ->
    RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.not (__eo_to_smt b)) ≠ SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.not (__eo_to_smt b)) = SmtType.Bool
  rw [typeof_not_eq]
  rw [typeof_not_eq] at hTrans'
  cases hTy : __smtx_typeof (__eo_to_smt b) <;>
    simp [hTy, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_and_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_and_eq]
  rw [typeof_and_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_or_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_or_eq]
  rw [typeof_or_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_or_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

private theorem has_bool_type_or_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

private theorem evaluate_eo_typeof_eq_bool_operands_eq
    (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

private theorem evaluate_apply_eq_typeof_bool_operands_eq
    (x y : Term)
    (h : __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) = Term.Bool) :
    __eo_typeof x = __eo_typeof y := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at h
  exact evaluate_eo_typeof_eq_bool_operands_eq
    (__eo_typeof x) (__eo_typeof y) h

private theorem eo_not_arg_boolean_of_typeof_bool
    (t : Term) :
    __eo_typeof (__eo_not t) = Term.Bool ->
    ∃ b : Bool, t = Term.Boolean b := by
  cases t <;> intro h
  case Boolean b =>
    exact ⟨b, rfl⟩
  case Binary w n =>
    change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) =
      Term.Bool at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

private theorem eo_and_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_and x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_and] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_and] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_and wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

private theorem eo_or_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_or x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_or] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_or] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_or wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Bool at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck = Term.Bool at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · simp [hWidth] at h
          change Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wy) =
            Term.Bool at h
          cases h
        · simp [hWidth] at h
          change Term.Stuck = Term.Bool at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck = Term.Bool at h
    change Term.Stuck = Term.Bool at h
    cases h

private theorem run_evaluate_sound_apply_not_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.not) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.not) b) := by
  intro hATrans hEvalTy
  have hNotBool :
      RuleProofs.eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) b) :=
    has_bool_type_not_of_has_translation b hATrans
  have hBBool : RuleProofs.eo_has_bool_type b :=
    RuleProofs.eo_has_bool_type_not_arg b hNotBool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hNotEoBool :
      __eo_typeof (Term.Apply (Term.UOp UserOp.not) b) = Term.Bool := by
    change __eo_typeof_not (__eo_typeof b) = Term.Bool
    rw [hBEoBool]
    rfl
  have hRunNotNe : __eo_not (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.not) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.not) b))
          (__eo_not (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_not (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunNotNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.not) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.not) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunNotEoBool : __eo_typeof (__eo_not (__run_evaluate b)) = Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.not) b)
        (__eo_not (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hNotEoBool
  rcases eo_not_arg_boolean_of_typeof_bool
      (__run_evaluate b) hRunNotEoBool with
    ⟨runBool, hRunBool⟩
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunBool]
    rfl
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool := by
    have hBNe : b ≠ Term.Stuck :=
      RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans
    have hRunBNe : __run_evaluate b ≠ Term.Stuck :=
      term_ne_stuck_of_typeof_bool hRunBEoBool
    have hProgEq :=
      eo_prog_evaluate_eq_of_term_and_run_ne_stuck b hBNe hRunBNe
    rw [hProgEq]
    change __eo_typeof_eq (__eo_typeof b) (__eo_typeof (__run_evaluate b)) =
      Term.Bool
    rw [hBEoBool, hRunBEoBool]
    simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
      native_not]
  rcases run_evaluate_rec_apply_arg M (Term.UOp UserOp.not) b rec
      hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.not (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt (__eo_not (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.not (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt (__eo_not (__run_evaluate b))))
  rw [hRunBool]
  constructor
  · change
      __smtx_typeof (SmtTerm.not (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_not runBool))
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_not_eq]
    rw [hBTy]
    rw [__smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runBool)) := by
      simpa [hRunBool] using hRel
    have hRelNot :=
      smt_value_rel_model_eval_not_of_rel
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (SmtTerm.Boolean runBool)) hRelBool
    simpa [__eo_not, __smtx_model_eval, __smtx_model_eval_not] using hRelNot

private theorem run_evaluate_sound_apply_and_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) := by
  intro hATrans hEvalTy
  have hAndBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) :=
    has_bool_type_and_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    RuleProofs.eo_has_bool_type_and_left a b hAndBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    RuleProofs.eo_has_bool_type_and_right a b hAndBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hAndEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunAndNe :
      __eo_and (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
          (__eo_and (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_and (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAndNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAndEoBool :
      __eo_typeof (__eo_and (__run_evaluate a) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) a) b)
        (__eo_and (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hAndEoBool
  rcases eo_and_args_boolean_of_typeof_bool
      (__run_evaluate a) (__run_evaluate b) hRunAndEoBool with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.and) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.and) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.and (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_and runA runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_and_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hRelAnd :=
      smt_value_rel_model_eval_and_of_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (SmtTerm.Boolean runA))
        (__smtx_model_eval M (SmtTerm.Boolean runB))
        hARelBool hBRelBool
    simpa [__eo_and, __smtx_model_eval, __smtx_model_eval_and] using hRelAnd

private theorem run_evaluate_sound_apply_or_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) := by
  intro hATrans hEvalTy
  have hOrBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) :=
    has_bool_type_or_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    has_bool_type_or_left a b hOrBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    has_bool_type_or_right a b hOrBool
  have hATransA : RuleProofs.eo_has_smt_translation a :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type a hABool
  have hBTrans : RuleProofs.eo_has_smt_translation b :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type b hBBool
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBool : __eo_typeof a = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hAMatch.symm.trans hABool)
  have hBEoBool : __eo_typeof b = Term.Bool :=
    TranslationProofs.eo_to_smt_type_eq_bool (hBMatch.symm.trans hBBool)
  have hOrEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunOrNe :
      __eo_or (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
          (__eo_or (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_or (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunOrNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunOrEoBool :
      __eo_typeof (__eo_or (__run_evaluate a) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) a) b)
        (__eo_or (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hOrEoBool
  rcases eo_or_args_boolean_of_typeof_bool
      (__run_evaluate a) (__run_evaluate b) hRunOrEoBool with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoBool : __eo_typeof (__run_evaluate a) = Term.Bool := by
    rw [hRunA]
    rfl
  have hRunBEoBool : __eo_typeof (__run_evaluate b) = Term.Bool := by
    rw [hRunB]
    rfl
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool a
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hAEoBool hRunAEoBool
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_typeof_bool_and_run_typeof_bool b
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBEoBool hRunBEoBool
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.or) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.or) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.or (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_or runA runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_or_eq, hATy, hBTy, __smtx_typeof.eq_1]
    simp [native_ite, native_Teq]
  · have hARelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (__smtx_model_eval M (SmtTerm.Boolean runA)) := by
      simpa [hRunA] using hARel
    have hBRelBool :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (__smtx_model_eval M (SmtTerm.Boolean runB)) := by
      simpa [hRunB] using hBRel
    have hRelOr :=
      smt_value_rel_model_eval_or_of_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
        (__smtx_model_eval M (SmtTerm.Boolean runA))
        (__smtx_model_eval M (SmtTerm.Boolean runB))
        hARelBool hBRelBool
    simpa [__eo_or, __smtx_model_eval, __smtx_model_eval_or] using hRelOr

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
  cases f with
  | UOp op =>
      cases op <;> first
        | exact run_evaluate_sound_apply_not_core M hM x rec hATrans hEvalTy
        | exact False.elim (hActive rfl)
        | sorry
  | UOp1 op a =>
      cases op <;> first
        | exact False.elim (hActive rfl)
        | sorry
  | UOp2 op a b =>
      cases op <;> first
        | exact False.elim (hActive rfl)
        | sorry
  | Apply g y =>
      cases g with
      | UOp op =>
          cases op <;> first
            | exact False.elim (hActive rfl)
            | exact run_evaluate_sound_apply_and_core M hM y x rec hATrans hEvalTy
            | exact run_evaluate_sound_apply_or_core M hM y x rec hATrans hEvalTy
            | sorry
      | Apply h z =>
          cases h with
          | UOp op =>
              cases op <;> first
                | exact False.elim (hActive rfl)
                | sorry
          | _ =>
              exact False.elim (hActive rfl)
      | _ =>
          exact False.elim (hActive rfl)
  | _ =>
      exact False.elim (hActive rfl)

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
  | Term.UOp2 UserOp2.extract _ _ =>
      run_evaluate_sound_of_eq_self M _ rfl
  | Term.UOp2 UserOp2._at_bv n m =>
      run_evaluate_sound_uop2_at_bv_core M hM
        n m (fun A _hA => run_evaluate_sound_core M hM A)
  | Term.UOp2 UserOp2.re_loop _ _ =>
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
