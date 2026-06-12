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

private theorem eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof
    (t T : Term) :
    t ≠ Term.Stuck ->
    T ≠ Term.Stuck ->
    __eo_typeof t = T ->
    __eo_typeof (__run_evaluate t) = T ->
    __eo_typeof (__eo_prog_evaluate t) = Term.Bool := by
  intro hTNe hTypeNe hTy hRunTy
  have hRunNe : __run_evaluate t ≠ Term.Stuck := by
    intro hRunStuck
    rw [hRunStuck] at hRunTy
    change Term.Stuck = T at hRunTy
    exact hTypeNe hRunTy.symm
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

private theorem smt_value_rel_model_eval_imp_of_rel
    (a b c d : SmtValue) :
    RuleProofs.smt_value_rel a c ->
    RuleProofs.smt_value_rel b d ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval_imp a b) (__smtx_model_eval_imp c d) := by
  intro hAC hBD
  unfold __smtx_model_eval_imp
  exact smt_value_rel_model_eval_or_of_rel
    (__smtx_model_eval_not a) b (__smtx_model_eval_not c) d
    (smt_value_rel_model_eval_not_of_rel a c hAC) hBD

private theorem smt_value_rel_boolean_eq
    (v : SmtValue) (b : Bool) :
    RuleProofs.smt_value_rel v (SmtValue.Boolean b) ->
    v = SmtValue.Boolean b := by
  intro hRel
  unfold RuleProofs.smt_value_rel at hRel
  cases v <;> simp [__smtx_model_eval_eq, native_veq] at hRel
  case Boolean b' =>
    cases b <;> cases b' <;> simp at hRel ⊢

private theorem smt_value_rel_binary_eq
    (v : SmtValue) (w n : native_Int) :
    RuleProofs.smt_value_rel v (SmtValue.Binary w n) ->
    v = SmtValue.Binary w n := by
  intro hRel
  exact (RuleProofs.smt_value_rel_iff_eq
    v (SmtValue.Binary w n) (by
      rintro ⟨r1, r2, _hv, hBin⟩
      cases hBin)).mp hRel

private theorem smtx_typeof_binary_mod_nat_to_int
    (w : native_Nat) (n : native_Int) :
    __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total n (native_int_pow2 (native_nat_to_int w)))) =
      SmtType.BitVec w := by
  have hNN :
      __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total n (native_int_pow2 (native_nat_to_int w)))) ≠
        SmtType.None := by
    unfold __smtx_typeof
    have hWidth :
        native_zleq 0 (native_nat_to_int w) = true := by
      simp [SmtEval.native_zleq, SmtEval.native_nat_to_int]
    have hMod :
        native_zeq
            (native_mod_total n (native_int_pow2 (native_nat_to_int w)))
            (native_mod_total
              (native_mod_total n (native_int_pow2 (native_nat_to_int w)))
              (native_int_pow2 (native_nat_to_int w))) =
          true :=
      native_mod_total_canonical (native_nat_to_int w) n
    simp [SmtEval.native_and, hWidth, hMod, native_ite]
  simpa [SmtEval.native_int_to_nat, SmtEval.native_nat_to_int]
    using
      TranslationProofs.smtx_typeof_binary_of_non_none
        (native_nat_to_int w)
        (native_mod_total n (native_int_pow2 (native_nat_to_int w))) hNN

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

private theorem has_bool_type_xor_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_xor_eq]
  rw [typeof_xor_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_imp_of_has_translation
    (a b : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) := by
  intro hTrans
  have hTrans' :
      __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) ≠
        SmtType.None := by
    simpa [RuleProofs.eo_has_smt_translation] using hTrans
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool
  rw [typeof_imp_eq]
  rw [typeof_imp_eq] at hTrans'
  cases hA : __smtx_typeof (__eo_to_smt a) <;>
    cases hB : __smtx_typeof (__eo_to_smt b) <;>
      simp [hA, hB, native_ite, native_Teq] at hTrans' ⊢

private theorem has_bool_type_imp_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

private theorem has_bool_type_imp_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

private theorem has_bool_type_xor_left
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type a := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).1

private theorem has_bool_type_xor_right
    (a b : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
    RuleProofs.eo_has_bool_type b := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq (__eo_to_smt a) (__eo_to_smt b)) hNN).2

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

private theorem eo_not_arg_binary_of_typeof_bitvec
    (t : Term) (w : native_Int) :
    __eo_typeof (__eo_not t) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ n : native_Int, t = Term.Binary w n := by
  cases t <;> intro h
  case Binary wt n =>
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wt) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
    exact ⟨n, rfl⟩
  case Boolean b =>
    change Term.Bool =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
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

private theorem eo_and_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_and x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_and] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
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
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
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

private theorem eo_or_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_or x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_or] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
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
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_xor_args_boolean_of_typeof_bool
    (x y : Term) :
    __eo_typeof (__eo_xor x y) = Term.Bool ->
    ∃ bx : Bool, ∃ by' : Bool,
      x = Term.Boolean bx ∧ y = Term.Boolean by' := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_xor] at h
    case Boolean by' =>
      exact ⟨bx, by', rfl, rfl⟩
    all_goals
      change __eo_typeof Term.Stuck = Term.Bool at h
      change Term.Stuck = Term.Bool at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_xor] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_xor wx nx ny)
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

private theorem eo_xor_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_xor x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Boolean bx =>
    cases y <;> simp only [__eo_xor] at h
    case Boolean by' =>
      change Term.Bool =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_xor] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_binary_xor wx nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_add_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_add x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_add] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_add] at h
    case Rational ry =>
      change Term.UOp UserOp.Real =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_add] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zplus nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_mul_args_binary_of_typeof_bitvec
    (x y : Term) (w : native_Int) :
    __eo_typeof (__eo_mul x y) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, ∃ ny : native_Int,
      x = Term.Binary w nx ∧ y = Term.Binary w ny := by
  cases x <;> intro h
  case Numeral nx =>
    cases y <;> simp only [__eo_mul] at h
    case Numeral ny =>
      change Term.UOp UserOp.Int =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Rational rx =>
    cases y <;> simp only [__eo_mul] at h
    case Rational ry =>
      change Term.UOp UserOp.Real =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  case Binary wx nx =>
    cases y <;> simp only [__eo_mul] at h
    case Binary wy ny =>
      change
        __eo_typeof
            (__eo_requires (Term.Numeral wx) (Term.Numeral wy)
              (Term.Binary wx
                (native_mod_total (native_zmult nx ny)
                  (native_int_pow2 wx)))) =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      simp [__eo_requires] at h
      cases hReq : native_teq (Term.Numeral wx) (Term.Numeral wy)
      · simp [hReq, native_ite] at h
        change Term.Stuck =
          Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
        cases h
      · simp [native_ite, native_teq, native_not] at h
        by_cases hWidth : wx = wy
        · subst wy
          simp at h
          cases h
          exact ⟨nx, ny, rfl, rfl⟩
        · simp [hWidth] at h
          change Term.Stuck =
            Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
          cases h
    all_goals
      change __eo_typeof Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      change Term.Stuck =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
      cases h
  all_goals
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h

private theorem eo_neg_arg_binary_of_eq_binary
    (x : Term) (w n : native_Int) :
    __eo_neg x = Term.Binary w n ->
    ∃ nx : native_Int, x = Term.Binary w nx := by
  cases x <;> intro h <;> simp [__eo_neg] at h
  case Binary wx nx =>
    rcases h with ⟨hW, _⟩
    cases hW
    exact ⟨nx, rfl⟩

private theorem eo_neg_arg_binary_of_typeof_bitvec
    (x : Term) (w : native_Int) :
    __eo_typeof (__eo_neg x) =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) ->
    ∃ nx : native_Int, x = Term.Binary w nx := by
  cases x <;> intro h
  case Numeral n =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Int =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  case Rational r =>
    simp only [__eo_neg] at h
    change Term.UOp UserOp.Real =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
  case Binary wx nx =>
    simp only [__eo_neg] at h
    change
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral wx) =
        Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    cases h
    exact ⟨nx, rfl⟩
  all_goals
    simp only [__eo_neg] at h
    change __eo_typeof Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
    change Term.Stuck =
      Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w) at h
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

private theorem run_evaluate_sound_apply_bvnot_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.bvnot) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.bvnot) b) := by
  intro hATrans hEvalTy
  have hBvNotNN :
      term_has_non_none_type (SmtTerm.bvnot (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvnot) (t := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_38])
      hBvNotNN with
    ⟨w, hBTy⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvNotEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvnot (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hBEoBv]
    rfl
  have hRunNotNe : __eo_not (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.bvnot) b))
          (__eo_not (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_not (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunNotNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvnot) b))
            (__eo_not (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunNotEoBv :
      __eo_typeof (__eo_not (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.bvnot) b)
        (__eo_not (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvNotEoType
  rcases eo_not_arg_binary_of_typeof_bitvec
      (__run_evaluate b) (native_nat_to_int w) hRunNotEoBv with
    ⟨runN, hRunB⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_arg M (Term.UOp UserOp.bvnot) b rec
      hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.bvnot (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt (__eo_not (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt (__eo_not (__run_evaluate b))))
  rw [hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvnot (__eo_to_smt b)) =
        __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_not (native_nat_to_int w) runN)
              (native_int_pow2 (native_nat_to_int w))))
    rw [show
        __smtx_typeof (SmtTerm.bvnot (__eo_to_smt b)) =
          __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_38]]
    rw [hBTy]
    change SmtType.BitVec w =
      __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total
            (native_binary_not (native_nat_to_int w) runN)
            (native_int_pow2 (native_nat_to_int w))))
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runN) := by
      rw [hRunB] at hRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
            SmtTerm.Binary (native_nat_to_int w) runN by
        rfl] at hRel
      rw [__smtx_model_eval.eq_5] at hRel
      exact hRel
    have hEvalB :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runN :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runN hRelValue
    rw [show
        __smtx_model_eval M (SmtTerm.bvnot (__eo_to_smt b)) =
          __smtx_model_eval_bvnot
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hEvalB]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_nat_to_int w)
          (native_mod_total
            (native_binary_not (native_nat_to_int w) runN)
            (native_int_pow2 (native_nat_to_int w))))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_not (native_nat_to_int w) runN)
              (native_int_pow2 (native_nat_to_int w)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_not (native_nat_to_int w) runN)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_not (native_nat_to_int w) runN)
              (native_int_pow2 (native_nat_to_int w))) by
    rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvneg_core
    (M : SmtModel) (hM : model_total_typed M)
    (b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A < sizeOf (Term.Apply (Term.UOp UserOp.bvneg) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M (Term.Apply (Term.UOp UserOp.bvneg) b) := by
  intro hATrans hEvalTy
  have hBvNegNN :
      term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_unop_arg_of_non_none
      (op := SmtTerm.bvneg) (t := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_46])
      hBvNegNN with
    ⟨w, hBTy⟩
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvNegEoType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvnot (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hBEoBv]
    rfl
  have hRunNegNe : __eo_neg (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvneg) b))
            (__eo_neg (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.UOp UserOp.bvneg) b))
          (__eo_neg (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_neg (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunNegNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvneg) b))
            (__eo_neg (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.UOp UserOp.bvneg) b))
            (__eo_neg (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunNegEoBv :
      __eo_typeof (__eo_neg (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.UOp UserOp.bvneg) b)
        (__eo_neg (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvNegEoType
  rcases eo_neg_arg_binary_of_typeof_bitvec
      (__run_evaluate b) (native_nat_to_int w) hRunNegEoBv with
    ⟨runN, hRunB⟩
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_arg M (Term.UOp UserOp.bvneg) b rec
      hBTrans hBProgTy with
    ⟨_hSameTy, hRel⟩
  change
    __smtx_typeof (SmtTerm.bvneg (__eo_to_smt b)) =
        __smtx_typeof (__eo_to_smt (__eo_neg (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt b)))
        (__smtx_model_eval M (__eo_to_smt (__eo_neg (__run_evaluate b))))
  rw [hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvneg (__eo_to_smt b)) =
        __smtx_typeof
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total (native_zneg runN)
              (native_int_pow2 (native_nat_to_int w))))
    rw [show
        __smtx_typeof (SmtTerm.bvneg (__eo_to_smt b)) =
          __smtx_typeof_bv_op_1 (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_46]]
    rw [hBTy]
    change SmtType.BitVec w =
      __smtx_typeof
        (SmtTerm.Binary (native_nat_to_int w)
          (native_mod_total (native_zneg runN)
            (native_int_pow2 (native_nat_to_int w))))
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runN) := by
      rw [hRunB] at hRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runN) =
            SmtTerm.Binary (native_nat_to_int w) runN by
        rfl] at hRel
      rw [__smtx_model_eval.eq_5] at hRel
      exact hRel
    have hEvalB :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runN :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runN hRelValue
    rw [show
        __smtx_model_eval M (SmtTerm.bvneg (__eo_to_smt b)) =
          __smtx_model_eval_bvneg
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_46]]
    rw [hEvalB]
    change
      RuleProofs.smt_value_rel
        (SmtValue.Binary (native_nat_to_int w)
          (native_mod_total (native_zneg runN)
            (native_int_pow2 (native_nat_to_int w))))
        (__smtx_model_eval M
          (SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total (native_zneg runN)
              (native_int_pow2 (native_nat_to_int w)))))
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total (native_zneg runN)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total (native_zneg runN)
              (native_int_pow2 (native_nat_to_int w))) by
    rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvand_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b) := by
  intro hATrans hEvalTy
  have hBvAndNN :
      term_has_non_none_type
        (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvand) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_39]) hBvAndNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvAndEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunAndNe :
      __eo_and (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
          (__eo_and (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_and (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAndNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b))
            (__eo_and (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAndEoBv :
      __eo_typeof (__eo_and (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) a) b)
        (__eo_and (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvAndEoType
  rcases eo_and_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunAndEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvand) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvand) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_and (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_and
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_and
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_and, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_39]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvand
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvand
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_and
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_and, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_and (native_nat_to_int w) runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_and (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvor_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b) := by
  intro hATrans hEvalTy
  have hBvOrNN :
      term_has_non_none_type
        (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvor) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_40]) hBvOrNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvOrEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunOrNe :
      __eo_or (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
          (__eo_or (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_or (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunOrNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b))
            (__eo_or (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunOrEoBv :
      __eo_typeof (__eo_or (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) a) b)
        (__eo_or (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvOrEoType
  rcases eo_or_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunOrEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvor) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvor) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_or (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_or
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_or
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_or, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_40]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvor
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvor
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_or
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_or, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_or (native_nat_to_int w) runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_or (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvxor_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b) := by
  intro hATrans hEvalTy
  have hBvXorNN :
      term_has_non_none_type
        (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvxor) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_43]) hBvXorNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvXorEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunXorNe :
      __eo_xor (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
          (__eo_xor (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_xor (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunXorNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunXorEoBv :
      __eo_typeof (__eo_xor (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) a) b)
        (__eo_xor (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvXorEoType
  rcases eo_xor_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunXorEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvxor) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvxor) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_xor
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_xor
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_xor, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_43]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvxor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvxor
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvxor
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_xor
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_xor, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_binary_xor (native_nat_to_int w) runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_binary_xor (native_nat_to_int w) runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvadd_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) := by
  intro hATrans hEvalTy
  have hBvAddNN :
      term_has_non_none_type
        (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvadd) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_47]) hBvAddNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvAddEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunAddNe :
      __eo_add (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
          (__eo_add (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_add (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunAddNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b))
            (__eo_add (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunAddEoBv :
      __eo_typeof (__eo_add (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) a) b)
        (__eo_add (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvAddEoType
  rcases eo_add_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunAddEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvadd) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvadd) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_add (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_47]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvadd (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvadd
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_47]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvadd
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zplus runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvmul_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b) := by
  intro hATrans hEvalTy
  have hBvMulNN :
      term_has_non_none_type
        (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvmul) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_48]) hBvMulNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvMulEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunMulNe :
      __eo_mul (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
          (__eo_mul (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_mul (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunMulNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b))
            (__eo_mul (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunMulEoBv :
      __eo_typeof (__eo_mul (__run_evaluate a) (__run_evaluate b)) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) a) b)
        (__eo_mul (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hBvMulEoType
  rcases eo_mul_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__run_evaluate b) (native_nat_to_int w)
      hRunMulEoBv with
    ⟨runA, runB, hRunA, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvmul) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvmul) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_mul (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_mul
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)))
    rw [show
        __eo_to_smt
            (__eo_mul
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_mul, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_48]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvmul (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvmul
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_48]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvmul
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_mul
              (Term.Binary (native_nat_to_int w) runA)
              (Term.Binary (native_nat_to_int w) runB)) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_mul, __eo_requires, native_ite, native_teq, native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zmult runA runB)
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zmult runA runB)
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

private theorem run_evaluate_sound_apply_bvsub_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b) := by
  intro hATrans hEvalTy
  have hBvSubNN :
      term_has_non_none_type
        (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) := by
    unfold term_has_non_none_type
    simpa [RuleProofs.eo_has_smt_translation] using hATrans
  rcases bv_binop_args_of_non_none
      (op := SmtTerm.bvsub) (t1 := __eo_to_smt a) (t2 := __eo_to_smt b)
      (by rw [__smtx_typeof.eq_51]) hBvSubNN with
    ⟨w, hATy, hBTy⟩
  have hATransA : RuleProofs.eo_has_smt_translation a := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hATy]
    simp
  have hBTrans : RuleProofs.eo_has_smt_translation b := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBTy]
    simp
  have hAMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATransA
  have hBMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation b hBTrans
  have hAEoBv :
      __eo_typeof a =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hAMatch.symm.trans hATy)
  have hBEoBv :
      __eo_typeof b =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec (hBMatch.symm.trans hBTy)
  have hBvSubEoType :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    change __eo_typeof_bvand (__eo_typeof a) (__eo_typeof b) =
      Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w))
    rw [hAEoBv, hBEoBv]
    simp [__eo_typeof_bvand, __eo_requires, __eo_eq, native_ite,
      native_teq, native_not]
  have hRunSubNe :
      __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
          (__eo_add (__run_evaluate a)
            (__eo_neg (__run_evaluate b))) ≠
        Term.Stuck := by
    intro hMk
    cases hRun :
        __eo_add (__run_evaluate a) (__eo_neg (__run_evaluate b)) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunSubNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b))
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunSubEoBv :
      __eo_typeof
          (__eo_add (__run_evaluate a)
            (__eo_neg (__run_evaluate b))) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) a) b)
        (__eo_add (__run_evaluate a)
          (__eo_neg (__run_evaluate b))) hEvalEqTy
    exact hEq.symm.trans hBvSubEoType
  rcases eo_add_args_binary_of_typeof_bitvec
      (__run_evaluate a) (__eo_neg (__run_evaluate b))
      (native_nat_to_int w) hRunSubEoBv with
    ⟨runA, runNegB, hRunA, hRunNegB⟩
  rcases eo_neg_arg_binary_of_eq_binary
      (__run_evaluate b) (native_nat_to_int w) runNegB hRunNegB with
    ⟨runB, hRunB⟩
  have hRunAEoType :
      __eo_typeof (__run_evaluate a) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunA]
    rfl
  have hRunBEoType :
      __eo_typeof (__run_evaluate b) =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) := by
    rw [hRunB]
    rfl
  have hBvTypeNe :
      Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) ≠
        Term.Stuck := by
    intro h
    cases h
  have hAProgTy : __eo_typeof (__eo_prog_evaluate a) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof a
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation a hATransA)
      hBvTypeNe hAEoBv hRunAEoType
  have hBProgTy : __eo_typeof (__eo_prog_evaluate b) = Term.Bool :=
    eo_prog_evaluate_typeof_bool_of_same_type_and_run_typeof b
      (Term.Apply (Term.UOp UserOp.BitVec)
        (Term.Numeral (native_nat_to_int w)))
      (RuleProofs.term_ne_stuck_of_has_smt_translation b hBTrans)
      hBvTypeNe hBEoBv hRunBEoType
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.bvsub) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.bvsub) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_add (__run_evaluate a)
              (__eo_neg (__run_evaluate b)))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (__eo_neg (Term.Binary (native_nat_to_int w) runB))))
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (__eo_neg (Term.Binary (native_nat_to_int w) runB))) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_neg, __eo_requires, native_ite, native_teq,
        native_not]
      rfl]
    rw [show
        __smtx_typeof (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt a))
            (__smtx_typeof (__eo_to_smt b)) by
      rw [__smtx_typeof.eq_51]]
    rw [hATy, hBTy]
    simp [__smtx_typeof_bv_op_2, native_ite, native_nateq]
    rw [smtx_typeof_binary_mod_nat_to_int]
  · have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Binary (native_nat_to_int w) runA) := by
      rw [hRunA] at hARel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runA) =
            SmtTerm.Binary (native_nat_to_int w) runA by
        rfl] at hARel
      rw [__smtx_model_eval.eq_5] at hARel
      exact hARel
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Binary (native_nat_to_int w) runB) := by
      rw [hRunB] at hBRel
      rw [show
          __eo_to_smt (Term.Binary (native_nat_to_int w) runB) =
            SmtTerm.Binary (native_nat_to_int w) runB by
        rfl] at hBRel
      rw [__smtx_model_eval.eq_5] at hBRel
      exact hBRel
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) =
          SmtValue.Binary (native_nat_to_int w) runA :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt a))
        (native_nat_to_int w) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) =
          SmtValue.Binary (native_nat_to_int w) runB :=
      smt_value_rel_binary_eq
        (__smtx_model_eval M (__eo_to_smt b))
        (native_nat_to_int w) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.bvsub (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_bvsub
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      rw [__smtx_model_eval.eq_51]]
    rw [hAEval, hBEval]
    rw [show
        __smtx_model_eval_bvsub
            (SmtValue.Binary (native_nat_to_int w) runA)
            (SmtValue.Binary (native_nat_to_int w) runB) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      rfl]
    rw [show
        __eo_to_smt
            (__eo_add
              (Term.Binary (native_nat_to_int w) runA)
              (__eo_neg (Term.Binary (native_nat_to_int w) runB))) =
          SmtTerm.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      simp [__eo_add, __eo_neg, __eo_requires, native_ite, native_teq,
        native_not]
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Binary (native_nat_to_int w)
              (native_mod_total
                (native_zplus runA
                  (native_mod_total (native_zneg runB)
                    (native_int_pow2 (native_nat_to_int w))))
                (native_int_pow2 (native_nat_to_int w)))) =
          SmtValue.Binary (native_nat_to_int w)
            (native_mod_total
              (native_zplus runA
                (native_mod_total (native_zneg runB)
                  (native_int_pow2 (native_nat_to_int w))))
              (native_int_pow2 (native_nat_to_int w))) by
      rw [__smtx_model_eval.eq_5]]
    exact RuleProofs.smt_value_rel_refl _

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

private theorem run_evaluate_sound_apply_xor_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) := by
  intro hATrans hEvalTy
  have hXorBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) :=
    has_bool_type_xor_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    has_bool_type_xor_left a b hXorBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    has_bool_type_xor_right a b hXorBool
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
  have hXorEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunXorNe :
      __eo_xor (__run_evaluate a) (__run_evaluate b) ≠ Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
          (__eo_xor (__run_evaluate a) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun : __eo_xor (__run_evaluate a) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunXorNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b))
            (__eo_xor (__run_evaluate a) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunXorEoBool :
      __eo_typeof (__eo_xor (__run_evaluate a) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) a) b)
        (__eo_xor (__run_evaluate a) (__run_evaluate b)) hEvalEqTy
    exact hEq.symm.trans hXorEoBool
  rcases eo_xor_args_boolean_of_typeof_bool
      (__run_evaluate a) (__run_evaluate b) hRunXorEoBool with
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
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.xor) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.xor) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt (__eo_xor (__run_evaluate a) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_xor runA runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_xor_eq, hATy, hBTy, __smtx_typeof.eq_1]
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
    have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Boolean runA) := by
      simpa [__smtx_model_eval] using hARelBool
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean runB) := by
      simpa [__smtx_model_eval] using hBRelBool
    have hAEval :
        __smtx_model_eval M (__eo_to_smt a) = SmtValue.Boolean runA :=
      smt_value_rel_boolean_eq
        (__smtx_model_eval M (__eo_to_smt a)) runA hARelValue
    have hBEval :
        __smtx_model_eval M (__eo_to_smt b) = SmtValue.Boolean runB :=
      smt_value_rel_boolean_eq
        (__smtx_model_eval M (__eo_to_smt b)) runB hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.xor (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_xor
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [hAEval, hBEval]
    rw [show
        __eo_to_smt
            (__eo_xor (Term.Boolean runA) (Term.Boolean runB)) =
          SmtTerm.Boolean (native_xor runA runB) by
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Boolean (native_xor runA runB)) =
          SmtValue.Boolean (native_xor runA runB) by
      simp [__smtx_model_eval]]
    cases runA <;> cases runB <;>
      simp [RuleProofs.smt_value_rel, __smtx_model_eval_xor,
        __smtx_model_eval_not, __smtx_model_eval_eq, native_xor,
        native_not, native_veq]

private theorem run_evaluate_sound_apply_imp_core
    (M : SmtModel) (hM : model_total_typed M)
    (a b : Term)
    (rec :
      ∀ A : Term,
        sizeOf A <
            sizeOf (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) ->
          RunEvaluateSoundGoal M A) :
  RunEvaluateSoundGoal M
    (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) := by
  intro hATrans hEvalTy
  have hImpBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) :=
    has_bool_type_imp_of_has_translation a b hATrans
  have hABool : RuleProofs.eo_has_bool_type a :=
    has_bool_type_imp_left a b hImpBool
  have hBBool : RuleProofs.eo_has_bool_type b :=
    has_bool_type_imp_right a b hImpBool
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
  have hImpEoBool :
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b) =
        Term.Bool := by
    change __eo_typeof_or (__eo_typeof a) (__eo_typeof b) = Term.Bool
    rw [hAEoBool, hBEoBool]
    rfl
  have hRunImpNe :
      __eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b) ≠
        Term.Stuck := by
    intro hStuck
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [hStuck] at hEvalTy
    change Term.Stuck = Term.Bool at hEvalTy
    cases hEvalTy
  have hMkNe :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.eq)
            (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
          (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b)) ≠
        Term.Stuck := by
    intro hMk
    cases hRun :
        __eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b) <;>
      simp [__eo_mk_apply, hRun] at hMk hRunImpNe
  have hEvalEqTy :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) =
        Term.Bool := by
    change
      __eo_typeof
          (__eo_mk_apply
            (Term.Apply (Term.UOp UserOp.eq)
              (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b))
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) =
        Term.Bool at hEvalTy
    rw [eo_mk_apply_eq_apply_of_ne_stuck _ _ hMkNe] at hEvalTy
    exact hEvalTy
  have hRunImpEoBool :
      __eo_typeof
          (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b)) =
        Term.Bool := by
    have hEq :=
      evaluate_apply_eq_typeof_bool_operands_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) a) b)
        (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))
        hEvalEqTy
    exact hEq.symm.trans hImpEoBool
  rcases eo_or_args_boolean_of_typeof_bool
      (__eo_not (__run_evaluate a)) (__run_evaluate b)
      hRunImpEoBool with
    ⟨runNotA, runB, hRunNotA, hRunB⟩
  have hRunNotAEoBool : __eo_typeof (__eo_not (__run_evaluate a)) = Term.Bool := by
    rw [hRunNotA]
    rfl
  rcases eo_not_arg_boolean_of_typeof_bool
      (__run_evaluate a) hRunNotAEoBool with
    ⟨runA, hRunA⟩
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
  rcases run_evaluate_rec_apply_apply_arg M (Term.UOp UserOp.imp) a b rec
      hATransA hAProgTy with
    ⟨_hASameTy, hARel⟩
  rcases run_evaluate_rec_apply_arg M
      (Term.Apply (Term.UOp UserOp.imp) a) b rec hBTrans hBProgTy with
    ⟨_hBSameTy, hBRel⟩
  change
    __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof
          (__eo_to_smt
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)))
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_or (__eo_not (__run_evaluate a)) (__run_evaluate b))))
  rw [hRunA, hRunB]
  constructor
  · change
      __smtx_typeof (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
        __smtx_typeof (SmtTerm.Boolean (native_or (native_not runA) runB))
    have hATy : __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hABool
    have hBTy : __smtx_typeof (__eo_to_smt b) = SmtType.Bool := by
      simpa [RuleProofs.eo_has_bool_type] using hBBool
    rw [typeof_imp_eq, hATy, hBTy, __smtx_typeof.eq_1]
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
    have hARelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt a))
          (SmtValue.Boolean runA) := by
      simpa [__smtx_model_eval] using hARelBool
    have hBRelValue :
        RuleProofs.smt_value_rel
          (__smtx_model_eval M (__eo_to_smt b))
          (SmtValue.Boolean runB) := by
      simpa [__smtx_model_eval] using hBRelBool
    have hRelImp :=
      smt_value_rel_model_eval_imp_of_rel
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt b))
        (SmtValue.Boolean runA)
        (SmtValue.Boolean runB)
        hARelValue hBRelValue
    rw [show
        __smtx_model_eval M
            (SmtTerm.imp (__eo_to_smt a) (__eo_to_smt b)) =
          __smtx_model_eval_imp
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt b)) by
      simp [__smtx_model_eval]]
    rw [show
        __eo_to_smt
            (__eo_or (__eo_not (Term.Boolean runA)) (Term.Boolean runB)) =
          SmtTerm.Boolean (native_or (native_not runA) runB) by
      rfl]
    rw [show
        __smtx_model_eval M
            (SmtTerm.Boolean (native_or (native_not runA) runB)) =
          SmtValue.Boolean (native_or (native_not runA) runB) by
      simp [__smtx_model_eval]]
    simpa [__smtx_model_eval_imp, __smtx_model_eval_not, __smtx_model_eval_or]
      using hRelImp

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
      match op with
      | UserOp.not =>
          exact run_evaluate_sound_apply_not_core M hM x rec hATrans hEvalTy
      | UserOp.bvnot =>
          exact run_evaluate_sound_apply_bvnot_core M hM x rec hATrans hEvalTy
      | UserOp.bvneg =>
          exact run_evaluate_sound_apply_bvneg_core M hM x rec hATrans hEvalTy
      | UserOp.bvnego =>
          exact False.elim (hActive rfl)
      | UserOp.bvredand =>
          exact False.elim (hActive rfl)
      | UserOp.bvredor =>
          exact False.elim (hActive rfl)
      | _ =>
          first
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
          match op with
          | UserOp.and =>
              exact run_evaluate_sound_apply_and_core M hM y x rec hATrans hEvalTy
          | UserOp.or =>
              exact run_evaluate_sound_apply_or_core M hM y x rec hATrans hEvalTy
          | UserOp.imp =>
              exact run_evaluate_sound_apply_imp_core M hM y x rec hATrans hEvalTy
          | UserOp.xor =>
              exact run_evaluate_sound_apply_xor_core M hM y x rec hATrans hEvalTy
          | UserOp.bvand =>
              exact run_evaluate_sound_apply_bvand_core M hM y x rec hATrans hEvalTy
          | UserOp.bvor =>
              exact run_evaluate_sound_apply_bvor_core M hM y x rec hATrans hEvalTy
          | UserOp.bvxor =>
              exact run_evaluate_sound_apply_bvxor_core M hM y x rec hATrans hEvalTy
          | UserOp.bvadd =>
              exact run_evaluate_sound_apply_bvadd_core M hM y x rec hATrans hEvalTy
          | UserOp.bvmul =>
              exact run_evaluate_sound_apply_bvmul_core M hM y x rec hATrans hEvalTy
          | UserOp.bvsub =>
              exact run_evaluate_sound_apply_bvsub_core M hM y x rec hATrans hEvalTy
          | UserOp.bvsdiv =>
              exact False.elim (hActive rfl)
          | UserOp.bvsrem =>
              exact False.elim (hActive rfl)
          | UserOp.bvsmod =>
              exact False.elim (hActive rfl)
          | UserOp.bvnand =>
              exact False.elim (hActive rfl)
          | UserOp.bvnor =>
              exact False.elim (hActive rfl)
          | UserOp.bvxnor =>
              exact False.elim (hActive rfl)
          | UserOp.bvcomp =>
              exact False.elim (hActive rfl)
          | UserOp.bvuaddo =>
              exact False.elim (hActive rfl)
          | UserOp.bvsaddo =>
              exact False.elim (hActive rfl)
          | UserOp.bvumulo =>
              exact False.elim (hActive rfl)
          | UserOp.bvsmulo =>
              exact False.elim (hActive rfl)
          | UserOp.bvusubo =>
              exact False.elim (hActive rfl)
          | UserOp.bvssubo =>
              exact False.elim (hActive rfl)
          | UserOp.bvsdivo =>
              exact False.elim (hActive rfl)
          | UserOp.bvultbv =>
              exact False.elim (hActive rfl)
          | UserOp.bvsltbv =>
              exact False.elim (hActive rfl)
          | _ =>
              sorry
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
