import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def quant_unused_lhs (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def quant_unused_formula (Q x F G : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) (quant_unused_lhs Q x F)) G

private theorem eo_requires_eq_result_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    __eo_requires x y z = z := by
  intro h
  by_cases hxy : native_teq x y = true
  · by_cases hxOk : native_not (native_teq x Term.Stuck) = true
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite]
    · simp [__eo_requires, hxy, hxOk, SmtEval.native_ite] at h
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

private theorem eo_requires_eq_of_ne_stuck (x y z : Term) :
    __eo_requires x y z ≠ Term.Stuck ->
    x = y := by
  intro h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [__eo_requires, hxy, SmtEval.native_ite] at h

private theorem quant_unused_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = quant_unused_formula Q x F G ∧
      __mk_quant Q (__mk_quant_unused_vars_rec x F) F = G ∧
      __eo_prog_quant_unused_vars x1 = quant_unused_formula Q x F G := by
  intro hProg
  cases x1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhsArg with
                  | Apply qx F =>
                      cases qx with
                      | Apply Q x =>
                          let guard := __mk_quant Q (__mk_quant_unused_vars_rec x F) F
                          let formula := quant_unused_formula Q x F G
                          have hReq : __eo_requires guard G formula ≠ Term.Stuck := by
                            simpa [guard, formula, quant_unused_formula, quant_unused_lhs,
                              __eo_prog_quant_unused_vars] using hProg
                          have hGuard : guard = G :=
                            eo_requires_eq_of_ne_stuck guard G formula hReq
                          have hProgEq :
                              __eo_prog_quant_unused_vars (quant_unused_formula Q x F G) =
                                quant_unused_formula Q x F G := by
                            have hReqEq :
                                __eo_requires guard G formula = formula :=
                              eo_requires_eq_result_of_ne_stuck guard G formula hReq
                            simpa [guard, formula, quant_unused_formula, quant_unused_lhs,
                              __eo_prog_quant_unused_vars] using hReqEq
                          exact ⟨Q, x, F, G, rfl, hGuard, hProgEq⟩
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

private theorem quant_unused_has_translation_of_input
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    RuleProofs.eo_has_smt_translation (__eo_prog_quant_unused_vars x1) := by
  intro hTrans hProg
  rcases quant_unused_shape_of_not_stuck x1 hProg with
    ⟨Q, x, F, G, hx1, _hGuard, hProgEq⟩
  rw [hProgEq]
  simpa [hx1] using hTrans

private theorem native_model_push_shadow
    (M : SmtModel) (s : native_String) (T : SmtType)
    (v₁ v₂ : SmtValue) :
    native_model_push (native_model_push M s T v₁) s T v₂ =
      native_model_push M s T v₂ := by
  cases M
  simp [native_model_push]
  funext s' T'
  by_cases h : s' = s ∧ T' = T <;> simp [h]

private theorem native_model_push_comm
    (M : SmtModel)
    (s₁ s₂ : native_String) (T₁ T₂ : SmtType)
    (v₁ v₂ : SmtValue)
    (hNe : ¬ (s₁ = s₂ ∧ T₁ = T₂)) :
    native_model_push (native_model_push M s₁ T₁ v₁) s₂ T₂ v₂ =
      native_model_push (native_model_push M s₂ T₂ v₂) s₁ T₁ v₁ := by
  cases M
  simp [native_model_push]
  funext s' T'
  by_cases h₁ : s' = s₁ ∧ T' = T₁
  · by_cases h₂ : s' = s₂ ∧ T' = T₂
    · have hSame : s₁ = s₂ ∧ T₁ = T₂ := by
        exact ⟨h₁.1.symm.trans h₂.1, h₁.2.symm.trans h₂.2⟩
      exact False.elim (hNe hSame)
    · simp [h₁]
      intro hs hT
      exact False.elim (h₂ ⟨h₁.1.trans hs, h₁.2.trans hT⟩)
  · by_cases h₂ : s' = s₂ ∧ T' = T₂
    · simp [h₂]
      intro hs hT
      exact False.elim (h₁ ⟨h₂.1.trans hs, h₂.2.trans hT⟩)
    · simp [h₁, h₂]

private theorem native_model_var_lookup_push_same
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue)
    (hWF : __smtx_type_wf T = true)
    (hv : __smtx_typeof_value v = T)
    (hCan : __smtx_value_canonical_bool v = true) :
    native_model_var_lookup (native_model_push M s T v) s T = v := by
  simp [native_model_var_lookup, native_model_push, hWF, hv, hCan, native_Teq,
    native_and]

private theorem native_model_var_lookup_push_other
    (M : SmtModel) (s s' : native_String) (T T' : SmtType) (v : SmtValue)
    (hNe : ¬ (s' = s ∧ T' = T)) :
    native_model_var_lookup (native_model_push M s T v) s' T' =
      native_model_var_lookup M s' T' := by
  by_cases hWF : __smtx_type_wf T' = true
  · simp [native_model_var_lookup, native_model_push, hWF, hNe]
  · have hWF' : __smtx_type_wf T' = false := by
      cases h : __smtx_type_wf T' with
      | false => rfl
      | true => exact False.elim (hWF h)
    simp [native_model_var_lookup, hWF']

private theorem smtx_model_eval_exists_of_push_irrel
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hIrrel :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
        __smtx_value_canonical v ->
        __smtx_model_eval (native_model_push M s T v) body =
          __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.exists s T body) =
      __smtx_model_eval M body := by
  classical
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with ⟨b, hb⟩
  let P : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true
  cases b
  · have hNotP : ¬ P := by
      intro hSat
      rcases hSat with ⟨v, hv, hCan, hEval⟩
      have hCan' : __smtx_value_canonical v := by
        simpa [__smtx_value_canonical] using hCan
      have hIrrelV := hIrrel v hv hCan'
      rw [hb] at hIrrelV
      rw [hEval] at hIrrelV
      cases hIrrelV
    have hPropEq : P = False := propext ⟨fun h => False.elim (hNotP h), False.elim⟩
    simp [P, __smtx_model_eval, hPropEq, hb]
  · have hDefTy : __smtx_typeof_value (__smtx_type_default T) = T :=
      type_default_typed_of_type_wf T hWF
    have hDefCan : __smtx_value_canonical (__smtx_type_default T) :=
      type_default_canonical_of_type_wf T hWF
    have hDefCanBool :
        __smtx_value_canonical_bool (__smtx_type_default T) = true := by
      simpa [__smtx_value_canonical] using hDefCan
    have hP : P := by
      refine ⟨__smtx_type_default T, hDefTy, hDefCanBool, ?_⟩
      rw [hIrrel (__smtx_type_default T) hDefTy hDefCan]
      exact hb
    have hPropEq : P = True := propext ⟨fun _ => trivial, fun _ => hP⟩
    simp [P, __smtx_model_eval, hPropEq, hb]

private theorem smtx_model_eval_forall_of_push_irrel
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hIrrel :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
        __smtx_value_canonical v ->
        __smtx_model_eval (native_model_push M s T v) body =
          __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.forall s T body) =
      __smtx_model_eval M body := by
  classical
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with ⟨b, hb⟩
  let P : Prop :=
    ∀ v : SmtValue,
      __smtx_typeof_value v = T ->
        __smtx_value_canonical_bool v = true ->
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true
  cases b
  · have hNotP : ¬ P := by
      intro hAll
      have hDefTy : __smtx_typeof_value (__smtx_type_default T) = T :=
        type_default_typed_of_type_wf T hWF
      have hDefCan : __smtx_value_canonical (__smtx_type_default T) :=
        type_default_canonical_of_type_wf T hWF
      have hDefCanBool :
          __smtx_value_canonical_bool (__smtx_type_default T) = true := by
        simpa [__smtx_value_canonical] using hDefCan
      have hEvalTrue :=
        hAll (__smtx_type_default T) hDefTy hDefCanBool
      have hIrrelDef := hIrrel (__smtx_type_default T) hDefTy hDefCan
      rw [hb] at hIrrelDef
      rw [hIrrelDef] at hEvalTrue
      cases hEvalTrue
    have hPropEq : P = False := propext ⟨fun h => False.elim (hNotP h), False.elim⟩
    simp [P, __smtx_model_eval, hPropEq, hb]
  · have hP : P := by
      intro v hv hCan
      have hCan' : __smtx_value_canonical v := by
        simpa [__smtx_value_canonical] using hCan
      rw [hIrrel v hv hCan']
      exact hb
    have hPropEq : P = True := propext ⟨fun _ => trivial, fun _ => hP⟩
    simp [P, __smtx_model_eval, hPropEq, hb]

private theorem smtx_model_eval_push_irrel_eo_to_smt_exists
    (s : native_String) (T : SmtType) (v : SmtValue) (body : SmtTerm)
    (hIrrel :
      ∀ M : SmtModel,
        __smtx_model_eval (native_model_push M s T v) body =
          __smtx_model_eval M body) :
    ∀ (M : SmtModel) (xs : Term),
      __smtx_model_eval (native_model_push M s T v)
          (__eo_to_smt_exists xs body) =
        __smtx_model_eval M (__eo_to_smt_exists xs body)
  := by
    intro M xs
    fun_induction __eo_to_smt_exists xs body generalizing M <;> try simp [__eo_to_smt_exists]
    · simpa [__eo_to_smt_exists] using hIrrel M
    · rename_i s' T' vs F T'' ih
      classical
      cases hWF : __smtx_type_wf T''
      · simp [native_ite, __smtx_model_eval]
      · let tail := __eo_to_smt_exists vs F
        let P₁ : Prop :=
          ∃ w : SmtValue,
            __smtx_typeof_value w = T'' ∧
              __smtx_value_canonical_bool w = true ∧
              __smtx_model_eval
                  (native_model_push (native_model_push M s T v) s' T'' w) tail =
                SmtValue.Boolean true
        let P₂ : Prop :=
          ∃ w : SmtValue,
            __smtx_typeof_value w = T'' ∧
              __smtx_value_canonical_bool w = true ∧
              __smtx_model_eval (native_model_push M s' T'' w) tail =
                SmtValue.Boolean true
        have hEvalPushBinder :
            ∀ w : SmtValue,
              __smtx_model_eval
                  (native_model_push (native_model_push M s T v) s' T'' w) tail =
                __smtx_model_eval (native_model_push M s' T'' w) tail := by
          intro w
          by_cases hSame : s = s' ∧ T = T''
          · rcases hSame with ⟨rfl, rfl⟩
            rw [native_model_push_shadow]
          · rw [native_model_push_comm M s s' T T'' v w hSame]
            exact ih hIrrel (native_model_push M s' T'' w)
        have hProp : P₁ = P₂ := by
          apply propext
          constructor
          · intro h
            rcases h with ⟨w, hwTy, hwCan, hwEval⟩
            refine ⟨w, hwTy, hwCan, ?_⟩
            rwa [hEvalPushBinder w] at hwEval
          · intro h
            rcases h with ⟨w, hwTy, hwCan, hwEval⟩
            refine ⟨w, hwTy, hwCan, ?_⟩
            rwa [hEvalPushBinder w]
        simp [native_ite, __smtx_model_eval, P₁, P₂, tail, hProp]
    · simp [__smtx_model_eval]

private theorem generic_apply_type_of_non_special_head_local
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  cases f <;> simp [__smtx_typeof]

private theorem smtx_typeof_apply_none_local (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  have hGeneric : generic_apply_type SmtTerm.None x := by
    exact generic_apply_type_of_non_special_head_local _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, TranslationProofs.smtx_typeof_none]
  simp [__smtx_typeof_apply]

private theorem smtx_typeof_apply_apply_none_local (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None y) x) =
      SmtType.None := by
  have hGeneric : generic_apply_type (SmtTerm.Apply SmtTerm.None y) x := by
    exact generic_apply_type_of_non_special_head_local _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, smtx_typeof_apply_none_local y]
  simp [__smtx_typeof_apply]

private theorem smtx_typeof_eo_to_smt_list_nil :
    __smtx_typeof (__eo_to_smt Term.__eo_List_nil) = SmtType.None := by
  native_decide

private theorem smtx_typeof_eo_to_smt_list_cons (x xs : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons x) xs)) =
      SmtType.None := by
  change
    __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
          (__eo_to_smt xs)) = SmtType.None
  exact smtx_typeof_apply_apply_none_local (__eo_to_smt xs) (__eo_to_smt x)

private theorem eo_has_smt_translation_ne_stuck_local
    (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    t ≠ Term.Stuck :=
  RuleProofs.term_ne_stuck_of_has_smt_translation t

private theorem eo_ite_true_false_eq_false
    (c d : Term) :
    __eo_ite c (Term.Boolean true) d = Term.Boolean false ->
    c = Term.Boolean false ∧ d = Term.Boolean false := by
  cases c
  case Boolean b =>
    cases b <;> simp [__eo_ite, native_teq, native_ite]
  all_goals
    simp [__eo_ite, native_teq, native_ite]

private theorem contains_atomic_term_apply_false
    (f a x : Term) :
    __contains_atomic_term (Term.Apply f a) x = Term.Boolean false ->
    __contains_atomic_term f x = Term.Boolean false ∧
      __contains_atomic_term a x = Term.Boolean false := by
  intro h
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__contains_atomic_term] at h
  · have hIte :
        __eo_ite (__contains_atomic_term f x) (Term.Boolean true)
          (__contains_atomic_term a x) = Term.Boolean false := by
      simpa [__contains_atomic_term, hx] using h
    exact eo_ite_true_false_eq_false
      (__contains_atomic_term f x) (__contains_atomic_term a x) hIte

private theorem mk_quant_unused_vars_rec_ne_stuck_shape
    (x F : Term) :
    __mk_quant_unused_vars_rec x F ≠ Term.Stuck ->
    F ≠ Term.Stuck ∧
      (x = Term.__eo_List_nil ∨
        ∃ y ys, x = Term.Apply (Term.Apply Term.__eo_List_cons y) ys) := by
  intro h
  constructor
  · intro hF
    subst F
    apply h
    cases x <;> rfl
  · cases x with
    | __eo_List_nil =>
        exact Or.inl rfl
    | Apply f ys =>
        cases f with
        | Apply g y =>
            cases g with
            | __eo_List_cons =>
                exact Or.inr ⟨y, ys, rfl⟩
            | _ =>
                cases F <;> simp [__mk_quant_unused_vars_rec] at h
        | _ =>
            cases F <;> simp [__mk_quant_unused_vars_rec] at h
    | _ =>
        cases F <;> simp [__mk_quant_unused_vars_rec] at h

private theorem mk_quant_ne_stuck_parts
    (Q xs F : Term) :
    __mk_quant Q xs F ≠ Term.Stuck ->
    xs ≠ Term.Stuck ∧ F ≠ Term.Stuck := by
  intro h
  constructor
  · intro hxs
    subst xs
    cases Q <;> simp [__mk_quant] at h
  · intro hF
    subst F
    cases Q <;> cases xs <;> simp [__mk_quant] at h

private theorem typed___eo_prog_quant_unused_vars_impl
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_quant_unused_vars x1) = Term.Bool ->
    RuleProofs.eo_has_bool_type (__eo_prog_quant_unused_vars x1) := by
  intro hTrans hProg hTy
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type
    (__eo_prog_quant_unused_vars x1)
    (quant_unused_has_translation_of_input x1 hTrans hProg)
    hTy

private theorem facts___eo_prog_quant_unused_vars_impl
    (M : SmtModel) (hM : model_total_typed M)
    (x1 : Term) :
    RuleProofs.eo_has_smt_translation x1 ->
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    __eo_typeof (__eo_prog_quant_unused_vars x1) = Term.Bool ->
    eo_interprets M (__eo_prog_quant_unused_vars x1) true := by
  intro hTrans hProg hTy
  rcases quant_unused_shape_of_not_stuck x1 hProg with
    ⟨Q, x, F, G, hx1, hGuard, hProgEq⟩
  have hBool :
      RuleProofs.eo_has_bool_type (quant_unused_formula Q x F G) := by
    rw [← hProgEq]
    exact typed___eo_prog_quant_unused_vars_impl x1 hTrans hProg hTy
  have hRhsTrans : RuleProofs.eo_has_smt_translation G := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (quant_unused_lhs Q x F) G hBool with ⟨hSame, hLhsNN⟩
    intro hNone
    apply hLhsNN
    rw [hSame, hNone]
  have hGNe : G ≠ Term.Stuck :=
    eo_has_smt_translation_ne_stuck_local G hRhsTrans
  have hMkNe :
      __mk_quant Q (__mk_quant_unused_vars_rec x F) F ≠ Term.Stuck := by
    intro hMk
    rw [hMk] at hGuard
    exact hGNe hGuard.symm
  have hRecNe : __mk_quant_unused_vars_rec x F ≠ Term.Stuck :=
    (mk_quant_ne_stuck_parts Q (__mk_quant_unused_vars_rec x F) F hMkNe).1
  have hFNe : F ≠ Term.Stuck :=
    (mk_quant_unused_vars_rec_ne_stuck_shape x F hRecNe).1
  have hXShape :
      x = Term.__eo_List_nil ∨
        ∃ y ys, x = Term.Apply (Term.Apply Term.__eo_List_cons y) ys :=
    (mk_quant_unused_vars_rec_ne_stuck_shape x F hRecNe).2
  rcases hXShape with hXNil | ⟨xHead, xTail, hXCons⟩
  · subst x
    unfold RuleProofs.eo_has_bool_type at hBool
    simp [quant_unused_formula, quant_unused_lhs] at hBool
    sorry
  · subst x
    sorry

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
  have hProg : __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠ Term.Stuck :=
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
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_unused_vars a1 ≠ Term.Stuck := by
                change __eo_prog_quant_unused_vars a1 ≠ Term.Stuck at hProg
                simpa using hProg
              have hTyQuant :
                  __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) = Term.Bool at hResultTy
                simpa using hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_quant_unused_vars a1) true
                exact facts___eo_prog_quant_unused_vars_impl M hM a1 hTransA1
                  hProgQuant hTyQuant
              · exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  (typed___eo_prog_quant_unused_vars_impl a1 hTransA1 hProgQuant hTyQuant)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
