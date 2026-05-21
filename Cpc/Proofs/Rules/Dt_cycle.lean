import Cpc.Proofs.RuleSupport.CnfSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_requires_self_of_non_stuck
    (T U : Term) :
    T ≠ Term.Stuck ->
    __eo_requires T T U = U := by
  intro hT
  simp [__eo_requires, native_ite, native_not, native_teq, hT]

private theorem prog_dt_cycle_condition_of_not_stuck
    (s t : Term) :
    __eo_prog_dt_cycle
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false)) ≠ Term.Stuck ->
    __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) = Term.Boolean true := by
  intro hProg
  have h :
      __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) = Term.Boolean true ∧
        __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) ≠ Term.Stuck := by
    simpa [__eo_prog_dt_cycle, __eo_requires, native_ite, native_teq, native_not,
      SmtEval.native_not] using hProg
  exact h.1

private theorem prog_dt_cycle_eq_input_of_not_stuck
    (s t : Term) :
    __eo_prog_dt_cycle
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false)) ≠ Term.Stuck ->
    __eo_prog_dt_cycle
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false)) =
      Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
        (Term.Boolean false) := by
  intro hProg
  have hCond : __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
      Term.Boolean true :=
    prog_dt_cycle_condition_of_not_stuck s t hProg
  have hCondNe :
      __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) ≠ Term.Stuck := by
    rw [hCond]
    simp
  simpa [__eo_prog_dt_cycle, hCond] using
    eo_requires_self_of_non_stuck
      (__dt_find_cycle t s (__is_cons_app t) (Term.Boolean false))
      (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
        (Term.Boolean false))
      hCondNe

private theorem prog_dt_cycle_shape_of_not_stuck
    (a : Term) :
    __eo_prog_dt_cycle a ≠ Term.Stuck ->
      ∃ s t,
        a =
          Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
            (Term.Boolean false) := by
  intro hProg
  cases a with
  | Apply outer b =>
      cases outer with
      | Apply eqOuter inner =>
          cases eqOuter with
          | UOp op =>
              cases op
              case eq =>
                cases inner with
                | Apply innerOuter t =>
                    cases innerOuter with
                    | Apply eqInner s =>
                        cases eqInner with
                        | UOp op2 =>
                            cases op2
                            case eq =>
                              cases b
                              case Boolean bb =>
                                cases bb
                                · exact ⟨s, t, rfl⟩
                                · simp [__eo_prog_dt_cycle] at hProg
                              all_goals simp [__eo_prog_dt_cycle] at hProg
                            all_goals simp [__eo_prog_dt_cycle] at hProg
                        | _ =>
                            simp [__eo_prog_dt_cycle] at hProg
                    | _ =>
                        simp [__eo_prog_dt_cycle] at hProg
                | _ =>
                    simp [__eo_prog_dt_cycle] at hProg
              all_goals simp [__eo_prog_dt_cycle] at hProg
          | _ =>
              simp [__eo_prog_dt_cycle] at hProg
      | _ =>
          simp [__eo_prog_dt_cycle] at hProg
  | _ =>
      simp [__eo_prog_dt_cycle] at hProg

private def smtValueSize : SmtValue -> Nat
  | SmtValue.Apply f x => smtValueSize f + smtValueSize x + 1
  | _ => 1

private theorem smtValueSize_apply_left_lt (f x : SmtValue) :
    smtValueSize f < smtValueSize (SmtValue.Apply f x) := by
  simp [smtValueSize]
  omega

private theorem smtValueSize_apply_right_lt (f x : SmtValue) :
    smtValueSize x < smtValueSize (SmtValue.Apply f x) := by
  simp [smtValueSize]
  omega

private theorem model_eval_eq_false_of_ne_not_reglan_pair
    {v₁ v₂ : SmtValue}
    (hNe : v₁ ≠ v₂)
    (hReg :
      ¬ ∃ r₁ r₂, v₁ = SmtValue.RegLan r₁ ∧ v₂ = SmtValue.RegLan r₂) :
    __smtx_model_eval_eq v₁ v₂ = SmtValue.Boolean false := by
  cases v₁ <;> cases v₂ <;>
    simp [__smtx_model_eval_eq, native_veq] at hNe hReg ⊢
  all_goals
    first
    | exact False.elim hReg
    | simpa using hNe

private theorem smt_type_ne_reglan_of_same_type_and_size_lt
    {v₁ v₂ : SmtValue} {T : SmtType}
    (hTy₁ : __smtx_typeof_value v₁ = T)
    (hTy₂ : __smtx_typeof_value v₂ = T)
    (hSize : smtValueSize v₁ < smtValueSize v₂) :
    T ≠ SmtType.RegLan := by
  intro hT
  subst hT
  rcases reglan_value_canonical hTy₁ with ⟨r₁, rfl⟩
  rcases reglan_value_canonical hTy₂ with ⟨r₂, rfl⟩
  simp [smtValueSize] at hSize

private theorem smt_value_dtc_shape
    {v : SmtValue} {A B : SmtType}
    (h : __smtx_typeof_value v = SmtType.DtcAppType A B) :
    (∃ s d i, v = SmtValue.DtCons s d i) ∨
      ∃ f x, v = SmtValue.Apply f x := by
  cases v with
  | NotValue =>
      simp [__smtx_typeof_value] at h
  | Boolean _ =>
      simp [__smtx_typeof_value] at h
  | Numeral _ =>
      simp [__smtx_typeof_value] at h
  | Rational _ =>
      simp [__smtx_typeof_value] at h
  | Binary w n =>
      cases hWidth : native_zleq 0 w <;>
        cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and,
            hWidth, hMod] at h
  | Map m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          simp [__smtx_typeof_value, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Fun _ _ _ =>
      simp [__smtx_typeof_value] at h
  | Set m =>
      cases typeof_map_value_shape m with
      | inl hMap =>
          rcases hMap with ⟨T, U, hMap⟩
          cases U <;> simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at h
      | inr hNone =>
          simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at h
  | Seq ss =>
      cases typeof_seq_value_shape ss with
      | inl hSeq =>
          rcases hSeq with ⟨T, hSeq⟩
          simp [__smtx_typeof_value, hSeq] at h
      | inr hNone =>
          simp [__smtx_typeof_value, hNone] at h
  | Char _ =>
      simp [__smtx_typeof_value] at h
  | UValue _ _ =>
      simp [__smtx_typeof_value] at h
  | RegLan _ =>
      simp [__smtx_typeof_value] at h
  | DtCons s d i =>
      exact Or.inl ⟨s, d, i, rfl⟩
  | Apply f x =>
      exact Or.inr ⟨f, x, rfl⟩

private theorem smt_eval_apply_dt_size_gt_fun
    (M : SmtModel)
    {f x : SmtTerm} {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof_value (__smtx_model_eval M x) = A) :
    smtValueSize (__smtx_model_eval M f) <
      smtValueSize (__smtx_model_eval M (SmtTerm.Apply f x)) := by
  have hxNe : __smtx_model_eval M x ≠ SmtValue.NotValue := by
    intro hxNV
    rw [hxNV] at hx
    simp [__smtx_typeof_value] at hx
    exact hA hx.symm
  rw [__smtx_model_eval.eq_142 M f x
    (by
      intro s d i j hfEq
      subst hfEq
      simp [__smtx_model_eval, __smtx_typeof_value] at hf)
    (by
      intro s d i hfEq
      subst hfEq
      simp [__smtx_model_eval, __smtx_typeof_value] at hf)]
  rcases smt_value_dtc_shape hf with hShape | hShape
  · rcases hShape with ⟨s, d, i, hF⟩
    rw [hF]
    cases hxv : __smtx_model_eval M x <;>
      simp [hxv, __smtx_model_eval_apply, smtValueSize] at hxNe ⊢ <;>
      omega
  · rcases hShape with ⟨g, y, hF⟩
    rw [hF]
    cases hxv : __smtx_model_eval M x <;>
      simp [hxv, __smtx_model_eval_apply, smtValueSize] at hxNe ⊢ <;>
      omega

private theorem smt_eval_apply_dt_size_gt_arg
    (M : SmtModel)
    {f x : SmtTerm} {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof_value (__smtx_model_eval M x) = A) :
    smtValueSize (__smtx_model_eval M x) <
      smtValueSize (__smtx_model_eval M (SmtTerm.Apply f x)) := by
  have hxNe : __smtx_model_eval M x ≠ SmtValue.NotValue := by
    intro hxNV
    rw [hxNV] at hx
    simp [__smtx_typeof_value] at hx
    exact hA hx.symm
  rw [__smtx_model_eval.eq_142 M f x
    (by
      intro s d i j hfEq
      subst hfEq
      simp [__smtx_model_eval, __smtx_typeof_value] at hf)
    (by
      intro s d i hfEq
      subst hfEq
      simp [__smtx_model_eval, __smtx_typeof_value] at hf)]
  rcases smt_value_dtc_shape hf with hShape | hShape
  · rcases hShape with ⟨s, d, i, hF⟩
    rw [hF]
    cases hxv : __smtx_model_eval M x <;>
      simp [hxv, __smtx_model_eval_apply, smtValueSize] at hxNe ⊢ <;>
      omega
  · rcases hShape with ⟨g, y, hF⟩
    rw [hF]
    cases hxv : __smtx_model_eval M x <;>
      simp [hxv, __smtx_model_eval_apply, smtValueSize] at hxNe ⊢ <;>
      omega

private theorem eo_interprets_eq_false_of_size_lt
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term)
    (hEqBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply Term.eq s) t))
    (hSize :
      smtValueSize (__smtx_model_eval M (__eo_to_smt s)) <
        smtValueSize (__smtx_model_eval M (__eo_to_smt t))) :
    eo_interprets M (Term.Apply (Term.Apply Term.eq s) t) false := by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type s t hEqBool with
    ⟨hTyEq, hSNN⟩
  let T := __smtx_typeof (__eo_to_smt s)
  have hSTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) = T := by
    simpa [T] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt s)
        (by
          unfold term_has_non_none_type
          exact hSNN)
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    simpa [hTyEq] using hSNN
  have hTTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) = T := by
    simpa [T, hTyEq] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t)
        (by
          unfold term_has_non_none_type
          exact hTNN)
  have hTNeReg : T ≠ SmtType.RegLan :=
    smt_type_ne_reglan_of_same_type_and_size_lt hSTy hTTy hSize
  have hNe :
      __smtx_model_eval M (__eo_to_smt s) ≠
        __smtx_model_eval M (__eo_to_smt t) := by
    intro hEq
    rw [hEq] at hSize
    exact Nat.lt_irrefl _ hSize
  have hNoReg :
      ¬ ∃ r₁ r₂,
        __smtx_model_eval M (__eo_to_smt s) = SmtValue.RegLan r₁ ∧
          __smtx_model_eval M (__eo_to_smt t) = SmtValue.RegLan r₂ := by
    rintro ⟨r₁, r₂, hS, _hT⟩
    have hReg : T = SmtType.RegLan := by
      rw [← hSTy, hS]
      rfl
    exact hTNeReg hReg
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  change smt_interprets M (SmtTerm.eq (__eo_to_smt s) (__eo_to_smt t)) false
  refine smt_interprets.intro_false M _ ?_ ?_
  · simpa [RuleProofs.eo_has_bool_type] using hEqBool
  · rw [__smtx_model_eval.eq_134]
    exact model_eval_eq_false_of_ne_not_reglan_pair hNe hNoReg

private theorem eo_has_bool_type_eq_left_of_eq_false_bool
    (s t : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
        (Term.Boolean false)) ->
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) := by
  intro hOuter
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.Apply Term.eq s) t) (Term.Boolean false) hOuter with
    ⟨hTy, _hNN⟩
  have hFalseTy :
      __smtx_typeof (__eo_to_smt (Term.Boolean false)) = SmtType.Bool := by
    change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
    rw [__smtx_typeof.eq_1]
  exact hTy.trans hFalseTy

private theorem dt_find_cycle_size_lt_of_same_type
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term)
    (hCycle :
      __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
        Term.Boolean true)
    (hEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t)) :
    smtValueSize (__smtx_model_eval M (__eo_to_smt s)) <
      smtValueSize (__smtx_model_eval M (__eo_to_smt t)) := by
  sorry

private theorem dt_cycle_inner_eq_false
    (M : SmtModel) (hM : model_total_typed M)
    (s t : Term)
    (hCycle :
      __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
        Term.Boolean true)
    (hEqBool : RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t)) :
    eo_interprets M (Term.Apply (Term.Apply Term.eq s) t) false := by
  exact eo_interprets_eq_false_of_size_lt M hM s t hEqBool
    (dt_find_cycle_size_lt_of_same_type M hM s t hCycle hEqBool)

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
      cases premises with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | cons a1 argsTail =>
      cases argsTail with
      | cons _ _ =>
          cases premises <;> change Term.Stuck ≠ Term.Stuck at hProg <;>
            exact False.elim (hProg rfl)
      | nil =>
          cases premises with
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | nil =>
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk,
                  RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hCmdTrans
              have hProgA1 : __eo_prog_dt_cycle a1 ≠ Term.Stuck := by
                change __eo_prog_dt_cycle a1 ≠ Term.Stuck at hProg
                exact hProg
              rcases prog_dt_cycle_shape_of_not_stuck a1 hProgA1 with
                ⟨sArg, t, rfl⟩
              let result :=
                Term.Apply
                  (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq sArg) t))
                  (Term.Boolean false)
              have hProgEq :
                  __eo_cmd_step_proven s CRule.dt_cycle
                      (CArgList.cons result CArgList.nil) CIndexList.nil =
                    result := by
                change __eo_prog_dt_cycle result = result
                exact prog_dt_cycle_eq_input_of_not_stuck sArg t hProgA1
              have hResultTy' : __eo_typeof result = Term.Bool := by
                change
                  __eo_typeof
                      (__eo_cmd_step_proven s CRule.dt_cycle
                        (CArgList.cons result CArgList.nil) CIndexList.nil) =
                    Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hResultBool : RuleProofs.eo_has_bool_type result :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  result hA1Trans hResultTy'
              have hInnerBool :
                  RuleProofs.eo_has_bool_type
                    (Term.Apply (Term.Apply Term.eq sArg) t) :=
                eo_has_bool_type_eq_left_of_eq_false_bool sArg t hResultBool
              have hCycle :
                  __dt_find_cycle t sArg (__is_cons_app t) (Term.Boolean false) =
                    Term.Boolean true :=
                prog_dt_cycle_condition_of_not_stuck sArg t hProgA1
              refine ⟨?_, ?_⟩
              · intro _hPremisesTrue
                rw [hProgEq]
                change eo_interprets M result true
                apply CnfSupport.eo_interprets_eq_true_of_false_false
                · exact dt_cycle_inner_eq_false M hM sArg t hCycle hInnerBool
                · exact CnfSupport.eo_interprets_false M
              · rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  result hResultBool
