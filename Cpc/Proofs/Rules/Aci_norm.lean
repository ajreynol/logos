import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private theorem eo_typeof_stuck_ne_bool :
    __eo_typeof Term.Stuck ≠ Term.Bool := by
  native_decide

private theorem eo_requires_true_eq_of_type_bool (x body : Term) :
    __eo_typeof (__eo_requires x (Term.Boolean true) body) = Term.Bool ->
    __eo_requires x (Term.Boolean true) body = body := by
  intro hTy
  cases x <;>
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hTy ⊢
  case Boolean b =>
    cases b <;>
      simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hTy ⊢
    exact False.elim (eo_typeof_stuck_ne_bool hTy)
  all_goals
    exact False.elim (eo_typeof_stuck_ne_bool hTy)

private theorem eo_prog_aci_norm_eq_input_of_type_bool (a1 : Term) :
  __eo_typeof (__eo_prog_aci_norm a1) = Term.Bool ->
  __eo_prog_aci_norm a1 = a1 := by
  intro hTy
  cases a1
  all_goals try
    have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_aci_norm] using hTy
    exact False.elim (eo_typeof_stuck_ne_bool hStuck)
  case Apply f x =>
    cases f
    all_goals try
      have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
        simpa [__eo_prog_aci_norm] using hTy
      exact False.elim (eo_typeof_stuck_ne_bool hStuck)
    case Apply g y =>
      cases g
      all_goals try
        have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
          simpa [__eo_prog_aci_norm] using hTy
        exact False.elim (eo_typeof_stuck_ne_bool hStuck)
      case UOp op =>
        cases op <;> simp [__eo_prog_aci_norm] at hTy ⊢
        case eq =>
          exact eo_requires_true_eq_of_type_bool _ _ hTy
        all_goals
          exact False.elim (eo_typeof_stuck_ne_bool hTy)

private def aciNormGuard (a b : Term) : Term :=
  __eo_ite (__aci_norm_eq (__get_aci_normal_form a) b) (Term.Boolean true)
    (__eo_ite (__aci_norm_eq (__get_aci_normal_form b) a) (Term.Boolean true)
      (__aci_norm_eq (__get_aci_normal_form a) (__get_aci_normal_form b)))

private theorem aci_norm_guard_true_of_type_bool (a b : Term) :
    __eo_typeof
        (__eo_requires (aciNormGuard a b) (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) = Term.Bool ->
    aciNormGuard a b = Term.Boolean true := by
  intro hTy
  cases hGuard : aciNormGuard a b <;>
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not,
      hGuard] at hTy
  case Boolean v =>
    cases v
    · exact False.elim (eo_typeof_stuck_ne_bool hTy)
    · rfl
  all_goals
    exact False.elim (eo_typeof_stuck_ne_bool hTy)

private theorem eq_of_eo_eq_true_local (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

private theorem smt_value_rel_of_eo_eq_true
    (M : SmtModel) (x y : Term) :
    __eo_eq x y = Term.Boolean true ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hEq
  have hyx : y = x := eq_of_eo_eq_true_local x y hEq
  subst y
  exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x))

private theorem generic_apply_type_of_non_special_head_local
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  exact __smtx_typeof.eq_140 f x hSel hTester

private theorem smtx_typeof_apply_none (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  have hGeneric : generic_apply_type SmtTerm.None x := by
    exact generic_apply_type_of_non_special_head_local _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, TranslationProofs.smtx_typeof_none]
  simp [__smtx_typeof_apply]

private theorem smtx_typeof_apply_apply_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None y) x) =
      SmtType.None := by
  have hGeneric : generic_apply_type (SmtTerm.Apply SmtTerm.None y) x := by
    exact generic_apply_type_of_non_special_head_local _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, smtx_typeof_apply_none y]
  simp [__smtx_typeof_apply]

private theorem aci_sorted_marker_not_has_smt_translation (f t : Term) :
    ¬ RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) t) := by
  intro hTrans
  apply hTrans
  simpa using smtx_typeof_apply_apply_none (__eo_to_smt t) (__eo_to_smt f)

private def aciNormPayload : Term -> Term
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) _) t => t
  | t => t

private theorem smt_value_rel_of_aci_norm_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x y : Term) :
  __aci_norm_eq x y = Term.Boolean true ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload x)))
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload y))) := by
  intro hEq
  by_cases hTermEq : __eo_eq x y = Term.Boolean true
  · have hyx : y = x := eq_of_eo_eq_true_local x y hTermEq
    subst y
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (aciNormPayload x)))
  · -- The remaining cases are the marker payload/list cases.
    sorry

private theorem aciNormPayload_has_smt_translation_of_has_smt_translation
    (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  RuleProofs.eo_has_smt_translation (aciNormPayload t) := by
  intro hTrans
  cases t <;> try exact hTrans
  case Apply f x =>
    cases f <;> try exact hTrans
    case Apply g y =>
      cases g <;> try exact hTrans
      case UOp op =>
        cases op <;> try exact hTrans
        exact False.elim (aci_sorted_marker_not_has_smt_translation y x hTrans)

private theorem smt_value_rel_aciNormPayload_self
    (M : SmtModel) (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload t)))
    (__smtx_model_eval M (__eo_to_smt t)) := by
  intro hTrans
  cases t <;> try exact RuleProofs.smt_value_rel_refl _
  case Apply f x =>
    cases f <;> try exact RuleProofs.smt_value_rel_refl _
    case Apply g y =>
      cases g <;> try exact RuleProofs.smt_value_rel_refl _
      case UOp op =>
        cases op <;> try exact RuleProofs.smt_value_rel_refl _
        exact False.elim (aci_sorted_marker_not_has_smt_translation y x hTrans)

private theorem smt_value_rel_get_aci_normal_form_payload
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form t)))) := by
  intro hTrans
  cases t <;> simp [__get_aci_normal_form, aciNormPayload] <;>
    try exact RuleProofs.smt_value_rel_refl _
  case Apply f x =>
    cases f <;> try exact RuleProofs.smt_value_rel_refl _
    case Apply g y =>
      cases g <;> try exact RuleProofs.smt_value_rel_refl _
      case UOp op =>
        cases op <;> simp [__get_aci_normal_form, aciNormPayload] <;>
          try exact RuleProofs.smt_value_rel_refl _
        all_goals
          -- These are the supported A/AI/ACI operators that the normalizer rewrites.
          sorry

private theorem smt_value_rel_of_aci_norm_guard_true
    (M : SmtModel) (hM : model_total_typed M) (a b : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  aciNormGuard a b = Term.Boolean true ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hEqTrans hEqBool hGuard
  have hAHas : RuleProofs.eo_has_smt_translation a := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hEqBool with
      ⟨_, hNonNone⟩
    exact hNonNone
  have hBHas : RuleProofs.eo_has_smt_translation b := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hEqBool with
      ⟨hTy, hNonNone⟩
    rw [hTy] at hNonNone
    exact hNonNone
  cases hLeft : __aci_norm_eq (__get_aci_normal_form a) b
  all_goals
    simp [aciNormGuard, __eo_ite, native_teq, hLeft] at hGuard
  case Boolean left =>
    cases left
    · cases hRight : __aci_norm_eq (__get_aci_normal_form b) a
      all_goals
        simp [aciNormGuard, __eo_ite, native_teq, hLeft, hRight] at hGuard
      case Boolean right =>
        cases right
        · have hNFARel :=
            smt_value_rel_get_aci_normal_form_payload M hM a hAHas
          have hNFBRel :=
            smt_value_rel_get_aci_normal_form_payload M hM b hBHas
          have hNFRel :=
            smt_value_rel_of_aci_norm_eq_true M hM
              (__get_aci_normal_form a) (__get_aci_normal_form b)
              hGuard
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form a))))
            (__smtx_model_eval M (__eo_to_smt b))
            hNFARel
            (RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form a))))
              (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form b))))
              (__smtx_model_eval M (__eo_to_smt b))
              hNFRel
              (RuleProofs.smt_value_rel_symm _ _ hNFBRel))
        · have hNFBRel :=
            smt_value_rel_get_aci_normal_form_payload M hM b hBHas
          have hRel :=
            smt_value_rel_of_aci_norm_eq_true M hM
              (__get_aci_normal_form b) a hRight
          have hPayloadA := smt_value_rel_aciNormPayload_self M a hAHas
          have hBA : RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt a)) :=
            RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form b))))
              (__smtx_model_eval M (__eo_to_smt a))
              hNFBRel
              (RuleProofs.smt_value_rel_trans
                (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form b))))
                (__smtx_model_eval M (__eo_to_smt (aciNormPayload a)))
                (__smtx_model_eval M (__eo_to_smt a))
                hRel hPayloadA)
          exact RuleProofs.smt_value_rel_symm
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt a))
            hBA
      all_goals
        contradiction
    · have hNFARel :=
        smt_value_rel_get_aci_normal_form_payload M hM a hAHas
      have hRel :=
        smt_value_rel_of_aci_norm_eq_true M hM
          (__get_aci_normal_form a) b hLeft
      have hPayloadB := smt_value_rel_aciNormPayload_self M b hBHas
      exact RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form a))))
        (__smtx_model_eval M (__eo_to_smt b))
        hNFARel
        (RuleProofs.smt_value_rel_trans
          (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form a))))
          (__smtx_model_eval M (__eo_to_smt (aciNormPayload b)))
          (__smtx_model_eval M (__eo_to_smt b))
          hRel hPayloadB)
  all_goals
    contradiction

private theorem facts___eo_prog_aci_norm_impl
    (M : SmtModel) (hM : model_total_typed M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_aci_norm a1) = Term.Bool ->
  eo_interprets M (__eo_prog_aci_norm a1) true := by
  intro hTrans hResultTy
  have hProgEq : __eo_prog_aci_norm a1 = a1 :=
    eo_prog_aci_norm_eq_input_of_type_bool a1 hResultTy
  cases a1
  all_goals try
    have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_aci_norm] using hResultTy
    exact False.elim (eo_typeof_stuck_ne_bool hStuck)
  case Apply f x =>
    cases f
    all_goals try
      have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
        simpa [__eo_prog_aci_norm] using hResultTy
      exact False.elim (eo_typeof_stuck_ne_bool hStuck)
    case Apply g y =>
      cases g
      all_goals try
        have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
          simpa [__eo_prog_aci_norm] using hResultTy
        exact False.elim (eo_typeof_stuck_ne_bool hStuck)
      case UOp op =>
        cases op <;> simp [__eo_prog_aci_norm] at hResultTy hProgEq ⊢
        case eq =>
          have hEqTrans :
              RuleProofs.eo_has_smt_translation
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) := hTrans
          have hEqTypeof : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) =
              Term.Bool := by
            simpa [hProgEq] using hResultTy
          have hEqBool :
              RuleProofs.eo_has_bool_type
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) :=
            RuleProofs.eo_typeof_bool_implies_has_bool_type
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) hEqTrans hEqTypeof
          have hGuard :
              aciNormGuard y x = Term.Boolean true := by
            apply aci_norm_guard_true_of_type_bool y x
            simpa [aciNormGuard] using hResultTy
          rw [hProgEq]
          exact RuleProofs.eo_interprets_eq_of_rel M y x hEqBool
            (smt_value_rel_of_aci_norm_guard_true M hM y x hEqTrans hEqBool hGuard)
        all_goals
          exact False.elim (eo_typeof_stuck_ne_bool hResultTy)

theorem cmd_step_aci_norm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.aci_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.aci_norm args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.aci_norm args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.aci_norm args premises ≠ Term.Stuck :=
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
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons a1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_aci_norm a1) = Term.Bool at hResultTy
              have hProgEq : __eo_prog_aci_norm a1 = a1 :=
                eo_prog_aci_norm_eq_input_of_type_bool a1 hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_aci_norm a1) true
                exact facts___eo_prog_aci_norm_impl M hM a1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_aci_norm a1)
                rw [hProgEq]
                exact hA1Trans
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
