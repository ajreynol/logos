import Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private abbrev mkDtCollapseSelectorGuard (s t : Term) : Term :=
  __assoc_nil_nth Term.__eo_List_cons (__dt_arg_list t)
    (__eo_list_find Term.__eo_List_cons
      (__dt_get_selectors_of_app (__eo_typeof t) t) s)

private theorem eo_to_smt_apply_dt_sel
    (s : native_String) (d : Datatype) (i j : native_Nat) (x : Term) :
    __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
      SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_apply_dt_cons
    (s : native_String) (d : Datatype) (i : native_Nat) (x : Term) :
    __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
      SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x) := by
  rfl

private theorem assoc_nil_nth_nil_stuck (f n : Term) :
    __assoc_nil_nth f Term.__eo_List_nil n = Term.Stuck := by
  cases f <;> cases n <;>
    simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth]

private theorem assoc_nil_nth_singleton_eq (x n ti : Term) :
    __assoc_nil_nth Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) Term.__eo_List_nil) n = ti ->
    ti ≠ Term.Stuck ->
    ti = x := by
  intro h hti
  cases n <;> try
    simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth, __eo_requires,
      __eo_eq, __eo_add, native_ite, native_teq, native_not,
      SmtEval.native_not] at h
  case Numeral z =>
    by_cases hz : z = 0
    · subst hz
      simp [__assoc_nil_nth, __eo_eq, native_ite, native_teq] at h
      exact h.symm
    · simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth, __eo_requires,
        __eo_eq, __eo_add, native_ite, native_teq, native_not,
        SmtEval.native_not, hz] at h
      exact False.elim (hti h.symm)
  all_goals exact False.elim (hti h.symm)

private theorem model_eval_apply_dtcons_of_arg_ne_notvalue
    (M : SmtModel) (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (v : SmtValue) :
    v ≠ SmtValue.NotValue ->
    __smtx_model_eval_apply M (SmtValue.DtCons s d i) v =
      SmtValue.Apply (SmtValue.DtCons s d i) v := by
  intro hv
  cases v <;> simp [__smtx_model_eval_apply] at hv ⊢

private theorem one_arg_count_of_apply_dtcons_datatype
    {v : SmtValue} {s : native_String} {d : SmtDatatype} {i : native_Nat}
    (hTy : __smtx_typeof_value (SmtValue.Apply (SmtValue.DtCons s d i) v) =
      SmtType.Datatype s d) :
    __smtx_dt_num_sels d i = 1 := by
  have hCountSub :
      vsm_num_apply_args (SmtValue.Apply (SmtValue.DtCons s d i) v) =
        __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
    exact vsm_num_apply_args_eq_dt_num_sels_of_datatype
      (v := SmtValue.Apply (SmtValue.DtCons s d i) v)
      (by simp [__vsm_apply_head]) hTy
  have hCount :
      vsm_num_apply_args (SmtValue.Apply (SmtValue.DtCons s d i) v) =
        __smtx_dt_num_sels d i := by
    rw [dt_num_sels_substitute s d d i] at hCountSub
    exact hCountSub
  simpa [vsm_num_apply_args] using hCount.symm

private theorem dt_sel_cons_one_eval_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i : native_Nat) (x : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) x) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hBool
  let D := __eo_to_smt_datatype d
  let X := __eo_to_smt x
  let vx := __smtx_model_eval M X
  have hTypes := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x)) x hBool
  have hLeftNN :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) ≠
        SmtType.None := hTypes.2
  cases hReserved : TranslationProofs.__eo_reserved_datatype_name s
  · have hLeftTranslate :
        __eo_to_smt
            (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x)) =
          SmtTerm.Apply (SmtTerm.DtSel s D i 0)
            (SmtTerm.Apply (SmtTerm.DtCons s D i) X) := by
      simp [eo_to_smt_apply_dt_sel, eo_to_smt_apply_dt_cons,
        TranslationProofs.eo_to_smt_term_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_cons, D, X, native_ite, hReserved]
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel s D i 0)
            (SmtTerm.Apply (SmtTerm.DtCons s D i) X)) := by
      unfold term_has_non_none_type
      rw [← hLeftTranslate]
      exact hLeftNN
    have hArgTy :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.DtCons s D i) X) =
          SmtType.Datatype s D :=
      dt_sel_arg_datatype_of_non_none hApplyNN
    have hXNN : __smtx_typeof X ≠ SmtType.None := by
      have hConsNN :
          __smtx_typeof (SmtTerm.Apply (SmtTerm.DtCons s D i) X) ≠
            SmtType.None := by
        rw [hArgTy]
        simp
      have hApplyNN' :
          __smtx_typeof_apply (__smtx_typeof (SmtTerm.DtCons s D i))
              (__smtx_typeof X) ≠
            SmtType.None := by
        simpa [__smtx_typeof] using hConsNN
      rcases typeof_apply_non_none_cases hApplyNN' with
        ⟨_A, _B, _hF, hX, hA, _hB⟩
      rw [hX]
      exact hA
    have hPresX : __smtx_typeof_value vx = __smtx_typeof X :=
      smt_model_eval_preserves_type_of_non_none M hM X hXNN
    have hvxNN : vx ≠ SmtValue.NotValue := by
      intro hv
      have hNone : __smtx_typeof_value vx = SmtType.None := by
        simp [hv, __smtx_typeof_value]
      rw [hPresX] at hNone
      exact hXNN hNone
    have hEvalCons :
        __smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtCons s D i) X) =
          SmtValue.Apply (SmtValue.DtCons s D i) vx := by
      simp [__smtx_model_eval, vx]
      exact model_eval_apply_dtcons_of_arg_ne_notvalue M s D i vx hvxNN
    have hConsValTy :
        __smtx_typeof_value (SmtValue.Apply (SmtValue.DtCons s D i) vx) =
          SmtType.Datatype s D := by
      rw [← hEvalCons]
      have hPres := smt_model_eval_preserves_type_of_non_none M hM
        (SmtTerm.Apply (SmtTerm.DtCons s D i) X) (by
          unfold term_has_non_none_type
          rw [hArgTy]
          simp)
      rw [hPres, hArgTy]
    have hNum : __smtx_dt_num_sels D i = 1 :=
      one_arg_count_of_apply_dtcons_datatype hConsValTy
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hLeftTranslate]
    simp [__smtx_model_eval, hEvalCons]
    unfold __smtx_model_eval_dt_sel
    have hHeadTrue :
        native_veq (__vsm_apply_head (SmtValue.Apply (SmtValue.DtCons s D i) vx))
            (SmtValue.DtCons s D i) = true := by
      simp [__vsm_apply_head, native_veq]
    simp [native_ite, hHeadTrue, hNum, __vsm_apply_arg_nth, native_nateq]
    simpa [vx] using RuleProofs.smt_value_rel_refl vx
  · exfalso
    apply hLeftNN
    have hTranslateNone :
        __eo_to_smt
            (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x)) =
          SmtTerm.Apply SmtTerm.None (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) := by
      simp [eo_to_smt_apply_dt_sel, eo_to_smt_apply_dt_cons,
        TranslationProofs.eo_to_smt_term_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_cons, native_ite, hReserved]
    rw [hTranslateNone]
    exact TranslationProofs.typeof_apply_none_eq
      (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))

private theorem dt_collapse_selector_direct_one_sound
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i : native_Nat) (x ti : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) ti) ->
    mkDtCollapseSelectorGuard (Term.DtSel s d i 0)
      (Term.Apply (Term.DtCons s d i) x) = ti ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) ti)
      true := by
  intro hBool hGuard
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))
      ti hBool
  have hTiTrans : RuleProofs.eo_has_smt_translation ti := by
    unfold RuleProofs.eo_has_smt_translation
    rw [← hTypes.1]
    exact hTypes.2
  have hTiNe : ti ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ti hTiTrans
  have hAssoc :
      __assoc_nil_nth Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) Term.__eo_List_nil)
        (__eo_list_find Term.__eo_List_cons
          (__dt_get_selectors_of_app (__eo_typeof (Term.Apply (Term.DtCons s d i) x))
            (Term.Apply (Term.DtCons s d i) x)) (Term.DtSel s d i 0)) = ti := by
    simpa [mkDtCollapseSelectorGuard, __dt_arg_list, __get_arg_list_rec] using
      hGuard
  have hTiEq : ti = x :=
    assoc_nil_nth_singleton_eq x _ ti hAssoc hTiNe
  have hBoolX :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) x) := by
    simpa [hTiEq] using hBool
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · rw [hTiEq]
    exact dt_sel_cons_one_eval_rel M hM s d i x hBoolX

axiom dt_collapse_selector_sound
    (M : SmtModel) (hM : model_total_typed M) (s t ti : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply s t)) ti) ->
  mkDtCollapseSelectorGuard s t = ti ->
  eo_interprets M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply s t)) ti) true

private theorem eq_args_of_prog_dt_collapse_selector_ne_stuck
    (a1 : Term) :
  __eo_prog_dt_collapse_selector a1 ≠ Term.Stuck ->
  ∃ s t ti,
    a1 = Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply s t)) ti ∧
    mkDtCollapseSelectorGuard s t = ti ∧
    __eo_prog_dt_collapse_selector a1 = a1 := by
  intro hProg
  cases a1 with
  | Apply f ti =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhs with
                  | Apply s t =>
                      let guard := mkDtCollapseSelectorGuard s t
                      let body :=
                        Term.Apply (Term.Apply (Term.UOp UserOp.eq)
                          (Term.Apply s t)) ti
                      have hReq :
                          __eo_requires guard ti body ≠ Term.Stuck := by
                        simpa [__eo_prog_dt_collapse_selector, guard, body,
                          mkDtCollapseSelectorGuard] using hProg
                      have hGuard : guard = ti :=
                        eo_requires_eq_of_ne_stuck guard ti body hReq
                      have hProgEq :
                          __eo_prog_dt_collapse_selector body = body := by
                        simpa [__eo_prog_dt_collapse_selector, guard, body,
                          mkDtCollapseSelectorGuard] using
                            eo_requires_eq_result_of_ne_stuck guard ti body hReq
                      exact ⟨s, t, ti, rfl, by simpa [guard] using hGuard, hProgEq⟩
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem prog_dt_collapse_selector_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_dt_collapse_selector a1) = Term.Bool ->
  __eo_prog_dt_collapse_selector a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_dt_collapse_selector a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases eq_args_of_prog_dt_collapse_selector_ne_stuck a1 hProg with
    ⟨_s, _t, _ti, _hEq, _hGuard, hProgEq⟩
  exact hProgEq

private theorem typed___eo_prog_dt_collapse_selector_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_selector a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_dt_collapse_selector a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_dt_collapse_selector a1 = a1 :=
    prog_dt_collapse_selector_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem facts___eo_prog_dt_collapse_selector_impl
    (M : SmtModel) (hM : model_total_typed M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_selector a1) = Term.Bool ->
  eo_interprets M (__eo_prog_dt_collapse_selector a1) true := by
  intro hA1Trans hResultTy
  have hProg : __eo_prog_dt_collapse_selector a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases eq_args_of_prog_dt_collapse_selector_ne_stuck a1 hProg with
    ⟨sel, t, ti, hA1Eq, hGuard, hProgEq⟩
  have hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply sel t)) ti) := by
    subst hA1Eq
    have hA1Ty :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply sel t)) ti) =
            Term.Bool := by
      simpa [hProgEq] using hResultTy
    exact RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply sel t)) ti)
      hA1Trans hA1Ty
  rw [hProgEq]
  rw [hA1Eq]
  exact dt_collapse_selector_sound M hM sel t ti hBool hGuard

theorem cmd_step_dt_collapse_selector_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_collapse_selector args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_collapse_selector args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_collapse_selector args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_collapse_selector args premises ≠
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
              have hA1TransPair :
                  RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                hA1TransPair.1
              change __eo_typeof (__eo_prog_dt_collapse_selector a1) =
                Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_dt_collapse_selector a1) true
                exact facts___eo_prog_dt_collapse_selector_impl M hM a1
                  hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_dt_collapse_selector a1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_dt_collapse_selector a1)
                  (typed___eo_prog_dt_collapse_selector_impl a1
                    hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
