import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CoreSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private def qterm (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def quantUnusedFormula (Q x F G : Term) : Term :=
  qeq (qterm Q x F) G

private def qexists (x F : Term) : Term :=
  qterm (Term.UOp UserOp.exists) x F

private def qforall (x F : Term) : Term :=
  qterm (Term.UOp UserOp.forall) x F

private theorem eo_to_smt_exists_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qexists x F) =
      __eo_to_smt_exists x (__eo_to_smt F) := by
  unfold qexists qterm
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qforall x F) =
      SmtTerm.not (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) := by
  unfold qforall qterm
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  cases h : __smtx_typeof t <;>
    simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢

private theorem smtx_typeof_not_bool_of_arg_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

private theorem smtx_typeof_exists_bool_or_none_local
    (s : native_String) (T : SmtType) (body : SmtTerm) :
    __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool ∨
      __smtx_typeof (SmtTerm.exists s T body) = SmtType.None := by
  rw [smtx_typeof_exists_term_eq]
  cases hBody : __smtx_typeof body <;>
    simp [native_ite, native_Teq]
  cases hWf : __smtx_type_wf T <;>
    simp [__smtx_typeof_guard_wf, native_ite, hWf]

private theorem smtx_typeof_qexists_bool_or_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool ∨
      __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.None := by
  unfold qexists qterm
  cases x
  case __eo_List_nil =>
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case Apply f tail =>
    cases f
    case Apply g head =>
      cases g
      case __eo_List_cons =>
        cases head
        case Var name T =>
          cases name
          case String s =>
            change
              __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt F))) =
                  SmtType.Bool ∨
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists tail (__eo_to_smt F))) =
                  SmtType.None
            exact smtx_typeof_exists_bool_or_none_local s (__eo_to_smt_type T)
              (__eo_to_smt_exists tail (__eo_to_smt F))
          all_goals
            right
            change __smtx_typeof SmtTerm.None = SmtType.None
            exact TranslationProofs.smtx_typeof_none
        all_goals
          right
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none
      all_goals
        right
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    all_goals
      right
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  all_goals
    right
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none

private theorem eo_to_smt_exists_top_bool_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qexists x F)) = SmtType.Bool := by
  rcases smtx_typeof_qexists_bool_or_none x F with hBool | hNone
  · exact hBool
  · exact False.elim (hNN hNone)

private theorem qexists_non_nil_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qexists x F)) ≠ SmtType.None) :
    x ≠ Term.__eo_List_nil := by
  intro hx
  subst x
  apply hNN
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_non_nil_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None) :
    x ≠ Term.__eo_List_nil := by
  intro hx
  subst x
  apply hNN
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_inner_exists_bool_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool := by
  have hx : x ≠ Term.__eo_List_nil := qforall_non_nil_of_non_none x F hNN
  have hNN' := hNN
  rw [eo_to_smt_forall_eq x F hx] at hNN'
  exact smtx_typeof_not_arg_of_non_none
    (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) hNN'

private theorem qforall_top_bool_of_non_none
    (x F : Term)
    (hNN : __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qforall x F)) = SmtType.Bool := by
  have hx : x ≠ Term.__eo_List_nil := qforall_non_nil_of_non_none x F hNN
  rw [eo_to_smt_forall_eq x F hx]
  exact smtx_typeof_not_bool_of_arg_bool _
    (qforall_inner_exists_bool_of_non_none x F hNN)

private theorem qterm_top_bool_of_non_none
    (Q x F : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNN : __smtx_typeof (__eo_to_smt (qterm Q x F)) ≠ SmtType.None) :
    __smtx_typeof (__eo_to_smt (qterm Q x F)) = SmtType.Bool := by
  rcases hQ with hQ | hQ
  · subst Q
    exact qforall_top_bool_of_non_none x F hNN
  · subst Q
    exact eo_to_smt_exists_top_bool_of_non_none x F hNN

private theorem get_unused_vars_not_stuck_of_no_free
    (Q x F G : Term)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false) :
    __get_unused_vars (qterm Q x F) G ≠ Term.Stuck := by
  intro h
  rw [h] at hNoFree
  cases G <;> simp [__contains_atomic_term_list_free_rec] at hNoFree

private theorem smtx_eval_exists_unused_of_body_invariant
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hInv : ∀ v,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M (SmtTerm.exists s T body) =
      __smtx_model_eval M body := by
  classical
  rcases Smtm.canonical_type_inhabited_of_type_wf T hWF with
    ⟨w, hwTy, hwCan⟩
  have hwCanBool : __smtx_value_canonical_bool w = true := by
    simpa [value_canonical_bool_eq_true] using hwCan
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with ⟨b, hb⟩
  let P : Prop :=
    ∃ v : SmtValue,
      __smtx_typeof_value v = T ∧
        __smtx_value_canonical_bool v = true ∧
        __smtx_model_eval (native_model_push M s T v) body =
          SmtValue.Boolean true
  cases b
  · have hNotP : ¬ P := by
      intro hP
      rcases hP with ⟨v, hvTy, hvCan, hvEval⟩
      have hEval := hInv v hvTy hvCan
      rw [hb] at hEval
      rw [hEval] at hvEval
      cases hvEval
    simp [__smtx_model_eval, P, hNotP, hb]
  · have hP : P := by
      refine ⟨w, hwTy, hwCanBool, ?_⟩
      rw [hInv w hwTy hwCanBool]
      exact hb
    simp [__smtx_model_eval, P, hP, hb]

private theorem smtx_eval_not_not_of_bool
    (M : SmtModel) (hM : model_total_typed M)
    (body : SmtTerm)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
    __smtx_model_eval M (SmtTerm.not (SmtTerm.not body)) =
      __smtx_model_eval M body := by
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with ⟨b, hb⟩
  cases b <;>
    simp [__smtx_model_eval, hb, __smtx_model_eval_not, SmtEval.native_not]

private theorem smtx_eval_forall_unused_of_body_invariant
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hInv : ∀ v,
      __smtx_typeof_value v = T ->
      __smtx_value_canonical_bool v = true ->
      __smtx_model_eval (native_model_push M s T v) body =
        __smtx_model_eval M body) :
    __smtx_model_eval M
        (SmtTerm.not (SmtTerm.exists s T (SmtTerm.not body))) =
      __smtx_model_eval M body := by
  have hNotTy : __smtx_typeof (SmtTerm.not body) = SmtType.Bool := by
    rw [typeof_not_eq]
    simp [hBodyTy, native_ite, native_Teq]
  have hExists :
      __smtx_model_eval M (SmtTerm.exists s T (SmtTerm.not body)) =
        __smtx_model_eval M (SmtTerm.not body) := by
    apply smtx_eval_exists_unused_of_body_invariant M hM s T
      (SmtTerm.not body) hWF hNotTy
    intro v hvTy hvCan
    simp [__smtx_model_eval, hInv v hvTy hvCan]
  rw [__smtx_model_eval.eq_6, hExists]
  simpa [__smtx_model_eval] using
    smtx_eval_not_not_of_bool M hM body hBodyTy

private theorem eq_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    x = y := by
  intro hReq
  by_cases hEq : native_teq x y = true
  · simpa [native_teq] using hEq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    unfold __eo_requires at hReq
    simp [hEqFalse, native_ite] at hReq

private theorem body_ne_stuck_of_requires_ne_stuck {x y B : Term} :
    __eo_requires x y B ≠ Term.Stuck ->
    B ≠ Term.Stuck := by
  intro hReq hB
  subst B
  unfold __eo_requires at hReq
  by_cases hEq : native_teq x y = true
  · by_cases hStuck : native_teq x Term.Stuck = true
    · simp [hEq, hStuck, native_ite] at hReq
    · have hStuckFalse : native_teq x Term.Stuck = false := by
        cases h : native_teq x Term.Stuck <;> simp [h] at hStuck ⊢
      simp [hEq, hStuckFalse, native_ite] at hReq
  · have hEqFalse : native_teq x y = false := by
      cases h : native_teq x y <;> simp [h] at hEq ⊢
    simp [hEqFalse, native_ite] at hReq

private theorem eo_or_eq_true_cases_local (x y : Term) :
    __eo_or x y = Term.Boolean true ->
    x = Term.Boolean true ∨ y = Term.Boolean true := by
  intro h
  cases x <;> cases y <;> simp [__eo_or] at h ⊢
  case Boolean.Boolean b1 b2 =>
    cases b1 <;> cases b2 <;> simp [native_or] at h ⊢
  case Binary.Binary w1 n1 w2 n2 =>
    by_cases hW : w1 = w2
    · subst w2
      simp [__eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not] at h
    · have hNumNe : Term.Numeral w1 ≠ Term.Numeral w2 := by
        intro hEq
        cases hEq
        exact hW rfl
      simp [__eo_requires, hNumNe, native_ite, native_teq] at h

private theorem get_unused_vars_quant_match
    (Q x F y : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hF : F ≠ Term.Stuck)
    (h :
      __get_unused_vars (qterm Q x F) (qterm Q y F) ≠ Term.Stuck) :
    __eo_list_minclude Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y =
      Term.Boolean true ∧
    __get_unused_vars (qterm Q x F) (qterm Q y F) =
      __eo_list_diff Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y := by
  rcases hQ with hQ | hQ <;> subst Q
  · let set := __eo_list_setof Term.__eo_List_cons x
    let diff := __eo_list_diff Term.__eo_List_cons set y
    have hReq :
        __eo_requires (__eo_list_minclude Term.__eo_List_cons set y)
            (Term.Boolean true) diff ≠ Term.Stuck := by
      simpa [qterm, __get_unused_vars, set, diff, __eo_and, __eo_eq,
        __eo_ite, native_ite, native_teq] using h
    have hIncl :
        __eo_list_minclude Term.__eo_List_cons set y = Term.Boolean true :=
      eq_of_requires_ne_stuck hReq
    have hGuard :
        __eo_and
            (__eo_eq (Term.UOp UserOp.forall) (Term.UOp UserOp.forall))
            (__eo_eq F F) =
          Term.Boolean true := by
      simp [__eo_and, __eo_eq, native_teq, native_and]
    constructor
    · simpa [set] using hIncl
    · simpa [qterm, __get_unused_vars, set, diff, hIncl, hGuard,
        __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not]
  · let set := __eo_list_setof Term.__eo_List_cons x
    let diff := __eo_list_diff Term.__eo_List_cons set y
    have hReq :
        __eo_requires (__eo_list_minclude Term.__eo_List_cons set y)
            (Term.Boolean true) diff ≠ Term.Stuck := by
      simpa [qterm, __get_unused_vars, set, diff, __eo_and, __eo_eq,
        __eo_ite, native_ite, native_teq] using h
    have hIncl :
        __eo_list_minclude Term.__eo_List_cons set y = Term.Boolean true :=
      eq_of_requires_ne_stuck hReq
    have hGuard :
        __eo_and
            (__eo_eq (Term.UOp UserOp.exists) (Term.UOp UserOp.exists))
            (__eo_eq F F) =
          Term.Boolean true := by
      simp [__eo_and, __eo_eq, native_teq, native_and]
    constructor
    · simpa [set] using hIncl
    · simpa [qterm, __get_unused_vars, set, diff, hIncl, hGuard,
        __eo_requires, native_ite, native_teq, native_not,
        SmtEval.native_not]

private axiom smtx_model_eval_quant_unused_formula
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false)
    (hBool : RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G)) :
    __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
      __smtx_model_eval M (__eo_to_smt G)

private theorem quant_unused_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = quantUnusedFormula Q x F G ∧
      (Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists) ∧
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false ∧
      __eo_prog_quant_unused_vars x1 = quantUnusedFormula Q x F G := by
  intro hProg
  cases x1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply qHead F =>
                      cases qHead with
                      | Apply Q x =>
                          let v0 := qterm Q x F
                          let unused := __get_unused_vars v0 G
                          let inner :=
                            __eo_requires
                              (__contains_atomic_term_list_free_rec G unused
                                Term.__eo_List_nil)
                              (Term.Boolean false) (qeq v0 G)
                          have hReq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner ≠ Term.Stuck := by
                            simpa [quantUnusedFormula, qeq, qterm, v0, unused,
                              inner, __eo_prog_quant_unused_vars] using hProg
                          have hGuard :
                              __eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                  (__eo_eq Q (Term.UOp UserOp.exists)) =
                                Term.Boolean true :=
                            eq_of_requires_ne_stuck hReq
                          have hInnerNe : inner ≠ Term.Stuck :=
                            body_ne_stuck_of_requires_ne_stuck hReq
                          have hNoFree :
                              __contains_atomic_term_list_free_rec G unused
                                  Term.__eo_List_nil =
                                Term.Boolean false :=
                            eq_of_requires_ne_stuck hInnerNe
                          rcases eo_or_eq_true_cases_local
                              (__eo_eq Q (Term.UOp UserOp.forall))
                              (__eo_eq Q (Term.UOp UserOp.exists)) hGuard with
                            hForall | hExists
                          · have hQ : Q = Term.UOp UserOp.forall :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.forall) hForall).symm
                            subst Q
                            have hNoFree' :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (qterm (Term.UOp UserOp.forall) x F) G)
                                    Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [v0, unused, qterm] using hNoFree
                            have hNoFreeRaw :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (((Term.UOp UserOp.forall).Apply x).Apply F)
                                      G) Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [qterm] using hNoFree'
                            refine ⟨Term.UOp UserOp.forall, x, F, G, rfl,
                              Or.inl rfl, ?_, ?_⟩
                            · exact hNoFree'
                            · change __eo_prog_quant_unused_vars
                                (quantUnusedFormula (Term.UOp UserOp.forall)
                                  x F G) =
                                quantUnusedFormula (Term.UOp UserOp.forall)
                                  x F G
                              simp [quantUnusedFormula, qeq, qterm,
                                __eo_prog_quant_unused_vars, hGuard,
                                hNoFreeRaw,
                                __eo_requires, native_ite, native_teq,
                                native_not, SmtEval.native_not]
                          · have hQ : Q = Term.UOp UserOp.exists :=
                              (RuleProofs.eq_of_eo_eq_true Q
                                (Term.UOp UserOp.exists) hExists).symm
                            subst Q
                            have hNoFree' :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (qterm (Term.UOp UserOp.exists) x F) G)
                                    Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [v0, unused, qterm] using hNoFree
                            have hNoFreeRaw :
                                __contains_atomic_term_list_free_rec G
                                    (__get_unused_vars
                                      (((Term.UOp UserOp.exists).Apply x).Apply F)
                                      G) Term.__eo_List_nil =
                                  Term.Boolean false := by
                              simpa [qterm] using hNoFree'
                            refine ⟨Term.UOp UserOp.exists, x, F, G, rfl,
                              Or.inr rfl, ?_, ?_⟩
                            · exact hNoFree'
                            · change __eo_prog_quant_unused_vars
                                (quantUnusedFormula (Term.UOp UserOp.exists)
                                  x F G) =
                                quantUnusedFormula (Term.UOp UserOp.exists)
                                  x F G
                              simp [quantUnusedFormula, qeq, qterm,
                                __eo_prog_quant_unused_vars, hGuard,
                                hNoFreeRaw,
                                __eo_requires, native_ite, native_teq,
                                native_not, SmtEval.native_not]
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
  have hProg : __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠
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
              have hTransA1 : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_unused_vars a1 ≠ Term.Stuck := by
                change __eo_prog_quant_unused_vars a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_unused_shape_of_not_stuck a1 hProgQuant with
                ⟨Q, x, F, G, ha1, hQ, hNoFree, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (quantUnusedFormula Q x F G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (quantUnusedFormula Q x F G) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type (quantUnusedFormula Q x F G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (quantUnusedFormula Q x F G) hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_quant_unused_vars a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M (qterm Q x F) G
                · exact hFormulaBool
                · have hEvalEq :=
                    smtx_model_eval_quant_unused_formula M hM Q x F G hQ
                      hNoFree hFormulaBool
                  rw [hEvalEq]
                  exact RuleProofs.smt_value_rel_refl
                    (__smtx_model_eval M (__eo_to_smt G))
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_unused_vars a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
