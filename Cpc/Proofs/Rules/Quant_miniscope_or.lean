import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.CoreSupport
import Cpc.Proofs.Closed.ContainsAtomicTermListFree

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def qforall (x F : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.forall) x) F

private def qor (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B

private def qeq (A B : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) A) B

private def quantMiniscopeOrFormula (x F G : Term) : Term :=
  qeq (qforall x F) G

private def smtForall (xs : Term) (body : SmtTerm) : SmtTerm :=
  SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))

private def miniToSmt : Term -> SmtTerm
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B =>
      SmtTerm.or (miniToSmt A) (miniToSmt B)
  | Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F =>
      smtForall xs (__eo_to_smt F)
  | t => __eo_to_smt t

private theorem eo_to_smt_or_eq (A B : Term) :
    __eo_to_smt (qor A B) =
      SmtTerm.or (__eo_to_smt A) (__eo_to_smt B) := by
  rfl

private theorem eo_to_smt_forall_eq (x F : Term)
    (hx : x ≠ Term.__eo_List_nil) :
    __eo_to_smt (qforall x F) =
      smtForall x (__eo_to_smt F) := by
  cases x <;> first | rfl | exact False.elim (hx rfl)

private theorem smtx_typeof_not_arg_of_bool
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool ->
    __smtx_typeof t = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq] at hTy
  cases h : __smtx_typeof t <;>
    simp [h, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_not_bool_of_arg_bool
    (t : SmtTerm) :
    __smtx_typeof t = SmtType.Bool ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hTy
  rw [typeof_not_eq]
  simp [hTy, native_ite, native_Teq]

private theorem smtx_typeof_not_bool_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.not t) = SmtType.Bool := by
  intro hNN
  have hArg : __smtx_typeof t = SmtType.Bool := by
    cases h : __smtx_typeof t <;>
      simp [typeof_not_eq, h, native_ite, native_Teq] at hNN ⊢
  exact smtx_typeof_not_bool_of_arg_bool t hArg

private theorem smtx_typeof_not_arg_of_non_none
    (t : SmtTerm) :
    __smtx_typeof (SmtTerm.not t) ≠ SmtType.None ->
    __smtx_typeof t = SmtType.Bool := by
  intro hNN
  exact smtx_typeof_not_arg_of_bool t
    (smtx_typeof_not_bool_of_non_none t hNN)

private theorem smtx_typeof_or_args_of_bool
    (A B : SmtTerm) :
    __smtx_typeof (SmtTerm.or A B) = SmtType.Bool ->
    __smtx_typeof A = SmtType.Bool ∧
      __smtx_typeof B = SmtType.Bool := by
  intro hTy
  rw [typeof_or_eq] at hTy
  cases hA : __smtx_typeof A <;>
    cases hB : __smtx_typeof B <;>
    simp [hA, hB, native_ite, native_Teq] at hTy ⊢

private theorem smtx_typeof_or_bool_of_args
    (A B : SmtTerm) :
    __smtx_typeof A = SmtType.Bool ->
    __smtx_typeof B = SmtType.Bool ->
    __smtx_typeof (SmtTerm.or A B) = SmtType.Bool := by
  intro hA hB
  rw [typeof_or_eq]
  simp [hA, hB, native_ite, native_Teq]

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool := by
  intro hTy
  have hExists :
      __smtx_typeof
          (SmtTerm.exists s (__eo_to_smt_type T)
            (__eo_to_smt_exists xs body)) = SmtType.Bool := by
    simpa [__eo_to_smt_exists] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists xs body)) := by
    unfold term_has_non_none_type
    rw [hExists]
    simp
  exact exists_body_bool_of_non_none hNN

private theorem smtx_type_wf_of_exists_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠ SmtType.None := by
    intro hNone
    have hExists :
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists xs body)) = SmtType.Bool := by
      simpa [__eo_to_smt_exists] using hTy
    rw [smtx_typeof_exists_term_eq, hTail] at hExists
    simp [native_ite, native_Teq, hNone] at hExists
  exact smtx_typeof_guard_wf_wf_of_non_none
    (__eo_to_smt_type T) SmtType.Bool hGuardNN

private theorem smtx_typeof_eo_to_smt_exists_same_binders
    (xs : Term) (body body' : SmtTerm) :
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    __smtx_typeof body' = SmtType.Bool ->
    __smtx_typeof (__eo_to_smt_exists xs body') = SmtType.Bool := by
  intro hTy hBody'
  cases hxs : xs
  case __eo_List_nil =>
      subst hxs
      simpa [__eo_to_smt_exists] using hBody'
  case Apply f a =>
      subst hxs
      cases f with
      | Apply g y =>
          cases g with
          | __eo_List_cons =>
              cases y with
              | Var name T =>
                  cases name with
                  | String s =>
                      have hTail :
                          __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool :=
                        smtx_typeof_exists_tail_bool_of_cons_bool s T a body hTy
                      have hTail' :
                          __smtx_typeof (__eo_to_smt_exists a body') = SmtType.Bool :=
                        smtx_typeof_eo_to_smt_exists_same_binders a body body'
                          hTail hBody'
                      have hWF :
                          __smtx_type_wf (__eo_to_smt_type T) = true :=
                        smtx_type_wf_of_exists_cons_bool s T a body hTy
                      change
                        __smtx_typeof
                          (SmtTerm.exists s (__eo_to_smt_type T)
                            (__eo_to_smt_exists a body')) = SmtType.Bool
                      rw [smtx_typeof_exists_term_eq, hTail']
                      simp [native_ite, native_Teq, __smtx_typeof_guard_wf, hWF]
                  | _ =>
                      simp [__eo_to_smt_exists] at hTy
              | _ =>
                  simp [__eo_to_smt_exists] at hTy
          | _ =>
              simp [__eo_to_smt_exists] at hTy
      | _ =>
          simp [__eo_to_smt_exists] at hTy
  all_goals
      subst hxs
      simp [__eo_to_smt_exists] at hTy

private theorem false_of_smtx_typeof_none_bool :
    __smtx_typeof SmtTerm.None = SmtType.Bool -> False := by
  intro h
  exact TranslationProofs.smtx_typeof_none_ne_bool h

private theorem qforall_non_nil_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    x ≠ Term.__eo_List_nil := by
  intro hNN hx
  subst x
  apply hNN
  change __smtx_typeof SmtTerm.None = SmtType.None
  exact TranslationProofs.smtx_typeof_none

private theorem qforall_exists_type_bool_of_non_none
    (x F : Term) :
    __smtx_typeof (__eo_to_smt (qforall x F)) ≠ SmtType.None ->
    __smtx_typeof
        (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) =
      SmtType.Bool := by
  intro hNN
  have hx : x ≠ Term.__eo_List_nil :=
    qforall_non_nil_of_non_none x F hNN
  exact smtx_typeof_not_arg_of_non_none
    (__eo_to_smt_exists x (SmtTerm.not (__eo_to_smt F))) (by
      simpa [eo_to_smt_forall_eq x F hx, smtForall] using hNN)

private theorem miniToSmt_eq_eo_to_smt_of_has_smt_translation :
    ∀ t : Term,
      RuleProofs.eo_has_smt_translation t ->
      miniToSmt t = __eo_to_smt t
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B => by
      intro hTrans
      have hTy :
          __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) ≠
            SmtType.None := by
        simpa [RuleProofs.eo_has_smt_translation] using hTrans
      have hArgs :
          __smtx_typeof (__eo_to_smt A) = SmtType.Bool ∧
            __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        rw [typeof_or_eq] at hTy
        cases hA : __smtx_typeof (__eo_to_smt A) <;>
          cases hB : __smtx_typeof (__eo_to_smt B) <;>
          simp [hA, hB, native_ite, native_Teq] at hTy ⊢
      have hATrans : RuleProofs.eo_has_smt_translation A := by
        intro hNone
        have hNoneOr :
            __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
              SmtType.None := by
          rw [typeof_or_eq, hNone]
          simp [native_ite, native_Teq]
        exact hTrans (by simpa using hNoneOr)
      have hBTrans : RuleProofs.eo_has_smt_translation B := by
        intro hNone
        have hNoneOr :
            __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
              SmtType.None := by
          rw [typeof_or_eq, hArgs.1, hNone]
          simp [native_ite, native_Teq]
        exact hTrans (by simpa using hNoneOr)
      rw [miniToSmt]
      rw [miniToSmt_eq_eo_to_smt_of_has_smt_translation A hATrans]
      rw [miniToSmt_eq_eo_to_smt_of_has_smt_translation B hBTrans]
      rfl
  | Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F => by
      intro hTrans
      have hx : xs ≠ Term.__eo_List_nil := by
        intro hxs
        subst xs
        exact hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none)
      rw [miniToSmt]
      exact (eo_to_smt_forall_eq xs F hx).symm
  | t => by
      intro hTrans
      cases t with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | UOp op =>
                  cases op with
                  | or =>
                      have hTy :
                          __smtx_typeof
                              (SmtTerm.or (__eo_to_smt y) (__eo_to_smt a)) ≠
                            SmtType.None := by
                        simpa [RuleProofs.eo_has_smt_translation] using hTrans
                      have hArgs :
                          __smtx_typeof (__eo_to_smt y) = SmtType.Bool ∧
                            __smtx_typeof (__eo_to_smt a) = SmtType.Bool := by
                        rw [typeof_or_eq] at hTy
                        cases hY : __smtx_typeof (__eo_to_smt y) <;>
                          cases hA : __smtx_typeof (__eo_to_smt a) <;>
                          simp [hY, hA, native_ite, native_Teq] at hTy ⊢
                      have hYTrans : RuleProofs.eo_has_smt_translation y := by
                        intro hNone
                        apply hTrans
                        rw [show
                            __eo_to_smt (((Term.UOp UserOp.or).Apply y).Apply a) =
                              SmtTerm.or (__eo_to_smt y) (__eo_to_smt a) by rfl]
                        rw [typeof_or_eq, hNone]
                        simp [native_ite, native_Teq]
                      have hATrans : RuleProofs.eo_has_smt_translation a := by
                        intro hNone
                        apply hTrans
                        rw [show
                            __eo_to_smt (((Term.UOp UserOp.or).Apply y).Apply a) =
                              SmtTerm.or (__eo_to_smt y) (__eo_to_smt a) by rfl]
                        rw [typeof_or_eq, hArgs.1, hNone]
                        simp [native_ite, native_Teq]
                      rw [miniToSmt]
                      rw [miniToSmt_eq_eo_to_smt_of_has_smt_translation y hYTrans]
                      rw [miniToSmt_eq_eo_to_smt_of_has_smt_translation a hATrans]
                      rfl
                  | «forall» =>
                      have hx : y ≠ Term.__eo_List_nil := by
                        intro hy
                        subst y
                        exact hTrans (by
                          change __smtx_typeof SmtTerm.None = SmtType.None
                          exact TranslationProofs.smtx_typeof_none)
                      rw [miniToSmt]
                      exact (eo_to_smt_forall_eq y a hx).symm
                  | _ =>
                      rfl
              | _ =>
                  rfl
          | _ =>
              rfl
      | _ =>
          rfl
termination_by t => sizeOf t

private theorem miniToSmt_type_bool_of_has_bool_type
    (t : Term) :
    RuleProofs.eo_has_bool_type t ->
    __smtx_typeof (miniToSmt t) = SmtType.Bool := by
  intro hBool
  have hTrans :
      RuleProofs.eo_has_smt_translation t :=
    RuleProofs.eo_has_smt_translation_of_has_bool_type t hBool
  rw [miniToSmt_eq_eo_to_smt_of_has_smt_translation t hTrans]
  exact hBool

private theorem qeq_rhs_non_none_of_has_bool_type
    (A B : Term) :
    RuleProofs.eo_has_bool_type (qeq A B) ->
    __smtx_typeof (__eo_to_smt B) ≠ SmtType.None := by
  intro hBool hNone
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      A B hBool with
    ⟨hSame, hLeftNN⟩
  apply hLeftNN
  rw [hSame, hNone]

private theorem qeq_lhs_non_none_of_has_bool_type
    (A B : Term) :
    RuleProofs.eo_has_bool_type (qeq A B) ->
    __smtx_typeof (__eo_to_smt A) ≠ SmtType.None := by
  intro hBool
  exact (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    A B hBool).2

private theorem eo_requires_arg_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

private theorem eo_requires_result_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> __eo_requires x y z = z := by
  intro h
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [hxy, hx, native_ite, SmtEval.native_not] at h
    · simp [hxy, hx, native_ite, SmtEval.native_not]
  · simp [hxy, native_ite] at h

private theorem quant_miniscope_or_shape_of_not_stuck
    (a1 : Term) :
    __eo_prog_quant_miniscope_or a1 ≠ Term.Stuck ->
    ∃ x F G,
      a1 = quantMiniscopeOrFormula x F G ∧
      __is_quant_miniscope_or x F G = Term.Boolean true ∧
      __eo_prog_quant_miniscope_or a1 =
        quantMiniscopeOrFormula x F G := by
  intro hProg
  cases a1 with
  | Apply lhs G =>
      cases lhs with
      | Apply eqHead lhsArg =>
          cases eqHead with
          | UOp opEq =>
              cases opEq with
              | eq =>
                  cases lhsArg with
                  | Apply forallHead F =>
                      cases forallHead with
                      | Apply forallOp x =>
                          cases forallOp with
                          | UOp opForall =>
                              cases opForall with
                              | «forall» =>
                                  let body :=
                                    quantMiniscopeOrFormula x F G
                                  let guard := __is_quant_miniscope_or x F G
                                  have hReq :
                                      __eo_requires guard
                                          (Term.Boolean true) body ≠
                                        Term.Stuck := by
                                    simpa [guard, body, quantMiniscopeOrFormula,
                                      qeq, qforall, __eo_prog_quant_miniscope_or]
                                      using hProg
                                  have hGuard :
                                      guard = Term.Boolean true :=
                                    eo_requires_arg_eq_of_ne_stuck hReq
                                  have hProgEq :
                                      __eo_prog_quant_miniscope_or
                                          (quantMiniscopeOrFormula x F G) =
                                        quantMiniscopeOrFormula x F G := by
                                    change
                                      __eo_requires guard
                                          (Term.Boolean true) body =
                                        body
                                    exact eo_requires_result_eq_of_ne_stuck hReq
                                  exact ⟨x, F, G, rfl, by simpa [guard] using hGuard,
                                    hProgEq⟩
                              | _ =>
                                  simp [__eo_prog_quant_miniscope_or] at hProg
                          | _ =>
                              simp [__eo_prog_quant_miniscope_or] at hProg
                      | _ =>
                          simp [__eo_prog_quant_miniscope_or] at hProg
                  | _ =>
                      simp [__eo_prog_quant_miniscope_or] at hProg
              | _ =>
                  simp [__eo_prog_quant_miniscope_or] at hProg
          | _ =>
              simp [__eo_prog_quant_miniscope_or] at hProg
      | _ =>
          simp [__eo_prog_quant_miniscope_or] at hProg
  | _ =>
      simp [__eo_prog_quant_miniscope_or] at hProg

-- TODO: replace this semantic kernel with the recursive miniscope proof.
-- The command wrapper below is proved, but this axiom is not a foundational
-- proof of the `quant_miniscope_or` rule.
private axiom quant_miniscope_or_formula_true
    (M : SmtModel) (hM : model_total_typed M)
    (x F G : Term) :
    RuleProofs.eo_has_smt_translation
        (quantMiniscopeOrFormula x F G) ->
    __eo_typeof (quantMiniscopeOrFormula x F G) = Term.Bool ->
    __is_quant_miniscope_or x F G = Term.Boolean true ->
    eo_interprets M (quantMiniscopeOrFormula x F G) true

theorem cmd_step_quant_miniscope_or_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.quant_miniscope_or args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.quant_miniscope_or args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.quant_miniscope_or args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg :
      __eo_cmd_step_proven s CRule.quant_miniscope_or args premises ≠
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
                simpa [cmdTranslationOk, cArgListTranslationOk] using
                  hCmdTrans
              have hProgQuant :
                  __eo_prog_quant_miniscope_or a1 ≠ Term.Stuck := by
                change __eo_prog_quant_miniscope_or a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_miniscope_or_shape_of_not_stuck a1 hProgQuant with
                ⟨x, F, G, ha1, hGuard, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation
                    (quantMiniscopeOrFormula x F G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (quantMiniscopeOrFormula x F G) =
                    Term.Bool := by
                change __eo_typeof (__eo_prog_quant_miniscope_or a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type
                    (quantMiniscopeOrFormula x F G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (quantMiniscopeOrFormula x F G)
                  hTransFormula hFormulaType
              have hFact :
                  eo_interprets M (quantMiniscopeOrFormula x F G) true :=
                quant_miniscope_or_formula_true M hM x F G
                  hTransFormula hFormulaType hGuard
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_miniscope_or a1) true
                rw [hProgEq]
                exact hFact
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_quant_miniscope_or a1)
                rw [hProgEq]
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type _
                  hFormulaBool
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
