import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Closed.ContainsAtomicTermListFree

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private def qterm (Q x F : Term) : Term :=
  Term.Apply (Term.Apply Q x) F

private def qeq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

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

private theorem eo_requires_true_nonstuck_eq
    {c r : Term}
    (hNonstuck : __eo_requires c (Term.Boolean true) r ≠ Term.Stuck) :
  __eo_requires c (Term.Boolean true) r = r :=
by
  by_cases hC : c = Term.Boolean true
  · subst c
    simp [__eo_requires, native_ite, native_teq, native_not]
  · exfalso
    apply hNonstuck
    simp [__eo_requires, native_ite, native_teq, hC]

private theorem eo_l1_get_unused_vars_nonstuck_eq
    {Q x F G : Term}
    (hG : G ≠ Term.Stuck) :
  __eo_l_1___get_unused_vars (Term.Apply (Term.Apply Q x) F) G =
    __eo_requires (__eo_eq F G) (Term.Boolean true)
      (__eo_list_setof Term.__eo_List_cons x) :=
by
  cases G <;> simp [__eo_l_1___get_unused_vars] at hG ⊢

private theorem eo_eq_self_true
    {t : Term}
    (hT : t ≠ Term.Stuck) :
  __eo_eq t t = Term.Boolean true :=
by
  cases t <;> simp [__eo_eq, native_teq] at hT ⊢

private theorem eo_eq_true_eq
    {a b : Term}
    (hEq : __eo_eq a b = Term.Boolean true) :
  a = b :=
by
  have hEqSymm : b = a := by
    cases a <;> cases b <;> simp [__eo_eq, native_teq] at hEq ⊢
    all_goals exact hEq
  exact hEqSymm.symm

private theorem eo_ite_nonstuck_guard_cases
    {c t e : Term}
    (hNonstuck : __eo_ite c t e ≠ Term.Stuck) :
  c = Term.Boolean true ∨ c = Term.Boolean false :=
by
  cases c <;> simp [__eo_ite, native_ite, native_teq] at hNonstuck ⊢

private theorem get_unused_vars_same_quant_body_eq
    {Q x F y : Term}
    (hQ : Q ≠ Term.Stuck)
    (hF : F ≠ Term.Stuck) :
  __get_unused_vars (Term.Apply (Term.Apply Q x) F)
      (Term.Apply (Term.Apply Q y) F) =
    __eo_requires
      (__eo_list_minclude Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y)
      (Term.Boolean true)
      (__eo_list_diff Term.__eo_List_cons
        (__eo_list_setof Term.__eo_List_cons x) y) :=
by
  have hQEq : __eo_eq Q Q = Term.Boolean true :=
    eo_eq_self_true hQ
  have hFEq : __eo_eq F F = Term.Boolean true :=
    eo_eq_self_true hF
  simp [__get_unused_vars, hQEq, hFEq, __eo_and, __eo_ite, native_and,
    native_ite, native_teq]

private theorem eo_var_env_of_l1_get_unused_vars_ne_stuck
    {Q x F G : Term} {xVars : List EoVarKey}
    (hX : EoVarEnv x xVars)
    (hNonstuck :
      __eo_l_1___get_unused_vars (Term.Apply (Term.Apply Q x) F) G ≠
        Term.Stuck) :
  ∃ vars,
    EoVarEnv
      (__eo_l_1___get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
      vars :=
by
  rcases EoVarEnv.setof hX with ⟨setVars, hSet⟩
  by_cases hG : G = Term.Stuck
  · subst G
    exfalso
    exact hNonstuck (by simp [__eo_l_1___get_unused_vars])
  · have hL1Eq :=
      eo_l1_get_unused_vars_nonstuck_eq
        (Q := Q) (x := x) (F := F) hG
    refine ⟨setVars, ?_⟩
    have hReqNonstuck :
        __eo_requires (__eo_eq F G) (Term.Boolean true)
            (__eo_list_setof Term.__eo_List_cons x) ≠
          Term.Stuck := by
      intro hReq
      apply hNonstuck
      rw [hL1Eq, hReq]
    have hReqEq := eo_requires_true_nonstuck_eq hReqNonstuck
    rw [hL1Eq, hReqEq]
    exact hSet

private theorem eo_var_env_of_get_unused_vars_same_quant_body_ne_stuck
    {Q x F y : Term} {xVars yVars : List EoVarKey}
    (hQ : Q ≠ Term.Stuck)
    (hF : F ≠ Term.Stuck)
    (hX : EoVarEnv x xVars)
    (hY : EoVarEnv y yVars)
    (hNonstuck :
      __get_unused_vars (Term.Apply (Term.Apply Q x) F)
          (Term.Apply (Term.Apply Q y) F) ≠
        Term.Stuck) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
        (Term.Apply (Term.Apply Q y) F))
      vars :=
by
  rcases EoVarEnv.setof hX with ⟨setVars, hSet⟩
  rcases EoVarEnv.diff hSet hY with ⟨diffVars, hDiff⟩
  have hGetEq :=
    get_unused_vars_same_quant_body_eq
      (Q := Q) (x := x) (F := F) (y := y) hQ hF
  refine ⟨diffVars, ?_⟩
  have hReqNonstuck :
      __eo_requires
          (__eo_list_minclude Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y)
          (Term.Boolean true)
          (__eo_list_diff Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y) ≠
        Term.Stuck := by
    intro hReq
    apply hNonstuck
    rw [hGetEq, hReq]
  have hReqEq := eo_requires_true_nonstuck_eq hReqNonstuck
  rw [hGetEq, hReqEq]
  exact hDiff

private theorem contains_atomic_term_list_free_rec_false_except_ne_stuck
    {t except bound : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec t except bound =
        Term.Boolean false) :
  except ≠ Term.Stuck :=
by
  intro hExcept
  subst except
  cases t <;> simp [__contains_atomic_term_list_free_rec] at hNoFree

private theorem eo_var_env_of_get_unused_vars_same_quant_body_of_contains_false
    {Q x F y : Term} {xVars yVars : List EoVarKey}
    (hQ : Q ≠ Term.Stuck)
    (hF : F ≠ Term.Stuck)
    (hX : EoVarEnv x xVars)
    (hY : EoVarEnv y yVars)
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply Q y) F)
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q y) F))
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
        (Term.Apply (Term.Apply Q y) F))
      vars :=
by
  have hGetNonstuck :
      __get_unused_vars (Term.Apply (Term.Apply Q x) F)
          (Term.Apply (Term.Apply Q y) F) ≠
        Term.Stuck :=
    contains_atomic_term_list_free_rec_false_except_ne_stuck hNoFree
  exact
    eo_var_env_of_get_unused_vars_same_quant_body_ne_stuck
      hQ hF hX hY hGetNonstuck

private theorem eo_var_env_of_get_unused_vars_quant_branch_of_contains_false
    {Q x F Q₂ y F₂ : Term}
    {xVars : List EoVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hX : EoVarEnv x xVars)
    (hGTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply Q₂ y) F₂))
    (hNoFree :
      __contains_atomic_term_list_free_rec
          (Term.Apply (Term.Apply Q₂ y) F₂)
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂))
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F)
        (Term.Apply (Term.Apply Q₂ y) F₂))
      vars :=
by
  have hGetNonstuck :
      __get_unused_vars (Term.Apply (Term.Apply Q x) F)
          (Term.Apply (Term.Apply Q₂ y) F₂) ≠
        Term.Stuck :=
    contains_atomic_term_list_free_rec_false_except_ne_stuck hNoFree
  have hIteNonstuck :
      __eo_ite
          (__eo_and (__eo_eq Q Q₂) (__eo_eq F F₂))
          (__eo_requires
            (__eo_list_minclude Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y)
            (Term.Boolean true)
            (__eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y))
          (__eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂)) ≠
        Term.Stuck := by
    intro hStuck
    apply hGetNonstuck
    simpa [__get_unused_vars] using hStuck
  rcases eo_ite_nonstuck_guard_cases hIteNonstuck with hGuard | hGuard
  · have hParts := eo_and_eq_true_cases hGuard
    have hQEq : Q = Q₂ := eo_eq_true_eq hParts.1
    have hFEqTrue : __eo_eq F F₂ = Term.Boolean true := hParts.2
    have hFEq : F = F₂ := eo_eq_true_eq hFEqTrue
    subst Q₂
    subst F₂
    have hQNonstuck : Q ≠ Term.Stuck := by
      rcases hQ with hForall | hExists
      · rw [hForall]
        intro h
        cases h
      · rw [hExists]
        intro h
        cases h
    have hFNonstuck : F ≠ Term.Stuck := by
      intro hF
      subst F
      simp [__eo_eq] at hFEqTrue
    rcases eo_var_env_of_quant_has_smt_translation hQ hGTrans with
      ⟨yVars, hY⟩
    exact
      eo_var_env_of_get_unused_vars_same_quant_body_of_contains_false
        hQNonstuck hFNonstuck hX hY hNoFree
  · have hGetEqFallback :
        __get_unused_vars (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂) =
          __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂) := by
      simp [__get_unused_vars, hGuard, __eo_ite, native_ite, native_teq]
    have hFallbackNonstuck :
        __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F)
            (Term.Apply (Term.Apply Q₂ y) F₂) ≠
          Term.Stuck := by
      intro hStuck
      apply hGetNonstuck
      rw [hGetEqFallback, hStuck]
    rcases
      eo_var_env_of_l1_get_unused_vars_ne_stuck hX hFallbackNonstuck with
      ⟨vars, hEnv⟩
    exact ⟨vars, by rw [hGetEqFallback]; exact hEnv⟩

private theorem get_unused_vars_fallback_eq_of_not_quant_branch
    {Q x F G : Term}
    (hG : G ≠ Term.Stuck)
    (hNotQuant :
      ∀ Q₂ y F₂,
        G ≠ Term.Apply (Term.Apply Q₂ y) F₂) :
  __get_unused_vars (Term.Apply (Term.Apply Q x) F) G =
    __eo_l_1___get_unused_vars (Term.Apply (Term.Apply Q x) F) G :=
by
  cases G <;> simp [__get_unused_vars] at hG hNotQuant ⊢
  case Apply f a =>
    cases f <;> simp at hNotQuant ⊢
    all_goals
      exfalso
      exact hNotQuant _ _ rfl

private theorem eo_var_env_of_get_unused_vars_of_contains_false
    {Q x F G : Term} {xVars : List EoVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hX : EoVarEnv x xVars)
    (hGTrans : eoHasSmtTranslation G)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
      vars :=
by
  by_cases hShape :
      ∃ Q₂ y F₂,
        G = Term.Apply (Term.Apply Q₂ y) F₂
  · rcases hShape with ⟨Q₂, y, F₂, rfl⟩
    exact
      eo_var_env_of_get_unused_vars_quant_branch_of_contains_false
        hQ hX hGTrans hNoFree
  · have hGetNonstuck :
        __get_unused_vars (Term.Apply (Term.Apply Q x) F) G ≠
          Term.Stuck :=
      contains_atomic_term_list_free_rec_false_except_ne_stuck hNoFree
    have hGNonstuck : G ≠ Term.Stuck := by
      intro hGStuck
      subst G
      apply hGetNonstuck
      simp [__get_unused_vars]
    have hGetEqFallback :
        __get_unused_vars (Term.Apply (Term.Apply Q x) F) G =
          __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F) G :=
      get_unused_vars_fallback_eq_of_not_quant_branch
        hGNonstuck
        (by
          intro Q₂ y F₂ hEq
          exact hShape ⟨Q₂, y, F₂, hEq⟩)
    have hFallbackNonstuck :
        __eo_l_1___get_unused_vars
            (Term.Apply (Term.Apply Q x) F) G ≠
          Term.Stuck := by
      intro hStuck
      apply hGetNonstuck
      rw [hGetEqFallback, hStuck]
    rcases
      eo_var_env_of_l1_get_unused_vars_ne_stuck hX hFallbackNonstuck with
      ⟨vars, hEnv⟩
    exact ⟨vars, by rw [hGetEqFallback]; exact hEnv⟩

private theorem eo_var_env_of_get_unused_vars_of_quant_has_smt_translation
    {Q x F G : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hLeftTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply Q x) F))
    (hGTrans : eoHasSmtTranslation G)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnv
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
      vars :=
by
  rcases eo_var_env_of_quant_has_smt_translation hQ hLeftTrans with
    ⟨xVars, hX⟩
  exact
    eo_var_env_of_get_unused_vars_of_contains_false
      hQ hX hGTrans hNoFree

private theorem eo_var_env_perm_of_get_unused_vars_of_quant_has_smt_translation
    {Q x F G : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hLeftTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply Q x) F))
    (hGTrans : eoHasSmtTranslation G)
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
          Term.__eo_List_nil =
        Term.Boolean false) :
  ∃ vars,
    EoVarEnvPerm
      (__get_unused_vars (Term.Apply (Term.Apply Q x) F) G)
      vars :=
by
  rcases
    eo_var_env_of_get_unused_vars_of_quant_has_smt_translation
      hQ hLeftTrans hGTrans hNoFree with
    ⟨vars, hEnv⟩
  exact ⟨vars, EoVarEnvPerm.of_exact hEnv⟩

private theorem quant_unused_vars_shape_of_not_stuck
    (x1 : Term) :
    __eo_prog_quant_unused_vars x1 ≠ Term.Stuck ->
    ∃ Q x F G,
      x1 = qeq (qterm Q x F) G ∧
      (Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists) ∧
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false ∧
      __eo_prog_quant_unused_vars x1 = qeq (qterm Q x F) G := by
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
                          let inner :=
                            __eo_requires
                              (__contains_atomic_term_list_free_rec G
                                (__get_unused_vars v0 G)
                                Term.__eo_List_nil)
                              (Term.Boolean false)
                              (qeq v0 G)
                          have hReq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner ≠ Term.Stuck := by
                            simpa [qeq, qterm, v0, inner,
                              __eo_prog_quant_unused_vars] using hProg
                          have hGuard :
                              __eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                  (__eo_eq Q (Term.UOp UserOp.exists)) =
                                Term.Boolean true :=
                            eo_requires_arg_eq_of_ne_stuck hReq
                          have hInnerNe : inner ≠ Term.Stuck :=
                            body_ne_stuck_of_requires_ne_stuck hReq
                          have hNoFree :
                              __contains_atomic_term_list_free_rec G
                                  (__get_unused_vars v0 G)
                                  Term.__eo_List_nil =
                                Term.Boolean false :=
                            eo_requires_arg_eq_of_ne_stuck hInnerNe
                          have hOuterEq :
                              __eo_requires
                                  (__eo_or (__eo_eq Q (Term.UOp UserOp.forall))
                                    (__eo_eq Q (Term.UOp UserOp.exists)))
                                  (Term.Boolean true) inner =
                                inner :=
                            eo_requires_result_eq_of_ne_stuck hReq
                          have hInnerEq :
                              inner = qeq v0 G := by
                            exact eo_requires_result_eq_of_ne_stuck hInnerNe
                          rcases eo_or_eq_true_cases_local
                              (__eo_eq Q (Term.UOp UserOp.forall))
                              (__eo_eq Q (Term.UOp UserOp.exists)) hGuard with
                            hForall | hExists
                          · have hQ : Q = Term.UOp UserOp.forall :=
                              eo_eq_true_eq hForall
                            subst Q
                            refine
                              ⟨Term.UOp UserOp.forall, x, F, G, rfl,
                                Or.inl rfl, ?_, ?_⟩
                            · simpa [v0, qterm] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.forall) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.forall) x F) G
                              simpa [qeq, qterm, v0,
                                __eo_prog_quant_unused_vars, hOuterEq,
                                hInnerEq]
                          · have hQ : Q = Term.UOp UserOp.exists :=
                              eo_eq_true_eq hExists
                            subst Q
                            refine
                              ⟨Term.UOp UserOp.exists, x, F, G, rfl,
                                Or.inr rfl, ?_, ?_⟩
                            · simpa [v0, qterm] using hNoFree
                            · change __eo_prog_quant_unused_vars
                                (qeq (qterm (Term.UOp UserOp.exists) x F) G) =
                                  qeq (qterm (Term.UOp UserOp.exists) x F) G
                              simpa [qeq, qterm, v0,
                                __eo_prog_quant_unused_vars, hOuterEq,
                                hInnerEq]
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

private theorem quant_unused_vars_eval
    (M : SmtModel) (hM : model_total_typed M)
    (Q x F G : Term)
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hBool : RuleProofs.eo_has_bool_type (qeq (qterm Q x F) G))
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false) :
  __smtx_model_eval M (__eo_to_smt (qterm Q x F)) =
    __smtx_model_eval M (__eo_to_smt G) :=
by
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (qterm Q x F) G hBool with
    ⟨hSameTy, hLeftNN⟩
  have hLeftTrans :
      RuleProofs.eo_has_smt_translation (qterm Q x F) := by
    exact hLeftNN
  have hGTrans :
      RuleProofs.eo_has_smt_translation G := by
    intro hNone
    exact hLeftNN (by rw [hSameTy, hNone])
  rcases
    eo_var_env_perm_of_get_unused_vars_of_quant_has_smt_translation
      hQ hLeftTrans hGTrans hNoFree with
    ⟨exceptVars, hExceptEnv⟩
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
  have hProg :
      __eo_cmd_step_proven s CRule.quant_unused_vars args premises ≠
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
                  __eo_prog_quant_unused_vars a1 ≠ Term.Stuck := by
                change __eo_prog_quant_unused_vars a1 ≠ Term.Stuck at hProg
                simpa using hProg
              rcases quant_unused_vars_shape_of_not_stuck a1 hProgQuant with
                ⟨Q, x, F, G, ha1, hQ, hNoFree, hProgEq⟩
              have hTransFormula :
                  RuleProofs.eo_has_smt_translation (qeq (qterm Q x F) G) := by
                simpa [ha1] using hTransA1
              have hFormulaType :
                  __eo_typeof (qeq (qterm Q x F) G) = Term.Bool := by
                change __eo_typeof (__eo_prog_quant_unused_vars a1) =
                  Term.Bool at hResultTy
                rw [hProgEq] at hResultTy
                exact hResultTy
              have hFormulaBool :
                  RuleProofs.eo_has_bool_type (qeq (qterm Q x F) G) :=
                RuleProofs.eo_typeof_bool_implies_has_bool_type
                  (qeq (qterm Q x F) G) hTransFormula hFormulaType
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M
                  (__eo_prog_quant_unused_vars a1) true
                rw [hProgEq]
                apply RuleProofs.eo_interprets_eq_of_rel M
                  (qterm Q x F) G
                · exact hFormulaBool
                · have hEvalEq :=
                    quant_unused_vars_eval M hM Q x F G hQ hFormulaBool
                      hNoFree
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
