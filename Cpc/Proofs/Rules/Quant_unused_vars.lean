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

private theorem get_unused_vars_branch_of_contains_false
    {Q x F G : Term}
    (hNoFree :
      __contains_atomic_term_list_free_rec G
          (__get_unused_vars (qterm Q x F) G) Term.__eo_List_nil =
        Term.Boolean false) :
  (G = F ∧
      __get_unused_vars (qterm Q x F) G =
        __eo_list_setof Term.__eo_List_cons x) ∨
    ∃ y,
      G = qterm Q y F ∧
        __eo_list_minclude Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y =
          Term.Boolean true ∧
        __get_unused_vars (qterm Q x F) G =
          __eo_list_diff Term.__eo_List_cons
            (__eo_list_setof Term.__eo_List_cons x) y :=
by
  have hGetNonstuck :
      __get_unused_vars (qterm Q x F) G ≠ Term.Stuck :=
    contains_atomic_term_list_free_rec_false_except_ne_stuck hNoFree
  by_cases hShape :
      ∃ Q₂ y F₂,
        G = Term.Apply (Term.Apply Q₂ y) F₂
  · rcases hShape with ⟨Q₂, y, F₂, rfl⟩
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
      simpa [qterm, __get_unused_vars] using hStuck
    rcases eo_ite_nonstuck_guard_cases hIteNonstuck with hGuard | hGuard
    · have hParts := eo_and_eq_true_cases hGuard
      have hQEq : Q = Q₂ := eo_eq_true_eq hParts.1
      have hFEq : F = F₂ := eo_eq_true_eq hParts.2
      subst Q₂
      subst F₂
      have hReqNonstuck :
          __eo_requires
              (__eo_list_minclude Term.__eo_List_cons
                (__eo_list_setof Term.__eo_List_cons x) y)
              (Term.Boolean true)
              (__eo_list_diff Term.__eo_List_cons
                (__eo_list_setof Term.__eo_List_cons x) y) ≠
            Term.Stuck := by
        intro hStuck
        apply hGetNonstuck
        simpa [qterm, __get_unused_vars, hGuard, __eo_ite,
          native_ite, native_teq] using hStuck
      have hMinclude :
          __eo_list_minclude Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y =
            Term.Boolean true :=
        eo_requires_arg_eq_of_ne_stuck hReqNonstuck
      have hReqEq :=
        eo_requires_true_nonstuck_eq hReqNonstuck
      right
      refine ⟨y, rfl, hMinclude, ?_⟩
      simp [qterm, __get_unused_vars, hGuard, __eo_ite,
        native_ite, native_teq, hReqEq]
    · have hGetEqFallback :
          __get_unused_vars (qterm Q x F)
              (Term.Apply (Term.Apply Q₂ y) F₂) =
            __eo_l_1___get_unused_vars
              (Term.Apply (Term.Apply Q x) F)
              (Term.Apply (Term.Apply Q₂ y) F₂) := by
        simp [qterm, __get_unused_vars, hGuard, __eo_ite,
          native_ite, native_teq]
      have hFallbackNonstuck :
          __eo_l_1___get_unused_vars
              (Term.Apply (Term.Apply Q x) F)
              (Term.Apply (Term.Apply Q₂ y) F₂) ≠
            Term.Stuck := by
        intro hStuck
        apply hGetNonstuck
        rw [hGetEqFallback, hStuck]
      have hGNonstuck :
          Term.Apply (Term.Apply Q₂ y) F₂ ≠ Term.Stuck := by
        intro h
        cases h
      have hL1Eq :=
        eo_l1_get_unused_vars_nonstuck_eq
          (Q := Q) (x := x) (F := F)
          (G := Term.Apply (Term.Apply Q₂ y) F₂) hGNonstuck
      have hReqNonstuck :
          __eo_requires (__eo_eq F (Term.Apply (Term.Apply Q₂ y) F₂))
              (Term.Boolean true)
              (__eo_list_setof Term.__eo_List_cons x) ≠
            Term.Stuck := by
        intro hStuck
        apply hFallbackNonstuck
        rw [hL1Eq, hStuck]
      have hEqGuard :
          __eo_eq F (Term.Apply (Term.Apply Q₂ y) F₂) =
            Term.Boolean true :=
        eo_requires_arg_eq_of_ne_stuck hReqNonstuck
      have hFG :
          F = Term.Apply (Term.Apply Q₂ y) F₂ :=
        eo_eq_true_eq hEqGuard
      have hReqEq :=
        eo_requires_true_nonstuck_eq hReqNonstuck
      left
      constructor
      · exact hFG.symm
      · rw [hGetEqFallback, hL1Eq, hReqEq]
  · have hGNonstuck : G ≠ Term.Stuck := by
      intro hG
      subst G
      apply hGetNonstuck
      simp [qterm, __get_unused_vars]
    have hGetEqFallback :
        __get_unused_vars (qterm Q x F) G =
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
    have hL1Eq :=
      eo_l1_get_unused_vars_nonstuck_eq
        (Q := Q) (x := x) (F := F) hGNonstuck
    have hReqNonstuck :
        __eo_requires (__eo_eq F G) (Term.Boolean true)
            (__eo_list_setof Term.__eo_List_cons x) ≠
          Term.Stuck := by
      intro hStuck
      apply hFallbackNonstuck
      rw [hL1Eq, hStuck]
    have hEqGuard :
        __eo_eq F G = Term.Boolean true :=
      eo_requires_arg_eq_of_ne_stuck hReqNonstuck
    have hFG : F = G := eo_eq_true_eq hEqGuard
    have hReqEq := eo_requires_true_nonstuck_eq hReqNonstuck
    left
    constructor
    · exact hFG.symm
    · rw [hGetEqFallback, hL1Eq, hReqEq]

private theorem quant_body_has_smt_translation
    {Q x F : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation (qterm Q x F)) :
  RuleProofs.eo_has_smt_translation F :=
by
  rcases eo_var_env_of_quant_has_smt_translation hQ hTrans with
    ⟨vars, hEnv⟩
  cases hEnv with
  | nil =>
      rcases hQ with hForall | hExists
      · subst Q
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
      · subst Q
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
  | cons hTail =>
      rename_i s T env tailVars
      rcases hQ with hForall | hExists
      · subst Q
        exact
          body_has_smt_translation_of_forall_list_branch_has_smt_translation
            hTrans
      · subst Q
        exact
          body_has_smt_translation_of_exists_list_branch_has_smt_translation
            hTrans

private theorem quant_body_has_bool_type
    {Q x F : Term}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation (qterm Q x F)) :
  __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
by
  rcases eo_var_env_of_quant_has_smt_translation hQ hTrans with
    ⟨vars, hEnv⟩
  cases hEnv with
  | nil =>
      rcases hQ with hForall | hExists
      · subst Q
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
      · subst Q
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
  | cons hTail =>
      rename_i s T env tailVars
      rcases hQ with hForall | hExists
      · subst Q
        have hNotBool :
            __smtx_typeof
                (SmtTerm.not
                  (__eo_to_smt_exists
                    (Term.Apply (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) env)
                    (SmtTerm.not (__eo_to_smt F)))) =
              SmtType.Bool :=
          smtx_typeof_not_eq_bool_of_non_none
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) env)
              (SmtTerm.not (__eo_to_smt F)))
            (by
              change
                __smtx_typeof
                    (SmtTerm.not
                      (__eo_to_smt_exists
                        (Term.Apply (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T)) env)
                        (SmtTerm.not (__eo_to_smt F)))) ≠
                  SmtType.None
              simpa [qterm, RuleProofs.eo_has_smt_translation] using hTrans)
        have hExistsBool :
            __smtx_typeof
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F))) =
              SmtType.Bool :=
          smtx_typeof_not_arg_eq_bool
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) env)
              (SmtTerm.not (__eo_to_smt F)))
            hNotBool
        have hBodyNotBool :
            __smtx_typeof (SmtTerm.not (__eo_to_smt F)) =
              SmtType.Bool :=
          TranslationProofs.eo_to_smt_exists_body_bool_of_bool
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (SmtTerm.not (__eo_to_smt F)) hExistsBool
        exact smtx_typeof_not_arg_eq_bool (__eo_to_smt F) hBodyNotBool
      · subst Q
        have hExistsBool :
            __smtx_typeof
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (__eo_to_smt F)) =
              SmtType.Bool :=
          smtx_typeof_eo_to_smt_exists_cons_eq_bool_of_non_none
            (Term.Var (Term.String s) T) env (__eo_to_smt F)
            (by
              change
                __smtx_typeof
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T)) env)
                      (__eo_to_smt F)) ≠
                  SmtType.None
              simpa [qterm, RuleProofs.eo_has_smt_translation] using hTrans)
        exact
          TranslationProofs.eo_to_smt_exists_body_bool_of_bool
            (Term.Apply (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) env)
            (__eo_to_smt F) hExistsBool

private theorem smtx_typeof_exists_tail_bool_of_cons_bool
    (s : native_String) (T xs : Term) (body : SmtTerm) :
    __smtx_typeof
        (__eo_to_smt_exists
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs)
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
          (Term.Apply (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) xs)
          body) = SmtType.Bool ->
    __smtx_type_wf (__eo_to_smt_type T) = true := by
  intro hTy
  have hTail :
      __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
    smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
  have hGuardNN :
      __smtx_typeof_guard_wf (__eo_to_smt_type T) SmtType.Bool ≠
        SmtType.None := by
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

private theorem smtx_type_wf_of_eo_var_env_exists_bool
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hTy : __smtx_typeof (__eo_to_smt_exists xs body) =
      SmtType.Bool) :
  ∀ s T, (s, T) ∈ vars ->
    __smtx_type_wf (__eo_to_smt_type T) = true :=
by
  induction hEnv generalizing body with
  | nil =>
      intro s T hMem
      cases hMem
  | cons hTail ih =>
      rename_i s T xs tailVars
      intro s' T' hMem
      cases hMem with
      | head =>
          exact smtx_type_wf_of_exists_cons_bool s T xs body hTy
      | tail _ hTailMem =>
          have hTailTy :
              __smtx_typeof (__eo_to_smt_exists xs body) =
                SmtType.Bool :=
            smtx_typeof_exists_tail_bool_of_cons_bool s T xs body hTy
          exact ih hTailTy s' T' hTailMem

private theorem quant_binder_types_wf
    {Q x F : Term} {vars : List EoVarKey}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation (qterm Q x F))
    (hEnv : EoVarEnv x vars) :
  ∀ s T, (s, T) ∈ vars ->
    __smtx_type_wf (__eo_to_smt_type T) = true :=
by
  rcases hQ with hForall | hExists
  · subst Q
    cases hEnv with
    | nil =>
        intro s T hMem
        cases hMem
    | cons hTail =>
        rename_i s T env tailVars
        have hNotTy :
            __smtx_typeof
                (SmtTerm.not
                  (__eo_to_smt_exists
                    (Term.Apply (Term.Apply Term.__eo_List_cons
                      (Term.Var (Term.String s) T)) env)
                    (SmtTerm.not (__eo_to_smt F)))) =
              SmtType.Bool :=
          smtx_typeof_not_eq_bool_of_non_none
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) env)
              (SmtTerm.not (__eo_to_smt F)))
            (by
              change
                __smtx_typeof
                    (SmtTerm.not
                      (__eo_to_smt_exists
                        (Term.Apply (Term.Apply Term.__eo_List_cons
                          (Term.Var (Term.String s) T)) env)
                        (SmtTerm.not (__eo_to_smt F)))) ≠
                  SmtType.None
              simpa [qterm, RuleProofs.eo_has_smt_translation] using hTrans)
        have hExistsTy :
            __smtx_typeof
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F))) =
              SmtType.Bool :=
          smtx_typeof_not_arg_eq_bool
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) env)
              (SmtTerm.not (__eo_to_smt F))) hNotTy
        exact
          smtx_type_wf_of_eo_var_env_exists_bool
            (EoVarEnv.cons (s := s) (T := T) hTail) hExistsTy
  · subst Q
    cases hEnv with
    | nil =>
        intro s T hMem
        cases hMem
    | cons hTail =>
        rename_i s T env tailVars
        have hExistsTy :
            __smtx_typeof
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (__eo_to_smt F)) =
              SmtType.Bool :=
          smtx_typeof_eo_to_smt_exists_cons_eq_bool_of_non_none
            (Term.Var (Term.String s) T) env (__eo_to_smt F)
            (by
              change
                __smtx_typeof
                    (__eo_to_smt_exists
                      (Term.Apply (Term.Apply Term.__eo_List_cons
                        (Term.Var (Term.String s) T)) env)
                      (__eo_to_smt F)) ≠
                  SmtType.None
              simpa [qterm, RuleProofs.eo_has_smt_translation] using hTrans)
        exact
          smtx_type_wf_of_eo_var_env_exists_bool
            (EoVarEnv.cons (s := s) (T := T) hTail) hExistsTy

private theorem smtx_model_eval_exists_eq_body_of_body_eval_eq
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hBody :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s T v) body =
              __smtx_model_eval M body) :
  __smtx_model_eval M (SmtTerm.exists s T body) =
    __smtx_model_eval M body :=
by
  classical
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with
    ⟨b, hEvalBody⟩
  rcases canonical_type_inhabited_of_type_wf T hWF with
    ⟨w, hwTy, hwCan⟩
  have hwCanBool : __smtx_value_canonical_bool w = true := by
    simpa [__smtx_value_canonical] using hwCan
  cases b
  · rw [hEvalBody]
    by_cases hSat :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true
    · rcases hSat with ⟨v, hvTy, hvCan, hvEval⟩
      have hConst := hBody v hvTy hvCan
      rw [hEvalBody] at hConst
      rw [hConst] at hvEval
      cases hvEval
    · simp [__smtx_model_eval, hSat]
  · rw [hEvalBody]
    have hSat :
        ∃ v : SmtValue,
          __smtx_typeof_value v = T ∧
            __smtx_value_canonical_bool v = true ∧
            __smtx_model_eval (native_model_push M s T v) body =
              SmtValue.Boolean true := by
      refine ⟨w, hwTy, hwCanBool, ?_⟩
      rw [hBody w hwTy hwCanBool, hEvalBody]
    simp [__smtx_model_eval, hSat]

private theorem smtx_model_eval_forall_eq_body_of_body_eval_eq
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (T : SmtType) (body : SmtTerm)
    (hWF : __smtx_type_wf T = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hBody :
      ∀ v : SmtValue,
        __smtx_typeof_value v = T ->
          __smtx_value_canonical_bool v = true ->
            __smtx_model_eval (native_model_push M s T v) body =
              __smtx_model_eval M body) :
  __smtx_model_eval M (SmtTerm.forall s T body) =
    __smtx_model_eval M body :=
by
  classical
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with
    ⟨b, hEvalBody⟩
  rcases canonical_type_inhabited_of_type_wf T hWF with
    ⟨w, hwTy, hwCan⟩
  have hwCanBool : __smtx_value_canonical_bool w = true := by
    simpa [__smtx_value_canonical] using hwCan
  cases b
  · rw [hEvalBody]
    have hNotAll :
        ¬ ∀ v : SmtValue,
          __smtx_typeof_value v = T ->
            __smtx_value_canonical_bool v = true ->
              __smtx_model_eval (native_model_push M s T v) body =
                SmtValue.Boolean true := by
      intro hAll
      have hConst := hBody w hwTy hwCanBool
      rw [hEvalBody] at hConst
      have hTrue := hAll w hwTy hwCanBool
      rw [hConst] at hTrue
      cases hTrue
    simp [__smtx_model_eval, hNotAll]
  · rw [hEvalBody]
    have hAll :
        ∀ v : SmtValue,
          __smtx_typeof_value v = T ->
            __smtx_value_canonical_bool v = true ->
              __smtx_model_eval (native_model_push M s T v) body =
        SmtValue.Boolean true := by
      intro v hvTy hvCan
      rw [hBody v hvTy hvCan, hEvalBody]
    simpa [__smtx_model_eval] using hAll

private theorem smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
    {xs : Term} {vars : List EoVarKey} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
  __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
by
  induction hEnv generalizing body with
  | nil =>
      simpa [__eo_to_smt_exists] using hBodyTy
  | cons hTail ih =>
      rename_i s T env tailVars
      exact
        closed_smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
          s T env body
          (hWf s T (List.Mem.head _))
          (ih
            (by
              intro s' T' hMem
              exact hWf s' T' (List.Mem.tail _ hMem))
            hBodyTy)

private theorem smtx_model_eval_eo_to_smt_exists_eq_base_of_body_eval_eq
    {xs : Term} {vars : List EoVarKey} {except : List SmtVarKey}
    {M : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hInExcept :
      ∀ s T, (s, T) ∈ vars ->
        (s, __eo_to_smt_type T) ∈ except)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hBodyInvariant :
      ∀ {N : SmtModel},
        model_total_typed N ->
          model_agrees_except_on_env except [] N M ->
            __smtx_model_eval N body =
              __smtx_model_eval M body) :
  ∀ {N : SmtModel},
    model_total_typed N ->
            model_agrees_except_on_env except [] N M ->
        __smtx_model_eval N (__eo_to_smt_exists xs body) =
          __smtx_model_eval M body :=
by
  induction hEnv generalizing except M body with
  | nil =>
      intro N hN hAgree
      simpa [__eo_to_smt_exists] using hBodyInvariant hN hAgree
  | cons hTail ih =>
      rename_i s T env tailVars
      intro N hN hAgree
      let ST := __eo_to_smt_type T
      have hHeadWf : __smtx_type_wf ST = true :=
        hWf s T (List.Mem.head _)
      have hTailWf :
          ∀ s' T', (s', T') ∈ tailVars ->
            __smtx_type_wf (__eo_to_smt_type T') = true := by
        intro s' T' hMem
        exact hWf s' T' (List.Mem.tail _ hMem)
      have hTailInExcept :
          ∀ s' T', (s', T') ∈ tailVars ->
            (s', __eo_to_smt_type T') ∈ except := by
        intro s' T' hMem
        exact hInExcept s' T' (List.Mem.tail _ hMem)
      have hTailTy :
          __smtx_typeof (__eo_to_smt_exists env body) =
            SmtType.Bool :=
        smtx_typeof_eo_to_smt_exists_eq_bool_of_eo_var_env
          hTail hTailWf hBodyTy
      have hNTail :
          __smtx_model_eval N (__eo_to_smt_exists env body) =
            __smtx_model_eval M body :=
        ih hTailWf hTailInExcept hBodyTy hBodyInvariant hN hAgree
      have hTailConst :
          ∀ v : SmtValue,
            __smtx_typeof_value v = ST ->
              __smtx_value_canonical_bool v = true ->
                __smtx_model_eval
                    (native_model_push N s ST v)
                    (__eo_to_smt_exists env body) =
                  __smtx_model_eval N (__eo_to_smt_exists env body) := by
        intro v hvTy hvCan
        have hPushTotal :
            model_total_typed (native_model_push N s ST v) :=
          model_total_typed_push hN s ST v hHeadWf hvTy
            (by simpa [__smtx_value_canonical] using hvCan)
        have hPushAgree :
            model_agrees_except_on_env except []
              (native_model_push N s ST v) M :=
          model_agrees_except_on_env_push_left hAgree
            (by
              simpa [ST] using hInExcept s T (List.Mem.head _))
            (by simp)
        have hPushTail :
            __smtx_model_eval
                (native_model_push N s ST v)
                (__eo_to_smt_exists env body) =
              __smtx_model_eval M body :=
          ih hTailWf hTailInExcept hBodyTy hBodyInvariant
            hPushTotal hPushAgree
        exact hPushTail.trans hNTail.symm
      have hDrop :
          __smtx_model_eval N
              (SmtTerm.exists s ST (__eo_to_smt_exists env body)) =
            __smtx_model_eval N (__eo_to_smt_exists env body) :=
        smtx_model_eval_exists_eq_body_of_body_eval_eq
          N hN s ST (__eo_to_smt_exists env body)
          hHeadWf hTailTy hTailConst
      change
        __smtx_model_eval N
            (SmtTerm.exists s ST (__eo_to_smt_exists env body)) =
          __smtx_model_eval M body
      exact hDrop.trans hNTail

private theorem smtx_model_eval_not_not_eq_self_of_bool
    (M : SmtModel) (hM : model_total_typed M) (body : SmtTerm)
    (hBodyTy : __smtx_typeof body = SmtType.Bool) :
  __smtx_model_eval M (SmtTerm.not (SmtTerm.not body)) =
    __smtx_model_eval M body :=
by
  rcases smt_model_eval_bool_is_boolean M hM body hBodyTy with
    ⟨b, hEval⟩
  rw [hEval]
  cases b <;>
    simp [__smtx_model_eval, hEval, __smtx_model_eval_not,
      SmtEval.native_not]

private theorem smtx_model_eval_eo_to_smt_forall_encoding_eq_base_of_body_eval_eq
    {xs : Term} {vars : List EoVarKey} {except : List SmtVarKey}
    {M : SmtModel} {body : SmtTerm}
    (hEnv : EoVarEnv xs vars)
    (hM : model_total_typed M)
    (hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true)
    (hInExcept :
      ∀ s T, (s, T) ∈ vars ->
        (s, __eo_to_smt_type T) ∈ except)
    (hBodyTy : __smtx_typeof body = SmtType.Bool)
    (hBodyInvariant :
      ∀ {N : SmtModel},
        model_total_typed N ->
          model_agrees_except_on_env except [] N M ->
            __smtx_model_eval N body =
              __smtx_model_eval M body) :
  ∀ {N : SmtModel},
    model_total_typed N ->
      model_agrees_except_on_env except [] N M ->
        __smtx_model_eval N
            (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
          __smtx_model_eval M body :=
by
  intro N hN hAgree
  have hNotBodyTy :
      __smtx_typeof (SmtTerm.not body) = SmtType.Bool :=
    smtx_typeof_not_eq_bool_of_non_none body
      (by
        rw [typeof_not_eq, hBodyTy]
        simp [native_ite, native_Teq])
  have hNotInvariant :
      ∀ {N' : SmtModel},
        model_total_typed N' ->
          model_agrees_except_on_env except [] N' M ->
            __smtx_model_eval N' (SmtTerm.not body) =
              __smtx_model_eval M (SmtTerm.not body) := by
    intro N' hN' hAgree'
    exact smtx_model_eval_not_eq_of_eval_eq
      (hBodyInvariant hN' hAgree')
  have hExistsNot :
      __smtx_model_eval N (__eo_to_smt_exists xs (SmtTerm.not body)) =
        __smtx_model_eval M (SmtTerm.not body) :=
    smtx_model_eval_eo_to_smt_exists_eq_base_of_body_eval_eq
      hEnv hWf hInExcept hNotBodyTy hNotInvariant hN hAgree
  have hNotEval :
      __smtx_model_eval N
          (SmtTerm.not (__eo_to_smt_exists xs (SmtTerm.not body))) =
        __smtx_model_eval M (SmtTerm.not (SmtTerm.not body)) :=
    by
      simp [__smtx_model_eval, hExistsNot]
  exact hNotEval.trans
    (smtx_model_eval_not_not_eq_self_of_bool M hM body hBodyTy)

private theorem smtx_model_eval_qterm_eq_body_of_body_eval_eq
    {Q x F : Term} {vars : List EoVarKey} {except : List SmtVarKey}
    {M : SmtModel}
    (hQ : Q = Term.UOp UserOp.forall ∨ Q = Term.UOp UserOp.exists)
    (hTrans : RuleProofs.eo_has_smt_translation (qterm Q x F))
    (hEnv : EoVarEnv x vars)
    (hM : model_total_typed M)
    (hInExcept :
      ∀ s T, (s, T) ∈ vars ->
        (s, __eo_to_smt_type T) ∈ except)
    (hBodyInvariant :
      ∀ {N : SmtModel},
        model_total_typed N ->
          model_agrees_except_on_env except [] N M ->
            __smtx_model_eval N (__eo_to_smt F) =
              __smtx_model_eval M (__eo_to_smt F)) :
  ∀ {N : SmtModel},
    model_total_typed N ->
      model_agrees_except_on_env except [] N M ->
        __smtx_model_eval N (__eo_to_smt (qterm Q x F)) =
          __smtx_model_eval M (__eo_to_smt F) :=
by
  have hWf :
      ∀ s T, (s, T) ∈ vars ->
        __smtx_type_wf (__eo_to_smt_type T) = true :=
    quant_binder_types_wf hQ hTrans hEnv
  have hBodyTy :
      __smtx_typeof (__eo_to_smt F) = SmtType.Bool :=
    quant_body_has_bool_type hQ hTrans
  rcases hQ with hForall | hExists
  · subst Q
    cases hEnv with
    | nil =>
        intro N hN hAgree
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
    | cons hTail =>
        rename_i s T env tailVars
        intro N hN hAgree
        change
          __smtx_model_eval N
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) env)
                  (SmtTerm.not (__eo_to_smt F)))) =
            __smtx_model_eval M (__eo_to_smt F)
        exact
          smtx_model_eval_eo_to_smt_forall_encoding_eq_base_of_body_eval_eq
            (EoVarEnv.cons (s := s) (T := T) hTail) hM hWf
            hInExcept hBodyTy hBodyInvariant hN hAgree
  · subst Q
    cases hEnv with
    | nil =>
        intro N hN hAgree
        exact False.elim (hTrans (by
          change __smtx_typeof SmtTerm.None = SmtType.None
          exact TranslationProofs.smtx_typeof_none))
    | cons hTail =>
        rename_i s T env tailVars
        intro N hN hAgree
        change
          __smtx_model_eval N
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) env)
                (__eo_to_smt F)) =
            __smtx_model_eval M (__eo_to_smt F)
        exact
          smtx_model_eval_eo_to_smt_exists_eq_base_of_body_eval_eq
            (EoVarEnv.cons (s := s) (T := T) hTail) hWf
            hInExcept hBodyTy hBodyInvariant hN hAgree

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
  have hFTrans :
      RuleProofs.eo_has_smt_translation F :=
    quant_body_has_smt_translation hQ hLeftTrans
  rcases eo_var_env_of_quant_has_smt_translation hQ hLeftTrans with
    ⟨xVars, hXEnv⟩
  rcases
    eo_var_env_perm_of_get_unused_vars_of_quant_has_smt_translation
      hQ hLeftTrans hGTrans hNoFree with
    ⟨exceptVars, hExceptEnv⟩
  rcases get_unused_vars_branch_of_contains_false hNoFree with
    hSameBody | hSameQuant
  · rcases hSameBody with ⟨hG, hGet⟩
    subst G
    have hGetSet :
        __get_unused_vars ((Q.Apply x).Apply F) F =
          __eo_list_setof Term.__eo_List_cons x := by
      simpa [qterm] using hGet
    have hExceptSet :
        EoVarEnvPerm (__eo_list_setof Term.__eo_List_cons x) exceptVars := by
      simpa [hGetSet] using hExceptEnv
    have hInExcept :
        ∀ s T, (s, T) ∈ xVars ->
          (s, __eo_to_smt_type T) ∈
            exceptVars.map EoVarKey.toSmt := by
      intro s T hMem
      rcases EoVarEnv.setof_mem_of_mem hXEnv hMem with
        ⟨setVars, hSetEnv, hSetMem⟩
      have hExceptMem :
          (s, T) ∈ exceptVars :=
        EoVarEnvPerm.mem_of_exact_env_mem
          hExceptSet hSetEnv hSetMem
      exact List.mem_map.2
        ⟨(s, T), hExceptMem, by simp [EoVarKey.toSmt]⟩
    have hNoFreeSet :
        __contains_atomic_term_list_free_rec F
            (__eo_list_setof Term.__eo_List_cons x) Term.__eo_List_nil =
          Term.Boolean false := by
      simpa [hGet] using hNoFree
    have hBodyInvariant :
        ∀ {N : SmtModel},
          model_total_typed N ->
            model_agrees_except_on_env
                (exceptVars.map EoVarKey.toSmt) [] N M ->
              __smtx_model_eval N (__eo_to_smt F) =
                __smtx_model_eval M (__eo_to_smt F) := by
      sorry
    exact
      smtx_model_eval_qterm_eq_body_of_body_eval_eq
        hQ hLeftTrans hXEnv hM hInExcept hBodyInvariant
        hM
        (model_agrees_except_on_env_refl
          (exceptVars.map EoVarKey.toSmt) [] M)
  · rcases hSameQuant with ⟨y, hG, hMinclude, hGet⟩
    subst G
    have hNoFreeDiff :
        __contains_atomic_term_list_free_rec (qterm Q y F)
            (__eo_list_diff Term.__eo_List_cons
              (__eo_list_setof Term.__eo_List_cons x) y)
            Term.__eo_List_nil =
          Term.Boolean false := by
      simpa [hGet] using hNoFree
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
