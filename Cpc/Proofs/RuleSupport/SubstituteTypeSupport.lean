import Cpc.Proofs.Closed.Substitute
import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Translation.Apply
import Cpc.Proofs.Translation.Inversions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace SubstituteSupport

private abbrev consTerm (v vs : Term) : Term :=
  Term.Apply (Term.Apply Term.__eo_List_cons v) vs

/-- A mapped-substitution entry has the same EO type as the variable it replaces. -/
def SubstEntryPreservesTypes (xs ss : Term) : Prop :=
  ∀ (s : native_String) (T : Term),
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons xs
          (Term.Var (Term.String s) T)) = Term.Boolean false ->
      __eo_typeof
          (__assoc_nil_nth Term.__eo_List_cons ss
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T))) = T

/-- SMT type equality against a well-formed binder type recovers exact EO type equality. -/
theorem eo_typeof_eq_of_smt_type_eq
    (actual T : Term)
    (hActual : RuleProofs.eo_has_smt_translation actual)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hSmt :
      __smtx_typeof (__eo_to_smt actual) = __eo_to_smt_type T) :
    __eo_typeof actual = T := by
  have hActual' : eoHasSmtTranslation actual := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hActual
  have hMatch :
      __smtx_typeof (__eo_to_smt actual) =
        __eo_to_smt_type (__eo_typeof actual) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation actual hActual'
  have hEq :
      __eo_to_smt_type T = __eo_to_smt_type (__eo_typeof actual) :=
    hSmt.symm.trans hMatch
  by_cases hReg : T = Term.UOp UserOp.RegLan
  · subst T
    exact TranslationProofs.eo_to_smt_type_eq_reglan hEq.symm
  · have hValid :
        TranslationProofs.eo_type_valid_rec [] T := by
      have hTop : TranslationProofs.eo_type_valid T :=
        TranslationProofs.eo_type_valid_of_smt_wf T hWf
      cases T <;> simpa [TranslationProofs.eo_type_valid] using hTop
    exact (TranslationProofs.eo_to_smt_type_eq_of_valid hValid hEq).symm

/-- Per-entry SMT typing facts imply the generic EO type-preservation callback. -/
theorem substEntryPreservesTypes_of_smt_type_eq
    {xs ss : Term}
    (hEntryTrans :
      ∀ (s : native_String) (T : Term),
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T)) = Term.Boolean false ->
          RuleProofs.eo_has_smt_translation
            (__assoc_nil_nth Term.__eo_List_cons ss
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T))))
    (hEntryWf :
      ∀ (s : native_String) (T : Term),
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T)) = Term.Boolean false ->
          __smtx_type_wf (__eo_to_smt_type T) = true)
    (hEntrySmt :
      ∀ (s : native_String) (T : Term),
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T)) = Term.Boolean false ->
          __smtx_typeof
              (__eo_to_smt
                (__assoc_nil_nth Term.__eo_List_cons ss
                  (__eo_list_find Term.__eo_List_cons xs
                    (Term.Var (Term.String s) T)))) =
            __eo_to_smt_type T) :
    SubstEntryPreservesTypes xs ss := by
  intro s T hFind
  exact eo_typeof_eq_of_smt_type_eq
    (__assoc_nil_nth Term.__eo_List_cons ss
      (__eo_list_find Term.__eo_List_cons xs
        (Term.Var (Term.String s) T)))
    T
    (hEntryTrans s T hFind)
    (hEntryWf s T hFind)
    (hEntrySmt s T hFind)

theorem eo_requires_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck -> x = y := by
  intro h
  unfold __eo_requires at h
  by_cases hxy : native_teq x y = true
  · simpa [native_teq] using hxy
  · simp [hxy, native_ite] at h

theorem eo_requires_result_eq_of_ne_stuck {x y z : Term} :
    __eo_requires x y z ≠ Term.Stuck ->
      __eo_requires x y z = z := by
  intro h
  unfold __eo_requires at h ⊢
  by_cases hxy : native_teq x y = true
  · by_cases hx : native_teq x Term.Stuck = true
    · simp [hxy, hx, native_ite, SmtEval.native_not] at h
    · simp [hxy, hx, native_ite, SmtEval.native_not]
  · simp [hxy, native_ite] at h

theorem term_ne_stuck_of_typeof_ne_stuck {t : Term}
    (hTy : __eo_typeof t ≠ Term.Stuck) :
    t ≠ Term.Stuck := by
  intro h
  subst t
  exact hTy rfl

theorem eo_mk_apply_eq_apply_of_typeof_ne_stuck {f x : Term}
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  have hTerm : __eo_mk_apply f x ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_ne_stuck hTy
  cases f <;> cases x <;> simp [__eo_mk_apply] at hTerm ⊢

theorem eo_mk_apply_fun_ne_stuck_of_ne_stuck {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
      f ≠ Term.Stuck := by
  intro h hf
  subst f
  cases x <;> simp [__eo_mk_apply] at h

theorem eo_mk_apply_arg_ne_stuck_of_ne_stuck {f x : Term} :
    __eo_mk_apply f x ≠ Term.Stuck ->
      x ≠ Term.Stuck := by
  intro h hx
  subst x
  cases f <;> simp [__eo_mk_apply] at h

theorem eo_mk_apply_eq_apply_of_ne_stuck (f x : Term)
    (h : __eo_mk_apply f x ≠ Term.Stuck) :
    __eo_mk_apply f x = Term.Apply f x := by
  have hf := eo_mk_apply_fun_ne_stuck_of_ne_stuck h
  have hx := eo_mk_apply_arg_ne_stuck_of_ne_stuck h
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

theorem eo_mk_apply_ne_stuck_of_typeof_ne_stuck {f x : Term}
    (hTy : __eo_typeof (__eo_mk_apply f x) ≠ Term.Stuck) :
    __eo_mk_apply f x ≠ Term.Stuck := by
  intro hStuck
  apply hTy
  rw [hStuck]
  rfl

/-- A translated EO term list is never `Stuck`. -/
theorem eoListAllHaveSmtTranslation_ne_stuck {ts : Term}
    (hTs : EoListAllHaveSmtTranslation ts) :
    ts ≠ Term.Stuck := by
  intro h
  subst ts
  cases hTs

theorem eo_typeof_apply_eq_of_has_smt_translation
    (f x : Term)
    (hTransF : RuleProofs.eo_has_smt_translation f) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  cases f <;> try rfl
  case __eo_List_cons =>
    exfalso
    apply hTransF
    change __smtx_typeof SmtTerm.None = SmtType.None
    exact TranslationProofs.smtx_typeof_none
  case UOp op =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp1 op i =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case UOp2 op i j =>
    cases op <;> try rfl
    all_goals
      exfalso
      apply hTransF
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply,
          TranslationProofs.smtx_typeof_none]
    case UOp1 op i =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hTransF
        change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
          SmtType.None
        simp [__smtx_typeof, __smtx_typeof_apply,
          TranslationProofs.smtx_typeof_none]
    case FunType =>
      exfalso
      apply hTransF
      change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
        SmtType.None
      simp [__smtx_typeof, __smtx_typeof_apply,
        TranslationProofs.smtx_typeof_none]
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exfalso
          apply hTransF
          change
            __smtx_typeof
              (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt b))
                (__eo_to_smt a)) = SmtType.None
          simp [__smtx_typeof, __smtx_typeof_apply,
            TranslationProofs.smtx_typeof_none]

theorem eo_typeof_eo_var_env_eq_list
    {xs : Term} {vars : List EoVarKey}
    (hEnv : EoVarEnv xs vars) :
    __eo_typeof xs = Term.__eo_List := by
  induction hEnv with
  | nil => rfl
  | cons hTail ih =>
      exact TranslationProofs.eo_typeof_list_cons_var _ _ _ ih

theorem eo_typeof_forall_body_bool_of_ne_stuck {T U : Term}
    (hT : T = Term.__eo_List)
    (hTy : __eo_typeof_forall T U ≠ Term.Stuck) :
    U = Term.Bool := by
  subst T
  cases U <;> try rfl
  all_goals
    exfalso
    apply hTy
    simp [__eo_typeof_forall]

theorem eo_typeof_body_bool_of_quant_type_ne_stuck
    {q xs body : Term} {vars : List EoVarKey}
    (hQ : q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists)
    (hEnv : EoVarEnv xs vars)
    (hTy :
      __eo_typeof (Term.Apply (Term.Apply q xs) body) ≠ Term.Stuck) :
    __eo_typeof body = Term.Bool := by
  rcases hQ with rfl | rfl
  · change
      __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) ≠
        Term.Stuck at hTy
    exact eo_typeof_forall_body_bool_of_ne_stuck
      (eo_typeof_eo_var_env_eq_list hEnv) hTy
  · change
      __eo_typeof_forall (__eo_typeof xs) (__eo_typeof body) ≠
        Term.Stuck at hTy
    exact eo_typeof_forall_body_bool_of_ne_stuck
      (eo_typeof_eo_var_env_eq_list hEnv) hTy

theorem eo_typeof_apply_eq_of_head_arg_type_eq
    (f f' x x' : Term)
    (hFTrans : RuleProofs.eo_has_smt_translation f)
    (hF'Trans : RuleProofs.eo_has_smt_translation f')
    (hFType : __eo_typeof f' = __eo_typeof f)
    (hXType : __eo_typeof x' = __eo_typeof x) :
    __eo_typeof (Term.Apply f' x') =
      __eo_typeof (Term.Apply f x) := by
  rw [eo_typeof_apply_eq_of_has_smt_translation f' x' hF'Trans,
    eo_typeof_apply_eq_of_has_smt_translation f x hFTrans,
    hFType, hXType]

theorem substitute_simul_rec_apply_typeof_eq_of_typeof_ne_stuck
    (f a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q (consTerm v vs))
    (hFTrans : RuleProofs.eo_has_smt_translation f)
    (hFSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) f xs ss bvs))
    (hFType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false) f xs ss bvs) =
        __eo_typeof f)
    (hAType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
        __eo_typeof a)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply f a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply f a) xs ss bvs) =
      __eo_typeof (Term.Apply f a) := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply f a) xs ss bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) :=
    substitute_simul_rec_apply
      (Term.Boolean false) f a xs ss bvs
      hisr hxs hss hbvs hNotBinder
  rw [hSubstEq] at hTy ⊢
  have hMk :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
        Term.Apply
          (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) :=
    eo_mk_apply_eq_apply_of_typeof_ne_stuck hTy
  rw [hMk]
  exact
    eo_typeof_apply_eq_of_head_arg_type_eq
      f (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
      a (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)
      hFTrans hFSubTrans hFType hAType

/-- Quantifier-shaped substitution case: if the substituted quantifier has a
non-`Stuck` type, the capture-avoidance `requires` guard returned the rebuilt
quantified body. -/
theorem substitute_simul_quant_eq_of_typeof_ne_stuck
    (q v vs a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs) ≠
        Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q (consTerm v vs)) a)
        xs ss bvs =
      __eo_mk_apply
        (Term.Apply q (consTerm v vs))
        (__substitute_simul_rec (Term.Boolean false) a xs ss
          (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) := by
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) :=
    substFalse_quant q v vs a xs ss bvs hxs hss hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    apply hTy
    rw [hSubstEq, hReqStuck]
    rfl
  rw [hSubstEq]
  exact eo_requires_result_eq_of_ne_stuck hReqNe

theorem substitute_simul_quant_guard_false_of_typeof_ne_stuck
    (q v vs a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs) ≠
        Term.Stuck) :
    __contains_atomic_term_list_free_rec ss (consTerm v vs)
        Term.__eo_List_nil =
      Term.Boolean false := by
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) :=
    substFalse_quant q v vs a xs ss bvs hxs hss hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    apply hTy
    rw [hSubstEq, hReqStuck]
    rfl
  exact eo_requires_eq_of_ne_stuck hReqNe

theorem substitute_simul_quant_eq_of_ne_stuck
    (q v vs a xs ss bvs : Term)
    (hxs : xs ≠ Term.Stuck)
    (hss : ss ≠ Term.Stuck)
    (hbvs : bvs ≠ Term.Stuck)
    (hNe :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs ≠
        Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false)
        (Term.Apply (Term.Apply q (consTerm v vs)) a)
        xs ss bvs =
      __eo_mk_apply
        (Term.Apply q (consTerm v vs))
        (__substitute_simul_rec (Term.Boolean false) a xs ss
          (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) := by
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs =
        __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) :=
    substFalse_quant q v vs a xs ss bvs hxs hss hbvs
  have hReqNe :
      __eo_requires
          (__contains_atomic_term_list_free_rec ss (consTerm v vs)
            Term.__eo_List_nil)
          (Term.Boolean false)
          (__eo_mk_apply
            (Term.Apply q (consTerm v vs))
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) ≠
        Term.Stuck := by
    intro hReqStuck
    exact hNe (by rw [hSubstEq, hReqStuck])
  rw [hSubstEq]
  exact eo_requires_result_eq_of_ne_stuck hReqNe

theorem substitute_simul_quant_typeof_eq_of_typeof_ne_stuck
    (q v vs a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hQuantTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply q (consTerm v vs)) a))
    (hBodyType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false) a xs ss
            (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) =
        __eo_typeof a)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply q (consTerm v vs)) a)
          xs ss bvs) =
      __eo_typeof (Term.Apply (Term.Apply q (consTerm v vs)) a) := by
  have hSubstEq :=
    substitute_simul_quant_eq_of_typeof_ne_stuck
      q v vs a xs ss bvs hXsEnv hBvsEnv hSs hTy
  rw [hSubstEq] at hTy ⊢
  have hMk :
      __eo_mk_apply
          (Term.Apply q (consTerm v vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss
            (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) =
        Term.Apply
          (Term.Apply q (consTerm v vs))
          (__substitute_simul_rec (Term.Boolean false) a xs ss
            (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs)) :=
    eo_mk_apply_eq_apply_of_typeof_ne_stuck hTy
  rw [hMk]
  have hQuantTrans' :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply q (consTerm v vs)) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hQuantTrans
  have hQ :
      q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists :=
    is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
      hQuantTrans'
  rcases hQ with rfl | rfl
  · change
      __eo_typeof_forall (__eo_typeof (consTerm v vs))
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) =
        __eo_typeof_forall (__eo_typeof (consTerm v vs)) (__eo_typeof a)
    rw [hBodyType]
  · change
      __eo_typeof_forall (__eo_typeof (consTerm v vs))
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss
              (__eo_list_concat Term.__eo_List_cons (consTerm v vs) bvs))) =
        __eo_typeof_forall (__eo_typeof (consTerm v vs)) (__eo_typeof a)
    rw [hBodyType]

theorem substitute_simul_rec_atom_eq_self_of_ne_stuck
    (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hSubstNe :
      __substitute_simul_rec (Term.Boolean false) F xs ss bvs ≠ Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false) F xs ss bvs = F := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean false) F xs ss bvs =
        __eo_requires (__is_closed_rec F Term.__eo_List_nil)
          (Term.Boolean true) F :=
    substitute_simul_rec_atom
      (Term.Boolean false) F xs ss bvs
      hisr hxs hss hbvs hNotApply hNotVar hNotStuck
  rw [hHeadEq] at hSubstNe ⊢
  exact eo_requires_result_eq_of_ne_stuck hSubstNe

theorem substitute_simul_rec_atom_typeof_eq_of_typeof_ne_stuck
    (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ss bvs) =
      __eo_typeof F := by
  have hSubstNe :
      __substitute_simul_rec (Term.Boolean false) F xs ss bvs ≠
        Term.Stuck :=
    term_ne_stuck_of_typeof_ne_stuck hTy
  rw [substitute_simul_rec_atom_eq_self_of_ne_stuck
    F xs ss bvs hXsEnv hBvsEnv hSs
    hNotApply hNotVar hNotStuck hSubstNe]

theorem substitute_simul_rec_var_string_typeof_eq
    (s : native_String) (T xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hss : ss ≠ Term.Stuck)
    (hEntryTypes : SubstEntryPreservesTypes xs ss) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Var (Term.String s) T) xs ss bvs) = T := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  rcases hBvsEnv with ⟨bvExact, hBvExact, _hBvEquiv⟩
  by_cases hBound : (s, T) ∈ bvExact
  · have hb :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) T)) = Term.Boolean false :=
      hBvExact.find_neg_false_of_mem hBound
    rw [substitute_simul_rec_var_bound
      (Term.Boolean false) (Term.String s) T xs ss bvs
      hisr hxs hss hbvs hb]
    rfl
  · have hb :
        __eo_is_neg
            (__eo_list_find Term.__eo_List_cons bvs
              (Term.Var (Term.String s) T)) = Term.Boolean true :=
      hBvExact.find_neg_true_of_not_mem hBound
    rcases hXsEnv with ⟨xsExact, hXsExact, _hXsEquiv⟩
    by_cases hMapped : (s, T) ∈ xsExact
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T)) = Term.Boolean false :=
        hXsExact.find_neg_false_of_mem hMapped
      rw [substitute_simul_rec_var_mapped
        (Term.Boolean false) (Term.String s) T xs ss bvs
        hisr hxs hss hbvs hb hx]
      exact hEntryTypes s T hx
    · have hx :
          __eo_is_neg
              (__eo_list_find Term.__eo_List_cons xs
                (Term.Var (Term.String s) T)) = Term.Boolean true :=
        hXsExact.find_neg_true_of_not_mem hMapped
      rw [substitute_simul_rec_var_unmapped
        (Term.Boolean false) (Term.String s) T xs ss bvs
        hisr hxs hss hbvs hb hx]
      rfl

theorem substitute_simul_rec_uop_eq_self
    (op : UserOp) (xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss) :
    __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ss bvs =
      Term.UOp op := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ss bvs =
        __eo_requires
          (__is_closed_rec (Term.UOp op) Term.__eo_List_nil)
          (Term.Boolean true) (Term.UOp op) :=
    substitute_simul_rec_atom
      (Term.Boolean false) (Term.UOp op) xs ss bvs
      hisr hxs hss hbvs
      (by intro f a h; cases h)
      (by intro s S h; cases h)
      (by intro h; cases h)
  rw [hHeadEq]
  simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]

theorem substitute_simul_rec_uop1_eq_self
    (op : UserOp1) (idx xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss) :
    __substitute_simul_rec (Term.Boolean false) (Term.UOp1 op idx) xs ss bvs =
      Term.UOp1 op idx := by
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean false) (Term.UOp1 op idx) xs ss bvs =
        __eo_requires
          (__is_closed_rec (Term.UOp1 op idx) Term.__eo_List_nil)
          (Term.Boolean true) (Term.UOp1 op idx) :=
    substitute_simul_rec_atom
      (Term.Boolean false) (Term.UOp1 op idx) xs ss bvs
      hisr hxs hss hbvs
      (by intro f a h; cases h)
      (by intro s S h; cases h)
      (by intro h; cases h)
  rw [hHeadEq]
  simp [__is_closed_rec, __eo_requires, native_ite, native_teq,
    native_not, SmtEval.native_not]

end SubstituteSupport
