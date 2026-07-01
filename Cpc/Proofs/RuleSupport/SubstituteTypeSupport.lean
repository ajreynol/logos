import Cpc.Proofs.Closed.Substitute
import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Translation.Full
import Cpc.Proofs.Translation.Inversions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

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

/-- A variable whose name is not an EO string cannot have an SMT translation. -/
theorem false_of_non_string_var_has_smt_translation
    {name S : Term} {P : Prop}
    (hName : ∀ s, name ≠ Term.String s)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Var name S)) :
    P := by
  exfalso
  apply hTrans
  cases name <;>
    try
      (change __smtx_typeof SmtTerm.None = SmtType.None
       exact TranslationProofs.smtx_typeof_none)
  case String s =>
    exact False.elim (hName s rfl)

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

private theorem eq_of_eo_eq_true (x y : Term)
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

private theorem eo_to_smt_type_eq_of_top_valid
    {T U : Term}
    (hValid : TranslationProofs.eo_type_valid T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  cases T
  case UOp op =>
    cases op
    case RegLan =>
      have hUReg : __eo_to_smt_type U = SmtType.RegLan := by
        simpa [__eo_to_smt_type] using hEq.symm
      exact (TranslationProofs.eo_to_smt_type_eq_reglan hUReg).symm
    all_goals
      exact
        TranslationProofs.eo_to_smt_type_eq_of_valid
          (by simpa [TranslationProofs.eo_type_valid] using hValid) hEq
  all_goals
    exact
      TranslationProofs.eo_to_smt_type_eq_of_valid
        (by simpa [TranslationProofs.eo_type_valid] using hValid) hEq

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

theorem eo_typeof_apply_arg_ne_stuck {F X : Term} :
    __eo_typeof_apply F X ≠ Term.Stuck ->
      X ≠ Term.Stuck := by
  intro h hX
  subst X
  cases F <;> simp [__eo_typeof_apply] at h

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

theorem apply_generic_args_have_smt_translation_of_has_smt_translation
    (f a : Term)
    (hTranslate :
      __eo_to_smt (Term.Apply f a) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a))
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply f a)) :
    RuleProofs.eo_has_smt_translation f ∧
      RuleProofs.eo_has_smt_translation a := by
  have hTrans' : eoHasSmtTranslation (Term.Apply f a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt a)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans'
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hFTrans, hATrans⟩
  constructor
  · simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hFTrans
  · simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hATrans

theorem var_apply_generic_smt_type (name T a : Term) :
    __smtx_typeof
        (SmtTerm.Apply (__eo_to_smt (Term.Var name T)) (__eo_to_smt a)) =
      __smtx_typeof_apply
        (__smtx_typeof (__eo_to_smt (Term.Var name T)))
        (__smtx_typeof (__eo_to_smt a)) := by
  cases name <;> try
    (change
      __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt a)) =
        __smtx_typeof_apply (__smtx_typeof SmtTerm.None)
          (__smtx_typeof (__eo_to_smt a))
     rw [__smtx_typeof.eq_def])
  case String s =>
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T))
            (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)))
          (__smtx_typeof (__eo_to_smt a))
    rw [__smtx_typeof.eq_def]

theorem dtcons_reserved_false_of_apply_has_smt_translation
    {s : native_String} {d : Datatype} {i : native_Nat} {a : Term}
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.DtCons s d i) a)) :
    native_reserved_datatype_name s = false := by
  unfold RuleProofs.eo_has_smt_translation at hTrans
  change
    __smtx_typeof
        (SmtTerm.Apply
          (native_ite (native_reserved_datatype_name s) SmtTerm.None
            (SmtTerm.DtCons s (__eo_to_smt_datatype d) i))
          (__eo_to_smt a)) ≠
      SmtType.None at hTrans
  cases hReserved : native_reserved_datatype_name s
  · rfl
  · exfalso
    rw [hReserved] at hTrans
    exact hTrans (by
      simpa [native_ite] using
        TranslationProofs.typeof_apply_none_eq (__eo_to_smt a))

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

theorem substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
    (f a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q (consTerm v vs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply f a) xs ss bvs) ≠
        Term.Stuck) :
    __substitute_simul_rec (Term.Boolean false) f xs ss bvs ≠
      Term.Stuck := by
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
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply
            (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  exact
    eo_mk_apply_fun_ne_stuck_of_ne_stuck
      (eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk)

theorem substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
    (f a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        f ≠ Term.Apply q (consTerm v vs))
    (hFSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) f xs ss bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply f a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
      Term.Stuck := by
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
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply
            (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) ≠
        Term.Stuck := by
    intro hStuck
    exact hTy (by rw [hSubstEq, hStuck])
  have hMk :
      __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
        Term.Apply
          (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) :=
    eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
  have hApplyTy :
      __eo_typeof
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) ≠
        Term.Stuck := by
    intro hStuck
    exact hTyMk (by rw [hMk, hStuck])
  have hApplyEq :
      __eo_typeof
          (Term.Apply
            (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) =
        __eo_typeof_apply
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean false) f xs ss bvs))
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) :=
    eo_typeof_apply_eq_of_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) f xs ss bvs)
      (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)
      hFSubTrans
  have hApplyTy' :
      __eo_typeof_apply
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean false) f xs ss bvs))
          (__eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs)) ≠
        Term.Stuck := by
    intro hStuck
    exact hApplyTy (by rw [hApplyEq, hStuck])
  exact eo_typeof_apply_arg_ne_stuck hApplyTy'

theorem eo_typeof_ne_stuck_of_has_smt_translation
    (t : Term)
    (hTrans : RuleProofs.eo_has_smt_translation t) :
    __eo_typeof t ≠ Term.Stuck := by
  have hTrans' : eoHasSmtTranslation t := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hTrans
  intro hTy
  have hMatch :
      __smtx_typeof (__eo_to_smt t) =
        __eo_to_smt_type (__eo_typeof t) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTrans'
  exact hTrans' (by
    rw [hMatch, hTy]
    rfl)

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

theorem substitute_simul_rec_atom_has_smt_translation_of_ne_stuck
    (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hNe :
      __substitute_simul_rec (Term.Boolean false) F xs ss bvs ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false) F xs ss bvs) := by
  rw [substitute_simul_rec_atom_eq_self_of_ne_stuck
    F xs ss bvs hXsEnv hBvsEnv hSs
    hNotApply hNotVar hNotStuck hNe]
  exact hFTrans

theorem substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
    (F a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hNotBinder :
      ∀ q v vs,
        F ≠ Term.Apply q (consTerm v vs))
    (hTranslate :
      __eo_to_smt (Term.Apply F a) =
        SmtTerm.Apply (__eo_to_smt F) (__eo_to_smt a))
    (hGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt F) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt F))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply F a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply F a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply F a) xs ss bvs) =
      __eo_typeof (Term.Apply F a) := by
  have hArgs :=
    apply_generic_args_have_smt_translation_of_has_smt_translation
      F a hTranslate hGeneric hTrans
  have hFTrans : RuleProofs.eo_has_smt_translation F := hArgs.1
  have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean false) F xs ss bvs ≠
        Term.Stuck :=
    substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
      F a xs ss bvs hXsEnv hBvsEnv hSs hNotBinder hTy
  have hHeadSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) F xs ss bvs) :=
    substitute_simul_rec_atom_has_smt_translation_of_ne_stuck
      F xs ss bvs hXsEnv hBvsEnv hSs hNotApply hNotVar hNotStuck
      hFTrans hHeadNe
  have hHeadType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false) F xs ss bvs) =
        __eo_typeof F :=
    substitute_simul_rec_atom_typeof_eq_of_typeof_ne_stuck
      F xs ss bvs hXsEnv hBvsEnv hSs hNotApply hNotVar hNotStuck
      (eo_typeof_ne_stuck_of_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) F xs ss bvs)
        hHeadSubTrans)
  have hATy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
        Term.Stuck :=
    substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
      F a xs ss bvs hXsEnv hBvsEnv hSs hNotBinder hHeadSubTrans hTy
  exact
    substitute_simul_rec_apply_typeof_eq_of_typeof_ne_stuck
      F a xs ss bvs hXsEnv hBvsEnv hSs hNotBinder hFTrans
      hHeadSubTrans hHeadType (hARec hATrans hATy) hTy

theorem substitute_simul_rec_apply_atom_generic_typeof_eq_of_typeof_ne_stuck
    (F a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotApply : ∀ f a, F ≠ Term.Apply f a)
    (hNotVar : ∀ s S, F ≠ Term.Var s S)
    (hNotStuck : F ≠ Term.Stuck)
    (hNotBinder :
      ∀ q v vs,
        F ≠ Term.Apply q (consTerm v vs))
    (hTranslate :
      __eo_to_smt (Term.Apply F a) =
        SmtTerm.Apply (__eo_to_smt F) (__eo_to_smt a))
    (hNoSel :
      ∀ s d i j,
        __eo_to_smt F ≠ SmtTerm.DtSel s d i j)
    (hNoTester :
      ∀ s d i,
        __eo_to_smt F ≠ SmtTerm.DtTester s d i)
    (hTrans : RuleProofs.eo_has_smt_translation (Term.Apply F a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply F a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply F a) xs ss bvs) =
      __eo_typeof (Term.Apply F a) := by
  exact
    substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
      F a xs ss bvs hXsEnv hBvsEnv hSs hNotApply hNotVar hNotStuck
      hNotBinder hTranslate
      (generic_apply_type_of_non_special_head_closed
        (__eo_to_smt F) (__eo_to_smt a) hNoSel hNoTester)
      hTrans hARec hTy

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

theorem substitute_simul_rec_var_any_typeof_eq
    (name T xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hEntryTypes : SubstEntryPreservesTypes xs ss)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name T)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Var name T) xs ss bvs) =
      __eo_typeof (Term.Var name T) := by
  by_cases hString : ∃ s, name = Term.String s
  · rcases hString with ⟨s, rfl⟩
    exact
      substitute_simul_rec_var_string_typeof_eq
        s T xs ss bvs hXsEnv hBvsEnv
        (eoListAllHaveSmtTranslation_ne_stuck hSs) hEntryTypes
  · exact
      false_of_non_string_var_has_smt_translation
        (fun s hEq => hString ⟨s, hEq⟩) hVarTrans

theorem substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
    (name T xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name T))
    (hNe :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Var name T) xs ss bvs ≠
        Term.Stuck) :
    RuleProofs.eo_has_smt_translation
      (__substitute_simul_rec (Term.Boolean false)
        (Term.Var name T) xs ss bvs) := by
  by_cases hString : ∃ s, name = Term.String s
  · rcases hString with ⟨s, rfl⟩
    have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
    have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
    have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
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
      exact hVarTrans
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
        have hSubstEq :
            __substitute_simul_rec (Term.Boolean false)
                (Term.Var (Term.String s) T) xs ss bvs =
              __assoc_nil_nth Term.__eo_List_cons ss
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) :=
          substitute_simul_rec_var_mapped
            (Term.Boolean false) (Term.String s) T xs ss bvs
            hisr hxs hss hbvs hb hx
        have hEntryNe :
            __assoc_nil_nth Term.__eo_List_cons ss
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) ≠
              Term.Stuck := by
          rwa [hSubstEq] at hNe
        have hEntryTrans :
            eoHasSmtTranslation
              (__assoc_nil_nth Term.__eo_List_cons ss
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T))) :=
          assoc_nil_nth_has_smt_translation_of_list_all_and_ne_stuck
            ss
            (__eo_list_find Term.__eo_List_cons xs
              (Term.Var (Term.String s) T))
            hSs hEntryNe
        simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
          hSubstEq] using hEntryTrans
      · have hx :
            __eo_is_neg
                (__eo_list_find Term.__eo_List_cons xs
                  (Term.Var (Term.String s) T)) = Term.Boolean true :=
          hXsExact.find_neg_true_of_not_mem hMapped
        rw [substitute_simul_rec_var_unmapped
          (Term.Boolean false) (Term.String s) T xs ss bvs
          hisr hxs hss hbvs hb hx]
        exact hVarTrans
  · exact
      false_of_non_string_var_has_smt_translation
        (fun s hEq => hString ⟨s, hEq⟩) hVarTrans

theorem substitute_simul_rec_apply_var_typeof_eq_of_typeof_ne_stuck
    (name T a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hEntryTypes : SubstEntryPreservesTypes xs ss)
    (hNotBinder :
      ∀ q v vs,
        Term.Var name T ≠ Term.Apply q (consTerm v vs))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Var name T) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Var name T)) (__eo_to_smt a))
    (hGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Var name T)) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Var name T)))
          (__smtx_typeof (__eo_to_smt a)))
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Var name T) a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Var name T) a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Var name T) a) xs ss bvs) =
      __eo_typeof (Term.Apply (Term.Var name T) a) := by
  have hArgs :=
    apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Var name T) a hTranslate hGeneric hTrans
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Var name T) := hArgs.1
  have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Var name T) xs ss bvs ≠
        Term.Stuck :=
    substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
      (Term.Var name T) a xs ss bvs hXsEnv hBvsEnv hSs
      hNotBinder hTy
  have hHeadSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Var name T) xs ss bvs) :=
    substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
      name T xs ss bvs hXsEnv hBvsEnv hSs hHeadTrans hHeadNe
  have hHeadType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Var name T) xs ss bvs) =
        __eo_typeof (Term.Var name T) :=
    substitute_simul_rec_var_any_typeof_eq
      name T xs ss bvs hXsEnv hBvsEnv hSs hEntryTypes hHeadTrans
  have hATy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
        Term.Stuck :=
    substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
      (Term.Var name T) a xs ss bvs hXsEnv hBvsEnv hSs
      hNotBinder hHeadSubTrans hTy
  exact
    substitute_simul_rec_apply_typeof_eq_of_typeof_ne_stuck
      (Term.Var name T) a xs ss bvs hXsEnv hBvsEnv hSs
      hNotBinder hHeadTrans hHeadSubTrans hHeadType
      (hARec hATrans hATy) hTy

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

theorem substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
    (op : UserOp) (a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        Term.UOp op ≠ Term.Apply q (consTerm v vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp op) a))
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) a) ->
        eoHasSmtTranslation a)
    (hArgTyNe :
      ∀ X,
        __eo_typeof (Term.Apply (Term.UOp op) X) ≠ Term.Stuck ->
          __eo_typeof X ≠ Term.Stuck)
    (hTypeCong :
      ∀ X Y,
        __eo_typeof X = __eo_typeof Y ->
          __eo_typeof (Term.Apply (Term.UOp op) X) =
            __eo_typeof (Term.Apply (Term.UOp op) Y))
    (hRecArg :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ss bvs) =
      __eo_typeof (Term.Apply (Term.UOp op) a) := by
  let aSub := __substitute_simul_rec (Term.Boolean false) a xs ss bvs
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.UOp op) xs ss bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ss bvs hXsEnv hBvsEnv hSs
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ss bvs =
        __eo_mk_apply (Term.UOp op) aSub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean false) (Term.UOp op) a xs ss bvs
        hisr hxs hss hbvs hNotBinder
    simpa [aSub, hHeadSub] using hApplyEq
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.UOp op) aSub) ≠ Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hMk :
      __eo_mk_apply (Term.UOp op) aSub =
        Term.Apply (Term.UOp op) aSub :=
    eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
  have hTyApply :
      __eo_typeof (Term.Apply (Term.UOp op) aSub) ≠ Term.Stuck := by
    rwa [hMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  have hATrans :
      RuleProofs.eo_has_smt_translation a := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hArgExtract hFTransEo
  have hAType :
      __eo_typeof aSub = __eo_typeof a :=
    hRecArg hATrans (hArgTyNe aSub hTyApply)
  rw [hSubstEq, hMk]
  exact hTypeCong aSub a hAType

theorem substitute_simul_unary_op_typeof_eq_via_type_fn
    (op : UserOp) (typeFn : Term -> Term) (a xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        Term.UOp op ≠ Term.Apply q (consTerm v vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp op) a))
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) a) ->
        eoHasSmtTranslation a)
    (hTypeFn :
      ∀ X,
        __eo_typeof (Term.Apply (Term.UOp op) X) =
          typeFn (__eo_typeof X))
    (hTypeFnStuck : typeFn Term.Stuck = Term.Stuck)
    (hRecArg :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ss bvs) =
          __eo_typeof a)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ss bvs) =
      __eo_typeof (Term.Apply (Term.UOp op) a) :=
  substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
    op a xs ss bvs hXsEnv hBvsEnv hSs hNotBinder hFTrans
    hArgExtract
    (fun X hApp hX => by
      rw [hTypeFn X, hX, hTypeFnStuck] at hApp
      exact hApp rfl)
    (fun X Y hXY => by
      rw [hTypeFn X, hTypeFn Y, hXY])
    hRecArg hTy

theorem substitute_simul_binary_op_typeof_eq_of_typeof_ne_stuck
    (op : UserOp) (x y xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠ Term.Apply q (consTerm v vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hArgTyNe :
      ∀ X Y,
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) ≠
          Term.Stuck ->
        __eo_typeof X ≠ Term.Stuck ∧ __eo_typeof Y ≠ Term.Stuck)
    (hTypeCong :
      ∀ X₁ Y₁ X₂ Y₂,
        __eo_typeof X₁ = __eo_typeof Y₁ ->
        __eo_typeof X₂ = __eo_typeof Y₂ ->
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X₁) X₂) =
          __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) Y₁) Y₂))
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) x xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) x xs ss bvs) =
          __eo_typeof x)
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) y xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) y xs ss bvs) =
          __eo_typeof y)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ss bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) := by
  let xSub := __substitute_simul_rec (Term.Boolean false) x xs ss bvs
  let ySub := __substitute_simul_rec (Term.Boolean false) y xs ss bvs
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.UOp op) xs ss bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ss bvs hXsEnv hBvsEnv hSs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) x) xs ss bvs =
        __eo_mk_apply (Term.UOp op) xSub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean false) (Term.UOp op) x xs ss bvs
        hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ss bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean false) (Term.Apply (Term.UOp op) x) y xs ss bvs
        hisr hxs hss hbvs hNotBinder
    simpa [ySub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub ≠
        Term.Stuck :=
    eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp op) xSub ≠ Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp op) xSub =
        Term.Apply (Term.UOp op) xSub :=
    eo_mk_apply_eq_apply_of_ne_stuck (Term.UOp op) xSub hInnerNe
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp op) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp op) xSub) ySub :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp op) xSub) ySub (by
      rw [← hInnerMk]
      exact hOuterNe)
  have hTyApply :
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  rcases hArgExtract hFTransEo with ⟨hXTransEo, hYTransEo⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hXTransEo
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hYTransEo
  rcases hArgTyNe xSub ySub hTyApply with ⟨hXSubTy, hYSubTy⟩
  have hXTy : __eo_typeof xSub = __eo_typeof x :=
    hRecX hXTrans hXSubTy
  have hYTy : __eo_typeof ySub = __eo_typeof y :=
    hRecY hYTrans hYSubTy
  rw [hSubstEq, hInnerMk, hOuterMk]
  exact hTypeCong xSub x ySub y hXTy hYTy

theorem substitute_simul_binary_op_typeof_eq_via_type_fn
    (op : UserOp) (typeFn : Term -> Term -> Term) (x y xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠ Term.Apply q (consTerm v vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hTypeFn :
      ∀ X Y,
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) =
          typeFn (__eo_typeof X) (__eo_typeof Y))
    (hTypeFnStuckLeft : ∀ Y, typeFn Term.Stuck Y = Term.Stuck)
    (hTypeFnStuckRight : ∀ X, typeFn X Term.Stuck = Term.Stuck)
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) x xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) x xs ss bvs) =
          __eo_typeof x)
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) y xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) y xs ss bvs) =
          __eo_typeof y)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ss bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) :=
  substitute_simul_binary_op_typeof_eq_of_typeof_ne_stuck
    op x y xs ss bvs hXsEnv hBvsEnv hSs hNotBinder hFTrans
    hArgExtract
    (fun X Y hApp => by
      constructor
      · intro hX
        rw [hTypeFn X Y, hX, hTypeFnStuckLeft] at hApp
        exact hApp rfl
      · intro hY
        rw [hTypeFn X Y, hY, hTypeFnStuckRight] at hApp
        exact hApp rfl)
    (fun X₁ Y₁ X₂ Y₂ hX hY => by
      rw [hTypeFn X₁ X₂, hTypeFn Y₁ Y₂, hX, hY])
    hRecX hRecY hTy

theorem eo_typeof_div_stuck_left (Y : Term) :
    __eo_typeof_div Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_div_stuck_right (X : Term) :
    __eo_typeof_div X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case UOp op =>
    cases op <;> rfl

theorem eo_typeof_divisible_stuck_left (Y : Term) :
    __eo_typeof_divisible Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_divisible_stuck_right (X : Term) :
    __eo_typeof_divisible X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case UOp op =>
    cases op <;> rfl

theorem eo_typeof_select_stuck_left (Y : Term) :
    __eo_typeof_select Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_select_stuck_right (X : Term) :
    __eo_typeof_select X Term.Stuck = Term.Stuck := by
  rfl

theorem eo_typeof_qdiv_stuck_left (Y : Term) :
    __eo_typeof_qdiv Term.Stuck Y = Term.Stuck := by
  rfl

theorem eo_typeof_qdiv_stuck_right (X : Term) :
    __eo_typeof_qdiv X Term.Stuck = Term.Stuck := by
  cases X <;> rfl

theorem eo_typeof_tuple_stuck_left (Y : Term) :
    __eo_typeof_tuple Term.Stuck Y = Term.Stuck := by
  rfl

theorem eo_typeof_tuple_stuck_right (X : Term) :
    __eo_typeof_tuple X Term.Stuck = Term.Stuck := by
  cases X <;> rfl

theorem eo_typeof_array_deq_diff_stuck_left (Y : Term) :
    __eo_typeof__at_array_deq_diff Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_array_deq_diff_stuck_right (X : Term) :
    __eo_typeof__at_array_deq_diff X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case Apply g b =>
      cases g <;> try rfl
      case UOp op =>
        cases op <;> rfl

theorem eo_typeof_strings_deq_diff_stuck_left (Y : Term) :
    __eo_typeof__at_strings_deq_diff Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_strings_deq_diff_stuck_right (X : Term) :
    __eo_typeof__at_strings_deq_diff X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

theorem eo_typeof_strings_stoi_result_stuck_left (Y : Term) :
    __eo_typeof__at_strings_stoi_result Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_strings_stoi_result_stuck_right (X : Term) :
    __eo_typeof__at_strings_stoi_result X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      case Seq =>
        cases a <;> try rfl
        case UOp op =>
          cases op <;> rfl

theorem eo_typeof_sets_deq_diff_stuck_left (Y : Term) :
    __eo_typeof__at_sets_deq_diff Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_sets_deq_diff_stuck_right (X : Term) :
    __eo_typeof__at_sets_deq_diff X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

theorem eo_typeof_concat_stuck_left (Y : Term) :
    __eo_typeof_concat Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_concat_stuck_right (X : Term) :
    __eo_typeof_concat X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

theorem eo_typeof_bvand_stuck_left (Y : Term) :
    __eo_typeof_bvand Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_bvand_stuck_right (X : Term) :
    __eo_typeof_bvand X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

theorem eo_typeof_bvcomp_stuck_left (Y : Term) :
    __eo_typeof_bvcomp Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_bvcomp_stuck_right (X : Term) :
    __eo_typeof_bvcomp X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

theorem eo_typeof_bvult_stuck_left (Y : Term) :
    __eo_typeof_bvult Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_bvult_stuck_right (X : Term) :
    __eo_typeof_bvult X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

theorem eo_typeof_from_bools_stuck_left (Y : Term) :
    __eo_typeof__at_from_bools Term.Stuck Y = Term.Stuck := by
  cases Y <;> rfl

theorem eo_typeof_from_bools_stuck_right (X : Term) :
    __eo_typeof__at_from_bools X Term.Stuck = Term.Stuck := by
  cases X <;> rfl

theorem eo_typeof_set_insert_stuck_right (X : Term) :
    __eo_typeof_set_insert X Term.Stuck = Term.Stuck := by
  cases X <;> try rfl
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> rfl

theorem eo_typeof_set_insert_eq_set_of_base_set
    (L T : Term)
    (hNN :
      __eo_typeof_set_insert L (Term.Apply (Term.UOp UserOp.Set) T) ≠
        Term.Stuck) :
    __eo_typeof_set_insert L (Term.Apply (Term.UOp UserOp.Set) T) =
      Term.Apply (Term.UOp UserOp.Set) T := by
  cases L <;> try (exfalso; apply hNN; rfl)
  case Apply f U =>
    cases f <;> try (exfalso; apply hNN; rfl)
    case UOp op =>
      cases op <;> try (exfalso; apply hNN; rfl)
      case _at__at_TypedList =>
        have hReqNN :
            __eo_requires (__eo_eq U T) (Term.Boolean true)
                (Term.Apply (Term.UOp UserOp.Set) U) ≠
              Term.Stuck := by
          simpa [__eo_typeof_set_insert] using hNN
        have hGuard : __eo_eq U T = Term.Boolean true :=
          eo_requires_eq_of_ne_stuck hReqNN
        have hTU : T = U := eq_of_eo_eq_true U T hGuard
        change
          __eo_requires (__eo_eq U T) (Term.Boolean true)
              (Term.Apply (Term.UOp UserOp.Set) U) =
            Term.Apply (Term.UOp UserOp.Set) T
        rw [eo_requires_result_eq_of_ne_stuck hReqNN]
        rw [hTU]

theorem substitute_simul_set_insert_typeof_eq_of_typeof_ne_stuck
    (typedList base xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.set_insert) typedList ≠
          Term.Apply q (consTerm v vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
          base))
    (hRecBase :
      RuleProofs.eo_has_smt_translation base ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) base xs ss bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) base xs ss bvs) =
          __eo_typeof base)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base)
          xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base)
          xs ss bvs) =
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
          base) := by
  let typedListSub :=
    __substitute_simul_rec (Term.Boolean false) typedList xs ss bvs
  let baseSub :=
    __substitute_simul_rec (Term.Boolean false) base xs ss bvs
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hss : ss ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hSs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.UOp UserOp.set_insert) xs ss bvs =
        Term.UOp UserOp.set_insert :=
    substitute_simul_rec_uop_eq_self
      UserOp.set_insert xs ss bvs hXsEnv hBvsEnv hSs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp UserOp.set_insert) typedList) xs ss bvs =
        __eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean false) (Term.UOp UserOp.set_insert) typedList
        xs ss bvs hisr hxs hss hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [typedListSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base) xs ss bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub := by
    have hApplyEq :=
      substitute_simul_rec_apply
        (Term.Boolean false)
        (Term.Apply (Term.UOp UserOp.set_insert) typedList)
        base xs ss bvs hisr hxs hss hbvs hNotBinder
    simpa [baseSub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply
            (__eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub)
            baseSub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub ≠
        Term.Stuck :=
    eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub ≠
        Term.Stuck :=
    eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub =
        Term.Apply (Term.UOp UserOp.set_insert) typedListSub :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.set_insert) typedListSub hInnerNe
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub :=
    eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.set_insert) typedListSub) baseSub
      (by
        rw [← hInnerMk]
        exact hOuterNe)
  have hTyApply :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
            baseSub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hFTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
          base) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  have hSetNN :
      __smtx_typeof
          (__eo_to_smt_set_insert typedList (__eo_to_smt base)) ≠
        SmtType.None := by
    have h := hFTransEo
    unfold eoHasSmtTranslation at h
    change
      __smtx_typeof
          (__eo_to_smt_set_insert typedList (__eo_to_smt base)) ≠
        SmtType.None at h
    exact h
  rcases eo_to_smt_set_insert_shape_of_non_none
      typedList (__eo_to_smt base) hSetNN with
    ⟨A, _hSetSmt, hBaseSmt, hElem, hANN⟩
  have hBaseTransEo : eoHasSmtTranslation base := by
    unfold eoHasSmtTranslation
    rw [hBaseSmt]
    simp
  have hBaseTrans : RuleProofs.eo_has_smt_translation base := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hBaseTransEo
  rcases
      TranslationProofs.eo_typeof_eq_set_of_smt_set_from_ih
        base
        (fun _ =>
          TranslationProofs.eo_to_smt_typeof_matches_translation
            base hBaseTransEo)
        hBaseSmt with
    ⟨T, hBaseType, hTToA⟩
  have hElemNN :
      __eo_to_smt_typed_list_elem_type typedList ≠ SmtType.None := by
    rw [hElem]
    exact hANN
  rcases
      TranslationProofs.eo_to_smt_typed_list_elem_type_of_non_none
        typedList hElemNN with
    ⟨U, hTypedListType, hUToElem, hUValid⟩
  have hUToA : __eo_to_smt_type U = A := by
    rw [hUToElem, hElem]
  have hUT : U = T :=
    eo_to_smt_type_eq_of_top_valid hUValid (hUToA.trans hTToA.symm)
  have hTValid : TranslationProofs.eo_type_valid T := by
    rwa [← hUT]
  have hTNe : T ≠ Term.Stuck :=
    TranslationProofs.eo_type_valid_not_stuck hTValid
  have hOrigSetType :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base) =
        Term.Apply (Term.UOp UserOp.Set) T := by
    change
      __eo_typeof_set_insert (__eo_typeof typedList) (__eo_typeof base) =
        Term.Apply (Term.UOp UserOp.Set) T
    rw [hTypedListType, hBaseType, hUT]
    simp [__eo_typeof_set_insert, __eo_requires, __eo_eq,
      native_ite, native_teq, SmtEval.native_not]
  have hBaseSubTyNe :
      __eo_typeof baseSub ≠ Term.Stuck := by
    intro hBaseStuck
    apply hTyApply
    change
      __eo_typeof_set_insert (__eo_typeof typedListSub)
          (__eo_typeof baseSub) =
        Term.Stuck
    rw [hBaseStuck]
    exact eo_typeof_set_insert_stuck_right (__eo_typeof typedListSub)
  have hBaseSubTy :
      __eo_typeof baseSub = __eo_typeof base :=
    hRecBase hBaseTrans hBaseSubTyNe
  have hBaseSubType :
      __eo_typeof baseSub = Term.Apply (Term.UOp UserOp.Set) T := by
    rw [hBaseSubTy, hBaseType]
  have hSubSetType :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
            baseSub) =
        Term.Apply (Term.UOp UserOp.Set) T := by
    change
      __eo_typeof_set_insert (__eo_typeof typedListSub)
          (__eo_typeof baseSub) =
        Term.Apply (Term.UOp UserOp.Set) T
    rw [hBaseSubType]
    apply eo_typeof_set_insert_eq_set_of_base_set
    have h := hTyApply
    change
      __eo_typeof_set_insert (__eo_typeof typedListSub)
          (__eo_typeof baseSub) ≠
        Term.Stuck at h
    rwa [hBaseSubType] at h
  rw [hSubstEq, hInnerMk, hOuterMk]
  rw [hSubSetType, hOrigSetType]

/-- Size-recursive type preservation for simultaneous substitution.

The variable case is where `SubstEntryPreservesTypes` is consumed: mapped
actuals have exactly the type of the variable they replace. The remaining
application case is the real spine lemma: substitution preserves the operator
shape while recursively preserving the types of the spine arguments. -/
theorem substitute_simul_rec_typeof_eq_of_typeof_ne_stuck_lt
    (n : Nat) (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hLt : sizeOf F < n)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hEntryTypes : SubstEntryPreservesTypes xs ss)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ss bvs) =
      __eo_typeof F := by
  cases n with
  | zero =>
      omega
  | succ n =>
      let hRec :
          ∀ {G xs' ss' bvs' : Term} {xsVars' bvsVars' : List EoVarKey},
            sizeOf G < sizeOf F ->
            EoVarEnvPerm xs' xsVars' ->
            EoVarEnvPerm bvs' bvsVars' ->
            RuleProofs.eo_has_smt_translation G ->
            EoListAllHaveSmtTranslation ss' ->
            SubstEntryPreservesTypes xs' ss' ->
            __eo_typeof
                (__substitute_simul_rec (Term.Boolean false) G xs' ss' bvs') ≠
              Term.Stuck ->
            __eo_typeof
                (__substitute_simul_rec (Term.Boolean false) G xs' ss' bvs') =
              __eo_typeof G :=
        fun {G xs' ss' bvs'} {xsVars' bvsVars'} hGLt hXsEnv' hBvsEnv'
            hGTrans hSs' hEntryTypes' hGTy =>
          substitute_simul_rec_typeof_eq_of_typeof_ne_stuck_lt
            n G xs' ss' bvs'
            (by omega) hXsEnv' hBvsEnv' hGTrans hSs' hEntryTypes' hGTy
      cases F with
      | Apply f a =>
          by_cases hBinder :
              ∃ q v vs, f = Term.Apply q (consTerm v vs)
          · rcases hBinder with ⟨q, v, vs, rfl⟩
            let binders := consTerm v vs
            let bodySub :=
              __substitute_simul_rec (Term.Boolean false) a xs ss
                (__eo_list_concat Term.__eo_List_cons binders bvs)
            have hFTrans' :
                eoHasSmtTranslation
                  (Term.Apply (Term.Apply q binders) a) := by
              simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
                binders] using hFTrans
            have hQ :
                q = Term.UOp UserOp.forall ∨
                  q = Term.UOp UserOp.exists :=
              is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
                hFTrans'
            rcases eo_var_env_of_list_branch_has_smt_translation hFTrans' with
              ⟨binderVars, hBinderEnv⟩
            have hSubstEq :
                __substitute_simul_rec (Term.Boolean false)
                    (Term.Apply (Term.Apply q binders) a) xs ss bvs =
                  __eo_mk_apply (Term.Apply q binders) bodySub := by
              simpa [binders, bodySub] using
                substitute_simul_quant_eq_of_typeof_ne_stuck
                  q v vs a xs ss bvs hXsEnv hBvsEnv hSs hTy
            have hTyMk :
                __eo_typeof
                    (__eo_mk_apply (Term.Apply q binders) bodySub) ≠
                  Term.Stuck := by
              rwa [hSubstEq] at hTy
            have hMk :
                __eo_mk_apply (Term.Apply q binders) bodySub =
                  Term.Apply (Term.Apply q binders) bodySub :=
              eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
            have hTyApply :
                __eo_typeof (Term.Apply (Term.Apply q binders) bodySub) ≠
                  Term.Stuck := by
              rwa [hMk] at hTyMk
            have hBodyBool : __eo_typeof bodySub = Term.Bool :=
              eo_typeof_body_bool_of_quant_type_ne_stuck
                hQ hBinderEnv hTyApply
            have hBodyTy : __eo_typeof bodySub ≠ Term.Stuck := by
              rw [hBodyBool]
              intro h
              cases h
            have hBodyTrans :
                RuleProofs.eo_has_smt_translation a := by
              simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
                using
                  body_has_smt_translation_of_list_branch_has_smt_translation
                    hFTrans'
            have hBvsEnv' :
                EoVarEnvPerm
                  (__eo_list_concat Term.__eo_List_cons binders bvs)
                  (binderVars.reverse ++ bvsVars) :=
              EoVarEnvPerm.concat_rev hBinderEnv hBvsEnv
            have hBodyType :
                __eo_typeof bodySub = __eo_typeof a :=
              hRec
                (G := a) (xs' := xs) (ss' := ss)
                (bvs' := __eo_list_concat Term.__eo_List_cons binders bvs)
                (by simp; omega)
                hXsEnv hBvsEnv' hBodyTrans hSs hEntryTypes
                (by simpa [bodySub] using hBodyTy)
            exact
              substitute_simul_quant_typeof_eq_of_typeof_ne_stuck
                q v vs a xs ss bvs hXsEnv hBvsEnv hSs hFTrans
                (by simpa [binders, bodySub] using hBodyType)
                hTy
          · by_cases hNot : f = Term.UOp UserOp.not
            · subst f
              exact
                substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                  UserOp.not a xs ss bvs hXsEnv hBvsEnv hSs
                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                  hFTrans
                  (fun h =>
                    not_arg_has_smt_translation_of_has_smt_translation h)
                  (fun X hApp => by
                    change __eo_typeof_not (__eo_typeof X) ≠
                      Term.Stuck at hApp
                    intro hX
                    rw [hX] at hApp
                    exact hApp rfl)
                  (fun X Y hXY => by
                    change __eo_typeof_not (__eo_typeof X) =
                      __eo_typeof_not (__eo_typeof Y)
                    rw [hXY])
                  (fun hATrans hATy =>
                    hRec
                      (G := a) (xs' := xs) (ss' := ss) (bvs' := bvs)
                      (by simp)
                      hXsEnv hBvsEnv hATrans hSs hEntryTypes hATy)
                  hTy
            · by_cases hAbs : f = Term.UOp UserOp.abs
              · subst f
                exact
                  substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                    UserOp.abs a xs ss bvs hXsEnv hBvsEnv hSs
                    (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                    hFTrans
                    (fun h =>
                      abs_arg_has_smt_translation_of_has_smt_translation h)
                    (fun X hApp => by
                      change __eo_typeof_abs (__eo_typeof X) ≠
                        Term.Stuck at hApp
                      intro hX
                      rw [hX] at hApp
                      exact hApp rfl)
                    (fun X Y hXY => by
                      change __eo_typeof_abs (__eo_typeof X) =
                        __eo_typeof_abs (__eo_typeof Y)
                      rw [hXY])
                    (fun hATrans hATy =>
                      hRec
                        (G := a) (xs' := xs) (ss' := ss) (bvs' := bvs)
                        (by simp)
                        hXsEnv hBvsEnv hATrans hSs hEntryTypes hATy)
                    hTy
              · by_cases hToReal : f = Term.UOp UserOp.to_real
                · subst f
                  exact
                    substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                      UserOp.to_real a xs ss bvs hXsEnv hBvsEnv hSs
                      (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                      hFTrans
                      (fun h =>
                        to_real_arg_has_smt_translation_of_has_smt_translation h)
                      (fun X hApp => by
                        change __eo_typeof_to_real (__eo_typeof X) ≠
                          Term.Stuck at hApp
                        intro hX
                        rw [hX] at hApp
                        exact hApp rfl)
                      (fun X Y hXY => by
                        change __eo_typeof_to_real (__eo_typeof X) =
                          __eo_typeof_to_real (__eo_typeof Y)
                        rw [hXY])
                      (fun hATrans hATy =>
                        hRec
                          (G := a) (xs' := xs) (ss' := ss) (bvs' := bvs)
                          (by simp)
                          hXsEnv hBvsEnv hATrans hSs hEntryTypes hATy)
                      hTy
                · by_cases hToInt : f = Term.UOp UserOp.to_int
                  · subst f
                    exact
                      substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                        UserOp.to_int a xs ss bvs hXsEnv hBvsEnv hSs
                        (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                        hFTrans
                        (fun h =>
                          to_int_arg_has_smt_translation_of_has_smt_translation h)
                        (fun X hApp => by
                          change __eo_typeof_to_int (__eo_typeof X) ≠
                            Term.Stuck at hApp
                          intro hX
                          rw [hX] at hApp
                          exact hApp rfl)
                        (fun X Y hXY => by
                          change __eo_typeof_to_int (__eo_typeof X) =
                            __eo_typeof_to_int (__eo_typeof Y)
                          rw [hXY])
                        (fun hATrans hATy =>
                          hRec
                            (G := a) (xs' := xs) (ss' := ss) (bvs' := bvs)
                            (by simp)
                            hXsEnv hBvsEnv hATrans hSs hEntryTypes hATy)
                        hTy
                  · by_cases hIsInt : f = Term.UOp UserOp.is_int
                    · subst f
                      exact
                        substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                          UserOp.is_int a xs ss bvs hXsEnv hBvsEnv hSs
                          (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                          hFTrans
                          (fun h =>
                            is_int_arg_has_smt_translation_of_has_smt_translation h)
                          (fun X hApp => by
                            change __eo_typeof_is_int (__eo_typeof X) ≠
                              Term.Stuck at hApp
                            intro hX
                            rw [hX] at hApp
                            exact hApp rfl)
                          (fun X Y hXY => by
                            change __eo_typeof_is_int (__eo_typeof X) =
                              __eo_typeof_is_int (__eo_typeof Y)
                            rw [hXY])
                          (fun hATrans hATy =>
                            hRec
                              (G := a) (xs' := xs) (ss' := ss) (bvs' := bvs)
                              (by simp)
                              hXsEnv hBvsEnv hATrans hSs hEntryTypes hATy)
                          hTy
                    · by_cases hUneg : f = Term.UOp UserOp.__eoo_neg_2
                      · subst f
                        exact
                          substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                            UserOp.__eoo_neg_2 a xs ss bvs hXsEnv hBvsEnv hSs
                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                            hFTrans
                            (fun h =>
                              uneg_arg_has_smt_translation_of_has_smt_translation h)
                            (fun X hApp => by
                              change __eo_typeof_abs (__eo_typeof X) ≠
                                Term.Stuck at hApp
                              intro hX
                              rw [hX] at hApp
                              exact hApp rfl)
                            (fun X Y hXY => by
                              change __eo_typeof_abs (__eo_typeof X) =
                                __eo_typeof_abs (__eo_typeof Y)
                              rw [hXY])
                            (fun hATrans hATy =>
                              hRec
                                (G := a) (xs' := xs) (ss' := ss)
                                (bvs' := bvs)
                                (by simp)
                                hXsEnv hBvsEnv hATrans hSs hEntryTypes hATy)
                            hTy
                      · by_cases hPow2 : f = Term.UOp UserOp.int_pow2
                        · subst f
                          exact
                            substitute_simul_unary_op_typeof_eq_via_type_fn
                              UserOp.int_pow2 __eo_typeof_int_pow2
                              a xs ss bvs hXsEnv hBvsEnv hSs
                              (fun q v vs hEq =>
                                hBinder ⟨q, v, vs, hEq⟩)
                              hFTrans
                              (fun h =>
                                int_pow2_arg_has_smt_translation_of_has_smt_translation h)
                              (fun X => by
                                change
                                  __eo_typeof_int_pow2 (__eo_typeof X) =
                                    __eo_typeof_int_pow2 (__eo_typeof X)
                                rfl)
                              (by rfl)
                              (fun hATrans hATy =>
                                hRec
                                  (G := a) (xs' := xs) (ss' := ss)
                                  (bvs' := bvs)
                                  (by simp)
                                  hXsEnv hBvsEnv hATrans hSs hEntryTypes hATy)
                              hTy
                        · by_cases hLog2 : f = Term.UOp UserOp.int_log2
                          · subst f
                            exact
                              substitute_simul_unary_op_typeof_eq_via_type_fn
                                UserOp.int_log2 __eo_typeof_int_pow2
                                a xs ss bvs hXsEnv hBvsEnv hSs
                                (fun q v vs hEq =>
                                  hBinder ⟨q, v, vs, hEq⟩)
                                hFTrans
                                (fun h =>
                                  int_log2_arg_has_smt_translation_of_has_smt_translation h)
                                (fun X => by
                                  change
                                    __eo_typeof_int_pow2 (__eo_typeof X) =
                                      __eo_typeof_int_pow2 (__eo_typeof X)
                                  rfl)
                                (by rfl)
                                (fun hATrans hATy =>
                                  hRec
                                    (G := a) (xs' := xs) (ss' := ss)
                                    (bvs' := bvs)
                                    (by simp)
                                    hXsEnv hBvsEnv hATrans hSs hEntryTypes hATy)
                                hTy
                          · by_cases hPurify : f = Term.UOp UserOp._at_purify
                            · subst f
                              exact
                                substitute_simul_unary_op_typeof_eq_via_type_fn
                                  UserOp._at_purify __eo_typeof__at_purify
                                  a xs ss bvs hXsEnv hBvsEnv hSs
                                  (fun q v vs hEq =>
                                    hBinder ⟨q, v, vs, hEq⟩)
                                  hFTrans
                                  (fun h =>
                                    purify_arg_has_smt_translation_of_has_smt_translation h)
                                  (fun X => by
                                    change
                                      __eo_typeof__at_purify (__eo_typeof X) =
                                        __eo_typeof__at_purify (__eo_typeof X)
                                    rfl)
                                  (by rfl)
                                  (fun hATrans hATy =>
                                    hRec
                                      (G := a) (xs' := xs) (ss' := ss)
                                      (bvs' := bvs)
                                      (by simp)
                                      hXsEnv hBvsEnv hATrans hSs
                                      hEntryTypes hATy)
                                  hTy
                            · by_cases hIntIspow2 :
                                f = Term.UOp UserOp.int_ispow2
                              · subst f
                                exact
                                  substitute_simul_unary_op_typeof_eq_via_type_fn
                                    UserOp.int_ispow2 __eo_typeof_int_ispow2
                                    a xs ss bvs hXsEnv hBvsEnv hSs
                                    (fun q v vs hEq =>
                                      hBinder ⟨q, v, vs, hEq⟩)
                                    hFTrans
                                    (fun h =>
                                      int_ispow2_arg_has_smt_translation_of_has_smt_translation h)
                                    (fun X => by
                                      change
                                        __eo_typeof_int_ispow2 (__eo_typeof X) =
                                          __eo_typeof_int_ispow2 (__eo_typeof X)
                                      rfl)
                                    (by rfl)
                                    (fun hATrans hATy =>
                                      hRec
                                        (G := a) (xs' := xs) (ss' := ss)
                                        (bvs' := bvs)
                                        (by simp)
                                        hXsEnv hBvsEnv hATrans hSs
                                        hEntryTypes hATy)
                                    hTy
                              · by_cases hIntDivZero :
                                  f = Term.UOp UserOp._at_int_div_by_zero
                                · subst f
                                  exact
                                    substitute_simul_unary_op_typeof_eq_via_type_fn
                                      UserOp._at_int_div_by_zero
                                      __eo_typeof_int_pow2
                                      a xs ss bvs hXsEnv hBvsEnv hSs
                                      (fun q v vs hEq =>
                                        hBinder ⟨q, v, vs, hEq⟩)
                                      hFTrans
                                      (fun h =>
                                        int_div_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                      (fun X => by
                                        change
                                          __eo_typeof_int_pow2 (__eo_typeof X) =
                                            __eo_typeof_int_pow2 (__eo_typeof X)
                                        rfl)
                                      (by rfl)
                                      (fun hATrans hATy =>
                                        hRec
                                          (G := a) (xs' := xs) (ss' := ss)
                                          (bvs' := bvs)
                                          (by simp)
                                          hXsEnv hBvsEnv hATrans hSs
                                          hEntryTypes hATy)
                                      hTy
                                · by_cases hModZero :
                                    f = Term.UOp UserOp._at_mod_by_zero
                                  · subst f
                                    exact
                                      substitute_simul_unary_op_typeof_eq_via_type_fn
                                        UserOp._at_mod_by_zero
                                        __eo_typeof_int_pow2
                                        a xs ss bvs hXsEnv hBvsEnv hSs
                                        (fun q v vs hEq =>
                                          hBinder ⟨q, v, vs, hEq⟩)
                                        hFTrans
                                        (fun h =>
                                          mod_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                        (fun X => by
                                          change
                                            __eo_typeof_int_pow2 (__eo_typeof X) =
                                              __eo_typeof_int_pow2 (__eo_typeof X)
                                          rfl)
                                        (by rfl)
                                        (fun hATrans hATy =>
                                          hRec
                                            (G := a) (xs' := xs) (ss' := ss)
                                            (bvs' := bvs)
                                            (by simp)
                                            hXsEnv hBvsEnv hATrans hSs
                                            hEntryTypes hATy)
                                        hTy
                                  · by_cases hQDivZero :
                                      f = Term.UOp UserOp._at_div_by_zero
                                    · subst f
                                      exact
                                        substitute_simul_unary_op_typeof_eq_via_type_fn
                                          UserOp._at_div_by_zero
                                          __eo_typeof__at_div_by_zero
                                          a xs ss bvs hXsEnv hBvsEnv hSs
                                          (fun q v vs hEq =>
                                            hBinder ⟨q, v, vs, hEq⟩)
                                          hFTrans
                                          (fun h =>
                                            qdiv_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                          (fun X => by
                                            change
                                              __eo_typeof__at_div_by_zero
                                                  (__eo_typeof X) =
                                                __eo_typeof__at_div_by_zero
                                                  (__eo_typeof X)
                                            rfl)
                                          (by rfl)
                                          (fun hATrans hATy =>
                                            hRec
                                              (G := a) (xs' := xs)
                                              (ss' := ss) (bvs' := bvs)
                                              (by simp)
                                              hXsEnv hBvsEnv hATrans hSs
                                          hEntryTypes hATy)
                                          hTy
                                    · by_cases hBvnot :
                                        f = Term.UOp UserOp.bvnot
                                      · subst f
                                        exact
                                          substitute_simul_unary_op_typeof_eq_via_type_fn
                                            UserOp.bvnot __eo_typeof_bvnot
                                            a xs ss bvs hXsEnv hBvsEnv hSs
                                            (fun q v vs hEq =>
                                              hBinder ⟨q, v, vs, hEq⟩)
                                            hFTrans
                                            (fun h =>
                                              bvnot_arg_has_smt_translation_of_has_smt_translation h)
                                            (fun X => by
                                              change
                                                __eo_typeof_bvnot
                                                    (__eo_typeof X) =
                                                  __eo_typeof_bvnot
                                                    (__eo_typeof X)
                                              rfl)
                                            (by rfl)
                                            (fun hATrans hATy =>
                                              hRec
                                                (G := a) (xs' := xs)
                                                (ss' := ss) (bvs' := bvs)
                                                (by simp)
                                                hXsEnv hBvsEnv hATrans hSs
                                                hEntryTypes hATy)
                                            hTy
                                      · by_cases hBvneg :
                                          f = Term.UOp UserOp.bvneg
                                        · subst f
                                          exact
                                            substitute_simul_unary_op_typeof_eq_via_type_fn
                                              UserOp.bvneg __eo_typeof_bvnot
                                              a xs ss bvs hXsEnv hBvsEnv hSs
                                              (fun q v vs hEq =>
                                                hBinder ⟨q, v, vs, hEq⟩)
                                              hFTrans
                                              (fun h =>
                                                bvneg_arg_has_smt_translation_of_has_smt_translation h)
                                              (fun X => by
                                                change
                                                  __eo_typeof_bvnot
                                                      (__eo_typeof X) =
                                                    __eo_typeof_bvnot
                                                      (__eo_typeof X)
                                                rfl)
                                              (by rfl)
                                              (fun hATrans hATy =>
                                                hRec
                                                  (G := a) (xs' := xs)
                                                  (ss' := ss) (bvs' := bvs)
                                                  (by simp)
                                                  hXsEnv hBvsEnv hATrans hSs
                                                  hEntryTypes hATy)
                                              hTy
                                        · by_cases hBvnego :
                                            f = Term.UOp UserOp.bvnego
                                          · subst f
                                            exact
                                              substitute_simul_unary_op_typeof_eq_via_type_fn
                                                UserOp.bvnego __eo_typeof_bvnego
                                                a xs ss bvs hXsEnv hBvsEnv hSs
                                                (fun q v vs hEq =>
                                                  hBinder ⟨q, v, vs, hEq⟩)
                                                hFTrans
                                                (fun h =>
                                                  bvnego_arg_has_smt_translation_of_has_smt_translation h)
                                                (fun X => by
                                                  change
                                                    __eo_typeof_bvnego
                                                        (__eo_typeof X) =
                                                      __eo_typeof_bvnego
                                                        (__eo_typeof X)
                                                  rfl)
                                                (by rfl)
                                                (fun hATrans hATy =>
                                                  hRec
                                                    (G := a) (xs' := xs)
                                                    (ss' := ss) (bvs' := bvs)
                                                    (by simp)
                                                    hXsEnv hBvsEnv hATrans hSs
                                                    hEntryTypes hATy)
                                                hTy
                                          · by_cases hBvsize :
                                              f = Term.UOp UserOp._at_bvsize
                                            · subst f
                                              exact
                                                substitute_simul_unary_op_typeof_eq_via_type_fn
                                                  UserOp._at_bvsize
                                                  __eo_typeof__at_bvsize
                                                  a xs ss bvs hXsEnv hBvsEnv hSs
                                                  (fun q v vs hEq =>
                                                    hBinder ⟨q, v, vs, hEq⟩)
                                                  hFTrans
                                                  (fun h =>
                                                    bvsize_arg_has_smt_translation_of_has_smt_translation h)
                                                  (fun X => by
                                                    change
                                                      __eo_typeof__at_bvsize
                                                          (__eo_typeof X) =
                                                        __eo_typeof__at_bvsize
                                                          (__eo_typeof X)
                                                    rfl)
                                                  (by rfl)
                                                  (fun hATrans hATy =>
                                                    hRec
                                                      (G := a) (xs' := xs)
                                                      (ss' := ss)
                                                      (bvs' := bvs)
                                                      (by simp)
                                                      hXsEnv hBvsEnv hATrans
                                                      hSs hEntryTypes hATy)
                                                  hTy
                                            · by_cases hBvredand :
                                                f = Term.UOp UserOp.bvredand
                                              · subst f
                                                exact
                                                  substitute_simul_unary_op_typeof_eq_via_type_fn
                                                    UserOp.bvredand
                                                    __eo_typeof_bvredand
                                                    a xs ss bvs hXsEnv hBvsEnv hSs
                                                    (fun q v vs hEq =>
                                                      hBinder ⟨q, v, vs, hEq⟩)
                                                    hFTrans
                                                    (fun h =>
                                                      bvredand_arg_has_smt_translation_of_has_smt_translation h)
                                                    (fun X => by
                                                      change
                                                        __eo_typeof_bvredand
                                                            (__eo_typeof X) =
                                                          __eo_typeof_bvredand
                                                            (__eo_typeof X)
                                                      rfl)
                                                    (by rfl)
                                                    (fun hATrans hATy =>
                                                      hRec
                                                        (G := a) (xs' := xs)
                                                        (ss' := ss)
                                                        (bvs' := bvs)
                                                        (by simp)
                                                        hXsEnv hBvsEnv hATrans
                                                        hSs hEntryTypes hATy)
                                                    hTy
                                              · by_cases hBvredor :
                                                  f = Term.UOp UserOp.bvredor
                                                · subst f
                                                  exact
                                                    substitute_simul_unary_op_typeof_eq_via_type_fn
                                                      UserOp.bvredor
                                                      __eo_typeof_bvredand
                                                      a xs ss bvs hXsEnv hBvsEnv hSs
                                                      (fun q v vs hEq =>
                                                        hBinder ⟨q, v, vs, hEq⟩)
                                                      hFTrans
                                                      (fun h =>
                                                        bvredor_arg_has_smt_translation_of_has_smt_translation h)
                                                      (fun X => by
                                                        change
                                                          __eo_typeof_bvredand
                                                              (__eo_typeof X) =
                                                            __eo_typeof_bvredand
                                                              (__eo_typeof X)
                                                        rfl)
                                                      (by rfl)
                                                      (fun hATrans hATy =>
                                                        hRec
                                                          (G := a) (xs' := xs)
                                                          (ss' := ss)
                                                          (bvs' := bvs)
                                                          (by simp)
                                                          hXsEnv hBvsEnv
                                                          hATrans hSs
                                                          hEntryTypes hATy)
                                                      hTy
                                                · by_cases hUbvToInt :
                                                    f = Term.UOp UserOp.ubv_to_int
                                                  · subst f
                                                    exact
                                                      substitute_simul_unary_op_typeof_eq_via_type_fn
                                                        UserOp.ubv_to_int
                                                        __eo_typeof__at_bvsize
                                                        a xs ss bvs hXsEnv hBvsEnv hSs
                                                        (fun q v vs hEq =>
                                                          hBinder ⟨q, v, vs, hEq⟩)
                                                        hFTrans
                                                        (fun h =>
                                                          ubv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                        (fun X => by
                                                          change
                                                            __eo_typeof__at_bvsize
                                                                (__eo_typeof X) =
                                                              __eo_typeof__at_bvsize
                                                                (__eo_typeof X)
                                                          rfl)
                                                        (by rfl)
                                                        (fun hATrans hATy =>
                                                          hRec
                                                            (G := a) (xs' := xs)
                                                            (ss' := ss)
                                                            (bvs' := bvs)
                                                            (by simp)
                                                            hXsEnv hBvsEnv
                                                            hATrans hSs
                                                            hEntryTypes hATy)
                                                        hTy
                                                  · by_cases hSbvToInt :
                                                      f = Term.UOp UserOp.sbv_to_int
                                                    · subst f
                                                      exact
                                                        substitute_simul_unary_op_typeof_eq_via_type_fn
                                                          UserOp.sbv_to_int
                                                          __eo_typeof__at_bvsize
                                                          a xs ss bvs hXsEnv hBvsEnv hSs
                                                          (fun q v vs hEq =>
                                                            hBinder ⟨q, v, vs, hEq⟩)
                                                          hFTrans
                                                          (fun h =>
                                                            sbv_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                          (fun X => by
                                                            change
                                                              __eo_typeof__at_bvsize
                                                                  (__eo_typeof X) =
                                                                __eo_typeof__at_bvsize
                                                                  (__eo_typeof X)
                                                            rfl)
                                                          (by rfl)
                                                          (fun hATrans hATy =>
                                                            hRec
                                                              (G := a)
                                                              (xs' := xs)
                                                              (ss' := ss)
                                                              (bvs' := bvs)
                                                              (by simp)
                                                              hXsEnv hBvsEnv
                                                              hATrans hSs
                                                              hEntryTypes hATy)
                                                          hTy
                                                    · by_cases hStrLen :
                                                        f = Term.UOp UserOp.str_len
                                                      · subst f
                                                        exact
                                                          substitute_simul_unary_op_typeof_eq_via_type_fn
                                                            UserOp.str_len
                                                            __eo_typeof_str_len
                                                            a xs ss bvs hXsEnv hBvsEnv hSs
                                                            (fun q v vs hEq =>
                                                              hBinder ⟨q, v, vs, hEq⟩)
                                                            hFTrans
                                                            (fun h =>
                                                              str_len_arg_has_smt_translation_of_has_smt_translation h)
                                                            (fun X => by
                                                              change
                                                                __eo_typeof_str_len
                                                                    (__eo_typeof X) =
                                                                  __eo_typeof_str_len
                                                                    (__eo_typeof X)
                                                              rfl)
                                                            (by rfl)
                                                            (fun hATrans hATy =>
                                                              hRec
                                                                (G := a)
                                                                (xs' := xs)
                                                                (ss' := ss)
                                                                (bvs' := bvs)
                                                                (by simp)
                                                                hXsEnv hBvsEnv
                                                                hATrans hSs
                                                                hEntryTypes hATy)
                                                            hTy
                                                      · by_cases hStrRev :
                                                          f = Term.UOp UserOp.str_rev
                                                        · subst f
                                                          exact
                                                            substitute_simul_unary_op_typeof_eq_via_type_fn
                                                              UserOp.str_rev
                                                              __eo_typeof_str_rev
                                                              a xs ss bvs hXsEnv hBvsEnv hSs
                                                              (fun q v vs hEq =>
                                                                hBinder ⟨q, v, vs, hEq⟩)
                                                              hFTrans
                                                              (fun h =>
                                                                str_rev_arg_has_smt_translation_of_has_smt_translation h)
                                                              (fun X => by
                                                                change
                                                                  __eo_typeof_str_rev
                                                                      (__eo_typeof X) =
                                                                    __eo_typeof_str_rev
                                                                      (__eo_typeof X)
                                                                rfl)
                                                              (by rfl)
                                                              (fun hATrans hATy =>
                                                                hRec
                                                                  (G := a)
                                                                  (xs' := xs)
                                                                  (ss' := ss)
                                                                  (bvs' := bvs)
                                                                  (by simp)
                                                                  hXsEnv hBvsEnv
                                                                  hATrans hSs
                                                                  hEntryTypes hATy)
                                                              hTy
                                                        · by_cases hStrToInt :
                                                            f = Term.UOp UserOp.str_to_int
                                                          · subst f
                                                            exact
                                                              substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                UserOp.str_to_int
                                                                __eo_typeof_str_to_code
                                                                a xs ss bvs hXsEnv hBvsEnv hSs
                                                                (fun q v vs hEq =>
                                                                  hBinder ⟨q, v, vs, hEq⟩)
                                                                hFTrans
                                                                (fun h =>
                                                                  str_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                (fun X => by
                                                                  change
                                                                    __eo_typeof_str_to_code
                                                                        (__eo_typeof X) =
                                                                      __eo_typeof_str_to_code
                                                                        (__eo_typeof X)
                                                                  rfl)
                                                                (by rfl)
                                                                (fun hATrans hATy =>
                                                                  hRec
                                                                    (G := a)
                                                                    (xs' := xs)
                                                                    (ss' := ss)
                                                                    (bvs' := bvs)
                                                                    (by simp)
                                                                    hXsEnv hBvsEnv
                                                                    hATrans hSs
                                                                    hEntryTypes hATy)
                                                                hTy
                                                          · by_cases hStrToRe :
                                                              f = Term.UOp UserOp.str_to_re
                                                            · subst f
                                                              exact
                                                                substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                  UserOp.str_to_re
                                                                  __eo_typeof_str_to_re
                                                                  a xs ss bvs hXsEnv hBvsEnv hSs
                                                                  (fun q v vs hEq =>
                                                                    hBinder ⟨q, v, vs, hEq⟩)
                                                                  hFTrans
                                                                  (fun h =>
                                                                    str_to_re_arg_has_smt_translation_of_has_smt_translation h)
                                                                  (fun X => by
                                                                    change
                                                                      __eo_typeof_str_to_re
                                                                          (__eo_typeof X) =
                                                                        __eo_typeof_str_to_re
                                                                          (__eo_typeof X)
                                                                    rfl)
                                                                  (by rfl)
                                                                  (fun hATrans hATy =>
                                                                    hRec
                                                                      (G := a)
                                                                      (xs' := xs)
                                                                      (ss' := ss)
                                                                      (bvs' := bvs)
                                                                      (by simp)
                                                                      hXsEnv hBvsEnv
                                                                      hATrans hSs
                                                                      hEntryTypes hATy)
                                                                  hTy
                                                            · by_cases hReMult :
                                                                f = Term.UOp UserOp.re_mult
                                                              · subst f
                                                                exact
                                                                  substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                    UserOp.re_mult
                                                                    __eo_typeof_re_mult
                                                                    a xs ss bvs hXsEnv hBvsEnv hSs
                                                                    (fun q v vs hEq =>
                                                                      hBinder ⟨q, v, vs, hEq⟩)
                                                                    hFTrans
                                                                    (fun h =>
                                                                      re_mult_arg_has_smt_translation_of_has_smt_translation h)
                                                                    (fun X => by
                                                                      change
                                                                        __eo_typeof_re_mult
                                                                            (__eo_typeof X) =
                                                                          __eo_typeof_re_mult
                                                                            (__eo_typeof X)
                                                                      rfl)
                                                                    (by rfl)
                                                                    (fun hATrans hATy =>
                                                                      hRec
                                                                        (G := a)
                                                                        (xs' := xs)
                                                                        (ss' := ss)
                                                                        (bvs' := bvs)
                                                                        (by simp)
                                                                        hXsEnv hBvsEnv
                                                                        hATrans hSs
                                                                        hEntryTypes hATy)
                                                                    hTy
                                                              · by_cases hStrToLower :
                                                                  f = Term.UOp UserOp.str_to_lower
                                                                · subst f
                                                                  exact
                                                                    substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                      UserOp.str_to_lower
                                                                      __eo_typeof_str_to_lower
                                                                      a xs ss bvs hXsEnv hBvsEnv hSs
                                                                      (fun q v vs hEq =>
                                                                        hBinder ⟨q, v, vs, hEq⟩)
                                                                      hFTrans
                                                                      (fun h =>
                                                                        str_to_lower_arg_has_smt_translation_of_has_smt_translation h)
                                                                      (fun X => by
                                                                        change
                                                                          __eo_typeof_str_to_lower
                                                                              (__eo_typeof X) =
                                                                            __eo_typeof_str_to_lower
                                                                              (__eo_typeof X)
                                                                        rfl)
                                                                      (by rfl)
                                                                      (fun hATrans hATy =>
                                                                        hRec
                                                                          (G := a)
                                                                          (xs' := xs)
                                                                          (ss' := ss)
                                                                          (bvs' := bvs)
                                                                          (by simp)
                                                                          hXsEnv hBvsEnv
                                                                          hATrans hSs
                                                                          hEntryTypes hATy)
                                                                      hTy
                                                                · by_cases hStrToUpper :
                                                                    f = Term.UOp UserOp.str_to_upper
                                                                  · subst f
                                                                    exact
                                                                      substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                        UserOp.str_to_upper
                                                                        __eo_typeof_str_to_lower
                                                                        a xs ss bvs hXsEnv hBvsEnv hSs
                                                                        (fun q v vs hEq =>
                                                                          hBinder ⟨q, v, vs, hEq⟩)
                                                                        hFTrans
                                                                        (fun h =>
                                                                          str_to_upper_arg_has_smt_translation_of_has_smt_translation h)
                                                                        (fun X => by
                                                                          change
                                                                            __eo_typeof_str_to_lower
                                                                                (__eo_typeof X) =
                                                                              __eo_typeof_str_to_lower
                                                                                (__eo_typeof X)
                                                                          rfl)
                                                                        (by rfl)
                                                                        (fun hATrans hATy =>
                                                                          hRec
                                                                            (G := a)
                                                                            (xs' := xs)
                                                                            (ss' := ss)
                                                                            (bvs' := bvs)
                                                                            (by simp)
                                                                            hXsEnv hBvsEnv
                                                                            hATrans hSs
                                                                            hEntryTypes hATy)
                                                                        hTy
                                                                  · by_cases hStrToCode :
                                                                      f = Term.UOp UserOp.str_to_code
                                                                    · subst f
                                                                      exact
                                                                        substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                          UserOp.str_to_code
                                                                          __eo_typeof_str_to_code
                                                                          a xs ss bvs hXsEnv hBvsEnv hSs
                                                                          (fun q v vs hEq =>
                                                                            hBinder ⟨q, v, vs, hEq⟩)
                                                                          hFTrans
                                                                          (fun h =>
                                                                            str_to_code_arg_has_smt_translation_of_has_smt_translation h)
                                                                          (fun X => by
                                                                            change
                                                                              __eo_typeof_str_to_code
                                                                                  (__eo_typeof X) =
                                                                                __eo_typeof_str_to_code
                                                                                  (__eo_typeof X)
                                                                            rfl)
                                                                          (by rfl)
                                                                          (fun hATrans hATy =>
                                                                            hRec
                                                                              (G := a)
                                                                              (xs' := xs)
                                                                              (ss' := ss)
                                                                              (bvs' := bvs)
                                                                              (by simp)
                                                                              hXsEnv hBvsEnv
                                                                              hATrans hSs
                                                                              hEntryTypes hATy)
                                                                          hTy
                                                                    · by_cases hStrFromCode :
                                                                        f = Term.UOp UserOp.str_from_code
                                                                      · subst f
                                                                        exact
                                                                          substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                            UserOp.str_from_code
                                                                            __eo_typeof_str_from_code
                                                                            a xs ss bvs hXsEnv hBvsEnv hSs
                                                                            (fun q v vs hEq =>
                                                                              hBinder ⟨q, v, vs, hEq⟩)
                                                                            hFTrans
                                                                            (fun h =>
                                                                              str_from_code_arg_has_smt_translation_of_has_smt_translation h)
                                                                            (fun X => by
                                                                              change
                                                                                __eo_typeof_str_from_code
                                                                                    (__eo_typeof X) =
                                                                                  __eo_typeof_str_from_code
                                                                                    (__eo_typeof X)
                                                                              rfl)
                                                                            (by rfl)
                                                                            (fun hATrans hATy =>
                                                                              hRec
                                                                                (G := a)
                                                                                (xs' := xs)
                                                                                (ss' := ss)
                                                                                (bvs' := bvs)
                                                                                (by simp)
                                                                                hXsEnv hBvsEnv
                                                                                hATrans hSs
                                                                                hEntryTypes hATy)
                                                                            hTy
                                                                      · by_cases hStrIsDigit :
                                                                          f = Term.UOp UserOp.str_is_digit
                                                                        · subst f
                                                                          exact
                                                                            substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                              UserOp.str_is_digit
                                                                              __eo_typeof_str_is_digit
                                                                              a xs ss bvs hXsEnv hBvsEnv hSs
                                                                              (fun q v vs hEq =>
                                                                                hBinder ⟨q, v, vs, hEq⟩)
                                                                              hFTrans
                                                                              (fun h =>
                                                                                str_is_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                                              (fun X => by
                                                                                change
                                                                                  __eo_typeof_str_is_digit
                                                                                      (__eo_typeof X) =
                                                                                    __eo_typeof_str_is_digit
                                                                                      (__eo_typeof X)
                                                                                rfl)
                                                                              (by rfl)
                                                                              (fun hATrans hATy =>
                                                                                hRec
                                                                                  (G := a)
                                                                                  (xs' := xs)
                                                                                  (ss' := ss)
                                                                                  (bvs' := bvs)
                                                                                  (by simp)
                                                                                  hXsEnv hBvsEnv
                                                                                  hATrans hSs
                                                                                  hEntryTypes hATy)
                                                                              hTy
                                                                        · by_cases hStrFromInt :
                                                                            f = Term.UOp UserOp.str_from_int
                                                                          · subst f
                                                                            exact
                                                                              substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                UserOp.str_from_int
                                                                                __eo_typeof_str_from_code
                                                                                a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                (fun q v vs hEq =>
                                                                                  hBinder ⟨q, v, vs, hEq⟩)
                                                                                hFTrans
                                                                                (fun h =>
                                                                                  str_from_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                                (fun X => by
                                                                                  change
                                                                                    __eo_typeof_str_from_code
                                                                                        (__eo_typeof X) =
                                                                                      __eo_typeof_str_from_code
                                                                                        (__eo_typeof X)
                                                                                  rfl)
                                                                                (by rfl)
                                                                                (fun hATrans hATy =>
                                                                                  hRec
                                                                                    (G := a)
                                                                                    (xs' := xs)
                                                                                    (ss' := ss)
                                                                                    (bvs' := bvs)
                                                                                    (by simp)
                                                                                    hXsEnv hBvsEnv
                                                                                    hATrans hSs
                                                                                    hEntryTypes hATy)
                                                                                hTy
                                                                          · by_cases hRePlus :
                                                                              f = Term.UOp UserOp.re_plus
                                                                            · subst f
                                                                              exact
                                                                                substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                  UserOp.re_plus
                                                                                  __eo_typeof_re_mult
                                                                                  a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                  (fun q v vs hEq =>
                                                                                    hBinder ⟨q, v, vs, hEq⟩)
                                                                                  hFTrans
                                                                                  (fun h =>
                                                                                    re_plus_arg_has_smt_translation_of_has_smt_translation h)
                                                                                  (fun X => by
                                                                                    change
                                                                                      __eo_typeof_re_mult
                                                                                          (__eo_typeof X) =
                                                                                        __eo_typeof_re_mult
                                                                                          (__eo_typeof X)
                                                                                    rfl)
                                                                                  (by rfl)
                                                                                  (fun hATrans hATy =>
                                                                                    hRec
                                                                                      (G := a)
                                                                                      (xs' := xs)
                                                                                      (ss' := ss)
                                                                                      (bvs' := bvs)
                                                                                      (by simp)
                                                                                      hXsEnv hBvsEnv
                                                                                      hATrans hSs
                                                                                      hEntryTypes hATy)
                                                                                  hTy
                                                                            · by_cases hReOpt :
                                                                                f = Term.UOp UserOp.re_opt
                                                                              · subst f
                                                                                exact
                                                                                  substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                    UserOp.re_opt
                                                                                    __eo_typeof_re_mult
                                                                                    a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                    (fun q v vs hEq =>
                                                                                      hBinder ⟨q, v, vs, hEq⟩)
                                                                                    hFTrans
                                                                                    (fun h =>
                                                                                      re_opt_arg_has_smt_translation_of_has_smt_translation h)
                                                                                    (fun X => by
                                                                                      change
                                                                                        __eo_typeof_re_mult
                                                                                            (__eo_typeof X) =
                                                                                          __eo_typeof_re_mult
                                                                                            (__eo_typeof X)
                                                                                      rfl)
                                                                                    (by rfl)
                                                                                    (fun hATrans hATy =>
                                                                                      hRec
                                                                                        (G := a)
                                                                                        (xs' := xs)
                                                                                        (ss' := ss)
                                                                                        (bvs' := bvs)
                                                                                        (by simp)
                                                                                        hXsEnv hBvsEnv
                                                                                        hATrans hSs
                                                                                        hEntryTypes hATy)
                                                                                    hTy
                                                                              · by_cases hReComp :
                                                                                  f = Term.UOp UserOp.re_comp
                                                                                · subst f
                                                                                  exact
                                                                                    substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                      UserOp.re_comp
                                                                                      __eo_typeof_re_mult
                                                                                      a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                      (fun q v vs hEq =>
                                                                                        hBinder ⟨q, v, vs, hEq⟩)
                                                                                      hFTrans
                                                                                      (fun h =>
                                                                                        re_comp_arg_has_smt_translation_of_has_smt_translation h)
                                                                                      (fun X => by
                                                                                        change
                                                                                          __eo_typeof_re_mult
                                                                                              (__eo_typeof X) =
                                                                                            __eo_typeof_re_mult
                                                                                              (__eo_typeof X)
                                                                                        rfl)
                                                                                      (by rfl)
                                                                                      (fun hATrans hATy =>
                                                                                        hRec
                                                                                          (G := a)
                                                                                          (xs' := xs)
                                                                                          (ss' := ss)
                                                                                          (bvs' := bvs)
                                                                                          (by simp)
                                                                                          hXsEnv hBvsEnv
                                                                                          hATrans hSs
                                                                                          hEntryTypes hATy)
                                                                                      hTy
                                                                                · by_cases hStoi :
                                                                                    f = Term.UOp UserOp._at_strings_stoi_non_digit
                                                                                  · subst f
                                                                                    exact
                                                                                      substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                        UserOp._at_strings_stoi_non_digit
                                                                                        __eo_typeof_str_to_code
                                                                                        a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                        (fun q v vs hEq =>
                                                                                          hBinder ⟨q, v, vs, hEq⟩)
                                                                                        hFTrans
                                                                                        (fun h =>
                                                                                          strings_stoi_non_digit_arg_has_smt_translation_of_has_smt_translation h)
                                                                                        (fun X => by
                                                                                          change
                                                                                            __eo_typeof_str_to_code
                                                                                                (__eo_typeof X) =
                                                                                              __eo_typeof_str_to_code
                                                                                                (__eo_typeof X)
                                                                                          rfl)
                                                                                        (by rfl)
                                                                                        (fun hATrans hATy =>
                                                                                          hRec
                                                                                            (G := a)
                                                                                            (xs' := xs)
                                                                                            (ss' := ss)
                                                                                            (bvs' := bvs)
                                                                                            (by simp)
                                                                                            hXsEnv hBvsEnv
                                                                                            hATrans hSs
                                                                                            hEntryTypes hATy)
                                                                                        hTy
                                                                                  · by_cases hSeqUnit :
                                                                                      f = Term.UOp UserOp.seq_unit
                                                                                    · subst f
                                                                                      exact
                                                                                        substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                          UserOp.seq_unit
                                                                                          __eo_typeof_seq_unit
                                                                                          a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                          (fun q v vs hEq =>
                                                                                            hBinder ⟨q, v, vs, hEq⟩)
                                                                                          hFTrans
                                                                                          (fun h =>
                                                                                            seq_unit_arg_has_smt_translation_of_has_smt_translation h)
                                                                                          (fun X => by
                                                                                            change
                                                                                              __eo_typeof_seq_unit
                                                                                                  (__eo_typeof X) =
                                                                                                __eo_typeof_seq_unit
                                                                                                  (__eo_typeof X)
                                                                                            rfl)
                                                                                          (by rfl)
                                                                                          (fun hATrans hATy =>
                                                                                            hRec
                                                                                              (G := a)
                                                                                              (xs' := xs)
                                                                                              (ss' := ss)
                                                                                              (bvs' := bvs)
                                                                                              (by simp)
                                                                                              hXsEnv hBvsEnv
                                                                                              hATrans hSs
                                                                                              hEntryTypes hATy)
                                                                                          hTy
                                                                                    · by_cases hSetSingleton :
                                                                                        f = Term.UOp UserOp.set_singleton
                                                                                      · subst f
                                                                                        exact
                                                                                          substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                            UserOp.set_singleton
                                                                                            __eo_typeof_set_singleton
                                                                                            a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                            (fun q v vs hEq =>
                                                                                              hBinder ⟨q, v, vs, hEq⟩)
                                                                                            hFTrans
                                                                                            (fun h =>
                                                                                              set_singleton_arg_has_smt_translation_of_has_smt_translation h)
                                                                                            (fun X => by
                                                                                              change
                                                                                                __eo_typeof_set_singleton
                                                                                                    (__eo_typeof X) =
                                                                                                  __eo_typeof_set_singleton
                                                                                                    (__eo_typeof X)
                                                                                              rfl)
                                                                                            (by rfl)
                                                                                            (fun hATrans hATy =>
                                                                                              hRec
                                                                                                (G := a)
                                                                                                (xs' := xs)
                                                                                                (ss' := ss)
                                                                                                (bvs' := bvs)
                                                                                                (by simp)
                                                                                                hXsEnv hBvsEnv
                                                                                                hATrans hSs
                                                                                                hEntryTypes hATy)
                                                                                            hTy
                                                                                      · by_cases hSetChoose :
                                                                                          f = Term.UOp UserOp.set_choose
                                                                                        · subst f
                                                                                          exact
                                                                                            substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                              UserOp.set_choose
                                                                                              __eo_typeof_set_choose
                                                                                              a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                              (fun q v vs hEq =>
                                                                                                hBinder ⟨q, v, vs, hEq⟩)
                                                                                              hFTrans
                                                                                              (fun h =>
                                                                                                set_choose_arg_has_smt_translation_of_has_smt_translation h)
                                                                                              (fun X => by
                                                                                                change
                                                                                                  __eo_typeof_set_choose
                                                                                                      (__eo_typeof X) =
                                                                                                    __eo_typeof_set_choose
                                                                                                      (__eo_typeof X)
                                                                                                rfl)
                                                                                              (by rfl)
                                                                                              (fun hATrans hATy =>
                                                                                                hRec
                                                                                                  (G := a)
                                                                                                  (xs' := xs)
                                                                                                  (ss' := ss)
                                                                                                  (bvs' := bvs)
                                                                                                  (by simp)
                                                                                                  hXsEnv hBvsEnv
                                                                                                  hATrans hSs
                                                                                                  hEntryTypes hATy)
                                                                                              hTy
                                                                                        · by_cases hSetEmpty :
                                                                                            f = Term.UOp UserOp.set_is_empty
                                                                                          · subst f
                                                                                            exact
                                                                                              substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                                UserOp.set_is_empty
                                                                                                __eo_typeof_set_is_empty
                                                                                                a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                                (fun q v vs hEq =>
                                                                                                  hBinder ⟨q, v, vs, hEq⟩)
                                                                                                hFTrans
                                                                                                (fun h =>
                                                                                                  set_is_empty_arg_has_smt_translation_of_has_smt_translation h)
                                                                                                (fun X => by
                                                                                                  change
                                                                                                    __eo_typeof_set_is_empty
                                                                                                        (__eo_typeof X) =
                                                                                                      __eo_typeof_set_is_empty
                                                                                                        (__eo_typeof X)
                                                                                                  rfl)
                                                                                                (by rfl)
                                                                                                (fun hATrans hATy =>
                                                                                                  hRec
                                                                                                    (G := a)
                                                                                                    (xs' := xs)
                                                                                                    (ss' := ss)
                                                                                                    (bvs' := bvs)
                                                                                                    (by simp)
                                                                                                    hXsEnv hBvsEnv
                                                                                                    hATrans hSs
                                                                                                    hEntryTypes hATy)
                                                                                                hTy
                                                                                          · by_cases hSetIsSingleton :
                                                                                              f = Term.UOp UserOp.set_is_singleton
                                                                                            · subst f
                                                                                              exact
                                                                                                substitute_simul_unary_op_typeof_eq_via_type_fn
                                                                                                  UserOp.set_is_singleton
                                                                                                  __eo_typeof_set_is_empty
                                                                                                  a xs ss bvs hXsEnv hBvsEnv hSs
                                                                                                  (fun q v vs hEq =>
                                                                                                    hBinder ⟨q, v, vs, hEq⟩)
                                                                                                  hFTrans
                                                                                                  (fun h =>
                                                                                                    set_is_singleton_arg_has_smt_translation_of_has_smt_translation h)
                                                                                                  (fun X => by
                                                                                                    change
                                                                                                      __eo_typeof_set_is_empty
                                                                                                          (__eo_typeof X) =
                                                                                                        __eo_typeof_set_is_empty
                                                                                                          (__eo_typeof X)
                                                                                                    rfl)
                                                                                                  (by rfl)
                                                                                                  (fun hATrans hATy =>
                                                                                                    hRec
                                                                                                      (G := a)
                                                                                                      (xs' := xs)
                                                                                                      (ss' := ss)
                                                                                                      (bvs' := bvs)
                                                                                                      (by simp)
                                                                                                      hXsEnv hBvsEnv
                                                                                                      hATrans hSs
                                                                                                      hEntryTypes hATy)
                                                                                                  hTy
                                                                                            · cases f with
                                                                                              | Apply g x1 =>
                                                                                                  cases g with
                                                                                                  | UOp op =>
                                                                                                      have hCurrentBin :
                                                                                                          ∀ (typeFn : Term -> Term -> Term),
                                                                                                            (eoHasSmtTranslation
                                                                                                                (Term.Apply
                                                                                                                  (Term.Apply (Term.UOp op) x1) a) ->
                                                                                                              eoHasSmtTranslation x1 ∧
                                                                                                                eoHasSmtTranslation a) ->
                                                                                                            (∀ X Y,
                                                                                                              __eo_typeof
                                                                                                                  (Term.Apply
                                                                                                                    (Term.Apply (Term.UOp op) X) Y) =
                                                                                                                typeFn (__eo_typeof X)
                                                                                                                  (__eo_typeof Y)) ->
                                                                                                            (∀ Y, typeFn Term.Stuck Y =
                                                                                                              Term.Stuck) ->
                                                                                                            (∀ X, typeFn X Term.Stuck =
                                                                                                              Term.Stuck) ->
                                                                                                            __eo_typeof
                                                                                                                (__substitute_simul_rec
                                                                                                                  (Term.Boolean false)
                                                                                                                  (Term.Apply
                                                                                                                    (Term.Apply
                                                                                                                      (Term.UOp op) x1) a)
                                                                                                                  xs ss bvs) =
                                                                                                              __eo_typeof
                                                                                                                (Term.Apply
                                                                                                                  (Term.Apply
                                                                                                                    (Term.UOp op) x1) a) := by
                                                                                                        intro typeFn hArgExtract hTypeFn
                                                                                                          hTypeFnStuckLeft
                                                                                                          hTypeFnStuckRight
                                                                                                        exact
                                                                                                          substitute_simul_binary_op_typeof_eq_via_type_fn
                                                                                                            op typeFn x1 a xs ss bvs
                                                                                                            hXsEnv hBvsEnv hSs
                                                                                                            (fun q v vs hEq =>
                                                                                                              hBinder ⟨q, v, vs, hEq⟩)
                                                                                                            hFTrans
                                                                                                            hArgExtract hTypeFn
                                                                                                            hTypeFnStuckLeft
                                                                                                            hTypeFnStuckRight
                                                                                                            (fun hXTrans hXTy =>
                                                                                                              hRec
                                                                                                                (G := x1)
                                                                                                                (xs' := xs)
                                                                                                                (ss' := ss)
                                                                                                                (bvs' := bvs)
                                                                                                                (by simp; omega)
                                                                                                                hXsEnv hBvsEnv
                                                                                                                hXTrans hSs
                                                                                                                hEntryTypes hXTy)
                                                                                                            (fun hATrans hATy =>
                                                                                                              hRec
                                                                                                                (G := a)
                                                                                                                (xs' := xs)
                                                                                                                (ss' := ss)
                                                                                                                (bvs' := bvs)
                                                                                                                (by simp; omega)
                                                                                                                hXsEnv hBvsEnv
                                                                                                                hATrans hSs
                                                                                                                hEntryTypes hATy)
                                                                                                            hTy
                                                                                                      have hCurrentSmtBin :
                                                                                                          ∀
                                                                                                            (smtOp :
                                                                                                              SmtTerm ->
                                                                                                                SmtTerm ->
                                                                                                                  SmtTerm)
                                                                                                            (typeFn :
                                                                                                              Term ->
                                                                                                                Term ->
                                                                                                                  Term),
                                                                                                            __eo_to_smt
                                                                                                                (Term.Apply
                                                                                                                  (Term.Apply
                                                                                                                    (Term.UOp op)
                                                                                                                    x1) a) =
                                                                                                              smtOp
                                                                                                                (__eo_to_smt x1)
                                                                                                                (__eo_to_smt a) ->
                                                                                                            (term_has_non_none_type
                                                                                                                (smtOp
                                                                                                                  (__eo_to_smt x1)
                                                                                                                  (__eo_to_smt a)) ->
                                                                                                              eoHasSmtTranslation x1 ∧
                                                                                                                eoHasSmtTranslation a) ->
                                                                                                            (∀ X Y,
                                                                                                              __eo_typeof
                                                                                                                  (Term.Apply
                                                                                                                    (Term.Apply
                                                                                                                      (Term.UOp op)
                                                                                                                      X) Y) =
                                                                                                                typeFn
                                                                                                                  (__eo_typeof X)
                                                                                                                  (__eo_typeof Y)) ->
                                                                                                            (∀ Y,
                                                                                                              typeFn Term.Stuck Y =
                                                                                                                Term.Stuck) ->
                                                                                                            (∀ X,
                                                                                                              typeFn X Term.Stuck =
                                                                                                                Term.Stuck) ->
                                                                                                            __eo_typeof
                                                                                                                (__substitute_simul_rec
                                                                                                                  (Term.Boolean false)
                                                                                                                  (Term.Apply
                                                                                                                    (Term.Apply
                                                                                                                      (Term.UOp op)
                                                                                                                      x1) a)
                                                                                                                  xs ss bvs) =
                                                                                                              __eo_typeof
                                                                                                                (Term.Apply
                                                                                                                  (Term.Apply
                                                                                                                    (Term.UOp op)
                                                                                                                    x1) a) := by
                                                                                                        intro smtOp typeFn hTranslate
                                                                                                          hArgs hTypeFn hTypeFnStuckLeft
                                                                                                          hTypeFnStuckRight
                                                                                                        exact
                                                                                                          hCurrentBin typeFn
                                                                                                            (fun h =>
                                                                                                              apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
                                                                                                                hTranslate hArgs h)
                                                                                                            hTypeFn hTypeFnStuckLeft
                                                                                                            hTypeFnStuckRight
                                                                                                      have hCurrentBvBin :
                                                                                                          ∀
                                                                                                            (smtOp :
                                                                                                              SmtTerm ->
                                                                                                                SmtTerm ->
                                                                                                                  SmtTerm),
                                                                                                            __eo_to_smt
                                                                                                                (Term.Apply
                                                                                                                  (Term.Apply
                                                                                                                    (Term.UOp op)
                                                                                                                    x1) a) =
                                                                                                              smtOp
                                                                                                                (__eo_to_smt x1)
                                                                                                                (__eo_to_smt a) ->
                                                                                                            (term_has_non_none_type
                                                                                                                (smtOp
                                                                                                                  (__eo_to_smt x1)
                                                                                                                  (__eo_to_smt a)) ->
                                                                                                              eoHasSmtTranslation x1 ∧
                                                                                                                eoHasSmtTranslation a) ->
                                                                                                            (∀ X Y,
                                                                                                              __eo_typeof
                                                                                                                  (Term.Apply
                                                                                                                    (Term.Apply
                                                                                                                      (Term.UOp op)
                                                                                                                      X) Y) =
                                                                                                                __eo_typeof_bvand
                                                                                                                  (__eo_typeof X)
                                                                                                                  (__eo_typeof Y)) ->
                                                                                                            __eo_typeof
                                                                                                                (__substitute_simul_rec
                                                                                                                  (Term.Boolean false)
                                                                                                                  (Term.Apply
                                                                                                                    (Term.Apply
                                                                                                                      (Term.UOp op)
                                                                                                                      x1) a)
                                                                                                                  xs ss bvs) =
                                                                                                              __eo_typeof
                                                                                                                (Term.Apply
                                                                                                                  (Term.Apply
                                                                                                                    (Term.UOp op)
                                                                                                                    x1) a) := by
                                                                                                        intro smtOp hTranslate hArgs hTypeFn
                                                                                                        exact
                                                                                                          hCurrentSmtBin smtOp
                                                                                                            __eo_typeof_bvand hTranslate
                                                                                                            hArgs
                                                                                                            hTypeFn
                                                                                                            eo_typeof_bvand_stuck_left
                                                                                                            eo_typeof_bvand_stuck_right
                                                                                                      have hCurrentBvRetBool :
                                                                                                          ∀
                                                                                                            (smtOp :
                                                                                                              SmtTerm ->
                                                                                                                SmtTerm ->
                                                                                                                  SmtTerm),
                                                                                                            __eo_to_smt
                                                                                                                (Term.Apply
                                                                                                                  (Term.Apply
                                                                                                                    (Term.UOp op)
                                                                                                                    x1) a) =
                                                                                                              smtOp
                                                                                                                (__eo_to_smt x1)
                                                                                                                (__eo_to_smt a) ->
                                                                                                            (term_has_non_none_type
                                                                                                                (smtOp
                                                                                                                  (__eo_to_smt x1)
                                                                                                                  (__eo_to_smt a)) ->
                                                                                                              eoHasSmtTranslation x1 ∧
                                                                                                                eoHasSmtTranslation a) ->
                                                                                                            (∀ X Y,
                                                                                                              __eo_typeof
                                                                                                                  (Term.Apply
                                                                                                                    (Term.Apply
                                                                                                                      (Term.UOp op)
                                                                                                                      X) Y) =
                                                                                                                __eo_typeof_bvult
                                                                                                                  (__eo_typeof X)
                                                                                                                  (__eo_typeof Y)) ->
                                                                                                            __eo_typeof
                                                                                                                (__substitute_simul_rec
                                                                                                                  (Term.Boolean false)
                                                                                                                  (Term.Apply
                                                                                                                    (Term.Apply
                                                                                                                      (Term.UOp op)
                                                                                                                      x1) a)
                                                                                                                  xs ss bvs) =
                                                                                                              __eo_typeof
                                                                                                                (Term.Apply
                                                                                                                  (Term.Apply
                                                                                                                    (Term.UOp op)
                                                                                                                    x1) a) := by
                                                                                                        intro smtOp hTranslate hArgs hTypeFn
                                                                                                        exact
                                                                                                          hCurrentSmtBin smtOp
                                                                                                            __eo_typeof_bvult hTranslate
                                                                                                            hArgs
                                                                                                            hTypeFn
                                                                                                            eo_typeof_bvult_stuck_left
                                                                                                            eo_typeof_bvult_stuck_right
                                                                                                      by_cases hAnd : op = UserOp.and
                                                                                                      · subst op
                                                                                                        exact
                                                                                                          hCurrentBin __eo_typeof_or
                                                                                                            (fun h =>
                                                                                                              and_args_have_smt_translation_of_has_smt_translation h)
                                                                                                            (fun X Y => by
                                                                                                              change
                                                                                                                __eo_typeof_or
                                                                                                                    (__eo_typeof X)
                                                                                                                    (__eo_typeof Y) =
                                                                                                                  __eo_typeof_or
                                                                                                                    (__eo_typeof X)
                                                                                                                    (__eo_typeof Y)
                                                                                                              rfl)
                                                                                                            (by intro Y; cases Y <;> rfl)
                                                                                                            (by intro X; cases X <;> rfl)
                                                                                                      · by_cases hOr : op = UserOp.or
                                                                                                        · subst op
                                                                                                          exact
                                                                                                            hCurrentBin __eo_typeof_or
                                                                                                              (fun h =>
                                                                                                                or_args_have_smt_translation_of_has_smt_translation h)
                                                                                                              (fun X Y => by
                                                                                                                change
                                                                                                                  __eo_typeof_or
                                                                                                                      (__eo_typeof X)
                                                                                                                      (__eo_typeof Y) =
                                                                                                                    __eo_typeof_or
                                                                                                                      (__eo_typeof X)
                                                                                                                      (__eo_typeof Y)
                                                                                                                rfl)
                                                                                                              (by intro Y; cases Y <;> rfl)
                                                                                                              (by intro X; cases X <;> rfl)
                                                                                                        · by_cases hImp : op = UserOp.imp
                                                                                                          · subst op
                                                                                                            exact
                                                                                                              hCurrentBin __eo_typeof_or
                                                                                                                (fun h =>
                                                                                                                  imp_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                (fun X Y => by
                                                                                                                  change
                                                                                                                    __eo_typeof_or
                                                                                                                        (__eo_typeof X)
                                                                                                                        (__eo_typeof Y) =
                                                                                                                      __eo_typeof_or
                                                                                                                        (__eo_typeof X)
                                                                                                                        (__eo_typeof Y)
                                                                                                                  rfl)
                                                                                                                (by intro Y; cases Y <;> rfl)
                                                                                                                (by intro X; cases X <;> rfl)
                                                                                                          · by_cases hXor :
                                                                                                              op = UserOp.xor
                                                                                                            · subst op
                                                                                                              exact
                                                                                                                hCurrentBin __eo_typeof_or
                                                                                                                  (fun h =>
                                                                                                                    xor_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                  (fun X Y => by
                                                                                                                    change
                                                                                                                      __eo_typeof_or
                                                                                                                          (__eo_typeof X)
                                                                                                                          (__eo_typeof Y) =
                                                                                                                        __eo_typeof_or
                                                                                                                          (__eo_typeof X)
                                                                                                                          (__eo_typeof Y)
                                                                                                                    rfl)
                                                                                                                  (by intro Y; cases Y <;> rfl)
                                                                                                                  (by intro X; cases X <;> rfl)
                                                                                                            · by_cases hEq :
                                                                                                                op = UserOp.eq
                                                                                                              · subst op
                                                                                                                exact
                                                                                                                  hCurrentBin __eo_typeof_eq
                                                                                                                    (fun h =>
                                                                                                                      eq_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                    (fun X Y => by
                                                                                                                      change
                                                                                                                        __eo_typeof_eq
                                                                                                                            (__eo_typeof X)
                                                                                                                            (__eo_typeof Y) =
                                                                                                                          __eo_typeof_eq
                                                                                                                            (__eo_typeof X)
                                                                                                                            (__eo_typeof Y)
                                                                                                                      rfl)
                                                                                                                    (by intro Y; cases Y <;> rfl)
                                                                                                                    (by intro X; cases X <;> rfl)
                                                                                                              · by_cases hPlus :
                                                                                                                  op = UserOp.plus
                                                                                                                · subst op
                                                                                                                  exact
                                                                                                                    hCurrentBin __eo_typeof_plus
                                                                                                                      (fun h =>
                                                                                                                        plus_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                      (fun X Y => by
                                                                                                                        change
                                                                                                                          __eo_typeof_plus
                                                                                                                              (__eo_typeof X)
                                                                                                                              (__eo_typeof Y) =
                                                                                                                            __eo_typeof_plus
                                                                                                                              (__eo_typeof X)
                                                                                                                              (__eo_typeof Y)
                                                                                                                        rfl)
                                                                                                                      (by intro Y; cases Y <;> rfl)
                                                                                                                      (by intro X; cases X <;> rfl)
                                                                                                                · by_cases hNeg :
                                                                                                                    op = UserOp.neg
                                                                                                                  · subst op
                                                                                                                    exact
                                                                                                                      hCurrentBin __eo_typeof_plus
                                                                                                                        (fun h =>
                                                                                                                          neg_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                        (fun X Y => by
                                                                                                                          change
                                                                                                                            __eo_typeof_plus
                                                                                                                                (__eo_typeof X)
                                                                                                                                (__eo_typeof Y) =
                                                                                                                              __eo_typeof_plus
                                                                                                                                (__eo_typeof X)
                                                                                                                                (__eo_typeof Y)
                                                                                                                          rfl)
                                                                                                                        (by intro Y; cases Y <;> rfl)
                                                                                                                        (by intro X; cases X <;> rfl)
                                                                                                                  · by_cases hMult :
                                                                                                                      op = UserOp.mult
                                                                                                                    · subst op
                                                                                                                      exact
                                                                                                                        hCurrentBin __eo_typeof_plus
                                                                                                                          (fun h =>
                                                                                                                            mult_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                          (fun X Y => by
                                                                                                                            change
                                                                                                                              __eo_typeof_plus
                                                                                                                                  (__eo_typeof X)
                                                                                                                                  (__eo_typeof Y) =
                                                                                                                                __eo_typeof_plus
                                                                                                                                  (__eo_typeof X)
                                                                                                                                  (__eo_typeof Y)
                                                                                                                            rfl)
                                                                                                                          (by intro Y; cases Y <;> rfl)
                                                                                                                          (by intro X; cases X <;> rfl)
                                                                                                                    · by_cases hLt :
                                                                                                                        op = UserOp.lt
                                                                                                                      · subst op
                                                                                                                        exact
                                                                                                                          hCurrentBin __eo_typeof_lt
                                                                                                                            (fun h =>
                                                                                                                              lt_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                            (fun X Y => by
                                                                                                                              change
                                                                                                                                __eo_typeof_lt
                                                                                                                                    (__eo_typeof X)
                                                                                                                                    (__eo_typeof Y) =
                                                                                                                                  __eo_typeof_lt
                                                                                                                                    (__eo_typeof X)
                                                                                                                                    (__eo_typeof Y)
                                                                                                                              rfl)
                                                                                                                            (by intro Y; cases Y <;> rfl)
                                                                                                                            (by intro X; cases X <;> rfl)
                                                                                                                      · by_cases hLeq :
                                                                                                                          op = UserOp.leq
                                                                                                                        · subst op
                                                                                                                          exact
                                                                                                                            hCurrentBin __eo_typeof_lt
                                                                                                                              (fun h =>
                                                                                                                                leq_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                              (fun X Y => by
                                                                                                                                change
                                                                                                                                  __eo_typeof_lt
                                                                                                                                      (__eo_typeof X)
                                                                                                                                      (__eo_typeof Y) =
                                                                                                                                    __eo_typeof_lt
                                                                                                                                      (__eo_typeof X)
                                                                                                                                      (__eo_typeof Y)
                                                                                                                                rfl)
                                                                                                                              (by intro Y; cases Y <;> rfl)
                                                                                                                              (by intro X; cases X <;> rfl)
                                                                                                                        · by_cases hGt :
                                                                                                                            op = UserOp.gt
                                                                                                                          · subst op
                                                                                                                            exact
                                                                                                                              hCurrentBin __eo_typeof_lt
                                                                                                                                (fun h =>
                                                                                                                                  gt_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                (fun X Y => by
                                                                                                                                  change
                                                                                                                                    __eo_typeof_lt
                                                                                                                                        (__eo_typeof X)
                                                                                                                                        (__eo_typeof Y) =
                                                                                                                                      __eo_typeof_lt
                                                                                                                                        (__eo_typeof X)
                                                                                                                                        (__eo_typeof Y)
                                                                                                                                  rfl)
                                                                                                                                (by intro Y; cases Y <;> rfl)
                                                                                                                                (by intro X; cases X <;> rfl)
                                                                                                                          · by_cases hGeq :
                                                                                                                              op = UserOp.geq
                                                                                                                            · subst op
                                                                                                                              exact
                                                                                                                                hCurrentBin __eo_typeof_lt
                                                                                                                                  (fun h =>
                                                                                                                                    geq_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                  (fun X Y => by
                                                                                                                                    change
                                                                                                                                      __eo_typeof_lt
                                                                                                                                          (__eo_typeof X)
                                                                                                                                          (__eo_typeof Y) =
                                                                                                                                        __eo_typeof_lt
                                                                                                                                          (__eo_typeof X)
                                                                                                                                          (__eo_typeof Y)
                                                                                                                                    rfl)
                                                                                                                                  (by intro Y; cases Y <;> rfl)
                                                                                                                                  (by intro X; cases X <;> rfl)
                                                                                                                            · by_cases hDiv :
                                                                                                                                op = UserOp.div
                                                                                                                              · subst op
                                                                                                                                exact
                                                                                                                                  hCurrentBin __eo_typeof_div
                                                                                                                                    (fun h =>
                                                                                                                                      div_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                    (fun X Y => by
                                                                                                                                      change
                                                                                                                                        __eo_typeof_div
                                                                                                                                            (__eo_typeof X)
                                                                                                                                            (__eo_typeof Y) =
                                                                                                                                          __eo_typeof_div
                                                                                                                                            (__eo_typeof X)
                                                                                                                                            (__eo_typeof Y)
                                                                                                                                      rfl)
                                                                                                                                    eo_typeof_div_stuck_left
                                                                                                                                    eo_typeof_div_stuck_right
                                                                                                                              · by_cases hMod :
                                                                                                                                  op = UserOp.mod
                                                                                                                                · subst op
                                                                                                                                  exact
                                                                                                                                    hCurrentBin __eo_typeof_div
                                                                                                                                      (fun h =>
                                                                                                                                        mod_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                      (fun X Y => by
                                                                                                                                        change
                                                                                                                                          __eo_typeof_div
                                                                                                                                              (__eo_typeof X)
                                                                                                                                              (__eo_typeof Y) =
                                                                                                                                            __eo_typeof_div
                                                                                                                                              (__eo_typeof X)
                                                                                                                                              (__eo_typeof Y)
                                                                                                                                        rfl)
                                                                                                                                      eo_typeof_div_stuck_left
                                                                                                                                      eo_typeof_div_stuck_right
                                                                                                                                · by_cases hMultmult :
                                                                                                                                    op = UserOp.multmult
                                                                                                                                  · subst op
                                                                                                                                    exact
                                                                                                                                      hCurrentBin __eo_typeof_div
                                                                                                                                        (fun h =>
                                                                                                                                          multmult_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                        (fun X Y => by
                                                                                                                                          change
                                                                                                                                            __eo_typeof_div
                                                                                                                                                (__eo_typeof X)
                                                                                                                                                (__eo_typeof Y) =
                                                                                                                                              __eo_typeof_div
                                                                                                                                                (__eo_typeof X)
                                                                                                                                                (__eo_typeof Y)
                                                                                                                                          rfl)
                                                                                                                                        eo_typeof_div_stuck_left
                                                                                                                                        eo_typeof_div_stuck_right
                                                                                                                                  · by_cases hDivisible :
                                                                                                                                      op = UserOp.divisible
                                                                                                                                    · subst op
                                                                                                                                      exact
                                                                                                                                        hCurrentBin __eo_typeof_divisible
                                                                                                                                          (fun h =>
                                                                                                                                            divisible_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                          (fun X Y => by
                                                                                                                                            change
                                                                                                                                              __eo_typeof_divisible
                                                                                                                                                  (__eo_typeof X)
                                                                                                                                                  (__eo_typeof Y) =
                                                                                                                                                __eo_typeof_divisible
                                                                                                                                                  (__eo_typeof X)
                                                                                                                                                  (__eo_typeof Y)
                                                                                                                                            rfl)
                                                                                                                                          eo_typeof_divisible_stuck_left
                                                                                                                                          eo_typeof_divisible_stuck_right
                                                                                                                                    · by_cases hDivTotal :
                                                                                                                                        op = UserOp.div_total
                                                                                                                                      · subst op
                                                                                                                                        exact
                                                                                                                                          hCurrentBin __eo_typeof_div
                                                                                                                                            (fun h =>
                                                                                                                                              div_total_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                            (fun X Y => by
                                                                                                                                              change
                                                                                                                                                __eo_typeof_div
                                                                                                                                                    (__eo_typeof X)
                                                                                                                                                    (__eo_typeof Y) =
                                                                                                                                                  __eo_typeof_div
                                                                                                                                                    (__eo_typeof X)
                                                                                                                                                    (__eo_typeof Y)
                                                                                                                                              rfl)
                                                                                                                                            eo_typeof_div_stuck_left
                                                                                                                                            eo_typeof_div_stuck_right
                                                                                                                                      · by_cases hModTotal :
                                                                                                                                          op = UserOp.mod_total
                                                                                                                                        · subst op
                                                                                                                                          exact
                                                                                                                                            hCurrentBin __eo_typeof_div
                                                                                                                                              (fun h =>
                                                                                                                                                mod_total_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                              (fun X Y => by
                                                                                                                                                change
                                                                                                                                                  __eo_typeof_div
                                                                                                                                                      (__eo_typeof X)
                                                                                                                                                      (__eo_typeof Y) =
                                                                                                                                                    __eo_typeof_div
                                                                                                                                                      (__eo_typeof X)
                                                                                                                                                      (__eo_typeof Y)
                                                                                                                                                rfl)
                                                                                                                                              eo_typeof_div_stuck_left
                                                                                                                                              eo_typeof_div_stuck_right
                                                                                                                                        · by_cases hMultmultTotal :
                                                                                                                                            op = UserOp.multmult_total
                                                                                                                                          · subst op
                                                                                                                                            exact
                                                                                                                                              hCurrentBin __eo_typeof_div
                                                                                                                                                (fun h =>
                                                                                                                                                  multmult_total_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                (fun X Y => by
                                                                                                                                                  change
                                                                                                                                                    __eo_typeof_div
                                                                                                                                                        (__eo_typeof X)
                                                                                                                                                        (__eo_typeof Y) =
                                                                                                                                                      __eo_typeof_div
                                                                                                                                                        (__eo_typeof X)
                                                                                                                                                        (__eo_typeof Y)
                                                                                                                                                  rfl)
                                                                                                                                                eo_typeof_div_stuck_left
                                                                                                                                                eo_typeof_div_stuck_right
                                                                                                                                          · by_cases hSelect :
                                                                                                                                              op = UserOp.select
                                                                                                                                            · subst op
                                                                                                                                              exact
                                                                                                                                                hCurrentBin __eo_typeof_select
                                                                                                                                                  (fun h =>
                                                                                                                                                    select_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                  (fun X Y => by
                                                                                                                                                    rfl)
                                                                                                                                                  eo_typeof_select_stuck_left
                                                                                                                                                  eo_typeof_select_stuck_right
                                                                                                                                            · by_cases hArrayDeq :
                                                                                                                                                op = UserOp._at_array_deq_diff
                                                                                                                                              · subst op
                                                                                                                                                exact
                                                                                                                                                  hCurrentBin __eo_typeof__at_array_deq_diff
                                                                                                                                                    (fun h =>
                                                                                                                                                      array_deq_diff_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                    (fun X Y => by
                                                                                                                                                      rfl)
                                                                                                                                                    eo_typeof_array_deq_diff_stuck_left
                                                                                                                                                    eo_typeof_array_deq_diff_stuck_right
                                                                                                                                              · by_cases hStringsDeq :
                                                                                                                                                  op = UserOp._at_strings_deq_diff
                                                                                                                                                · subst op
                                                                                                                                                  exact
                                                                                                                                                    hCurrentBin __eo_typeof__at_strings_deq_diff
                                                                                                                                                      (fun h =>
                                                                                                                                                        strings_deq_diff_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                      (fun X Y => by
                                                                                                                                                        rfl)
                                                                                                                                                      eo_typeof_strings_deq_diff_stuck_left
                                                                                                                                                      eo_typeof_strings_deq_diff_stuck_right
                                                                                                                                                · by_cases hStringsStoi :
                                                                                                                                                    op = UserOp._at_strings_stoi_result
                                                                                                                                                  · subst op
                                                                                                                                                    exact
                                                                                                                                                      hCurrentBin __eo_typeof__at_strings_stoi_result
                                                                                                                                                        (fun h =>
                                                                                                                                                          strings_stoi_result_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                        (fun X Y => by
                                                                                                                                                          rfl)
                                                                                                                                                        eo_typeof_strings_stoi_result_stuck_left
                                                                                                                                                        eo_typeof_strings_stoi_result_stuck_right
                                                                                                                                                  · by_cases hStringsItos :
                                                                                                                                                      op = UserOp._at_strings_itos_result
                                                                                                                                                    · subst op
                                                                                                                                                      exact
                                                                                                                                                        hCurrentBin __eo_typeof_div
                                                                                                                                                          (fun h =>
                                                                                                                                                            strings_itos_result_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                          (fun X Y => by
                                                                                                                                                            rfl)
                                                                                                                                                          eo_typeof_div_stuck_left
                                                                                                                                                          eo_typeof_div_stuck_right
                                                                                                                                                    · by_cases hStringsNumOccur :
                                                                                                                                                        op = UserOp._at_strings_num_occur
                                                                                                                                                      · subst op
                                                                                                                                                        exact
                                                                                                                                                          hCurrentBin __eo_typeof__at_strings_deq_diff
                                                                                                                                                            (fun h =>
                                                                                                                                                              strings_num_occur_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                            (fun X Y => by
                                                                                                                                                              rfl)
                                                                                                                                                            eo_typeof_strings_deq_diff_stuck_left
                                                                                                                                                            eo_typeof_strings_deq_diff_stuck_right
                                                                                                                                                      · by_cases hTuple :
                                                                                                                                                          op = UserOp.tuple
                                                                                                                                                        · subst op
                                                                                                                                                          exact
                                                                                                                                                            hCurrentBin __eo_typeof_tuple
                                                                                                                                                              (fun h =>
                                                                                                                                                                tuple_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                              (fun X Y => by
                                                                                                                                                                rfl)
                                                                                                                                                              eo_typeof_tuple_stuck_left
                                                                                                                                                              eo_typeof_tuple_stuck_right
                                                                                                                                                        · by_cases hSetsDeq :
                                                                                                                                                            op = UserOp._at_sets_deq_diff
                                                                                                                                                          · subst op
                                                                                                                                                            exact
                                                                                                                                                              hCurrentBin __eo_typeof__at_sets_deq_diff
                                                                                                                                                                (fun h =>
                                                                                                                                                                  sets_deq_diff_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                (fun X Y => by
                                                                                                                                                                  rfl)
                                                                                                                                                                eo_typeof_sets_deq_diff_stuck_left
                                                                                                                                                                eo_typeof_sets_deq_diff_stuck_right
                                                                                                                                                          · by_cases hQdiv :
                                                                                                                                                              op = UserOp.qdiv
                                                                                                                                                            · subst op
                                                                                                                                                              exact
                                                                                                                                                                hCurrentBin __eo_typeof_qdiv
                                                                                                                                                                  (fun h =>
                                                                                                                                                                    qdiv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                  (fun X Y => by
                                                                                                                                                                    rfl)
                                                                                                                                                                  eo_typeof_qdiv_stuck_left
                                                                                                                                                                  eo_typeof_qdiv_stuck_right
                                                                                                                                                            · by_cases hQdivTotal :
                                                                                                                                                                op = UserOp.qdiv_total
                                                                                                                                                              · subst op
                                                                                                                                                                exact
                                                                                                                                                                  hCurrentBin __eo_typeof_qdiv
                                                                                                                                                                    (fun h =>
                                                                                                                                                                      qdiv_total_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                    (fun X Y => by
                                                                                                                                                                      rfl)
                                                                                                                                                                    eo_typeof_qdiv_stuck_left
                                                                                                                                                                    eo_typeof_qdiv_stuck_right
                                                                                                                                                              · by_cases hConcat :
                                                                                                                                                                  op = UserOp.concat
                                                                                                                                                                · subst op
                                                                                                                                                                  exact
                                                                                                                                                                    hCurrentSmtBin
                                                                                                                                                                      SmtTerm.concat
                                                                                                                                                                      __eo_typeof_concat
                                                                                                                                                                      (by rfl)
                                                                                                                                                                      bv_concat_args_have_smt_translation_of_non_none
                                                                                                                                                                      (fun X Y => by
                                                                                                                                                                        rfl)
                                                                                                                                                                      eo_typeof_concat_stuck_left
                                                                                                                                                                      eo_typeof_concat_stuck_right
                                                                                                                                                                · by_cases hBvand :
                                                                                                                                                                    op = UserOp.bvand
                                                                                                                                                                  · subst op
                                                                                                                                                                    exact
                                                                                                                                                                      hCurrentSmtBin
                                                                                                                                                                        SmtTerm.bvand
                                                                                                                                                                        __eo_typeof_bvand
                                                                                                                                                                        (by rfl)
                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                          bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                            (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                            hNN)
                                                                                                                                                                        (fun X Y => by
                                                                                                                                                                          rfl)
                                                                                                                                                                        eo_typeof_bvand_stuck_left
                                                                                                                                                                        eo_typeof_bvand_stuck_right
                                                                                                                                                                  · by_cases hBvor :
                                                                                                                                                                      op = UserOp.bvor
                                                                                                                                                                    · subst op
                                                                                                                                                                      exact
                                                                                                                                                                        hCurrentSmtBin
                                                                                                                                                                          SmtTerm.bvor
                                                                                                                                                                          __eo_typeof_bvand
                                                                                                                                                                          (by rfl)
                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                            bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                              (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                              hNN)
                                                                                                                                                                          (fun X Y => by
                                                                                                                                                                            rfl)
                                                                                                                                                                          eo_typeof_bvand_stuck_left
                                                                                                                                                                          eo_typeof_bvand_stuck_right
                                                                                                                                                                    · by_cases hBvnand :
                                                                                                                                                                        op = UserOp.bvnand
                                                                                                                                                                      · subst op
                                                                                                                                                                        exact
                                                                                                                                                                          hCurrentSmtBin
                                                                                                                                                                            SmtTerm.bvnand
                                                                                                                                                                            __eo_typeof_bvand
                                                                                                                                                                            (by rfl)
                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                              bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                hNN)
                                                                                                                                                                            (fun X Y => by
                                                                                                                                                                              rfl)
                                                                                                                                                                            eo_typeof_bvand_stuck_left
                                                                                                                                                                            eo_typeof_bvand_stuck_right
                                                                                                                                                                      · by_cases hBvnor :
                                                                                                                                                                          op = UserOp.bvnor
                                                                                                                                                                        · subst op
                                                                                                                                                                          exact
                                                                                                                                                                            hCurrentSmtBin
                                                                                                                                                                              SmtTerm.bvnor
                                                                                                                                                                              __eo_typeof_bvand
                                                                                                                                                                              (by rfl)
                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                  (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                  hNN)
                                                                                                                                                                              (fun X Y => by
                                                                                                                                                                                rfl)
                                                                                                                                                                              eo_typeof_bvand_stuck_left
                                                                                                                                                                              eo_typeof_bvand_stuck_right
                                                                                                                                                                        · by_cases hBvxor :
                                                                                                                                                                            op = UserOp.bvxor
                                                                                                                                                                          · subst op
                                                                                                                                                                            exact
                                                                                                                                                                              hCurrentSmtBin
                                                                                                                                                                                SmtTerm.bvxor
                                                                                                                                                                                __eo_typeof_bvand
                                                                                                                                                                                (by rfl)
                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                  bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                    (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                    hNN)
                                                                                                                                                                                (fun X Y => by
                                                                                                                                                                                  rfl)
                                                                                                                                                                                eo_typeof_bvand_stuck_left
                                                                                                                                                                                eo_typeof_bvand_stuck_right
                                                                                                                                                                          · by_cases hBvxnor :
                                                                                                                                                                              op = UserOp.bvxnor
                                                                                                                                                                            · subst op
                                                                                                                                                                              exact
                                                                                                                                                                                hCurrentSmtBin
                                                                                                                                                                                  SmtTerm.bvxnor
                                                                                                                                                                                  __eo_typeof_bvand
                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                    bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                      (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                      hNN)
                                                                                                                                                                                  (fun X Y => by
                                                                                                                                                                                    rfl)
                                                                                                                                                                                  eo_typeof_bvand_stuck_left
                                                                                                                                                                                  eo_typeof_bvand_stuck_right
                                                                                                                                                                            · by_cases hBvcomp :
                                                                                                                                                                                op = UserOp.bvcomp
                                                                                                                                                                              · subst op
                                                                                                                                                                                exact
                                                                                                                                                                                  hCurrentSmtBin
                                                                                                                                                                                    SmtTerm.bvcomp
                                                                                                                                                                                    __eo_typeof_bvcomp
                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                      bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                        (ret := SmtType.BitVec 1)
                                                                                                                                                                                        (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                        hNN)
                                                                                                                                                                                    (fun X Y => by
                                                                                                                                                                                      rfl)
                                                                                                                                                                                    eo_typeof_bvcomp_stuck_left
                                                                                                                                                                                    eo_typeof_bvcomp_stuck_right
                                                                                                                                                                              · by_cases hBvadd :
                                                                                                                                                                                  op = UserOp.bvadd
                                                                                                                                                                                · subst op
                                                                                                                                                                                  exact
                                                                                                                                                                                    hCurrentSmtBin
                                                                                                                                                                                      SmtTerm.bvadd
                                                                                                                                                                                      __eo_typeof_bvand
                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                        bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                          (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                          hNN)
                                                                                                                                                                                      (fun X Y => by
                                                                                                                                                                                        rfl)
                                                                                                                                                                                      eo_typeof_bvand_stuck_left
                                                                                                                                                                                      eo_typeof_bvand_stuck_right
                                                                                                                                                                                · by_cases hBvmul :
                                                                                                                                                                                    op = UserOp.bvmul
                                                                                                                                                                                  · subst op
                                                                                                                                                                                    exact
                                                                                                                                                                                      hCurrentSmtBin
                                                                                                                                                                                        SmtTerm.bvmul
                                                                                                                                                                                        __eo_typeof_bvand
                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                          bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                            (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                            hNN)
                                                                                                                                                                                        (fun X Y => by
                                                                                                                                                                                          rfl)
                                                                                                                                                                                        eo_typeof_bvand_stuck_left
                                                                                                                                                                                        eo_typeof_bvand_stuck_right
                                                                                                                                                                                  · by_cases hBvudiv :
                                                                                                                                                                                      op = UserOp.bvudiv
                                                                                                                                                                                    · subst op
                                                                                                                                                                                      exact hCurrentBvBin
                                                                                                                                                                                        SmtTerm.bvudiv (by rfl)
                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                          bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                            (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                            hNN)
                                                                                                                                                                                        (fun X Y => by rfl)
                                                                                                                                                                                    · by_cases hBvurem :
                                                                                                                                                                                        op = UserOp.bvurem
                                                                                                                                                                                      · subst op
                                                                                                                                                                                        exact hCurrentBvBin
                                                                                                                                                                                          SmtTerm.bvurem (by rfl)
                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                            bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                              (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                              hNN)
                                                                                                                                                                                          (fun X Y => by rfl)
                                                                                                                                                                                      · by_cases hBvsub :
                                                                                                                                                                                          op = UserOp.bvsub
                                                                                                                                                                                        · subst op
                                                                                                                                                                                          exact hCurrentBvBin
                                                                                                                                                                                            SmtTerm.bvsub (by rfl)
                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                              bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                hNN)
                                                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                                                        · by_cases hBvsdiv :
                                                                                                                                                                                            op = UserOp.bvsdiv
                                                                                                                                                                                          · subst op
                                                                                                                                                                                            exact hCurrentBvBin
                                                                                                                                                                                              SmtTerm.bvsdiv (by rfl)
                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                  (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                  hNN)
                                                                                                                                                                                              (fun X Y => by rfl)
                                                                                                                                                                                          · by_cases hBvsrem :
                                                                                                                                                                                              op = UserOp.bvsrem
                                                                                                                                                                                            · subst op
                                                                                                                                                                                              exact hCurrentBvBin
                                                                                                                                                                                                SmtTerm.bvsrem (by rfl)
                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                  bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                    (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                    hNN)
                                                                                                                                                                                                (fun X Y => by rfl)
                                                                                                                                                                                            · by_cases hBvsmod :
                                                                                                                                                                                                op = UserOp.bvsmod
                                                                                                                                                                                              · subst op
                                                                                                                                                                                                exact hCurrentBvBin
                                                                                                                                                                                                  SmtTerm.bvsmod (by rfl)
                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                    bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                      (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                      hNN)
                                                                                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                                                                              · by_cases hBvshl :
                                                                                                                                                                                                  op = UserOp.bvshl
                                                                                                                                                                                                · subst op
                                                                                                                                                                                                  exact hCurrentBvBin
                                                                                                                                                                                                    SmtTerm.bvshl (by rfl)
                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                      bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                        (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                        hNN)
                                                                                                                                                                                                    (fun X Y => by rfl)
                                                                                                                                                                                                · by_cases hBvlshr :
                                                                                                                                                                                                    op = UserOp.bvlshr
                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                    exact hCurrentBvBin
                                                                                                                                                                                                      SmtTerm.bvlshr (by rfl)
                                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                                        bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                          (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                          hNN)
                                                                                                                                                                                                      (fun X Y => by rfl)
                                                                                                                                                                                                  · by_cases hBvashr :
                                                                                                                                                                                                      op = UserOp.bvashr
                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                      exact hCurrentBvBin
                                                                                                                                                                                                        SmtTerm.bvashr (by rfl)
                                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                                          bv_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                            (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                            hNN)
                                                                                                                                                                                                        (fun X Y => by rfl)
                                                                                                                                                                                                    · by_cases hBvult :
                                                                                                                                                                                                        op = UserOp.bvult
                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                        exact hCurrentBvRetBool
                                                                                                                                                                                                          SmtTerm.bvult (by rfl)
                                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                                            bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                              (ret := SmtType.Bool)
                                                                                                                                                                                                              (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                              hNN)
                                                                                                                                                                                                          (fun X Y => by rfl)
                                                                                                                                                                                                      · by_cases hBvule :
                                                                                                                                                                                                          op = UserOp.bvule
                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                          exact hCurrentBvRetBool
                                                                                                                                                                                                            SmtTerm.bvule (by rfl)
                                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                                              bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                (ret := SmtType.Bool)
                                                                                                                                                                                                                (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                hNN)
                                                                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                                                                        · by_cases hBvugt :
                                                                                                                                                                                                            op = UserOp.bvugt
                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                            exact hCurrentBvRetBool
                                                                                                                                                                                                              SmtTerm.bvugt (by rfl)
                                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                                bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                  (ret := SmtType.Bool)
                                                                                                                                                                                                                  (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                  hNN)
                                                                                                                                                                                                              (fun X Y => by rfl)
                                                                                                                                                                                                          · by_cases hBvuge :
                                                                                                                                                                                                              op = UserOp.bvuge
                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                              exact hCurrentBvRetBool
                                                                                                                                                                                                                SmtTerm.bvuge (by rfl)
                                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                                  bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                    (ret := SmtType.Bool)
                                                                                                                                                                                                                    (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                    hNN)
                                                                                                                                                                                                                (fun X Y => by rfl)
                                                                                                                                                                                                            · by_cases hBvslt :
                                                                                                                                                                                                                op = UserOp.bvslt
                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                exact hCurrentBvRetBool
                                                                                                                                                                                                                  SmtTerm.bvslt (by rfl)
                                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                                    bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                      (ret := SmtType.Bool)
                                                                                                                                                                                                                      (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                      hNN)
                                                                                                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                                                                                              · by_cases hBvsle :
                                                                                                                                                                                                                  op = UserOp.bvsle
                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                  exact hCurrentBvRetBool
                                                                                                                                                                                                                    SmtTerm.bvsle (by rfl)
                                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                                      bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                        (ret := SmtType.Bool)
                                                                                                                                                                                                                        (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                        hNN)
                                                                                                                                                                                                                    (fun X Y => by rfl)
                                                                                                                                                                                                                · by_cases hBvsgt :
                                                                                                                                                                                                                    op = UserOp.bvsgt
                                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                                    exact hCurrentBvRetBool
                                                                                                                                                                                                                      SmtTerm.bvsgt (by rfl)
                                                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                                                        bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                          (ret := SmtType.Bool)
                                                                                                                                                                                                                          (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                          hNN)
                                                                                                                                                                                                                      (fun X Y => by rfl)
                                                                                                                                                                                                                  · by_cases hBvsge :
                                                                                                                                                                                                                      op = UserOp.bvsge
                                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                                      exact hCurrentBvRetBool
                                                                                                                                                                                                                        SmtTerm.bvsge (by rfl)
                                                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                                                          bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                            (ret := SmtType.Bool)
                                                                                                                                                                                                                            (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                            hNN)
                                                                                                                                                                                                                        (fun X Y => by rfl)
                                                                                                                                                                                                                    · by_cases hBvuaddo :
                                                                                                                                                                                                                        op = UserOp.bvuaddo
                                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                                        exact hCurrentBvRetBool
                                                                                                                                                                                                                          SmtTerm.bvuaddo (by rfl)
                                                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                                                            bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                              (ret := SmtType.Bool)
                                                                                                                                                                                                                              (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                              hNN)
                                                                                                                                                                                                                          (fun X Y => by rfl)
                                                                                                                                                                                                                      · by_cases hBvsaddo :
                                                                                                                                                                                                                          op = UserOp.bvsaddo
                                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                                          exact hCurrentBvRetBool
                                                                                                                                                                                                                            SmtTerm.bvsaddo (by rfl)
                                                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                                                              bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                (ret := SmtType.Bool)
                                                                                                                                                                                                                                (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                hNN)
                                                                                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                                                                                        · by_cases hBvumulo :
                                                                                                                                                                                                                            op = UserOp.bvumulo
                                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                                            exact hCurrentBvRetBool
                                                                                                                                                                                                                              SmtTerm.bvumulo (by rfl)
                                                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                                                bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                  (ret := SmtType.Bool)
                                                                                                                                                                                                                                  (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                  hNN)
                                                                                                                                                                                                                              (fun X Y => by rfl)
                                                                                                                                                                                                                          · by_cases hBvsmulo :
                                                                                                                                                                                                                              op = UserOp.bvsmulo
                                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                                              exact hCurrentBvRetBool
                                                                                                                                                                                                                                SmtTerm.bvsmulo (by rfl)
                                                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                                                  bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                    (ret := SmtType.Bool)
                                                                                                                                                                                                                                    (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                    hNN)
                                                                                                                                                                                                                                (fun X Y => by rfl)
                                                                                                                                                                                                                            · by_cases hBvusubo :
                                                                                                                                                                                                                                op = UserOp.bvusubo
                                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                                exact hCurrentBvRetBool
                                                                                                                                                                                                                                  SmtTerm.bvusubo (by rfl)
                                                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                                                    bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                      (ret := SmtType.Bool)
                                                                                                                                                                                                                                      (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                      hNN)
                                                                                                                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                                                                                                              · by_cases hBvssubo :
                                                                                                                                                                                                                                  op = UserOp.bvssubo
                                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                                  exact hCurrentBvRetBool
                                                                                                                                                                                                                                    SmtTerm.bvssubo (by rfl)
                                                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                                                      bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                        (ret := SmtType.Bool)
                                                                                                                                                                                                                                        (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                        hNN)
                                                                                                                                                                                                                                    (fun X Y => by rfl)
                                                                                                                                                                                                                                · by_cases hBvsdivo :
                                                                                                                                                                                                                                    op = UserOp.bvsdivo
                                                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                                                    exact hCurrentBvRetBool
                                                                                                                                                                                                                                      SmtTerm.bvsdivo (by rfl)
                                                                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                                                                        bv_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                          (ret := SmtType.Bool)
                                                                                                                                                                                                                                          (by rw [__smtx_typeof.eq_def])
                                                                                                                                                                                                                                          hNN)
                                                                                                                                                                                                                                      (fun X Y => by rfl)
                                                                                                                                                                                                                                  · by_cases hBvultbv :
                                                                                                                                                                                                                                      op = UserOp.bvultbv
                                                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                                                      exact
                                                                                                                                                                                                                                        hCurrentBin __eo_typeof_bvcomp
                                                                                                                                                                                                                                          (fun h =>
                                                                                                                                                                                                                                            bvultbv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                                          (fun X Y => by rfl)
                                                                                                                                                                                                                                          eo_typeof_bvcomp_stuck_left
                                                                                                                                                                                                                                          eo_typeof_bvcomp_stuck_right
                                                                                                                                                                                                                                    · by_cases hBvsltbv :
                                                                                                                                                                                                                                        op = UserOp.bvsltbv
                                                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                                                        exact
                                                                                                                                                                                                                                          hCurrentBin __eo_typeof_bvcomp
                                                                                                                                                                                                                                            (fun h =>
                                                                                                                                                                                                                                              bvsltbv_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                                                                                                            eo_typeof_bvcomp_stuck_left
                                                                                                                                                                                                                                            eo_typeof_bvcomp_stuck_right
                                                                                                                                                                                                                                      · by_cases hFromBools :
                                                                                                                                                                                                                                          op = UserOp._at_from_bools
                                                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                                                          exact
                                                                                                                                                                                                                                            hCurrentBin __eo_typeof__at_from_bools
                                                                                                                                                                                                                                              (fun h =>
                                                                                                                                                                                                                                                from_bools_args_have_smt_translation_of_has_smt_translation h)
                                                                                                                                                                                                                                              (fun X Y => by rfl)
                                                                                                                                                                                                                                              eo_typeof_from_bools_stuck_left
                                                                                                                                                                                                                                              eo_typeof_from_bools_stuck_right
                                                                                                                                                                                                                                        · by_cases hStrConcat :
                                                                                                                                                                                                                                            op = UserOp.str_concat
                                                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                                                            exact
                                                                                                                                                                                                                                              hCurrentSmtBin
                                                                                                                                                                                                                                                SmtTerm.str_concat
                                                                                                                                                                                                                                                __eo_typeof_str_concat
                                                                                                                                                                                                                                                (by rfl)
                                                                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                                                                  seq_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                    (typeof_str_concat_eq
                                                                                                                                                                                                                                                      (__eo_to_smt x1)
                                                                                                                                                                                                                                                      (__eo_to_smt a))
                                                                                                                                                                                                                                                    hNN)
                                                                                                                                                                                                                                                (fun X Y => by rfl)
                                                                                                                                                                                                                                                (by intro Y; rfl)
                                                                                                                                                                                                                                                (by
                                                                                                                                                                                                                                                  intro X
                                                                                                                                                                                                                                                  cases X <;> try rfl
                                                                                                                                                                                                                                                  case Apply f x =>
                                                                                                                                                                                                                                                    cases f <;> try rfl
                                                                                                                                                                                                                                                    case UOp op =>
                                                                                                                                                                                                                                                      cases op <;> rfl)
                                                                                                                                                                                                                                          · by_cases hStrContains :
                                                                                                                                                                                                                                              op = UserOp.str_contains
                                                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                                                              exact
                                                                                                                                                                                                                                                hCurrentSmtBin
                                                                                                                                                                                                                                                  SmtTerm.str_contains
                                                                                                                                                                                                                                                  __eo_typeof_str_contains
                                                                                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                                                                    seq_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                      (ret := SmtType.Bool)
                                                                                                                                                                                                                                                      (typeof_str_contains_eq
                                                                                                                                                                                                                                                        (__eo_to_smt x1)
                                                                                                                                                                                                                                                        (__eo_to_smt a))
                                                                                                                                                                                                                                                      hNN)
                                                                                                                                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                                                                                                                                  (by intro Y; rfl)
                                                                                                                                                                                                                                                  (by
                                                                                                                                                                                                                                                    intro X
                                                                                                                                                                                                                                                    cases X <;> try rfl
                                                                                                                                                                                                                                                    case Apply f x =>
                                                                                                                                                                                                                                                      cases f <;> try rfl
                                                                                                                                                                                                                                                      case UOp op =>
                                                                                                                                                                                                                                                        cases op <;> rfl)
                                                                                                                                                                                                                                            · by_cases hStrAt :
                                                                                                                                                                                                                                                op = UserOp.str_at
                                                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                                                exact
                                                                                                                                                                                                                                                  hCurrentSmtBin
                                                                                                                                                                                                                                                    SmtTerm.str_at
                                                                                                                                                                                                                                                    __eo_typeof_str_at
                                                                                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                                                                      str_at_args_have_smt_translation_of_non_none hNN)
                                                                                                                                                                                                                                                    (fun X Y => by rfl)
                                                                                                                                                                                                                                                    (by intro Y; rfl)
                                                                                                                                                                                                                                                    (by
                                                                                                                                                                                                                                                      intro X
                                                                                                                                                                                                                                                      cases X <;> try rfl
                                                                                                                                                                                                                                                      case Apply f x =>
                                                                                                                                                                                                                                                        cases f <;> try rfl
                                                                                                                                                                                                                                                        case UOp op =>
                                                                                                                                                                                                                                                          cases op <;> rfl)
                                                                                                                                                                                                                                              · by_cases hStrPrefixof :
                                                                                                                                                                                                                                                  op = UserOp.str_prefixof
                                                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                                                  exact
                                                                                                                                                                                                                                                    hCurrentSmtBin
                                                                                                                                                                                                                                                      SmtTerm.str_prefixof
                                                                                                                                                                                                                                                      __eo_typeof_str_contains
                                                                                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                                                                                        seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                          (ret := SmtType.Bool)
                                                                                                                                                                                                                                                          (typeof_str_prefixof_eq
                                                                                                                                                                                                                                                            (__eo_to_smt x1)
                                                                                                                                                                                                                                                            (__eo_to_smt a))
                                                                                                                                                                                                                                                          hNN)
                                                                                                                                                                                                                                                      (fun X Y => by rfl)
                                                                                                                                                                                                                                                      (by intro Y; rfl)
                                                                                                                                                                                                                                                      (by
                                                                                                                                                                                                                                                        intro X
                                                                                                                                                                                                                                                        cases X <;> try rfl
                                                                                                                                                                                                                                                        case Apply f x =>
                                                                                                                                                                                                                                                          cases f <;> try rfl
                                                                                                                                                                                                                                                          case UOp op =>
                                                                                                                                                                                                                                                            cases op <;> rfl)
                                                                                                                                                                                                                                                · by_cases hStrSuffixof :
                                                                                                                                                                                                                                                    op = UserOp.str_suffixof
                                                                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                                                                    exact
                                                                                                                                                                                                                                                      hCurrentSmtBin
                                                                                                                                                                                                                                                        SmtTerm.str_suffixof
                                                                                                                                                                                                                                                        __eo_typeof_str_contains
                                                                                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                                                                                          seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                            (ret := SmtType.Bool)
                                                                                                                                                                                                                                                            (typeof_str_suffixof_eq
                                                                                                                                                                                                                                                              (__eo_to_smt x1)
                                                                                                                                                                                                                                                              (__eo_to_smt a))
                                                                                                                                                                                                                                                            hNN)
                                                                                                                                                                                                                                                        (fun X Y => by rfl)
                                                                                                                                                                                                                                                        (by intro Y; rfl)
                                                                                                                                                                                                                                                        (by
                                                                                                                                                                                                                                                          intro X
                                                                                                                                                                                                                                                          cases X <;> try rfl
                                                                                                                                                                                                                                                          case Apply f x =>
                                                                                                                                                                                                                                                            cases f <;> try rfl
                                                                                                                                                                                                                                                            case UOp op =>
                                                                                                                                                                                                                                                              cases op <;> rfl)
                                                                                                                                                                                                                                                  · by_cases hStrLt :
                                                                                                                                                                                                                                                      op = UserOp.str_lt
                                                                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                                                                      exact
                                                                                                                                                                                                                                                        hCurrentSmtBin
                                                                                                                                                                                                                                                          SmtTerm.str_lt
                                                                                                                                                                                                                                                          __eo_typeof_str_lt
                                                                                                                                                                                                                                                          (by rfl)
                                                                                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                                                                                            seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                              (ret := SmtType.Bool)
                                                                                                                                                                                                                                                              (typeof_str_lt_eq
                                                                                                                                                                                                                                                                (__eo_to_smt x1)
                                                                                                                                                                                                                                                                (__eo_to_smt a))
                                                                                                                                                                                                                                                              hNN)
                                                                                                                                                                                                                                                          (fun X Y => by rfl)
                                                                                                                                                                                                                                                          (by intro Y; rfl)
                                                                                                                                                                                                                                                          (by
                                                                                                                                                                                                                                                            intro X
                                                                                                                                                                                                                                                            cases X <;> try rfl
                                                                                                                                                                                                                                                            case Apply f x =>
                                                                                                                                                                                                                                                              cases f <;> try rfl
                                                                                                                                                                                                                                                              case UOp op =>
                                                                                                                                                                                                                                                                cases op <;> try rfl
                                                                                                                                                                                                                                                                case Seq =>
                                                                                                                                                                                                                                                                  cases x <;> try rfl
                                                                                                                                                                                                                                                                  case UOp op =>
                                                                                                                                                                                                                                                                    cases op <;> rfl)
                                                                                                                                                                                                                                                    · by_cases hStrLeq :
                                                                                                                                                                                                                                                        op = UserOp.str_leq
                                                                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                                                                        exact
                                                                                                                                                                                                                                                          hCurrentSmtBin
                                                                                                                                                                                                                                                            SmtTerm.str_leq
                                                                                                                                                                                                                                                            __eo_typeof_str_lt
                                                                                                                                                                                                                                                            (by rfl)
                                                                                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                                                                                              seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                (ret := SmtType.Bool)
                                                                                                                                                                                                                                                                (typeof_str_leq_eq
                                                                                                                                                                                                                                                                  (__eo_to_smt x1)
                                                                                                                                                                                                                                                                  (__eo_to_smt a))
                                                                                                                                                                                                                                                                hNN)
                                                                                                                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                                                                                                                            (by intro Y; rfl)
                                                                                                                                                                                                                                                            (by
                                                                                                                                                                                                                                                              intro X
                                                                                                                                                                                                                                                              cases X <;> try rfl
                                                                                                                                                                                                                                                              case Apply f x =>
                                                                                                                                                                                                                                                                cases f <;> try rfl
                                                                                                                                                                                                                                                                case UOp op =>
                                                                                                                                                                                                                                                                  cases op <;> try rfl
                                                                                                                                                                                                                                                                  case Seq =>
                                                                                                                                                                                                                                                                    cases x <;> try rfl
                                                                                                                                                                                                                                                                    case UOp op =>
                                                                                                                                                                                                                                                                      cases op <;> rfl)
                                                                                                                                                                                                                                                      · by_cases hReRange :
                                                                                                                                                                                                                                                          op = UserOp.re_range
                                                                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                                                                          exact
                                                                                                                                                                                                                                                            hCurrentSmtBin
                                                                                                                                                                                                                                                              SmtTerm.re_range
                                                                                                                                                                                                                                                              __eo_typeof_re_range
                                                                                                                                                                                                                                                              (by rfl)
                                                                                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                                                                                seq_char_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                  (ret := SmtType.RegLan)
                                                                                                                                                                                                                                                                  (typeof_re_range_eq
                                                                                                                                                                                                                                                                    (__eo_to_smt x1)
                                                                                                                                                                                                                                                                    (__eo_to_smt a))
                                                                                                                                                                                                                                                                  hNN)
                                                                                                                                                                                                                                                              (fun X Y => by rfl)
                                                                                                                                                                                                                                                              (by intro Y; rfl)
                                                                                                                                                                                                                                                              (by
                                                                                                                                                                                                                                                                intro X
                                                                                                                                                                                                                                                                cases X <;> try rfl
                                                                                                                                                                                                                                                                case Apply f x =>
                                                                                                                                                                                                                                                                  cases f <;> try rfl
                                                                                                                                                                                                                                                                  case UOp op =>
                                                                                                                                                                                                                                                                    cases op <;> try rfl
                                                                                                                                                                                                                                                                    case Seq =>
                                                                                                                                                                                                                                                                      cases x <;> try rfl
                                                                                                                                                                                                                                                                      case UOp op =>
                                                                                                                                                                                                                                                                        cases op <;> rfl)
                                                                                                                                                                                                                                                        · by_cases hReConcat :
                                                                                                                                                                                                                                                            op = UserOp.re_concat
                                                                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                                                                            exact
                                                                                                                                                                                                                                                              hCurrentSmtBin
                                                                                                                                                                                                                                                                SmtTerm.re_concat
                                                                                                                                                                                                                                                                __eo_typeof_re_concat
                                                                                                                                                                                                                                                                (by rfl)
                                                                                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                                                                                  reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                    (typeof_re_concat_eq
                                                                                                                                                                                                                                                                      (__eo_to_smt x1)
                                                                                                                                                                                                                                                                      (__eo_to_smt a))
                                                                                                                                                                                                                                                                    hNN)
                                                                                                                                                                                                                                                                (fun X Y => by rfl)
                                                                                                                                                                                                                                                                (by intro Y; rfl)
                                                                                                                                                                                                                                                                (by
                                                                                                                                                                                                                                                                  intro X
                                                                                                                                                                                                                                                                  cases X <;> try rfl
                                                                                                                                                                                                                                                                  case UOp op =>
                                                                                                                                                                                                                                                                    cases op <;> rfl)
                                                                                                                                                                                                                                                          · by_cases hReInter :
                                                                                                                                                                                                                                                              op = UserOp.re_inter
                                                                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                                                                              exact
                                                                                                                                                                                                                                                                hCurrentSmtBin
                                                                                                                                                                                                                                                                  SmtTerm.re_inter
                                                                                                                                                                                                                                                                  __eo_typeof_re_concat
                                                                                                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                                                                                    reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                      (typeof_re_inter_eq
                                                                                                                                                                                                                                                                        (__eo_to_smt x1)
                                                                                                                                                                                                                                                                        (__eo_to_smt a))
                                                                                                                                                                                                                                                                      hNN)
                                                                                                                                                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                                                                                                                                                  (by intro Y; rfl)
                                                                                                                                                                                                                                                                  (by
                                                                                                                                                                                                                                                                    intro X
                                                                                                                                                                                                                                                                    cases X <;> try rfl
                                                                                                                                                                                                                                                                    case UOp op =>
                                                                                                                                                                                                                                                                      cases op <;> rfl)
                                                                                                                                                                                                                                                            · by_cases hReUnion :
                                                                                                                                                                                                                                                                op = UserOp.re_union
                                                                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                                                                exact
                                                                                                                                                                                                                                                                  hCurrentSmtBin
                                                                                                                                                                                                                                                                    SmtTerm.re_union
                                                                                                                                                                                                                                                                    __eo_typeof_re_concat
                                                                                                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                                                                                      reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                        (typeof_re_union_eq
                                                                                                                                                                                                                                                                          (__eo_to_smt x1)
                                                                                                                                                                                                                                                                          (__eo_to_smt a))
                                                                                                                                                                                                                                                                        hNN)
                                                                                                                                                                                                                                                                    (fun X Y => by rfl)
                                                                                                                                                                                                                                                                    (by intro Y; rfl)
                                                                                                                                                                                                                                                                    (by
                                                                                                                                                                                                                                                                      intro X
                                                                                                                                                                                                                                                                      cases X <;> try rfl
                                                                                                                                                                                                                                                                      case UOp op =>
                                                                                                                                                                                                                                                                        cases op <;> rfl)
                                                                                                                                                                                                                                                              · by_cases hReDiff :
                                                                                                                                                                                                                                                                  op = UserOp.re_diff
                                                                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                                                                  exact
                                                                                                                                                                                                                                                                    hCurrentSmtBin
                                                                                                                                                                                                                                                                      SmtTerm.re_diff
                                                                                                                                                                                                                                                                      __eo_typeof_re_concat
                                                                                                                                                                                                                                                                      (by rfl)
                                                                                                                                                                                                                                                                      (fun hNN =>
                                                                                                                                                                                                                                                                        reglan_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                          (typeof_re_diff_eq
                                                                                                                                                                                                                                                                            (__eo_to_smt x1)
                                                                                                                                                                                                                                                                            (__eo_to_smt a))
                                                                                                                                                                                                                                                                          hNN)
                                                                                                                                                                                                                                                                      (fun X Y => by rfl)
                                                                                                                                                                                                                                                                      (by intro Y; rfl)
                                                                                                                                                                                                                                                                      (by
                                                                                                                                                                                                                                                                        intro X
                                                                                                                                                                                                                                                                        cases X <;> try rfl
                                                                                                                                                                                                                                                                        case UOp op =>
                                                                                                                                                                                                                                                                          cases op <;> rfl)
                                                                                                                                                                                                                                                                · by_cases hStrInRe :
                                                                                                                                                                                                                                                                    op = UserOp.str_in_re
                                                                                                                                                                                                                                                                  · subst op
                                                                                                                                                                                                                                                                    exact
                                                                                                                                                                                                                                                                      hCurrentSmtBin
                                                                                                                                                                                                                                                                        SmtTerm.str_in_re
                                                                                                                                                                                                                                                                        __eo_typeof_str_in_re
                                                                                                                                                                                                                                                                        (by rfl)
                                                                                                                                                                                                                                                                        (fun hNN =>
                                                                                                                                                                                                                                                                          seq_char_reglan_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                            (ret := SmtType.Bool)
                                                                                                                                                                                                                                                                            (typeof_str_in_re_eq
                                                                                                                                                                                                                                                                              (__eo_to_smt x1)
                                                                                                                                                                                                                                                                              (__eo_to_smt a))
                                                                                                                                                                                                                                                                            hNN)
                                                                                                                                                                                                                                                                        (fun X Y => by rfl)
                                                                                                                                                                                                                                                                        (by intro Y; rfl)
                                                                                                                                                                                                                                                                        (by
                                                                                                                                                                                                                                                                          intro X
                                                                                                                                                                                                                                                                          cases X <;> try rfl
                                                                                                                                                                                                                                                                          case Apply f x =>
                                                                                                                                                                                                                                                                            cases f <;> try rfl
                                                                                                                                                                                                                                                                            case UOp op =>
                                                                                                                                                                                                                                                                              cases op <;> try rfl
                                                                                                                                                                                                                                                                              case Seq =>
                                                                                                                                                                                                                                                                                cases x <;> try rfl
                                                                                                                                                                                                                                                                                case UOp op =>
                                                                                                                                                                                                                                                                                  cases op <;> rfl)
                                                                                                                                                                                                                                                                  · by_cases hSeqNth :
                                                                                                                                                                                                                                                                      op = UserOp.seq_nth
                                                                                                                                                                                                                                                                    · subst op
                                                                                                                                                                                                                                                                      exact
                                                                                                                                                                                                                                                                        hCurrentSmtBin
                                                                                                                                                                                                                                                                          SmtTerm.seq_nth
                                                                                                                                                                                                                                                                          __eo_typeof_seq_nth
                                                                                                                                                                                                                                                                          (by rfl)
                                                                                                                                                                                                                                                                          (fun hNN =>
                                                                                                                                                                                                                                                                            seq_nth_args_have_smt_translation_of_non_none hNN)
                                                                                                                                                                                                                                                                          (fun X Y => by rfl)
                                                                                                                                                                                                                                                                          (by intro Y; rfl)
                                                                                                                                                                                                                                                                          (by
                                                                                                                                                                                                                                                                            intro X
                                                                                                                                                                                                                                                                            cases X <;> try rfl
                                                                                                                                                                                                                                                                            case Apply f x =>
                                                                                                                                                                                                                                                                              cases f <;> try rfl
                                                                                                                                                                                                                                                                              case UOp op =>
                                                                                                                                                                                                                                                                                cases op <;> rfl)
                                                                                                                                                                                                                                                                    · by_cases hSetUnion :
                                                                                                                                                                                                                                                                        op = UserOp.set_union
                                                                                                                                                                                                                                                                      · subst op
                                                                                                                                                                                                                                                                        exact
                                                                                                                                                                                                                                                                          hCurrentSmtBin
                                                                                                                                                                                                                                                                            SmtTerm.set_union
                                                                                                                                                                                                                                                                            __eo_typeof_set_union
                                                                                                                                                                                                                                                                            (by rfl)
                                                                                                                                                                                                                                                                            (fun hNN =>
                                                                                                                                                                                                                                                                              set_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                                (typeof_set_union_eq
                                                                                                                                                                                                                                                                                  (__eo_to_smt x1)
                                                                                                                                                                                                                                                                                  (__eo_to_smt a))
                                                                                                                                                                                                                                                                                hNN)
                                                                                                                                                                                                                                                                            (fun X Y => by rfl)
                                                                                                                                                                                                                                                                            (by intro Y; rfl)
                                                                                                                                                                                                                                                                            (by
                                                                                                                                                                                                                                                                              intro X
                                                                                                                                                                                                                                                                              cases X <;> try rfl
                                                                                                                                                                                                                                                                              case Apply f x =>
                                                                                                                                                                                                                                                                                cases f <;> try rfl
                                                                                                                                                                                                                                                                                case UOp op =>
                                                                                                                                                                                                                                                                                  cases op <;> rfl)
                                                                                                                                                                                                                                                                      · by_cases hSetInter :
                                                                                                                                                                                                                                                                          op = UserOp.set_inter
                                                                                                                                                                                                                                                                        · subst op
                                                                                                                                                                                                                                                                          exact
                                                                                                                                                                                                                                                                            hCurrentSmtBin
                                                                                                                                                                                                                                                                              SmtTerm.set_inter
                                                                                                                                                                                                                                                                              __eo_typeof_set_union
                                                                                                                                                                                                                                                                              (by rfl)
                                                                                                                                                                                                                                                                              (fun hNN =>
                                                                                                                                                                                                                                                                                set_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                                  (typeof_set_inter_eq
                                                                                                                                                                                                                                                                                    (__eo_to_smt x1)
                                                                                                                                                                                                                                                                                    (__eo_to_smt a))
                                                                                                                                                                                                                                                                                  hNN)
                                                                                                                                                                                                                                                                              (fun X Y => by rfl)
                                                                                                                                                                                                                                                                              (by intro Y; rfl)
                                                                                                                                                                                                                                                                              (by
                                                                                                                                                                                                                                                                                intro X
                                                                                                                                                                                                                                                                                cases X <;> try rfl
                                                                                                                                                                                                                                                                                case Apply f x =>
                                                                                                                                                                                                                                                                                  cases f <;> try rfl
                                                                                                                                                                                                                                                                                  case UOp op =>
                                                                                                                                                                                                                                                                                    cases op <;> rfl)
                                                                                                                                                                                                                                                                        · by_cases hSetMinus :
                                                                                                                                                                                                                                                                            op = UserOp.set_minus
                                                                                                                                                                                                                                                                          · subst op
                                                                                                                                                                                                                                                                            exact
                                                                                                                                                                                                                                                                              hCurrentSmtBin
                                                                                                                                                                                                                                                                                SmtTerm.set_minus
                                                                                                                                                                                                                                                                                __eo_typeof_set_union
                                                                                                                                                                                                                                                                                (by rfl)
                                                                                                                                                                                                                                                                                (fun hNN =>
                                                                                                                                                                                                                                                                                  set_binop_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                                    (typeof_set_minus_eq
                                                                                                                                                                                                                                                                                      (__eo_to_smt x1)
                                                                                                                                                                                                                                                                                      (__eo_to_smt a))
                                                                                                                                                                                                                                                                                    hNN)
                                                                                                                                                                                                                                                                                (fun X Y => by rfl)
                                                                                                                                                                                                                                                                                (by intro Y; rfl)
                                                                                                                                                                                                                                                                                (by
                                                                                                                                                                                                                                                                                  intro X
                                                                                                                                                                                                                                                                                  cases X <;> try rfl
                                                                                                                                                                                                                                                                                  case Apply f x =>
                                                                                                                                                                                                                                                                                    cases f <;> try rfl
                                                                                                                                                                                                                                                                                    case UOp op =>
                                                                                                                                                                                                                                                                                      cases op <;> rfl)
                                                                                                                                                                                                                                                                          · by_cases hSetMember :
                                                                                                                                                                                                                                                                              op = UserOp.set_member
                                                                                                                                                                                                                                                                            · subst op
                                                                                                                                                                                                                                                                              exact
                                                                                                                                                                                                                                                                                hCurrentSmtBin
                                                                                                                                                                                                                                                                                  SmtTerm.set_member
                                                                                                                                                                                                                                                                                  __eo_typeof_set_member
                                                                                                                                                                                                                                                                                  (by rfl)
                                                                                                                                                                                                                                                                                  (fun hNN =>
                                                                                                                                                                                                                                                                                    set_member_args_have_smt_translation_of_non_none hNN)
                                                                                                                                                                                                                                                                                  (fun X Y => by rfl)
                                                                                                                                                                                                                                                                                  (by intro Y; rfl)
                                                                                                                                                                                                                                                                                  (by
                                                                                                                                                                                                                                                                                    intro X
                                                                                                                                                                                                                                                                                    cases X <;> try rfl)
                                                                                                                                                                                                                                                                            · by_cases hSetSubset :
                                                                                                                                                                                                                                                                                op = UserOp.set_subset
                                                                                                                                                                                                                                                                              · subst op
                                                                                                                                                                                                                                                                                exact
                                                                                                                                                                                                                                                                                  hCurrentSmtBin
                                                                                                                                                                                                                                                                                    SmtTerm.set_subset
                                                                                                                                                                                                                                                                                    __eo_typeof_set_subset
                                                                                                                                                                                                                                                                                    (by rfl)
                                                                                                                                                                                                                                                                                    (fun hNN =>
                                                                                                                                                                                                                                                                                      set_binop_ret_args_have_smt_translation_of_non_none
                                                                                                                                                                                                                                                                                        (ret := SmtType.Bool)
                                                                                                                                                                                                                                                                                        (typeof_set_subset_eq
                                                                                                                                                                                                                                                                                          (__eo_to_smt x1)
                                                                                                                                                                                                                                                                                          (__eo_to_smt a))
                                                                                                                                                                                                                                                                                        hNN)
                                                                                                                                                                                                                                                                                    (fun X Y => by rfl)
                                                                                                                                                                                                                                                                                    (by intro Y; rfl)
                                                                                                                                                                                                                                                                                    (by
                                                                                                                                                                                                                                                                                      intro X
                                                                                                                                                                                                                                                                                      cases X <;> try rfl
                                                                                                                                                                                                                                                                                      case Apply f x =>
                                                                                                                                                                                                                                                                                        cases f <;> try rfl
                                                                                                                                                                                                                                                                                        case UOp op =>
                                                                                                                                                                                                                                                                                          cases op <;> rfl)
                                                                                                                                                                                                                                                                              · by_cases hSetInsert :
                                                                                                                                                                                                                                                                                  op = UserOp.set_insert
                                                                                                                                                                                                                                                                                · subst op
                                                                                                                                                                                                                                                                                  exact
                                                                                                                                                                                                                                                                                    substitute_simul_set_insert_typeof_eq_of_typeof_ne_stuck
                                                                                                                                                                                                                                                                                      x1 a xs ss bvs
                                                                                                                                                                                                                                                                                      hXsEnv hBvsEnv hSs
                                                                                                                                                                                                                                                                                      (fun q v vs hEq =>
                                                                                                                                                                                                                                                                                        hBinder ⟨q, v, vs, hEq⟩)
                                                                                                                                                                                                                                                                                      hFTrans
                                                                                                                                                                                                                                                                                      (fun hATrans hATy =>
                                                                                                                                                                                                                                                                                        hRec
                                                                                                                                                                                                                                                                                          (G := a)
                                                                                                                                                                                                                                                                                          (xs' := xs)
                                                                                                                                                                                                                                                                                          (ss' := ss)
                                                                                                                                                                                                                                                                                          (bvs' := bvs)
                                                                                                                                                                                                                                                                                          (by simp; omega)
                                                                                                                                                                                                                                                                                          hXsEnv hBvsEnv
                                                                                                                                                                                                                                                                                          hATrans hSs
                                                                                                                                                                                                                                                                                          hEntryTypes hATy)
                                                                                                                                                                                                                                                                                      hTy
                                                                                                                                                                                                                                                                                · sorry
                                                                                                  | _ => sorry
                                                                                              | Var name T =>
                                                                                                  exact
                                                                                                    substitute_simul_rec_apply_var_typeof_eq_of_typeof_ne_stuck
                                                                                                      name T a xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSs
                                                                                                      hEntryTypes
                                                                                                      (by intro q v vs hEq; cases hEq)
                                                                                                      (by rfl)
                                                                                                      (var_apply_generic_smt_type name T a)
                                                                                                      hFTrans
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a)
                                                                                                          (xs' := xs)
                                                                                                          (ss' := ss)
                                                                                                          (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv
                                                                                                          hATrans hSs
                                                                                                          hEntryTypes hATy)
                                                                                                      hTy
                                                                                              | UConst i U =>
                                                                                                  exact
                                                                                                    substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
                                                                                                      (Term.UConst i U) a xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSs
                                                                                                      (by intro f x h; cases h)
                                                                                                      (by intro s S h; cases h)
                                                                                                      (by intro h; cases h)
                                                                                                      (by intro q v vs hEq; cases hEq)
                                                                                                      (by rfl)
                                                                                                      (by
                                                                                                        change
                                                                                                          __smtx_typeof
                                                                                                              (SmtTerm.Apply
                                                                                                                (SmtTerm.UConst
                                                                                                                  (native_uconst_id i)
                                                                                                                  (__eo_to_smt_type U))
                                                                                                                (__eo_to_smt a)) =
                                                                                                            __smtx_typeof_apply
                                                                                                              (__smtx_typeof
                                                                                                                (SmtTerm.UConst
                                                                                                                  (native_uconst_id i)
                                                                                                                  (__eo_to_smt_type U)))
                                                                                                              (__smtx_typeof
                                                                                                                (__eo_to_smt a))
                                                                                                        rw [__smtx_typeof.eq_def])
                                                                                                      hFTrans
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a)
                                                                                                          (xs' := xs)
                                                                                                          (ss' := ss)
                                                                                                          (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv
                                                                                                          hATrans hSs
                                                                                                          hEntryTypes hATy)
                                                                                                      hTy
                                                                                              | DtCons s d i =>
                                                                                                  exact
                                                                                                    substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
                                                                                                      (Term.DtCons s d i) a xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSs
                                                                                                      (by intro f x h; cases h)
                                                                                                      (by intro name T h; cases h)
                                                                                                      (by intro h; cases h)
                                                                                                      (by intro q v vs hEq; cases hEq)
                                                                                                      (by rfl)
                                                                                                      (by
                                                                                                        have hReserved :
                                                                                                            native_reserved_datatype_name s =
                                                                                                              false :=
                                                                                                          dtcons_reserved_false_of_apply_has_smt_translation
                                                                                                            hFTrans
                                                                                                        change
                                                                                                          __smtx_typeof
                                                                                                              (SmtTerm.Apply
                                                                                                                (native_ite
                                                                                                                  (native_reserved_datatype_name s)
                                                                                                                  SmtTerm.None
                                                                                                                  (SmtTerm.DtCons s
                                                                                                                    (__eo_to_smt_datatype d)
                                                                                                                    i))
                                                                                                                (__eo_to_smt a)) =
                                                                                                            __smtx_typeof_apply
                                                                                                              (__smtx_typeof
                                                                                                                (native_ite
                                                                                                                  (native_reserved_datatype_name s)
                                                                                                                  SmtTerm.None
                                                                                                                  (SmtTerm.DtCons s
                                                                                                                    (__eo_to_smt_datatype d)
                                                                                                                    i)))
                                                                                                              (__smtx_typeof
                                                                                                                (__eo_to_smt a))
                                                                                                        rw [hReserved]
                                                                                                        rw [__smtx_typeof.eq_def])
                                                                                                      hFTrans
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a)
                                                                                                          (xs' := xs)
                                                                                                          (ss' := ss)
                                                                                                          (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv
                                                                                                          hATrans hSs
                                                                                                          hEntryTypes hATy)
                                                                                                      hTy
                                                                                              | Boolean b =>
                                                                                                  exact
                                                                                                    substitute_simul_rec_apply_atom_generic_typeof_eq_of_typeof_ne_stuck
                                                                                                      (Term.Boolean b) a xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSs
                                                                                                      (by intro f x h; cases h)
                                                                                                      (by intro name T h; cases h)
                                                                                                      (by intro h; cases h)
                                                                                                      (by intro q v vs hEq; cases hEq)
                                                                                                      (by rfl)
                                                                                                      (by intro s d i j h; cases h)
                                                                                                      (by intro s d i h; cases h)
                                                                                                      hFTrans
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a)
                                                                                                          (xs' := xs)
                                                                                                          (ss' := ss)
                                                                                                          (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv
                                                                                                          hATrans hSs
                                                                                                          hEntryTypes hATy)
                                                                                                      hTy
                                                                                              | Numeral n =>
                                                                                                  exact
                                                                                                    substitute_simul_rec_apply_atom_generic_typeof_eq_of_typeof_ne_stuck
                                                                                                      (Term.Numeral n) a xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSs
                                                                                                      (by intro f x h; cases h)
                                                                                                      (by intro name T h; cases h)
                                                                                                      (by intro h; cases h)
                                                                                                      (by intro q v vs hEq; cases hEq)
                                                                                                      (by rfl)
                                                                                                      (by intro s d i j h; cases h)
                                                                                                      (by intro s d i h; cases h)
                                                                                                      hFTrans
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a)
                                                                                                          (xs' := xs)
                                                                                                          (ss' := ss)
                                                                                                          (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv
                                                                                                          hATrans hSs
                                                                                                          hEntryTypes hATy)
                                                                                                      hTy
                                                                                              | Rational r =>
                                                                                                  exact
                                                                                                    substitute_simul_rec_apply_atom_generic_typeof_eq_of_typeof_ne_stuck
                                                                                                      (Term.Rational r) a xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSs
                                                                                                      (by intro f x h; cases h)
                                                                                                      (by intro name T h; cases h)
                                                                                                      (by intro h; cases h)
                                                                                                      (by intro q v vs hEq; cases hEq)
                                                                                                      (by rfl)
                                                                                                      (by intro s d i j h; cases h)
                                                                                                      (by intro s d i h; cases h)
                                                                                                      hFTrans
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a)
                                                                                                          (xs' := xs)
                                                                                                          (ss' := ss)
                                                                                                          (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv
                                                                                                          hATrans hSs
                                                                                                          hEntryTypes hATy)
                                                                                                      hTy
                                                                                              | String s =>
                                                                                                  exact
                                                                                                    substitute_simul_rec_apply_atom_generic_typeof_eq_of_typeof_ne_stuck
                                                                                                      (Term.String s) a xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSs
                                                                                                      (by intro f x h; cases h)
                                                                                                      (by intro name T h; cases h)
                                                                                                      (by intro h; cases h)
                                                                                                      (by intro q v vs hEq; cases hEq)
                                                                                                      (by rfl)
                                                                                                      (by intro s d i j h; cases h)
                                                                                                      (by intro s d i h; cases h)
                                                                                                      hFTrans
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a)
                                                                                                          (xs' := xs)
                                                                                                          (ss' := ss)
                                                                                                          (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv
                                                                                                          hATrans hSs
                                                                                                          hEntryTypes hATy)
                                                                                                      hTy
                                                                                              | Binary w n =>
                                                                                                  exact
                                                                                                    substitute_simul_rec_apply_atom_generic_typeof_eq_of_typeof_ne_stuck
                                                                                                      (Term.Binary w n) a xs ss bvs
                                                                                                      hXsEnv hBvsEnv hSs
                                                                                                      (by intro f x h; cases h)
                                                                                                      (by intro name T h; cases h)
                                                                                                      (by intro h; cases h)
                                                                                                      (by intro q v vs hEq; cases hEq)
                                                                                                      (by rfl)
                                                                                                      (by intro s d i j h; cases h)
                                                                                                      (by intro s d i h; cases h)
                                                                                                      hFTrans
                                                                                                      (fun hATrans hATy =>
                                                                                                        hRec
                                                                                                          (G := a)
                                                                                                          (xs' := xs)
                                                                                                          (ss' := ss)
                                                                                                          (bvs' := bvs)
                                                                                                          (by simp; omega)
                                                                                                          hXsEnv hBvsEnv
                                                                                                          hATrans hSs
                                                                                                          hEntryTypes hATy)
                                                                                                      hTy
                                                                                              | _ => sorry
      | Var name T =>
          exact
            substitute_simul_rec_var_any_typeof_eq
              name T xs ss bvs hXsEnv hBvsEnv hSs hEntryTypes hFTrans
      | Stuck =>
          exact False.elim
            ((RuleProofs.term_ne_stuck_of_has_smt_translation Term.Stuck hFTrans) rfl)
      | _ =>
          exact
            substitute_simul_rec_atom_typeof_eq_of_typeof_ne_stuck
              _ xs ss bvs hXsEnv hBvsEnv hSs
              (by intro f a h; cases h)
              (by intro s S h; cases h)
              (by intro h; cases h)
              hTy

theorem substitute_simul_rec_typeof_eq_of_typeof_ne_stuck
    (F xs ss bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hSs : EoListAllHaveSmtTranslation ss)
    (hEntryTypes : SubstEntryPreservesTypes xs ss)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ss bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ss bvs) =
      __eo_typeof F :=
  substitute_simul_rec_typeof_eq_of_typeof_ne_stuck_lt
    (sizeOf F + 1) F xs ss bvs
    (by omega) hXsEnv hBvsEnv hFTrans hSs hEntryTypes hTy

end SubstituteSupport
