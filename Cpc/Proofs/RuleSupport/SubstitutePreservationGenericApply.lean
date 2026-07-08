import Cpc.Proofs.RuleSupport.SubstitutePreservationAtomGeneric
import Cpc.Proofs.RuleSupport.TypedListSubstitutionSupport

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport
open TypedListSubstitutionSupport

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

namespace SubstitutePreservationSupport

private theorem eo_typeof_apply_apply_head_typeof_ne_stuck_of_head_has_smt_translation
    (f x y : Term)
    (hFTrans : RuleProofs.eo_has_smt_translation f)
    (hTy : __eo_typeof (Term.Apply (Term.Apply f x) y) ≠ Term.Stuck) :
    __eo_typeof (Term.Apply f x) ≠ Term.Stuck := by
  have hOuterGeneric :
      __eo_typeof (Term.Apply (Term.Apply f x) y) =
        __eo_typeof_apply (__eo_typeof (Term.Apply f x)) (__eo_typeof y) := by
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hFTrans
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    case UOp1 op i =>
      cases op <;> try rfl
      all_goals
        exfalso
        apply hFTrans
        change __smtx_typeof SmtTerm.None = SmtType.None
        exact TranslationProofs.smtx_typeof_none
    case FunType =>
      exfalso
      apply hFTrans
      change __smtx_typeof SmtTerm.None = SmtType.None
      exact TranslationProofs.smtx_typeof_none
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          exfalso
          apply hFTrans
          change __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt b)) =
            SmtType.None
          simp [__smtx_typeof, __smtx_typeof_apply,
            TranslationProofs.smtx_typeof_none]
  rw [hOuterGeneric] at hTy
  exact SubstituteSupport.eo_typeof_apply_head_ne_stuck hTy

theorem substitute_simul_apply_apply_var_head_generic_head_typeof_ne_stuck
    (name T x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Var name T) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Var name T) x) a))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Var name T) x) xs ts bvs) ≠
      Term.Stuck := by
  let varSub :=
    __substitute_simul_rec (Term.Boolean false) (Term.Var name T) xs ts bvs
  let xSub := __substitute_simul_rec (Term.Boolean false) x xs ts bvs
  let aSub := __substitute_simul_rec (Term.Boolean false) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean false)
      (Term.Apply (Term.Var name T) x) xs ts bvs
  have hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Var name T) x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) x))
          (__eo_to_smt a) := by
    rfl
  have hOuterGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) x))
            (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Var name T) x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply (Term.Var name T) x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel (Term.Var name T) x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester (Term.Var name T) x)
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Var name T) x) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply (Term.Var name T) x) a hOuterTranslate hOuterGeneric
      hFTrans).1
  have hVarTrans : RuleProofs.eo_has_smt_translation (Term.Var name T) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Var name T) x (by rfl)
      (SubstituteSupport.var_apply_generic_smt_type name T x)
      hHeadTrans).1
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadRaw :
      headSub = __eo_mk_apply varSub xSub := by
    simpa [headSub, varSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.Var name T) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.Apply (Term.Var name T) x) a xs ts bvs
        hisr hxs hts hbvs
        hNotBinderOuter
  have hOuterTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMkNe : __eo_mk_apply headSub aSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hOuterTyMk
  have hHeadNe : headSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterMkNe
  have hHeadMkNe : __eo_mk_apply varSub xSub ≠ Term.Stuck := by
    rwa [← hHeadRaw]
  have hVarNe : varSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hVarSubTrans :
      RuleProofs.eo_has_smt_translation varSub := by
    simpa [varSub] using
      SubstituteSupport.substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
        name T xs ts bvs hXsEnv hBvsEnv hTs hVarTrans
        (by simpa [varSub] using hVarNe)
  have hHeadMk : __eo_mk_apply varSub xSub = Term.Apply varSub xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck varSub xSub hHeadMkNe
  have hOuterMk : __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck headSub aSub hOuterMkNe
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hOuterTyMk
  have hOuterApplyTy' :
      __eo_typeof (Term.Apply (Term.Apply varSub xSub) aSub) ≠
        Term.Stuck := by
    simpa [hHeadRaw, hHeadMk] using hOuterApplyTy
  have hHeadApplyTy :
      __eo_typeof (Term.Apply varSub xSub) ≠ Term.Stuck :=
    eo_typeof_apply_apply_head_typeof_ne_stuck_of_head_has_smt_translation
      varSub xSub aSub hVarSubTrans hOuterApplyTy'
  simpa [headSub, hHeadRaw, hHeadMk] using hHeadApplyTy

theorem substitute_simul_apply_apply_atom_base_generic_head_typeof_ne_stuck
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f y, g ≠ Term.Apply f y)
    (hNotVar : ∀ name T, g ≠ Term.Var name T)
    (hNotStuck : g ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hInnerTranslate :
      __eo_to_smt (Term.Apply g x) =
        SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt x))
    (hInnerGeneric :
      __smtx_typeof (SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt x)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt g)) (__smtx_typeof (__eo_to_smt x)))
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a))
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply g x) xs ts bvs) ≠
      Term.Stuck := by
  let gSub := __substitute_simul_rec (Term.Boolean false) g xs ts bvs
  let xSub := __substitute_simul_rec (Term.Boolean false) x xs ts bvs
  let aSub := __substitute_simul_rec (Term.Boolean false) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean false) (Term.Apply g x) xs ts bvs
  have hOuterGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply g x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel g x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester g x)
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply g x) a hOuterTranslate hOuterGeneric hFTrans).1
  have hGTrans : RuleProofs.eo_has_smt_translation g :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      g x hInnerTranslate hInnerGeneric hHeadTrans).1
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadRaw :
      headSub = __eo_mk_apply gSub xSub := by
    simpa [headSub, gSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) g x xs ts bvs hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotApply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) hEq)
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.Apply g x) a xs ts bvs
        hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotBinderOuter q v vs hEq)
  have hOuterTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMkNe : __eo_mk_apply headSub aSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hOuterTyMk
  have hHeadNe : headSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterMkNe
  have hHeadMkNe : __eo_mk_apply gSub xSub ≠ Term.Stuck := by
    rwa [← hHeadRaw]
  have hGSubNe : gSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hGSubEq : gSub = g := by
    simpa [gSub] using
      SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
        g xs ts bvs hXsEnv hBvsEnv hTs hNotApply hNotVar hNotStuck
        (by simpa [gSub] using hGSubNe)
  have hGSubTrans : RuleProofs.eo_has_smt_translation gSub := by
    simpa [hGSubEq] using hGTrans
  have hHeadMk : __eo_mk_apply gSub xSub = Term.Apply gSub xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck gSub xSub hHeadMkNe
  have hOuterMk : __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck headSub aSub hOuterMkNe
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hOuterTyMk
  have hOuterApplyTy' :
      __eo_typeof (Term.Apply (Term.Apply gSub xSub) aSub) ≠
        Term.Stuck := by
    simpa [hHeadRaw, hHeadMk] using hOuterApplyTy
  have hHeadApplyTy :
      __eo_typeof (Term.Apply gSub xSub) ≠ Term.Stuck :=
    eo_typeof_apply_apply_head_typeof_ne_stuck_of_head_has_smt_translation
      gSub xSub aSub hGSubTrans hOuterApplyTy'
  simpa [headSub, hHeadRaw, hHeadMk] using hHeadApplyTy

theorem substitute_simul_apply_apply_atom_head_typeof_ne_stuck_of_head_translation
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f y, g ≠ Term.Apply f y)
    (hNotVar : ∀ name T, g ≠ Term.Var name T)
    (hNotStuck : g ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hGTrans : RuleProofs.eo_has_smt_translation g)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply g x) xs ts bvs) ≠
      Term.Stuck := by
  let gSub := __substitute_simul_rec (Term.Boolean false) g xs ts bvs
  let xSub := __substitute_simul_rec (Term.Boolean false) x xs ts bvs
  let aSub := __substitute_simul_rec (Term.Boolean false) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean false) (Term.Apply g x) xs ts bvs
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadRaw :
      headSub = __eo_mk_apply gSub xSub := by
    simpa [headSub, gSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) g x xs ts bvs hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotApply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) hEq)
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.Apply g x) a xs ts bvs
        hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotBinderOuter q v vs hEq)
  have hOuterTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMkNe : __eo_mk_apply headSub aSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hOuterTyMk
  have hHeadNe : headSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterMkNe
  have hHeadMkNe : __eo_mk_apply gSub xSub ≠ Term.Stuck := by
    rwa [← hHeadRaw]
  have hGSubNe : gSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hGSubEq : gSub = g := by
    simpa [gSub] using
      SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
        g xs ts bvs hXsEnv hBvsEnv hTs hNotApply hNotVar hNotStuck
        (by simpa [gSub] using hGSubNe)
  have hGSubTrans : RuleProofs.eo_has_smt_translation gSub := by
    simpa [hGSubEq] using hGTrans
  have hHeadMk : __eo_mk_apply gSub xSub = Term.Apply gSub xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck gSub xSub hHeadMkNe
  have hOuterMk : __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck headSub aSub hOuterMkNe
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hOuterTyMk
  have hOuterApplyTy' :
      __eo_typeof (Term.Apply (Term.Apply gSub xSub) aSub) ≠
        Term.Stuck := by
    simpa [hHeadRaw, hHeadMk] using hOuterApplyTy
  have hHeadApplyTy :
      __eo_typeof (Term.Apply gSub xSub) ≠ Term.Stuck :=
    eo_typeof_apply_apply_head_typeof_ne_stuck_of_head_has_smt_translation
      gSub xSub aSub hGSubTrans hOuterApplyTy'
  simpa [headSub, hHeadRaw, hHeadMk] using hHeadApplyTy

theorem substitute_simul_apply_apply_atom_residual_head_typeof_ne_stuck
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f y, g ≠ Term.Apply f y)
    (hNotVar : ∀ name T, g ≠ Term.Var name T)
    (hNotUOp : ∀ op, g ≠ Term.UOp op)
    (hNoUpdate : ¬ ∃ idx, g = Term.UOp1 UserOp1.update idx)
    (hNoTupleUpdate :
      ¬ ∃ idx, g = Term.UOp1 UserOp1.tuple_update idx)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply g x) xs ts bvs) ≠
      Term.Stuck := by
  let gSub := __substitute_simul_rec (Term.Boolean false) g xs ts bvs
  let xSub := __substitute_simul_rec (Term.Boolean false) x xs ts bvs
  let aSub := __substitute_simul_rec (Term.Boolean false) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean false) (Term.Apply g x) xs ts bvs
  have hNotStuck : g ≠ Term.Stuck := by
    intro hEq
    subst g
    apply hFTrans
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
            (__eo_to_smt a)) =
        SmtType.None
    simp [__smtx_typeof, __smtx_typeof_apply,
      TranslationProofs.smtx_typeof_none]
  have hNotFunType : g ≠ Term.FunType := by
    intro hEq
    subst g
    apply hFTrans
    change
      __smtx_typeof
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
            (__eo_to_smt a)) =
        SmtType.None
    simp [__smtx_typeof, __smtx_typeof_apply,
      TranslationProofs.smtx_typeof_none]
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadRaw :
      headSub = __eo_mk_apply gSub xSub := by
    simpa [headSub, gSub, xSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) g x xs ts bvs hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotApply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) hEq)
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.Apply g x) a xs ts bvs
        hisr hxs hts hbvs
        (by
          intro q v vs hEq
          exact hNotBinderOuter q v vs hEq)
  have hOuterTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMkNe : __eo_mk_apply headSub aSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hOuterTyMk
  have hHeadNe : headSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterMkNe
  have hHeadMkNe : __eo_mk_apply gSub xSub ≠ Term.Stuck := by
    rwa [← hHeadRaw]
  have hGSubNe : gSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hHeadMkNe
  have hGSubEq : gSub = g := by
    simpa [gSub] using
      SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
        g xs ts bvs hXsEnv hBvsEnv hTs hNotApply hNotVar hNotStuck
        (by simpa [gSub] using hGSubNe)
  have hHeadMk : __eo_mk_apply gSub xSub = Term.Apply gSub xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck gSub xSub hHeadMkNe
  have hHeadShape : headSub = Term.Apply g xSub := by
    rw [hHeadRaw, hHeadMk, hGSubEq]
  have hOuterMk : __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck headSub aSub hOuterMkNe
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hOuterTyMk
  have hOuterGeneric :
      __eo_typeof (Term.Apply headSub aSub) =
        __eo_typeof_apply (__eo_typeof headSub) (__eo_typeof aSub) := by
    rw [hHeadShape]
    cases g <;> try rfl
    · rename_i op
      exact False.elim (hNotUOp op rfl)
    · rename_i op idx
      cases op <;> try rfl
      · exact False.elim (hNoUpdate ⟨idx, rfl⟩)
      · exact False.elim (hNoTupleUpdate ⟨idx, rfl⟩)
    · rename_i f y
      exact False.elim (hNotApply f y rfl)
    · exact False.elim (hNotFunType rfl)
  rw [hOuterGeneric] at hOuterApplyTy
  exact SubstituteSupport.eo_typeof_apply_head_ne_stuck hOuterApplyTy

theorem substitute_simul_apply_applied_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a))
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs) =
        __eo_typeof (Term.Apply g x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs))
    (hRecA :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs))
    (hHeadSubTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply g x) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) := by
  let aSub := __substitute_simul_rec (Term.Boolean false) a xs ts bvs
  let headSub :=
    __substitute_simul_rec (Term.Boolean false) (Term.Apply g x) xs ts bvs
  have hGenericOuter :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply g x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel g x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester g x)
  have hArgs :=
    SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply g x) a hOuterTranslate hGenericOuter hFTrans
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) := hArgs.1
  have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hOuterRaw :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs =
        __eo_mk_apply headSub aSub := by
    simpa [headSub, aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.Apply g x) a xs ts bvs
        hisr hxs hts hbvs hNotBinderOuter
  have hTyMk :
      __eo_typeof (__eo_mk_apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterRaw] at hTy
  have hOuterMk :
      __eo_mk_apply headSub aSub = Term.Apply headSub aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
  have hOuterApplyTy :
      __eo_typeof (Term.Apply headSub aSub) ≠ Term.Stuck := by
    rwa [hOuterMk] at hTyMk
  have hHeadBoth := hRecHead hHeadTrans (by simpa [headSub] using hHeadSubTy)
  have hATy : __eo_typeof aSub ≠ Term.Stuck := by
    simpa [aSub] using
      SubstituteSupport.substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
        (Term.Apply g x) a xs ts bvs hXsEnv hBvsEnv hTs
        hNotBinderOuter hHeadBoth.2 hTy
  have hABoth := hRecA hATrans hATy
  refine ⟨?_, ?_⟩
  · exact
      SubstituteSupport.substitute_simul_rec_apply_typeof_eq_of_typeof_ne_stuck
        (Term.Apply g x) a xs ts bvs hXsEnv hBvsEnv hTs hNotBinderOuter
        hHeadTrans hHeadBoth.2 hHeadBoth.1 hABoth.1 hTy
  · exact
      SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
        (Term.Apply g x) a xs ts bvs hXsEnv hBvsEnv hTs hNotBinderOuter
        hHeadBoth.2 hABoth.2 hTy

theorem substitute_simul_apply_apply_uop_generic_preserves_type_and_translation_of_typeof_ne_stuck
    (op : UserOp) (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) x) y) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) x))
          (__eo_to_smt y))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp op) x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.UOp op) x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.UOp op) x) xs ts bvs) =
        __eo_typeof (Term.Apply (Term.UOp op) x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.UOp op) x) xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) y xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) y xs ts bvs) =
        __eo_typeof y ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) y xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) := by
  let xSub := __substitute_simul_rec (Term.Boolean false) x xs ts bvs
  let ySub := __substitute_simul_rec (Term.Boolean false) y xs ts bvs
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck :=
    SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean false) (Term.UOp op) xs ts bvs =
        Term.UOp op :=
    SubstituteSupport.substitute_simul_rec_uop_eq_self
      op xs ts bvs hXsEnv hBvsEnv hTs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) x) xs ts bvs =
        __eo_mk_apply (Term.UOp op) xSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.UOp op) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.Apply (Term.UOp op) x) y xs ts bvs
        hisr hxs hts hbvs hNotBinder
    simpa [ySub, hInnerSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub ≠
        Term.Stuck :=
    SubstituteSupport.eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp op) xSub ≠ Term.Stuck :=
    SubstituteSupport.eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp op) xSub =
        Term.Apply (Term.UOp op) xSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp op) xSub hInnerNe
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp op) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp op) xSub) ySub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_ne_stuck
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
  have hGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) x))
            (__eo_to_smt y)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp op) x)))
          (__smtx_typeof (__eo_to_smt y)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply (Term.UOp op) x)) (__eo_to_smt y)
      (SubstituteSupport.eo_to_smt_uop_apply_ne_dt_sel op x)
      (SubstituteSupport.eo_to_smt_uop_apply_ne_dt_tester op x)
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.UOp op) x))
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hFTransEo
  rcases apply_args_have_smt_translation_of_non_none hGeneric hNN with
    ⟨hHeadTransEo, hYTransEo⟩
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp op) x) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hHeadTransEo
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hYTransEo
  have hUnary : SubstituteSupport.substitute_uopHasUnarySmtTranslation op = true :=
    SubstituteSupport.substitute_uopHasUnarySmtTranslation_eq_true_of_apply_translation
      hHeadTrans
  have hTypeSupport :=
    SubstituteSupport.eo_typeof_apply_apply_uop_generic_support_of_unary_smt_translation
      hUnary
  rcases hTypeSupport.1 xSub ySub hTyApply with ⟨hHeadSubTy, hYSubTy⟩
  have hHeadSubTy' :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.UOp op) x) xs ts bvs) ≠
        Term.Stuck := by
    rw [hInnerSub, hInnerMk]
    exact hHeadSubTy
  have hHeadBoth := hRecHead hHeadTrans hHeadSubTy'
  have hYBoth := hRecY hYTrans (by simpa [ySub] using hYSubTy)
  have hHeadTy :
      __eo_typeof (Term.Apply (Term.UOp op) xSub) =
        __eo_typeof (Term.Apply (Term.UOp op) x) := by
    simpa [hInnerSub, hInnerMk] using hHeadBoth.1
  have hYTy : __eo_typeof ySub = __eo_typeof y := by
    simpa [ySub] using hYBoth.1
  refine ⟨?_, ?_⟩
  · rw [hSubstEq, hInnerMk, hOuterMk]
    exact hTypeSupport.2 x xSub y ySub hHeadTy hYTy
  · exact
      SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
        (Term.Apply (Term.UOp op) x) y xs ts bvs
        hXsEnv hBvsEnv hTs hNotBinder hHeadBoth.2 hYBoth.2 hTy

theorem substitute_simul_apply_apply_var_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
    (name T x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply (Term.Var name T) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Var name T) x) a))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Var name T) x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Var name T) x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Var name T) x) xs ts bvs) =
        __eo_typeof (Term.Apply (Term.Var name T) x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Var name T) x) xs ts bvs))
    (hRecA :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs))
    (hHeadSubTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Var name T) x) xs ts bvs) ≠
        Term.Stuck)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.Var name T) x) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Var name T) x) a) xs ts bvs) := by
  have hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.Var name T) x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) x))
          (__eo_to_smt a) := by
    rfl
  have hGenericOuter :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply (Term.Var name T) x))
            (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply (Term.Var name T) x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply (Term.Var name T) x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel (Term.Var name T) x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester (Term.Var name T) x)
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Var name T) x) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply (Term.Var name T) x) a hOuterTranslate hGenericOuter
      hFTrans).1
  exact
    substitute_simul_apply_applied_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
      (Term.Var name T) x a xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinderOuter hOuterTranslate
      hFTrans hRecHead hRecA hHeadSubTy hTy

/--
Residual higher-order application head non-vacuity.

In the fully generic `((g x) a)` branch, the outer substituted application
being typeable forces the substituted applied head `(g x)[xs := ts]` to be
typeable as well. This is the remaining operator-spine non-vacuity obligation
shared with the old type-only substitution engine.
-/
theorem substitute_simul_apply_apply_branch_residual_head_typeof_ne_stuck
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hUOp : ApplyApplyUOpBranchExclusions g)
    (hNoUpdate : ¬ ∃ idx, g = Term.UOp1 UserOp1.update idx)
    (hNoTupleUpdate :
      ¬ ∃ idx, g = Term.UOp1 UserOp1.tuple_update idx)
    (hApplyUOp : ApplyApplyApplyUOpBranchExclusions g)
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply g x) xs ts bvs) ≠
      Term.Stuck := by
  -- TODO(instRefactor): prove the higher-order operator-spine non-vacuity
  -- bridge and remove the matching old type-only `sorry`s in
  -- `SubstituteTypeSupport.substitute_simul_rec_typeof_eq_of_typeof_ne_stuck_lt`.
  sorry

theorem substitute_simul_apply_apply_branch_residual_preserves_type_and_translation_of_typeof_ne_stuck
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hUOp : ApplyApplyUOpBranchExclusions g)
    (hNoUpdate : ¬ ∃ idx, g = Term.UOp1 UserOp1.update idx)
    (hNoTupleUpdate :
      ¬ ∃ idx, g = Term.UOp1 UserOp1.tuple_update idx)
    (hApplyUOp : ApplyApplyApplyUOpBranchExclusions g)
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs) =
        __eo_typeof (Term.Apply g x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs))
    (hRecA :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply g x) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) := by
  have hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a) :=
    eo_to_smt_apply_apply_generic_of_branch_exclusions
      (g := g) (x := x) (a := a)
      hUOp hNoUpdate hNoTupleUpdate hApplyUOp
  have hHeadSubTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck :=
    substitute_simul_apply_apply_branch_residual_head_typeof_ne_stuck
      g x a xs ts bvs hXsEnv hBvsEnv hTs hNotBinderOuter
      hUOp hNoUpdate hNoTupleUpdate hApplyUOp hFTrans hTy
  exact
    substitute_simul_apply_applied_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
      g x a xs ts bvs
      hXsEnv hBvsEnv hTs
      hNotBinderOuter
      hOuterTranslate
      hFTrans hRecHead hRecA hHeadSubTy hTy

theorem substitute_simul_apply_apply_atom_base_generic_preserves_type_and_translation_of_typeof_ne_stuck
    (g x a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotApply : ∀ f y, g ≠ Term.Apply f y)
    (hNotVar : ∀ name T, g ≠ Term.Var name T)
    (hNotStuck : g ≠ Term.Stuck)
    (hNotBinderOuter :
      ∀ q v vs,
        Term.Apply g x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hInnerTranslate :
      __eo_to_smt (Term.Apply g x) =
        SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt x))
    (hInnerGeneric :
      __smtx_typeof (SmtTerm.Apply (__eo_to_smt g) (__eo_to_smt x)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt g)) (__smtx_typeof (__eo_to_smt x)))
    (hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a))
    (hFTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply (Term.Apply g x) a))
    (hRecHead :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs) =
        __eo_typeof (Term.Apply g x) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs))
    (hRecA :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs))
    (hHeadSubTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply g x) xs ts bvs) ≠
        Term.Stuck)
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply g x) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply g x) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply g x) a) xs ts bvs) := by
  have hGenericOuter :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt (Term.Apply g x)))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a)
      (TranslationProofs.eo_to_smt_apply_ne_dt_sel g x)
      (TranslationProofs.eo_to_smt_apply_ne_dt_tester g x)
  have hHeadTrans :
      RuleProofs.eo_has_smt_translation (Term.Apply g x) :=
    (SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      (Term.Apply g x) a hOuterTranslate hGenericOuter hFTrans).1
  exact
    substitute_simul_apply_applied_head_generic_preserves_type_and_translation_of_typeof_ne_stuck
      g x a xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinderOuter hOuterTranslate
      hFTrans hRecHead hRecA hHeadSubTy hTy

end SubstitutePreservationSupport
