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
  have hOuterTranslate :
      __eo_to_smt (Term.Apply (Term.Apply g x) a) =
        SmtTerm.Apply (__eo_to_smt (Term.Apply g x)) (__eo_to_smt a) :=
    eo_to_smt_apply_apply_generic_of_branch_exclusions
      (g := g) (x := x) (a := a)
      hUOp hNoUpdate hNoTupleUpdate hApplyUOp
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
