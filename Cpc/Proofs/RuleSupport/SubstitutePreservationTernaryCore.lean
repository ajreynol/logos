import Cpc.Proofs.RuleSupport.SubstitutePreservationShared
import Cpc.Proofs.RuleSupport.SubstitutePreservationGenericOps

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

theorem substitute_simul_ternary_op_preserves_type_and_translation_of_typeof_ne_stuck
    (op : UserOp) (x y z xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
          xs ts bvs) ≠
        Term.Stuck)
    (hArgExtract :
      eoHasSmtTranslation
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) ->
        eoHasSmtTranslation x ∧
          eoHasSmtTranslation y ∧
            eoHasSmtTranslation z)
    (hArgTyNe :
      ∀ X Y Z,
        __eo_typeof
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) X) Y) Z) ≠
          Term.Stuck ->
        __eo_typeof X ≠ Term.Stuck ∧
          __eo_typeof Y ≠ Term.Stuck ∧
            __eo_typeof Z ≠ Term.Stuck)
    (hTypeCong :
      ∀ X₁ Y₁ Z₁ X₂ Y₂ Z₂,
        __eo_typeof X₁ = __eo_typeof X₂ ->
        __eo_typeof Y₁ = __eo_typeof Y₂ ->
        __eo_typeof Z₁ = __eo_typeof Z₂ ->
        __eo_typeof
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) X₁) Y₁) Z₁) =
          __eo_typeof
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) X₂) Y₂) Z₂))
    (hBuild :
      ∀ X Y Z,
        RuleProofs.eo_has_smt_translation X ->
          RuleProofs.eo_has_smt_translation Y ->
            RuleProofs.eo_has_smt_translation Z ->
              __eo_typeof
                  (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) X) Y) Z) ≠
                Term.Stuck ->
              RuleProofs.eo_has_smt_translation
                (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) X) Y) Z))
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) x xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) x xs ts bvs) =
          __eo_typeof x ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs) =
          __eo_typeof y ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs))
    (hRecZ :
      RuleProofs.eo_has_smt_translation z ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) z xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) z xs ts bvs) =
          __eo_typeof z ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) z xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
          xs ts bvs) =
      __eo_typeof
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
          xs ts bvs) := by
  let xSub := __substitute_simul_rec (Term.Boolean false) x xs ts bvs
  let ySub := __substitute_simul_rec (Term.Boolean false) y xs ts bvs
  let zSub := __substitute_simul_rec (Term.Boolean false) z xs ts bvs
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hFTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  rcases hArgExtract hFTransEo with ⟨hXTransEo, hYTransEo, hZTransEo⟩
  have hXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hXTransEo
  have hYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hYTransEo
  have hZTrans : RuleProofs.eo_has_smt_translation z := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hZTransEo
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.UOp op) xs ts bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ts bvs hXsEnv hBvsEnv hTs
  have hFirstSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) x) xs ts bvs =
        __eo_mk_apply (Term.UOp op) xSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.UOp op) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSecondNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    exact term_not_eo_list_cons_of_has_smt_translation hXTransEo v vs rfl
  have hSecondSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.Apply (Term.UOp op) x) y xs ts bvs
        hisr hxs hts hbvs hSecondNotBinder
    simpa [ySub, hFirstSub] using hApplyEq
  have hThirdNotBinder :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.UOp op) x) y ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs hEq
    cases hEq
    exact term_not_eo_list_cons_of_has_smt_translation hYTransEo v vs rfl
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
          xs ts bvs =
        __eo_mk_apply
          (__eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub) zSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.Apply (Term.Apply (Term.UOp op) x) y)
        z xs ts bvs hisr hxs hts hbvs hThirdNotBinder
    simpa [zSub, hSecondSub] using hApplyEq
  have hTyMk :
      __eo_typeof
          (__eo_mk_apply
            (__eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub)
            zSub) ≠
        Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hOuterNe :
      __eo_mk_apply
          (__eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub)
          zSub ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hMidNe :
      __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerNe :
      __eo_mk_apply (Term.UOp op) xSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hMidNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp op) xSub =
        Term.Apply (Term.UOp op) xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp op) xSub hInnerNe
  have hMidMk :
      __eo_mk_apply (Term.Apply (Term.UOp op) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp op) xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp op) xSub) ySub (by
        rw [← hInnerMk]
        exact hMidNe)
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.Apply (Term.UOp op) xSub) ySub) zSub =
        Term.Apply (Term.Apply (Term.Apply (Term.UOp op) xSub) ySub)
          zSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.Apply (Term.UOp op) xSub) ySub) zSub (by
        rw [← hMidMk, ← hInnerMk]
        exact hOuterNe)
  have hTyApply :
      __eo_typeof
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) xSub) ySub)
            zSub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hMidMk, hOuterMk] at hTyMk
  rcases hArgTyNe xSub ySub zSub hTyApply with
    ⟨hXSubTy, hYSubTy, hZSubTy⟩
  have hXSubBoth := hRecX hXTrans hXSubTy
  have hYSubBoth := hRecY hYTrans hYSubTy
  have hZSubBoth := hRecZ hZTrans hZSubTy
  refine ⟨?_, ?_⟩
  · rw [hSubstEq, hInnerMk, hMidMk, hOuterMk]
    exact
      hTypeCong xSub ySub zSub x y z
        hXSubBoth.1 hYSubBoth.1 hZSubBoth.1
  · rw [hSubstEq, hInnerMk, hMidMk, hOuterMk]
    exact
      hBuild xSub ySub zSub
        hXSubBoth.2 hYSubBoth.2 hZSubBoth.2 hTyApply


end SubstitutePreservationSupport
