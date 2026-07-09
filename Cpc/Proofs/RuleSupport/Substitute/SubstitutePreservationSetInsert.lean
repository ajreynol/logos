import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinarySetHelpers

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

theorem substitute_simul_set_insert_preserves_type_and_translation_of_typeof_ne_stuck
    (typedList base xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.set_insert) typedList ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
          base))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base) xs ts bvs) ≠
        Term.Stuck)
    (hTypedListSmtType :
      ∀ t,
        sizeOf t < sizeOf typedList ->
        RuleProofs.eo_has_smt_translation t ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) t xs ts bvs) ≠
          Term.Stuck ->
          __smtx_typeof
              (__eo_to_smt
                (__substitute_simul_rec (Term.Boolean false) t xs ts bvs)) =
            __smtx_typeof (__eo_to_smt t))
    (hRecBase :
      RuleProofs.eo_has_smt_translation base ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) base xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) base xs ts bvs) =
          __eo_typeof base ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) base xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base) xs ts bvs) =
      __eo_typeof
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
          base) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base) xs ts bvs) := by
  let typedListSub :=
    __substitute_simul_rec (Term.Boolean false) typedList xs ts bvs
  let baseSub :=
    __substitute_simul_rec (Term.Boolean false) base xs ts bvs
  have hType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
              base) xs ts bvs) =
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base) :=
    SubstituteSupport.substitute_simul_set_insert_typeof_eq_of_typeof_ne_stuck
      typedList base xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans
      (fun hBaseTrans hBaseTy => (hRecBase hBaseTrans hBaseTy).1)
      hTy
  refine ⟨hType, ?_⟩
  have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.UOp UserOp.set_insert) xs ts bvs =
        Term.UOp UserOp.set_insert :=
    SubstituteSupport.substitute_simul_rec_uop_eq_self
      UserOp.set_insert xs ts bvs hXsEnv hBvsEnv hTs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp UserOp.set_insert) typedList) xs ts bvs =
        __eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.UOp UserOp.set_insert) typedList
        xs ts bvs hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [typedListSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_insert) typedList)
            base) xs ts bvs =
        __eo_mk_apply
          (__eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false)
        (Term.Apply (Term.UOp UserOp.set_insert) typedList)
        base xs ts bvs hisr hxs hts hbvs hNotBinder
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
    instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub ≠
        Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp UserOp.set_insert) typedListSub =
        Term.Apply (Term.UOp UserOp.set_insert) typedListSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp UserOp.set_insert) typedListSub hInnerNe
  have hOuterMk :
      __eo_mk_apply
          (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub =
        Term.Apply
          (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
          baseSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.set_insert) typedListSub) baseSub (by
        rw [← hInnerMk]
        exact hOuterNe)
  have hTyApply :
      __eo_typeof
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.set_insert) typedListSub)
            baseSub) ≠
        Term.Stuck := by
    rwa [hInnerMk, hOuterMk] at hTyMk
  have hTypedListSubTyped :
      ∃ T,
        __eo_typeof typedListSub =
          Term.Apply (Term.UOp UserOp._at__at_TypedList) T :=
    eo_typeof_set_insert_left_typed_list_of_ne_stuck
      (__eo_typeof typedListSub) (__eo_typeof baseSub) (by
        change
          __eo_typeof_set_insert (__eo_typeof typedListSub)
              (__eo_typeof baseSub) ≠
            Term.Stuck at hTyApply
        exact hTyApply)
  have hOrigNN :
      __smtx_typeof
          (__eo_to_smt_set_insert typedList (__eo_to_smt base)) ≠
        SmtType.None := by
    unfold RuleProofs.eo_has_smt_translation at hFTrans
    change
      __smtx_typeof
          (__eo_to_smt_set_insert typedList (__eo_to_smt base)) ≠
        SmtType.None at hFTrans
    exact hFTrans
  rcases eo_to_smt_set_insert_shape_of_non_none
      typedList (__eo_to_smt base) hOrigNN with
    ⟨A, _hOrigSet, hBaseSmt, hElem, hANN⟩
  have hElemNN : __eo_to_smt_typed_list_elem_type typedList ≠ SmtType.None := by
    rw [hElem]
    exact hANN
  have hBaseTrans :
      RuleProofs.eo_has_smt_translation base := by
    unfold RuleProofs.eo_has_smt_translation
    rw [hBaseSmt]
    simp
  have hBaseSubTyNe : __eo_typeof baseSub ≠ Term.Stuck := by
    intro hBaseStuck
    apply hTyApply
    change
      __eo_typeof_set_insert (__eo_typeof typedListSub)
          (__eo_typeof baseSub) =
        Term.Stuck
    rw [hBaseStuck]
    exact SubstituteSupport.eo_typeof_set_insert_stuck_right
      (__eo_typeof typedListSub)
  have hBaseBoth := hRecBase hBaseTrans hBaseSubTyNe
  have hBaseSubSmt :
      __smtx_typeof (__eo_to_smt baseSub) = SmtType.Set A := by
    have hBaseMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation base hBaseTrans
    have hBaseSubMatch :=
      TranslationProofs.eo_to_smt_typeof_matches_translation baseSub
        hBaseBoth.2
    rw [hBaseSubMatch, hBaseBoth.1, ← hBaseMatch, hBaseSmt]
  have hElemSubEq :
      __eo_to_smt_typed_list_elem_type typedListSub =
        __eo_to_smt_typed_list_elem_type typedList := by
    simpa [typedListSub] using
      substitute_simul_rec_typed_list_elem_type_eq_of_non_none
        typedList xs ts bvs hXsEnv hBvsEnv hTs
        hTypedListSmtType hTypedListSubTyped hElemNN
  have hElemSub :
      __eo_to_smt_typed_list_elem_type typedListSub = A := by
    rw [hElemSubEq, hElem]
  have hSubSmt :
      __smtx_typeof
          (__eo_to_smt_set_insert typedListSub (__eo_to_smt baseSub)) =
        SmtType.Set A :=
    smt_set_insert_type_eq_of_base_set_and_elem_type
      typedListSub (__eo_to_smt baseSub) A hBaseSubSmt hElemSub hANN
  rw [hSubstEq, hInnerMk, hOuterMk]
  unfold RuleProofs.eo_has_smt_translation
  change
    __smtx_typeof
        (__eo_to_smt_set_insert typedListSub (__eo_to_smt baseSub)) ≠
      SmtType.None
  rw [hSubSmt]
  simp

end SubstitutePreservationSupport
