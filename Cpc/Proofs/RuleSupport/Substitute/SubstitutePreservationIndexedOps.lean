module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationDtSel
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationDtSel

public section

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

theorem smt_numeral_nonneg_of_eo_to_smt_nat_is_valid
    {idx : Term}
    (hValid : __eo_to_smt_nat_is_valid idx = true) :
    ∃ n : native_Int,
      __eo_to_smt idx = SmtTerm.Numeral n ∧
        native_zleq 0 n = true := by
  cases idx <;> simp [__eo_to_smt_nat_is_valid] at hValid ⊢
  case Numeral n =>
    exact ⟨n, rfl, hValid⟩

theorem apply_uop1_arg_rule_has_smt_translation_of_rule
    (op : UserOp1) (idx a : Term)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp1 op idx) a)) :
    RuleProofs.eo_has_smt_translation a := by
  have hTransEo :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 op idx) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  have hAEo :
      eoHasSmtTranslation a :=
    apply_uop1_arg_has_smt_translation_of_has_smt_translation hTransEo
  simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation] using hAEo

theorem smt_typeof_subst_arg_eq_of_type_eq
    {X a : Term} {T : SmtType}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hXTyEq : __eo_typeof X = __eo_typeof a)
    (hASmtTy : __smtx_typeof (__eo_to_smt a) = T) :
    __smtx_typeof (__eo_to_smt X) = T := by
  have hXSmtMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
  have hASmtMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation a hATrans
  rw [hXSmtMatch, hXTyEq, ← hASmtMatch, hASmtTy]

theorem smt_typeof_subst_arg_eq_bitvec_of_type_eq
    {X a : Term} {w : native_Nat}
    (hXTrans : RuleProofs.eo_has_smt_translation X)
    (hATrans : RuleProofs.eo_has_smt_translation a)
    (hXTyEq : __eo_typeof X = __eo_typeof a)
    (hASmtTy : __smtx_typeof (__eo_to_smt a) = SmtType.BitVec w) :
    __smtx_typeof (__eo_to_smt X) = SmtType.BitVec w := by
  exact smt_typeof_subst_arg_eq_of_type_eq
    hXTrans hATrans hXTyEq hASmtTy

private theorem eo_typeof_re_loop_arg_reglan_of_ne_stuck
    {A lo B hi C : Term}
    (h : __eo_typeof_re_loop A lo B hi C ≠ Term.Stuck) :
    C = Term.UOp UserOp.RegLan := by
  unfold __eo_typeof_re_loop at h
  split at h <;> simp at h ⊢

private theorem eo_typeof_extract_arg_bitvec_of_ne_stuck
    {A hi B lo C : Term}
    (h : __eo_typeof_extract A hi B lo C ≠ Term.Stuck) :
    ∃ w, C = Term.Apply (Term.UOp UserOp.BitVec) w := by
  unfold __eo_typeof_extract at h
  split at h <;> simp at h ⊢

private theorem substitute_simul_apply_uop2_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (op : UserOp2) (i j a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp2 op i j) a))
    (hArgExtract :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 op i j) a) ->
        eoHasSmtTranslation a)
    (hArgTyNe :
      ∀ X,
        __eo_typeof (Term.Apply (Term.UOp2 op i j) X) ≠ Term.Stuck ->
          __eo_typeof X ≠ Term.Stuck)
    (hTypeCong :
      ∀ X Y,
        __eo_typeof X = __eo_typeof Y ->
          __eo_typeof (Term.Apply (Term.UOp2 op i j) X) =
            __eo_typeof (Term.Apply (Term.UOp2 op i j) Y))
    (hBuild :
      ∀ X,
        RuleProofs.eo_has_smt_translation X ->
          __eo_typeof X = __eo_typeof a ->
          __eo_typeof (Term.Apply (Term.UOp2 op i j) X) ≠ Term.Stuck ->
            RuleProofs.eo_has_smt_translation
              (Term.Apply (Term.UOp2 op i j) X))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp2 op i j) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 op i j) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp2 op i j) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 op i j) a) xs ts bvs) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hNotBinder :
      ∀ q v vs,
        Term.UOp2 op i j ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
    intro q v vs h
    cases h
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 op i j) a) xs ts bvs =
        __eo_mk_apply
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.UOp2 op i j) xs ts bvs)
          aSub := by
    simpa [aSub] using
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp2 op i j) a xs ts bvs
        hisr hxs hts hbvs hNotBinder
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp2 op i j) xs ts bvs ≠
        Term.Stuck :=
    SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
      (Term.UOp2 op i j) a xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hTy
  have hHeadEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp2 op i j) xs ts bvs =
        Term.UOp2 op i j :=
    SubstituteSupport.substitute_simul_rec_atom_eq_self_of_ne_stuck
      (Term.UOp2 op i j) xs ts bvs hXsEnv hBvsEnv hTs
      (by intro f x h; cases h)
      (by intro name T h; cases h)
      (by intro h; cases h)
      hHeadNe
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.UOp2 op i j) aSub) ≠
        Term.Stuck := by
    simpa [hSubstEq, hHeadEq] using hTy
  have hMk :
      __eo_mk_apply (Term.UOp2 op i j) aSub =
        Term.Apply (Term.UOp2 op i j) aSub :=
    SubstituteSupport.eo_mk_apply_eq_apply_of_typeof_ne_stuck hTyMk
  have hResultEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 op i j) a) xs ts bvs =
        Term.Apply (Term.UOp2 op i j) aSub := by
    rw [hSubstEq, hHeadEq, hMk]
  have hTyApply :
      __eo_typeof (Term.Apply (Term.UOp2 op i j) aSub) ≠
        Term.Stuck := by
    simpa [hResultEq] using hTy
  have hTransEo :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 op i j) a) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hTrans
  have hATrans :
      RuleProofs.eo_has_smt_translation a := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hArgExtract hTransEo
  have hABoth :
      __eo_typeof aSub = __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation aSub :=
    hARec hATrans (hArgTyNe aSub hTyApply)
  refine ⟨?_, ?_⟩
  · rw [hResultEq]
    exact hTypeCong aSub a hABoth.1
  · rw [hResultEq]
    exact hBuild aSub hABoth.2 hABoth.1 hTyApply

theorem substitute_simul_apply_re_loop_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (lo hi a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop2_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp2.re_loop lo hi a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop2_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_re_loop (__eo_typeof lo) lo (__eo_typeof hi) hi
              (__eo_typeof X) ≠
            Term.Stuck at hApp
        have hXTy := eo_typeof_re_loop_arg_reglan_of_ne_stuck hApp
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof_re_loop (__eo_typeof lo) lo (__eo_typeof hi) hi
              (__eo_typeof X) =
            __eo_typeof_re_loop (__eo_typeof lo) lo (__eo_typeof hi) hi
              (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans _hXTyEq hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi)
                (__eo_to_smt X)) ≠
            SmtType.None
        have hTransEo :
            eoHasSmtTranslation
              (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) a) := by
          simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
            using hTrans
        rcases re_loop_indices_nat_valid_and_arg_has_smt_translation hTransEo with
          ⟨hLoValid, hHiValid, _hATrans⟩
        rcases smt_numeral_nonneg_of_eo_to_smt_nat_is_valid hLoValid with
          ⟨loN, hLoNum, hLoNonneg⟩
        rcases smt_numeral_nonneg_of_eo_to_smt_nat_is_valid hHiValid with
          ⟨hiN, hHiNum, hHiNonneg⟩
        change
          __eo_typeof_re_loop (__eo_typeof lo) lo (__eo_typeof hi) hi
              (__eo_typeof X) ≠
            Term.Stuck at hApp
        have hXTy := eo_typeof_re_loop_arg_reglan_of_ne_stuck hApp
        have hXSmt :=
          smt_typeof_eo_to_smt_reglan_of_typeof_reglan hXTrans hXTy
        rw [typeof_re_loop_eq, hLoNum, hHiNum, hXSmt]
        simp [__smtx_typeof_re_loop, hLoNonneg, hHiNonneg, native_ite])
      hARec hTy

theorem substitute_simul_apply_extract_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (hi lo a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp2 UserOp2.extract hi lo) a))
    (hARec :
      RuleProofs.eo_has_smt_translation a ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp2 UserOp2.extract hi lo) a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 UserOp2.extract hi lo) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp2 UserOp2.extract hi lo) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp2 UserOp2.extract hi lo) a) xs ts bvs) := by
  exact
    substitute_simul_apply_uop2_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp2.extract hi lo a xs ts bvs hXsEnv hBvsEnv hTs hTrans
      (fun h =>
        apply_uop2_arg_has_smt_translation_of_has_smt_translation h)
      (fun X hApp => by
        change
          __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
              (__eo_typeof X) ≠
            Term.Stuck at hApp
        rcases eo_typeof_extract_arg_bitvec_of_ne_stuck hApp with
          ⟨w, hXTy⟩
        rw [hXTy]
        intro h
        cases h)
      (fun X Y hXY => by
        change
          __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
              (__eo_typeof X) =
            __eo_typeof_extract (__eo_typeof hi) hi (__eo_typeof lo) lo
              (__eo_typeof Y)
        rw [hXY])
      (fun X hXTrans hXTyEq _hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo)
                (__eo_to_smt X)) ≠
            SmtType.None
        have hTransEo :
            eoHasSmtTranslation
              (Term.Apply (Term.UOp2 UserOp2.extract hi lo) a) := by
          simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
            using hTrans
        have hATrans :
            RuleProofs.eo_has_smt_translation a := by
          have hAEo :
              eoHasSmtTranslation a :=
            apply_uop2_arg_has_smt_translation_of_has_smt_translation hTransEo
          simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
            using hAEo
        have hNN :
            term_has_non_none_type
              (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo)
                (__eo_to_smt a)) := by
          unfold term_has_non_none_type
          have hTransRaw := hTrans
          unfold RuleProofs.eo_has_smt_translation at hTransRaw
          change
            __smtx_typeof
                (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo)
                  (__eo_to_smt a)) ≠
              SmtType.None at hTransRaw
          exact hTransRaw
        rcases extract_args_of_non_none hNN with
          ⟨hiN, loN, w, hHiNum, hLoNum, hASmtTy, hLoNonneg, hWidth,
            hHiBound⟩
        have hXSmtMatch :=
          TranslationProofs.eo_to_smt_typeof_matches_translation X hXTrans
        have hASmtMatch :=
          TranslationProofs.eo_to_smt_typeof_matches_translation a hATrans
        have hXSmtTy :
            __smtx_typeof (__eo_to_smt X) = SmtType.BitVec w := by
          rw [hXSmtMatch, hXTyEq, ← hASmtMatch, hASmtTy]
        rw [typeof_extract_eq, hHiNum, hLoNum, hXSmtTy]
        simp [__smtx_typeof_extract, native_ite, hLoNonneg, hWidth,
          hHiBound])
      hARec hTy

end SubstitutePreservationSupport
