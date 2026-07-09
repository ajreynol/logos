import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationGenericOps
import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationBinaryBvHelpers

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

theorem substitute_simul_re_range_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.re_range) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y) xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.re_range x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder
      hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := UserOp.re_range) (smtOp := SmtTerm.re_range)
          (by rfl)
          (fun hNN =>
            seq_char_binop_args_have_smt_translation_of_non_none
              (ret := SmtType.RegLan)
              (typeof_re_range_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
          h)
      (fun X Y hApp => by
        change __eo_typeof_re_range (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact eo_typeof_re_range_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof_re_range (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof_re_range (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.re_range (__eo_to_smt X) (__eo_to_smt Y)) ≠
            SmtType.None
        change __eo_typeof_re_range (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact
          smt_re_range_non_none_of_eo_typeof_re_range_ne_stuck
            X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_reglan_binop_preserves_type_and_translation_of_typeof_ne_stuck
    (op : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) ≠
        Term.Stuck)
    (hTranslate :
      ∀ X Y,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) X) Y) =
          smtOp (__eo_to_smt X) (__eo_to_smt Y))
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          native_ite (native_Teq (__smtx_typeof X) SmtType.RegLan)
            (native_ite (native_Teq (__smtx_typeof Y) SmtType.RegLan)
              SmtType.RegLan SmtType.None)
            SmtType.None)
    (hEoType :
      ∀ X Y,
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) =
          __eo_typeof_re_concat (__eo_typeof X) (__eo_typeof Y))
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      op x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := op) (smtOp := smtOp)
          (hTranslate x y)
          (fun hNN =>
            reglan_binop_args_have_smt_translation_of_non_none
              (hSmtType (__eo_to_smt x) (__eo_to_smt y)) hNN)
          h)
      (fun X Y hApp => by
        rw [hEoType X Y] at hApp
        exact eo_typeof_re_concat_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        rw [hEoType X₁ X₂, hEoType Y₁ Y₂]
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        rw [hTranslate X Y]
        rw [hEoType X Y] at hApp
        exact
          smt_reglan_binop_non_none_of_eo_typeof_re_concat_ne_stuck
            smtOp hSmtType X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_str_in_re_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.str_in_re) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y) xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.str_in_re x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder
      hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := UserOp.str_in_re) (smtOp := SmtTerm.str_in_re)
          (by rfl)
          (fun hNN =>
            seq_char_reglan_args_have_smt_translation_of_non_none
              (ret := SmtType.Bool)
              (typeof_str_in_re_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
          h)
      (fun X Y hApp => by
        change __eo_typeof_str_in_re (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact eo_typeof_str_in_re_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof_str_in_re (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof_str_in_re (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_in_re (__eo_to_smt X) (__eo_to_smt Y)) ≠
            SmtType.None
        change __eo_typeof_str_in_re (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact
          smt_str_in_re_non_none_of_eo_typeof_str_in_re_ne_stuck
            X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_seq_nth_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.seq_nth) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.seq_nth x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder
      hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := UserOp.seq_nth) (smtOp := SmtTerm.seq_nth)
          (by rfl)
          (fun hNN =>
            seq_nth_args_have_smt_translation_of_non_none hNN)
          h)
      (fun X Y hApp => by
        change __eo_typeof_seq_nth (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact eo_typeof_seq_nth_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof_seq_nth (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof_seq_nth (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.seq_nth (__eo_to_smt X) (__eo_to_smt Y)) ≠
            SmtType.None
        change __eo_typeof_seq_nth (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact
          smt_seq_nth_non_none_of_eo_typeof_seq_nth_ne_stuck
            X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_set_binop_preserves_type_and_translation_of_typeof_ne_stuck
    (op : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) ≠
        Term.Stuck)
    (hTranslate :
      ∀ X Y,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) X) Y) =
          smtOp (__eo_to_smt X) (__eo_to_smt Y))
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          __smtx_typeof_sets_op_2
            (__smtx_typeof X) (__smtx_typeof Y))
    (hEoType :
      ∀ X Y,
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) =
          __eo_typeof_set_union (__eo_typeof X) (__eo_typeof Y))
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      op x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := op) (smtOp := smtOp)
          (hTranslate x y)
          (fun hNN =>
            set_binop_args_have_smt_translation_of_non_none
              (hSmtType (__eo_to_smt x) (__eo_to_smt y)) hNN)
          h)
      (fun X Y hApp => by
        rw [hEoType X Y] at hApp
        exact eo_typeof_set_union_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        rw [hEoType X₁ X₂, hEoType Y₁ Y₂]
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        rw [hTranslate X Y]
        rw [hEoType X Y] at hApp
        exact
          smt_set_binop_non_none_of_eo_typeof_set_union_ne_stuck
            smtOp hSmtType X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_set_member_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.set_member) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.set_member x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder
      hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := UserOp.set_member) (smtOp := SmtTerm.set_member)
          (by rfl)
          (fun hNN =>
            set_member_args_have_smt_translation_of_non_none hNN)
          h)
      (fun X Y hApp => by
        change __eo_typeof_set_member (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact eo_typeof_set_member_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof_set_member (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof_set_member (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.set_member (__eo_to_smt X) (__eo_to_smt Y)) ≠
            SmtType.None
        change __eo_typeof_set_member (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact
          smt_set_member_non_none_of_eo_typeof_set_member_ne_stuck
            X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_set_subset_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.set_subset) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y) xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.set_subset) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp.set_subset x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder
      hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := UserOp.set_subset) (smtOp := SmtTerm.set_subset)
          (by rfl)
          (fun hNN =>
            set_binop_ret_args_have_smt_translation_of_non_none
              (ret := SmtType.Bool)
              (typeof_set_subset_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
          h)
      (fun X Y hApp => by
        change __eo_typeof_set_subset (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact eo_typeof_set_subset_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof_set_subset (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof_set_subset (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.set_subset (__eo_to_smt X) (__eo_to_smt Y)) ≠
            SmtType.None
        change __eo_typeof_set_subset (__eo_typeof X) (__eo_typeof Y) ≠
          Term.Stuck at hApp
        exact
          smt_set_subset_non_none_of_eo_typeof_set_subset_ne_stuck
            X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_array_deq_diff_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp._at_array_deq_diff) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y)
          xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_array_deq_diff) x) y)
          xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_array_deq_diff x y xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hFTrans hTy
      (fun h => array_deq_diff_args_have_smt_translation_of_has_smt_translation h)
      (fun X Y hApp => by
        change
          __eo_typeof__at_array_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact eo_typeof_array_deq_diff_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof__at_array_deq_diff (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof__at_array_deq_diff (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (__eo_to_smt_array_deq_diff (__eo_to_smt X)
                (__smtx_typeof (__eo_to_smt X)) (__eo_to_smt Y)
                (__smtx_typeof (__eo_to_smt Y))) ≠
            SmtType.None
        change
          __eo_typeof__at_array_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact smt_array_deq_diff_non_none_of_eo_typeof_ne_stuck
          X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_sets_deq_diff_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y)
          xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_sets_deq_diff) x) y)
          xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_sets_deq_diff x y xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hFTrans hTy
      (fun h => sets_deq_diff_args_have_smt_translation_of_has_smt_translation h)
      (fun X Y hApp => by
        change
          __eo_typeof__at_sets_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact eo_typeof_sets_deq_diff_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof__at_sets_deq_diff (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof__at_sets_deq_diff (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (__eo_to_smt_sets_deq_diff (__eo_to_smt X)
                (__smtx_typeof (__eo_to_smt X)) (__eo_to_smt Y)
                (__smtx_typeof (__eo_to_smt Y))) ≠
            SmtType.None
        change
          __eo_typeof__at_sets_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact smt_sets_deq_diff_non_none_of_eo_typeof_ne_stuck
          X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_strings_deq_diff_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y)
          xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_deq_diff) x) y)
          xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_strings_deq_diff x y xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hFTrans hTy
      (fun h => strings_deq_diff_args_have_smt_translation_of_has_smt_translation h)
      (fun X Y hApp => by
        change
          __eo_typeof__at_strings_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact eo_typeof_strings_deq_diff_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof__at_strings_deq_diff (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof__at_strings_deq_diff (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.seq_diff (__eo_to_smt X) (__eo_to_smt Y)) ≠
            SmtType.None
        change
          __eo_typeof__at_strings_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact smt_strings_deq_diff_non_none_of_eo_typeof_ne_stuck
          X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_strings_stoi_result_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y)
          xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) x) y)
          xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_strings_stoi_result x y xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hFTrans hTy
      (fun h => strings_stoi_result_args_have_smt_translation_of_has_smt_translation h)
      (fun X Y hApp => by
        change
          __eo_typeof__at_strings_stoi_result (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact eo_typeof_strings_stoi_result_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof__at_strings_stoi_result (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof__at_strings_stoi_result (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.str_to_int
                (SmtTerm.str_substr (__eo_to_smt X) (SmtTerm.Numeral 0)
                  (__eo_to_smt Y))) ≠
            SmtType.None
        change
          __eo_typeof__at_strings_stoi_result (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact smt_strings_stoi_result_non_none_of_eo_typeof_ne_stuck
          X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_strings_itos_result_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp._at_strings_itos_result) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y)
          xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_itos_result) x) y)
          xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_strings_itos_result x y xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hFTrans hTy
      (fun h => strings_itos_result_args_have_smt_translation_of_has_smt_translation h)
      (fun X Y hApp => by
        change
          __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact eo_int_binop_args_not_stuck
          (eo_typeof_div_arg_types_of_ne_stuck hApp))
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof_div (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof_div (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.mod (__eo_to_smt X)
                (SmtTerm.multmult (SmtTerm.Numeral 10)
                  (__eo_to_smt Y))) ≠
            SmtType.None
        change
          __eo_typeof_div (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact smt_strings_itos_result_non_none_of_eo_typeof_ne_stuck
          X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_strings_num_occur_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp._at_strings_num_occur) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y)
          xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y)
          xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck_arg_type_eq
      UserOp._at_strings_num_occur x y xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hFTrans hTy
      (fun h => strings_num_occur_args_have_smt_translation_of_has_smt_translation h)
      (fun X Y hApp => by
        change
          __eo_typeof__at_strings_deq_diff (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact eo_typeof_strings_deq_diff_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof__at_strings_deq_diff (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof__at_strings_deq_diff (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hXTy hYTy _hApp => by
        have hFTransEo :
            eoHasSmtTranslation
              (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_num_occur) x) y) := by
          simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
            using hFTrans
        rcases strings_num_occur_args_have_smt_translation_of_has_smt_translation
            hFTransEo with ⟨hXOrigEo, hYOrigEo⟩
        have hXOrigTrans : RuleProofs.eo_has_smt_translation x := by
          simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
            using hXOrigEo
        have hYOrigTrans : RuleProofs.eo_has_smt_translation y := by
          simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
            using hYOrigEo
        have hXSmt :
            __smtx_typeof (__eo_to_smt X) =
              __smtx_typeof (__eo_to_smt x) := by
          rw [
            TranslationProofs.eo_to_smt_typeof_matches_translation
              X hXTrans,
            TranslationProofs.eo_to_smt_typeof_matches_translation
              x hXOrigTrans,
            hXTy]
        have hYSmt :
            __smtx_typeof (__eo_to_smt Y) =
              __smtx_typeof (__eo_to_smt y) := by
          rw [
            TranslationProofs.eo_to_smt_typeof_matches_translation
              Y hYTrans,
            TranslationProofs.eo_to_smt_typeof_matches_translation
              y hYOrigTrans,
            hYTy]
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.div
                (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt X))
                  (SmtTerm.str_len
                    (SmtTerm.str_replace_all (__eo_to_smt X) (__eo_to_smt Y)
                      (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
                (SmtTerm.str_len (__eo_to_smt Y))) ≠
            SmtType.None
        have hOrig :
            __smtx_typeof
                (SmtTerm.div
                  (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt x))
                    (SmtTerm.str_len
                      (SmtTerm.str_replace_all (__eo_to_smt x) (__eo_to_smt y)
                        (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
                  (SmtTerm.str_len (__eo_to_smt y))) ≠
              SmtType.None := by
          unfold RuleProofs.eo_has_smt_translation at hFTrans
          change
            __smtx_typeof
                (SmtTerm.div
                  (SmtTerm.neg (SmtTerm.str_len (__eo_to_smt x))
                    (SmtTerm.str_len
                      (SmtTerm.str_replace_all (__eo_to_smt x) (__eo_to_smt y)
                        (SmtTerm.seq_empty (SmtType.Seq SmtType.Char)))))
                  (SmtTerm.str_len (__eo_to_smt y))) ≠
              SmtType.None at hFTrans
          exact hFTrans
        rw [smt_strings_num_occur_typeof_congr hXSmt hYSmt]
        exact hOrig)
        hRecX hRecY

theorem substitute_simul_str_prefixof_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.str_prefixof) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y)
          xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y)
            xs ts bvs) := by
  have hFTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) x) y) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  rcases
      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
        (eoOp := UserOp.str_prefixof) (smtOp := SmtTerm.str_prefixof)
        (by rfl)
        (fun hNN =>
          seq_binop_ret_args_have_smt_translation_of_non_none
            (typeof_str_prefixof_eq (__eo_to_smt x) (__eo_to_smt y))
            hNN)
        hFTransEo with
    ⟨hOrigXEo, hOrigYEo⟩
  have hOrigXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hOrigXEo
  have hOrigYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hOrigYEo
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck_arg_type_eq
      UserOp.str_prefixof x y xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := UserOp.str_prefixof) (smtOp := SmtTerm.str_prefixof)
          (by rfl)
          (fun hNN =>
            seq_binop_ret_args_have_smt_translation_of_non_none
              (typeof_str_prefixof_eq (__eo_to_smt x) (__eo_to_smt y))
              hNN)
          h)
      (fun X Y hApp => by
        change
          __eo_typeof_str_contains (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact eo_typeof_str_contains_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof_str_contains (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof_str_contains (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hXTyEq hYTyEq _hApp =>
        seq_bool_binop_has_translation_of_original_type_eq
          UserOp.str_prefixof SmtTerm.str_prefixof
          (fun X Y => by rfl)
          (fun X Y => typeof_str_prefixof_eq X Y)
          x y X Y hFTrans hOrigXTrans hOrigYTrans
          hXTrans hYTrans hXTyEq hYTyEq)
      hRecX hRecY

theorem substitute_simul_str_suffixof_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp.str_suffixof) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y)
          xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y)
            xs ts bvs) =
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y) ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y)
            xs ts bvs) := by
  have hFTransEo :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) x) y) := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hFTrans
  rcases
      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
        (eoOp := UserOp.str_suffixof) (smtOp := SmtTerm.str_suffixof)
        (by rfl)
        (fun hNN =>
          seq_binop_ret_args_have_smt_translation_of_non_none
            (typeof_str_suffixof_eq (__eo_to_smt x) (__eo_to_smt y))
            hNN)
        hFTransEo with
    ⟨hOrigXEo, hOrigYEo⟩
  have hOrigXTrans : RuleProofs.eo_has_smt_translation x := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hOrigXEo
  have hOrigYTrans : RuleProofs.eo_has_smt_translation y := by
    simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation]
      using hOrigYEo
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck_arg_type_eq
      UserOp.str_suffixof x y xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := UserOp.str_suffixof) (smtOp := SmtTerm.str_suffixof)
          (by rfl)
          (fun hNN =>
            seq_binop_ret_args_have_smt_translation_of_non_none
              (typeof_str_suffixof_eq (__eo_to_smt x) (__eo_to_smt y))
              hNN)
          h)
      (fun X Y hApp => by
        change
          __eo_typeof_str_contains (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact eo_typeof_str_contains_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof_str_contains (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof_str_contains (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hXTyEq hYTyEq _hApp =>
        seq_bool_binop_has_translation_of_original_type_eq
          UserOp.str_suffixof SmtTerm.str_suffixof
          (fun X Y => by rfl)
          (fun X Y => typeof_str_suffixof_eq X Y)
          x y X Y hFTrans hOrigXTrans hOrigYTrans
          hXTrans hYTrans hXTyEq hYTyEq)
      hRecX hRecY

theorem substitute_simul_from_bools_preserves_type_and_translation_of_typeof_ne_stuck
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp UserOp._at_from_bools) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)
          xs ts bvs) ≠
        Term.Stuck)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)
          xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp UserOp._at_from_bools) x) y)
          xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      UserOp._at_from_bools x y xs ts bvs hXsEnv hBvsEnv hTs
      hNotBinder hFTrans hTy
      (fun h => from_bools_args_have_smt_translation_of_has_smt_translation h)
      (fun X Y hApp => by
        change
          __eo_typeof__at_from_bools (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact eo_typeof_from_bools_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        change
          __eo_typeof__at_from_bools (__eo_typeof X₁) (__eo_typeof X₂) =
            __eo_typeof__at_from_bools (__eo_typeof Y₁) (__eo_typeof Y₂)
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        change
          __smtx_typeof
              (SmtTerm.concat
                (SmtTerm.ite (__eo_to_smt X)
                  (SmtTerm.Binary 1 1) (SmtTerm.Binary 1 0))
                (__eo_to_smt Y)) ≠
            SmtType.None
        change
          __eo_typeof__at_from_bools (__eo_typeof X) (__eo_typeof Y) ≠
            Term.Stuck at hApp
        exact smt_from_bools_non_none_of_eo_typeof_ne_stuck
          X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_bv_binop_preserves_type_and_translation_of_typeof_ne_stuck
    (op : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) ≠
        Term.Stuck)
    (hTranslate :
      ∀ X Y,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) X) Y) =
          smtOp (__eo_to_smt X) (__eo_to_smt Y))
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          __smtx_typeof_bv_op_2 (__smtx_typeof X) (__smtx_typeof Y))
    (hEoType :
      ∀ X Y,
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) =
          __eo_typeof_bvand (__eo_typeof X) (__eo_typeof Y))
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      op x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := op) (smtOp := smtOp)
          (hTranslate x y)
          (fun hNN =>
            bv_binop_args_have_smt_translation_of_non_none
              (hSmtType (__eo_to_smt x) (__eo_to_smt y)) hNN)
          h)
      (fun X Y hApp => by
        rw [hEoType X Y] at hApp
        exact eo_typeof_bvand_args_not_stuck_of_ne_stuck hApp)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        rw [hEoType X₁ X₂, hEoType Y₁ Y₂]
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        rw [hTranslate X Y, hSmtType]
        rw [hEoType X Y] at hApp
        exact smt_bv_binop_non_none_of_eo_typeof_bvand_ne_stuck
          X Y hXTrans hYTrans hApp)
      hRecX hRecY

theorem substitute_simul_bv_binop_ret_preserves_type_and_translation_of_typeof_ne_stuck
    (op : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (eoTypeFn : Term -> Term -> Term) (ret : SmtType)
    (x y xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) ≠
        Term.Stuck)
    (hTranslate :
      ∀ X Y,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp op) X) Y) =
          smtOp (__eo_to_smt X) (__eo_to_smt Y))
    (hSmtType :
      ∀ X Y,
        __smtx_typeof (smtOp X Y) =
          __smtx_typeof_bv_op_2_ret
            (__smtx_typeof X) (__smtx_typeof Y) ret)
    (hEoType :
      ∀ X Y,
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) =
          eoTypeFn (__eo_typeof X) (__eo_typeof Y))
    (hArgTypes :
      ∀ {A B},
        eoTypeFn A B ≠ Term.Stuck ->
          ∃ w,
            A = Term.Apply (Term.UOp UserOp.BitVec) w ∧
              B = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hRet : ret ≠ SmtType.None)
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
            (__substitute_simul_rec (Term.Boolean false) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) := by
  exact
    substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
      op x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans hTy
      (fun h =>
        apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
          (eoOp := op) (smtOp := smtOp)
          (hTranslate x y)
          (fun hNN =>
            bv_binop_ret_args_have_smt_translation_of_non_none
              (hSmtType (__eo_to_smt x) (__eo_to_smt y)) hNN)
          h)
      (fun X Y hApp => by
        rw [hEoType X Y] at hApp
        rcases hArgTypes hApp with ⟨w, hXTy, hYTy⟩
        constructor
        · intro hStuck
          rw [hXTy] at hStuck
          cases hStuck
        · intro hStuck
          rw [hYTy] at hStuck
          cases hStuck)
      (fun X₁ Y₁ X₂ Y₂ hX hY => by
        rw [hEoType X₁ X₂, hEoType Y₁ Y₂]
        rw [hX, hY])
      (fun X Y hXTrans hYTrans hApp => by
        unfold RuleProofs.eo_has_smt_translation
        rw [hTranslate X Y, hSmtType]
        rw [hEoType X Y] at hApp
        exact
          smt_bv_binop_ret_non_none_of_eo_bitvec_arg_types
            X Y hXTrans hYTrans (hArgTypes hApp) hRet)
      hRecX hRecY


end SubstitutePreservationSupport
