module

public import Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationAtomApply
import all Cpc.Proofs.RuleSupport.Substitute.SubstitutePreservationAtomApply

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

/-- SMT-side facts for atom heads that use the generic application translation. -/
theorem generic_atom_head_smt_apply_conditions
    (F a : Term)
    (hNotApply : ∀ g x, F ≠ Term.Apply g x)
    (hNotVar : ∀ name T, F ≠ Term.Var name T)
    (hNoUOp : ∀ op, F ≠ Term.UOp op)
    (hNoUOp1 : ∀ op x, F ≠ Term.UOp1 op x)
    (hNoUOp2 : ∀ op x y, F ≠ Term.UOp2 op x y)
    (hNoUOp3 : ∀ op w x y, F ≠ Term.UOp3 op w x y)
    (hNoDtCons : ∀ s d i, F ≠ Term.DtCons s d i)
    (hNoDtSel : ∀ s d i j, F ≠ Term.DtSel s d i j)
    (hNotStuck : F ≠ Term.Stuck)
    (hNoUConst : ∀ i U, F ≠ Term.UConst i U) :
    __eo_to_smt (Term.Apply F a) =
        SmtTerm.Apply (__eo_to_smt F) (__eo_to_smt a) ∧
      (∀ s d i j, __eo_to_smt F ≠ SmtTerm.DtSel s d i j) ∧
      (∀ s d i, __eo_to_smt F ≠ SmtTerm.DtTester s d i) := by
  constructor
  · cases F with
    | UOp op =>
        exact False.elim (hNoUOp op rfl)
    | UOp1 op x =>
        exact False.elim (hNoUOp1 op x rfl)
    | UOp2 op x y =>
        exact False.elim (hNoUOp2 op x y rfl)
    | UOp3 op x y z =>
        exact False.elim (hNoUOp3 op x y z rfl)
    | Apply g x =>
        exact False.elim (hNotApply g x rfl)
    | Var name T =>
        exact False.elim (hNotVar name T rfl)
    | DtCons s d i =>
        exact False.elim (hNoDtCons s d i rfl)
    | DtSel s d i j =>
        exact False.elim (hNoDtSel s d i j rfl)
    | Stuck =>
        exact False.elim (hNotStuck rfl)
    | UConst i U =>
        exact False.elim (hNoUConst i U rfl)
    | _ => rfl
  constructor
  · intro s d i j hEq
    cases F with
    | UOp op =>
        exact hNoUOp op rfl
    | UOp1 op x =>
        exact hNoUOp1 op x rfl
    | UOp2 op x y =>
        exact hNoUOp2 op x y rfl
    | UOp3 op x y z =>
        exact hNoUOp3 op x y z rfl
    | Apply g x =>
        exact hNotApply g x rfl
    | Var name T =>
        exact hNotVar name T rfl
    | DtCons s0 d0 i0 =>
        exact hNoDtCons s0 d0 i0 rfl
    | DtSel s0 d0 i0 j0 =>
        exact hNoDtSel s0 d0 i0 j0 rfl
    | Stuck =>
        exact hNotStuck rfl
    | UConst i0 U =>
        exact hNoUConst i0 U rfl
    | _ => cases hEq
  · intro s d i hEq
    cases F with
    | UOp op =>
        exact hNoUOp op rfl
    | UOp1 op x =>
        exact hNoUOp1 op x rfl
    | UOp2 op x y =>
        exact hNoUOp2 op x y rfl
    | UOp3 op x y z =>
        exact hNoUOp3 op x y z rfl
    | Apply g x =>
        exact hNotApply g x rfl
    | Var name T =>
        exact hNotVar name T rfl
    | DtCons s0 d0 i0 =>
        exact hNoDtCons s0 d0 i0 rfl
    | DtSel s0 d0 i0 j0 =>
        exact hNoDtSel s0 d0 i0 j0 rfl
    | Stuck =>
        exact hNotStuck rfl
    | UConst i0 U =>
        exact hNoUConst i0 U rfl
    | _ => cases hEq

/-- Combined substitution preservation for an application headed by a unary
special operator. Operator-specific callers provide only argument extraction,
argument type non-stuckness, result type congruence, and translation rebuilding
for the rebuilt application. -/
theorem substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (op : UserOp) (a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.UOp op ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp op) a))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ts bvs) ≠
        Term.Stuck)
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
    (hBuild :
      ∀ X,
        RuleProofs.eo_has_smt_translation X ->
          __eo_typeof (Term.Apply (Term.UOp op) X) ≠ Term.Stuck ->
            RuleProofs.eo_has_smt_translation
              (Term.Apply (Term.UOp op) X))
    (hRecArg :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
          __eo_typeof a ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp op) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ts bvs) := by
  refine ⟨?_, ?_⟩
  · exact
      SubstituteSupport.substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
        op a xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans
        hArgExtract hArgTyNe hTypeCong
        (fun hATrans hATy => (hRecArg hATrans hATy).1)
        hTy
  · exact
      SubstituteTranslatabilitySupport.substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
        op a xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans hTy
        hArgExtract hArgTyNe hBuild
        (fun hATrans hATy => (hRecArg hATrans hATy).2)

/-- Combined unary preservation variant for operators whose SMT rebuild proof
needs the substituted argument's preserved EO type. -/
theorem substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck_arg_type_eq
    {isRename : Bool}
    (op : UserOp) (a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hNotBinder :
      ∀ q v vs,
        Term.UOp op ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp op) a))
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ts bvs) ≠
        Term.Stuck)
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
    (hBuild :
      ∀ X,
        RuleProofs.eo_has_smt_translation X ->
          __eo_typeof X = __eo_typeof a ->
            __eo_typeof (Term.Apply (Term.UOp op) X) ≠ Term.Stuck ->
              RuleProofs.eo_has_smt_translation
                (Term.Apply (Term.UOp op) X))
    (hRecArg :
      RuleProofs.eo_has_smt_translation a ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs) =
          __eo_typeof a ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) a xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp op) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ts bvs) := by
  let aSub := __substitute_simul_rec (Term.Boolean isRename) a xs ts bvs
  have hType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.UOp op) a) xs ts bvs) =
        __eo_typeof (Term.Apply (Term.UOp op) a) :=
    SubstituteSupport.substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
      op a xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans
      hArgExtract hArgTyNe hTypeCong
      (fun hATrans hATy => (hRecArg hATrans hATy).1)
      hTy
  refine ⟨hType, ?_⟩
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp op) xs ts bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ts bvs hXsEnv hBvsEnv hTs
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) a) xs ts bvs =
        __eo_mk_apply (Term.UOp op) aSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp op) a xs ts bvs
        hisr hxs hts hbvs hNotBinder
    simpa [aSub, hHeadSub] using hApplyEq
  have hTyMk :
      __eo_typeof (__eo_mk_apply (Term.UOp op) aSub) ≠ Term.Stuck := by
    rwa [hSubstEq] at hTy
  have hMk :
      __eo_mk_apply (Term.UOp op) aSub =
        Term.Apply (Term.UOp op) aSub :=
    instantiate_eo_mk_apply_eq_apply_of_typeof_ne_stuck
      (Term.UOp op) aSub hTyMk
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
  have hASubRec := hRecArg hATrans (hArgTyNe aSub hTyApply)
  rw [hSubstEq, hMk]
  exact hBuild aSub hASubRec.2 hASubRec.1 hTyApply

/-- Combined substitution preservation for a fully-applied binary special
operator. Binary heads such as `(and x)` are not generally SMT-translatable on
their own, so the recursive calls are made directly on the two operands. -/
theorem substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck
    {isRename : Bool}
    (op : UserOp) (x y xs ts bvs : Term)
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
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) ≠
        Term.Stuck)
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
    (hBuild :
      ∀ X Y,
        RuleProofs.eo_has_smt_translation X ->
          RuleProofs.eo_has_smt_translation Y ->
          __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) ≠
            Term.Stuck ->
          RuleProofs.eo_has_smt_translation
            (Term.Apply (Term.Apply (Term.UOp op) X) Y))
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) =
          __eo_typeof x ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) =
          __eo_typeof y ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) := by
  refine ⟨?_, ?_⟩
  · exact
      SubstituteSupport.substitute_simul_binary_op_typeof_eq_of_typeof_ne_stuck
        op x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans
        hArgExtract hArgTyNe hTypeCong
        (fun hXTrans hXTy => (hRecX hXTrans hXTy).1)
        (fun hYTrans hYTy => (hRecY hYTrans hYTy).1)
        hTy
  · exact
      SubstituteTranslatabilitySupport.substitute_simul_binary_op_has_smt_translation_of_typeof_ne_stuck
        op x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans hTy
        hArgExtract hArgTyNe hBuild
        (fun hXTrans hXTy => (hRecX hXTrans hXTy).2)
        (fun hYTrans hYTy => (hRecY hYTrans hYTy).2)

/-- Binary preservation variant for operators whose translation rebuild depends
on the substituted operands having the same EO types as the original operands. -/
theorem substitute_simul_binary_op_preserves_type_and_translation_of_typeof_ne_stuck_arg_type_eq
    {isRename : Bool}
    (op : UserOp) (x y xs ts bvs : Term)
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
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) ≠
        Term.Stuck)
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
    (hBuild :
      ∀ X Y,
        RuleProofs.eo_has_smt_translation X ->
          RuleProofs.eo_has_smt_translation Y ->
          __eo_typeof X = __eo_typeof x ->
          __eo_typeof Y = __eo_typeof y ->
          __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) X) Y) ≠
            Term.Stuck ->
          RuleProofs.eo_has_smt_translation
            (Term.Apply (Term.Apply (Term.UOp op) X) Y))
    (hRecX :
      RuleProofs.eo_has_smt_translation x ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs) =
          __eo_typeof x ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) x xs ts bvs))
    (hRecY :
      RuleProofs.eo_has_smt_translation y ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs) =
          __eo_typeof y ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean isRename) y xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) := by
  let xSub := __substitute_simul_rec (Term.Boolean isRename) x xs ts bvs
  let ySub := __substitute_simul_rec (Term.Boolean isRename) y xs ts bvs
  have hType :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean isRename)
            (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs) =
        __eo_typeof (Term.Apply (Term.Apply (Term.UOp op) x) y) :=
    SubstituteSupport.substitute_simul_binary_op_typeof_eq_of_typeof_ne_stuck
      op x y xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hFTrans
      hArgExtract hArgTyNe hTypeCong
      (fun hXTrans hXTy => (hRecX hXTrans hXTy).1)
      (fun hYTrans hYTy => (hRecY hYTrans hYTy).1)
      hTy
  refine ⟨hType, ?_⟩
  have hisr : (Term.Boolean isRename : Term) ≠ Term.Stuck := by cases isRename <;> decide
  have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
  have hts : ts ≠ Term.Stuck := eoListAllHaveSmtTranslation_ne_stuck hTs
  have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.UOp op) xs ts bvs =
        Term.UOp op :=
    substitute_simul_rec_uop_eq_self op xs ts bvs hXsEnv hBvsEnv hTs
  have hInnerSub :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.UOp op) x) xs ts bvs =
        __eo_mk_apply (Term.UOp op) xSub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.UOp op) x xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)
    simpa [xSub, hHeadSub] using hApplyEq
  have hSubstEq :
      __substitute_simul_rec (Term.Boolean isRename)
          (Term.Apply (Term.Apply (Term.UOp op) x) y) xs ts bvs =
        __eo_mk_apply (__eo_mk_apply (Term.UOp op) xSub) ySub := by
    have hApplyEq :=
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean isRename) (Term.Apply (Term.UOp op) x) y xs ts bvs
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
    instantiate_eo_mk_apply_ne_stuck_of_typeof_ne_stuck hTyMk
  have hInnerNe :
      __eo_mk_apply (Term.UOp op) xSub ≠ Term.Stuck :=
    instantiate_eo_mk_apply_fun_ne_stuck_of_ne_stuck hOuterNe
  have hInnerMk :
      __eo_mk_apply (Term.UOp op) xSub =
        Term.Apply (Term.UOp op) xSub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
      (Term.UOp op) xSub hInnerNe
  have hOuterMk :
      __eo_mk_apply (Term.Apply (Term.UOp op) xSub) ySub =
        Term.Apply (Term.Apply (Term.UOp op) xSub) ySub :=
    instantiate_eo_mk_apply_eq_apply_of_ne_stuck
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
  have hXSubBoth := hRecX hXTrans hXSubTy
  have hYSubBoth := hRecY hYTrans hYSubTy
  rw [hSubstEq, hInnerMk, hOuterMk]
  exact
    hBuild xSub ySub hXSubBoth.2 hYSubBoth.2
      hXSubBoth.1 hYSubBoth.1 hTyApply

end SubstitutePreservationSupport
