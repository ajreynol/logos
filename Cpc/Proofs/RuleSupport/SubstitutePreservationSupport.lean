import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport

open Eo
open SmtEval
open Smtm
open SubstituteTranslatabilitySupport

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2000

/-!
# Combined substitution preservation support

This module is a staging point for merging the two structural preservation
proofs for substitution mode (`isr = false`):

* EO type preservation of `__substitute_simul_rec`;
* SMT-translatability preservation of `__substitute_simul_rec`.

The instantiate-facing projection wrappers have been removed; callers now use
the combined theorem directly. Internally, the combined theorem still delegates
the remaining application/operator-spine fallback to the old recursive engines.
The next refactor step is to move those cases here, after which the duplicated
recursive engines can be deleted.
-/

namespace SubstitutePreservationSupport

private abbrev substResult (F xs ts bvs : Term) : Term :=
  __substitute_simul_rec (Term.Boolean false) F xs ts bvs

/-- Shared combined preservation proof for non-special atom heads whose SMT
translation is a generic application. -/
theorem substitute_simul_apply_atom_generic_preserves_type_and_translation_of_typeof_ne_stuck
    (F a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hEntryTypes : SubstituteSupport.SubstEntryPreservesTypes xs ts)
    (hNotApply : ∀ f x, F ≠ Term.Apply f x)
    (hNotVar : ∀ name T, F ≠ Term.Var name T)
    (hNotStuck : F ≠ Term.Stuck)
    (hNotBinder :
      ∀ q v vs,
        F ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
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
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
        Term.Stuck ->
      __eo_typeof (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) =
        __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs))
    (hTy :
      __eo_typeof
          (__substitute_simul_rec (Term.Boolean false)
            (Term.Apply F a) xs ts bvs) ≠
        Term.Stuck) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply F a) xs ts bvs) =
      __eo_typeof (Term.Apply F a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply F a) xs ts bvs) := by
  let aSub := __substitute_simul_rec (Term.Boolean false) a xs ts bvs
  have hGeneric :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt F) (__eo_to_smt a)) =
        __smtx_typeof_apply
          (__smtx_typeof (__eo_to_smt F))
          (__smtx_typeof (__eo_to_smt a)) :=
    generic_apply_type_of_non_special_head_closed
      (__eo_to_smt F) (__eo_to_smt a) hNoSel hNoTester
  have hArgs :=
    SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
      F a hTranslate hGeneric hTrans
  have hHeadTrans : RuleProofs.eo_has_smt_translation F := hArgs.1
  have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
  have hHeadNe :
      __substitute_simul_rec (Term.Boolean false) F xs ts bvs ≠
        Term.Stuck :=
    SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
      F a xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hTy
  have hHeadSubTrans :
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) F xs ts bvs) :=
    SubstituteSupport.substitute_simul_rec_atom_has_smt_translation_of_ne_stuck
      F xs ts bvs hXsEnv hBvsEnv hTs hNotApply hNotVar hNotStuck
      hHeadTrans hHeadNe
  have hATy : __eo_typeof aSub ≠ Term.Stuck := by
    simpa [aSub] using
      SubstituteSupport.substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
        F a xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hHeadSubTrans hTy
  have hABoth :
      __eo_typeof aSub = __eo_typeof a ∧
        RuleProofs.eo_has_smt_translation aSub :=
    hARec hATrans (by simpa [aSub] using hATy)
  refine ⟨?_, ?_⟩
  · exact
      SubstituteSupport.substitute_simul_rec_apply_atom_generic_typeof_eq_of_typeof_ne_stuck
        F a xs ts bvs hXsEnv hBvsEnv hTs hNotApply hNotVar hNotStuck
        hNotBinder hTranslate hNoSel hNoTester hTrans
        (fun _ _ => by simpa [aSub] using hABoth.1)
        hTy
  · exact
      SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
        F a xs ts bvs hXsEnv hBvsEnv hTs hNotBinder hHeadSubTrans
        (by simpa [aSub] using hABoth.2)
        hTy

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
        (__substitute_simul_rec (Term.Boolean false)
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
            (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
          Term.Stuck ->
        __eo_typeof
            (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) =
          __eo_typeof a ∧
          RuleProofs.eo_has_smt_translation
            (__substitute_simul_rec (Term.Boolean false) a xs ts bvs)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp op) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp op) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
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

/--
Size-recursive form of combined substitution preservation under an arbitrary
bound-variable accumulator.

`SubstActualsHaveSmtTypes` is the stronger, instantiate-facing side condition:
it implies the exact EO entry type facts consumed by the older type-preservation
theorem and also carries the SMT-translation/type facts consumed by the older
translatability theorem.
-/
theorem substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck_lt
    (n : Nat) (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hLt : sizeOf F < n)
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
      (hFTrans : RuleProofs.eo_has_smt_translation F)
      (hTs : EoListAllHaveSmtTranslation ts)
      (hActuals : SubstActualsHaveSmtTypes xs ts)
      (hTy : __eo_typeof (substResult F xs ts bvs) ≠ Term.Stuck) :
      __eo_typeof (substResult F xs ts bvs) = __eo_typeof F ∧
        RuleProofs.eo_has_smt_translation (substResult F xs ts bvs) := by
    cases n with
    | zero =>
        omega
    | succ n =>
      have hEntryTypes : SubstituteSupport.SubstEntryPreservesTypes xs ts :=
        SubstActualsHaveSmtTypes.entry_eo_type_eq hActuals
      let hRec :
          ∀ {G xs' ts' bvs' : Term} {xsVars' bvsVars' : List EoVarKey},
            sizeOf G < sizeOf F ->
            EoVarEnvPerm xs' xsVars' ->
            EoVarEnvPerm bvs' bvsVars' ->
            RuleProofs.eo_has_smt_translation G ->
            EoListAllHaveSmtTranslation ts' ->
            SubstActualsHaveSmtTypes xs' ts' ->
            __eo_typeof
                (__substitute_simul_rec (Term.Boolean false) G xs' ts' bvs') ≠
              Term.Stuck ->
            __eo_typeof
                (__substitute_simul_rec (Term.Boolean false) G xs' ts' bvs') =
              __eo_typeof G ∧
              RuleProofs.eo_has_smt_translation
                (__substitute_simul_rec (Term.Boolean false) G xs' ts' bvs') :=
        fun {G xs' ts' bvs'} {xsVars' bvsVars'} hGLt hXsEnv' hBvsEnv'
            hGTrans hTs' hActuals' hGTy =>
          substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck_lt
            n G xs' ts' bvs'
            (by omega) hXsEnv' hBvsEnv' hGTrans hTs' hActuals' hGTy
      by_cases hApply : ∃ f a, F = Term.Apply f a
      · rcases hApply with ⟨f, a, rfl⟩
        by_cases hBinder :
            ∃ q v vs,
              f =
                Term.Apply q
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        · rcases hBinder with ⟨q, v, vs, rfl⟩
          let binders := Term.Apply (Term.Apply Term.__eo_List_cons v) vs
          let bodySub :=
            __substitute_simul_rec (Term.Boolean false) a xs ts
              (__eo_list_concat Term.__eo_List_cons binders bvs)
          have hFTrans' :
              eoHasSmtTranslation (Term.Apply (Term.Apply q binders) a) := by
            simpa [RuleProofs.eo_has_smt_translation, eoHasSmtTranslation,
              binders] using hFTrans
          have hQ :
              q = Term.UOp UserOp.forall ∨ q = Term.UOp UserOp.exists :=
            is_closed_rec_list_branch_head_term_quantifier_of_has_smt_translation
              hFTrans'
          rcases eo_var_env_of_list_branch_has_smt_translation hFTrans' with
            ⟨binderVars, hBinderEnv⟩
          have hSubstEq :
              __substitute_simul_rec (Term.Boolean false)
                  (Term.Apply (Term.Apply q binders) a) xs ts bvs =
                __eo_mk_apply (Term.Apply q binders) bodySub := by
            simpa [binders, bodySub] using
              substitute_simul_quant_eq_of_typeof_ne_stuck
                q v vs a xs ts bvs hXsEnv hBvsEnv hTs hTy
          have hTyMk :
              __eo_typeof (__eo_mk_apply (Term.Apply q binders) bodySub) ≠
                Term.Stuck := by
            have hTyRaw :
                __eo_typeof
                    (__substitute_simul_rec (Term.Boolean false)
                      (Term.Apply (Term.Apply q binders) a) xs ts bvs) ≠
                  Term.Stuck := by
              simpa [substResult, binders] using hTy
            rwa [hSubstEq] at hTyRaw
          have hMk :
              __eo_mk_apply (Term.Apply q binders) bodySub =
                Term.Apply (Term.Apply q binders) bodySub :=
            eo_mk_apply_apply_head_eq_apply_of_typeof_ne_stuck
              q binders bodySub hTyMk
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
              __eo_typeof bodySub = __eo_typeof a := by
            simpa [bodySub] using
              (hRec
                (G := a) (xs' := xs) (ts' := ts)
                (bvs' := __eo_list_concat Term.__eo_List_cons binders bvs)
                (by
                  simp
                  omega)
                hXsEnv hBvsEnv' hBodyTrans hTs hActuals
                (by simpa [bodySub] using hBodyTy)).1
          have hBodySubTrans :
              RuleProofs.eo_has_smt_translation bodySub := by
            simpa [bodySub] using
              (hRec
                (G := a) (xs' := xs) (ts' := ts)
                (bvs' := __eo_list_concat Term.__eo_List_cons binders bvs)
                (by
                  simp
                  omega)
                hXsEnv hBvsEnv' hBodyTrans hTs hActuals
                (by simpa [bodySub] using hBodyTy)).2
          refine ⟨?_, ?_⟩
          · simpa [binders, bodySub] using
              SubstituteSupport.substitute_simul_quant_typeof_eq_of_typeof_ne_stuck
                q v vs a xs ts bvs hXsEnv hBvsEnv hTs
                hFTrans hBodyType hTy
          · simpa [binders, bodySub] using
              substitute_simul_quant_has_smt_translation_of_typeof_ne_stuck
                q v vs a xs ts bvs hXsEnv hBvsEnv hTs
                hFTrans hBodySubTrans hTy
        · by_cases hHeadVar : ∃ name T, f = Term.Var name T
          · rcases hHeadVar with ⟨name, T, rfl⟩
            let aSub :=
              __substitute_simul_rec (Term.Boolean false) a xs ts bvs
            have hNotBinder :
                ∀ q v vs,
                  Term.Var name T ≠
                    Term.Apply q
                      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
              intro q v vs hEq
              cases hEq
            have hArgs :=
              SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                (Term.Var name T) a
                (by rfl)
                (SubstituteSupport.var_apply_generic_smt_type name T a)
                hFTrans
            have hHeadTrans :
                RuleProofs.eo_has_smt_translation (Term.Var name T) :=
              hArgs.1
            have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
            have hHeadNe :
                __substitute_simul_rec (Term.Boolean false)
                    (Term.Var name T) xs ts bvs ≠
                  Term.Stuck :=
              SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
                (Term.Var name T) a xs ts bvs hXsEnv hBvsEnv hTs
                hNotBinder hTy
            have hHeadSubTrans :
                RuleProofs.eo_has_smt_translation
                  (__substitute_simul_rec (Term.Boolean false)
                    (Term.Var name T) xs ts bvs) :=
              SubstituteSupport.substitute_simul_rec_var_any_has_smt_translation_of_ne_stuck
                name T xs ts bvs hXsEnv hBvsEnv hTs hHeadTrans hHeadNe
            have hATy : __eo_typeof aSub ≠ Term.Stuck := by
              simpa [aSub] using
                SubstituteSupport.substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
                  (Term.Var name T) a xs ts bvs hXsEnv hBvsEnv hTs
                  hNotBinder hHeadSubTrans hTy
            have hABoth :
                __eo_typeof aSub = __eo_typeof a ∧
                  RuleProofs.eo_has_smt_translation aSub := by
              simpa [aSub] using
                hRec
                  (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                  (by
                    simp
                    omega)
                  hXsEnv hBvsEnv hATrans hTs hActuals
                  (by simpa [aSub] using hATy)
            refine ⟨?_, ?_⟩
            · exact
                SubstituteSupport.substitute_simul_rec_apply_var_typeof_eq_of_typeof_ne_stuck
                  name T a xs ts bvs
                  hXsEnv hBvsEnv hTs hEntryTypes hNotBinder
                  (by rfl)
                  (SubstituteSupport.var_apply_generic_smt_type name T a)
                  hFTrans
                  (fun _ _ => by simpa [aSub] using hABoth.1)
                  hTy
            · exact
                SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
                  (Term.Var name T) a xs ts bvs hXsEnv hBvsEnv hTs
                  hNotBinder hHeadSubTrans
                  (by simpa [aSub] using hABoth.2)
                  hTy
          · by_cases hHeadUConst : ∃ i U, f = Term.UConst i U
            · rcases hHeadUConst with ⟨i, U, rfl⟩
              let aSub :=
                __substitute_simul_rec (Term.Boolean false) a xs ts bvs
              have hNotBinder :
                  ∀ q v vs,
                    Term.UConst i U ≠
                      Term.Apply q
                        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
                intro q v vs hEq
                cases hEq
              have hTranslate :
                  __eo_to_smt (Term.Apply (Term.UConst i U) a) =
                    SmtTerm.Apply (__eo_to_smt (Term.UConst i U))
                      (__eo_to_smt a) := by
                rfl
              have hGeneric :
                  __smtx_typeof
                      (SmtTerm.Apply (__eo_to_smt (Term.UConst i U))
                        (__eo_to_smt a)) =
                    __smtx_typeof_apply
                      (__smtx_typeof (__eo_to_smt (Term.UConst i U)))
                      (__smtx_typeof (__eo_to_smt a)) := by
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
                      (__smtx_typeof (__eo_to_smt a))
                rw [__smtx_typeof.eq_def]
              have hArgs :=
                SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                  (Term.UConst i U) a hTranslate hGeneric hFTrans
              have hHeadTrans :
                  RuleProofs.eo_has_smt_translation (Term.UConst i U) :=
                hArgs.1
              have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
              have hHeadNe :
                  __substitute_simul_rec (Term.Boolean false)
                      (Term.UConst i U) xs ts bvs ≠
                    Term.Stuck :=
                SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
                  (Term.UConst i U) a xs ts bvs hXsEnv hBvsEnv hTs
                  hNotBinder hTy
              have hHeadSubTrans :
                  RuleProofs.eo_has_smt_translation
                    (__substitute_simul_rec (Term.Boolean false)
                      (Term.UConst i U) xs ts bvs) :=
                SubstituteSupport.substitute_simul_rec_atom_has_smt_translation_of_ne_stuck
                  (Term.UConst i U) xs ts bvs hXsEnv hBvsEnv hTs
                  (by intro f x h; cases h)
                  (by intro name T h; cases h)
                  (by intro h; cases h)
                  hHeadTrans hHeadNe
              have hATy : __eo_typeof aSub ≠ Term.Stuck := by
                simpa [aSub] using
                  SubstituteSupport.substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
                    (Term.UConst i U) a xs ts bvs hXsEnv hBvsEnv hTs
                    hNotBinder hHeadSubTrans hTy
              have hABoth :
                  __eo_typeof aSub = __eo_typeof a ∧
                    RuleProofs.eo_has_smt_translation aSub := by
                simpa [aSub] using
                  hRec
                    (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                    (by
                      simp
                      omega)
                    hXsEnv hBvsEnv hATrans hTs hActuals
                    (by simpa [aSub] using hATy)
              refine ⟨?_, ?_⟩
              · exact
                  SubstituteSupport.substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
                    (Term.UConst i U) a xs ts bvs
                    hXsEnv hBvsEnv hTs
                    (by intro f x h; cases h)
                    (by intro name T h; cases h)
                    (by intro h; cases h)
                    hNotBinder hTranslate hGeneric hFTrans
                    (fun _ _ => by simpa [aSub] using hABoth.1)
                    hTy
              · exact
                  SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
                    (Term.UConst i U) a xs ts bvs hXsEnv hBvsEnv hTs
                    hNotBinder hHeadSubTrans
                    (by simpa [aSub] using hABoth.2)
                    hTy
            · by_cases hHeadDtCons : ∃ s d i, f = Term.DtCons s d i
              · rcases hHeadDtCons with ⟨s, d, i, rfl⟩
                let aSub :=
                  __substitute_simul_rec (Term.Boolean false) a xs ts bvs
                have hNotBinder :
                    ∀ q v vs,
                      Term.DtCons s d i ≠
                        Term.Apply q
                          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) := by
                  intro q v vs hEq
                  cases hEq
                have hTranslate :
                    __eo_to_smt (Term.Apply (Term.DtCons s d i) a) =
                      SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i))
                        (__eo_to_smt a) := by
                  rfl
                have hGeneric :
                    __smtx_typeof
                        (SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i))
                          (__eo_to_smt a)) =
                      __smtx_typeof_apply
                        (__smtx_typeof (__eo_to_smt (Term.DtCons s d i)))
                        (__smtx_typeof (__eo_to_smt a)) := by
                  have hReserved :
                      native_reserved_datatype_name s = false :=
                    SubstituteSupport.dtcons_reserved_false_of_apply_has_smt_translation
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
                        (__smtx_typeof (__eo_to_smt a))
                  rw [hReserved]
                  simp [native_ite]
                  rw [__smtx_typeof.eq_def]
                have hArgs :=
                  SubstituteSupport.apply_generic_args_have_smt_translation_of_has_smt_translation
                    (Term.DtCons s d i) a hTranslate hGeneric hFTrans
                have hHeadTrans :
                    RuleProofs.eo_has_smt_translation (Term.DtCons s d i) :=
                  hArgs.1
                have hATrans : RuleProofs.eo_has_smt_translation a := hArgs.2
                have hHeadNe :
                    __substitute_simul_rec (Term.Boolean false)
                        (Term.DtCons s d i) xs ts bvs ≠
                      Term.Stuck :=
                  SubstituteSupport.substitute_simul_rec_apply_head_ne_stuck_of_typeof_ne_stuck
                    (Term.DtCons s d i) a xs ts bvs hXsEnv hBvsEnv hTs
                    hNotBinder hTy
                have hHeadSubTrans :
                    RuleProofs.eo_has_smt_translation
                      (__substitute_simul_rec (Term.Boolean false)
                        (Term.DtCons s d i) xs ts bvs) :=
                  SubstituteSupport.substitute_simul_rec_atom_has_smt_translation_of_ne_stuck
                    (Term.DtCons s d i) xs ts bvs hXsEnv hBvsEnv hTs
                    (by intro f x h; cases h)
                    (by intro name T h; cases h)
                    (by intro h; cases h)
                    hHeadTrans hHeadNe
                have hATy : __eo_typeof aSub ≠ Term.Stuck := by
                  simpa [aSub] using
                    SubstituteSupport.substitute_simul_rec_apply_arg_typeof_ne_stuck_of_typeof_ne_stuck
                      (Term.DtCons s d i) a xs ts bvs hXsEnv hBvsEnv hTs
                      hNotBinder hHeadSubTrans hTy
                have hABoth :
                    __eo_typeof aSub = __eo_typeof a ∧
                      RuleProofs.eo_has_smt_translation aSub := by
                  simpa [aSub] using
                    hRec
                      (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                      (by
                        simp
                        omega)
                      hXsEnv hBvsEnv hATrans hTs hActuals
                      (by simpa [aSub] using hATy)
                refine ⟨?_, ?_⟩
                · exact
                    SubstituteSupport.substitute_simul_rec_apply_atom_typeof_eq_of_typeof_ne_stuck
                      (Term.DtCons s d i) a xs ts bvs
                      hXsEnv hBvsEnv hTs
                      (by intro f x h; cases h)
                      (by intro name T h; cases h)
                      (by intro h; cases h)
                      hNotBinder hTranslate hGeneric hFTrans
                      (fun _ _ => by simpa [aSub] using hABoth.1)
                      hTy
                · exact
                    SubstituteTranslatabilitySupport.substitute_simul_apply_has_smt_translation_of_typeof_ne_stuck
                      (Term.DtCons s d i) a xs ts bvs hXsEnv hBvsEnv hTs
                      hNotBinder hHeadSubTrans
                      (by simpa [aSub] using hABoth.2)
                      hTy
              · have hOld :
                    __eo_typeof
                        (__substitute_simul_rec (Term.Boolean false)
                          (Term.Apply f a) xs ts bvs) =
                      __eo_typeof (Term.Apply f a) ∧
                      RuleProofs.eo_has_smt_translation
                        (__substitute_simul_rec (Term.Boolean false)
                          (Term.Apply f a) xs ts bvs) := by
                  refine ⟨?_, ?_⟩
                  · exact
                      SubstituteSupport.substitute_simul_rec_typeof_eq_of_typeof_ne_stuck_lt
                        (Nat.succ n) (Term.Apply f a) xs ts bvs
                        hLt hXsEnv hBvsEnv hFTrans hTs hEntryTypes hTy
                  · exact
                      SubstituteTranslatabilitySupport.substitute_simul_has_smt_translation_of_typeof_ne_stuck_lt
                        (Nat.succ n) (Term.Apply f a) xs ts bvs
                        hLt hXsEnv hBvsEnv hFTrans hTs hActuals hTy
                by_cases hHeadApply : ∃ g x, f = Term.Apply g x
                · exact hOld
                · by_cases hHeadSpecial :
                    (∃ op, f = Term.UOp op) ∨
                      (∃ op x, f = Term.UOp1 op x) ∨
                      (∃ op x y, f = Term.UOp2 op x y) ∨
                      (∃ op w x y, f = Term.UOp3 op w x y) ∨
                      (∃ s d i j, f = Term.DtSel s d i j) ∨
                      f = Term.Stuck
                  · by_cases hHeadNot : f = Term.UOp UserOp.not
                    · subst f
                      refine ⟨?_, ?_⟩
                      · exact
                          SubstituteSupport.substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                            UserOp.not a xs ts bvs hXsEnv hBvsEnv hTs
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
                              (hRec
                                (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                (by simp)
                                hXsEnv hBvsEnv hATrans hTs hActuals hATy).1)
                            hTy
                      · exact
                          SubstituteTranslatabilitySupport.substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                            UserOp.not a xs ts bvs hXsEnv hBvsEnv hTs
                            (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                            hFTrans hTy
                            (fun h =>
                              not_arg_has_smt_translation_of_has_smt_translation h)
                            (fun X hApp => by
                              change __eo_typeof_not (__eo_typeof X) ≠
                                Term.Stuck at hApp
                              intro hX
                              rw [hX] at hApp
                              exact hApp rfl)
                            (fun X hXTrans hApp => by
                              have hXBool : __eo_typeof X = Term.Bool := by
                                change __eo_typeof_not (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                cases hXTy : __eo_typeof X <;>
                                  simp [__eo_typeof_not, hXTy] at hApp ⊢
                              have hXBoolType : RuleProofs.eo_has_bool_type X :=
                                RuleProofs.eo_typeof_bool_implies_has_bool_type
                                  X hXTrans hXBool
                              exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                (Term.Apply (Term.UOp UserOp.not) X)
                                (RuleProofs.eo_has_bool_type_not_of_bool_arg
                                  X hXBoolType))
                            (fun hATrans hATy =>
                              (hRec
                                (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                (by simp)
                                hXsEnv hBvsEnv hATrans hTs hActuals hATy).2)
                    · by_cases hHeadAbs : f = Term.UOp UserOp.abs
                      · subst f
                        refine ⟨?_, ?_⟩
                        · exact
                            SubstituteSupport.substitute_simul_unary_op_typeof_eq_of_typeof_ne_stuck
                              UserOp.abs a xs ts bvs hXsEnv hBvsEnv hTs
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
                                (hRec
                                  (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                  (by simp)
                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy).1)
                              hTy
                        · exact
                            SubstituteTranslatabilitySupport.substitute_simul_unary_op_has_smt_translation_of_typeof_ne_stuck
                              UserOp.abs a xs ts bvs hXsEnv hBvsEnv hTs
                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                              hFTrans hTy
                              (fun h =>
                                abs_arg_has_smt_translation_of_has_smt_translation h)
                              (fun X hApp => by
                                change __eo_typeof_abs (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with
                                  hArg | hArg
                                · rw [hArg]
                                  intro h
                                  cases h
                                · rw [hArg]
                                  intro h
                                  cases h)
                              (fun X hXTrans hApp => by
                                have hXMatch :
                                    __smtx_typeof (__eo_to_smt X) =
                                      __eo_to_smt_type (__eo_typeof X) :=
                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                    X hXTrans
                                unfold RuleProofs.eo_has_smt_translation
                                change
                                  __smtx_typeof (SmtTerm.abs (__eo_to_smt X)) ≠
                                    SmtType.None
                                rw [typeof_abs_eq]
                                change __eo_typeof_abs (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with
                                  hArgInt | hArgReal
                                · have hSmtArg :
                                      __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                    rw [hXMatch, hArgInt]
                                    rfl
                                  simp [__smtx_typeof_arith_overload_op_1,
                                    hSmtArg]
                                · have hSmtArg :
                                      __smtx_typeof (__eo_to_smt X) = SmtType.Real := by
                                    rw [hXMatch, hArgReal]
                                    rfl
                                  simp [__smtx_typeof_arith_overload_op_1,
                                    hSmtArg])
                              (fun hATrans hATy =>
                                (hRec
                                  (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                  (by simp)
                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy).2)
                      · by_cases hHeadToReal : f = Term.UOp UserOp.to_real
                        · subst f
                          exact
                            substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                              UserOp.to_real a xs ts bvs hXsEnv hBvsEnv hTs
                              (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                              hFTrans hTy
                              (fun h =>
                                to_real_arg_has_smt_translation_of_has_smt_translation h)
                              (fun X hApp => by
                                change __eo_typeof_to_real (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                rcases eo_typeof_to_real_arg_arith_of_ne_stuck hApp with
                                  hArg | hArg
                                · rw [hArg]
                                  intro h
                                  cases h
                                · rw [hArg]
                                  intro h
                                  cases h)
                              (fun X Y hXY => by
                                change __eo_typeof_to_real (__eo_typeof X) =
                                  __eo_typeof_to_real (__eo_typeof Y)
                                rw [hXY])
                              (fun X hXTrans hApp => by
                                have hXMatch :
                                    __smtx_typeof (__eo_to_smt X) =
                                      __eo_to_smt_type (__eo_typeof X) :=
                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                    X hXTrans
                                unfold RuleProofs.eo_has_smt_translation
                                change
                                  __smtx_typeof (SmtTerm.to_real (__eo_to_smt X)) ≠
                                    SmtType.None
                                rw [typeof_to_real_eq]
                                change __eo_typeof_to_real (__eo_typeof X) ≠
                                  Term.Stuck at hApp
                                rcases eo_typeof_to_real_arg_arith_of_ne_stuck hApp with
                                  hArgInt | hArgReal
                                · have hSmtArg :
                                      __smtx_typeof (__eo_to_smt X) = SmtType.Int := by
                                    rw [hXMatch, hArgInt]
                                    rfl
                                  simp [hSmtArg, native_ite, native_Teq]
                                · have hSmtArg :
                                      __smtx_typeof (__eo_to_smt X) = SmtType.Real := by
                                    rw [hXMatch, hArgReal]
                                    rfl
                                  simp [hSmtArg, native_ite, native_Teq])
                              (fun hATrans hATy =>
                                hRec
                                  (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                  (by simp)
                                  hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                        · by_cases hHeadToInt : f = Term.UOp UserOp.to_int
                          · subst f
                            exact
                              substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                UserOp.to_int a xs ts bvs hXsEnv hBvsEnv hTs
                                (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                hFTrans hTy
                                (fun h =>
                                  to_int_arg_has_smt_translation_of_has_smt_translation h)
                                (fun X hApp => by
                                  change __eo_typeof_to_int (__eo_typeof X) ≠
                                    Term.Stuck at hApp
                                  have hArgReal :
                                      __eo_typeof X = Term.UOp UserOp.Real :=
                                    eo_typeof_to_int_arg_real_of_ne_stuck hApp
                                  rw [hArgReal]
                                  intro h
                                  cases h)
                                (fun X Y hXY => by
                                  change __eo_typeof_to_int (__eo_typeof X) =
                                    __eo_typeof_to_int (__eo_typeof Y)
                                  rw [hXY])
                                (fun X hXTrans hApp => by
                                  have hXMatch :
                                      __smtx_typeof (__eo_to_smt X) =
                                        __eo_to_smt_type (__eo_typeof X) :=
                                    TranslationProofs.eo_to_smt_typeof_matches_translation
                                      X hXTrans
                                  unfold RuleProofs.eo_has_smt_translation
                                  change
                                    __smtx_typeof (SmtTerm.to_int (__eo_to_smt X)) ≠
                                      SmtType.None
                                  rw [typeof_to_int_eq]
                                  have hArgReal :
                                      __eo_typeof X = Term.UOp UserOp.Real := by
                                    apply eo_typeof_to_int_arg_real_of_ne_stuck
                                    change __eo_typeof_to_int (__eo_typeof X) ≠
                                      Term.Stuck at hApp
                                    exact hApp
                                  have hSmtArg :
                                      __smtx_typeof (__eo_to_smt X) = SmtType.Real := by
                                    rw [hXMatch, hArgReal]
                                    rfl
                                  simp [hSmtArg, native_ite, native_Teq])
                                (fun hATrans hATy =>
                                  hRec
                                    (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                    (by simp)
                                    hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                          · by_cases hHeadIsInt : f = Term.UOp UserOp.is_int
                            · subst f
                              exact
                                substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                  UserOp.is_int a xs ts bvs hXsEnv hBvsEnv hTs
                                  (fun q v vs hEq => hBinder ⟨q, v, vs, hEq⟩)
                                  hFTrans hTy
                                  (fun h =>
                                    is_int_arg_has_smt_translation_of_has_smt_translation h)
                                  (fun X hApp => by
                                    change __eo_typeof_is_int (__eo_typeof X) ≠
                                      Term.Stuck at hApp
                                    have hArgReal :
                                        __eo_typeof X = Term.UOp UserOp.Real :=
                                      eo_typeof_is_int_arg_real_of_ne_stuck hApp
                                    rw [hArgReal]
                                    intro h
                                    cases h)
                                  (fun X Y hXY => by
                                    change __eo_typeof_is_int (__eo_typeof X) =
                                      __eo_typeof_is_int (__eo_typeof Y)
                                    rw [hXY])
                                  (fun X hXTrans hApp => by
                                    have hXMatch :
                                        __smtx_typeof (__eo_to_smt X) =
                                          __eo_to_smt_type (__eo_typeof X) :=
                                      TranslationProofs.eo_to_smt_typeof_matches_translation
                                        X hXTrans
                                    unfold RuleProofs.eo_has_smt_translation
                                    change
                                      __smtx_typeof (SmtTerm.is_int (__eo_to_smt X)) ≠
                                        SmtType.None
                                    rw [typeof_is_int_eq]
                                    have hArgReal :
                                        __eo_typeof X = Term.UOp UserOp.Real := by
                                      apply eo_typeof_is_int_arg_real_of_ne_stuck
                                      change __eo_typeof_is_int (__eo_typeof X) ≠
                                        Term.Stuck at hApp
                                      exact hApp
                                    have hSmtArg :
                                        __smtx_typeof (__eo_to_smt X) = SmtType.Real := by
                                      rw [hXMatch, hArgReal]
                                      rfl
                                    simp [hSmtArg, native_ite, native_Teq])
                                  (fun hATrans hATy =>
                                    hRec
                                      (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                                      (by simp)
                                      hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                            · by_cases hHeadUneg :
                                f = Term.UOp UserOp.__eoo_neg_2
                              · subst f
                                exact
                                  substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                    UserOp.__eoo_neg_2 a xs ts bvs
                                    hXsEnv hBvsEnv hTs
                                    (fun q v vs hEq =>
                                      hBinder ⟨q, v, vs, hEq⟩)
                                    hFTrans hTy
                                    (fun h =>
                                      uneg_arg_has_smt_translation_of_has_smt_translation h)
                                    (fun X hApp => by
                                      change __eo_typeof_abs (__eo_typeof X) ≠
                                        Term.Stuck at hApp
                                      rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with
                                        hArg | hArg
                                      · rw [hArg]
                                        intro h
                                        cases h
                                      · rw [hArg]
                                        intro h
                                        cases h)
                                    (fun X Y hXY => by
                                      change __eo_typeof_abs (__eo_typeof X) =
                                        __eo_typeof_abs (__eo_typeof Y)
                                      rw [hXY])
                                    (fun X hXTrans hApp => by
                                      have hXMatch :
                                          __smtx_typeof (__eo_to_smt X) =
                                            __eo_to_smt_type (__eo_typeof X) :=
                                        TranslationProofs.eo_to_smt_typeof_matches_translation
                                          X hXTrans
                                      unfold RuleProofs.eo_has_smt_translation
                                      change
                                        __smtx_typeof
                                            (SmtTerm.uneg (__eo_to_smt X)) ≠
                                          SmtType.None
                                      rw [typeof_uneg_eq]
                                      change __eo_typeof_abs (__eo_typeof X) ≠
                                        Term.Stuck at hApp
                                      rcases eo_typeof_abs_arg_arith_of_ne_stuck hApp with
                                        hArgInt | hArgReal
                                      · have hSmtArg :
                                            __smtx_typeof (__eo_to_smt X) =
                                              SmtType.Int := by
                                          rw [hXMatch, hArgInt]
                                          rfl
                                        simp [__smtx_typeof_arith_overload_op_1,
                                          hSmtArg]
                                      · have hSmtArg :
                                            __smtx_typeof (__eo_to_smt X) =
                                              SmtType.Real := by
                                          rw [hXMatch, hArgReal]
                                          rfl
                                        simp [__smtx_typeof_arith_overload_op_1,
                                          hSmtArg])
                                    (fun hATrans hATy =>
                                      hRec
                                        (G := a) (xs' := xs) (ts' := ts)
                                        (bvs' := bvs)
                                        (by simp)
                                        hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                              · by_cases hHeadPow2 :
                                  f = Term.UOp UserOp.int_pow2
                                · subst f
                                  exact
                                    substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                      UserOp.int_pow2 a xs ts bvs
                                      hXsEnv hBvsEnv hTs
                                      (fun q v vs hEq =>
                                        hBinder ⟨q, v, vs, hEq⟩)
                                      hFTrans hTy
                                      (fun h =>
                                        int_pow2_arg_has_smt_translation_of_has_smt_translation h)
                                      (fun X hApp => by
                                        change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                          Term.Stuck at hApp
                                        rw [eo_typeof_int_pow2_arg_int_of_ne_stuck hApp]
                                        intro h
                                        cases h)
                                      (fun X Y hXY => by
                                        change __eo_typeof_int_pow2 (__eo_typeof X) =
                                          __eo_typeof_int_pow2 (__eo_typeof Y)
                                        rw [hXY])
                                      (fun X hXTrans hApp => by
                                        have hXMatch :
                                            __smtx_typeof (__eo_to_smt X) =
                                              __eo_to_smt_type (__eo_typeof X) :=
                                          TranslationProofs.eo_to_smt_typeof_matches_translation
                                            X hXTrans
                                        unfold RuleProofs.eo_has_smt_translation
                                        change
                                          __smtx_typeof
                                              (SmtTerm.int_pow2 (__eo_to_smt X)) ≠
                                            SmtType.None
                                        rw [typeof_int_pow2_eq]
                                        change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                          Term.Stuck at hApp
                                        have hArgInt :=
                                          eo_typeof_int_pow2_arg_int_of_ne_stuck hApp
                                        have hSmtArg :
                                            __smtx_typeof (__eo_to_smt X) =
                                              SmtType.Int := by
                                          rw [hXMatch, hArgInt]
                                          rfl
                                        simp [hSmtArg, native_ite, native_Teq])
                                      (fun hATrans hATy =>
                                        hRec
                                          (G := a) (xs' := xs) (ts' := ts)
                                          (bvs' := bvs)
                                          (by simp)
                                          hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                                · by_cases hHeadLog2 :
                                    f = Term.UOp UserOp.int_log2
                                  · subst f
                                    exact
                                      substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                        UserOp.int_log2 a xs ts bvs
                                        hXsEnv hBvsEnv hTs
                                        (fun q v vs hEq =>
                                          hBinder ⟨q, v, vs, hEq⟩)
                                        hFTrans hTy
                                        (fun h =>
                                          int_log2_arg_has_smt_translation_of_has_smt_translation h)
                                        (fun X hApp => by
                                          change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                            Term.Stuck at hApp
                                          rw [eo_typeof_int_pow2_arg_int_of_ne_stuck hApp]
                                          intro h
                                          cases h)
                                        (fun X Y hXY => by
                                          change __eo_typeof_int_pow2 (__eo_typeof X) =
                                            __eo_typeof_int_pow2 (__eo_typeof Y)
                                          rw [hXY])
                                        (fun X hXTrans hApp => by
                                          have hXMatch :
                                              __smtx_typeof (__eo_to_smt X) =
                                                __eo_to_smt_type (__eo_typeof X) :=
                                            TranslationProofs.eo_to_smt_typeof_matches_translation
                                              X hXTrans
                                          unfold RuleProofs.eo_has_smt_translation
                                          change
                                            __smtx_typeof
                                                (SmtTerm.int_log2 (__eo_to_smt X)) ≠
                                              SmtType.None
                                          rw [typeof_int_log2_eq]
                                          change __eo_typeof_int_pow2 (__eo_typeof X) ≠
                                            Term.Stuck at hApp
                                          have hArgInt :=
                                            eo_typeof_int_pow2_arg_int_of_ne_stuck hApp
                                          have hSmtArg :
                                              __smtx_typeof (__eo_to_smt X) =
                                                SmtType.Int := by
                                            rw [hXMatch, hArgInt]
                                            rfl
                                          simp [hSmtArg, native_ite, native_Teq])
                                        (fun hATrans hATy =>
                                          hRec
                                            (G := a) (xs' := xs) (ts' := ts)
                                            (bvs' := bvs)
                                            (by simp)
                                            hXsEnv hBvsEnv hATrans hTs hActuals
                                            hATy)
                                  · by_cases hHeadPurify :
                                      f = Term.UOp UserOp._at_purify
                                    · subst f
                                      exact
                                        substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                          UserOp._at_purify a xs ts bvs
                                          hXsEnv hBvsEnv hTs
                                          (fun q v vs hEq =>
                                            hBinder ⟨q, v, vs, hEq⟩)
                                          hFTrans hTy
                                          (fun h =>
                                            purify_arg_has_smt_translation_of_has_smt_translation h)
                                          (fun X hApp => by
                                            change
                                              __eo_typeof__at_purify
                                                  (__eo_typeof X) ≠
                                                Term.Stuck at hApp
                                            simpa [eo_typeof_purify_eq] using hApp)
                                          (fun X Y hXY => by
                                            change
                                              __eo_typeof__at_purify
                                                  (__eo_typeof X) =
                                                __eo_typeof__at_purify
                                                  (__eo_typeof Y)
                                            rw [hXY])
                                          (fun X hXTrans hApp => by
                                            unfold RuleProofs.eo_has_smt_translation
                                            change
                                              __smtx_typeof
                                                  (SmtTerm._at_purify
                                                    (__eo_to_smt X)) ≠
                                                SmtType.None
                                            rw [__smtx_typeof.eq_11]
                                            simpa [RuleProofs.eo_has_smt_translation]
                                              using hXTrans)
                                          (fun hATrans hATy =>
                                            hRec
                                              (G := a) (xs' := xs) (ts' := ts)
                                              (bvs' := bvs)
                                              (by simp)
                                              hXsEnv hBvsEnv hATrans hTs
                                              hActuals hATy)
                                    · by_cases hHeadIntIspow2 :
                                        f = Term.UOp UserOp.int_ispow2
                                      · subst f
                                        exact
                                          substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                            UserOp.int_ispow2 a xs ts bvs
                                            hXsEnv hBvsEnv hTs
                                            (fun q v vs hEq =>
                                              hBinder ⟨q, v, vs, hEq⟩)
                                            hFTrans hTy
                                            (fun h =>
                                              int_ispow2_arg_has_smt_translation_of_has_smt_translation h)
                                            (fun X hApp => by
                                              change
                                                __eo_typeof_int_ispow2
                                                    (__eo_typeof X) ≠
                                                  Term.Stuck at hApp
                                              rw [
                                                eo_typeof_int_ispow2_arg_int_of_ne_stuck
                                                  hApp]
                                              intro h
                                              cases h)
                                            (fun X Y hXY => by
                                              change
                                                __eo_typeof_int_ispow2
                                                    (__eo_typeof X) =
                                                  __eo_typeof_int_ispow2
                                                    (__eo_typeof Y)
                                              rw [hXY])
                                            (fun X hXTrans hApp => by
                                              have hXMatch :
                                                  __smtx_typeof (__eo_to_smt X) =
                                                    __eo_to_smt_type
                                                      (__eo_typeof X) :=
                                                TranslationProofs.eo_to_smt_typeof_matches_translation
                                                  X hXTrans
                                              unfold RuleProofs.eo_has_smt_translation
                                              change
                                                __smtx_typeof
                                                    (SmtTerm.and
                                                      (SmtTerm.geq (__eo_to_smt X)
                                                        (SmtTerm.Numeral 0))
                                                      (SmtTerm.eq (__eo_to_smt X)
                                                        (SmtTerm.int_pow2
                                                          (SmtTerm.int_log2
                                                            (__eo_to_smt X))))) ≠
                                                  SmtType.None
                                              change
                                                __eo_typeof_int_ispow2
                                                    (__eo_typeof X) ≠
                                                  Term.Stuck at hApp
                                              have hArgInt :=
                                                eo_typeof_int_ispow2_arg_int_of_ne_stuck
                                                  hApp
                                              have hSmtArg :
                                                  __smtx_typeof (__eo_to_smt X) =
                                                    SmtType.Int := by
                                                rw [hXMatch, hArgInt]
                                                rfl
                                              rw [typeof_and_eq, typeof_geq_eq,
                                                typeof_eq_eq, typeof_int_pow2_eq,
                                                typeof_int_log2_eq, hSmtArg,
                                                __smtx_typeof.eq_2]
                                              simp [
                                                __smtx_typeof_arith_overload_op_2_ret,
                                                __smtx_typeof_eq,
                                                __smtx_typeof_guard,
                                                native_ite, native_Teq])
                                            (fun hATrans hATy =>
                                              hRec
                                                (G := a) (xs' := xs)
                                                (ts' := ts) (bvs' := bvs)
                                                (by simp)
                                                hXsEnv hBvsEnv hATrans hTs
                                                hActuals hATy)
                                      · by_cases hHeadIntDivByZero :
                                          f =
                                            Term.UOp UserOp._at_int_div_by_zero
                                        · subst f
                                          exact
                                            substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                              UserOp._at_int_div_by_zero
                                              a xs ts bvs hXsEnv hBvsEnv hTs
                                              (fun q v vs hEq =>
                                                hBinder ⟨q, v, vs, hEq⟩)
                                              hFTrans hTy
                                              (fun h =>
                                                int_div_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                              (fun X hApp => by
                                                change
                                                  __eo_typeof_int_pow2
                                                      (__eo_typeof X) ≠
                                                    Term.Stuck at hApp
                                                rw [
                                                  eo_typeof_int_pow2_arg_int_of_ne_stuck
                                                    hApp]
                                                intro h
                                                cases h)
                                              (fun X Y hXY => by
                                                change
                                                  __eo_typeof_int_pow2
                                                      (__eo_typeof X) =
                                                    __eo_typeof_int_pow2
                                                      (__eo_typeof Y)
                                                rw [hXY])
                                              (fun X hXTrans hApp => by
                                                have hXMatch :
                                                    __smtx_typeof (__eo_to_smt X) =
                                                      __eo_to_smt_type
                                                        (__eo_typeof X) :=
                                                  TranslationProofs.eo_to_smt_typeof_matches_translation
                                                    X hXTrans
                                                unfold RuleProofs.eo_has_smt_translation
                                                change
                                                  __smtx_typeof
                                                      (SmtTerm.div (__eo_to_smt X)
                                                        (SmtTerm.Numeral 0)) ≠
                                                    SmtType.None
                                                rw [typeof_div_eq]
                                                change
                                                  __eo_typeof_int_pow2
                                                      (__eo_typeof X) ≠
                                                    Term.Stuck at hApp
                                                have hArgInt :=
                                                  eo_typeof_int_pow2_arg_int_of_ne_stuck
                                                    hApp
                                                have hSmtArg :
                                                    __smtx_typeof (__eo_to_smt X) =
                                                      SmtType.Int := by
                                                  rw [hXMatch, hArgInt]
                                                  rfl
                                                simp [hSmtArg, __smtx_typeof.eq_2,
                                                  native_ite, native_Teq])
                                              (fun hATrans hATy =>
                                                hRec
                                                  (G := a) (xs' := xs)
                                                  (ts' := ts) (bvs' := bvs)
                                                  (by simp)
                                                  hXsEnv hBvsEnv hATrans hTs
                                                  hActuals hATy)
                                        · by_cases hHeadModByZero :
                                            f =
                                              Term.UOp UserOp._at_mod_by_zero
                                          · subst f
                                            exact
                                              substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                UserOp._at_mod_by_zero
                                                a xs ts bvs hXsEnv hBvsEnv hTs
                                                (fun q v vs hEq =>
                                                  hBinder ⟨q, v, vs, hEq⟩)
                                                hFTrans hTy
                                                (fun h =>
                                                  mod_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                (fun X hApp => by
                                                  change
                                                    __eo_typeof_int_pow2
                                                        (__eo_typeof X) ≠
                                                      Term.Stuck at hApp
                                                  rw [
                                                    eo_typeof_int_pow2_arg_int_of_ne_stuck
                                                      hApp]
                                                  intro h
                                                  cases h)
                                                (fun X Y hXY => by
                                                  change
                                                    __eo_typeof_int_pow2
                                                        (__eo_typeof X) =
                                                      __eo_typeof_int_pow2
                                                        (__eo_typeof Y)
                                                  rw [hXY])
                                                (fun X hXTrans hApp => by
                                                  have hXMatch :
                                                      __smtx_typeof (__eo_to_smt X) =
                                                        __eo_to_smt_type
                                                          (__eo_typeof X) :=
                                                    TranslationProofs.eo_to_smt_typeof_matches_translation
                                                      X hXTrans
                                                  unfold RuleProofs.eo_has_smt_translation
                                                  change
                                                    __smtx_typeof
                                                        (SmtTerm.mod (__eo_to_smt X)
                                                          (SmtTerm.Numeral 0)) ≠
                                                      SmtType.None
                                                  rw [typeof_mod_eq]
                                                  change
                                                    __eo_typeof_int_pow2
                                                        (__eo_typeof X) ≠
                                                      Term.Stuck at hApp
                                                  have hArgInt :=
                                                    eo_typeof_int_pow2_arg_int_of_ne_stuck
                                                      hApp
                                                  have hSmtArg :
                                                      __smtx_typeof (__eo_to_smt X) =
                                                        SmtType.Int := by
                                                    rw [hXMatch, hArgInt]
                                                    rfl
                                                  simp [hSmtArg,
                                                    __smtx_typeof.eq_2,
                                                    native_ite, native_Teq])
                                                (fun hATrans hATy =>
                                                  hRec
                                                    (G := a) (xs' := xs)
                                                    (ts' := ts) (bvs' := bvs)
                                                    (by simp)
                                                    hXsEnv hBvsEnv hATrans hTs
                                                    hActuals hATy)
                                          · by_cases hHeadQDivByZero :
                                              f =
                                                Term.UOp UserOp._at_div_by_zero
                                            · subst f
                                              exact
                                                substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                  UserOp._at_div_by_zero
                                                  a xs ts bvs hXsEnv hBvsEnv hTs
                                                  (fun q v vs hEq =>
                                                    hBinder ⟨q, v, vs, hEq⟩)
                                                  hFTrans hTy
                                                  (fun h =>
                                                    qdiv_by_zero_arg_has_smt_translation_of_has_smt_translation h)
                                                  (fun X hApp => by
                                                    change
                                                      __eo_typeof__at_div_by_zero
                                                          (__eo_typeof X) ≠
                                                        Term.Stuck at hApp
                                                    rw [
                                                      eo_typeof_at_div_by_zero_arg_real_of_ne_stuck
                                                        hApp]
                                                    intro h
                                                    cases h)
                                                  (fun X Y hXY => by
                                                    change
                                                      __eo_typeof__at_div_by_zero
                                                          (__eo_typeof X) =
                                                        __eo_typeof__at_div_by_zero
                                                          (__eo_typeof Y)
                                                    rw [hXY])
                                                  (fun X hXTrans hApp => by
                                                    have hXMatch :
                                                        __smtx_typeof
                                                            (__eo_to_smt X) =
                                                          __eo_to_smt_type
                                                            (__eo_typeof X) :=
                                                      TranslationProofs.eo_to_smt_typeof_matches_translation
                                                        X hXTrans
                                                    unfold RuleProofs.eo_has_smt_translation
                                                    change
                                                      __smtx_typeof
                                                          (SmtTerm.qdiv
                                                            (__eo_to_smt X)
                                                            (SmtTerm.Rational
                                                              (native_mk_rational
                                                                0 1))) ≠
                                                        SmtType.None
                                                    change
                                                      __eo_typeof__at_div_by_zero
                                                          (__eo_typeof X) ≠
                                                        Term.Stuck at hApp
                                                    have hArgReal :=
                                                      eo_typeof_at_div_by_zero_arg_real_of_ne_stuck
                                                        hApp
                                                    have hSmtArg :
                                                        __smtx_typeof
                                                            (__eo_to_smt X) =
                                                          SmtType.Real := by
                                                      rw [hXMatch, hArgReal]
                                                      rfl
                                                    have hRatTy :
                                                        __smtx_typeof
                                                            (SmtTerm.Rational
                                                              (native_mk_rational
                                                                0 1)) =
                                                          SmtType.Real := by
                                                      unfold __smtx_typeof
                                                      rfl
                                                    rw [typeof_qdiv_eq, hSmtArg,
                                                      hRatTy]
                                                    simp [
                                                      __smtx_typeof_arith_overload_op_2_ret])
                                                  (fun hATrans hATy =>
                                                    hRec
                                                      (G := a) (xs' := xs)
                                                      (ts' := ts)
                                                      (bvs' := bvs)
                                                      (by simp)
                                                      hXsEnv hBvsEnv hATrans hTs
                                                      hActuals hATy)
                                            · by_cases hHeadBvnot :
                                                f = Term.UOp UserOp.bvnot
                                              · subst f
                                                exact
                                                  substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                    UserOp.bvnot a xs ts bvs
                                                    hXsEnv hBvsEnv hTs
                                                    (fun q v vs hEq =>
                                                      hBinder ⟨q, v, vs, hEq⟩)
                                                    hFTrans hTy
                                                    (fun h =>
                                                      bvnot_arg_has_smt_translation_of_has_smt_translation h)
                                                    (fun X hApp => by
                                                      change
                                                        __eo_typeof_bvnot
                                                            (__eo_typeof X) ≠
                                                          Term.Stuck at hApp
                                                      rcases
                                                          eo_typeof_bvnot_arg_bitvec_of_ne_stuck
                                                            hApp with
                                                        ⟨w, hArg⟩
                                                      rw [hArg]
                                                      intro h
                                                      cases h)
                                                    (fun X Y hXY => by
                                                      change
                                                        __eo_typeof_bvnot
                                                            (__eo_typeof X) =
                                                          __eo_typeof_bvnot
                                                            (__eo_typeof Y)
                                                      rw [hXY])
                                                    (fun X hXTrans hApp => by
                                                      unfold RuleProofs.eo_has_smt_translation
                                                      change
                                                        __smtx_typeof
                                                            (SmtTerm.bvnot
                                                              (__eo_to_smt X)) ≠
                                                          SmtType.None
                                                      change
                                                        __eo_typeof_bvnot
                                                            (__eo_typeof X) ≠
                                                          Term.Stuck at hApp
                                                      rcases
                                                          eo_typeof_bvnot_arg_bitvec_of_ne_stuck
                                                            hApp with
                                                        ⟨w, hArgEo⟩
                                                      rcases
                                                          smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                            hXTrans hArgEo with
                                                        ⟨n, hSmtArg⟩
                                                      rw [smt_typeof_bvnot_eq, hSmtArg]
                                                      simp [__smtx_typeof_bv_op_1])
                                                    (fun hATrans hATy =>
                                                      hRec
                                                        (G := a) (xs' := xs)
                                                        (ts' := ts)
                                                        (bvs' := bvs)
                                                        (by simp)
                                                        hXsEnv hBvsEnv hATrans
                                                        hTs hActuals hATy)
                                              · by_cases hHeadBvneg :
                                                  f = Term.UOp UserOp.bvneg
                                                · subst f
                                                  exact
                                                    substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                      UserOp.bvneg a xs ts bvs
                                                      hXsEnv hBvsEnv hTs
                                                      (fun q v vs hEq =>
                                                        hBinder ⟨q, v, vs, hEq⟩)
                                                      hFTrans hTy
                                                      (fun h =>
                                                        bvneg_arg_has_smt_translation_of_has_smt_translation h)
                                                      (fun X hApp => by
                                                        change
                                                          __eo_typeof_bvnot
                                                              (__eo_typeof X) ≠
                                                            Term.Stuck at hApp
                                                        rcases
                                                            eo_typeof_bvnot_arg_bitvec_of_ne_stuck
                                                              hApp with
                                                          ⟨w, hArg⟩
                                                        rw [hArg]
                                                        intro h
                                                        cases h)
                                                      (fun X Y hXY => by
                                                        change
                                                          __eo_typeof_bvnot
                                                              (__eo_typeof X) =
                                                            __eo_typeof_bvnot
                                                              (__eo_typeof Y)
                                                        rw [hXY])
                                                      (fun X hXTrans hApp => by
                                                        unfold RuleProofs.eo_has_smt_translation
                                                        change
                                                          __smtx_typeof
                                                              (SmtTerm.bvneg
                                                                (__eo_to_smt X)) ≠
                                                            SmtType.None
                                                        change
                                                          __eo_typeof_bvnot
                                                              (__eo_typeof X) ≠
                                                            Term.Stuck at hApp
                                                        rcases
                                                            eo_typeof_bvnot_arg_bitvec_of_ne_stuck
                                                              hApp with
                                                          ⟨w, hArgEo⟩
                                                        rcases
                                                            smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                              hXTrans hArgEo with
                                                          ⟨n, hSmtArg⟩
                                                        rw [smt_typeof_bvneg_eq,
                                                          hSmtArg]
                                                        simp [__smtx_typeof_bv_op_1])
                                                      (fun hATrans hATy =>
                                                        hRec
                                                          (G := a) (xs' := xs)
                                                          (ts' := ts)
                                                          (bvs' := bvs)
                                                          (by simp)
                                                          hXsEnv hBvsEnv hATrans
                                                          hTs hActuals hATy)
                                                · by_cases hHeadBvnego :
                                                    f = Term.UOp UserOp.bvnego
                                                  · subst f
                                                    exact
                                                      substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                        UserOp.bvnego a xs ts bvs
                                                        hXsEnv hBvsEnv hTs
                                                        (fun q v vs hEq =>
                                                          hBinder
                                                            ⟨q, v, vs, hEq⟩)
                                                        hFTrans hTy
                                                        (fun h =>
                                                          bvnego_arg_has_smt_translation_of_has_smt_translation h)
                                                        (fun X hApp => by
                                                          change
                                                            __eo_typeof_bvnego
                                                                (__eo_typeof X) ≠
                                                              Term.Stuck at hApp
                                                          rcases
                                                              eo_typeof_bvnego_arg_bitvec_of_ne_stuck
                                                                hApp with
                                                            ⟨w, hArg⟩
                                                          rw [hArg]
                                                          intro h
                                                          cases h)
                                                        (fun X Y hXY => by
                                                          change
                                                            __eo_typeof_bvnego
                                                                (__eo_typeof X) =
                                                              __eo_typeof_bvnego
                                                                (__eo_typeof Y)
                                                          rw [hXY])
                                                        (fun X hXTrans hApp => by
                                                          unfold RuleProofs.eo_has_smt_translation
                                                          change
                                                            __smtx_typeof
                                                                (SmtTerm.bvnego
                                                                  (__eo_to_smt X)) ≠
                                                              SmtType.None
                                                          change
                                                            __eo_typeof_bvnego
                                                                (__eo_typeof X) ≠
                                                              Term.Stuck at hApp
                                                          rcases
                                                              eo_typeof_bvnego_arg_bitvec_of_ne_stuck
                                                                hApp with
                                                            ⟨w, hArgEo⟩
                                                          rcases
                                                              smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                hXTrans hArgEo with
                                                            ⟨n, hSmtArg⟩
                                                          rw [smt_typeof_bvnego_eq,
                                                            hSmtArg]
                                                          simp [
                                                            __smtx_typeof_bv_op_1_ret])
                                                        (fun hATrans hATy =>
                                                          hRec
                                                            (G := a)
                                                            (xs' := xs)
                                                            (ts' := ts)
                                                            (bvs' := bvs)
                                                            (by simp)
                                                            hXsEnv hBvsEnv
                                                            hATrans hTs
                                                            hActuals hATy)
                                                  · by_cases hHeadBvsize :
                                                      f =
                                                        Term.UOp UserOp._at_bvsize
                                                    · subst f
                                                      exact
                                                        substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                          UserOp._at_bvsize
                                                          a xs ts bvs
                                                          hXsEnv hBvsEnv hTs
                                                          (fun q v vs hEq =>
                                                            hBinder
                                                              ⟨q, v, vs, hEq⟩)
                                                          hFTrans hTy
                                                          (fun h =>
                                                            bvsize_arg_has_smt_translation_of_has_smt_translation h)
                                                          (fun X hApp => by
                                                            change
                                                              __eo_typeof__at_bvsize
                                                                  (__eo_typeof X) ≠
                                                                Term.Stuck at hApp
                                                            rcases
                                                                eo_typeof_bvsize_arg_bitvec_of_ne_stuck
                                                                  hApp with
                                                              ⟨w, hArg⟩
                                                            rw [hArg]
                                                            intro h
                                                            cases h)
                                                          (fun X Y hXY => by
                                                            change
                                                              __eo_typeof__at_bvsize
                                                                  (__eo_typeof X) =
                                                                __eo_typeof__at_bvsize
                                                                  (__eo_typeof Y)
                                                            rw [hXY])
                                                          (fun X hXTrans hApp => by
                                                            unfold RuleProofs.eo_has_smt_translation
                                                            change
                                                              __smtx_typeof
                                                                  (native_ite
                                                                    (native_zleq 0
                                                                      (__smtx_bv_sizeof_type
                                                                        (__smtx_typeof
                                                                          (__eo_to_smt X))))
                                                                    (SmtTerm._at_purify
                                                                      (SmtTerm.Numeral
                                                                        (__smtx_bv_sizeof_type
                                                                          (__smtx_typeof
                                                                            (__eo_to_smt X)))))
                                                                    SmtTerm.None) ≠
                                                                SmtType.None
                                                            change
                                                              __eo_typeof__at_bvsize
                                                                  (__eo_typeof X) ≠
                                                                Term.Stuck at hApp
                                                            rcases
                                                                eo_typeof_bvsize_arg_bitvec_of_ne_stuck
                                                                  hApp with
                                                              ⟨w, hArgEo⟩
                                                            rcases
                                                                smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                  hXTrans hArgEo with
                                                              ⟨n, hSmtArg⟩
                                                            rw [hSmtArg]
                                                            simp [__smtx_bv_sizeof_type,
                                                              __smtx_typeof.eq_11,
                                                              __smtx_typeof.eq_2,
                                                              native_ite, native_zleq,
                                                              SmtEval.native_zleq,
                                                              SmtEval.native_nat_to_int])
                                                          (fun hATrans hATy =>
                                                            hRec
                                                              (G := a)
                                                              (xs' := xs)
                                                              (ts' := ts)
                                                              (bvs' := bvs)
                                                              (by simp)
                                                              hXsEnv hBvsEnv
                                                              hATrans hTs
                                                              hActuals hATy)
                                                    · by_cases hHeadBvredand :
                                                        f =
                                                          Term.UOp UserOp.bvredand
                                                      · subst f
                                                        exact
                                                          substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                            UserOp.bvredand
                                                            a xs ts bvs
                                                            hXsEnv hBvsEnv hTs
                                                            (fun q v vs hEq =>
                                                              hBinder
                                                                ⟨q, v, vs, hEq⟩)
                                                            hFTrans hTy
                                                            (fun h =>
                                                              bvredand_arg_has_smt_translation_of_has_smt_translation h)
                                                            (fun X hApp => by
                                                              change
                                                                __eo_typeof_bvredand
                                                                    (__eo_typeof X) ≠
                                                                  Term.Stuck at hApp
                                                              rcases
                                                                  eo_typeof_bvredand_arg_bitvec_of_ne_stuck
                                                                    hApp with
                                                                ⟨w, hArg⟩
                                                              rw [hArg]
                                                              intro h
                                                              cases h)
                                                            (fun X Y hXY => by
                                                              change
                                                                __eo_typeof_bvredand
                                                                    (__eo_typeof X) =
                                                                  __eo_typeof_bvredand
                                                                    (__eo_typeof Y)
                                                              rw [hXY])
                                                            (fun X hXTrans hApp => by
                                                              unfold RuleProofs.eo_has_smt_translation
                                                              change
                                                                __smtx_typeof
                                                                    (SmtTerm.bvcomp
                                                                      (__eo_to_smt X)
                                                                      (SmtTerm.bvnot
                                                                        (SmtTerm.Binary
                                                                          (__smtx_bv_sizeof_type
                                                                            (__smtx_typeof
                                                                              (__eo_to_smt X)))
                                                                          0))) ≠
                                                                  SmtType.None
                                                              change
                                                                __eo_typeof_bvredand
                                                                    (__eo_typeof X) ≠
                                                                  Term.Stuck at hApp
                                                              rcases
                                                                  eo_typeof_bvredand_arg_bitvec_of_ne_stuck
                                                                    hApp with
                                                                ⟨w, hArgEo⟩
                                                              rcases
                                                                  smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                    hXTrans hArgEo with
                                                                ⟨n, hSmtArg⟩
                                                              rw [smt_typeof_bvcomp_eq,
                                                                hSmtArg,
                                                                smt_typeof_bvnot_eq]
                                                              simp [__smtx_bv_sizeof_type,
                                                                smt_typeof_binary_nat_to_int_zero,
                                                                __smtx_typeof_bv_op_1,
                                                                __smtx_typeof_bv_op_2_ret,
                                                                native_ite,
                                                                native_nateq,
                                                                SmtEval.native_nateq])
                                                            (fun hATrans hATy =>
                                                              hRec
                                                                (G := a)
                                                                (xs' := xs)
                                                                (ts' := ts)
                                                                (bvs' := bvs)
                                                                (by simp)
                                                                hXsEnv hBvsEnv
                                                                hATrans hTs
                                                                hActuals hATy)
                                                      · by_cases hHeadBvredor :
                                                          f =
                                                            Term.UOp UserOp.bvredor
                                                        · subst f
                                                          exact
                                                            substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                              UserOp.bvredor
                                                              a xs ts bvs
                                                              hXsEnv hBvsEnv hTs
                                                              (fun q v vs hEq =>
                                                                hBinder
                                                                  ⟨q, v, vs, hEq⟩)
                                                              hFTrans hTy
                                                              (fun h =>
                                                                bvredor_arg_has_smt_translation_of_has_smt_translation h)
                                                              (fun X hApp => by
                                                                change
                                                                  __eo_typeof_bvredand
                                                                      (__eo_typeof X) ≠
                                                                    Term.Stuck at hApp
                                                                rcases
                                                                    eo_typeof_bvredand_arg_bitvec_of_ne_stuck
                                                                      hApp with
                                                                  ⟨w, hArg⟩
                                                                rw [hArg]
                                                                intro h
                                                                cases h)
                                                              (fun X Y hXY => by
                                                                change
                                                                  __eo_typeof_bvredand
                                                                      (__eo_typeof X) =
                                                                    __eo_typeof_bvredand
                                                                      (__eo_typeof Y)
                                                                rw [hXY])
                                                              (fun X hXTrans hApp => by
                                                                unfold RuleProofs.eo_has_smt_translation
                                                                change
                                                                  __smtx_typeof
                                                                      (SmtTerm.bvnot
                                                                        (SmtTerm.bvcomp
                                                                          (__eo_to_smt X)
                                                                          (SmtTerm.Binary
                                                                            (__smtx_bv_sizeof_type
                                                                              (__smtx_typeof
                                                                                (__eo_to_smt X)))
                                                                            0))) ≠
                                                                    SmtType.None
                                                                change
                                                                  __eo_typeof_bvredand
                                                                      (__eo_typeof X) ≠
                                                                    Term.Stuck at hApp
                                                                rcases
                                                                    eo_typeof_bvredand_arg_bitvec_of_ne_stuck
                                                                      hApp with
                                                                  ⟨w, hArgEo⟩
                                                                rcases
                                                                    smt_typeof_eo_to_smt_bitvec_of_typeof_bitvec
                                                                      hXTrans hArgEo with
                                                                  ⟨n, hSmtArg⟩
                                                                rw [smt_typeof_bvnot_eq,
                                                                  smt_typeof_bvcomp_eq,
                                                                  hSmtArg]
                                                                simp [
                                                                  __smtx_bv_sizeof_type,
                                                                  smt_typeof_binary_nat_to_int_zero,
                                                                  __smtx_typeof_bv_op_1,
                                                                  __smtx_typeof_bv_op_2_ret,
                                                                  native_ite,
                                                                  native_nateq,
                                                                  SmtEval.native_nateq])
                                                              (fun hATrans hATy =>
                                                                hRec
                                                                  (G := a)
                                                                  (xs' := xs)
                                                                  (ts' := ts)
                                                                  (bvs' := bvs)
                                                                  (by simp)
                                                                  hXsEnv hBvsEnv
                                                                  hATrans hTs
                                                                  hActuals hATy)
                                                        · by_cases hHeadStrLen :
                                                            f =
                                                              Term.UOp UserOp.str_len
                                                          · subst f
                                                            exact
                                                              substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                UserOp.str_len
                                                                a xs ts bvs
                                                                hXsEnv hBvsEnv hTs
                                                                (fun q v vs hEq =>
                                                                  hBinder
                                                                    ⟨q, v, vs,
                                                                      hEq⟩)
                                                                hFTrans hTy
                                                                (fun h =>
                                                                  str_len_arg_has_smt_translation_of_has_smt_translation h)
                                                                (fun X hApp => by
                                                                  change
                                                                    __eo_typeof_str_len
                                                                        (__eo_typeof X) ≠
                                                                      Term.Stuck at hApp
                                                                  rcases
                                                                      eo_typeof_str_len_arg_seq_of_ne_stuck
                                                                        hApp with
                                                                    ⟨V, hArg⟩
                                                                  rw [hArg]
                                                                  intro h
                                                                  cases h)
                                                                (fun X Y hXY => by
                                                                  change
                                                                    __eo_typeof_str_len
                                                                        (__eo_typeof X) =
                                                                      __eo_typeof_str_len
                                                                        (__eo_typeof Y)
                                                                  rw [hXY])
                                                                (fun X hXTrans hApp => by
                                                                  unfold RuleProofs.eo_has_smt_translation
                                                                  change
                                                                    __smtx_typeof
                                                                        (SmtTerm.str_len
                                                                          (__eo_to_smt X)) ≠
                                                                      SmtType.None
                                                                  change
                                                                    __eo_typeof_str_len
                                                                        (__eo_typeof X) ≠
                                                                      Term.Stuck at hApp
                                                                  rcases
                                                                      eo_typeof_str_len_arg_seq_of_ne_stuck
                                                                        hApp with
                                                                    ⟨V, hArgEo⟩
                                                                  rcases
                                                                      smt_typeof_eo_to_smt_seq_of_typeof_seq
                                                                        hXTrans
                                                                        hArgEo with
                                                                    ⟨T, hSmtArg⟩
                                                                  rw [typeof_str_len_eq,
                                                                    hSmtArg]
                                                                  simp [
                                                                    __smtx_typeof_seq_op_1_ret])
                                                                (fun hATrans hATy =>
                                                                  hRec
                                                                    (G := a)
                                                                    (xs' := xs)
                                                                    (ts' := ts)
                                                                    (bvs' := bvs)
                                                                    (by simp)
                                                                    hXsEnv hBvsEnv
                                                                    hATrans hTs
                                                                    hActuals hATy)
                                                          · by_cases hHeadStrRev :
                                                              f =
                                                                Term.UOp
                                                                  UserOp.str_rev
                                                            · subst f
                                                              exact
                                                                substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                  UserOp.str_rev
                                                                  a xs ts bvs
                                                                  hXsEnv hBvsEnv hTs
                                                                  (fun q v vs hEq =>
                                                                    hBinder
                                                                      ⟨q, v, vs,
                                                                        hEq⟩)
                                                                  hFTrans hTy
                                                                  (fun h =>
                                                                    str_rev_arg_has_smt_translation_of_has_smt_translation h)
                                                                  (fun X hApp => by
                                                                    change
                                                                      __eo_typeof_str_rev
                                                                          (__eo_typeof X) ≠
                                                                        Term.Stuck at hApp
                                                                    rcases
                                                                        eo_typeof_str_rev_arg_seq_of_ne_stuck
                                                                          hApp with
                                                                      ⟨V, hArg⟩
                                                                    rw [hArg]
                                                                    intro h
                                                                    cases h)
                                                                  (fun X Y hXY => by
                                                                    change
                                                                      __eo_typeof_str_rev
                                                                          (__eo_typeof X) =
                                                                        __eo_typeof_str_rev
                                                                          (__eo_typeof Y)
                                                                    rw [hXY])
                                                                  (fun X hXTrans hApp => by
                                                                    unfold RuleProofs.eo_has_smt_translation
                                                                    change
                                                                      __smtx_typeof
                                                                          (SmtTerm.str_rev
                                                                            (__eo_to_smt X)) ≠
                                                                        SmtType.None
                                                                    change
                                                                      __eo_typeof_str_rev
                                                                          (__eo_typeof X) ≠
                                                                        Term.Stuck at hApp
                                                                    rcases
                                                                        eo_typeof_str_rev_arg_seq_of_ne_stuck
                                                                          hApp with
                                                                      ⟨V, hArgEo⟩
                                                                    rcases
                                                                        smt_typeof_eo_to_smt_seq_of_typeof_seq
                                                                          hXTrans
                                                                          hArgEo with
                                                                      ⟨T, hSmtArg⟩
                                                                    rw [typeof_str_rev_eq,
                                                                      hSmtArg]
                                                                    simp [
                                                                      __smtx_typeof_seq_op_1])
                                                                  (fun hATrans hATy =>
                                                                    hRec
                                                                      (G := a)
                                                                      (xs' := xs)
                                                                      (ts' := ts)
                                                                      (bvs' := bvs)
                                                                      (by simp)
                                                                      hXsEnv
                                                                      hBvsEnv
                                                                      hATrans hTs
                                                                      hActuals
                                                                      hATy)
                                                            · by_cases hHeadStrToInt :
                                                                f =
                                                                  Term.UOp
                                                                    UserOp.str_to_int
                                                              · subst f
                                                                exact
                                                                  substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                    UserOp.str_to_int
                                                                    a xs ts bvs
                                                                    hXsEnv hBvsEnv
                                                                    hTs
                                                                    (fun q v vs hEq =>
                                                                      hBinder
                                                                        ⟨q, v, vs,
                                                                          hEq⟩)
                                                                    hFTrans hTy
                                                                    (fun h =>
                                                                      str_to_int_arg_has_smt_translation_of_has_smt_translation h)
                                                                    (fun X hApp => by
                                                                      change
                                                                        __eo_typeof_str_to_code
                                                                            (__eo_typeof X) ≠
                                                                          Term.Stuck at hApp
                                                                      rw [
                                                                        eo_typeof_str_to_code_arg_seq_char_of_ne_stuck
                                                                          hApp]
                                                                      intro h
                                                                      cases h)
                                                                    (fun X Y hXY => by
                                                                      change
                                                                        __eo_typeof_str_to_code
                                                                            (__eo_typeof X) =
                                                                          __eo_typeof_str_to_code
                                                                            (__eo_typeof Y)
                                                                      rw [hXY])
                                                                    (fun X hXTrans hApp => by
                                                                      unfold RuleProofs.eo_has_smt_translation
                                                                      change
                                                                        __smtx_typeof
                                                                            (SmtTerm.str_to_int
                                                                              (__eo_to_smt X)) ≠
                                                                          SmtType.None
                                                                      change
                                                                        __eo_typeof_str_to_code
                                                                            (__eo_typeof X) ≠
                                                                          Term.Stuck at hApp
                                                                      have hArgEo :=
                                                                        eo_typeof_str_to_code_arg_seq_char_of_ne_stuck
                                                                          hApp
                                                                      have hSmtArg :=
                                                                        smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                          hXTrans
                                                                          hArgEo
                                                                      rw [typeof_str_to_int_eq,
                                                                        hSmtArg]
                                                                      simp [native_ite,
                                                                        native_Teq])
                                                                    (fun hATrans hATy =>
                                                                      hRec
                                                                        (G := a)
                                                                        (xs' := xs)
                                                                        (ts' := ts)
                                                                        (bvs' := bvs)
                                                                        (by simp)
                                                                        hXsEnv
                                                                        hBvsEnv
                                                                        hATrans hTs
                                                                        hActuals
                                                                        hATy)
                                                              · by_cases hHeadStrToRe :
                                                                  f =
                                                                    Term.UOp
                                                                      UserOp.str_to_re
                                                                · subst f
                                                                  exact
                                                                    substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                      UserOp.str_to_re
                                                                      a xs ts bvs
                                                                      hXsEnv
                                                                      hBvsEnv hTs
                                                                      (fun q v vs hEq =>
                                                                        hBinder
                                                                          ⟨q, v, vs,
                                                                            hEq⟩)
                                                                      hFTrans hTy
                                                                      (fun h =>
                                                                        str_to_re_arg_has_smt_translation_of_has_smt_translation h)
                                                                      (fun X hApp => by
                                                                        change
                                                                          __eo_typeof_str_to_re
                                                                              (__eo_typeof X) ≠
                                                                            Term.Stuck at hApp
                                                                        rw [
                                                                          eo_typeof_str_to_re_arg_seq_char_of_ne_stuck
                                                                            hApp]
                                                                        intro h
                                                                        cases h)
                                                                      (fun X Y hXY => by
                                                                        change
                                                                          __eo_typeof_str_to_re
                                                                              (__eo_typeof X) =
                                                                            __eo_typeof_str_to_re
                                                                              (__eo_typeof Y)
                                                                        rw [hXY])
                                                                      (fun X hXTrans hApp => by
                                                                        unfold RuleProofs.eo_has_smt_translation
                                                                        change
                                                                          __smtx_typeof
                                                                              (SmtTerm.str_to_re
                                                                                (__eo_to_smt X)) ≠
                                                                            SmtType.None
                                                                        change
                                                                          __eo_typeof_str_to_re
                                                                              (__eo_typeof X) ≠
                                                                            Term.Stuck at hApp
                                                                        have hArgEo :=
                                                                          eo_typeof_str_to_re_arg_seq_char_of_ne_stuck
                                                                            hApp
                                                                        have hSmtArg :=
                                                                          smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                            hXTrans
                                                                            hArgEo
                                                                        rw [typeof_str_to_re_eq,
                                                                          hSmtArg]
                                                                        simp [native_ite,
                                                                          native_Teq])
                                                                      (fun hATrans hATy =>
                                                                        hRec
                                                                          (G := a)
                                                                          (xs' := xs)
                                                                          (ts' := ts)
                                                                          (bvs' := bvs)
                                                                          (by simp)
                                                                          hXsEnv
                                                                          hBvsEnv
                                                                          hATrans
                                                                          hTs
                                                                          hActuals
                                                                          hATy)
                                                                · by_cases hHeadReMult :
                                                                    f =
                                                                      Term.UOp
                                                                        UserOp.re_mult
                                                                  · subst f
                                                                    exact
                                                                      substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                        UserOp.re_mult
                                                                        a xs ts bvs
                                                                        hXsEnv
                                                                        hBvsEnv hTs
                                                                        (fun q v vs hEq =>
                                                                          hBinder
                                                                            ⟨q, v,
                                                                              vs,
                                                                              hEq⟩)
                                                                        hFTrans hTy
                                                                        (fun h =>
                                                                          re_mult_arg_has_smt_translation_of_has_smt_translation h)
                                                                        (fun X hApp => by
                                                                          change
                                                                            __eo_typeof_re_mult
                                                                                (__eo_typeof X) ≠
                                                                              Term.Stuck at hApp
                                                                          rw [
                                                                            eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                              hApp]
                                                                          intro h
                                                                          cases h)
                                                                        (fun X Y hXY => by
                                                                          change
                                                                            __eo_typeof_re_mult
                                                                                (__eo_typeof X) =
                                                                              __eo_typeof_re_mult
                                                                                (__eo_typeof Y)
                                                                          rw [hXY])
                                                                        (fun X hXTrans hApp => by
                                                                          unfold RuleProofs.eo_has_smt_translation
                                                                          change
                                                                            __smtx_typeof
                                                                                (SmtTerm.re_mult
                                                                                  (__eo_to_smt X)) ≠
                                                                              SmtType.None
                                                                          change
                                                                            __eo_typeof_re_mult
                                                                                (__eo_typeof X) ≠
                                                                              Term.Stuck at hApp
                                                                          have hArgEo :=
                                                                            eo_typeof_re_mult_arg_reglan_of_ne_stuck
                                                                              hApp
                                                                          have hSmtArg :=
                                                                            smt_typeof_eo_to_smt_reglan_of_typeof_reglan
                                                                              hXTrans
                                                                              hArgEo
                                                                          rw [typeof_re_mult_eq,
                                                                            hSmtArg]
                                                                          simp [
                                                                            native_ite,
                                                                            native_Teq])
                                                                        (fun hATrans hATy =>
                                                                          hRec
                                                                            (G := a)
                                                                            (xs' := xs)
                                                                            (ts' := ts)
                                                                            (bvs' := bvs)
                                                                            (by simp)
                                                                            hXsEnv
                                                                            hBvsEnv
                                                                            hATrans
                                                                            hTs
                                                                            hActuals
                                                                            hATy)
                                                                  · by_cases hHeadStrToLower :
                                                                      f =
                                                                        Term.UOp
                                                                          UserOp.str_to_lower
                                                                    · subst f
                                                                      exact
                                                                        substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                          UserOp.str_to_lower
                                                                          a xs ts
                                                                          bvs
                                                                          hXsEnv
                                                                          hBvsEnv
                                                                          hTs
                                                                          (fun q v vs hEq =>
                                                                            hBinder
                                                                              ⟨q, v,
                                                                                vs,
                                                                                hEq⟩)
                                                                          hFTrans
                                                                          hTy
                                                                          (fun h =>
                                                                            str_to_lower_arg_has_smt_translation_of_has_smt_translation h)
                                                                          (fun X hApp => by
                                                                            change
                                                                              __eo_typeof_str_to_lower
                                                                                  (__eo_typeof X) ≠
                                                                                Term.Stuck at hApp
                                                                            rw [
                                                                              eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck
                                                                                hApp]
                                                                            intro h
                                                                            cases h)
                                                                          (fun X Y hXY => by
                                                                            change
                                                                              __eo_typeof_str_to_lower
                                                                                  (__eo_typeof X) =
                                                                                __eo_typeof_str_to_lower
                                                                                  (__eo_typeof Y)
                                                                            rw [hXY])
                                                                          (fun X hXTrans hApp => by
                                                                            unfold RuleProofs.eo_has_smt_translation
                                                                            change
                                                                              __smtx_typeof
                                                                                  (SmtTerm.str_to_lower
                                                                                    (__eo_to_smt X)) ≠
                                                                                SmtType.None
                                                                            change
                                                                              __eo_typeof_str_to_lower
                                                                                  (__eo_typeof X) ≠
                                                                                Term.Stuck at hApp
                                                                            have hArgEo :=
                                                                              eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck
                                                                                hApp
                                                                            have hSmtArg :=
                                                                              smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                                hXTrans
                                                                                hArgEo
                                                                            rw [
                                                                              typeof_str_to_lower_eq,
                                                                              hSmtArg]
                                                                            simp [
                                                                              native_ite,
                                                                              native_Teq])
                                                                          (fun hATrans hATy =>
                                                                            hRec
                                                                              (G := a)
                                                                              (xs' := xs)
                                                                              (ts' := ts)
                                                                              (bvs' := bvs)
                                                                              (by simp)
                                                                              hXsEnv
                                                                              hBvsEnv
                                                                              hATrans
                                                                              hTs
                                                                              hActuals
                                                                              hATy)
                                                                    · by_cases hHeadStrToUpper :
                                                                        f =
                                                                          Term.UOp
                                                                            UserOp.str_to_upper
                                                                      · subst f
                                                                        exact
                                                                          substitute_simul_unary_op_preserves_type_and_translation_of_typeof_ne_stuck
                                                                            UserOp.str_to_upper
                                                                            a xs ts
                                                                            bvs
                                                                            hXsEnv
                                                                            hBvsEnv
                                                                            hTs
                                                                            (fun q v vs hEq =>
                                                                              hBinder
                                                                                ⟨q, v,
                                                                                  vs,
                                                                                  hEq⟩)
                                                                            hFTrans
                                                                            hTy
                                                                            (fun h =>
                                                                              str_to_upper_arg_has_smt_translation_of_has_smt_translation h)
                                                                            (fun X hApp => by
                                                                              change
                                                                                __eo_typeof_str_to_lower
                                                                                    (__eo_typeof X) ≠
                                                                                  Term.Stuck at hApp
                                                                              rw [
                                                                                eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck
                                                                                  hApp]
                                                                              intro h
                                                                              cases h)
                                                                            (fun X Y hXY => by
                                                                              change
                                                                                __eo_typeof_str_to_lower
                                                                                    (__eo_typeof X) =
                                                                                  __eo_typeof_str_to_lower
                                                                                    (__eo_typeof Y)
                                                                              rw [hXY])
                                                                            (fun X hXTrans hApp => by
                                                                              unfold RuleProofs.eo_has_smt_translation
                                                                              change
                                                                                __smtx_typeof
                                                                                    (SmtTerm.str_to_upper
                                                                                      (__eo_to_smt X)) ≠
                                                                                  SmtType.None
                                                                              change
                                                                                __eo_typeof_str_to_lower
                                                                                    (__eo_typeof X) ≠
                                                                                  Term.Stuck at hApp
                                                                              have hArgEo :=
                                                                                eo_typeof_str_to_lower_arg_seq_char_of_ne_stuck
                                                                                  hApp
                                                                              have hSmtArg :=
                                                                                smt_typeof_eo_to_smt_seq_char_of_typeof_seq_char
                                                                                  hXTrans
                                                                                  hArgEo
                                                                              rw [
                                                                                typeof_str_to_upper_eq,
                                                                                hSmtArg]
                                                                              simp [
                                                                                native_ite,
                                                                                native_Teq])
                                                                            (fun hATrans hATy =>
                                                                              hRec
                                                                                (G := a)
                                                                                (xs' := xs)
                                                                                (ts' := ts)
                                                                                (bvs' := bvs)
                                                                                (by simp)
                                                                                hXsEnv
                                                                                hBvsEnv
                                                                                hATrans
                                                                                hTs
                                                                                hActuals
                                                                                hATy)
                                                                      · exact hOld
                  · have hHeadNotApply : ∀ g x, f ≠ Term.Apply g x := by
                      intro g x hEq
                      exact hHeadApply ⟨g, x, hEq⟩
                    have hHeadNotVar : ∀ name T, f ≠ Term.Var name T := by
                      intro name T hEq
                      exact hHeadVar ⟨name, T, hEq⟩
                    have hNoUOp : ∀ op, f ≠ Term.UOp op := by
                      intro op hEq
                      exact hHeadSpecial (Or.inl ⟨op, hEq⟩)
                    have hNoUOp1 :
                        ∀ op x, f ≠ Term.UOp1 op x := by
                      intro op x hEq
                      exact hHeadSpecial (Or.inr (Or.inl ⟨op, x, hEq⟩))
                    have hNoUOp2 :
                        ∀ op x y, f ≠ Term.UOp2 op x y := by
                      intro op x y hEq
                      exact hHeadSpecial
                        (Or.inr (Or.inr (Or.inl ⟨op, x, y, hEq⟩)))
                    have hNoUOp3 :
                        ∀ op w x y, f ≠ Term.UOp3 op w x y := by
                      intro op w x y hEq
                      exact hHeadSpecial
                        (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨op, w, x, y, hEq⟩))))
                    have hNoDtSel :
                        ∀ s d i j, f ≠ Term.DtSel s d i j := by
                      intro s d i j hEq
                      exact hHeadSpecial
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨s, d, i, j, hEq⟩)))))
                    have hHeadNotStuck : f ≠ Term.Stuck := by
                      intro hEq
                      exact hHeadSpecial
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hEq)))))
                    have hNotBinder :
                        ∀ q v vs,
                          f ≠
                            Term.Apply q
                              (Term.Apply (Term.Apply Term.__eo_List_cons v)
                                vs) := by
                      intro q v vs hEq
                      exact hHeadNotApply q
                        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                        hEq
                    have hSmtConds :=
                      generic_atom_head_smt_apply_conditions
                        f a hHeadNotApply hHeadNotVar hNoUOp hNoUOp1
                        hNoUOp2 hNoUOp3
                        (fun s d i hEq => hHeadDtCons ⟨s, d, i, hEq⟩)
                        hNoDtSel hHeadNotStuck
                        (fun i U hEq => hHeadUConst ⟨i, U, hEq⟩)
                    exact
                      substitute_simul_apply_atom_generic_preserves_type_and_translation_of_typeof_ne_stuck
                        f a xs ts bvs hXsEnv hBvsEnv hTs hEntryTypes
                        hHeadNotApply hHeadNotVar hHeadNotStuck hNotBinder
                        hSmtConds.1 hSmtConds.2.1 hSmtConds.2.2 hFTrans
                        (fun hATrans hATy =>
                          hRec
                            (G := a) (xs' := xs) (ts' := ts) (bvs' := bvs)
                            (by
                              simp
                              omega)
                            hXsEnv hBvsEnv hATrans hTs hActuals hATy)
                        hTy
      · by_cases hVar : ∃ name T, F = Term.Var name T
        · rcases hVar with ⟨name, T, rfl⟩
          exact ⟨
            SubstituteSupport.substitute_simul_rec_var_any_typeof_eq
              name T xs ts bvs hXsEnv hBvsEnv hTs hEntryTypes hFTrans,
            substitute_simul_var_any_has_smt_translation_of_typeof_ne_stuck
              name T xs ts bvs hXsEnv hBvsEnv hFTrans hTs hTy⟩
        · by_cases hStuck : F = Term.Stuck
          · subst F
            exact False.elim
              ((RuleProofs.term_ne_stuck_of_has_smt_translation Term.Stuck hFTrans) rfl)
          · have hNotApply : ∀ f a, F ≠ Term.Apply f a := by
              intro f a hEq
              exact hApply ⟨f, a, hEq⟩
            have hNotVar : ∀ name T, F ≠ Term.Var name T := by
              intro name T hEq
              exact hVar ⟨name, T, hEq⟩
            exact ⟨
              SubstituteSupport.substitute_simul_rec_atom_typeof_eq_of_typeof_ne_stuck
                _ xs ts bvs hXsEnv hBvsEnv hTs
                hNotApply hNotVar hStuck
                hTy,
              substitute_simul_atom_has_smt_translation_of_typeof_ne_stuck
                _ xs ts bvs hXsEnv hBvsEnv hTs
                hNotApply hNotVar hStuck
                hFTrans hTy⟩

/--
Combined substitution preservation under an arbitrary bound-variable
accumulator.
-/
theorem substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck
    (F xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hFTrans : RuleProofs.eo_has_smt_translation F)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy : __eo_typeof (substResult F xs ts bvs) ≠ Term.Stuck) :
    __eo_typeof (substResult F xs ts bvs) = __eo_typeof F ∧
      RuleProofs.eo_has_smt_translation (substResult F xs ts bvs) :=
  substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck_lt
    (sizeOf F + 1) F xs ts bvs
    (by omega) hXsEnv hBvsEnv hFTrans hTs hActuals hTy

/--
Instantiate-facing combined preservation for a Boolean-typed substitution result.
-/
theorem substitute_simul_preserves_type_and_translation_of_typeof_bool
    (F xs ts : Term)
    (hForall : RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.forall) xs) F))
    (hTs : EoListAllHaveSmtTranslation ts)
    (hActuals : SubstActualsHaveSmtTypes xs ts)
    (hTy :
      __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
        Term.Bool) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) =
      __eo_typeof F ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false) F xs ts Term.__eo_List_nil) := by
  have hBodyTrans :
      RuleProofs.eo_has_smt_translation F :=
    forall_body_has_smt_translation_of_has_smt_translation xs F hForall
  rcases forall_binders_env_of_has_smt_translation xs F hForall with
    ⟨_binderVars, hXsEnv⟩
  exact
    substitute_simul_preserves_type_and_translation_of_typeof_ne_stuck
      F xs ts Term.__eo_List_nil
      (EoVarEnvPerm.of_exact hXsEnv)
      (EoVarEnvPerm.of_exact EoVarEnv.nil)
      hBodyTrans hTs hActuals
      (by
        intro hStuck
        rw [hStuck] at hTy
        cases hTy)

end SubstitutePreservationSupport
