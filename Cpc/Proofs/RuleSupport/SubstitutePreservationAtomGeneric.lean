import Cpc.Proofs.RuleSupport.SubstitutePreservationClassifiers
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

end SubstitutePreservationSupport
