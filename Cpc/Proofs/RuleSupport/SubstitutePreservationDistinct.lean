import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport
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

theorem substitute_simul_distinct_preserves_type_and_translation
    (a xs ts bvs : Term)
    {xsVars bvsVars : List EoVarKey}
    (hXsEnv : EoVarEnvPerm xs xsVars)
    (hBvsEnv : EoVarEnvPerm bvs bvsVars)
    (hTs : EoListAllHaveSmtTranslation ts)
    (hFTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply (Term.UOp UserOp.distinct) a))
    (hTypedListSmtType :
      ∀ t,
        sizeOf t < sizeOf a ->
        RuleProofs.eo_has_smt_translation t ->
        __eo_typeof t ≠ Term.Stuck ->
          __smtx_typeof
              (__eo_to_smt
                (__substitute_simul_rec (Term.Boolean false) t xs ts bvs)) =
            __smtx_typeof (__eo_to_smt t)) :
    __eo_typeof
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp UserOp.distinct) a) xs ts bvs) =
      __eo_typeof (Term.Apply (Term.UOp UserOp.distinct) a) ∧
      RuleProofs.eo_has_smt_translation
        (__substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp UserOp.distinct) a) xs ts bvs) := by
  have hElemNN :
      __eo_to_smt_typed_list_elem_type a ≠ SmtType.None :=
    TypedListSubstitutionSupport.typed_list_elem_type_non_none_of_distinct_has_smt_translation
      hFTrans
  have hElemSubNN :
      __eo_to_smt_typed_list_elem_type
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) ≠
        SmtType.None :=
    substitute_simul_rec_typed_list_elem_type_non_none
      a xs ts bvs hXsEnv hBvsEnv hTs hTypedListSmtType hElemNN
  have hHeadSub :
      __substitute_simul_rec (Term.Boolean false)
          (Term.UOp UserOp.distinct) xs ts bvs =
        Term.UOp UserOp.distinct :=
    SubstituteSupport.substitute_simul_rec_uop_eq_self
      UserOp.distinct xs ts bvs hXsEnv hBvsEnv hTs
  have hArgSubNe :
      __substitute_simul_rec (Term.Boolean false) a xs ts bvs ≠
        Term.Stuck :=
    typed_list_elem_type_non_none_not_stuck hElemSubNN
  have hSubEq :
      __substitute_simul_rec (Term.Boolean false)
          (Term.Apply (Term.UOp UserOp.distinct) a) xs ts bvs =
        Term.Apply (Term.UOp UserOp.distinct)
          (__substitute_simul_rec (Term.Boolean false) a xs ts bvs) := by
    have hisr : (Term.Boolean false : Term) ≠ Term.Stuck := by decide
    have hxs : xs ≠ Term.Stuck := hXsEnv.ne_stuck
    have hts : ts ≠ Term.Stuck :=
      SubstituteSupport.eoListAllHaveSmtTranslation_ne_stuck hTs
    have hbvs : bvs ≠ Term.Stuck := hBvsEnv.ne_stuck
    rw [
      SubstituteSupport.substitute_simul_rec_apply
        (Term.Boolean false) (Term.UOp UserOp.distinct) a xs ts bvs
        hisr hxs hts hbvs
        (by intro q v vs hEq; cases hEq)]
    rw [hHeadSub]
    cases hArg :
        __substitute_simul_rec (Term.Boolean false) a xs ts bvs <;>
      simp [__eo_mk_apply] at hArgSubNe ⊢
    · exact False.elim (hArgSubNe hArg)
  refine ⟨?_, ?_⟩
  · rw [hSubEq]
    rw [
      eo_typeof_distinct_eq_bool_of_elem_type_non_none
        (__substitute_simul_rec (Term.Boolean false) a xs ts bvs)
        hElemSubNN]
    rw [eo_typeof_distinct_eq_bool_of_elem_type_non_none a hElemNN]
  · rw [hSubEq]
    exact
      eo_has_smt_translation_distinct_of_elem_type_non_none
        (__substitute_simul_rec (Term.Boolean false) a xs ts bvs)
        hElemSubNN

end SubstitutePreservationSupport
