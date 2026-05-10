import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Translation.Apply
import Cpc.Proofs.Translation.Inversions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace CongSupport

/--
Typing for the generated EO implementation of `cong`.

The proof obligation is intentionally isolated here because it is the semantic
heart of the rule: `__eo_prog_cong` reverses the premise conjunction and walks
the application spine, so this lemma packages the corresponding type argument
for the generated program.
-/
axiom typed___eo_prog_cong_impl (t E : Term) :
  RuleProofs.eo_has_smt_translation t ->
  RuleProofs.eo_has_bool_type E ->
  __eo_prog_cong t (Proof.pf E) ≠ Term.Stuck ->
  RuleProofs.eo_has_bool_type (__eo_prog_cong t (Proof.pf E))

/--
Correctness for the generated EO implementation of `cong`.

This is the semantic core of the rule.  If the premise conjunction represented
by `E` is true, then the generated equality between the original application
spine and the rewritten spine is true.
-/
axiom facts___eo_prog_cong_impl
    (M : SmtModel) (hM : model_total_typed M) (t E : Term) :
  RuleProofs.eo_has_smt_translation t ->
  eo_interprets M E true ->
  __eo_prog_cong t (Proof.pf E) ≠ Term.Stuck ->
  eo_interprets M (__eo_prog_cong t (Proof.pf E)) true

theorem smt_value_rel_model_eval_apply_of_rel
    (M : SmtModel) (hM : model_total_typed M)
    (f g x y : SmtTerm)
    (hAppNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hFy : __smtx_typeof f = __smtx_typeof g)
    (hXy : __smtx_typeof x = __smtx_typeof y)
    (hFRel : RuleProofs.smt_value_rel (__smtx_model_eval M f) (__smtx_model_eval M g))
    (hXRel : RuleProofs.smt_value_rel (__smtx_model_eval M x) (__smtx_model_eval M y)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x))
      (__smtx_model_eval_apply (__smtx_model_eval M g) (__smtx_model_eval M y)) := by
  rcases typeof_apply_non_none_cases hAppNN with
    ⟨A, B, hHead, hX, hA, _hB⟩
  have hFNN : term_has_non_none_type f := by
    unfold term_has_non_none_type
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hGNN : term_has_non_none_type g := by
    unfold term_has_non_none_type
    rw [← hFy]
    exact hFNN
  have hXNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hX]
    exact hA
  have hYNN : term_has_non_none_type y := by
    unfold term_has_non_none_type
    rw [← hXy]
    exact hXNN
  have hFPres :
      __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f :=
    smt_model_eval_preserves_type_of_non_none M hM f hFNN
  have hGPres :
      __smtx_typeof_value (__smtx_model_eval M g) = __smtx_typeof g :=
    smt_model_eval_preserves_type_of_non_none M hM g hGNN
  have hXPres :
      __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x :=
    smt_model_eval_preserves_type_of_non_none M hM x hXNN
  have hYPres :
      __smtx_typeof_value (__smtx_model_eval M y) = __smtx_typeof y :=
    smt_model_eval_preserves_type_of_non_none M hM y hYNN
  have hFNeReg : __smtx_typeof f ≠ SmtType.RegLan := by
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hArgField :
      TranslationProofs.smtx_type_field_wf_rec A native_reflist_nil := by
    have hDomains :=
      TranslationProofs.smtx_term_fun_like_domains_wf_of_non_none f hFNN
    exact TranslationProofs.smtx_type_fun_like_arg_field_wf_of_domains_wf hDomains hHead
  have hANeReg : A ≠ SmtType.RegLan :=
    TranslationProofs.smtx_type_field_wf_rec_ne_reglan hArgField
  have hFEq : __smtx_model_eval M f = __smtx_model_eval M g :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      hFPres (by simpa [hFy] using hGPres) hFNeReg hFRel
  have hXEq : __smtx_model_eval M x = __smtx_model_eval M y :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      (by simpa [hX] using hXPres)
      (by
        rw [← hXy, hX] at hYPres
        exact hYPres)
      hANeReg hXRel
  rw [hFEq, hXEq]
  exact RuleProofs.smt_value_rel_refl _

end CongSupport
