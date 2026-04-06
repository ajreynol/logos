import CpcMicro.Proofs.Translation.Datatypes
import CpcMicro.Proofs.TypePreservation.CoreArith

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

theorem smtx_typeof_translation_not_of_non_none
    (x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply Term.not x)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hArg : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
    cases h : __smtx_typeof (__eo_to_smt x) <;>
      simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, h] at hNonNone
    simp
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArg]

theorem smtx_typeof_translation_or_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.or x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.or (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl hApplyNN
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]

theorem smtx_typeof_translation_and_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.and x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.and (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl hApplyNN
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]

theorem smtx_typeof_translation_imp_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.imp x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.imp (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl hApplyNN
  simp [__smtx_typeof, smt_lit_ite, smt_lit_Teq, hArgs.1, hArgs.2]

theorem smtx_typeof_translation_eq_of_non_none
    (x y : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.eq x) y)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.eq x) y)) = SmtType.Bool := by
  intro hNonNone
  rw [__eo_to_smt.eq_def] at hNonNone ⊢
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x)) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hNonNone
  simpa using
    eq_term_typeof_of_non_none (t1 := __eo_to_smt x) (t2 := __eo_to_smt y) hApplyNN

end TranslationProofs
