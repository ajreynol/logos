import CpcMicro.Proofs.Translation.Datatypes
import CpcMicro.Proofs.Translation.Apply

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-!
This file is the staging area for the reduced `CpcMicro` EO-to-SMT translation
typing port.

Unlike full `Cpc`, the micro development here still focuses on the fragment
already used by the checker. The type translation now includes EO function
types via SMT maps, but the proof file below is still centered on the direct
boolean/equality fragment that already lines up cleanly:

1. Shape lemmas for key translated type forms.
2. Fully translated boolean/equality applications.
-/

/-- Derives `eo_typeof_eq_self` from `not_stuck`. -/
private theorem eo_typeof_eq_self_of_not_stuck
    (A : Term)
    (hA : A ≠ Term.Stuck) :
    __eo_typeof_eq A A = Term.Bool := by
  cases A <;>
    try simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_teq, native_ite, native_not,
      SmtEval.native_not]
  exact False.elim (hA rfl)

/-- Derives `eo_typeof_bool` from `smt_bool`. -/
private theorem eo_typeof_bool_of_smt_bool
    {t : Term}
    (hRec : __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (hBool : __smtx_typeof (__eo_to_smt t) = SmtType.Bool) :
    __eo_typeof t = Term.Bool := by
  apply eo_to_smt_type_eq_of_non_none
  · calc
      __eo_to_smt_type (__eo_typeof t)
          = __smtx_typeof (__eo_to_smt t) := by
              symm
              exact hRec
      _ = SmtType.Bool := hBool
      _ = __eo_to_smt_type Term.Bool := by
              rfl
  · calc
      __eo_to_smt_type (__eo_typeof t)
          = __smtx_typeof (__eo_to_smt t) := by
              symm
              exact hRec
      _ = SmtType.Bool := hBool
      _ ≠ SmtType.None := by
              simp

/-- Computes EO typing for generic double applications. -/
private theorem eo_typeof_double_apply_generic
    (g y x : Term)
    (hFun : g ≠ Term.FunType)
    (hOr : g ≠ Term.or)
    (hAnd : g ≠ Term.and)
    (hImp : g ≠ Term.imp)
    (hEq : g ≠ Term.eq) :
    __eo_typeof (Term.Apply (Term.Apply g y) x) =
      __eo_typeof_apply (__eo_typeof (Term.Apply g y)) (__eo_typeof x) := by
  cases g <;> try rfl
  case FunType =>
      exact False.elim (hFun rfl)
  case or =>
      exact False.elim (hOr rfl)
  case and =>
      exact False.elim (hAnd rfl)
  case imp =>
      exact False.elim (hImp rfl)
  case eq =>
      exact False.elim (hEq rfl)

/-- Computes EO typing for generic single applications. -/
private theorem eo_typeof_single_apply_generic
    (f x : Term)
    (hApply : ∀ g y, f ≠ Term.Apply g y)
    (hBitVec : f ≠ Term.BitVec)
    (hSeq : f ≠ Term.Seq)
    (hListCons : f ≠ Term.__eo_List_cons)
    (hNot : f ≠ Term.not) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  cases f <;> try rfl
  case Apply g y =>
      exact False.elim (hApply g y rfl)
  case BitVec =>
      exact False.elim (hBitVec rfl)
  case Seq =>
      exact False.elim (hSeq rfl)
  case __eo_List_cons =>
      exact False.elim (hListCons rfl)
  case not =>
      exact False.elim (hNot rfl)

/-- Computes SMT translation for generic double EO applications. -/
private theorem eo_to_smt_double_apply_generic
    (g y x : Term)
    (hOr : g ≠ Term.or)
    (hAnd : g ≠ Term.and)
    (hImp : g ≠ Term.imp)
    (hEq : g ≠ Term.eq) :
    __eo_to_smt (Term.Apply (Term.Apply g y) x) =
      SmtTerm.Apply (__eo_to_smt (Term.Apply g y)) (__eo_to_smt x) := by
  cases g <;> try rfl
  case or =>
      exact False.elim (hOr rfl)
  case and =>
      exact False.elim (hAnd rfl)
  case imp =>
      exact False.elim (hImp rfl)
  case eq =>
      exact False.elim (hEq rfl)

/-- Computes SMT translation for generic single EO applications. -/
private theorem eo_to_smt_single_apply_generic
    (f x : Term)
    (hApply : ∀ g y, f ≠ Term.Apply g y)
    (hNot : f ≠ Term.not) :
    __eo_to_smt (Term.Apply f x) =
      SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x) := by
  cases f <;> try rfl
  case Apply g y =>
      exact False.elim (hApply g y rfl)
  case not =>
      exact False.elim (hNot rfl)

/-- Shows that translated SMT terms carry the type predicted by EO typing when the translation is defined. -/
private theorem eo_to_smt_typeof_matches_translation :
    ∀ (t : Term),
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t)
  | Term.__eo_pf p, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Int, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Real, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.BitVec, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Char, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Seq, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.__eo_List, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.__eo_List_nil, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.__eo_List_cons, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Bool, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Boolean b, _ => by
      simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof]
  | Term.Numeral n, _ => by
      simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof, __native_type_Numeral]
  | Term.Rational r, _ => by
      simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof, __native_type_Rational]
  | Term.String s, _ => by
      simp [__eo_to_smt.eq_def, __smtx_typeof, __eo_typeof, __native_type_String,
        __eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]
  | Term.Binary w n, hNN => by
      have hWidth : native_zleq 0 w = true := by
        by_cases hw : native_zleq 0 w = true
        · exact hw
        · exfalso
          apply hNN
          simp [__eo_to_smt.eq_def, native_ite, SmtEval.native_and, hw]
      have hSmt := smtx_typeof_binary_of_non_none w n hNN
      have hEo :
          __eo_to_smt_type (__eo_typeof (Term.Binary w n)) =
            SmtType.BitVec (native_int_to_nat w) := by
        simp [__eo_typeof, __native_type_Binary, __eo_mk_apply, __eo_len,
          __eo_to_smt_type, native_ite, hWidth]
      simpa [__eo_to_smt.eq_def] using hSmt.trans hEo.symm
  | Term.Type, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Stuck, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.FunType, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Var name T, hNN => by
      cases name with
      | String s =>
          simpa [__eo_to_smt.eq_def, __eo_typeof] using
            smtx_typeof_var_of_non_none s (__eo_to_smt_type T) hNN
      | _ =>
          exact False.elim (hNN (by simp [__eo_to_smt.eq_def, __smtx_typeof]))
  | Term.USort i, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.UConst i T, hNN => by
      simpa [__eo_to_smt.eq_def, __eo_typeof] using
        smtx_typeof_uconst_of_non_none (native_uconst_id i) (__eo_to_smt_type T) hNN
  | Term.not, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.or, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.and, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.imp, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.eq, hNN => by
      simp [__eo_to_smt.eq_def, __smtx_typeof] at hNN
  | Term.Apply f x, hNN => by
      by_cases hApply : ∃ g y, f = Term.Apply g y
      · rcases hApply with ⟨g, y, rfl⟩
        by_cases hFun : g = Term.FunType
        · subst hFun
          have hTranslate :
              __eo_to_smt (Term.Apply (Term.Apply Term.FunType y) x) =
                SmtTerm.Apply (__eo_to_smt (Term.Apply Term.FunType y)) (__eo_to_smt x) := by
            rw [__eo_to_smt.eq_def]
          have hHeadTranslate :
              __eo_to_smt (Term.Apply Term.FunType y) =
                SmtTerm.Apply (__eo_to_smt Term.FunType) (__eo_to_smt y) := by
            exact eo_to_smt_single_apply_generic Term.FunType y
              (by intro g z h; cases h)
              (by intro h; cases h)
          have hHeadNone : __eo_to_smt Term.FunType = SmtTerm.None := by
            rw [__eo_to_smt.eq_def]
          have hNN' := hNN
          rw [hTranslate, hHeadTranslate, hHeadNone] at hNN'
          simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
        · by_cases hOr : g = Term.or
          · subst hOr
            have hTranslate :
                __eo_to_smt (Term.Apply (Term.Apply Term.or y) x) =
                  SmtTerm.or (__eo_to_smt y) (__eo_to_smt x) := by
              rw [__eo_to_smt.eq_def]
            have hApplyNN :
                term_has_non_none_type
                  (SmtTerm.or (__eo_to_smt y) (__eo_to_smt x)) := by
              unfold term_has_non_none_type
              simpa [hTranslate] using hNN
            have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or) rfl hApplyNN
            have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
              rw [hArgs.1]
              simp
            have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
              rw [hArgs.2]
              simp
            have hIy := eo_to_smt_typeof_matches_translation y h1NN
            have hIx := eo_to_smt_typeof_matches_translation x h2NN
            have hTyY : __eo_typeof y = Term.Bool :=
              eo_typeof_bool_of_smt_bool hIy hArgs.1
            have hTyX : __eo_typeof x = Term.Bool :=
              eo_typeof_bool_of_smt_bool hIx hArgs.2
            have hTy :
                __eo_typeof (Term.Apply (Term.Apply Term.or y) x) = Term.Bool := by
              simp [__eo_typeof, __eo_typeof_or, hTyY, hTyX]
            rw [hTy]
            exact smtx_typeof_translation_or_of_non_none y x hNN
          · by_cases hAnd : g = Term.and
            · subst hAnd
              have hTranslate :
                  __eo_to_smt (Term.Apply (Term.Apply Term.and y) x) =
                    SmtTerm.and (__eo_to_smt y) (__eo_to_smt x) := by
                rw [__eo_to_smt.eq_def]
              have hApplyNN :
                  term_has_non_none_type
                    (SmtTerm.and (__eo_to_smt y) (__eo_to_smt x)) := by
                unfold term_has_non_none_type
                simpa [hTranslate] using hNN
              have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and) rfl hApplyNN
              have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                rw [hArgs.1]
                simp
              have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                rw [hArgs.2]
                simp
              have hIy := eo_to_smt_typeof_matches_translation y h1NN
              have hIx := eo_to_smt_typeof_matches_translation x h2NN
              have hTyY : __eo_typeof y = Term.Bool :=
                eo_typeof_bool_of_smt_bool hIy hArgs.1
              have hTyX : __eo_typeof x = Term.Bool :=
                eo_typeof_bool_of_smt_bool hIx hArgs.2
              have hTy :
                  __eo_typeof (Term.Apply (Term.Apply Term.and y) x) = Term.Bool := by
                simp [__eo_typeof, __eo_typeof_or, hTyY, hTyX]
              rw [hTy]
              exact smtx_typeof_translation_and_of_non_none y x hNN
            · by_cases hImp : g = Term.imp
              · subst hImp
                have hTranslate :
                    __eo_to_smt (Term.Apply (Term.Apply Term.imp y) x) =
                      SmtTerm.imp (__eo_to_smt y) (__eo_to_smt x) := by
                  rw [__eo_to_smt.eq_def]
                have hApplyNN :
                    term_has_non_none_type
                      (SmtTerm.imp (__eo_to_smt y) (__eo_to_smt x)) := by
                  unfold term_has_non_none_type
                  simpa [hTranslate] using hNN
                have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.imp) rfl hApplyNN
                have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
                  rw [hArgs.1]
                  simp
                have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                  rw [hArgs.2]
                  simp
                have hIy := eo_to_smt_typeof_matches_translation y h1NN
                have hIx := eo_to_smt_typeof_matches_translation x h2NN
                have hTyY : __eo_typeof y = Term.Bool :=
                  eo_typeof_bool_of_smt_bool hIy hArgs.1
                have hTyX : __eo_typeof x = Term.Bool :=
                  eo_typeof_bool_of_smt_bool hIx hArgs.2
                have hTy :
                    __eo_typeof (Term.Apply (Term.Apply Term.imp y) x) = Term.Bool := by
                  simp [__eo_typeof, __eo_typeof_or, hTyY, hTyX]
                rw [hTy]
                exact smtx_typeof_translation_imp_of_non_none y x hNN
              · by_cases hEq : g = Term.eq
                · subst hEq
                  have hTranslate :
                      __eo_to_smt (Term.Apply (Term.Apply Term.eq y) x) =
                        SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt y)) (__eo_to_smt x) := by
                    rw [__eo_to_smt.eq_def]
                  have hNN' := hNN
                  rw [hTranslate] at hNN'
                  have hEqNN :
                      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt y)) (__smtx_typeof (__eo_to_smt x)) ≠
                        SmtType.None := by
                    simpa [__smtx_typeof] using hNN'
                  have hArgs := smtx_typeof_eq_non_none hEqNN
                  have h1NN : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := hArgs.2
                  have h2NN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                    intro hNone
                    apply hArgs.2
                    rw [hArgs.1, hNone]
                  have hIy := eo_to_smt_typeof_matches_translation y h1NN
                  have hIx := eo_to_smt_typeof_matches_translation x h2NN
                  have hTyEq :
                      __eo_to_smt_type (__eo_typeof y) = __eo_to_smt_type (__eo_typeof x) := by
                    rw [← hIy, ← hIx, hArgs.1]
                  have hTyYEqTyX : __eo_typeof y = __eo_typeof x := by
                    exact eo_to_smt_type_eq_of_non_none hTyEq (by rwa [← hIy])
                  have hTyYNN : __eo_to_smt_type (__eo_typeof y) ≠ SmtType.None := by
                    rwa [← hIy]
                  have hTyYNotStuck : __eo_typeof y ≠ Term.Stuck := by
                    intro hStuck
                    apply hTyYNN
                    simp [hStuck, __eo_to_smt_type]
                  have hTy :
                      __eo_typeof (Term.Apply (Term.Apply Term.eq y) x) = Term.Bool := by
                    change __eo_typeof_eq (__eo_typeof y) (__eo_typeof x) = Term.Bool
                    rw [← hTyYEqTyX]
                    exact eo_typeof_eq_self_of_not_stuck (__eo_typeof y) hTyYNotStuck
                  rw [hTy]
                  exact smtx_typeof_translation_eq_of_non_none y x hNN
                · exact eo_to_smt_typeof_matches_translation_apply (Term.Apply g y) x
                    (eo_to_smt_typeof_matches_translation (Term.Apply g y))
                    (eo_to_smt_typeof_matches_translation x)
                    (eo_to_smt_double_apply_generic g y x hOr hAnd hImp hEq)
                    (eo_typeof_double_apply_generic g y x hFun hOr hAnd hImp hEq)
                    hNN
      · have hHeadApply : ∀ g y, f ≠ Term.Apply g y := by
          intro g y hEq
          exact hApply ⟨g, y, hEq⟩
        by_cases hBitVec : f = Term.BitVec
        · subst hBitVec
          have hTranslate :
              __eo_to_smt (Term.Apply Term.BitVec x) =
                SmtTerm.Apply (__eo_to_smt Term.BitVec) (__eo_to_smt x) := by
            exact eo_to_smt_single_apply_generic Term.BitVec x
              (by intro g y h; cases h)
              (by intro h; cases h)
          have hHeadNone : __eo_to_smt Term.BitVec = SmtTerm.None := by
            rw [__eo_to_smt.eq_def]
          have hNN' := hNN
          rw [hTranslate, hHeadNone] at hNN'
          simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
        · by_cases hSeq : f = Term.Seq
          · subst hSeq
            have hTranslate :
                __eo_to_smt (Term.Apply Term.Seq x) =
                  SmtTerm.Apply (__eo_to_smt Term.Seq) (__eo_to_smt x) := by
              exact eo_to_smt_single_apply_generic Term.Seq x
                (by intro g y h; cases h)
                (by intro h; cases h)
            have hHeadNone : __eo_to_smt Term.Seq = SmtTerm.None := by
              rw [__eo_to_smt.eq_def]
            have hNN' := hNN
            rw [hTranslate, hHeadNone] at hNN'
            simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
          · by_cases hListCons : f = Term.__eo_List_cons
            · subst hListCons
              have hTranslate :
                  __eo_to_smt (Term.Apply Term.__eo_List_cons x) =
                    SmtTerm.Apply (__eo_to_smt Term.__eo_List_cons) (__eo_to_smt x) := by
                exact eo_to_smt_single_apply_generic Term.__eo_List_cons x
                  (by intro g y h; cases h)
                  (by intro h; cases h)
              have hHeadNone : __eo_to_smt Term.__eo_List_cons = SmtTerm.None := by
                rw [__eo_to_smt.eq_def]
              have hNN' := hNN
              rw [hTranslate, hHeadNone] at hNN'
              simp [__smtx_typeof, __smtx_typeof_apply] at hNN'
            · by_cases hNot : f = Term.not
              · subst hNot
                have hTranslate :
                    __eo_to_smt (Term.Apply Term.not x) =
                      SmtTerm.not (__eo_to_smt x) := by
                  rw [__eo_to_smt.eq_def]
                have hArgSmtTy : __smtx_typeof (__eo_to_smt x) = SmtType.Bool := by
                  have hNN' := hNN
                  rw [hTranslate] at hNN'
                  cases h : __smtx_typeof (__eo_to_smt x) <;>
                    simp [__smtx_typeof, native_ite, native_Teq, h] at hNN'
                  simp
                have hArgNN : __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
                  rw [hArgSmtTy]
                  simp
                have hIx := eo_to_smt_typeof_matches_translation x hArgNN
                have hTyX : __eo_typeof x = Term.Bool :=
                  eo_typeof_bool_of_smt_bool hIx hArgSmtTy
                have hTy :
                    __eo_typeof (Term.Apply Term.not x) = Term.Bool := by
                  simp [__eo_typeof, __eo_typeof_not, hTyX]
                rw [hTy]
                exact smtx_typeof_translation_not_of_non_none x hNN
              · exact eo_to_smt_typeof_matches_translation_apply f x
                  (eo_to_smt_typeof_matches_translation f)
                  (eo_to_smt_typeof_matches_translation x)
                  (eo_to_smt_single_apply_generic f x hHeadApply hNot)
                  (eo_typeof_single_apply_generic f x hHeadApply hBitVec hSeq hListCons hNot)
                  hNN
termination_by t _ => sizeOf t
decreasing_by
  all_goals
    subst_vars
    simp_wf
  all_goals
    omega

/-- Transfers EO typing information to the translated SMT term when the translation is defined. -/
theorem eo_to_smt_well_typed_and_typeof_implies_smt_type
    (t T : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = T ->
  __smtx_typeof s = __eo_to_smt_type T := by
  intro hs hNN hTy
  subst s T
  exact eo_to_smt_typeof_matches_translation t hNN

end TranslationProofs
