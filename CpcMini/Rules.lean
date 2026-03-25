import CpcMini.Spec
import CpcMini.SmtModelLemmas

open Eo
open Smtm

namespace RuleProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

theorem eo_interprets_iff_smt_interprets (M : SmtModel) (t : Term) (b : Bool) :
  eo_interprets M t b ↔ smt_interprets M (__eo_to_smt t) b := by
  constructor
  · intro h
    rcases h with ⟨s, hs, hInterp⟩
    cases hs
    simpa using hInterp
  · intro h
    exact ⟨__eo_to_smt t, eo_is_obj.intro t, h⟩

theorem eo_interprets_true (M : SmtModel) :
  eo_interprets M (Term.Boolean true) true := by
  rw [eo_interprets_iff_smt_interprets]
  exact smt_interprets.intro_true M (__eo_to_smt (Term.Boolean true)) rfl rfl

def eo_has_smt_translation (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

def eo_has_bool_type (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Bool

/-
Bridge from the checker-facing `__eo_typeof` guard to trusted SMT typing.

The intended use is: if a Eunoia term translates to some non-`None` SMT term
and the checker says its type is `Bool`, then the SMT translation should also
have SMT type `Bool`.

For now this is an assumed property of the future real `__eo_typeof`.
-/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  s ≠ SmtTerm.None ->
  __eo_typeof t = Term.Bool ->
  __smtx_typeof s = SmtType.Bool := by
  sorry

theorem eo_typeof_bool_implies_has_bool_type
    (t : Term) :
  eo_has_smt_translation t ->
  __eo_typeof t = Term.Bool ->
  eo_has_bool_type t := by
  intro hTrans hTy
  have hNotNone : __eo_to_smt t ≠ SmtTerm.None := by
    intro hNone
    apply hTrans
    simp [hNone, __smtx_typeof]
  exact eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t (__eo_to_smt t) rfl hNotNone hTy

theorem eo_interprets_of_bool_eval
    (M : SmtModel) (t : Term) (b : Bool) :
  eo_has_bool_type t ->
  __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b ->
  eo_interprets M t b := by
  intro hTy hEval
  rw [eo_interprets_iff_smt_interprets]
  cases b with
  | false =>
      exact smt_interprets.intro_false M (__eo_to_smt t) hTy hEval
  | true =>
      exact smt_interprets.intro_true M (__eo_to_smt t) hTy hEval

theorem eo_eval_is_boolean_of_has_bool_type
    (M : SmtModel) (hM : smt_model_well_typed M) (t : Term) :
  eo_has_bool_type t ->
  ∃ b : Bool, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b := by
  intro hTy
  exact smt_model_eval_bool_is_boolean M hM (__eo_to_smt t) hTy

theorem eo_interprets_true_not_false (M : SmtModel) (t : Term) :
  eo_interprets M t true -> ¬ eo_interprets M t false := by
  intro hTrue hFalse
  rw [eo_interprets_iff_smt_interprets] at hTrue hFalse
  cases hTrue with
  | intro_true hTyTrue hEvalTrue =>
      cases hFalse with
      | intro_false hTyFalse hEvalFalse =>
          rw [hEvalTrue] at hEvalFalse
          cases hEvalFalse

theorem eo_interprets_and_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) true ->
  eo_interprets M A true := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  cases h with
  | intro_true hty hEval =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        by_cases hA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool
        · exact hA
        · have : False := by
            simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite, hA] at hty
          exact False.elim this
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __eo_to_smt, __smtx_model_eval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.smt_lit_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

theorem eo_interprets_and_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) true ->
  eo_interprets M B true := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  cases h with
  | intro_true hty hEval =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        by_cases hB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool
        · exact hB
        · have : False := by
            simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite, hB] at hty
          exact False.elim this
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __eo_to_smt, __smtx_model_eval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.smt_lit_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

theorem eo_interprets_and_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply Term.and A) B) true := by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · simp [__eo_to_smt, __smtx_typeof, htyA, htyB, smt_lit_Teq, smt_lit_ite]
          · simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_and, hEvalA, hEvalB,
              SmtEval.smt_lit_and]

def smt_value_rel : SmtValue -> SmtValue -> Prop
  | SmtValue.Map m1, SmtValue.Map m2 => ∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v
  | v1, v2 => v1 = v2

theorem smt_value_rel_trans (v1 v2 v3 : SmtValue) :
  smt_value_rel v1 v2 ->
  smt_value_rel v2 v3 ->
  smt_value_rel v1 v3 := by
  cases v1 <;> cases v2 <;> cases v3 <;> simp [smt_value_rel]
  case Map.Map.Map m1 m2 m3 =>
    intro h12 h23 v
    rw [h12 v, h23 v]
  all_goals
    intros
    subst_vars
    simp [smt_value_rel]

theorem smt_value_rel_iff_model_eval_eq_true (v1 v2 : SmtValue) :
  smt_value_rel v1 v2 ↔ __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true := by
  cases v1 <;> cases v2 <;>
    simp [smt_value_rel, __smtx_model_eval_eq, smt_lit_veq]

theorem smtx_typeof_eq_bool_iff (T U : SmtType) :
  __smtx_typeof_eq T U = SmtType.Bool ↔ T = U ∧ T ≠ SmtType.None := by
  unfold __smtx_typeof_eq __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · subst hT
    simp [smt_lit_ite, smt_lit_Teq]
  · by_cases hEq : T = U
    · subst hEq
      simp [smt_lit_ite, smt_lit_Teq, hT]
    · simp [smt_lit_ite, smt_lit_Teq, hEq, hT]

theorem eo_eq_operands_same_smt_type (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) true ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hEq
  rw [eo_interprets_iff_smt_interprets] at hEq
  cases hEq with
  | intro_true hTy _ =>
      simpa [__eo_to_smt, __smtx_typeof] using
        (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y))).mp hTy

theorem eo_eq_operands_same_smt_type_of_false (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) false ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hEq
  rw [eo_interprets_iff_smt_interprets] at hEq
  cases hEq with
  | intro_false hTy _ =>
      simpa [__eo_to_smt, __smtx_typeof] using
        (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y))).mp hTy

theorem eo_has_bool_type_eq_of_true_chain (M : SmtModel) (x y z : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply Term.eq y) z) true ->
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) z) := by
  intro hXY hYZ
  rcases eo_eq_operands_same_smt_type M x y hXY with ⟨hTyXY, hNonNone⟩
  rcases eo_eq_operands_same_smt_type M y z hYZ with ⟨hTyYZ, _⟩
  have hTyXZ : __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt z) := by
    rw [hTyXY, hTyYZ]
  unfold eo_has_bool_type
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt z)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt z))).mpr ⟨hTyXZ, hNonNone⟩
  simpa [__eo_to_smt, __smtx_typeof] using hEqTy

theorem eo_has_bool_type_eq_of_true (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) true ->
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) y) := by
  intro hXY
  rcases eo_eq_operands_same_smt_type M x y hXY with ⟨hTyXY, hNonNone⟩
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y))).mpr ⟨hTyXY, hNonNone⟩
  simpa [eo_has_bool_type, __eo_to_smt, __smtx_typeof] using hEqTy

theorem eo_interprets_eq_rel (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) true ->
  smt_value_rel (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hEq
  rw [smt_value_rel_iff_model_eval_eq_true]
  rw [eo_interprets_iff_smt_interprets] at hEq
  cases hEq with
  | intro_true _ hEval =>
      simpa [__eo_to_smt, __smtx_model_eval] using hEval

theorem eo_interprets_eq_of_rel (M : SmtModel) (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) y) ->
  smt_value_rel (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) ->
  eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) true := by
  intro hTy hRel
  rw [eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M (__eo_to_smt (Term.Apply (Term.Apply Term.eq x) y)) ?_ ?_
  · simpa [eo_has_bool_type] using hTy
  · have hEvalEq :
        __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean true :=
      (smt_value_rel_iff_model_eval_eq_true
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))).mp hRel
    simpa [__eo_to_smt, __smtx_model_eval] using hEvalEq

theorem eo_interprets_eq_trans (M : SmtModel) (x y z : Term) :
  eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply Term.eq y) z) true ->
  eo_interprets M (Term.Apply (Term.Apply Term.eq x) z) true := by
  intro hXY hYZ
  apply eo_interprets_eq_of_rel M x z
  · exact eo_has_bool_type_eq_of_true_chain M x y z hXY hYZ
  · exact smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z))
      (eo_interprets_eq_rel M x y hXY)
      (eo_interprets_eq_rel M y z hYZ)

theorem eo_interprets_not_of_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> eo_interprets M (Term.Apply Term.not t) true := by
  intro hFalse
  rw [eo_interprets_iff_smt_interprets] at hFalse ⊢
  cases hFalse with
  | intro_false hTy hEval =>
      refine smt_interprets.intro_true M (__eo_to_smt (Term.Apply Term.not t)) ?_ ?_
      · simp [__eo_to_smt, __smtx_typeof, hTy, smt_lit_Teq, smt_lit_ite]
      · simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_not, hEval,
          SmtEval.smt_lit_not]

theorem term_ne_stuck_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets] at h
  cases h with
  | intro_true hTy _ =>
      simp [__eo_to_smt, __smtx_typeof] at hTy

theorem term_ne_stuck_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets] at h
  cases h with
  | intro_false hTy _ =>
      simp [__eo_to_smt, __smtx_typeof] at hTy

theorem term_ne_stuck_of_has_bool_type (t : Term) :
  eo_has_bool_type t -> t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  simp [eo_has_bool_type, __eo_to_smt, __smtx_typeof] at hTy

set_option linter.unusedSimpArgs false in
theorem eo_interprets_not_true_implies_false (M : SmtModel) (t : Term) :
  eo_interprets M (Term.Apply Term.not t) true -> eo_interprets M t false := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  cases h with
  | intro_true hty hEval =>
      have htyt : __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
        simp [__eo_to_smt, __smtx_typeof, smt_lit_Teq, smt_lit_ite] at hty
        exact hty
      cases ht : __smtx_model_eval M (__eo_to_smt t) <;>
        simp [__eo_to_smt, __smtx_model_eval, __smtx_model_eval_not, ht, SmtEval.smt_lit_not] at hEval
      case Boolean b =>
        cases b <;> simp [SmtEval.smt_lit_not] at hEval
        exact smt_interprets.intro_false M (__eo_to_smt t) htyt ht

theorem smtx_typeof_eq_refl (T : SmtType) :
  T ≠ SmtType.None -> __smtx_typeof_eq T T = SmtType.Bool := by
  intro hT
  unfold __smtx_typeof_eq __smtx_typeof_guard
  simp [smt_lit_ite, smt_lit_Teq, hT]

theorem smtx_model_eval_eq_refl (v : SmtValue) :
  __smtx_model_eval_eq v v = SmtValue.Boolean true := by
  unfold __smtx_model_eval_eq
  cases v <;> simp [smt_lit_veq]

theorem correct___eo_prog_refl_of_smt_translation (M : SmtModel) (x1 : Term) :
  eo_has_smt_translation x1 ->
  eo_has_bool_type (__eo_prog_refl x1) ->
  eo_interprets M (__eo_prog_refl x1) true := by
  intro hTy _
  have hNotEqStuck : x1 ≠ Term.Stuck := by
    intro hStuck
    subst hStuck
    simp [eo_has_smt_translation, __eo_to_smt, __smtx_typeof] at hTy
  rw [eo_interprets_iff_smt_interprets]
  refine smt_interprets.intro_true M (__eo_to_smt (__eo_prog_refl x1)) ?_ ?_
  · simp [__eo_prog_refl, __eo_to_smt, __smtx_typeof]
    exact smtx_typeof_eq_refl (__smtx_typeof (__eo_to_smt x1)) hTy
  · simpa [__eo_prog_refl, hNotEqStuck, __eo_to_smt, __smtx_model_eval] using
      smtx_model_eval_eq_refl (__smtx_model_eval M (__eo_to_smt x1))

theorem correct___eo_prog_contra (M : SmtModel) (x1 x2 : Term) :
  eo_interprets M x1 true ->
  eo_interprets M x2 true ->
  eo_has_bool_type (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) ->
  eo_interprets M (__eo_prog_contra (Proof.pf x1) (Proof.pf x2)) true := by
  intro hX1True hX2True hTy
  have hProgNotStuck : __eo_prog_contra (Proof.pf x1) (Proof.pf x2) ≠ Term.Stuck := by
    intro hStuck
    simp [eo_has_bool_type, hStuck, __eo_to_smt, __smtx_typeof] at hTy
  cases x2 with
  | Apply f a =>
      cases f with
      | not =>
          by_cases hEq : x1 = a
          · subst hEq
            have hX1False : eo_interprets M x1 false :=
              eo_interprets_not_true_implies_false M x1 hX2True
            exact False.elim ((eo_interprets_true_not_false M x1 hX1True) hX1False)
          · exfalso
            have hEq' : a ≠ x1 := by
              simpa [eq_comm] using hEq
            have hx1NotStuck : x1 ≠ Term.Stuck :=
              term_ne_stuck_of_interprets_true M x1 hX1True
            have hAFalse : eo_interprets M a false :=
              eo_interprets_not_true_implies_false M a hX2True
            have hANotStuck : a ≠ Term.Stuck :=
              term_ne_stuck_of_interprets_false M a hAFalse
            have hContraStuck :
                __eo_prog_contra (Proof.pf x1) (Proof.pf (Term.Apply Term.not a)) = Term.Stuck := by
              simp [__eo_prog_contra, __eo_requires, __eo_eq, eo_lit_teq, hEq', eo_lit_ite]
            exact hProgNotStuck hContraStuck
      | _ =>
          exact False.elim (hProgNotStuck (by simp [__eo_prog_contra]))
  | _ =>
      exact False.elim (hProgNotStuck (by simp [__eo_prog_contra]))

theorem correct___eo_prog_scope
    (M : SmtModel) (hM : smt_model_well_typed M) (x1 x2 : Term) :
  (eo_interprets M x1 true -> eo_interprets M x2 true) ->
  eo_has_bool_type (__eo_prog_scope x1 (Proof.pf x2)) ->
  eo_interprets M (__eo_prog_scope x1 (Proof.pf x2)) true := by
  intro hImp hTy
  by_cases hStuck : x1 = Term.Stuck
  · subst hStuck
    simp [eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof] at hTy
  · have hTy1 : __smtx_typeof (__eo_to_smt x1) = SmtType.Bool := by
      by_cases hx1 : __smtx_typeof (__eo_to_smt x1) = SmtType.Bool
      · exact hx1
      · simp [eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof,
          smt_lit_ite, smt_lit_Teq, hx1] at hTy
    have hTy2 : __smtx_typeof (__eo_to_smt x2) = SmtType.Bool := by
      by_cases hx2 : __smtx_typeof (__eo_to_smt x2) = SmtType.Bool
      · exact hx2
      · simp [eo_has_bool_type, __eo_prog_scope, __eo_to_smt, __smtx_typeof,
          smt_lit_ite, smt_lit_Teq, hTy1, hx2] at hTy
    have hTy1' : eo_has_bool_type x1 := hTy1
    have hTy2' : eo_has_bool_type x2 := hTy2
    rcases eo_eval_is_boolean_of_has_bool_type M hM x1 hTy1' with ⟨b1, hEval1⟩
    rw [eo_interprets_iff_smt_interprets]
    refine smt_interprets.intro_true M (__eo_to_smt (__eo_prog_scope x1 (Proof.pf x2))) ?_ ?_
    · simpa [eo_has_bool_type, __eo_prog_scope, hStuck, __eo_to_smt] using hTy
    · cases b1 with
      | false =>
          rcases eo_eval_is_boolean_of_has_bool_type M hM x2 hTy2' with ⟨b2, hEval2⟩
          cases b2 <;>
            simp [__eo_prog_scope, __eo_to_smt, __smtx_model_eval, hEval1, hEval2,
              __smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
              SmtEval.smt_lit_not, SmtEval.smt_lit_or]
      | true =>
          have hX1True : eo_interprets M x1 true :=
            eo_interprets_of_bool_eval M x1 true hTy1' hEval1
          have hX2True : eo_interprets M x2 true := hImp hX1True
          rw [eo_interprets_iff_smt_interprets] at hX2True
          cases hX2True with
          | intro_true _ hEval2 =>
              simp [__eo_prog_scope, __eo_to_smt, __smtx_model_eval, hEval1, hEval2,
                __smtx_model_eval_imp, __smtx_model_eval_or, __smtx_model_eval_not,
                SmtEval.smt_lit_not, SmtEval.smt_lit_or]

theorem not_eo_interprets_prog_refl_or_true (M : SmtModel) :
  ¬ eo_interprets M (__eo_prog_refl Term.or) true := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy hEval =>
      simp [__eo_prog_refl, __eo_to_smt, __smtx_typeof, __smtx_typeof_eq,
        __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at hTy

theorem not_eo_interprets_prog_scope_num_true (M : SmtModel) :
  ¬ eo_interprets M (__eo_prog_scope (Term.Numeral 0) (Proof.pf (Term.Boolean true))) true := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy hEval =>
      simp [__eo_prog_scope, __eo_to_smt, __smtx_typeof, smt_lit_ite, smt_lit_Teq] at hTy

end RuleProofs
