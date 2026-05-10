import Cpc.Proofs.RuleSupport.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rfl

theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rfl

theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply Term.not t) = SmtTerm.not (__eo_to_smt t) := by
  rfl

theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

theorem eo_to_smt_select_eq (a i : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.select a) i) =
      SmtTerm.select (__eo_to_smt a) (__eo_to_smt i) := by
  rfl

theorem eo_to_smt_store_eq (a i e : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e) =
      SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e) := by
  rfl

theorem eo_to_smt_type_array_of_non_none (A B : Term)
    (h : __eo_to_smt_type (Term.Apply (Term.Apply Term.Array A) B) ≠ SmtType.None) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.Array A) B) =
      SmtType.Map (__eo_to_smt_type A) (__eo_to_smt_type B) := by
  cases hA : __eo_to_smt_type A <;> cases hB : __eo_to_smt_type B <;>
    simp [TranslationProofs.eo_to_smt_type_array, __smtx_typeof_guard,
      native_ite, native_Teq, hA, hB] at h ⊢

theorem eo_typeof_eq_bool_operands_not_stuck (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · exact ⟨hA, hB⟩

theorem eo_typeof_eq_bool_operands_eq (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
    y = x := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg'
  exact eq_of_eo_eq_true x y hProg'.1

theorem eqs_of_requires_and_eq_true_not_stuck (x1 y1 x2 y2 B : Term) :
    __eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
      (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd : __eo_and (__eo_eq x1 x2) (__eo_eq y1 y2) = Term.Boolean true := hProg'.1
  have hBoth :
      __eo_eq x1 x2 = Term.Boolean true ∧ __eo_eq y1 y2 = Term.Boolean true := by
    have eq_stuck_or_bool :
        ∀ a b : Term, __eo_eq a b = Term.Stuck ∨
          ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
      intro a b
      by_cases ha : a = Term.Stuck
      · subst a
        exact Or.inl (by simp [__eo_eq])
      · by_cases hb : b = Term.Stuck
        · subst b
          exact Or.inl (by simp [__eo_eq])
        · exact Or.inr ⟨native_teq b a, by simp [__eo_eq, ha, hb]⟩
    rcases eq_stuck_or_bool x1 x2 with hX | ⟨b1, hX⟩
    · simp [__eo_and, hX] at hAnd
    rcases eq_stuck_or_bool y1 y2 with hY | ⟨b2, hY⟩
    · simp [__eo_and, hX, hY] at hAnd
    cases b1 <;> cases b2 <;> simp [__eo_and, hX, hY, native_and] at hAnd ⊢
  exact ⟨eq_of_eo_eq_true x1 x2 hBoth.1, eq_of_eo_eq_true y1 y2 hBoth.2⟩

theorem eo_typeof_store_not_stuck_implies_array (A I E : Term)
    (h : __eo_typeof_store A I E ≠ Term.Stuck) :
    A = Term.Apply (Term.Apply Term.Array I) E := by
  by_cases hI : I = Term.Stuck
  · subst I
    simp [__eo_typeof_store] at h
  · by_cases hE : E = Term.Stuck
    · subst E
      simp [__eo_typeof_store] at h
    · cases A with
      | Apply f x =>
          cases f with
          | Apply g y =>
              cases g with
              | UOp op =>
                  cases op with
                  | Array =>
                      have hReq :
                          __eo_requires (__eo_and (__eo_eq y I) (__eo_eq x E))
                            (Term.Boolean true) (Term.Apply (Term.Apply Term.Array y) x) ≠
                            Term.Stuck := by
                        simpa [__eo_typeof_store, hI, hE] using h
                      have hEqs :
                          I = y ∧ E = x :=
                        eqs_of_requires_and_eq_true_not_stuck y x I E
                          (Term.Apply (Term.Apply Term.Array y) x) hReq
                      simpa [hEqs.1, hEqs.2]
                  | _ =>
                      simp [__eo_typeof_store, hI, hE] at h
              | _ =>
                  simp [__eo_typeof_store, hI, hE] at h
          | _ =>
              simp [__eo_typeof_store, hI, hE] at h
      | _ =>
          simp [__eo_typeof_store, hI, hE] at h

theorem eo_typeof_select_not_stuck_implies_array (A I : Term)
    (h : __eo_typeof_select A I ≠ Term.Stuck) :
    ∃ E : Term, A = Term.Apply (Term.Apply Term.Array I) E := by
  by_cases hI : I = Term.Stuck
  · subst I
    simp [__eo_typeof_select] at h
  · cases A with
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | UOp op =>
                cases op with
                | Array =>
                    have hReq :
                        __eo_requires (__eo_eq y I) (Term.Boolean true) x ≠ Term.Stuck := by
                      simpa [__eo_typeof_select, hI] using h
                    have hEq : I = y :=
                      eq_of_requires_eq_true_not_stuck y I x hReq
                    exact ⟨x, by simpa [hEq]⟩
                | _ =>
                    simp [__eo_typeof_select, hI] at h
            | _ =>
                simp [__eo_typeof_select, hI] at h
        | _ =>
            simp [__eo_typeof_select, hI] at h
    | _ =>
        simp [__eo_typeof_select, hI] at h

theorem smt_value_rel_map_of_lookup_eq
    (m1 m2 : SmtMap)
    (h : ∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v) :
    smt_value_rel (SmtValue.Map m1) (SmtValue.Map m2) := by
  sorry

theorem smt_value_rel_set_of_lookup_eq
    (m1 m2 : SmtMap)
    (h : ∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v) :
    smt_value_rel (SmtValue.Set m1) (SmtValue.Set m2) := by
  sorry

theorem smt_value_rel_select_store_same_of_map
    (m : SmtMap) (i e : SmtValue) :
    smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store (SmtValue.Map m) i e) i)
      e := by
  sorry

private theorem eq_of_native_veq_true {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = true) :
    v1 = v2 := by
  simpa [native_veq] using h

private theorem ne_of_native_veq_false {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = false) :
    v1 ≠ v2 := by
  intro hEq
  subst v2
  simp [native_veq] at h

theorem smt_value_rel_store_overwrite
    (v i e f : SmtValue) :
    smt_value_rel
      (__smtx_model_eval_store (__smtx_model_eval_store v i e) i f)
      (__smtx_model_eval_store v i f) := by
  sorry

theorem smt_value_rel_store_swap_of_native_veq_false
    (v i j e f : SmtValue)
    (hij : native_veq i j = false) :
    smt_value_rel
      (__smtx_model_eval_store (__smtx_model_eval_store v i e) j f)
      (__smtx_model_eval_store (__smtx_model_eval_store v j f) i e) := by
  sorry

theorem smt_value_rel_select_store_other_of_native_veq_false
    (v i j e : SmtValue)
    (hij : native_veq i j = false) :
    smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store v i e) j)
      (__smtx_model_eval_select v j) := by
  sorry

theorem smt_value_rel_store_self_of_map
    (m : SmtMap) (i : SmtValue) :
    smt_value_rel
      (__smtx_model_eval_store
        (SmtValue.Map m) i
        (__smtx_model_eval_select (SmtValue.Map m) i))
      (SmtValue.Map m) := by
  sorry

theorem model_eval_eq_false_of_eo_eq_false
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) false ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_eq_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [__smtx_model_eval.eq_133] at hEval
      exact hEval

theorem native_veq_false_of_model_eval_eq_false
    {v1 v2 : SmtValue}
    (h : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false) :
    native_veq v1 v2 = false := by
  by_cases hEq : native_veq v1 v2 = false
  · exact hEq
  · have hEqTrue : native_veq v1 v2 = true := by
      cases hV : native_veq v1 v2 with
      | false =>
          exfalso
          exact hEq hV
      | true =>
          rfl
    have hv : v1 = v2 := by
      simpa [native_veq] using hEqTrue
    subst hv
    rw [smtx_model_eval_eq_refl] at h
    cases h

private theorem model_eval_eq_is_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b := by
  cases v1 <;> cases v2 <;> simp [__smtx_model_eval_eq]

theorem model_eval_eq_false_of_eq_false_eq_true
    (M : SmtModel) (x y : Term) :
  eo_interprets M
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq x) y))
          (Term.Boolean false)) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h
  rw [eo_to_smt_eq_eq, eo_to_smt_eq_eq, eo_to_smt_false_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [__smtx_model_eval.eq_133] at hEval
      have hEqEval :
          __smtx_model_eval M ((__eo_to_smt x).eq (__eo_to_smt y)) =
            __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
              (__smtx_model_eval M (__eo_to_smt y)) := by
        rw [__smtx_model_eval.eq_133]
      have hFalseEval :
          __smtx_model_eval M (SmtTerm.Boolean false) =
            SmtValue.Boolean false := by
        rw [__smtx_model_eval.eq_1]
      rw [hEqEval, hFalseEval] at hEval
      rcases model_eval_eq_is_boolean
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) with
        ⟨b, hInner⟩
      rw [hInner] at hEval
      cases b
      · exact hInner
      · simp [__smtx_model_eval_eq, native_veq] at hEval

theorem model_eval_eq_false_of_not_eq_true
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x) y)) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  exact model_eval_eq_false_of_eo_eq_false M x y
    (eo_interprets_not_true_implies_false M _ h)

end RuleProofs
