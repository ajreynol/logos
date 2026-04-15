import Cpc.Proofs.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

/-- Simplifies EO-to-SMT translation for `true`. -/
theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `false`. -/
theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `not`. -/
theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply Term.not t) = SmtTerm.not (__eo_to_smt t) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `eq`. -/
theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x)) (__eo_to_smt y) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `select`. -/
theorem eo_to_smt_select_eq (a i : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.select a) i) =
      SmtTerm.select (__eo_to_smt a) (__eo_to_smt i) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `store`. -/
theorem eo_to_smt_store_eq (a i e : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e) =
      SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e) := by
  rw [__eo_to_smt.eq_def]

/-- Computes EO-to-SMT array type translation under a non-`None` premise. -/
theorem eo_to_smt_type_array_of_non_none (A B : Term)
    (h : __eo_to_smt_type (Term.Apply (Term.Apply Term.Array A) B) ≠ SmtType.None) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.Array A) B) =
      SmtType.Map (__eo_to_smt_type A) (__eo_to_smt_type B) := by
  cases hA : __eo_to_smt_type A <;> cases hB : __eo_to_smt_type B <;>
    simp [TranslationProofs.eo_to_smt_type_array, __smtx_typeof_guard,
      native_ite, native_Teq, hA, hB] at h ⊢

/-- `eq` has Boolean EO type only when both operand types are defined. -/
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

/-- `eq` has Boolean EO type only when both operand types agree. -/
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

/-- Evaluating `__eo_eq` to `true` forces the matched terms to agree. -/
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

/-- A satisfied `requires (eq x y) true` guard forces the aligned terms to match. -/
theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
    y = x := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg'
  exact eq_of_eo_eq_true x y hProg'.1

/-- A satisfied paired `requires` guard forces both alignment equalities. -/
theorem eqs_of_requires_and_eq_true_not_stuck (x1 y1 x2 y2 B : Term) :
    __eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
      (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd : __eo_and (__eo_eq x1 x2) (__eo_eq y1 y2) = Term.Boolean true := hProg'.1
  simp [__eo_and] at hAnd
  exact ⟨eq_of_eo_eq_true x1 x2 hAnd.1, eq_of_eo_eq_true y1 y2 hAnd.2⟩

/-- A well-typed EO `store` must be storing into an array of matching index and element type. -/
theorem eo_typeof_store_not_stuck_implies_array (A I E : Term)
    (h : __eo_typeof_store A I E ≠ Term.Stuck) :
    A = Term.Apply (Term.Apply Term.Array I) E := by
  cases A with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | Array =>
              change __eo_requires (__eo_and (__eo_eq y I) (__eo_eq x E))
                  (Term.Boolean true) ((Term.Array.Apply y).Apply x) ≠ Term.Stuck at h
              have hEqs :
                  I = y ∧ E = x :=
                eqs_of_requires_and_eq_true_not_stuck y x I E
                  ((Term.Array.Apply y).Apply x) h
              subst I
              subst E
              rfl
          | _ =>
              simp [__eo_typeof_store] at h
      | _ =>
          simp [__eo_typeof_store] at h
  | _ =>
      simp [__eo_typeof_store] at h

/-- A well-typed EO `select` must be selecting from an array with matching index type. -/
theorem eo_typeof_select_not_stuck_implies_array (A I : Term)
    (h : __eo_typeof_select A I ≠ Term.Stuck) :
    ∃ E : Term, A = Term.Apply (Term.Apply Term.Array I) E := by
  cases A with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | Array =>
              change __eo_requires (__eo_eq y I) (Term.Boolean true) x ≠ Term.Stuck at h
              have hEq : I = y :=
                eq_of_requires_eq_true_not_stuck y I x h
              subst I
              exact ⟨x, rfl⟩
          | _ =>
              simp [__eo_typeof_select] at h
      | _ =>
          simp [__eo_typeof_select] at h
  | _ =>
      simp [__eo_typeof_select] at h

/-- Builds map equality from pointwise lookup equality. -/
theorem smt_value_rel_map_of_lookup_eq
    (m1 m2 : SmtMap)
    (h : ∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v) :
    smt_value_rel (SmtValue.Map m1) (SmtValue.Map m2) := by
  classical
  rw [smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq, h]

/-- Builds set equality from pointwise lookup equality. -/
theorem smt_value_rel_set_of_lookup_eq
    (m1 m2 : SmtMap)
    (h : ∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v) :
    smt_value_rel (SmtValue.Set m1) (SmtValue.Set m2) := by
  classical
  rw [smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_eq, h]

/-- Reading the same index immediately after a store returns the stored value. -/
theorem smt_value_rel_select_store_same_of_map
    (m : SmtMap) (i e : SmtValue) :
    smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store (SmtValue.Map m) i e) i)
      e := by
  rw [smt_value_rel_iff_model_eval_eq_true]
  simp [__smtx_model_eval_select, __smtx_model_eval_store, __smtx_map_select,
    __smtx_map_store, __smtx_msm_lookup, __smtx_model_eval_eq, native_ite, native_veq]

/-- Overwriting the same array index twice is equivalent to keeping only the last write. -/
theorem smt_value_rel_store_overwrite
    (v i e f : SmtValue) :
    smt_value_rel
      (__smtx_model_eval_store (__smtx_model_eval_store v i e) i f)
      (__smtx_model_eval_store v i f) := by
  cases v with
  | Map m =>
      apply smt_value_rel_map_of_lookup_eq
      intro x
      by_cases hix : native_veq i x
      · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
          native_ite, hix]
      · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
          native_ite, hix]
  | Set m =>
      apply smt_value_rel_set_of_lookup_eq
      intro x
      by_cases hix : native_veq i x
      · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
          native_ite, hix]
      · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
          native_ite, hix]
  all_goals
    rw [smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_store, __smtx_map_store, __smtx_model_eval_eq, native_veq]

/-- Swapping two writes at distinct indices preserves the array value. -/
theorem smt_value_rel_store_swap_of_native_veq_false
    (v i j e f : SmtValue)
    (hij : native_veq i j = false) :
    smt_value_rel
      (__smtx_model_eval_store (__smtx_model_eval_store v i e) j f)
      (__smtx_model_eval_store (__smtx_model_eval_store v j f) i e) := by
  cases v with
  | Map m =>
      apply smt_value_rel_map_of_lookup_eq
      intro x
      by_cases hix : native_veq i x
      · by_cases hjx : native_veq j x
        · have hix' : i = x := by
            simpa [native_veq] using hix
          have hjx' : j = x := by
            simpa [native_veq] using hjx
          have hij' : i = j := hix'.trans hjx'.symm
          have : native_veq i j = true := by
            simpa [native_veq] using hij'
          rw [this] at hij
          cases hij
        · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
            native_ite, hix, hjx]
      · by_cases hjx : native_veq j x
        · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
            native_ite, hix, hjx]
        · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
            native_ite, hix, hjx]
  | Set m =>
      apply smt_value_rel_set_of_lookup_eq
      intro x
      by_cases hix : native_veq i x
      · by_cases hjx : native_veq j x
        · have hix' : i = x := by
            simpa [native_veq] using hix
          have hjx' : j = x := by
            simpa [native_veq] using hjx
          have hij' : i = j := hix'.trans hjx'.symm
          have : native_veq i j = true := by
            simpa [native_veq] using hij'
          rw [this] at hij
          cases hij
        · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
            native_ite, hix, hjx]
      · by_cases hjx : native_veq j x
        · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
            native_ite, hix, hjx]
        · simp [__smtx_model_eval_store, __smtx_map_store, __smtx_msm_lookup,
            native_ite, hix, hjx]
  all_goals
    rw [smt_value_rel_iff_model_eval_eq_true]
    simp [__smtx_model_eval_store, __smtx_map_store, __smtx_model_eval_eq, native_veq]

/-- Reading at a different index commutes past a store. -/
theorem smt_value_rel_select_store_other_of_native_veq_false
    (v i j e : SmtValue)
    (hij : native_veq i j = false) :
    smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store v i e) j)
      (__smtx_model_eval_select v j) := by
  cases v <;>
    rw [smt_value_rel_iff_model_eval_eq_true] <;>
    simp [__smtx_model_eval_select, __smtx_model_eval_store, __smtx_map_select,
      __smtx_map_store, __smtx_msm_lookup, __smtx_model_eval_eq, native_ite, hij, native_veq]

/-- Writing back the value already stored at an index preserves the array. -/
theorem smt_value_rel_store_self_of_map
    (m : SmtMap) (i : SmtValue) :
    smt_value_rel
      (__smtx_model_eval_store
        (SmtValue.Map m) i
        (__smtx_model_eval_select (SmtValue.Map m) i))
      (SmtValue.Map m) := by
  apply smt_value_rel_map_of_lookup_eq
  intro x
  by_cases hix : native_veq i x
  · simp [__smtx_model_eval_store, __smtx_model_eval_select, __smtx_map_store,
      __smtx_map_select, __smtx_msm_lookup, native_ite, hix]
  · simp [__smtx_model_eval_store, __smtx_model_eval_select, __smtx_map_store,
      __smtx_map_select, __smtx_msm_lookup, native_ite, hix]

/-- Reads off an SMT equality evaluation from an EO `eq = false` proof. -/
theorem model_eval_eq_false_of_eo_eq_false
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) false ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_eq_eq] at h
  cases h with
  | intro_false _ hEval =>
      simpa using hEval

/-- Turns an SMT equality evaluation to `false` into a failed structural equality. -/
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

/-- Reads off an inner SMT equality evaluation from an EO `(eq (eq x y) false)` proof. -/
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
      simp [__smtx_model_eval, __smtx_model_eval_eq] at hEval
      let vx := __smtx_model_eval M (__eo_to_smt x)
      let vy := __smtx_model_eval M (__eo_to_smt y)
      have hBool :
          ∃ b : Bool, __smtx_model_eval_eq vx vy = SmtValue.Boolean b :=
        bool_value_canonical (typeof_value_model_eval_eq_value vx vy)
      rcases hBool with ⟨b, hb⟩
      rw [hb] at hEval
      cases b with
      | false =>
          simpa [vx, vy] using hb
      | true =>
          simp [native_veq] at hEval

/-- Reads off an SMT equality evaluation from an EO `not (eq x y)` proof. -/
theorem model_eval_eq_false_of_not_eq_true
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x) y)) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  exact model_eval_eq_false_of_eo_eq_false M x y
    (eo_interprets_not_true_implies_false M _ h)

end RuleProofs
