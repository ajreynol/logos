import CpcMini.Proofs.TypePreservation
import CpcMini.Proofs.Translation

open Eo
open SmtEval
open Smtm

namespace RuleProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

/-- Simplifies EO-to-SMT translation for `true`. -/
private theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `stuck`. -/
private theorem eo_to_smt_stuck_eq :
    __eo_to_smt Term.Stuck = SmtTerm.None := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `and`. -/
private theorem eo_to_smt_and_eq (A B : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) =
      SmtTerm.and (__eo_to_smt A) (__eo_to_smt B) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `not`. -/
private theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply (Term.UOp UserOp.not) t) =
      SmtTerm.not (__eo_to_smt t) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `eq`. -/
private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rw [__eo_to_smt.eq_def]

/-- Characterizes EO interpretation in terms of the translated SMT interpretation. -/
theorem eo_interprets_iff_smt_interprets (M : SmtModel) (t : Term) (b : Bool) :
  eo_interprets M t b ↔ smt_interprets M (__eo_to_smt t) b := by
  constructor
  · intro h
    rcases h with ⟨s, hs, hInterp⟩
    cases hs
    simpa using hInterp
  · intro h
    exact ⟨__eo_to_smt t, eo_is_obj.intro t, h⟩

/-- Shows that the EO term `true` is interpreted as `true` in every model. -/
theorem eo_interprets_true (M : SmtModel) :
  eo_interprets M (Term.Boolean true) true := by
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_true_eq]
  refine smt_interprets.intro_true M (SmtTerm.Boolean true) ?_ ?_
  · simpa using Smtm.__smtx_typeof.eq_1 true
  · simpa using Smtm.__smtx_model_eval.eq_1 M true

/-- Predicate asserting that translating an EO term yields a non-`None` SMT term. -/
def eo_has_smt_translation (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

/-- Predicate asserting that an EO term translates to SMT Boolean type. -/
def eo_has_bool_type (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Bool

/-- Lemma about `eo_has_smt_translation_true`. -/
theorem eo_has_smt_translation_true :
  eo_has_smt_translation (Term.Boolean true) := by
  unfold eo_has_smt_translation
  rw [eo_to_smt_true_eq, Smtm.__smtx_typeof.eq_1]
  decide

/-- Lemma about `eo_has_bool_type_true`. -/
theorem eo_has_bool_type_true :
  eo_has_bool_type (Term.Boolean true) := by
  unfold eo_has_bool_type
  rw [eo_to_smt_true_eq, Smtm.__smtx_typeof.eq_1]

/-- Derives `eo_has_bool_type` from `interprets_true`. -/
theorem eo_has_bool_type_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true ->
  eo_has_bool_type t := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy _ =>
      simpa [eo_has_bool_type] using hTy

/-- Derives `eo_has_bool_type` from `interprets_false`. -/
theorem eo_has_bool_type_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false ->
  eo_has_bool_type t := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_false hTy _ =>
      simpa [eo_has_bool_type] using hTy

/-- Transfers EO Boolean typing to the translated SMT term under a defined translation. -/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = Term.Bool ->
  __smtx_typeof s = SmtType.Bool := by
  intro hs hS hTy
  exact eo_to_smt_well_typed_and_typeof_implies_smt_type
    t Term.Bool s hs hS hTy

/-- Computes `__eo_typeof` for `bool_implies_has_bool_type`. -/
theorem eo_typeof_bool_implies_has_bool_type
    (t : Term) :
  eo_has_smt_translation t ->
  __eo_typeof t = Term.Bool ->
  eo_has_bool_type t := by
  intro hTrans hTy
  exact eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t (__eo_to_smt t) rfl hTrans hTy

/-- Derives `eo_has_smt_translation` from `has_bool_type`. -/
theorem eo_has_smt_translation_of_has_bool_type (t : Term) :
  eo_has_bool_type t ->
  eo_has_smt_translation t := by
  intro hTy
  intro hNone
  rw [eo_has_bool_type] at hTy
  rw [hNone] at hTy
  cases hTy

/-- Derives `term_ne_stuck` from `has_smt_translation`. -/
theorem term_ne_stuck_of_has_smt_translation (t : Term) :
  eo_has_smt_translation t -> t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  rw [eo_has_smt_translation, eo_to_smt_stuck_eq] at hTy
  exact hTy (by simp [Smtm.__smtx_typeof.eq_def])

/-- Derives `eo_has_bool_type_and` from `bool_args`. -/
theorem eo_has_bool_type_and_of_bool_args (A B : Term) :
  eo_has_bool_type A ->
  eo_has_bool_type B ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) := by
  intro hA hB
  unfold eo_has_bool_type at hA hB ⊢
  rw [eo_to_smt_and_eq A B]
  simp [Smtm.__smtx_typeof.eq_8, hA, hB, native_ite, native_Teq]

/-- Left-projection lemma for `eo_has_bool_type_and`. -/
theorem eo_has_bool_type_and_left (A B : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) ->
  eo_has_bool_type A := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_and_eq A B] at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact
    (bool_binop_args_bool_of_non_none
      (op := SmtTerm.and) (Smtm.__smtx_typeof.eq_8 (__eo_to_smt A) (__eo_to_smt B)) hNN).1

/-- Right-projection lemma for `eo_has_bool_type_and`. -/
theorem eo_has_bool_type_and_right (A B : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) ->
  eo_has_bool_type B := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_and_eq A B] at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact
    (bool_binop_args_bool_of_non_none
      (op := SmtTerm.and) (Smtm.__smtx_typeof.eq_8 (__eo_to_smt A) (__eo_to_smt B)) hNN).2

/-- Derives `eo_has_bool_type_not` from `bool_arg`. -/
theorem eo_has_bool_type_not_of_bool_arg (t : Term) :
  eo_has_bool_type t ->
  eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) t) := by
  intro hTy
  unfold eo_has_bool_type at hTy ⊢
  rw [eo_to_smt_not_eq t]
  simp [Smtm.__smtx_typeof.eq_6, hTy, native_ite, native_Teq]

/-- Lemma about `eo_has_bool_type_not_arg`. -/
theorem eo_has_bool_type_not_arg (t : Term) :
  eo_has_bool_type (Term.Apply (Term.UOp UserOp.not) t) ->
  eo_has_bool_type t := by
  intro hTy
  by_cases hT : __smtx_typeof (__eo_to_smt t) = SmtType.Bool
  · simpa [eo_has_bool_type] using hT
  · have : False := by
      unfold eo_has_bool_type at hTy
      rw [eo_to_smt_not_eq t] at hTy
      rw [Smtm.__smtx_typeof.eq_6] at hTy
      simp [hT, native_ite, native_Teq] at hTy
    exact False.elim this

/-- Derives `eo_interprets` from `bool_eval`. -/
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

/-- Derives `eo_eval_is_boolean` from `has_bool_type`. -/
theorem eo_eval_is_boolean_of_has_bool_type
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  eo_has_bool_type t ->
  ∃ b : Bool, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Boolean b := by
  intro hTy
  exact smt_model_eval_bool_is_boolean M hM (__eo_to_smt t) hTy

/-- Lemma about `eo_interprets_true_not_false`. -/
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

/-- Left-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_left (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M A true := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_and_eq A B] at h
  cases h with
  | intro_true hty hEval =>
      have htyA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact
          (bool_binop_args_bool_of_non_none
            (op := SmtTerm.and) (Smtm.__smtx_typeof.eq_8 (__eo_to_smt A) (__eo_to_smt B)) hNN).1
      have hEvalA : __smtx_model_eval M (__eo_to_smt A) = SmtValue.Boolean true := by
        rw [Smtm.__smtx_model_eval.eq_8] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.native_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt A) htyA hEvalA

/-- Right-projection lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_right (M : SmtModel) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true ->
  eo_interprets M B true := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_and_eq A B] at h
  cases h with
  | intro_true hty hEval =>
      have htyB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool := by
        have hNN : term_has_non_none_type
            (SmtTerm.and (__eo_to_smt A) (__eo_to_smt B)) := by
          unfold term_has_non_none_type
          rw [hty]
          simp
        exact
          (bool_binop_args_bool_of_non_none
            (op := SmtTerm.and) (Smtm.__smtx_typeof.eq_8 (__eo_to_smt A) (__eo_to_smt B)) hNN).2
      have hEvalB : __smtx_model_eval M (__eo_to_smt B) = SmtValue.Boolean true := by
        rw [Smtm.__smtx_model_eval.eq_8] at hEval
        cases hAeval : __smtx_model_eval M (__eo_to_smt A) <;>
          cases hBeval : __smtx_model_eval M (__eo_to_smt B) <;>
          simp [hAeval, hBeval, __smtx_model_eval_and] at hEval
        case Boolean.Boolean a b =>
          cases a <;> cases b <;> simp [SmtEval.native_and] at hEval
          simp
      exact smt_interprets.intro_true M (__eo_to_smt B) htyB hEvalB

/-- Introduction lemma for `eo_interprets_and`. -/
theorem eo_interprets_and_intro (M : SmtModel) (A B : Term) :
  eo_interprets M A true ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) A) B) true := by
  intro hA hB
  rw [eo_interprets_iff_smt_interprets] at hA hB ⊢
  rw [eo_to_smt_and_eq A B]
  cases hA with
  | intro_true htyA hEvalA =>
      cases hB with
      | intro_true htyB hEvalB =>
          apply smt_interprets.intro_true
          · simp [Smtm.__smtx_typeof.eq_8, htyA, htyB, native_Teq, native_ite]
          · simp [Smtm.__smtx_model_eval.eq_8, __smtx_model_eval_and, hEvalA, hEvalB, SmtEval.native_and]

/-- Semantic equality relation on SMT values, defined by evaluation of SMT equality. -/
def smt_value_rel (v1 v2 : SmtValue) : Prop :=
  __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true

/-- Semantic equality relation on SMT sequences, lifted through `SmtValue.Seq`. -/
def smt_seq_rel (s1 s2 : SmtSeq) : Prop :=
  __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true

/-- Fallback equation for typed equality when the left value is not a map. -/
private theorem smtx_value_eq_map_fallback_left
    (T U : SmtType) {v1 v2 : SmtValue}
    (hLeft : ∀ m, v1 ≠ SmtValue.Map m) :
    __smtx_value_eq (SmtType.Map T U) v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

/-- Fallback equation for typed equality when the right value is not a map. -/
private theorem smtx_value_eq_map_fallback_right
    (T U : SmtType) {v1 v2 : SmtValue}
    (hRight : ∀ m, v2 ≠ SmtValue.Map m) :
    __smtx_value_eq (SmtType.Map T U) v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

/-- Fallback equation for typed equality when the left value is not a set. -/
private theorem smtx_value_eq_set_fallback_left
    (T : SmtType) {v1 v2 : SmtValue}
    (hLeft : ∀ m, v1 ≠ SmtValue.Set m) :
    __smtx_value_eq (SmtType.Set T) v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

/-- Fallback equation for typed equality when the right value is not a set. -/
private theorem smtx_value_eq_set_fallback_right
    (T : SmtType) {v1 v2 : SmtValue}
    (hRight : ∀ m, v2 ≠ SmtValue.Set m) :
    __smtx_value_eq (SmtType.Set T) v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

/-- Fallback equation for typed equality when the left value is not a function. -/
private theorem smtx_value_eq_fun_fallback_left
    (T U : SmtType) {v1 v2 : SmtValue}
    (hLeft : ∀ m, v1 ≠ SmtValue.Fun m) :
    __smtx_value_eq (SmtType.FunType T U) v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

/-- Fallback equation for typed equality when the right value is not a function. -/
private theorem smtx_value_eq_fun_fallback_right
    (T U : SmtType) {v1 v2 : SmtValue}
    (hRight : ∀ m, v2 ≠ SmtValue.Fun m) :
    __smtx_value_eq (SmtType.FunType T U) v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

/-- Fallback equation for typed equality when the left value is not a regular language. -/
private theorem smtx_value_eq_reglan_fallback_left
    {v1 v2 : SmtValue}
    (hLeft : ∀ r, v1 ≠ SmtValue.RegLan r) :
    __smtx_value_eq SmtType.RegLan v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

/-- Fallback equation for typed equality when the right value is not a regular language. -/
private theorem smtx_value_eq_reglan_fallback_right
    {v1 v2 : SmtValue}
    (hRight : ∀ r, v2 ≠ SmtValue.RegLan r) :
    __smtx_value_eq SmtType.RegLan v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

/-- Fallback equation for typed equality when the left value is not a sequence. -/
private theorem smtx_value_eq_seq_fallback_left
    (T : SmtType) {v1 v2 : SmtValue}
    (hLeft : ∀ s, v1 ≠ SmtValue.Seq s) :
    __smtx_value_eq (SmtType.Seq T) v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

/-- Fallback equation for typed equality when the right value is not a sequence. -/
private theorem smtx_value_eq_seq_fallback_right
    (T : SmtType) {v1 v2 : SmtValue}
    (hRight : ∀ s, v2 ≠ SmtValue.Seq s) :
    __smtx_value_eq (SmtType.Seq T) v1 v2 = native_veq v1 v2 := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

private theorem smtx_value_eq_seq_empty_cons_fallback
    (T T1 : SmtType) (v2 : SmtValue) (s2 : SmtSeq) :
    __smtx_value_eq (SmtType.Seq T) (SmtValue.Seq (SmtSeq.empty T1))
      (SmtValue.Seq (SmtSeq.cons v2 s2)) =
        native_veq (SmtValue.Seq (SmtSeq.empty T1))
          (SmtValue.Seq (SmtSeq.cons v2 s2)) := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

private theorem smtx_value_eq_seq_cons_empty_fallback
    (T : SmtType) (v1 : SmtValue) (s1 : SmtSeq) (T2 : SmtType) :
    __smtx_value_eq (SmtType.Seq T) (SmtValue.Seq (SmtSeq.cons v1 s1))
      (SmtValue.Seq (SmtSeq.empty T2)) =
        native_veq (SmtValue.Seq (SmtSeq.cons v1 s1))
          (SmtValue.Seq (SmtSeq.empty T2)) := by
  rw [Smtm.__smtx_value_eq.eq_7]
  all_goals
    intro
    simp_all

private theorem smtx_value_eq_reglan_trans_aux {v1 v2 v3 : SmtValue}
    (h12 : __smtx_value_eq SmtType.RegLan v1 v2 = true)
    (h23 : __smtx_value_eq SmtType.RegLan v2 v3 = true) :
    __smtx_value_eq SmtType.RegLan v1 v3 = true := by
  by_cases hv1 : ∃ r1, v1 = SmtValue.RegLan r1
  · rcases hv1 with ⟨r1, rfl⟩
    by_cases hv2 : ∃ r2, v2 = SmtValue.RegLan r2
    · rcases hv2 with ⟨r2, rfl⟩
      by_cases hv3 : ∃ r3, v3 = SmtValue.RegLan r3
      · rcases hv3 with ⟨r3, rfl⟩
        classical
        simp [__smtx_value_eq] at h12 h23 ⊢
        intro s
        exact (h12 s).trans (h23 s)
      · have h23Native : native_veq (SmtValue.RegLan r2) v3 = true := by
          simpa [smtx_value_eq_reglan_fallback_right
            (v1 := SmtValue.RegLan r2) (v2 := v3) (by
              intro r hr
              exact hv3 ⟨r, hr⟩)] using h23
        have hEq : SmtValue.RegLan r2 = v3 := by
          simpa [native_veq] using h23Native
        exact False.elim (hv3 ⟨r2, hEq.symm⟩)
    · have h12Native : native_veq (SmtValue.RegLan r1) v2 = true := by
        simpa [smtx_value_eq_reglan_fallback_right
          (v1 := SmtValue.RegLan r1) (v2 := v2) (by
            intro r hr
            exact hv2 ⟨r, hr⟩)] using h12
      have hEq : SmtValue.RegLan r1 = v2 := by
        simpa [native_veq] using h12Native
      exact False.elim (hv2 ⟨r1, hEq.symm⟩)
  · have h12Native : native_veq v1 v2 = true := by
      simpa [smtx_value_eq_reglan_fallback_left
        (v1 := v1) (v2 := v2) (by
          intro r hr
          exact hv1 ⟨r, hr⟩)] using h12
    have hEq12 : v1 = v2 := by
      simpa [native_veq] using h12Native
    subst v2
    have h23Native : native_veq v1 v3 = true := by
      simpa [smtx_value_eq_reglan_fallback_left
        (v1 := v1) (v2 := v3) (by
          intro r hr
          exact hv1 ⟨r, hr⟩)] using h23
    have hEq13 : v1 = v3 := by
      simpa [native_veq] using h23Native
    subst v3
    rw [smtx_value_eq_reglan_fallback_left (v1 := v1) (v2 := v1) (by
      intro r hr
      exact hv1 ⟨r, hr⟩)]
    simp [native_veq]

private theorem smtx_value_eq_reglan_symm_aux {v1 v2 : SmtValue}
    (h : __smtx_value_eq SmtType.RegLan v1 v2 = true) :
    __smtx_value_eq SmtType.RegLan v2 v1 = true := by
  by_cases hv1 : ∃ r1, v1 = SmtValue.RegLan r1
  · rcases hv1 with ⟨r1, rfl⟩
    by_cases hv2 : ∃ r2, v2 = SmtValue.RegLan r2
    · rcases hv2 with ⟨r2, rfl⟩
      classical
      simp [__smtx_value_eq] at h ⊢
      intro s
      exact (h s).symm
    · have hNative : native_veq (SmtValue.RegLan r1) v2 = true := by
        simpa [smtx_value_eq_reglan_fallback_right
          (v1 := SmtValue.RegLan r1) (v2 := v2) (by
            intro r hr
            exact hv2 ⟨r, hr⟩)] using h
      have hEq : SmtValue.RegLan r1 = v2 := by
        simpa [native_veq] using hNative
      exact False.elim (hv2 ⟨r1, hEq.symm⟩)
  · have hNative : native_veq v1 v2 = true := by
      simpa [smtx_value_eq_reglan_fallback_left
        (v1 := v1) (v2 := v2) (by
          intro r hr
          exact hv1 ⟨r, hr⟩)] using h
    have hEq : v1 = v2 := by
      simpa [native_veq] using hNative
    subst v2
    rw [smtx_value_eq_reglan_fallback_left (v1 := v1) (v2 := v1) (by
      intro r hr
      exact hv1 ⟨r, hr⟩)]
    simp [native_veq]

private theorem smtx_value_eq_map_trans_aux
    (T U : SmtType)
    (rec : ∀ {a b c : SmtValue},
      __smtx_value_eq U a b = true ->
      __smtx_value_eq U b c = true ->
      __smtx_value_eq U a c = true)
    {v1 v2 v3 : SmtValue}
    (h12 : __smtx_value_eq (SmtType.Map T U) v1 v2 = true)
    (h23 : __smtx_value_eq (SmtType.Map T U) v2 v3 = true) :
    __smtx_value_eq (SmtType.Map T U) v1 v3 = true := by
  by_cases hv1 : ∃ m1, v1 = SmtValue.Map m1
  · rcases hv1 with ⟨m1, rfl⟩
    by_cases hv2 : ∃ m2, v2 = SmtValue.Map m2
    · rcases hv2 with ⟨m2, rfl⟩
      by_cases hv3 : ∃ m3, v3 = SmtValue.Map m3
      · rcases hv3 with ⟨m3, rfl⟩
        classical
        simp [__smtx_value_eq] at h12 h23 ⊢
        intro v
        exact rec (h12 v) (h23 v)
      · have h23Native : native_veq (SmtValue.Map m2) v3 = true := by
          simpa [smtx_value_eq_map_fallback_right T U
            (v1 := SmtValue.Map m2) (v2 := v3) (by
              intro m hm
              exact hv3 ⟨m, hm⟩)] using h23
        have hEq : SmtValue.Map m2 = v3 := by
          simpa [native_veq] using h23Native
        exact False.elim (hv3 ⟨m2, hEq.symm⟩)
    · have h12Native : native_veq (SmtValue.Map m1) v2 = true := by
        simpa [smtx_value_eq_map_fallback_right T U
          (v1 := SmtValue.Map m1) (v2 := v2) (by
            intro m hm
            exact hv2 ⟨m, hm⟩)] using h12
      have hEq : SmtValue.Map m1 = v2 := by
        simpa [native_veq] using h12Native
      exact False.elim (hv2 ⟨m1, hEq.symm⟩)
  · have h12Native : native_veq v1 v2 = true := by
      simpa [smtx_value_eq_map_fallback_left T U
        (v1 := v1) (v2 := v2) (by
          intro m hm
          exact hv1 ⟨m, hm⟩)] using h12
    have hEq12 : v1 = v2 := by
      simpa [native_veq] using h12Native
    subst v2
    have h23Native : native_veq v1 v3 = true := by
      simpa [smtx_value_eq_map_fallback_left T U
        (v1 := v1) (v2 := v3) (by
          intro m hm
          exact hv1 ⟨m, hm⟩)] using h23
    have hEq13 : v1 = v3 := by
      simpa [native_veq] using h23Native
    subst v3
    rw [smtx_value_eq_map_fallback_left T U (v1 := v1) (v2 := v1) (by
      intro m hm
      exact hv1 ⟨m, hm⟩)]
    simp [native_veq]

private theorem smtx_value_eq_map_symm_aux
    (T U : SmtType)
    (rec : ∀ {a b : SmtValue},
      __smtx_value_eq U a b = true ->
      __smtx_value_eq U b a = true)
    {v1 v2 : SmtValue}
    (h : __smtx_value_eq (SmtType.Map T U) v1 v2 = true) :
    __smtx_value_eq (SmtType.Map T U) v2 v1 = true := by
  by_cases hv1 : ∃ m1, v1 = SmtValue.Map m1
  · rcases hv1 with ⟨m1, rfl⟩
    by_cases hv2 : ∃ m2, v2 = SmtValue.Map m2
    · rcases hv2 with ⟨m2, rfl⟩
      classical
      simp [__smtx_value_eq] at h ⊢
      intro v
      exact rec (h v)
    · have hNative : native_veq (SmtValue.Map m1) v2 = true := by
        simpa [smtx_value_eq_map_fallback_right T U
          (v1 := SmtValue.Map m1) (v2 := v2) (by
            intro m hm
            exact hv2 ⟨m, hm⟩)] using h
      have hEq : SmtValue.Map m1 = v2 := by
        simpa [native_veq] using hNative
      exact False.elim (hv2 ⟨m1, hEq.symm⟩)
  · have hNative : native_veq v1 v2 = true := by
      simpa [smtx_value_eq_map_fallback_left T U
        (v1 := v1) (v2 := v2) (by
          intro m hm
          exact hv1 ⟨m, hm⟩)] using h
    have hEq : v1 = v2 := by
      simpa [native_veq] using hNative
    subst v2
    rw [smtx_value_eq_map_fallback_left T U (v1 := v1) (v2 := v1) (by
      intro m hm
      exact hv1 ⟨m, hm⟩)]
    simp [native_veq]

private theorem smtx_value_eq_set_trans_aux
    (T : SmtType) {v1 v2 v3 : SmtValue}
    (h12 : __smtx_value_eq (SmtType.Set T) v1 v2 = true)
    (h23 : __smtx_value_eq (SmtType.Set T) v2 v3 = true) :
    __smtx_value_eq (SmtType.Set T) v1 v3 = true := by
  by_cases hv1 : ∃ m1, v1 = SmtValue.Set m1
  · rcases hv1 with ⟨m1, rfl⟩
    by_cases hv2 : ∃ m2, v2 = SmtValue.Set m2
    · rcases hv2 with ⟨m2, rfl⟩
      by_cases hv3 : ∃ m3, v3 = SmtValue.Set m3
      · rcases hv3 with ⟨m3, rfl⟩
        classical
        simp [__smtx_value_eq] at h12 h23 ⊢
        intro v
        have hv12 := h12 v
        have hv23 := h23 v
        simp [native_veq] at hv12 hv23 ⊢
        exact hv12.trans hv23
      · have h23Native : native_veq (SmtValue.Set m2) v3 = true := by
          simpa [smtx_value_eq_set_fallback_right T
            (v1 := SmtValue.Set m2) (v2 := v3) (by
              intro m hm
              exact hv3 ⟨m, hm⟩)] using h23
        have hEq : SmtValue.Set m2 = v3 := by
          simpa [native_veq] using h23Native
        exact False.elim (hv3 ⟨m2, hEq.symm⟩)
    · have h12Native : native_veq (SmtValue.Set m1) v2 = true := by
        simpa [smtx_value_eq_set_fallback_right T
          (v1 := SmtValue.Set m1) (v2 := v2) (by
            intro m hm
            exact hv2 ⟨m, hm⟩)] using h12
      have hEq : SmtValue.Set m1 = v2 := by
        simpa [native_veq] using h12Native
      exact False.elim (hv2 ⟨m1, hEq.symm⟩)
  · have h12Native : native_veq v1 v2 = true := by
      simpa [smtx_value_eq_set_fallback_left T
        (v1 := v1) (v2 := v2) (by
          intro m hm
          exact hv1 ⟨m, hm⟩)] using h12
    have hEq12 : v1 = v2 := by
      simpa [native_veq] using h12Native
    subst v2
    have h23Native : native_veq v1 v3 = true := by
      simpa [smtx_value_eq_set_fallback_left T
        (v1 := v1) (v2 := v3) (by
          intro m hm
          exact hv1 ⟨m, hm⟩)] using h23
    have hEq13 : v1 = v3 := by
      simpa [native_veq] using h23Native
    subst v3
    rw [smtx_value_eq_set_fallback_left T (v1 := v1) (v2 := v1) (by
      intro m hm
      exact hv1 ⟨m, hm⟩)]
    simp [native_veq]

private theorem smtx_value_eq_set_symm_aux
    (T : SmtType) {v1 v2 : SmtValue}
    (h : __smtx_value_eq (SmtType.Set T) v1 v2 = true) :
    __smtx_value_eq (SmtType.Set T) v2 v1 = true := by
  by_cases hv1 : ∃ m1, v1 = SmtValue.Set m1
  · rcases hv1 with ⟨m1, rfl⟩
    by_cases hv2 : ∃ m2, v2 = SmtValue.Set m2
    · rcases hv2 with ⟨m2, rfl⟩
      classical
      simp [__smtx_value_eq] at h ⊢
      intro v
      have hv := h v
      simp [native_veq] at hv ⊢
      exact hv.symm
    · have hNative : native_veq (SmtValue.Set m1) v2 = true := by
        simpa [smtx_value_eq_set_fallback_right T
          (v1 := SmtValue.Set m1) (v2 := v2) (by
            intro m hm
            exact hv2 ⟨m, hm⟩)] using h
      have hEq : SmtValue.Set m1 = v2 := by
        simpa [native_veq] using hNative
      exact False.elim (hv2 ⟨m1, hEq.symm⟩)
  · have hNative : native_veq v1 v2 = true := by
      simpa [smtx_value_eq_set_fallback_left T
        (v1 := v1) (v2 := v2) (by
          intro m hm
          exact hv1 ⟨m, hm⟩)] using h
    have hEq : v1 = v2 := by
      simpa [native_veq] using hNative
    subst v2
    rw [smtx_value_eq_set_fallback_left T (v1 := v1) (v2 := v1) (by
      intro m hm
      exact hv1 ⟨m, hm⟩)]
    simp [native_veq]

private theorem smtx_value_eq_fun_trans_aux
    (T U : SmtType)
    (rec : ∀ {a b c : SmtValue},
      __smtx_value_eq U a b = true ->
      __smtx_value_eq U b c = true ->
      __smtx_value_eq U a c = true)
    {v1 v2 v3 : SmtValue}
    (h12 : __smtx_value_eq (SmtType.FunType T U) v1 v2 = true)
    (h23 : __smtx_value_eq (SmtType.FunType T U) v2 v3 = true) :
    __smtx_value_eq (SmtType.FunType T U) v1 v3 = true := by
  by_cases hv1 : ∃ m1, v1 = SmtValue.Fun m1
  · rcases hv1 with ⟨m1, rfl⟩
    by_cases hv2 : ∃ m2, v2 = SmtValue.Fun m2
    · rcases hv2 with ⟨m2, rfl⟩
      by_cases hv3 : ∃ m3, v3 = SmtValue.Fun m3
      · rcases hv3 with ⟨m3, rfl⟩
        classical
        simp [__smtx_value_eq] at h12 h23 ⊢
        intro v
        exact rec (h12 v) (h23 v)
      · have h23Native : native_veq (SmtValue.Fun m2) v3 = true := by
          simpa [smtx_value_eq_fun_fallback_right T U
            (v1 := SmtValue.Fun m2) (v2 := v3) (by
              intro m hm
              exact hv3 ⟨m, hm⟩)] using h23
        have hEq : SmtValue.Fun m2 = v3 := by
          simpa [native_veq] using h23Native
        exact False.elim (hv3 ⟨m2, hEq.symm⟩)
    · have h12Native : native_veq (SmtValue.Fun m1) v2 = true := by
        simpa [smtx_value_eq_fun_fallback_right T U
          (v1 := SmtValue.Fun m1) (v2 := v2) (by
            intro m hm
            exact hv2 ⟨m, hm⟩)] using h12
      have hEq : SmtValue.Fun m1 = v2 := by
        simpa [native_veq] using h12Native
      exact False.elim (hv2 ⟨m1, hEq.symm⟩)
  · have h12Native : native_veq v1 v2 = true := by
      simpa [smtx_value_eq_fun_fallback_left T U
        (v1 := v1) (v2 := v2) (by
          intro m hm
          exact hv1 ⟨m, hm⟩)] using h12
    have hEq12 : v1 = v2 := by
      simpa [native_veq] using h12Native
    subst v2
    have h23Native : native_veq v1 v3 = true := by
      simpa [smtx_value_eq_fun_fallback_left T U
        (v1 := v1) (v2 := v3) (by
          intro m hm
          exact hv1 ⟨m, hm⟩)] using h23
    have hEq13 : v1 = v3 := by
      simpa [native_veq] using h23Native
    subst v3
    rw [smtx_value_eq_fun_fallback_left T U (v1 := v1) (v2 := v1) (by
      intro m hm
      exact hv1 ⟨m, hm⟩)]
    simp [native_veq]

private theorem smtx_value_eq_fun_symm_aux
    (T U : SmtType)
    (rec : ∀ {a b : SmtValue},
      __smtx_value_eq U a b = true ->
      __smtx_value_eq U b a = true)
    {v1 v2 : SmtValue}
    (h : __smtx_value_eq (SmtType.FunType T U) v1 v2 = true) :
    __smtx_value_eq (SmtType.FunType T U) v2 v1 = true := by
  by_cases hv1 : ∃ m1, v1 = SmtValue.Fun m1
  · rcases hv1 with ⟨m1, rfl⟩
    by_cases hv2 : ∃ m2, v2 = SmtValue.Fun m2
    · rcases hv2 with ⟨m2, rfl⟩
      classical
      simp [__smtx_value_eq] at h ⊢
      intro v
      exact rec (h v)
    · have hNative : native_veq (SmtValue.Fun m1) v2 = true := by
        simpa [smtx_value_eq_fun_fallback_right T U
          (v1 := SmtValue.Fun m1) (v2 := v2) (by
            intro m hm
            exact hv2 ⟨m, hm⟩)] using h
      have hEq : SmtValue.Fun m1 = v2 := by
        simpa [native_veq] using hNative
      exact False.elim (hv2 ⟨m1, hEq.symm⟩)
  · have hNative : native_veq v1 v2 = true := by
      simpa [smtx_value_eq_fun_fallback_left T U
        (v1 := v1) (v2 := v2) (by
          intro m hm
          exact hv1 ⟨m, hm⟩)] using h
    have hEq : v1 = v2 := by
      simpa [native_veq] using hNative
    subst v2
    rw [smtx_value_eq_fun_fallback_left T U (v1 := v1) (v2 := v1) (by
      intro m hm
      exact hv1 ⟨m, hm⟩)]
    simp [native_veq]

/-- Reflexivity of executable value equality at a fixed SMT type. -/
private theorem smtx_value_eq_refl (T : SmtType) (v : SmtValue) :
    __smtx_value_eq T v v = true := by
  cases T with
  | None => simp [__smtx_value_eq, native_veq]
  | Bool => simp [__smtx_value_eq, native_veq]
  | Int => simp [__smtx_value_eq, native_veq]
  | Real => simp [__smtx_value_eq, native_veq]
  | RegLan =>
      cases v
      case RegLan r =>
        classical
        simp [__smtx_value_eq]
      all_goals
        rw [Smtm.__smtx_value_eq.eq_7]
        · simp [native_veq]
        all_goals
          intro
          simp_all
  | BitVec n => simp [__smtx_value_eq, native_veq]
  | Map T U =>
      cases v
      case Map m =>
        classical
        simp [__smtx_value_eq]
        intro v
        exact smtx_value_eq_refl U (__smtx_msm_lookup T m v)
      all_goals
        rw [Smtm.__smtx_value_eq.eq_7]
        · simp [native_veq]
        all_goals
          intro
          simp_all
  | Set T =>
      cases v
      case Set m =>
        classical
        simp [__smtx_value_eq]
        intro v
        simp [native_veq]
      all_goals
        rw [Smtm.__smtx_value_eq.eq_7]
        · simp [native_veq]
        all_goals
          intro
          simp_all
  | Seq T =>
      cases v
      case Seq s =>
        cases s
        case empty U =>
          simp [__smtx_value_eq]
        case cons v s =>
          simp [__smtx_value_eq, SmtEval.native_and,
            smtx_value_eq_refl T v,
            smtx_value_eq_refl (SmtType.Seq T) (SmtValue.Seq s)]
      all_goals
        rw [Smtm.__smtx_value_eq.eq_7]
        · simp [native_veq]
        all_goals
          intro
          simp_all
  | Char => simp [__smtx_value_eq, native_veq]
  | Datatype s d => simp [__smtx_value_eq, native_veq]
  | TypeRef s => simp [__smtx_value_eq, native_veq]
  | USort n => simp [__smtx_value_eq, native_veq]
  | FunType T U =>
      cases v
      case Fun m =>
        classical
        simp [__smtx_value_eq]
        intro v
        exact smtx_value_eq_refl U (__smtx_msm_lookup T m v)
      all_goals
        rw [Smtm.__smtx_value_eq.eq_7]
        · simp [native_veq]
        all_goals
          intro
          simp_all
  | DtcAppType T U => simp [__smtx_value_eq, native_veq]
termination_by
  (sizeOf T, sizeOf v)
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals first
    | exact Prod.Lex.left _ _ (by
        have hSizeOfT : 0 < sizeOf T := by
          cases T <;> simp <;> omega
        omega)
    | apply Prod.Lex.right
      omega

/-- Symmetry of executable value equality at a fixed SMT type. -/
private theorem smtx_value_eq_symm (T : SmtType) {v1 v2 : SmtValue} :
    __smtx_value_eq T v1 v2 = true ->
      __smtx_value_eq T v2 v1 = true := by
  intro h
  cases T with
  | None =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
  | Bool =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
  | Int =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
  | Real =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
  | RegLan =>
      exact smtx_value_eq_reglan_symm_aux h
  | BitVec n =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
  | Map T U =>
      exact smtx_value_eq_map_symm_aux T U
        (fun h => smtx_value_eq_symm U h) h
  | Set T =>
      exact smtx_value_eq_set_symm_aux T h
  | Seq T =>
      by_cases hv1 : ∃ s1, v1 = SmtValue.Seq s1
      · rcases hv1 with ⟨s1, rfl⟩
        by_cases hv2 : ∃ s2, v2 = SmtValue.Seq s2
        · rcases hv2 with ⟨s2, rfl⟩
          cases s1 with
          | empty T1 =>
              cases s2 with
              | empty T2 =>
                  simp [__smtx_value_eq]
              | cons v2 s2 =>
                  have hFalse : False := by
                    simp [smtx_value_eq_seq_empty_cons_fallback T T1 v2 s2,
                      native_veq] at h
                  exact False.elim hFalse
          | cons v1 s1 =>
              cases s2 with
              | empty T2 =>
                  have hFalse : False := by
                    simp [smtx_value_eq_seq_cons_empty_fallback T v1 s1 T2,
                      native_veq] at h
                  exact False.elim hFalse
              | cons v2 s2 =>
                  simp [__smtx_value_eq, SmtEval.native_and] at h ⊢
                  exact ⟨smtx_value_eq_symm T h.1,
                    smtx_value_eq_symm (SmtType.Seq T) h.2⟩
        · have hNative : native_veq (SmtValue.Seq s1) v2 = true := by
            simpa [smtx_value_eq_seq_fallback_right T
              (v1 := SmtValue.Seq s1) (v2 := v2) (by
                intro s hs
                exact hv2 ⟨s, hs⟩)] using h
          have hEq : SmtValue.Seq s1 = v2 := by
            simpa [native_veq] using hNative
          exact False.elim (hv2 ⟨s1, hEq.symm⟩)
      · have hNative : native_veq v1 v2 = true := by
          simpa [smtx_value_eq_seq_fallback_left T
            (v1 := v1) (v2 := v2) (by
              intro s hs
              exact hv1 ⟨s, hs⟩)] using h
        have hEq : v1 = v2 := by
          simpa [native_veq] using hNative
        subst v2
        rw [smtx_value_eq_seq_fallback_left T (v1 := v1) (v2 := v1) (by
          intro s hs
          exact hv1 ⟨s, hs⟩)]
        simp [native_veq]
  | Char =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
  | Datatype s d =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
  | TypeRef s =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
  | USort n =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
  | FunType T U =>
      exact smtx_value_eq_fun_symm_aux T U
        (fun h => smtx_value_eq_symm U h) h
  | DtcAppType T U =>
      simp [__smtx_value_eq, native_veq] at h ⊢
      exact h.symm
termination_by
  (sizeOf T, sizeOf v1 + sizeOf v2)
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals first
    | exact Prod.Lex.left _ _ (by
        have hSizeOfT : 0 < sizeOf T := by
          cases T <;> simp <;> omega
        omega)
    | apply Prod.Lex.right
      omega

/-- Transitivity of executable value equality at a fixed SMT type. -/
private theorem smtx_value_eq_trans (T : SmtType) {v1 v2 v3 : SmtValue} :
    __smtx_value_eq T v1 v2 = true ->
      __smtx_value_eq T v2 v3 = true ->
        __smtx_value_eq T v1 v3 = true := by
  intro h12 h23
  cases T with
  | None =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
  | Bool =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
  | Int =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
  | Real =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
  | RegLan =>
      exact smtx_value_eq_reglan_trans_aux h12 h23
  | BitVec n =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
  | Map T U =>
      exact smtx_value_eq_map_trans_aux T U
        (fun h12 h23 => smtx_value_eq_trans U h12 h23) h12 h23
  | Set T =>
      exact smtx_value_eq_set_trans_aux T h12 h23
  | Seq T =>
      by_cases hv1 : ∃ s1, v1 = SmtValue.Seq s1
      · rcases hv1 with ⟨s1, rfl⟩
        by_cases hv2 : ∃ s2, v2 = SmtValue.Seq s2
        · rcases hv2 with ⟨s2, rfl⟩
          by_cases hv3 : ∃ s3, v3 = SmtValue.Seq s3
          · rcases hv3 with ⟨s3, rfl⟩
            cases s1 with
            | empty T1 =>
                cases s2 with
                | empty T2 =>
                    cases s3 with
                    | empty T3 =>
                        simp [__smtx_value_eq]
                    | cons v3 s3 =>
                        have hFalse : False := by
                          simp [smtx_value_eq_seq_empty_cons_fallback T T2 v3 s3,
                            native_veq] at h23
                        exact False.elim hFalse
                | cons v2 s2 =>
                    have hFalse : False := by
                      simp [smtx_value_eq_seq_empty_cons_fallback T T1 v2 s2,
                        native_veq] at h12
                    exact False.elim hFalse
            | cons v1 s1 =>
                cases s2 with
                | empty T2 =>
                    have hFalse : False := by
                      simp [smtx_value_eq_seq_cons_empty_fallback T v1 s1 T2,
                        native_veq] at h12
                    exact False.elim hFalse
                | cons v2 s2 =>
                    cases s3 with
                    | empty T3 =>
                        have hFalse : False := by
                          simp [smtx_value_eq_seq_cons_empty_fallback T v2 s2 T3,
                            native_veq] at h23
                        exact False.elim hFalse
                    | cons v3 s3 =>
                        simp [__smtx_value_eq, SmtEval.native_and] at h12 h23 ⊢
                        exact ⟨smtx_value_eq_trans T h12.1 h23.1,
                          smtx_value_eq_trans (SmtType.Seq T) h12.2 h23.2⟩
          · have h23Native : native_veq (SmtValue.Seq s2) v3 = true := by
              simpa [smtx_value_eq_seq_fallback_right T
                (v1 := SmtValue.Seq s2) (v2 := v3) (by
                  intro s hs
                  exact hv3 ⟨s, hs⟩)] using h23
            have hEq : SmtValue.Seq s2 = v3 := by
              simpa [native_veq] using h23Native
            exact False.elim (hv3 ⟨s2, hEq.symm⟩)
        · have h12Native : native_veq (SmtValue.Seq s1) v2 = true := by
            simpa [smtx_value_eq_seq_fallback_right T
              (v1 := SmtValue.Seq s1) (v2 := v2) (by
                intro s hs
                exact hv2 ⟨s, hs⟩)] using h12
          have hEq : SmtValue.Seq s1 = v2 := by
            simpa [native_veq] using h12Native
          exact False.elim (hv2 ⟨s1, hEq.symm⟩)
      · have h12Native : native_veq v1 v2 = true := by
          simpa [smtx_value_eq_seq_fallback_left T
            (v1 := v1) (v2 := v2) (by
              intro s hs
              exact hv1 ⟨s, hs⟩)] using h12
        have hEq12 : v1 = v2 := by
          simpa [native_veq] using h12Native
        subst v2
        have h23Native : native_veq v1 v3 = true := by
          simpa [smtx_value_eq_seq_fallback_left T
            (v1 := v1) (v2 := v3) (by
              intro s hs
              exact hv1 ⟨s, hs⟩)] using h23
        have hEq13 : v1 = v3 := by
          simpa [native_veq] using h23Native
        subst v3
        rw [smtx_value_eq_seq_fallback_left T (v1 := v1) (v2 := v1) (by
          intro s hs
          exact hv1 ⟨s, hs⟩)]
        simp [native_veq]
  | Char =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
  | Datatype s d =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
  | TypeRef s =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
  | USort n =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
  | FunType T U =>
      exact smtx_value_eq_fun_trans_aux T U
        (fun h12 h23 => smtx_value_eq_trans U h12 h23) h12 h23
  | DtcAppType T U =>
      simp [__smtx_value_eq, native_veq] at h12 h23 ⊢
      exact h12.trans h23
termination_by
  (sizeOf T, sizeOf v1 + sizeOf v2 + sizeOf v3)
decreasing_by
  all_goals subst_vars; simp_wf
  all_goals first
    | exact Prod.Lex.left _ _ (by
        have hSizeOfT : 0 < sizeOf T := by
          cases T <;> simp <;> omega
        omega)
    | apply Prod.Lex.right
      omega

/-- Reflexivity for the Apply-aware wrapper used by model equality. -/
private theorem native_apply_veq_refl :
    (v : SmtValue) -> (n : native_Nat) ->
      native_apply_veq __smtx_typeof_value __smtx_value_eq v v n = true
  | SmtValue.NotValue, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Boolean b, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Numeral n, k => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Rational q, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Binary w n, k => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Map m, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Fun m, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Set m, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Seq s, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Char c, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.UValue i e, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.RegLan r, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.DtCons s d i, n => by
      simp [native_apply_veq, SmtEval.native_and, native_Teq, smtx_value_eq_refl]
  | SmtValue.Apply f v, n => by
      simp [native_apply_veq, SmtEval.native_and,
        native_apply_veq_refl f native_nat_zero,
        native_apply_veq_refl v native_nat_zero]
termination_by v n => (sizeOf v, n)
decreasing_by
  all_goals subst_vars; simp_wf; omega

private theorem native_apply_veq_base_symm (v1 v2 : SmtValue) :
    native_and (native_Teq (__smtx_typeof_value v1) (__smtx_typeof_value v2))
        (__smtx_value_eq (__smtx_typeof_value v1) v1 v2) = true ->
    native_and (native_Teq (__smtx_typeof_value v2) (__smtx_typeof_value v1))
        (__smtx_value_eq (__smtx_typeof_value v2) v2 v1) = true := by
  intro h
  by_cases hTy : __smtx_typeof_value v1 = __smtx_typeof_value v2
  · have hEq : __smtx_value_eq (__smtx_typeof_value v1) v1 v2 = true := by
      simpa [SmtEval.native_and, native_Teq, hTy] using h
    simp [SmtEval.native_and, native_Teq, hTy.symm]
    exact smtx_value_eq_symm (__smtx_typeof_value v1) hEq
  · exact False.elim (by
      simp [SmtEval.native_and, native_Teq, hTy] at h)

private theorem native_apply_veq_base_trans (v1 v2 v3 : SmtValue) :
    native_and (native_Teq (__smtx_typeof_value v1) (__smtx_typeof_value v2))
        (__smtx_value_eq (__smtx_typeof_value v1) v1 v2) = true ->
    native_and (native_Teq (__smtx_typeof_value v2) (__smtx_typeof_value v3))
        (__smtx_value_eq (__smtx_typeof_value v2) v2 v3) = true ->
    native_and (native_Teq (__smtx_typeof_value v1) (__smtx_typeof_value v3))
        (__smtx_value_eq (__smtx_typeof_value v1) v1 v3) = true := by
  intro h12 h23
  by_cases hTy12 : __smtx_typeof_value v1 = __smtx_typeof_value v2
  · by_cases hTy23 : __smtx_typeof_value v2 = __smtx_typeof_value v3
    · have hEq12 : __smtx_value_eq (__smtx_typeof_value v1) v1 v2 = true := by
        simpa [SmtEval.native_and, native_Teq, hTy12] using h12
      have hEq23 : __smtx_value_eq (__smtx_typeof_value v1) v2 v3 = true := by
        simpa [SmtEval.native_and, native_Teq, hTy23, hTy12] using h23
      simp [SmtEval.native_and, native_Teq, hTy12.trans hTy23]
      rw [← hTy12.trans hTy23]
      exact smtx_value_eq_trans (__smtx_typeof_value v1) hEq12 hEq23
    · simp [SmtEval.native_and, native_Teq, hTy23] at h23
  · simp [SmtEval.native_and, native_Teq, hTy12] at h12

/-- Symmetry for the Apply-aware wrapper used by model equality. -/
private theorem native_apply_veq_symm :
    (v1 v2 : SmtValue) -> (n n' : native_Nat) ->
      native_apply_veq __smtx_typeof_value __smtx_value_eq v1 v2 n = true ->
      native_apply_veq __smtx_typeof_value __smtx_value_eq v2 v1 n' = true
  | v1, v2, n, n', h => by
    cases v1 <;> cases v2
    case Apply.Apply f1 v1 f2 v2 =>
      simp [native_apply_veq, SmtEval.native_and] at h ⊢
      exact ⟨native_apply_veq_symm f1 f2 native_nat_zero native_nat_zero h.1,
        native_apply_veq_symm v1 v2 native_nat_zero native_nat_zero h.2⟩
    all_goals
      simpa [native_apply_veq] using
        native_apply_veq_base_symm _ _ (by
          simpa [native_apply_veq] using h)
termination_by v1 v2 n n' => sizeOf v1 + sizeOf v2
decreasing_by
  all_goals subst_vars; simp_wf; omega

/-- Transitivity for the Apply-aware wrapper used by model equality. -/
private theorem native_apply_veq_trans :
    (v1 v2 v3 : SmtValue) -> (n12 n23 n13 : native_Nat) ->
      native_apply_veq __smtx_typeof_value __smtx_value_eq v1 v2 n12 = true ->
      native_apply_veq __smtx_typeof_value __smtx_value_eq v2 v3 n23 = true ->
      native_apply_veq __smtx_typeof_value __smtx_value_eq v1 v3 n13 = true
  | v1, v2, v3, n12, n23, n13, h12, h23 => by
    cases v1 <;> cases v2 <;> cases v3
    case Apply.Apply.Apply f1 v1 f2 v2 f3 v3 =>
      simp [native_apply_veq, SmtEval.native_and] at h12 h23 ⊢
      exact ⟨native_apply_veq_trans f1 f2 f3 native_nat_zero native_nat_zero native_nat_zero h12.1 h23.1,
        native_apply_veq_trans v1 v2 v3 native_nat_zero native_nat_zero native_nat_zero h12.2 h23.2⟩
    all_goals first
    | simpa [native_apply_veq] using native_apply_veq_base_trans _ _ _
        (by simpa [native_apply_veq] using h12)
        (by simpa [native_apply_veq] using h23)
    | simp [native_apply_veq, SmtEval.native_and, native_Teq,
        __smtx_value_eq, native_veq] at h12 h23
    | simp [native_apply_veq, SmtEval.native_and, native_Teq,
        __smtx_value_eq, native_veq]
termination_by v1 v2 v3 n12 n23 n13 => sizeOf v1 + sizeOf v2 + sizeOf v3
decreasing_by
  all_goals subst_vars; simp_wf; omega

/-- Reflexivity for the executable value equality at an explicit comparison type. -/
@[simp] theorem smtx_value_eq_refl_typed (T : SmtType) (v : SmtValue) :
    __smtx_value_eq T v v = true :=
  smtx_value_eq_refl T v

/-- Symmetry for executable value equality at an explicit comparison type. -/
theorem smtx_value_eq_symm_typed (T : SmtType) {v1 v2 : SmtValue} :
    __smtx_value_eq T v1 v2 = true ->
    __smtx_value_eq T v2 v1 = true :=
  smtx_value_eq_symm T

/-- Transitivity for executable value equality at an explicit comparison type. -/
theorem smtx_value_eq_trans_typed (T : SmtType) {v1 v2 v3 : SmtValue} :
    __smtx_value_eq T v1 v2 = true ->
    __smtx_value_eq T v2 v3 = true ->
    __smtx_value_eq T v1 v3 = true :=
  smtx_value_eq_trans T

/-- Reflexivity lemma for `smt_value_rel`. -/
theorem smt_value_rel_refl (v : SmtValue) : smt_value_rel v v :=
  by
    unfold smt_value_rel __smtx_model_eval_eq
    rw [native_apply_veq_refl]

/-- Reflexivity lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_refl (s : SmtSeq) : smt_seq_rel s s :=
  by
    unfold smt_seq_rel __smtx_model_eval_eq
    rw [native_apply_veq_refl]

/-- Symmetry lemma for `smt_value_rel`. -/
theorem smt_value_rel_symm (v1 v2 : SmtValue) :
    __smtx_typeof_value v1 = __smtx_typeof_value v2 ->
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v1 := by
  intro _hTy hRel
  simp [smt_value_rel, __smtx_model_eval_eq] at hRel ⊢
  exact native_apply_veq_symm v1 v2 _ _ hRel

/-- Symmetry lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_symm (s1 s2 : SmtSeq) :
    __smtx_typeof_seq_value s1 = __smtx_typeof_seq_value s2 ->
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s1 := by
  intro hTy hRel
  exact smt_value_rel_symm (SmtValue.Seq s1) (SmtValue.Seq s2)
    (by simpa [__smtx_typeof_value] using hTy) hRel

/-- Transitivity lemma for `smt_value_rel`. -/
theorem smt_value_rel_trans (v1 v2 v3 : SmtValue) :
    __smtx_typeof_value v1 = __smtx_typeof_value v2 ->
    __smtx_typeof_value v2 = __smtx_typeof_value v3 ->
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v3 ->
    smt_value_rel v1 v3 := by
  intro _hTy12 _hTy23 h12 h23
  simp [smt_value_rel, __smtx_model_eval_eq] at h12 h23 ⊢
  exact native_apply_veq_trans v1 v2 v3 _ _ _ h12 h23

/-- Transitivity lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_trans (s1 s2 s3 : SmtSeq) :
    __smtx_typeof_seq_value s1 = __smtx_typeof_seq_value s2 ->
    __smtx_typeof_seq_value s2 = __smtx_typeof_seq_value s3 ->
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s3 ->
    smt_seq_rel s1 s3 := by
  intro hTy12 hTy23 h12 h23
  exact smt_value_rel_trans (SmtValue.Seq s1) (SmtValue.Seq s2) (SmtValue.Seq s3)
    (by simpa [__smtx_typeof_value] using hTy12)
    (by simpa [__smtx_typeof_value] using hTy23) h12 h23

/-- Characterizes `smt_value_rel` in terms of `model_eval_eq_true`. -/
theorem smt_value_rel_iff_model_eval_eq_true
    (v1 : SmtValue) (v2 : SmtValue) :
    smt_value_rel v1 v2 ↔ __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true :=
  Iff.rfl

/-- Characterizes `smt_seq_rel` in terms of `model_eval_eq_true`. -/
theorem smt_seq_rel_iff_model_eval_eq_true
    (s1 : SmtSeq) (s2 : SmtSeq) :
    smt_seq_rel s1 s2 ↔
      __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true :=
  Iff.rfl

/-- Computes `__smtx_typeof` for `eq_bool_iff`. -/
theorem smtx_typeof_eq_bool_iff (T U : SmtType) :
  __smtx_typeof_eq T U = SmtType.Bool ↔ T = U ∧ T ≠ SmtType.None := by
  unfold __smtx_typeof_eq __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · subst hT
    simp [native_ite, native_Teq]
  · by_cases hEq : T = U
    · subst hEq
      simp [native_ite, native_Teq, hT]
    · simp [native_ite, native_Teq, hEq, hT]

/-- Derives `eo_eq_operands_same_smt_type` from `has_bool_type`. -/
theorem eo_eq_operands_same_smt_type_of_has_bool_type (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTy
  unfold eo_has_bool_type at hTy
  rw [eo_to_smt_eq_eq x y] at hTy
  rw [Smtm.__smtx_typeof.eq_11] at hTy
  exact (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
    (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_has_bool_type_eq` from `same_smt_type`. -/
theorem eo_has_bool_type_eq_of_same_smt_type (x y : Term) :
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ->
  __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) := by
  intro hTy hNonNone
  unfold eo_has_bool_type
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x))
      (__smtx_typeof (__eo_to_smt y))).mpr ⟨hTy, hNonNone⟩
  rw [eo_to_smt_eq_eq x y]
  rw [Smtm.__smtx_typeof.eq_11]
  exact hEqTy

/-- Symmetry lemma for `eo_has_bool_type_eq`. -/
theorem eo_has_bool_type_eq_symm (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) := by
  intro hTy
  rcases eo_eq_operands_same_smt_type_of_has_bool_type x y hTy with ⟨hEq, hNonNone⟩
  have hNonNone' : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    simpa [hEq] using hNonNone
  exact eo_has_bool_type_eq_of_same_smt_type y x hEq.symm hNonNone'

/-- Derives `eo_has_bool_type_eq` from `bool_chain`. -/
theorem eo_has_bool_type_eq_of_bool_chain (x y z : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) := by
  intro hXY hYZ
  rcases eo_eq_operands_same_smt_type_of_has_bool_type x y hXY with ⟨hTyXY, hNonNone⟩
  rcases eo_eq_operands_same_smt_type_of_has_bool_type y z hYZ with ⟨hTyYZ, _⟩
  have hTyXZ : __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt z) := by
    rw [hTyXY, hTyYZ]
  exact eo_has_bool_type_eq_of_same_smt_type x z hTyXZ hNonNone

/-- Establishes an equality relating `eo` and `operands_same_smt_type`. -/
theorem eo_eq_operands_same_smt_type (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hEq
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_true hTy _ =>
      rw [Smtm.__smtx_typeof.eq_11] at hTy
      exact (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_eq_operands_same_smt_type` from `false`. -/
theorem eo_eq_operands_same_smt_type_of_false (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) false ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hEq
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_false hTy _ =>
      rw [Smtm.__smtx_typeof.eq_11] at hTy
      exact (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_has_bool_type_eq` from `true_chain`. -/
theorem eo_has_bool_type_eq_of_true_chain (M : SmtModel) (x y z : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) true ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) := by
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
  rw [eo_to_smt_eq_eq x z]
  rw [Smtm.__smtx_typeof.eq_11]
  exact hEqTy

/-- Derives `eo_has_bool_type_eq` from `true`. -/
theorem eo_has_bool_type_eq_of_true (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) := by
  intro hXY
  rcases eo_eq_operands_same_smt_type M x y hXY with ⟨hTyXY, hNonNone⟩
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x)) (__smtx_typeof (__eo_to_smt y))).mpr ⟨hTyXY, hNonNone⟩
  unfold eo_has_bool_type
  rw [eo_to_smt_eq_eq x y]
  rw [Smtm.__smtx_typeof.eq_11]
  exact hEqTy

/-- Establishes an equality relating `eo_interprets` and `rel`. -/
theorem eo_interprets_eq_rel (M : SmtModel) (x y : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  smt_value_rel (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hEq
  rw [smt_value_rel_iff_model_eval_eq_true]
  rw [eo_interprets_iff_smt_interprets] at hEq
  rw [eo_to_smt_eq_eq x y] at hEq
  cases hEq with
  | intro_true _ hEval =>
      rw [Smtm.__smtx_model_eval.eq_11] at hEval
      exact hEval

/-- Derives `eo_interprets_eq` from `rel`. -/
theorem eo_interprets_eq_of_rel (M : SmtModel) (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) ->
  smt_value_rel (__smtx_model_eval M (__eo_to_smt x))
    (__smtx_model_eval M (__eo_to_smt y)) ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true := by
  intro hTy hRel
  rw [eo_interprets_iff_smt_interprets]
  rw [eo_to_smt_eq_eq x y]
  refine smt_interprets.intro_true M (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) ?_ ?_
  · simpa [eo_has_bool_type, eo_to_smt_eq_eq x y] using hTy
  · have hEvalEq :
        __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean true :=
      (smt_value_rel_iff_model_eval_eq_true
        (__smtx_model_eval M (__eo_to_smt x))
        (__smtx_model_eval M (__eo_to_smt y))).mp hRel
    simpa [Smtm.__smtx_model_eval.eq_11] using hEvalEq

/-- Transitivity lemma for `eo_interprets_eq`. -/
theorem eo_interprets_eq_trans (M : SmtModel) (hM : model_total_typed M) (x y z : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) z) true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) z) true := by
  intro hXY hYZ
  rcases eo_eq_operands_same_smt_type M x y hXY with ⟨hTyXY, hXNonNone⟩
  rcases eo_eq_operands_same_smt_type M y z hYZ with ⟨hTyYZ, _⟩
  have hYNonNone : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    simpa [← hTyXY] using hXNonNone
  have hZNonNone : __smtx_typeof (__eo_to_smt z) ≠ SmtType.None := by
    simpa [← hTyYZ] using hYNonNone
  have hEvalTyXY :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) := by
    rw [type_preservation M hM (__eo_to_smt x) (by
        unfold term_has_non_none_type
        exact hXNonNone),
      type_preservation M hM (__eo_to_smt y) (by
        unfold term_has_non_none_type
        exact hYNonNone),
      hTyXY]
  have hEvalTyYZ :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt y)) =
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt z)) := by
    rw [type_preservation M hM (__eo_to_smt y) (by
        unfold term_has_non_none_type
        exact hYNonNone),
      type_preservation M hM (__eo_to_smt z) (by
        unfold term_has_non_none_type
        exact hZNonNone),
      hTyYZ]
  apply eo_interprets_eq_of_rel M x z
  · exact eo_has_bool_type_eq_of_true_chain M x y z hXY hYZ
  · exact smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt z))
      hEvalTyXY
      hEvalTyYZ
      (eo_interprets_eq_rel M x y hXY)
      (eo_interprets_eq_rel M y z hYZ)

/-- Derives `eo_interprets_not` from `false`. -/
theorem eo_interprets_not_of_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> eo_interprets M (Term.Apply (Term.UOp UserOp.not) t) true := by
  intro hFalse
  rw [eo_interprets_iff_smt_interprets] at hFalse ⊢
  rw [eo_to_smt_not_eq t]
  cases hFalse with
  | intro_false hTy hEval =>
      refine smt_interprets.intro_true M
          (SmtTerm.not (__eo_to_smt t)) ?_ ?_
      · simp [Smtm.__smtx_typeof.eq_6, hTy, native_Teq, native_ite]
      · simp [Smtm.__smtx_model_eval.eq_6, __smtx_model_eval_not, SmtEval.native_not, hEval]

/-- Derives `term_ne_stuck` from `interprets_true`. -/
theorem term_ne_stuck_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq] at h
  cases h with
  | intro_true hTy _ =>
      have : SmtType.None = SmtType.Bool := by
        simp [Smtm.__smtx_typeof.eq_def] at hTy
      cases this

/-- Derives `term_ne_stuck` from `interprets_false`. -/
theorem term_ne_stuck_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_stuck_eq] at h
  cases h with
  | intro_false hTy _ =>
      have : SmtType.None = SmtType.Bool := by
        simp [Smtm.__smtx_typeof.eq_def] at hTy
      cases this

/-- Derives `term_ne_stuck` from `has_bool_type`. -/
theorem term_ne_stuck_of_has_bool_type (t : Term) :
  eo_has_bool_type t -> t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  rw [eo_has_bool_type, eo_to_smt_stuck_eq] at hTy
  have : SmtType.None = SmtType.Bool := by
    simp [Smtm.__smtx_typeof.eq_def] at hTy
  cases this

set_option linter.unusedSimpArgs false in
/-- Shows that `eo_interprets_not_true` implies `false`. -/
theorem eo_interprets_not_true_implies_false (M : SmtModel) (t : Term) :
  eo_interprets M (Term.Apply (Term.UOp UserOp.not) t) true -> eo_interprets M t false := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h ⊢
  rw [eo_to_smt_not_eq t] at h
  cases h with
  | intro_true hty hEval =>
      have htyt : __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
        rw [Smtm.__smtx_typeof.eq_6] at hty
        simpa [native_Teq, native_ite] using hty
      rw [Smtm.__smtx_model_eval.eq_6] at hEval
      cases ht : __smtx_model_eval M (__eo_to_smt t) with
      | NotValue =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Boolean b =>
          cases b with
          | false =>
              exact smt_interprets.intro_false M (__eo_to_smt t) htyt ht
          | true =>
              exfalso
              simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Numeral n =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Rational q =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Binary w n =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Map m =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Fun m =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Set m =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Seq s =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Char c =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | UValue s i =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | RegLan r =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | DtCons s d i =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval
      | Apply f x =>
          exfalso
          simp [__smtx_model_eval_not, ht, SmtEval.native_not] at hEval

/-- Computes `__smtx_typeof` for `eq_refl`. -/
theorem smtx_typeof_eq_refl (T : SmtType) :
  T ≠ SmtType.None -> __smtx_typeof_eq T T = SmtType.Bool := by
  intro hT
  unfold __smtx_typeof_eq __smtx_typeof_guard
  simp [native_ite, native_Teq, hT]

/-- Reflexivity lemma for `smtx_model_eval_eq`. -/
theorem smtx_model_eval_eq_refl (v : SmtValue) :
  __smtx_model_eval_eq v v = SmtValue.Boolean true := by
  exact (smt_value_rel_iff_model_eval_eq_true v v).mp (smt_value_rel_refl v)

end RuleProofs
