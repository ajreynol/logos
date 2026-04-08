import CpcMicro.Proofs.TypePreservation
import CpcMicro.Proofs.Translation

open Eo
open Smtm

namespace RuleProofs

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

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
  rw [eo_interprets_iff_smt_interprets]
  exact smt_interprets.intro_true M (__eo_to_smt (Term.Boolean true)) rfl rfl

/-- Predicate asserting that translating an EO term yields a non-`None` SMT term. -/
def eo_has_smt_translation (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) ≠ SmtType.None

/-- Predicate asserting that an EO term translates to SMT Boolean type. -/
def eo_has_bool_type (t : Term) : Prop :=
  __smtx_typeof (__eo_to_smt t) = SmtType.Bool

/-- Shows that `Term.Boolean true` has an SMT translation. -/
theorem eo_has_smt_translation_true :
  eo_has_smt_translation (Term.Boolean true) := by
  simp [eo_has_smt_translation, __eo_to_smt, __smtx_typeof]

/-- Shows that `Term.Boolean true` has translated SMT Boolean type. -/
theorem eo_has_bool_type_true :
  eo_has_bool_type (Term.Boolean true) := by
  simp [eo_has_bool_type, __eo_to_smt, __smtx_typeof]

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

/-- Shows that `eo_to_smt_non_none_and_typeof_bool` implies `smt_bool`. -/
theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = Term.Bool ->
  __smtx_typeof s = SmtType.Bool := by
  intro hs hS hTy
  exact TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
    t Term.Bool s hs hS hTy

/-- Shows that `eo_typeof_bool` implies `has_bool_type`. -/
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
  simp [eo_has_smt_translation, __eo_to_smt, __smtx_typeof] at hTy

/-- Derives `eo_has_bool_type_and` from `bool_args`. -/
theorem eo_has_bool_type_and_of_bool_args (A B : Term) :
  eo_has_bool_type A ->
  eo_has_bool_type B ->
  eo_has_bool_type (Term.Apply (Term.Apply Term.and A) B) := by
  intro hA hB
  unfold eo_has_bool_type at hA hB ⊢
  simp [__eo_to_smt, __smtx_typeof, hA, hB, smt_lit_ite, smt_lit_Teq]

/-- Left-projection lemma for `eo_has_bool_type_and`. -/
theorem eo_has_bool_type_and_left (A B : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply Term.and A) B) ->
  eo_has_bool_type A := by
  intro hTy
  by_cases hA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool
  · simpa [eo_has_bool_type] using hA
  · have : False := by
      simp [eo_has_bool_type, __eo_to_smt, __smtx_typeof, hA,
        smt_lit_ite, smt_lit_Teq] at hTy
    exact False.elim this

/-- Right-projection lemma for `eo_has_bool_type_and`. -/
theorem eo_has_bool_type_and_right (A B : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply Term.and A) B) ->
  eo_has_bool_type B := by
  intro hTy
  have hA : __smtx_typeof (__eo_to_smt A) = SmtType.Bool := by
    exact eo_has_bool_type_and_left A B hTy
  by_cases hB : __smtx_typeof (__eo_to_smt B) = SmtType.Bool
  · simpa [eo_has_bool_type] using hB
  · have : False := by
      simp [eo_has_bool_type, __eo_to_smt, __smtx_typeof, hA, hB,
        smt_lit_ite, smt_lit_Teq] at hTy
    exact False.elim this

/-- Derives `eo_has_bool_type_not` from `bool_arg`. -/
theorem eo_has_bool_type_not_of_bool_arg (t : Term) :
  eo_has_bool_type t ->
  eo_has_bool_type (Term.Apply Term.not t) := by
  intro hTy
  simpa [eo_has_bool_type, __eo_to_smt, __smtx_typeof, hTy,
    smt_lit_ite, smt_lit_Teq]

/-- Shows that a translated `not` term can only be Boolean when its argument is Boolean. -/
theorem eo_has_bool_type_not_arg (t : Term) :
  eo_has_bool_type (Term.Apply Term.not t) ->
  eo_has_bool_type t := by
  intro hTy
  by_cases hT : __smtx_typeof (__eo_to_smt t) = SmtType.Bool
  · simpa [eo_has_bool_type] using hT
  · have : False := by
      simp [eo_has_bool_type, __eo_to_smt, __smtx_typeof, hT,
        smt_lit_ite, smt_lit_Teq] at hTy
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

/-- Shows that an EO term cannot be interpreted as both `true` and `false`. -/
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

/-- Right-projection lemma for `eo_interprets_and`. -/
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

/-- Introduction lemma for `eo_interprets_and`. -/
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

/-- Semantic equality relation on SMT values, defined by evaluation of SMT equality. -/
def smt_value_rel (v1 v2 : SmtValue) : Prop :=
  __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true

/-- Semantic equality relation on SMT sequences, lifted through `SmtValue.Seq`. -/
def smt_seq_rel (s1 s2 : SmtSeq) : Prop :=
  __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true

mutual

/-- Establishes an equality relating `smtx_model_eval` and `refl_aux`. -/
private theorem smtx_model_eval_eq_refl_aux :
    (v : SmtValue) -> __smtx_model_eval_eq v v = SmtValue.Boolean true
  | SmtValue.Map _ => by
      simp [__smtx_model_eval_eq]
  | SmtValue.Set _ => by
      simp [__smtx_model_eval_eq]
  | SmtValue.Seq s => by
      simpa using smtx_model_eval_seq_eq_refl_aux s
  | SmtValue.NotValue => by
      simp [__smtx_model_eval_eq, smt_lit_veq]
  | SmtValue.Boolean _ => by
      simp [__smtx_model_eval_eq, smt_lit_veq]
  | SmtValue.Numeral _ => by
      simp [__smtx_model_eval_eq, smt_lit_veq]
  | SmtValue.Rational _ => by
      simp [__smtx_model_eval_eq, smt_lit_veq]
  | SmtValue.Binary _ _ => by
      simp [__smtx_model_eval_eq, smt_lit_veq]
  | SmtValue.Char _ => by
      simp [__smtx_model_eval_eq, smt_lit_veq]
  | SmtValue.RegLan _ => by
      simp [__smtx_model_eval_eq, smt_lit_veq]

/-- Establishes an equality relating `smtx_model_eval_seq` and `refl_aux`. -/
private theorem smtx_model_eval_seq_eq_refl_aux :
    (s : SmtSeq) -> __smtx_model_eval_eq (SmtValue.Seq s) (SmtValue.Seq s) = SmtValue.Boolean true
  | SmtSeq.empty _ => by
      simp [__smtx_model_eval_eq]
  | SmtSeq.cons v s => by
      simp [__smtx_model_eval_eq, smt_lit_veq, SmtEval.smt_lit_and,
        smtx_model_eval_eq_refl_aux v, smtx_model_eval_seq_eq_refl_aux s]
end

mutual

/-- Establishes an equality relating `smtx_model_eval` and `true_symm`. -/
private theorem smtx_model_eval_eq_true_symm
    {v1 v2 : SmtValue}
    (h : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true) :
    __smtx_model_eval_eq v2 v1 = SmtValue.Boolean true := by
  cases v1 <;> cases v2
  case Map.Map m1 m2 =>
    classical
    simp [__smtx_model_eval_eq] at h ⊢
    intro v
    symm
    exact h v
  case Set.Set m1 m2 =>
    classical
    simp [__smtx_model_eval_eq] at h ⊢
    intro v
    symm
    exact h v
  case Seq.Seq s1 s2 =>
    simpa using smtx_model_eval_seq_eq_true_symm h
  all_goals
    simp [__smtx_model_eval_eq, smt_lit_veq] at h ⊢
    try exact h
    try exact h.symm
    try exact ⟨h.1.symm, h.2.symm⟩
    try exact False.elim h

/-- Establishes an equality relating `smtx_model_eval_seq` and `true_symm`. -/
private theorem smtx_model_eval_seq_eq_true_symm
    {s1 s2 : SmtSeq}
    (h : __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true) :
    __smtx_model_eval_eq (SmtValue.Seq s2) (SmtValue.Seq s1) = SmtValue.Boolean true := by
  cases s1 <;> cases s2
  case cons.cons v1 s1 v2 s2 =>
    simp [__smtx_model_eval_eq, smt_lit_veq, SmtEval.smt_lit_and] at h ⊢
    exact ⟨smtx_model_eval_eq_true_symm h.1, smtx_model_eval_seq_eq_true_symm h.2⟩
  case empty.empty T1 T2 =>
    simp [__smtx_model_eval_eq]
  all_goals
    simp [__smtx_model_eval_eq, smt_lit_veq] at h

end

mutual

/-- Establishes an equality relating `smtx_model_eval` and `true_trans`. -/
private theorem smtx_model_eval_eq_true_trans
    {v1 v2 v3 : SmtValue}
    (h12 : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true)
    (h23 : __smtx_model_eval_eq v2 v3 = SmtValue.Boolean true) :
    __smtx_model_eval_eq v1 v3 = SmtValue.Boolean true := by
  cases v1 <;> cases v2 <;> cases v3
  case Map.Map.Map m1 m2 m3 =>
    classical
    simp [__smtx_model_eval_eq] at h12 h23 ⊢
    intro v
    calc
      __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v := h12 v
      _ = __smtx_msm_lookup m3 v := h23 v
  case Set.Set.Set m1 m2 m3 =>
    classical
    simp [__smtx_model_eval_eq] at h12 h23 ⊢
    intro v
    calc
      __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v := h12 v
      _ = __smtx_msm_lookup m3 v := h23 v
  case Seq.Seq.Seq s1 s2 s3 =>
    simpa using smtx_model_eval_seq_eq_true_trans h12 h23
  all_goals
    simp [__smtx_model_eval_eq, smt_lit_veq] at h12 h23 ⊢
    try exact h12.trans h23
    try exact ⟨h12.1.trans h23.1, h12.2.trans h23.2⟩
    try exact False.elim h12
    try exact False.elim h23
    try trivial

/-- Establishes an equality relating `smtx_model_eval_seq` and `true_trans`. -/
private theorem smtx_model_eval_seq_eq_true_trans
    {s1 s2 s3 : SmtSeq}
    (h12 : __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true)
    (h23 : __smtx_model_eval_eq (SmtValue.Seq s2) (SmtValue.Seq s3) = SmtValue.Boolean true) :
    __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s3) = SmtValue.Boolean true := by
  cases s1 <;> cases s2 <;> cases s3
  case cons.cons.cons v1 s1 v2 s2 v3 s3 =>
    simp [__smtx_model_eval_eq, smt_lit_veq, SmtEval.smt_lit_and] at h12 h23 ⊢
    exact ⟨smtx_model_eval_eq_true_trans h12.1 h23.1,
      smtx_model_eval_seq_eq_true_trans h12.2 h23.2⟩
  case empty.empty.empty T1 T2 T3 =>
    simp [__smtx_model_eval_eq]
  all_goals
    simp [__smtx_model_eval_eq, smt_lit_veq] at h12 h23
    try exact False.elim h12
    try exact False.elim h23

end

/-- Reflexivity lemma for `smt_value_rel`. -/
theorem smt_value_rel_refl (v : SmtValue) : smt_value_rel v v :=
  smtx_model_eval_eq_refl_aux v

/-- Reflexivity lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_refl (s : SmtSeq) : smt_seq_rel s s :=
  smtx_model_eval_seq_eq_refl_aux s

/-- Symmetry lemma for `smt_value_rel`. -/
theorem smt_value_rel_symm (v1 v2 : SmtValue) :
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v1 :=
  smtx_model_eval_eq_true_symm

/-- Symmetry lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_symm (s1 s2 : SmtSeq) :
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s1 :=
  smtx_model_eval_seq_eq_true_symm

/-- Transitivity lemma for `smt_value_rel`. -/
theorem smt_value_rel_trans (v1 v2 v3 : SmtValue) :
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v3 ->
    smt_value_rel v1 v3 :=
  smtx_model_eval_eq_true_trans

/-- Transitivity lemma for `smt_seq_rel`. -/
theorem smt_seq_rel_trans (s1 s2 s3 : SmtSeq) :
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s3 ->
    smt_seq_rel s1 s3 :=
  smtx_model_eval_seq_eq_true_trans

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

/-- Establishes an equality relating `smtx_typeof` and `bool_iff`. -/
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

/-- Derives `eo_eq_operands_same_smt_type` from `has_bool_type`. -/
theorem eo_eq_operands_same_smt_type_of_has_bool_type (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) y) ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTy
  unfold eo_has_bool_type at hTy
  simpa [__eo_to_smt, __smtx_typeof] using
    (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
      (__smtx_typeof (__eo_to_smt y))).mp hTy

/-- Derives `eo_has_bool_type_eq` from `same_smt_type`. -/
theorem eo_has_bool_type_eq_of_same_smt_type (x y : Term) :
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ->
  __smtx_typeof (__eo_to_smt x) ≠ SmtType.None ->
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) y) := by
  intro hTy hNonNone
  unfold eo_has_bool_type
  have hEqTy :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
        (__smtx_typeof (__eo_to_smt y)) = SmtType.Bool := by
    exact (smtx_typeof_eq_bool_iff
      (__smtx_typeof (__eo_to_smt x))
      (__smtx_typeof (__eo_to_smt y))).mpr ⟨hTy, hNonNone⟩
  simpa [__eo_to_smt, __smtx_typeof] using hEqTy

/-- Establishes an equality relating `eo_has_bool_type` and `symm`. -/
theorem eo_has_bool_type_eq_symm (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) y) ->
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq y) x) := by
  intro hTy
  rcases eo_eq_operands_same_smt_type_of_has_bool_type x y hTy with ⟨hEq, hNonNone⟩
  have hNonNone' : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    simpa [hEq] using hNonNone
  exact eo_has_bool_type_eq_of_same_smt_type y x hEq.symm hNonNone'

/-- Derives `eo_has_bool_type_eq` from `bool_chain`. -/
theorem eo_has_bool_type_eq_of_bool_chain (x y z : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) y) ->
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq y) z) ->
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) z) := by
  intro hXY hYZ
  rcases eo_eq_operands_same_smt_type_of_has_bool_type x y hXY with ⟨hTyXY, hNonNone⟩
  rcases eo_eq_operands_same_smt_type_of_has_bool_type y z hYZ with ⟨hTyYZ, _⟩
  have hTyXZ : __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt z) := by
    rw [hTyXY, hTyYZ]
  exact eo_has_bool_type_eq_of_same_smt_type x z hTyXZ hNonNone

/-- Establishes an equality relating `eo` and `operands_same_smt_type`. -/
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

/-- Derives `eo_eq_operands_same_smt_type` from `false`. -/
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

/-- Derives `eo_has_bool_type_eq` from `true_chain`. -/
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

/-- Derives `eo_has_bool_type_eq` from `true`. -/
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

/-- Establishes an equality relating `eo_interprets` and `rel`. -/
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

/-- Derives `eo_interprets_eq` from `rel`. -/
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

/-- Establishes an equality relating `eo_interprets` and `trans`. -/
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

/-- Derives `eo_interprets_not` from `false`. -/
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

/-- Derives `term_ne_stuck` from `interprets_true`. -/
theorem term_ne_stuck_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets] at h
  cases h with
  | intro_true hTy _ =>
      simp [__eo_to_smt, __smtx_typeof] at hTy

/-- Derives `term_ne_stuck` from `interprets_false`. -/
theorem term_ne_stuck_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false -> t ≠ Term.Stuck := by
  intro h hStuck
  subst hStuck
  rw [eo_interprets_iff_smt_interprets] at h
  cases h with
  | intro_false hTy _ =>
      simp [__eo_to_smt, __smtx_typeof] at hTy

/-- Derives `term_ne_stuck` from `has_bool_type`. -/
theorem term_ne_stuck_of_has_bool_type (t : Term) :
  eo_has_bool_type t -> t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  simp [eo_has_bool_type, __eo_to_smt, __smtx_typeof] at hTy

set_option linter.unusedSimpArgs false in
/-- Shows that `eo_interprets_not_true` implies `false`. -/
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

/-- Establishes an equality relating `smtx_typeof` and `refl`. -/
theorem smtx_typeof_eq_refl (T : SmtType) :
  T ≠ SmtType.None -> __smtx_typeof_eq T T = SmtType.Bool := by
  intro hT
  unfold __smtx_typeof_eq __smtx_typeof_guard
  simp [smt_lit_ite, smt_lit_Teq, hT]

/-- Establishes an equality relating `smtx_model_eval` and `refl`. -/
theorem smtx_model_eval_eq_refl (v : SmtValue) :
  __smtx_model_eval_eq v v = SmtValue.Boolean true := by
  exact (smt_value_rel_iff_model_eval_eq_true v v).mp (smt_value_rel_refl v)

end RuleProofs
