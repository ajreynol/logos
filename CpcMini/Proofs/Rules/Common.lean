import CpcMini.Proofs.Unproven

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

structure RuleResultFacts (M : SmtModel) (P : Term) : Prop where
  true_in_model : eo_interprets M P true
  has_smt_translation : eo_has_smt_translation P

theorem eo_has_smt_translation_true :
  eo_has_smt_translation (Term.Boolean true) := by
  simp [eo_has_smt_translation, __eo_to_smt, __smtx_typeof]

theorem eo_has_bool_type_true :
  eo_has_bool_type (Term.Boolean true) := by
  simp [eo_has_bool_type, __eo_to_smt, __smtx_typeof]

theorem eo_has_bool_type_of_interprets_true (M : SmtModel) (t : Term) :
  eo_interprets M t true ->
  eo_has_bool_type t := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_true hTy _ =>
      simpa [eo_has_bool_type] using hTy

theorem eo_has_bool_type_of_interprets_false (M : SmtModel) (t : Term) :
  eo_interprets M t false ->
  eo_has_bool_type t := by
  rw [eo_interprets_iff_smt_interprets]
  intro h
  cases h with
  | intro_false hTy _ =>
      simpa [eo_has_bool_type] using hTy

theorem eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    (t : Term) (s : SmtTerm) :
  __eo_to_smt t = s ->
  __smtx_typeof s ≠ SmtType.None ->
  __eo_typeof t = Term.Bool ->
  __smtx_typeof s = SmtType.Bool := by
  intro hs hS hTy
  exact eo_to_smt_well_typed_and_typeof_implies_smt_type
    t Term.Bool s hs hS hTy

theorem eo_typeof_bool_implies_has_bool_type
    (t : Term) :
  eo_has_smt_translation t ->
  __eo_typeof t = Term.Bool ->
  eo_has_bool_type t := by
  intro hTrans hTy
  exact eo_to_smt_non_none_and_typeof_bool_implies_smt_bool
    t (__eo_to_smt t) rfl hTrans hTy

theorem eo_has_smt_translation_of_has_bool_type (t : Term) :
  eo_has_bool_type t ->
  eo_has_smt_translation t := by
  intro hTy
  intro hNone
  rw [eo_has_bool_type] at hTy
  rw [hNone] at hTy
  cases hTy

theorem term_ne_stuck_of_has_smt_translation (t : Term) :
  eo_has_smt_translation t -> t ≠ Term.Stuck := by
  intro hTy hStuck
  subst hStuck
  simp [eo_has_smt_translation, __eo_to_smt, __smtx_typeof] at hTy

theorem eo_has_bool_type_and_of_bool_args (A B : Term) :
  eo_has_bool_type A ->
  eo_has_bool_type B ->
  eo_has_bool_type (Term.Apply (Term.Apply Term.and A) B) := by
  intro hA hB
  unfold eo_has_bool_type at hA hB ⊢
  simp [__eo_to_smt, __smtx_typeof, hA, hB, smt_lit_ite, smt_lit_Teq]

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

theorem eo_has_bool_type_not_of_bool_arg (t : Term) :
  eo_has_bool_type t ->
  eo_has_bool_type (Term.Apply Term.not t) := by
  intro hTy
  simpa [eo_has_bool_type, __eo_to_smt, __smtx_typeof, hTy,
    smt_lit_ite, smt_lit_Teq]

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
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
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

mutual

inductive smt_value_rel : SmtValue -> SmtValue -> Prop where
  | map {m1 m2 : SmtMap} :
      (∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v) ->
      smt_value_rel (SmtValue.Map m1) (SmtValue.Map m2)
  | set {m1 m2 : SmtMap} :
      (∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v) ->
      smt_value_rel (SmtValue.Set m1) (SmtValue.Set m2)
  | seq {s1 s2 : SmtSeq} :
      smt_seq_rel s1 s2 ->
      smt_value_rel (SmtValue.Seq s1) (SmtValue.Seq s2)
  | apply {f1 v1 f2 v2 : SmtValue} :
      smt_value_rel f1 f2 ->
      smt_value_rel v1 v2 ->
      smt_value_rel (SmtValue.Apply f1 v1) (SmtValue.Apply f2 v2)
  | base {v1 v2 : SmtValue} :
      v1 = v2 ->
      smt_value_rel v1 v2

inductive smt_seq_rel : SmtSeq -> SmtSeq -> Prop where
  | empty {T1 T2 : SmtType} :
      smt_seq_rel (SmtSeq.empty T1) (SmtSeq.empty T2)
  | cons {v1 v2 : SmtValue} {s1 s2 : SmtSeq} :
      smt_value_rel v1 v2 ->
      smt_seq_rel s1 s2 ->
      smt_seq_rel (SmtSeq.cons v1 s1) (SmtSeq.cons v2 s2)

end

mutual

theorem smt_value_rel_refl : (v : SmtValue) -> smt_value_rel v v
  | SmtValue.NotValue => by
      exact smt_value_rel.base rfl
  | SmtValue.Boolean _ => by
      exact smt_value_rel.base rfl
  | SmtValue.Numeral _ => by
      exact smt_value_rel.base rfl
  | SmtValue.Rational _ => by
      exact smt_value_rel.base rfl
  | SmtValue.Binary _ _ => by
      exact smt_value_rel.base rfl
  | SmtValue.Map _ => by
      exact smt_value_rel.map (fun _ => rfl)
  | SmtValue.Set _ => by
      exact smt_value_rel.set (fun _ => rfl)
  | SmtValue.Seq s => by
      exact smt_value_rel.seq (smt_seq_rel_refl s)
  | SmtValue.Char _ => by
      exact smt_value_rel.base rfl
  | SmtValue.RegLan _ => by
      exact smt_value_rel.base rfl
  | SmtValue.DtCons _ _ _ => by
      exact smt_value_rel.base rfl
  | SmtValue.Apply f v => by
      exact smt_value_rel.apply (smt_value_rel_refl f) (smt_value_rel_refl v)

theorem smt_seq_rel_refl : (s : SmtSeq) -> smt_seq_rel s s
  | SmtSeq.empty _ => by
      exact smt_seq_rel.empty
  | SmtSeq.cons v s => by
      exact smt_seq_rel.cons (smt_value_rel_refl v) (smt_seq_rel_refl s)

end

mutual

theorem smt_value_rel_symm (v1 v2 : SmtValue) :
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v1 := by
  intro h
  cases h with
  | map hm =>
      exact smt_value_rel.map (fun v => (hm v).symm)
  | set hm =>
      exact smt_value_rel.set (fun v => (hm v).symm)
  | seq hs =>
      exact smt_value_rel.seq (smt_seq_rel_symm _ _ hs)
  | apply hf hv =>
      exact smt_value_rel.apply (smt_value_rel_symm _ _ hf) (smt_value_rel_symm _ _ hv)
  | base hEq =>
      exact smt_value_rel.base hEq.symm

theorem smt_seq_rel_symm (s1 s2 : SmtSeq) :
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s1 := by
  intro h
  cases h with
  | empty =>
      exact smt_seq_rel.empty
  | cons hv hs =>
      exact smt_seq_rel.cons (smt_value_rel_symm _ _ hv) (smt_seq_rel_symm _ _ hs)

end

mutual

theorem smt_value_rel_trans (v1 v2 v3 : SmtValue) :
    smt_value_rel v1 v2 ->
    smt_value_rel v2 v3 ->
    smt_value_rel v1 v3 := by
  intro h12 h23
  cases h12 with
  | map hm12 =>
      cases h23 with
      | map hm23 =>
          exact smt_value_rel.map (fun v => by rw [hm12 v, hm23 v])
      | base hEq =>
          subst hEq
          exact smt_value_rel.map hm12
  | set hm12 =>
      cases h23 with
      | set hm23 =>
          exact smt_value_rel.set (fun v => by rw [hm12 v, hm23 v])
      | base hEq =>
          subst hEq
          exact smt_value_rel.set hm12
  | seq hs12 =>
      cases h23 with
      | seq hs23 =>
          exact smt_value_rel.seq (smt_seq_rel_trans _ _ _ hs12 hs23)
      | base hEq =>
          subst hEq
          exact smt_value_rel.seq hs12
  | apply hf12 hv12 =>
      cases h23 with
      | apply hf23 hv23 =>
          exact smt_value_rel.apply (smt_value_rel_trans _ _ _ hf12 hf23)
            (smt_value_rel_trans _ _ _ hv12 hv23)
      | base hEq =>
          subst hEq
          exact smt_value_rel.apply hf12 hv12
  | base hEq =>
      subst hEq
      exact h23

theorem smt_seq_rel_trans (s1 s2 s3 : SmtSeq) :
    smt_seq_rel s1 s2 ->
    smt_seq_rel s2 s3 ->
    smt_seq_rel s1 s3 := by
  intro h12 h23
  cases h12 with
  | empty =>
      cases h23 with
      | empty =>
          exact smt_seq_rel.empty
  | cons hv12 hs12 =>
      cases h23 with
      | cons hv23 hs23 =>
          exact smt_seq_rel.cons (smt_value_rel_trans _ _ _ hv12 hv23)
            (smt_seq_rel_trans _ _ _ hs12 hs23)

end

mutual

private theorem smtx_model_eval_eq_refl_aux :
    (v : SmtValue) -> __smtx_model_eval_eq v v = SmtValue.Boolean true
  | SmtValue.Map _ => by
      simp [__smtx_model_eval_eq]
  | SmtValue.Set _ => by
      simp [__smtx_model_eval_eq]
  | SmtValue.Seq s => by
      simpa using smtx_model_eval_seq_eq_refl_aux s
  | SmtValue.Apply f v => by
      simp [__smtx_model_eval_eq, smt_lit_veq, SmtEval.smt_lit_and,
        smtx_model_eval_eq_refl_aux f, smtx_model_eval_eq_refl_aux v]
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
  | SmtValue.DtCons _ _ _ => by
      simp [__smtx_model_eval_eq, smt_lit_veq]

private theorem smtx_model_eval_seq_eq_refl_aux :
    (s : SmtSeq) -> __smtx_model_eval_eq (SmtValue.Seq s) (SmtValue.Seq s) = SmtValue.Boolean true
  | SmtSeq.empty _ => by
      simp [__smtx_model_eval_eq]
  | SmtSeq.cons v s => by
      simp [__smtx_model_eval_eq, smt_lit_veq, SmtEval.smt_lit_and,
        smtx_model_eval_eq_refl_aux v, smtx_model_eval_seq_eq_refl_aux s]

theorem smt_value_rel_iff_model_eval_eq_true :
    (v1 : SmtValue) -> (v2 : SmtValue) ->
    smt_value_rel v1 v2 ↔ __smtx_model_eval_eq v1 v2 = SmtValue.Boolean true
  | v1, v2 => by
      constructor
      · intro h
        cases h with
        | map hm =>
            classical
            simp [__smtx_model_eval_eq, hm]
        | set hm =>
            classical
            simp [__smtx_model_eval_eq, hm]
        | seq hs =>
            simpa using (smt_seq_rel_iff_model_eval_eq_true _ _).mp hs
        | apply hf hv =>
            have hF := (smt_value_rel_iff_model_eval_eq_true _ _).mp hf
            have hV := (smt_value_rel_iff_model_eval_eq_true _ _).mp hv
            simp [__smtx_model_eval_eq, smt_lit_veq, SmtEval.smt_lit_and, hF, hV]
        | base hEq =>
            subst hEq
            exact smtx_model_eval_eq_refl_aux _
      · intro h
        cases v1 <;> cases v2
        case Map.Map m1 m2 =>
          classical
          simp [__smtx_model_eval_eq] at h
          exact smt_value_rel.map h
        case Set.Set m1 m2 =>
          classical
          simp [__smtx_model_eval_eq] at h
          exact smt_value_rel.set h
        case Seq.Seq s1 s2 =>
          exact smt_value_rel.seq ((smt_seq_rel_iff_model_eval_eq_true _ _).mpr h)
        case Apply.Apply f1 v1 f2 v2 =>
          simp [__smtx_model_eval_eq, smt_lit_veq, SmtEval.smt_lit_and] at h
          exact smt_value_rel.apply
            ((smt_value_rel_iff_model_eval_eq_true _ _).mpr h.1)
            ((smt_value_rel_iff_model_eval_eq_true _ _).mpr h.2)
        case NotValue.NotValue =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h
          exact smt_value_rel.base rfl
        case Boolean.Boolean b1 b2 =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h
          subst h
          exact smt_value_rel.base rfl
        case Numeral.Numeral n1 n2 =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h
          subst h
          exact smt_value_rel.base rfl
        case Rational.Rational q1 q2 =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h
          subst h
          exact smt_value_rel.base rfl
        case Binary.Binary hi1 lo1 hi2 lo2 =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h
          rcases h with ⟨rfl, rfl⟩
          exact smt_value_rel.base rfl
        case Char.Char c1 c2 =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h
          subst h
          exact smt_value_rel.base rfl
        case RegLan.RegLan r1 r2 =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h
          subst h
          exact smt_value_rel.base rfl
        case DtCons.DtCons n1 dt1 ar1 n2 dt2 ar2 =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          exact smt_value_rel.base rfl
        all_goals
          simp [__smtx_model_eval_eq, smt_lit_veq] at h

theorem smt_seq_rel_iff_model_eval_eq_true :
    (s1 : SmtSeq) -> (s2 : SmtSeq) ->
    smt_seq_rel s1 s2 ↔ __smtx_model_eval_eq (SmtValue.Seq s1) (SmtValue.Seq s2) = SmtValue.Boolean true
  | s1, s2 => by
      constructor
      · intro h
        cases h with
        | empty =>
            simp [__smtx_model_eval_eq]
        | cons hv hs =>
            have hV := (smt_value_rel_iff_model_eval_eq_true _ _).mp hv
            have hS := (smt_seq_rel_iff_model_eval_eq_true _ _).mp hs
            simp [__smtx_model_eval_eq, smt_lit_veq, SmtEval.smt_lit_and, hV, hS]
      · intro h
        cases s1 <;> cases s2
        case empty.empty =>
          exact smt_seq_rel.empty
        case cons.cons v1 s1 v2 s2 =>
          simp [__smtx_model_eval_eq, smt_lit_veq, SmtEval.smt_lit_and] at h
          exact smt_seq_rel.cons
            ((smt_value_rel_iff_model_eval_eq_true _ _).mpr h.1)
            ((smt_seq_rel_iff_model_eval_eq_true _ _).mpr h.2)
        case cons.empty =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h
        case empty.cons =>
          simp [__smtx_model_eval_eq, smt_lit_veq] at h

end

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

theorem eo_eq_operands_same_smt_type_of_has_bool_type (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) y) ->
  __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) ∧
    __smtx_typeof (__eo_to_smt x) ≠ SmtType.None := by
  intro hTy
  unfold eo_has_bool_type at hTy
  simpa [__eo_to_smt, __smtx_typeof] using
    (smtx_typeof_eq_bool_iff (__smtx_typeof (__eo_to_smt x))
      (__smtx_typeof (__eo_to_smt y))).mp hTy

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

theorem eo_has_bool_type_eq_symm (x y : Term) :
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq x) y) ->
  eo_has_bool_type (Term.Apply (Term.Apply Term.eq y) x) := by
  intro hTy
  rcases eo_eq_operands_same_smt_type_of_has_bool_type x y hTy with ⟨hEq, hNonNone⟩
  have hNonNone' : __smtx_typeof (__eo_to_smt y) ≠ SmtType.None := by
    simpa [hEq] using hNonNone
  exact eo_has_bool_type_eq_of_same_smt_type y x hEq.symm hNonNone'

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
  exact (smt_value_rel_iff_model_eval_eq_true v v).mp (smt_value_rel_refl v)

end RuleProofs
