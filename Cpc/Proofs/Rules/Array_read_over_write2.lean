import Cpc.Proofs.Support

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rw [__eo_to_smt.eq_def]

theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq (__eo_to_smt x)) (__eo_to_smt y) := by
  rw [__eo_to_smt.eq_def]

theorem eo_to_smt_select_eq (a i : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.select a) i) =
      SmtTerm.select (__eo_to_smt a) (__eo_to_smt i) := by
  rw [__eo_to_smt.eq_def]

theorem eo_to_smt_store_eq (a i e : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e) =
      SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e) := by
  rw [__eo_to_smt.eq_def]

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

private theorem eq_of_eo_eq_true (x y : Term)
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

private theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
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
    cases hx : __eo_eq x1 x2 <;> cases hy : __eo_eq y1 y2 <;>
      simp [__eo_and, hx, hy] at hAnd ⊢
    · rename_i b1 b2
      cases b1 <;> cases b2 <;> simp [native_and] at hAnd ⊢
    · rename_i w1 n1 w2 n2
      cases x1 <;> cases x2 <;> simp [__eo_eq] at hx
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
                  simp [__eo_typeof_store] at h
          | _ =>
              simp [__eo_typeof_store] at h
      | _ =>
          simp [__eo_typeof_store] at h

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
            | Array =>
                have hReq :
                    __eo_requires (__eo_eq y I) (Term.Boolean true) x ≠ Term.Stuck := by
                  simpa [__eo_typeof_select, hI] using h
                have hEq : I = y :=
                  eq_of_requires_eq_true_not_stuck y I x hReq
                exact ⟨x, by simpa [hEq]⟩
            | _ =>
                simp [__eo_typeof_select] at h
        | _ =>
            simp [__eo_typeof_select] at h
    | _ =>
        simp [__eo_typeof_select] at h

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

private theorem ne_of_native_veq_false {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = false) :
    v1 ≠ v2 := by
  intro hEq
  subst v2
  simp [native_veq] at h

theorem smt_value_rel_select_store_other_of_native_veq_false
    (v i j e : SmtValue)
    (hij : native_veq i j = false) :
    smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store v i e) j)
      (__smtx_model_eval_select v j) := by
  have hij' : i ≠ j := ne_of_native_veq_false hij
  rw [smt_value_rel_iff_model_eval_eq_true]
  cases v <;>
    simp [__smtx_model_eval_select, __smtx_model_eval_store, __smtx_map_select,
      __smtx_map_store, __smtx_msm_lookup, __smtx_model_eval_eq, native_ite,
      native_veq, hij', smtx_model_eval_eq_refl]

end RuleProofs

private theorem array_index_eq_of_eq
    (I1 E1 I2 E2 : Term)
    (h :
      Term.Apply (Term.Apply Term.Array I1) E1 =
        Term.Apply (Term.Apply Term.Array I2) E2) :
    I1 = I2 := by
  have h' := congrArg
    (fun t =>
      match t with
      | Term.Apply (Term.Apply Term.Array I) _ => I
      | _ => Term.Stuck) h
  simpa using h'

private theorem prog_array_read_over_write2_eq
    (t1 i1 j1 e1 i2 j2 : Term)
    (hT1NotStuck : t1 ≠ Term.Stuck)
    (hI1NotStuck : i1 ≠ Term.Stuck)
    (hJ1NotStuck : j1 ≠ Term.Stuck)
    (hE1NotStuck : e1 ≠ Term.Stuck) :
    __eo_prog_array_read_over_write2 t1 i1 j1 e1
      (Proof.pf
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply (Term.Apply Term.eq i2) j2))
          (Term.Boolean false))) =
      __eo_requires (__eo_and (__eo_eq i1 i2) (__eo_eq j1 j2)) (Term.Boolean true)
        (Term.Apply
          (Term.Apply Term.eq
            (Term.Apply
              (Term.Apply Term.select
                (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) j1))
          (Term.Apply (Term.Apply Term.select t1) j1)) := by
  by_cases hT : t1 = Term.Stuck
  · contradiction
  · by_cases hI : i1 = Term.Stuck
    · contradiction
    · by_cases hJ : j1 = Term.Stuck
      · contradiction
      · by_cases hE : e1 = Term.Stuck
        · contradiction
        · simp [__eo_prog_array_read_over_write2, hT, hI, hJ, hE]

private theorem typeof_args_of_prog_array_read_over_write2_bool
    (t1 i1 j1 e1 p1 : Term)
    (hT1Trans : RuleProofs.eo_has_smt_translation t1)
    (hI1Trans : RuleProofs.eo_has_smt_translation i1)
    (hJ1Trans : RuleProofs.eo_has_smt_translation j1)
    (hE1Trans : RuleProofs.eo_has_smt_translation e1)
    (h : __eo_typeof (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) =
      Term.Bool) :
    __eo_typeof t1 = Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof e1) ∧
      __eo_typeof j1 = __eo_typeof i1 := by
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hProg :
      __eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool h
  cases p1 with
  | Apply f pRhs =>
      cases f with
      | Apply g pLhs =>
          cases g with
          | eq =>
              cases pLhs with
              | Apply f2 j2 =>
                  cases f2 with
                  | Apply g2 i2 =>
                      cases g2 with
                      | eq =>
                          cases pRhs with
                          | Boolean b =>
                              cases b with
                              | false =>
                                  rw [prog_array_read_over_write2_eq
                                        t1 i1 j1 e1 i2 j2
                                        hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck]
                                    at hProg h
                                  let lhs :=
                                    Term.Apply
                                      (Term.Apply Term.select
                                        (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                      j1
                                  let rhs := Term.Apply (Term.Apply Term.select t1) j1
                                  let body := Term.Apply (Term.Apply Term.eq lhs) rhs
                                  have hAlign :
                                      i2 = i1 ∧ j2 = j1 :=
                                    RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                      i1 j1 i2 j2 body hProg
                                  have hi2 : i2 = i1 := hAlign.1
                                  have hj2 : j2 = j1 := hAlign.2
                                  subst i2
                                  subst j2
                                  simp [body, lhs, rhs, __eo_requires, __eo_and, __eo_eq,
                                    native_ite, native_teq, native_not,
                                    SmtEval.native_not] at h
                                  have hTypesNotStuck :=
                                    RuleProofs.eo_typeof_eq_bool_operands_not_stuck
                                      (__eo_typeof lhs) (__eo_typeof rhs) h
                                  have hLhsNotStuck : __eo_typeof lhs ≠ Term.Stuck :=
                                    hTypesNotStuck.1
                                  have hRhsNotStuck : __eo_typeof rhs ≠ Term.Stuck :=
                                    hTypesNotStuck.2
                                  have hStoreNotStuck :
                                      __eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1) ≠
                                        Term.Stuck := by
                                    intro hStoreStuck
                                    change __eo_typeof_select
                                        (__eo_typeof
                                          (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                        (__eo_typeof j1) ≠ Term.Stuck at hLhsNotStuck
                                    rw [hStoreStuck] at hLhsNotStuck
                                    have hSelectStuck :
                                        __eo_typeof_select Term.Stuck (__eo_typeof j1) = Term.Stuck := by
                                      cases hJTy : __eo_typeof j1 <;>
                                        simp [__eo_typeof_select, hJTy]
                                    exact hLhsNotStuck hSelectStuck
                                  have hT1Ty :
                                      __eo_typeof t1 =
                                        Term.Apply (Term.Apply Term.Array (__eo_typeof i1))
                                          (__eo_typeof e1) := by
                                    change __eo_typeof_store (__eo_typeof t1) (__eo_typeof i1)
                                        (__eo_typeof e1) ≠ Term.Stuck at hStoreNotStuck
                                    exact RuleProofs.eo_typeof_store_not_stuck_implies_array
                                      (__eo_typeof t1) (__eo_typeof i1) (__eo_typeof e1)
                                      hStoreNotStuck
                                  have hT1TyJ :
                                      ∃ E : Term,
                                        __eo_typeof t1 =
                                          Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) E := by
                                    change __eo_typeof_select (__eo_typeof t1) (__eo_typeof j1) ≠
                                      Term.Stuck at hRhsNotStuck
                                    exact RuleProofs.eo_typeof_select_not_stuck_implies_array
                                      (__eo_typeof t1) (__eo_typeof j1) hRhsNotStuck
                                  rcases hT1TyJ with ⟨E, hT1TyJ⟩
                                  have hArrayEq :
                                      Term.Apply (Term.Apply Term.Array (__eo_typeof i1))
                                        (__eo_typeof e1) =
                                        Term.Apply (Term.Apply Term.Array (__eo_typeof j1)) E :=
                                    hT1Ty.symm.trans hT1TyJ
                                  have hIJ : __eo_typeof i1 = __eo_typeof j1 :=
                                    array_index_eq_of_eq
                                      (__eo_typeof i1) (__eo_typeof e1) (__eo_typeof j1) E
                                      hArrayEq
                                  exact ⟨hT1Ty, hIJ.symm⟩
                              | true =>
                                  have : False := by
                                    simp [__eo_prog_array_read_over_write2] at hProg
                                  exact False.elim this
                          | _ =>
                              have : False := by
                                simp [__eo_prog_array_read_over_write2] at hProg
                              exact False.elim this
                      | _ =>
                          have : False := by
                            simp [__eo_prog_array_read_over_write2] at hProg
                          exact False.elim this
                  | _ =>
                      have : False := by
                        simp [__eo_prog_array_read_over_write2] at hProg
                      exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_prog_array_read_over_write2] at hProg
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_prog_array_read_over_write2] at hProg
              exact False.elim this
      | _ =>
          have : False := by
            simp [__eo_prog_array_read_over_write2] at hProg
          exact False.elim this
  | _ =>
      have : False := by
        simp [__eo_prog_array_read_over_write2] at hProg
      exact False.elim this

private theorem typed___eo_prog_array_read_over_write2_impl
    (t1 i1 j1 e1 p1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation j1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  __eo_typeof (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) := by
  intro hT1Trans hI1Trans hJ1Trans hE1Trans hResultTy
  rcases typeof_args_of_prog_array_read_over_write2_bool
      t1 i1 j1 e1 p1 hT1Trans hI1Trans hJ1Trans hE1Trans hResultTy with
    ⟨hT1Ty, hJI⟩
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hSmtT1Raw :
      __smtx_typeof (__eo_to_smt t1) =
        __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof e1)) :=
    TranslationProofs.eo_to_smt_well_typed_and_typeof_implies_smt_type
      t1 _ (__eo_to_smt t1) rfl hT1Trans hT1Ty
  have hT1TyNonNone :
      __eo_to_smt_type
          (Term.Apply (Term.Apply Term.Array (__eo_typeof i1)) (__eo_typeof e1)) ≠
        SmtType.None := by
    rw [← hSmtT1Raw]
    exact hT1Trans
  have hSmtT1 :
      __smtx_typeof (__eo_to_smt t1) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof e1)) := by
    exact hSmtT1Raw.trans
      (RuleProofs.eo_to_smt_type_array_of_non_none
        (__eo_typeof i1) (__eo_typeof e1) hT1TyNonNone)
  have hSmtI1 :
      __smtx_typeof (__eo_to_smt i1) = __eo_to_smt_type (__eo_typeof i1) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation i1 hI1Trans
  have hSmtJ1 :
      __smtx_typeof (__eo_to_smt j1) = __eo_to_smt_type (__eo_typeof i1) := by
    rw [TranslationProofs.eo_to_smt_typeof_matches_translation j1 hJ1Trans, hJI]
  have hSmtE1 :
      __smtx_typeof (__eo_to_smt e1) = __eo_to_smt_type (__eo_typeof e1) :=
    TranslationProofs.eo_to_smt_typeof_matches_translation e1 hE1Trans
  have hStoreTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) =
        SmtType.Map (__eo_to_smt_type (__eo_typeof i1)) (__eo_to_smt_type (__eo_typeof e1)) := by
    rw [RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_store, __smtx_typeof_guard,
      native_ite, native_Teq, hSmtT1, hSmtI1, hSmtE1]
  have hLhsTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply
              (Term.Apply Term.select
                (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) j1)) =
        __eo_to_smt_type (__eo_typeof e1) := by
    rw [RuleProofs.eo_to_smt_select_eq, RuleProofs.eo_to_smt_store_eq]
    simp [__smtx_typeof, __smtx_typeof_select, __smtx_typeof_store, __smtx_typeof_guard,
      native_ite, native_Teq, hSmtT1, hSmtI1, hSmtJ1, hSmtE1]
  have hRhsTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply Term.select t1) j1)) =
        __eo_to_smt_type (__eo_typeof e1) := by
    rw [RuleProofs.eo_to_smt_select_eq]
    simp [__smtx_typeof, __smtx_typeof_select, __smtx_typeof_guard,
      native_ite, native_Teq, hSmtT1, hSmtJ1]
  have hE1TyNonNone : __eo_to_smt_type (__eo_typeof e1) ≠ SmtType.None := by
    rw [← hSmtE1]
    exact hE1Trans
  have hLhsTrans :
      RuleProofs.eo_has_smt_translation
        (Term.Apply
          (Term.Apply Term.select
            (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1)) j1) := by
    simpa [RuleProofs.eo_has_smt_translation, hLhsTy] using hE1TyNonNone
  have hProg :
      __eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1) ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases p1 with
  | Apply f pRhs =>
      cases f with
      | Apply g pLhs =>
          cases g with
          | eq =>
              cases pLhs with
              | Apply f2 j2 =>
                  cases f2 with
                  | Apply g2 i2 =>
                      cases g2 with
                      | eq =>
                          cases pRhs with
                          | Boolean b =>
                              cases b with
                              | false =>
                                  let lhs :=
                                    Term.Apply
                                      (Term.Apply Term.select
                                        (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                      j1
                                  let rhs := Term.Apply (Term.Apply Term.select t1) j1
                                  let body := Term.Apply (Term.Apply Term.eq lhs) rhs
                                  have hProgEq :=
                                    prog_array_read_over_write2_eq
                                      t1 i1 j1 e1 i2 j2
                                      hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck
                                  rw [hProgEq] at hProg
                                  have hAlign :
                                      i2 = i1 ∧ j2 = j1 :=
                                    RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                      i1 j1 i2 j2 body hProg
                                  have hi2 : i2 = i1 := hAlign.1
                                  have hj2 : j2 = j1 := hAlign.2
                                  subst i2
                                  subst j2
                                  rw [prog_array_read_over_write2_eq
                                        t1 i1 j1 e1 i1 j1
                                        hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck]
                                  simp [body, lhs, rhs, __eo_requires, __eo_and, __eo_eq,
                                    native_ite, native_teq, native_not, SmtEval.native_not]
                                  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
                                    lhs rhs
                                    (by rw [hLhsTy, hRhsTy]) hLhsTrans
                              | true =>
                                  have : False := by
                                    simp [__eo_prog_array_read_over_write2] at hProg
                                  exact False.elim this
                          | _ =>
                              have : False := by
                                simp [__eo_prog_array_read_over_write2] at hProg
                              exact False.elim this
                      | _ =>
                          have : False := by
                            simp [__eo_prog_array_read_over_write2] at hProg
                          exact False.elim this
                  | _ =>
                      have : False := by
                        simp [__eo_prog_array_read_over_write2] at hProg
                      exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_prog_array_read_over_write2] at hProg
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_prog_array_read_over_write2] at hProg
              exact False.elim this
      | _ =>
          have : False := by
            simp [__eo_prog_array_read_over_write2] at hProg
          exact False.elim this
  | _ =>
      have : False := by
        simp [__eo_prog_array_read_over_write2] at hProg
      exact False.elim this

private theorem facts___eo_prog_array_read_over_write2_impl
    (M : SmtModel) (_hM : model_total_typed M) (t1 i1 j1 e1 p1 : Term) :
  RuleProofs.eo_has_smt_translation t1 ->
  RuleProofs.eo_has_smt_translation i1 ->
  RuleProofs.eo_has_smt_translation j1 ->
  RuleProofs.eo_has_smt_translation e1 ->
  eo_interprets M p1 true ->
  __eo_typeof (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) = Term.Bool ->
  eo_interprets M (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) true := by
  intro hT1Trans hI1Trans hJ1Trans hE1Trans hP1True hResultTy
  have hProgBool :
      RuleProofs.eo_has_bool_type (__eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1)) :=
    typed___eo_prog_array_read_over_write2_impl
      t1 i1 j1 e1 p1 hT1Trans hI1Trans hJ1Trans hE1Trans hResultTy
  have hT1NotStuck : t1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t1 hT1Trans
  have hI1NotStuck : i1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation i1 hI1Trans
  have hJ1NotStuck : j1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation j1 hJ1Trans
  have hE1NotStuck : e1 ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation e1 hE1Trans
  have hProg :
      __eo_prog_array_read_over_write2 t1 i1 j1 e1 (Proof.pf p1) ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_bool_type _
      hProgBool
  cases p1 with
  | Apply f pRhs =>
      cases f with
      | Apply g pLhs =>
          cases g with
          | eq =>
              cases pLhs with
              | Apply f2 j2 =>
                  cases f2 with
                  | Apply g2 i2 =>
                      cases g2 with
                      | eq =>
                          cases pRhs with
                          | Boolean b =>
                              cases b with
                              | false =>
                                  let lhs :=
                                    Term.Apply
                                      (Term.Apply Term.select
                                        (Term.Apply (Term.Apply (Term.Apply Term.store t1) i1) e1))
                                      j1
                                  let rhs := Term.Apply (Term.Apply Term.select t1) j1
                                  let body := Term.Apply (Term.Apply Term.eq lhs) rhs
                                  have hProgEq :=
                                    prog_array_read_over_write2_eq
                                      t1 i1 j1 e1 i2 j2
                                      hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck
                                  rw [hProgEq] at hProg
                                  have hAlign :
                                      i2 = i1 ∧ j2 = j1 :=
                                    RuleProofs.eqs_of_requires_and_eq_true_not_stuck
                                      i1 j1 i2 j2 body hProg
                                  have hi2 : i2 = i1 := hAlign.1
                                  have hj2 : j2 = j1 := hAlign.2
                                  subst i2
                                  subst j2
                                  have hij :
                                      native_veq
                                        (__smtx_model_eval M (__eo_to_smt i1))
                                        (__smtx_model_eval M (__eo_to_smt j1)) = false := by
                                    exact RuleProofs.native_veq_false_of_model_eval_eq_false
                                      (RuleProofs.model_eval_eq_false_of_eq_false_eq_true M i1 j1
                                        hP1True)
                                  have hBodyBool :
                                      RuleProofs.eo_has_bool_type body := by
                                    rw [prog_array_read_over_write2_eq
                                          t1 i1 j1 e1 i1 j1
                                          hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck] at hProgBool
                                    simpa [body, lhs, rhs, __eo_requires, __eo_and, __eo_eq,
                                      native_ite, native_teq, native_not,
                                      SmtEval.native_not] using hProgBool
                                  rw [prog_array_read_over_write2_eq
                                        t1 i1 j1 e1 i1 j1
                                        hT1NotStuck hI1NotStuck hJ1NotStuck hE1NotStuck]
                                  simp [body, lhs, rhs, __eo_requires, __eo_and, __eo_eq,
                                    native_ite, native_teq, native_not, SmtEval.native_not]
                                  exact RuleProofs.eo_interprets_eq_of_rel M lhs rhs hBodyBool <| by
                                    simpa [lhs, rhs, RuleProofs.eo_to_smt_select_eq,
                                      RuleProofs.eo_to_smt_store_eq, __smtx_model_eval] using
                                      (RuleProofs.smt_value_rel_select_store_other_of_native_veq_false
                                        (__smtx_model_eval M (__eo_to_smt t1))
                                        (__smtx_model_eval M (__eo_to_smt i1))
                                        (__smtx_model_eval M (__eo_to_smt j1))
                                        (__smtx_model_eval M (__eo_to_smt e1))
                                        hij)
                              | true =>
                                  have : False := by
                                    simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                                      hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                                  exact False.elim this
                          | _ =>
                              have : False := by
                                simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                                  hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                              exact False.elim this
                      | _ =>
                          have : False := by
                            simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                              hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                          exact False.elim this
                  | _ =>
                      have : False := by
                        simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                          hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                      exact False.elim this
              | _ =>
                  have : False := by
                    simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                      hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_prog_array_read_over_write2, hT1NotStuck,
                  hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
              exact False.elim this
      | _ =>
          have : False := by
            simp [__eo_prog_array_read_over_write2, hT1NotStuck,
              hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
          exact False.elim this
  | _ =>
      have : False := by
        simp [__eo_prog_array_read_over_write2, hT1NotStuck,
          hI1NotStuck, hJ1NotStuck, hE1NotStuck] at hProg
      exact False.elim this

theorem cmd_step_array_read_over_write2_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.array_read_over_write2 args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.array_read_over_write2 args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.array_read_over_write2 args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.array_read_over_write2 args premises ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
      | cons a2 args =>
          cases args with
          | nil =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
          | cons a3 args =>
              cases args with
              | nil =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
              | cons a4 args =>
                  cases args with
                  | nil =>
                      cases premises with
                      | nil =>
                          change Term.Stuck ≠ Term.Stuck at hProg
                          exact False.elim (hProg rfl)
                      | cons n1 premises =>
                          cases premises with
                          | nil =>
                              let T1 := a1
                              let I1 := a2
                              let J1 := a3
                              let E1 := a4
                              let P1 := __eo_state_proven_nth s n1
                              have hTranses :
                                  RuleProofs.eo_has_smt_translation T1 ∧
                                    RuleProofs.eo_has_smt_translation I1 ∧
                                    RuleProofs.eo_has_smt_translation J1 ∧
                                    RuleProofs.eo_has_smt_translation E1 := by
                                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
                              change __eo_typeof
                                  (__eo_prog_array_read_over_write2 T1 I1 J1 E1 (Proof.pf P1)) =
                                Term.Bool at hResultTy
                              refine ⟨?_, ?_⟩
                              · intro hTrue
                                change eo_interprets M
                                  (__eo_prog_array_read_over_write2 T1 I1 J1 E1 (Proof.pf P1))
                                  true
                                exact facts___eo_prog_array_read_over_write2_impl M hM
                                  T1 I1 J1 E1 P1
                                  hTranses.1 hTranses.2.1 hTranses.2.2.1 hTranses.2.2.2
                                  (hTrue P1 (by simp [P1, premiseTermList]))
                                  hResultTy
                              · change RuleProofs.eo_has_smt_translation
                                  (__eo_prog_array_read_over_write2 T1 I1 J1 E1 (Proof.pf P1))
                                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                  (__eo_prog_array_read_over_write2 T1 I1 J1 E1 (Proof.pf P1))
                                  (typed___eo_prog_array_read_over_write2_impl
                                    T1 I1 J1 E1 P1
                                    hTranses.1 hTranses.2.1 hTranses.2.2.1 hTranses.2.2.2
                                    hResultTy)
                          | cons _ _ =>
                              change Term.Stuck ≠ Term.Stuck at hProg
                              exact False.elim (hProg rfl)
                  | cons _ _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
