import Cpc.SmtModel

set_option maxHeartbeats 10000000

namespace Smtm

/--
A model is well-typed when every lookup returns a value of the requested type.
This is the assumption needed to state preservation for `__smtx_model_eval`.
-/
def smtx_model_well_typed (M : SmtModel) : Prop :=
  ∀ n T, __smtx_typeof_value (__smtx_model_lookup M n T) = T

/--
Minimal well-formedness for terms used by the preservation statement.
The only non-syntactic case is `Const`, whose annotation must match the value.
-/
def smtx_term_well_formed : SmtTerm -> Prop
  | SmtTerm.Apply f x => smtx_term_well_formed f ∧ smtx_term_well_formed x
  | SmtTerm.Const v T => __smtx_typeof_value v = T
  | _ => True

private theorem typeof_eq_app_is_bool {x1 x2 : SmtTerm}
    (ht : __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) ≠ SmtType.None) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) = SmtType.Bool := by
  have hdef : __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) =
      __smtx_typeof_eq (__smtx_typeof x1) (__smtx_typeof x2) := rfl
  rw [hdef]
  by_cases hnone : __smtx_typeof x1 = SmtType.None
  · rw [hdef] at ht
    simp [__smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hnone] at ht
  · by_cases hsame : __smtx_typeof x1 = __smtx_typeof x2
    · have hnone2 : __smtx_typeof x2 ≠ SmtType.None := by
        simpa [hsame] using hnone
      simp [__smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hsame, hnone2]
    · rw [hdef] at ht
      simp [__smtx_typeof_eq, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hnone, hsame] at ht

private theorem typeof_xor_app_is_bool {x1 x2 : SmtTerm}
    (ht : __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor x1) x2) ≠ SmtType.None) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor x1) x2) = SmtType.Bool := by
  have hdef : __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor x1) x2) =
      smt_lit_ite (smt_lit_Teq (__smtx_typeof x1) SmtType.Bool)
        (smt_lit_ite (smt_lit_Teq (__smtx_typeof x2) SmtType.Bool) SmtType.Bool SmtType.None)
        SmtType.None := rfl
  by_cases hx1 : __smtx_typeof x1 = SmtType.Bool
  · by_cases hx2 : __smtx_typeof x2 = SmtType.Bool
    · rw [hdef]
      simp [smt_lit_ite, smt_lit_Teq, hx1, hx2]
    · rw [hdef] at ht
      simp [smt_lit_ite, smt_lit_Teq, hx1, hx2] at ht
  · rw [hdef] at ht
    simp [smt_lit_ite, smt_lit_Teq, hx1] at ht

private theorem typeof_exists_app_is_bool {s : smt_lit_String} {T : SmtType} {x : SmtTerm}
    (ht : __smtx_typeof (SmtTerm.Apply (SmtTerm.exists s T) x) ≠ SmtType.None) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.exists s T) x) = SmtType.Bool := by
  have hdef : __smtx_typeof (SmtTerm.Apply (SmtTerm.exists s T) x) =
      smt_lit_ite (smt_lit_Teq (__smtx_typeof x) SmtType.Bool) SmtType.Bool SmtType.None := rfl
  by_cases hx : __smtx_typeof x = SmtType.Bool
  · rw [hdef]
    simp [smt_lit_ite, smt_lit_Teq, hx]
  · rw [hdef] at ht
    simp [smt_lit_ite, smt_lit_Teq, hx] at ht

private theorem typeof_forall_app_is_bool {s : smt_lit_String} {T : SmtType} {x : SmtTerm}
    (ht : __smtx_typeof (SmtTerm.Apply (SmtTerm.forall s T) x) ≠ SmtType.None) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.forall s T) x) = SmtType.Bool := by
  have hdef : __smtx_typeof (SmtTerm.Apply (SmtTerm.forall s T) x) =
      smt_lit_ite (smt_lit_Teq (__smtx_typeof x) SmtType.Bool) SmtType.Bool SmtType.None := rfl
  by_cases hx : __smtx_typeof x = SmtType.Bool
  · rw [hdef]
    simp [smt_lit_ite, smt_lit_Teq, hx]
  · rw [hdef] at ht
    simp [smt_lit_ite, smt_lit_Teq, hx] at ht

private theorem typeof_dt_tester_app_is_bool
    {s : smt_lit_String} {d : SmtDatatype} {i : smt_lit_Nat} {x : SmtTerm}
    (ht : __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) ≠ SmtType.None) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) = SmtType.Bool := by
  have hdef : __smtx_typeof (SmtTerm.Apply (SmtTerm.DtTester s d i) x) =
      __smtx_typeof_apply (SmtType.Map (SmtType.Datatype s d) SmtType.Bool) (__smtx_typeof x) := rfl
  by_cases hx : __smtx_typeof x = SmtType.Datatype s d
  · rw [hdef]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hx]
  · rw [hdef] at ht
    simp [__smtx_typeof_apply, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at ht
    exact False.elim (hx ht.symm)

private theorem __smtx_model_eval_type_preservation_go
    {M : SmtModel} (hM : smtx_model_well_typed M) :
    ∀ {t : SmtTerm},
      smtx_term_well_formed t ->
      __smtx_typeof t ≠ SmtType.None ->
      __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t
  | SmtTerm.Boolean _, _, _ => by rfl
  | SmtTerm.Numeral _, _, _ => by rfl
  | SmtTerm.Rational _, _, _ => by rfl
  | SmtTerm.String _, _, _ => by rfl
  | SmtTerm.re_allchar, _, _ => by rfl
  | SmtTerm.re_none, _, _ => by rfl
  | SmtTerm.re_all, _, _ => by rfl
  | SmtTerm.Const v T, hwf, _ => by
      have hv : __smtx_typeof_value v = T := by
        simpa [smtx_term_well_formed] using hwf
      rw [show __smtx_model_eval M (SmtTerm.Const v T) =
          smt_lit_ite (smt_lit_Teq (__smtx_typeof_value v) T) v SmtValue.NotValue from rfl]
      rw [show __smtx_typeof (SmtTerm.Const v T) = T from rfl]
      simp [smt_lit_ite, smt_lit_Teq, hv]
  | SmtTerm.UConst i T, _, _ => by
      rw [show __smtx_model_eval M (SmtTerm.UConst i T) =
          __smtx_model_lookup M (smt_lit_nat_to_int i) T from rfl]
      rw [show __smtx_typeof (SmtTerm.UConst i T) = T from rfl]
      simpa using hM (smt_lit_nat_to_int i) T
  | SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2, _, ht => by
      rw [typeof_eq_app_is_bool ht]
      rw [show __smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) =
          __smtx_model_eval_eq (__smtx_model_eval M x1) (__smtx_model_eval M x2) from rfl]
      cases h1 : __smtx_model_eval M x1 <;> cases h2 : __smtx_model_eval M x2 <;>
        simp [__smtx_model_eval_eq, __smtx_typeof_value, smt_lit_veq_ext]
  | SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct x1) x2, _, ht => by
      rw [show __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct x1) x2) =
          __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.eq x1) x2) from rfl]
      rw [typeof_eq_app_is_bool ht]
      rw [show __smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.distinct x1) x2) =
          __smtx_model_eval_distinct (__smtx_model_eval M x1) (__smtx_model_eval M x2) from rfl]
      cases h1 : __smtx_model_eval M x1 <;> cases h2 : __smtx_model_eval M x2 <;>
        simp [__smtx_model_eval_distinct, __smtx_model_eval_not, __smtx_model_eval_eq,
          __smtx_typeof_value, smt_lit_veq_ext]
  | SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor x1) x2, _, ht => by
      rw [typeof_xor_app_is_bool ht]
      rw [show __smtx_model_eval M (SmtTerm.Apply (SmtTerm.Apply SmtTerm.xor x1) x2) =
          __smtx_model_eval_xor (__smtx_model_eval M x1) (__smtx_model_eval M x2) from rfl]
      cases h1 : __smtx_model_eval M x1 <;> cases h2 : __smtx_model_eval M x2 <;>
        simp [__smtx_model_eval_xor, __smtx_model_eval_not, __smtx_model_eval_eq,
          __smtx_typeof_value, smt_lit_veq_ext]
  | SmtTerm.Apply (SmtTerm.exists s T) x, _, ht => by
      rw [typeof_exists_app_is_bool ht]
      rfl
  | SmtTerm.Apply (SmtTerm.forall s T) x, _, ht => by
      rw [typeof_forall_app_is_bool ht]
      rfl
  | SmtTerm.Apply (SmtTerm.DtTester s d i) x, _, ht => by
      rw [typeof_dt_tester_app_is_bool ht]
      rw [show __smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtTester s d i) x) =
          __smtx_model_eval_dt_tester s d i (__smtx_model_eval M x) from rfl]
      rfl
  | _, _, _ => by
      sorry

theorem __smtx_model_eval_type_preservation
    {M : SmtModel} {t : SmtTerm}
    (hM : smtx_model_well_typed M)
    (hwf : smtx_term_well_formed t)
    (ht : __smtx_typeof t ≠ SmtType.None) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  exact __smtx_model_eval_type_preservation_go hM hwf ht

end Smtm
