import CpcMini.SmtModel

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Establishes an equality relating `smtx_inhabited_type` and `true_iff`. -/
theorem smtx_inhabited_type_eq_true_iff (T : SmtType) :
    native_inhabited_type T = true ↔ type_inhabited T := by
  classical
  unfold native_inhabited_type type_inhabited
  simp

/-- Establishes an equality relating `smtx_inhabited_type` and `false_iff`. -/
theorem smtx_inhabited_type_eq_false_iff (T : SmtType) :
    native_inhabited_type T = false ↔ ¬ type_inhabited T := by
  classical
  unfold native_inhabited_type type_inhabited
  by_cases h : ∃ v : SmtValue, __smtx_typeof_value v = T
  · simp [h]
  · simp [h]

/-- Computes the well-formedness/inhabitation guard from a non-`None` result. -/
theorem smtx_typeof_guard_wf_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    __smtx_typeof_guard_wf T U = U := by
  intro h
  unfold __smtx_typeof_guard_wf at h ⊢
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h ⊢

/-- Extracts semantic inhabitation from a non-`None` guarded type. -/
theorem smtx_typeof_guard_wf_inhabited_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    type_inhabited T := by
  intro h
  unfold __smtx_typeof_guard_wf at h
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h
  have hPair :
      native_inhabited_type T = true ∧
        __smtx_type_wf_rec T native_reflist_nil = true := by
    simpa [__smtx_type_wf, native_and] using hWf
  exact (smtx_inhabited_type_eq_true_iff T).1 hPair.1

/-- Extracts well-formedness of the guarded source type from a non-`None` guarded type. -/
theorem smtx_typeof_guard_wf_wf_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    __smtx_type_wf T = true := by
  intro h
  unfold __smtx_typeof_guard_wf at h
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h ⊢

/-- Any well-formed SMT type is different from `None`. -/
theorem type_wf_non_none
    {T : SmtType}
    (h : __smtx_type_wf T = true) :
    T ≠ SmtType.None := by
  intro hNone
  simp [__smtx_type_wf, __smtx_type_wf_rec, native_and, hNone] at h

/-- Rebuilds public well-formedness from recursive well-formedness plus inhabitation. -/
theorem type_wf_of_inhabited_and_wf_rec
    {T : SmtType}
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T native_reflist_nil = true) :
    __smtx_type_wf T = true := by
  simp [__smtx_type_wf, native_and, hInh, hRec]

/-- Predicate asserting that an SMT term does not have type `None`. -/
def term_has_non_none_type (t : SmtTerm) : Prop :=
  __smtx_typeof t ≠ SmtType.None

/-- Predicate asserting that the SMT type of a term is inhabited. -/
def term_has_inhabited_type (t : SmtTerm) : Prop :=
  type_inhabited (__smtx_typeof t)

/-- Predicate asserting that application typing is computed by `__smtx_typeof_apply` for a pair of terms. -/
def generic_apply_type (f x : SmtTerm) : Prop :=
  __smtx_typeof (SmtTerm.Apply f x) =
    __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x)

/-- Predicate asserting that application evaluation is computed by `__smtx_model_eval_apply` for a pair of terms. -/
def generic_apply_eval (f x : SmtTerm) : Prop :=
  ∀ M,
    __smtx_model_eval M (SmtTerm.Apply f x) =
      __smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x)

/-- Predicate asserting that a model returns a correctly typed value, or `NotValue`, at a given symbol and type. -/
def model_typed_at (M : SmtModel) (s : native_String) (T : SmtType) : Prop :=
  (type_inhabited T -> __smtx_typeof_value (__smtx_model_lookup M s T) = T) ∧
  (¬ type_inhabited T -> __smtx_model_lookup M s T = SmtValue.NotValue)

/-- Shows that the SMT type `bool` is inhabited. -/
theorem type_inhabited_bool : type_inhabited SmtType.Bool :=
  ⟨SmtValue.Boolean true, rfl⟩

/-- Shows that the SMT type `int` is inhabited. -/
theorem type_inhabited_int : type_inhabited SmtType.Int :=
  ⟨SmtValue.Numeral 0, rfl⟩

/-- Shows that the SMT type `real` is inhabited. -/
theorem type_inhabited_real : type_inhabited SmtType.Real :=
  ⟨SmtValue.Rational (native_mk_rational 0 1), rfl⟩

/-- Shows that the SMT type `seq` is inhabited. -/
theorem type_inhabited_seq (T : SmtType) : type_inhabited (SmtType.Seq T) :=
  ⟨SmtValue.Seq (SmtSeq.empty T), rfl⟩

/-- Shows that the SMT type `map` is inhabited. -/
theorem type_inhabited_map {A B : SmtType} (hB : type_inhabited B) :
    type_inhabited (SmtType.Map A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Map (SmtMap.default A v), by simp [__smtx_typeof_value, __smtx_typeof_map_value, hv]⟩

private def subst_field (s : native_String) (d : SmtDatatype) : SmtType -> SmtType
  | SmtType.Datatype s2 d2 =>
      SmtType.Datatype s2
        (native_ite (native_streq s s2) d2 (__smtx_dt_substitute s d d2))
  | T => native_ite (native_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T

mutual

private theorem finite_type_default_subst_field_id
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType)
    (h : __smtx_finite_type_default T ≠ SmtValue.NotValue) :
    subst_field s d T = T := by
  cases T <;>
    simp [subst_field, native_ite, native_Teq, __smtx_finite_type_default, native_not,
      native_and] at h ⊢
  case Datatype s2 d2 =>
    cases hs : native_streq s s2
    · have hd := finite_datatype_default_subst_id s d s2 d2 d2 native_nat_zero h
      simp [native_ite, hs, hd]
    · simp [native_ite, hs]

private theorem finite_datatype_default_subst_id
    (s : native_String)
    (d : SmtDatatype)
    (s0 : native_String)
    (d0 : SmtDatatype) :
    ∀ current n,
      __smtx_finite_datatype_default s0 d0 current n ≠ SmtValue.NotValue ->
        __smtx_dt_substitute s d current = current
  | SmtDatatype.null, _, h => by
      simp [__smtx_finite_datatype_default] at h
  | SmtDatatype.sum c SmtDatatype.null, n, h => by
      have hc := finite_datatype_cons_default_subst_id s d (SmtValue.DtCons s0 d0 n) c h
      simp [__smtx_dt_substitute, hc]
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), n, h => by
      simp [__smtx_finite_datatype_default] at h
      by_cases hcEq :
          native_veq
              (__smtx_finite_datatype_cons_default (SmtValue.DtCons s0 d0 n) c)
              SmtValue.NotValue = true
      · simp [hcEq, native_and, native_not] at h
      · by_cases hdEq :
          native_veq
              (__smtx_finite_datatype_default s0 d0 (SmtDatatype.sum c2 d2)
                (native_nat_succ n))
              SmtValue.NotValue = true
        · simp [hcEq, hdEq, native_and, native_not] at h
        · have hcNe :
              __smtx_finite_datatype_cons_default (SmtValue.DtCons s0 d0 n) c ≠
                SmtValue.NotValue := by
            intro hh
            simp [hh, native_veq] at hcEq
          have hdNe :
              __smtx_finite_datatype_default s0 d0 (SmtDatatype.sum c2 d2)
                  (native_nat_succ n) ≠
                SmtValue.NotValue := by
            intro hh
            simp [hh, native_veq] at hdEq
          have hcSub := finite_datatype_cons_default_subst_id s d (SmtValue.DtCons s0 d0 n) c hcNe
          have hdSub :=
            finite_datatype_default_subst_id s d s0 d0 (SmtDatatype.sum c2 d2)
              (native_nat_succ n) hdNe
          simpa [__smtx_dt_substitute, hcSub] using hdSub

private theorem finite_datatype_cons_default_subst_id
    (s : native_String)
    (d : SmtDatatype)
    (v : SmtValue) :
    ∀ c,
      __smtx_finite_datatype_cons_default v c ≠ SmtValue.NotValue ->
        __smtx_dtc_substitute s d c = c
  | SmtDatatypeCons.unit, _ => by
      simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, h => by
      simp [__smtx_finite_datatype_cons_default] at h
      by_cases hT : native_veq (__smtx_finite_type_default T) SmtValue.NotValue = true
      · simp [hT] at h
      · have hTne : __smtx_finite_type_default T ≠ SmtValue.NotValue := by
          intro hh
          simp [hh, native_veq] at hT
        have hField := finite_type_default_subst_field_id s d T hTne
        have hcNe :
            __smtx_finite_datatype_cons_default
                (SmtValue.Apply v (__smtx_finite_type_default T)) c ≠
              SmtValue.NotValue := h.2
        have hc :=
          finite_datatype_cons_default_subst_id s d
            (SmtValue.Apply v (__smtx_finite_type_default T)) c hcNe
        cases T <;> simp [subst_field, __smtx_dtc_substitute, native_ite, native_Teq] at hField ⊢
        all_goals try simp [hField, hc]
        exact hField

end

mutual

private theorem finite_type_default_typed_canonical
    (T : SmtType)
    (h : __smtx_finite_type_default T ≠ SmtValue.NotValue) :
    __smtx_typeof_value (__smtx_finite_type_default T) = T ∧
      __smtx_value_canonical (__smtx_finite_type_default T) := by
  cases T with
  | Bool =>
      simp [__smtx_finite_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_finite_defaults_canonical]
  | BitVec w =>
      constructor
      · simp [__smtx_finite_type_default, __smtx_typeof_value, native_ite, native_and,
          native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total,
          native_nat_to_int, native_int_to_nat]
      · simp [__smtx_finite_type_default, __smtx_value_canonical,
          __smtx_value_finite_defaults_canonical]
  | Char =>
      simp [__smtx_finite_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_finite_defaults_canonical]
  | Datatype s d =>
      exact finite_datatype_default_typed_canonical s d h
  | Map A B =>
      by_cases hUnit : native_veq (__smtx_unit_type_default B) SmtValue.NotValue = true
      · simp [__smtx_finite_type_default, hUnit, native_not, native_and] at h ⊢
        by_cases hAeq : native_veq (__smtx_finite_type_default A) SmtValue.NotValue = true
        · simp [hAeq, native_not, native_and] at h
        · by_cases hBeq : native_veq (__smtx_finite_type_default B) SmtValue.NotValue = true
          · simp [hAeq, hBeq, native_not, native_and] at h
          · have hBne : __smtx_finite_type_default B ≠ SmtValue.NotValue := by
              intro hb
              simp [hb, native_veq] at hBeq
            have ihB := finite_type_default_typed_canonical B hBne
            simp [hAeq, hBeq, native_not, native_and, __smtx_typeof_value,
              __smtx_typeof_map_value, ihB.1, __smtx_value_canonical,
              __smtx_value_finite_defaults_canonical, __smtx_map_values_finite_defaults_canonical,
              __smtx_map_finite_default_canonical, __smtx_msm_get_default]
            simpa [__smtx_value_canonical] using ihB.2
      · have hUnitFalse :
            native_veq (__smtx_unit_type_default B) SmtValue.NotValue = false := by
          cases hUnitBool : native_veq (__smtx_unit_type_default B) SmtValue.NotValue <;>
            simp [hUnitBool] at hUnit ⊢
        simp [__smtx_finite_type_default, hUnitFalse, native_not, native_and] at h ⊢
        by_cases hBeq : native_veq (__smtx_finite_type_default B) SmtValue.NotValue = true
        · simp [hBeq, native_not, native_and] at h
        · have hBne : __smtx_finite_type_default B ≠ SmtValue.NotValue := by
            intro hb
            simp [hb, native_veq] at hBeq
          have ihB := finite_type_default_typed_canonical B hBne
          simp [hBeq, native_not, native_and, __smtx_typeof_value,
            __smtx_typeof_map_value, ihB.1, __smtx_value_canonical,
            __smtx_value_finite_defaults_canonical, __smtx_map_values_finite_defaults_canonical,
            __smtx_map_finite_default_canonical, __smtx_msm_get_default]
          simpa [__smtx_value_canonical] using ihB.2
  | Set A =>
      simp [__smtx_finite_type_default] at h ⊢
      by_cases hAeq : native_veq (__smtx_finite_type_default A) SmtValue.NotValue = true
      · simp [hAeq] at h
      · simp [hAeq, __smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type,
          __smtx_value_canonical, __smtx_value_finite_defaults_canonical,
          __smtx_map_values_finite_defaults_canonical, __smtx_map_finite_default_canonical,
          __smtx_msm_get_default, __smtx_finite_type_default]
  | FunType A B =>
      by_cases hUnit : native_veq (__smtx_unit_type_default B) SmtValue.NotValue = true
      · simp [__smtx_finite_type_default, hUnit, native_not, native_and] at h ⊢
        by_cases hAeq : native_veq (__smtx_finite_type_default A) SmtValue.NotValue = true
        · simp [hAeq, native_not, native_and] at h
        · by_cases hBeq : native_veq (__smtx_finite_type_default B) SmtValue.NotValue = true
          · simp [hAeq, hBeq, native_not, native_and] at h
          · have hBne : __smtx_finite_type_default B ≠ SmtValue.NotValue := by
              intro hb
              simp [hb, native_veq] at hBeq
            have ihB := finite_type_default_typed_canonical B hBne
            simp [hAeq, hBeq, native_not, native_and, __smtx_typeof_value,
              __smtx_typeof_map_value, __smtx_map_to_fun_type, ihB.1,
              __smtx_value_canonical, __smtx_value_finite_defaults_canonical,
              __smtx_map_values_finite_defaults_canonical, __smtx_map_finite_default_canonical,
              __smtx_msm_get_default]
            simpa [__smtx_value_canonical] using ihB.2
      · have hUnitFalse :
            native_veq (__smtx_unit_type_default B) SmtValue.NotValue = false := by
          cases hUnitBool : native_veq (__smtx_unit_type_default B) SmtValue.NotValue <;>
            simp [hUnitBool] at hUnit ⊢
        simp [__smtx_finite_type_default, hUnitFalse, native_not, native_and] at h ⊢
        by_cases hBeq : native_veq (__smtx_finite_type_default B) SmtValue.NotValue = true
        · simp [hBeq, native_not, native_and] at h
        · have hBne : __smtx_finite_type_default B ≠ SmtValue.NotValue := by
            intro hb
            simp [hb, native_veq] at hBeq
          have ihB := finite_type_default_typed_canonical B hBne
          simp [hBeq, native_not, native_and, __smtx_typeof_value,
            __smtx_typeof_map_value, __smtx_map_to_fun_type, ihB.1,
            __smtx_value_canonical, __smtx_value_finite_defaults_canonical,
            __smtx_map_values_finite_defaults_canonical, __smtx_map_finite_default_canonical,
            __smtx_msm_get_default]
          simpa [__smtx_value_canonical] using ihB.2
  | _ =>
      simp [__smtx_finite_type_default] at h

private theorem finite_datatype_default_typed_canonical
    (s : native_String) :
    ∀ d,
      __smtx_finite_datatype_default s d d native_nat_zero ≠ SmtValue.NotValue ->
      __smtx_typeof_value (__smtx_finite_datatype_default s d d native_nat_zero) =
          SmtType.Datatype s d ∧
        __smtx_value_canonical (__smtx_finite_datatype_default s d d native_nat_zero)
  | SmtDatatype.null, h => by
      simp [__smtx_finite_datatype_default] at h
  | SmtDatatype.sum c rest, h => by
      have hSub :=
        finite_datatype_default_subst_id s (SmtDatatype.sum c rest) s (SmtDatatype.sum c rest)
          (SmtDatatype.sum c rest) native_nat_zero h
      have hv :
          __smtx_typeof_value (SmtValue.DtCons s (SmtDatatype.sum c rest) native_nat_zero) =
            __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s (SmtDatatype.sum c rest))
              (SmtDatatype.sum c rest) native_nat_zero := by
        simpa [__smtx_typeof_value, hSub]
      have hvCanon :
          __smtx_value_canonical (SmtValue.DtCons s (SmtDatatype.sum c rest) native_nat_zero) := by
        simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]
      cases rest with
      | null =>
          exact finite_datatype_cons_default_typed_canonical
            (SmtType.Datatype s (SmtDatatype.sum c SmtDatatype.null)) SmtDatatype.null
            (SmtValue.DtCons s (SmtDatatype.sum c SmtDatatype.null) native_nat_zero)
            c hv hvCanon h
      | sum c2 d2 =>
          simp [__smtx_finite_datatype_default] at h ⊢
          by_cases hcEq :
              native_veq
                  (__smtx_finite_datatype_cons_default
                    (SmtValue.DtCons s (SmtDatatype.sum c (SmtDatatype.sum c2 d2)) native_nat_zero)
                    c)
                  SmtValue.NotValue = true
          · simp [hcEq, native_and, native_not] at h
          · by_cases hdEq :
              native_veq
                  (__smtx_finite_datatype_default s (SmtDatatype.sum c (SmtDatatype.sum c2 d2))
                    (SmtDatatype.sum c2 d2) (native_nat_succ native_nat_zero))
                  SmtValue.NotValue = true
            · simp [hcEq, hdEq, native_and, native_not] at h
            · have hcNe :
                  __smtx_finite_datatype_cons_default
                      (SmtValue.DtCons s (SmtDatatype.sum c (SmtDatatype.sum c2 d2))
                        native_nat_zero) c ≠
                    SmtValue.NotValue := by
                intro hh
                simp [hh, native_veq] at hcEq
              have hRes :=
                finite_datatype_cons_default_typed_canonical
                  (SmtType.Datatype s (SmtDatatype.sum c (SmtDatatype.sum c2 d2)))
                  (SmtDatatype.sum c2 d2)
                  (SmtValue.DtCons s (SmtDatatype.sum c (SmtDatatype.sum c2 d2))
                    native_nat_zero)
                  c hv hvCanon hcNe
              simpa [hcEq, hdEq, native_not, native_and] using hRes

private theorem finite_datatype_cons_default_typed_canonical
    (Tfinal : SmtType)
    (rest : SmtDatatype)
    (v : SmtValue) :
    ∀ c,
      __smtx_typeof_value v =
          __smtx_typeof_dt_cons_value_rec Tfinal (SmtDatatype.sum c rest) native_nat_zero ->
      __smtx_value_canonical v ->
      __smtx_finite_datatype_cons_default v c ≠ SmtValue.NotValue ->
      __smtx_typeof_value (__smtx_finite_datatype_cons_default v c) = Tfinal ∧
        __smtx_value_canonical (__smtx_finite_datatype_cons_default v c)
  | SmtDatatypeCons.unit, hv, hvCanon, _ => by
      simpa [__smtx_finite_datatype_cons_default, __smtx_typeof_dt_cons_value_rec] using
        And.intro hv hvCanon
  | SmtDatatypeCons.cons U c, hv, hvCanon, h => by
      simp [__smtx_finite_datatype_cons_default] at h ⊢
      by_cases hUeq : native_veq (__smtx_finite_type_default U) SmtValue.NotValue = true
      · simp [hUeq] at h
      · have hUFalse :
            native_veq (__smtx_finite_type_default U) SmtValue.NotValue = false := by
          cases hUb : native_veq (__smtx_finite_type_default U) SmtValue.NotValue <;>
            simp [hUb] at hUeq ⊢
        have hUne : __smtx_finite_type_default U ≠ SmtValue.NotValue := by
          intro hh
          simp [hh, native_veq] at hUeq
        have ihU := finite_type_default_typed_canonical U hUne
        have hUNone : U ≠ SmtType.None := by
          intro hNone
          subst U
          simp [__smtx_finite_type_default] at hUne
        have hApplyTy :
            __smtx_typeof_value (SmtValue.Apply v (__smtx_finite_type_default U)) =
              __smtx_typeof_dt_cons_value_rec Tfinal (SmtDatatype.sum c rest) native_nat_zero := by
          simp [__smtx_typeof_value, __smtx_typeof_apply_value,
            __smtx_typeof_dt_cons_value_rec, hv, ihU.1, __smtx_typeof_guard, native_ite,
            native_Teq, hUNone]
        have hApplyCanon :
            __smtx_value_canonical (SmtValue.Apply v (__smtx_finite_type_default U)) := by
          simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]
          constructor
          · simpa [__smtx_value_canonical] using hvCanon
          · simpa [__smtx_value_canonical] using ihU.2
        have hRes :=
          finite_datatype_cons_default_typed_canonical Tfinal rest
            (SmtValue.Apply v (__smtx_finite_type_default U)) c hApplyTy hApplyCanon h.2
        simpa [hUFalse] using hRes

end

private theorem finite_map_default_codomain_non_notvalue
    (A B : SmtType)
    (h : __smtx_finite_type_default (SmtType.Map A B) ≠ SmtValue.NotValue) :
    __smtx_finite_type_default B ≠ SmtValue.NotValue := by
  by_cases hUnit : native_veq (__smtx_unit_type_default B) SmtValue.NotValue = true
  · simp [__smtx_finite_type_default, hUnit, native_not, native_and] at h
    by_cases hAeq : native_veq (__smtx_finite_type_default A) SmtValue.NotValue = true
    · simp [hAeq, native_not, native_and] at h
    · by_cases hBeq : native_veq (__smtx_finite_type_default B) SmtValue.NotValue = true
      · simp [hAeq, hBeq, native_not, native_and] at h
      · intro hb
        simp [hb, native_veq] at hBeq
  · have hUnitFalse : native_veq (__smtx_unit_type_default B) SmtValue.NotValue = false := by
      cases hUnitBool : native_veq (__smtx_unit_type_default B) SmtValue.NotValue <;>
        simp [hUnitBool] at hUnit ⊢
    simp [__smtx_finite_type_default, hUnitFalse, native_not, native_and] at h
    by_cases hBeq : native_veq (__smtx_finite_type_default B) SmtValue.NotValue = true
    · simp [hBeq] at h
    · intro hb
      simp [hb, native_veq] at hBeq

mutual

private theorem canonical_value_of_typeof :
    ∀ v : SmtValue,
      ∃ v' : SmtValue,
        __smtx_typeof_value v' = __smtx_typeof_value v ∧ __smtx_value_canonical v'
  | SmtValue.Map m => by
      rcases canonical_map_of_typeof m with ⟨m', hmTy, hmDefault, hmValues⟩
      exact ⟨SmtValue.Map m', by simp [__smtx_typeof_value, hmTy],
        by
          simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]
          exact ⟨hmDefault, hmValues⟩⟩
  | SmtValue.Fun m => by
      rcases canonical_map_of_typeof m with ⟨m', hmTy, hmDefault, hmValues⟩
      exact ⟨SmtValue.Fun m', by simp [__smtx_typeof_value, hmTy],
        by
          simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]
          exact ⟨hmDefault, hmValues⟩⟩
  | SmtValue.Set m => by
      rcases canonical_map_of_typeof m with ⟨m', hmTy, hmDefault, hmValues⟩
      exact ⟨SmtValue.Set m', by simp [__smtx_typeof_value, hmTy],
        by
          simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]
          exact ⟨hmDefault, hmValues⟩⟩
  | SmtValue.Seq s => by
      rcases canonical_seq_of_typeof s with ⟨s', hsTy, hsCanon⟩
      exact ⟨SmtValue.Seq s', by simp [__smtx_typeof_value, hsTy],
        by simpa [__smtx_value_canonical, __smtx_value_finite_defaults_canonical] using hsCanon⟩
  | SmtValue.Apply f x => by
      rcases canonical_value_of_typeof f with ⟨f', hfTy, hfCanon⟩
      rcases canonical_value_of_typeof x with ⟨x', hxTy, hxCanon⟩
      exact ⟨SmtValue.Apply f' x', by simp [__smtx_typeof_value, hfTy, hxTy],
        by
          simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]
          exact ⟨by simpa [__smtx_value_canonical] using hfCanon,
            by simpa [__smtx_value_canonical] using hxCanon⟩⟩
  | SmtValue.NotValue => by
      exact ⟨SmtValue.NotValue, rfl,
        by simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]⟩
  | SmtValue.Boolean b => by
      exact ⟨SmtValue.Boolean b, rfl,
        by simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]⟩
  | SmtValue.Numeral n => by
      exact ⟨SmtValue.Numeral n, rfl,
        by simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]⟩
  | SmtValue.Rational q => by
      exact ⟨SmtValue.Rational q, rfl,
        by simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]⟩
  | SmtValue.Binary w n => by
      exact ⟨SmtValue.Binary w n, rfl,
        by simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]⟩
  | SmtValue.Char c => by
      exact ⟨SmtValue.Char c, rfl,
        by simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]⟩
  | SmtValue.UValue i e => by
      exact ⟨SmtValue.UValue i e, rfl,
        by simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]⟩
  | SmtValue.RegLan r => by
      exact ⟨SmtValue.RegLan r, rfl,
        by simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]⟩
  | SmtValue.DtCons s d i => by
      exact ⟨SmtValue.DtCons s d i, rfl,
        by simp [__smtx_value_canonical, __smtx_value_finite_defaults_canonical]⟩

private theorem canonical_map_of_typeof :
    ∀ m : SmtMap,
      ∃ m' : SmtMap,
        __smtx_typeof_map_value m' = __smtx_typeof_map_value m ∧
          __smtx_map_finite_default_canonical m' ∧
            __smtx_map_values_finite_defaults_canonical m'
  | SmtMap.default A e => by
      rcases canonical_value_of_typeof e with ⟨e', heTy, heCanon⟩
      let U := __smtx_typeof_value e
      by_cases hFin : __smtx_finite_type_default (SmtType.Map A U) = SmtValue.NotValue
      · refine ⟨SmtMap.default A e', ?_, ?_, ?_⟩
        · simp [__smtx_typeof_map_value, U, heTy]
        · simp [__smtx_map_finite_default_canonical, __smtx_typeof_map_value,
            __smtx_msm_get_default, U, heTy]
          intro hNe
          exact False.elim (hNe hFin)
        · simpa [__smtx_map_values_finite_defaults_canonical, __smtx_value_canonical] using
            heCanon
      · have hCodomain := finite_map_default_codomain_non_notvalue A U hFin
        have hDefault := finite_type_default_typed_canonical U hCodomain
        refine ⟨SmtMap.default A (__smtx_finite_type_default U), ?_, ?_, ?_⟩
        · simp [__smtx_typeof_map_value, U, hDefault.1]
        · simp [__smtx_map_finite_default_canonical, __smtx_typeof_map_value,
            __smtx_msm_get_default, hDefault.1]
        · simpa [__smtx_map_values_finite_defaults_canonical, __smtx_value_canonical] using
            hDefault.2
  | SmtMap.cons i e m => by
      rcases canonical_map_of_typeof m with ⟨m', hmTy, hmDefault, hmValues⟩
      by_cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m) = true
      · exact ⟨m', by simp [__smtx_typeof_map_value, hEq, hmTy, native_ite],
          hmDefault, hmValues⟩
      · have hEqFalse :
            native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
              (__smtx_typeof_map_value m) = false := by
          cases hEqBool :
              native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
                (__smtx_typeof_map_value m) <;>
            simp [hEqBool] at hEq ⊢
        let bad : SmtMap :=
          SmtMap.cons SmtValue.NotValue SmtValue.NotValue
            (SmtMap.default SmtType.Bool (SmtValue.Boolean false))
        refine ⟨bad, ?_, ?_, ?_⟩
        · have hBad : __smtx_typeof_map_value bad = SmtType.None := by
            simp [bad, __smtx_typeof_map_value, __smtx_typeof_value, native_Teq, native_ite]
          have hOrig :
              __smtx_typeof_map_value (SmtMap.cons i e m) = SmtType.None := by
            simp [__smtx_typeof_map_value, hEqFalse, native_ite]
          rw [hBad, hOrig]
        · simp [bad, __smtx_map_finite_default_canonical, __smtx_typeof_map_value,
            __smtx_typeof_value, native_Teq, native_ite]
        · simp [bad, __smtx_map_values_finite_defaults_canonical,
            __smtx_value_finite_defaults_canonical]

private theorem canonical_seq_of_typeof :
    ∀ s : SmtSeq,
      ∃ s' : SmtSeq,
        __smtx_typeof_seq_value s' = __smtx_typeof_seq_value s ∧
          __smtx_seq_values_finite_defaults_canonical s'
  | SmtSeq.empty T => by
      exact ⟨SmtSeq.empty T, rfl, by simp [__smtx_seq_values_finite_defaults_canonical]⟩
  | SmtSeq.cons v s => by
      rcases canonical_value_of_typeof v with ⟨v', hvTy, hvCanon⟩
      rcases canonical_seq_of_typeof s with ⟨s', hsTy, hsCanon⟩
      refine ⟨SmtSeq.cons v' s', ?_, ?_⟩
      · simp [__smtx_typeof_seq_value, hvTy, hsTy]
      · simp [__smtx_seq_values_finite_defaults_canonical]
        exact ⟨by simpa [__smtx_value_canonical] using hvCanon, hsCanon⟩

end

/-- Every inhabited Mini SMT type has a canonical inhabitant. -/
theorem canonical_type_inhabited_of_type_inhabited
    {T : SmtType}
    (hT : type_inhabited T) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
  rcases hT with ⟨v, hv⟩
  rcases canonical_value_of_typeof v with ⟨v', hvTy, hvCanon⟩
  exact ⟨v', by rw [hvTy, hv], hvCanon⟩

/-- Choice-based model that returns a canonical inhabitant for every inhabited SMT type. -/
noncomputable def default_typed_model : SmtModel := by
  classical
  exact fun k =>
    if h : type_inhabited k.ty then
      some (Classical.choose (canonical_type_inhabited_of_type_inhabited h))
    else
      none

end Smtm
