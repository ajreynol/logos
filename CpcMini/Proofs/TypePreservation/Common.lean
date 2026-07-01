import CpcMini.Proofs.TypePreservation.Predicates
import CpcMini.Proofs.TypePreservation.CanonicalAssumptions
import CpcMini.Proofs.Canonical.TypeDefaultBasic

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace Smtm

attribute [local simp] __smtx_type_wf_component

@[simp] theorem native_char_valid_zero :
    native_char_valid 0 = true := by
  native_decide

@[simp] theorem native_re_canonical_none :
    native_re_canonical native_re_none = true := by
  native_decide

/-- The typing conjunct carried by the inhabitation check. -/
theorem native_inhabited_type_typed {T : SmtType} (h : native_inhabited_type T = true) :
    native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true := by
  simp only [native_inhabited_type, native_and, Bool.and_eq_true] at h
  exact h.2

/-- The two facts carried by the inhabitation check: not `None`, and typed at the input. -/
theorem native_inhabited_type_parts {T : SmtType} (h : native_inhabited_type T = true) :
    T ≠ SmtType.None ∧ __smtx_typeof_value (__smtx_type_default T) = T := by
  refine ⟨?_, ?_⟩
  · intro hNone
    rw [hNone] at h
    simp [native_inhabited_type, native_and, native_not, native_Teq, __smtx_type_default,
      __smtx_type_default_rec, __smtx_typeof_value] at h
  · exact of_decide_eq_true (by simpa [native_Teq] using native_inhabited_type_typed h)

/-- Reassembles the inhabitation check from the not-`None` and typed facts. -/
theorem native_inhabited_type_of_typed {T : SmtType} (hNe : T ≠ SmtType.None)
    (hT : __smtx_typeof_value (__smtx_type_default T) = T) :
    native_inhabited_type T = true := by
  simp [native_inhabited_type, native_and, native_not, native_Teq, hT, hNe]

/-- Extracts semantic inhabitation from the generated Boolean inhabitation check. -/
theorem type_inhabited_of_native_inhabited_type
    (T : SmtType)
    (h : native_inhabited_type T = true) :
    type_inhabited T :=
  ⟨__smtx_type_default T, (native_inhabited_type_parts h).2⟩

/-- Extracts the concrete default witness carried by the generated Boolean inhabitation check. -/
theorem type_default_typed_canonical_of_native_inhabited_type
    (T : SmtType)
    (h : native_inhabited_type T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical (__smtx_type_default T) := by
  refine ⟨(native_inhabited_type_parts h).2, ?_⟩
  simpa [__smtx_value_canonical] using type_default_canonical_of_typed T (native_inhabited_type_typed h)

/-- Non-inhabited types fail the generated Boolean inhabitation check. -/
theorem native_inhabited_type_eq_false_of_not_type_inhabited
    (T : SmtType)
    (h : ¬ type_inhabited T) :
    native_inhabited_type T = false := by
  classical
  cases hNative : native_inhabited_type T
  · rfl
  · exact False.elim (h (type_inhabited_of_native_inhabited_type T hNative))

/-- Computes the well-formedness/inhabitation guard from a non-`None` result. -/
theorem smtx_typeof_guard_wf_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    __smtx_typeof_guard_wf T U = U := by
  intro h
  unfold __smtx_typeof_guard_wf at h ⊢
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h ⊢

/-- Extracts the component well-formedness facts from a well-formed function type. -/
theorem fun_type_wf_parts
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    native_inhabited_type A = true ∧
      __smtx_type_wf_rec A A = true ∧
        native_inhabited_type B = true ∧
          __smtx_type_wf_rec B B = true := by
  have hAll :
      (native_inhabited_type A = true ∧
        __smtx_type_wf_rec A A = true) ∧
          (native_inhabited_type B = true ∧
            __smtx_type_wf_rec B B = true) := by
    simpa [__smtx_type_wf, native_and] using h
  exact ⟨hAll.1.1, hAll.1.2, hAll.2.1, hAll.2.2⟩

/-- Compatibility name for the former native-function well-formedness helper. -/
theorem ifun_type_wf_parts
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    native_inhabited_type A = true ∧
      __smtx_type_wf_rec A A = true ∧
        native_inhabited_type B = true ∧
          __smtx_type_wf_rec B B = true := by
  exact fun_type_wf_parts h

/-- Extracts semantic inhabitation from a non-`None` guarded type. -/
theorem smtx_typeof_guard_wf_inhabited_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_wf T U ≠ SmtType.None ->
    type_inhabited T := by
  intro h
  unfold __smtx_typeof_guard_wf at h
  cases hWf : __smtx_type_wf T <;> simp [native_ite, hWf] at h
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl⟩
  · by_cases hFun : ∃ A B, T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, rfl⟩
      have hParts :
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A A = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B B = true := by
        exact fun_type_wf_parts hWf
      have hDef := type_default_typed_canonical_of_native_inhabited_type B hParts.2.2.1
      exact ⟨SmtValue.Fun native_default_ifun_id A B, by
        simp [__smtx_typeof_value, hDef.1]⟩
    · have hPair :
        native_inhabited_type T = true ∧
          __smtx_type_wf_rec T T = true := by
        cases T <;> simp [__smtx_type_wf, native_and] at hWf hReg hFun ⊢
        all_goals first | contradiction | assumption
      exact type_inhabited_of_native_inhabited_type T hPair.1

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
    (hRec : __smtx_type_wf_rec T T = true) :
    __smtx_type_wf T = true := by
  cases T <;> simp [__smtx_type_wf, __smtx_type_wf_rec, native_and, hInh, hRec] at *
  all_goals first | contradiction | exact hRec

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
      __smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x)

/-- Predicate asserting that a model returns a correctly typed value, or `NotValue`, at a given symbol and type. -/
def model_typed_at (M : SmtModel) (s : native_String) (T : SmtType) : Prop :=
  (__smtx_type_wf T = true -> __smtx_typeof_value (native_model_var_lookup M s T) = T) ∧
  (__smtx_type_wf T = false -> native_model_var_lookup M s T = SmtValue.NotValue)

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

/-- The generated Boolean inhabitation check accepts `bool`. -/
@[simp] theorem native_inhabited_type_bool :
    native_inhabited_type SmtType.Bool = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts `int`. -/
@[simp] theorem native_inhabited_type_int :
    native_inhabited_type SmtType.Int = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts `real`. -/
@[simp] theorem native_inhabited_type_real :
    native_inhabited_type SmtType.Real = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts regular languages. -/
@[simp] theorem native_inhabited_type_reglan :
    native_inhabited_type SmtType.RegLan = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts characters. -/
@[simp] theorem native_inhabited_type_char :
    native_inhabited_type SmtType.Char = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_value_canonical_bool, native_and, SmtEval.native_ite]

/-- The generated Boolean inhabitation check accepts uninterpreted sorts. -/
@[simp] theorem native_inhabited_type_usort (i : native_Nat) :
    native_inhabited_type (SmtType.USort i) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts sequences. -/
@[simp] theorem native_inhabited_type_seq (T : SmtType) :
    native_inhabited_type (SmtType.Seq T) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_typeof_seq_value, __smtx_value_canonical_bool, __smtx_seq_canonical,
    native_and]

/-- The generated Boolean inhabitation check accepts sets. -/
@[simp] theorem native_inhabited_type_set (A : SmtType) :
    native_inhabited_type (SmtType.Set A) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_typeof_map_value, __smtx_map_to_set_type, __smtx_value_canonical_bool,
    __smtx_map_canonical, __smtx_map_default_canonical, __smtx_msm_get_default,
    native_and]

/-- Maps have a generated default witness when their codomain does. -/
theorem native_inhabited_type_map {A B : SmtType}
    (hB : native_inhabited_type B = true) :
    native_inhabited_type (SmtType.Map A B) = true := by
  obtain ⟨hBne, hBty⟩ := native_inhabited_type_parts hB
  have hBty' : __smtx_typeof_value (__smtx_type_default_rec B B) = B := by
    simpa [__smtx_type_default] using hBty
  have hBval : __smtx_type_default_rec B B ≠ SmtValue.NotValue := by
    intro hNV; rw [hNV] at hBty'; simp [__smtx_typeof_value] at hBty'; exact hBne hBty'.symm
  apply native_inhabited_type_of_typed (by simp)
  show __smtx_typeof_value (__smtx_type_default (SmtType.Map A B)) = SmtType.Map A B
  rw [__smtx_type_default, __smtx_type_default_rec, native_ite,
    if_neg (by simpa [native_veq] using hBval)]
  simp [__smtx_typeof_value, __smtx_typeof_map_value, hBty']

/-- Function types have a generated default witness when their codomain does. -/
theorem native_inhabited_type_fun {A B : SmtType}
    (hB : native_inhabited_type B = true) :
    native_inhabited_type (SmtType.FunType A B) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_value_canonical_bool, native_and]

/-- Compatibility name for the former native-function inhabitation helper. -/
@[simp] theorem native_inhabited_type_ifun (A B : SmtType) :
    native_inhabited_type (SmtType.FunType A B) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec, __smtx_typeof_value, native_not, native_Teq,
    __smtx_value_canonical_bool, native_and]

/-- Every well-formed SMT type is semantically inhabited. -/
theorem type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    type_inhabited T := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl⟩
  · by_cases hFun : ∃ A B, T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, rfl⟩
      have hParts :
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A A = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B B = true := by
        exact fun_type_wf_parts hWF
      exact ⟨SmtValue.Fun native_default_ifun_id A B, rfl⟩
    · have hInh : native_inhabited_type T = true := by
        cases T <;> simp [__smtx_type_wf, native_and] at hWF hReg hFun ⊢
        all_goals first | contradiction | exact hWF.1 | simp [native_inhabited_type,
          __smtx_type_default, __smtx_typeof_value, __smtx_value_canonical_bool,
          native_and]
      exact type_inhabited_of_native_inhabited_type T hInh

/-- Extracts well-formedness of the element type of a well-formed sequence type. -/
theorem seq_type_wf_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Seq A) = true) :
    __smtx_type_wf A = true := by
  have hPair :
      native_inhabited_type A = true ∧ __smtx_type_wf_rec A A = true := by
    have hAll :
        native_inhabited_type (SmtType.Seq A) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A A = true := by
      simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
    exact hAll.2
  exact type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2

/-- Extracts well-formedness of the element type of a well-formed set type. -/
theorem set_type_wf_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    __smtx_type_wf A = true := by
  have hPair :
      native_inhabited_type A = true ∧ __smtx_type_wf_rec A A = true := by
    have hAll :
        native_inhabited_type (SmtType.Set A) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A A = true := by
      simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
    exact hAll.2
  exact type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2

/-- Extracts well-formedness of the domain and codomain of a well-formed map type. -/
theorem map_type_wf_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.Map A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  have hPair :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A A = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B B = true := by
    have hAll :
        native_inhabited_type (SmtType.Map A B) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A A = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B B = true := by
      simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
    exact hAll.2
  exact ⟨type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2.1,
    type_wf_of_inhabited_and_wf_rec hPair.2.2.1 hPair.2.2.2⟩

/-- Extracts well-formedness of the domain and codomain of a well-formed function type. -/
theorem fun_type_wf_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  have hPair :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A A = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B B = true := by
    exact fun_type_wf_parts h
  exact ⟨type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2.1,
    type_wf_of_inhabited_and_wf_rec hPair.2.2.1 hPair.2.2.2⟩

/-- Compatibility name for the former native-function component helper. -/
theorem ifun_type_wf_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  exact fun_type_wf_components_of_wf h

private theorem native_veq_notValue_false_of_ne
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    native_veq v SmtValue.NotValue = false := by
  simpa [native_veq] using h

private theorem ne_notValue_of_native_veq_notValue_false
    {v : SmtValue}
    (h : native_veq v SmtValue.NotValue = false) :
    v ≠ SmtValue.NotValue := by
  intro hEq
  subst hEq
  simp [native_veq] at h

private theorem dt_cons_wf_rec_tail_of_true
    {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF)
        (SmtDatatypeCons.cons TU cU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true := by
  cases TF <;> cases TU <;>
    simp [__smtx_dt_cons_wf_rec, native_ite, native_and] at h ⊢
  all_goals first | exact h | exact h.2 | exact h.2.2

private theorem dt_wf_cons_of_wf
    {cF cU : SmtDatatypeCons} {dF dU : SmtDatatype}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum cF dF) (SmtDatatype.sum cU dU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true := by
  cases hc : __smtx_dt_cons_wf_rec cF cU <;>
    simp [__smtx_dt_wf_rec, native_ite, hc] at h ⊢

private theorem dt_wf_tail_of_nonempty_tail_wf
    {cF cTailF cU cTailU : SmtDatatypeCons}
    {dTailF dTailU : SmtDatatype}
    (h : __smtx_dt_wf_rec
        (SmtDatatype.sum cF (SmtDatatype.sum cTailF dTailF))
        (SmtDatatype.sum cU (SmtDatatype.sum cTailU dTailU)) = true) :
    __smtx_dt_wf_rec (SmtDatatype.sum cTailF dTailF)
      (SmtDatatype.sum cTailU dTailU) = true := by
  have hc : __smtx_dt_cons_wf_rec cF cU = true :=
    dt_wf_cons_of_wf h
  simpa [__smtx_dt_wf_rec, native_ite, hc] using h

private theorem datatype_type_default_typed_canonical_of_wf_rec
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) (SmtType.Datatype s d) = true) :
      __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  exact cpcmini_datatype_type_default_typed_canonical_assumption s d _hInh _hRec

private theorem type_default_typed_canonical_of_wf_rec
    (T : SmtType) (hInh : native_inhabited_type T = true)
    (_hRec : __smtx_type_wf_rec T T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical (__smtx_type_default T) :=
  type_default_typed_canonical_of_native_inhabited_type T hInh

/-- Every well-formed Mini SMT type has a canonical inhabitant. -/
theorem canonical_type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl, by
      simp [__smtx_value_canonical, __smtx_value_canonical_bool]⟩
  · by_cases hFun : ∃ A B, T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, rfl⟩
      have hParts :
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A A = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B B = true := by
        exact fun_type_wf_parts hWF
      have hDef :=
        type_default_typed_canonical_of_native_inhabited_type
          (SmtType.FunType A B) (native_inhabited_type_fun hParts.2.2.1)
      exact ⟨__smtx_type_default (SmtType.FunType A B), hDef.1, hDef.2⟩
    · have hParts :
        native_inhabited_type T = true ∧
          __smtx_type_wf_rec T T = true := by
        cases T <;> simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hWF hReg hFun ⊢ <;>
          exact hWF
      have hDef :=
        type_default_typed_canonical_of_wf_rec T hParts.1 hParts.2
      exact ⟨__smtx_type_default T, hDef.1, hDef.2⟩

/-- The default value of an inhabited recursively well-formed Mini SMT type is canonical. -/
theorem type_default_typed_canonical_of_inhabited_wf_rec
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical (__smtx_type_default T) := by
  exact type_default_typed_canonical_of_wf_rec T hInh hRec

end Smtm
