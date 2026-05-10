import Cpc.Proofs.TermCompat
import Cpc.SmtModel

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
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl⟩
  · have hPair :
        native_inhabited_type T = true ∧
          __smtx_type_wf_rec T native_reflist_nil = true := by
      cases T <;> simp [__smtx_type_wf, native_and] at hWf hReg ⊢
      all_goals first | contradiction | assumption
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
  cases T <;> simp [__smtx_type_wf, native_and, hInh, hRec]

/-- Extracts well-formedness of the element type of a well-formed sequence type. -/
theorem seq_type_wf_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Seq A) = true) :
    __smtx_type_wf A = true := by
  have hPair :
      native_inhabited_type A = true ∧ __smtx_type_wf_rec A native_reflist_nil = true := by
    have hAll :
        native_inhabited_type (SmtType.Seq A) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A native_reflist_nil = true := by
      simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
    exact hAll.2
  exact type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2

/-- Extracts well-formedness of the element type of a well-formed set type. -/
theorem set_type_wf_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    __smtx_type_wf A = true := by
  have hPair :
      native_inhabited_type A = true ∧ __smtx_type_wf_rec A native_reflist_nil = true := by
    have hAll :
        native_inhabited_type (SmtType.Set A) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A native_reflist_nil = true := by
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
        __smtx_type_wf_rec A native_reflist_nil = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B native_reflist_nil = true := by
    have hAll :
        native_inhabited_type (SmtType.Map A B) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A native_reflist_nil = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B native_reflist_nil = true := by
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
        __smtx_type_wf_rec A native_reflist_nil = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B native_reflist_nil = true := by
    have hAll :
        native_inhabited_type (SmtType.FunType A B) = true ∧
          native_inhabited_type A = true ∧
            __smtx_type_wf_rec A native_reflist_nil = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B native_reflist_nil = true := by
      simpa [__smtx_type_wf, __smtx_type_wf_rec, native_and] using h
    exact hAll.2
  exact ⟨type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2.1,
    type_wf_of_inhabited_and_wf_rec hPair.2.2.1 hPair.2.2.2⟩

/-- A well-formed sequence type has a non-`None` element type. -/
theorem seq_type_component_non_none_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Seq A) = true) :
    A ≠ SmtType.None :=
  type_wf_non_none (seq_type_wf_component_of_wf h)

/-- A well-formed set type has a non-`None` element type. -/
theorem set_type_component_non_none_of_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    A ≠ SmtType.None :=
  type_wf_non_none (set_type_wf_component_of_wf h)

/-- A well-formed map type has non-`None` domain and codomain types. -/
theorem map_type_components_non_none_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.Map A B) = true) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  rcases map_type_wf_components_of_wf h with ⟨hA, hB⟩
  exact ⟨type_wf_non_none hA, type_wf_non_none hB⟩

/-- A well-formed function type has non-`None` domain and codomain types. -/
theorem fun_type_components_non_none_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  rcases fun_type_wf_components_of_wf h with ⟨hA, hB⟩
  exact ⟨type_wf_non_none hA, type_wf_non_none hB⟩

/-- A self-guarded sequence type equal to `Seq A` has a non-`None` element type. -/
theorem smtx_typeof_guard_wf_self_eq_seq_component_non_none
    {T A : SmtType}
    (h : __smtx_typeof_guard_wf T T = SmtType.Seq A) :
    A ≠ SmtType.None := by
  have hNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hT : T = SmtType.Seq A := by
    have hGuard := smtx_typeof_guard_wf_of_non_none T T hNN
    simpa [hGuard] using h
  subst hT
  exact seq_type_component_non_none_of_wf
    (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Seq A) (SmtType.Seq A) hNN)

/-- A self-guarded set type equal to `Set A` has a non-`None` element type. -/
theorem smtx_typeof_guard_wf_self_eq_set_component_non_none
    {T A : SmtType}
    (h : __smtx_typeof_guard_wf T T = SmtType.Set A) :
    A ≠ SmtType.None := by
  have hNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hT : T = SmtType.Set A := by
    have hGuard := smtx_typeof_guard_wf_of_non_none T T hNN
    simpa [hGuard] using h
  subst hT
  exact set_type_component_non_none_of_wf
    (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Set A) (SmtType.Set A) hNN)

/-- A self-guarded map type equal to `Map A B` has non-`None` components. -/
theorem smtx_typeof_guard_wf_self_eq_map_components_non_none
    {T A B : SmtType}
    (h : __smtx_typeof_guard_wf T T = SmtType.Map A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  have hNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hT : T = SmtType.Map A B := by
    have hGuard := smtx_typeof_guard_wf_of_non_none T T hNN
    simpa [hGuard] using h
  subst hT
  exact map_type_components_non_none_of_wf
    (smtx_typeof_guard_wf_wf_of_non_none (SmtType.Map A B) (SmtType.Map A B) hNN)

/-- A self-guarded function type equal to `FunType A B` has non-`None` components. -/
theorem smtx_typeof_guard_wf_self_eq_fun_components_non_none
    {T A B : SmtType}
    (h : __smtx_typeof_guard_wf T T = SmtType.FunType A B) :
    A ≠ SmtType.None ∧ B ≠ SmtType.None := by
  have hNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at h
    simp at h
  have hT : T = SmtType.FunType A B := by
    have hGuard := smtx_typeof_guard_wf_of_non_none T T hNN
    simpa [hGuard] using h
  subst hT
  exact fun_type_components_non_none_of_wf
    (smtx_typeof_guard_wf_wf_of_non_none (SmtType.FunType A B) (SmtType.FunType A B) hNN)

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

/-- Shows that the SMT type `reglan` is inhabited. -/
theorem type_inhabited_reglan : type_inhabited SmtType.RegLan :=
  ⟨SmtValue.RegLan native_re_none, rfl⟩

/-- Shows that the SMT type `char` is inhabited. -/
theorem type_inhabited_char : type_inhabited SmtType.Char :=
  ⟨SmtValue.Char 'a', rfl⟩

/-- Shows that every uninterpreted sort is inhabited. -/
theorem type_inhabited_usort (i : native_Nat) : type_inhabited (SmtType.USort i) :=
  ⟨SmtValue.UValue i 0, rfl⟩

/-- Shows that the SMT type `seq` is inhabited. -/
theorem type_inhabited_seq (T : SmtType) : type_inhabited (SmtType.Seq T) :=
  ⟨SmtValue.Seq (SmtSeq.empty T), rfl⟩

/-- Shows that the SMT type `map` is inhabited. -/
theorem type_inhabited_map {A B : SmtType} (hB : type_inhabited B) :
    type_inhabited (SmtType.Map A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Map (SmtMap.default A v), by simp [__smtx_typeof_value, __smtx_typeof_map_value, hv]⟩

/-- Shows that the SMT type `fun` is inhabited when its result type is inhabited. -/
theorem type_inhabited_fun {A B : SmtType} (hB : type_inhabited B) :
    type_inhabited (SmtType.FunType A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Fun (SmtMap.default A v), by
    simp [__smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_fun_type, hv]⟩

/-- Shows that the SMT type `set` is inhabited. -/
theorem type_inhabited_set (A : SmtType) : type_inhabited (SmtType.Set A) :=
  ⟨SmtValue.Set (SmtMap.default A (SmtValue.Boolean false)), by
    simp [__smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type]⟩

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
      · exfalso
        exact h (by simp [hcEq, native_and, native_not, native_ite])
      · by_cases hdEq :
          native_veq
              (__smtx_finite_datatype_default s0 d0 (SmtDatatype.sum c2 d2)
                (native_nat_succ n))
              SmtValue.NotValue = true
        · exfalso
          have hcFalse :
              native_veq
                  (__smtx_finite_datatype_cons_default (SmtValue.DtCons s0 d0 n) c)
                  SmtValue.NotValue = false := by
            cases hcBool :
                native_veq
                  (__smtx_finite_datatype_cons_default (SmtValue.DtCons s0 d0 n) c)
                  SmtValue.NotValue <;>
              simp [hcBool] at hcEq ⊢
          exact h (by simp [hcFalse, hdEq, native_and, native_not, native_ite])
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
      · exfalso
        exact h (by simp [hT, native_ite])
      · have hTne : __smtx_finite_type_default T ≠ SmtValue.NotValue := by
          intro hh
          simp [hh, native_veq] at hT
        have hTFalse :
            native_veq (__smtx_finite_type_default T) SmtValue.NotValue = false := by
          cases hTb : native_veq (__smtx_finite_type_default T) SmtValue.NotValue <;>
            simp [hTb] at hT ⊢
        have hField := finite_type_default_subst_field_id s d T hTne
        have hcNe :
            __smtx_finite_datatype_cons_default
                (SmtValue.Apply v (__smtx_finite_type_default T)) c ≠
              SmtValue.NotValue := by
          intro hh
          exact h (by simp [hTFalse, hh, native_ite])
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
  sorry

private theorem finite_datatype_default_typed_canonical
    (s : native_String) :
    ∀ d,
      __smtx_finite_datatype_default s d d native_nat_zero ≠ SmtValue.NotValue ->
      __smtx_typeof_value (__smtx_finite_datatype_default s d d native_nat_zero) =
          SmtType.Datatype s d ∧
        __smtx_value_canonical (__smtx_finite_datatype_default s d d native_nat_zero)
  := by
    intro d h
    sorry

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
  := by
    intro c hv hvCanon h
    sorry

end

private theorem finite_map_default_codomain_non_notvalue
    (A B : SmtType)
    (h : __smtx_finite_type_default (SmtType.Map A B) ≠ SmtValue.NotValue) :
    __smtx_finite_type_default B ≠ SmtValue.NotValue := by
  sorry

private theorem binary_canonical_of_type_guard
    (w n : native_Int)
    (hg :
      native_and (native_zleq 0 w)
        (native_zeq n (native_mod_total n (native_int_pow2 w))) = true) :
    __smtx_value_canonical (SmtValue.Binary w n) := by
  sorry

mutual

private theorem canonical_value_of_typeof :
    ∀ v : SmtValue,
      ∃ v' : SmtValue,
        __smtx_typeof_value v' = __smtx_typeof_value v ∧ __smtx_value_canonical v'
  := by
    intro v
    sorry

private theorem canonical_map_of_typeof :
    ∀ m : SmtMap,
      ∃ m' : SmtMap,
        __smtx_typeof_map_value m' = __smtx_typeof_map_value m ∧
          __smtx_map_canonical m' = true
  := by
    intro m
    sorry

private theorem canonical_seq_of_typeof :
    ∀ s : SmtSeq,
      ∃ s' : SmtSeq,
        __smtx_typeof_seq_value s' = __smtx_typeof_seq_value s ∧
          __smtx_seq_canonical s' = true
  := by
    intro s
    sorry

end

/-- Every inhabited Cpc SMT type has a canonical inhabitant. -/
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
