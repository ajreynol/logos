import Cpc.Proofs.TermCompat
import Cpc.SmtModel

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

namespace Smtm

/-- Extracts semantic inhabitation from the generated Boolean inhabitation check. -/
theorem type_inhabited_of_native_inhabited_type
    (T : SmtType)
    (h : native_inhabited_type T = true) :
    type_inhabited T := by
  classical
  have hPair :
      __smtx_typeof_value (__smtx_type_default T) = T ∧
        __smtx_value_canonical_bool (__smtx_type_default T) = true := by
    simpa [native_inhabited_type, native_and] using h
  exact ⟨__smtx_type_default T, hPair.1⟩

/-- Extracts the concrete default witness carried by the generated Boolean inhabitation check. -/
theorem type_default_typed_canonical_of_native_inhabited_type
    (T : SmtType)
    (h : native_inhabited_type T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical (__smtx_type_default T) := by
  classical
  have hPair :
      __smtx_typeof_value (__smtx_type_default T) = T ∧
        __smtx_value_canonical_bool (__smtx_type_default T) = true := by
    simpa [native_inhabited_type, native_and] using h
  exact ⟨hPair.1, by simpa [__smtx_value_canonical] using hPair.2⟩

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
      __smtx_type_wf_rec A native_reflist_nil = true ∧
        native_inhabited_type B = true ∧
          __smtx_type_wf_rec B native_reflist_nil = true := by
  have hAll :
      (native_inhabited_type A = true ∧
        __smtx_type_wf_rec A native_reflist_nil = true) ∧
          (native_inhabited_type B = true ∧
            __smtx_type_wf_rec B native_reflist_nil = true) := by
    simpa [__smtx_type_wf, native_and] using h
  exact ⟨hAll.1.1, hAll.1.2, hAll.2.1, hAll.2.2⟩

/-- Compatibility name for the former native-function well-formedness helper. -/
theorem ifun_type_wf_parts
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    native_inhabited_type A = true ∧
      __smtx_type_wf_rec A native_reflist_nil = true ∧
        native_inhabited_type B = true ∧
          __smtx_type_wf_rec B native_reflist_nil = true := by
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
            __smtx_type_wf_rec A native_reflist_nil = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B native_reflist_nil = true := by
        exact fun_type_wf_parts hWf
      have hDef := type_default_typed_canonical_of_native_inhabited_type B hParts.2.2.1
      exact ⟨SmtValue.Fun native_default_ifun_id A B, by
        simp [__smtx_typeof_value, hDef.1]⟩
    · have hPair :
        native_inhabited_type T = true ∧
          __smtx_type_wf_rec T native_reflist_nil = true := by
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

/-- Recursive well-formedness rejects `RegLan` at nested positions. -/
theorem type_wf_rec_ne_reglan
    {T : SmtType} {refs : RefList}
    (h : __smtx_type_wf_rec T refs = true) :
    T ≠ SmtType.RegLan := by
  intro hReg
  subst hReg
  simp [__smtx_type_wf_rec] at h

/-- Rebuilds public well-formedness from recursive well-formedness plus inhabitation. -/
theorem type_wf_of_inhabited_and_wf_rec
    {T : SmtType}
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T native_reflist_nil = true) :
    __smtx_type_wf T = true := by
  cases T <;> simp [__smtx_type_wf, __smtx_type_wf_rec, native_and, hInh, hRec] at *
  all_goals first | contradiction | exact hRec

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
            __smtx_type_wf_rec A native_reflist_nil = true ∧
              native_inhabited_type B = true ∧
                __smtx_type_wf_rec B native_reflist_nil = true := by
        exact fun_type_wf_parts hWF
      have hDef := type_default_typed_canonical_of_native_inhabited_type B hParts.2.2.1
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
        native_inhabited_type A = true ∧
          __smtx_type_wf_rec A native_reflist_nil = true ∧
            native_inhabited_type B = true ∧
              __smtx_type_wf_rec B native_reflist_nil = true := by
      exact fun_type_wf_parts h
    exact hAll
  exact ⟨type_wf_of_inhabited_and_wf_rec hPair.1 hPair.2.1,
    type_wf_of_inhabited_and_wf_rec hPair.2.2.1 hPair.2.2.2⟩

/-- Compatibility name for the former native-function component helper. -/
theorem ifun_type_wf_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf A = true ∧ __smtx_type_wf B = true := by
  exact fun_type_wf_components_of_wf h

/-- Extracts recursive well-formedness of the domain and codomain of a well-formed function type. -/
theorem fun_type_wf_rec_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf_rec A native_reflist_nil = true ∧
      __smtx_type_wf_rec B native_reflist_nil = true := by
  have hPair :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A native_reflist_nil = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B native_reflist_nil = true := by
    have hAll :
        native_inhabited_type A = true ∧
          __smtx_type_wf_rec A native_reflist_nil = true ∧
            native_inhabited_type B = true ∧
              __smtx_type_wf_rec B native_reflist_nil = true := by
      exact fun_type_wf_parts h
    exact hAll
  exact ⟨hPair.2.1, hPair.2.2.2⟩

/-- Compatibility name for the former native-function recursive component helper. -/
theorem ifun_type_wf_rec_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf_rec A native_reflist_nil = true ∧
      __smtx_type_wf_rec B native_reflist_nil = true := by
  exact fun_type_wf_rec_components_of_wf h

/-- The domain of a well-formed function type is not `RegLan`. -/
theorem fun_type_domain_ne_reglan_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    A ≠ SmtType.RegLan :=
  type_wf_rec_ne_reglan (fun_type_wf_rec_components_of_wf h).1

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
      __smtx_model_eval_apply M (__smtx_model_eval M f) (__smtx_model_eval M x)

/-- Predicate asserting that a model returns a correctly typed value for well-formed types,
or `NotValue` for non-well-formed types, at a given symbol and type. -/
def model_typed_at (M : SmtModel) (s : native_String) (T : SmtType) : Prop :=
  (__smtx_type_wf T = true -> __smtx_typeof_value (__smtx_model_lookup M s T) = T) ∧
  (__smtx_type_wf T = false -> __smtx_model_lookup M s T = SmtValue.NotValue)

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

/-- Maps have a generated default witness when their codomain does. -/
theorem native_inhabited_type_map
    {A B : SmtType}
    (hB : native_inhabited_type B = true) :
    native_inhabited_type (SmtType.Map A B) = true := by
  have hDef := type_default_typed_canonical_of_native_inhabited_type B hB
  have hCanon :
      __smtx_value_canonical_bool (__smtx_type_default B) = true := by
    simpa [__smtx_value_canonical] using hDef.2
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_typeof_map_value, __smtx_value_canonical_bool, __smtx_map_canonical,
    __smtx_map_default_canonical, native_and, hDef.1, hCanon]
  cases __smtx_is_finite_type A <;> simp [native_ite, native_veq]

/-- Builds well-formedness for the fallback map used by sequence nth defaults. -/
theorem seq_nth_wrong_map_type_wf
    {T : SmtType}
    (hTInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T native_reflist_nil = true) :
    __smtx_type_wf
      (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T)) = true := by
  have hIntInh : native_inhabited_type SmtType.Int = true := by
    simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
      __smtx_value_canonical_bool, native_and]
  have hSeqInh : native_inhabited_type (SmtType.Seq T) = true := by
    simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
      __smtx_typeof_seq_value, __smtx_value_canonical_bool, __smtx_seq_canonical,
      native_and]
  have hMapInh : native_inhabited_type (SmtType.Map SmtType.Int T) = true := by
    exact native_inhabited_type_map hTInh
  have hOuterInh :
      native_inhabited_type
        (SmtType.Map (SmtType.Seq T) (SmtType.Map SmtType.Int T)) = true :=
    by
      exact native_inhabited_type_map hMapInh
  simp [__smtx_type_wf, __smtx_type_wf_rec, native_and, hTInh, hRec, hIntInh,
    hSeqInh, hMapInh, hOuterInh]

/-- Shows that the SMT type `fun` is inhabited when its result type is inhabited. -/
theorem type_inhabited_fun {A B : SmtType} (hB : type_inhabited B) :
    type_inhabited (SmtType.FunType A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Fun native_default_ifun_id A B, rfl⟩

/-- Compatibility name for the former native function handle inhabitation helper. -/
theorem type_inhabited_ifun (A B : SmtType) :
    type_inhabited (SmtType.FunType A B) :=
  ⟨SmtValue.Fun native_default_ifun_id A B, rfl⟩

/-- Shows that the SMT type `set` is inhabited. -/
theorem type_inhabited_set (A : SmtType) : type_inhabited (SmtType.Set A) :=
  ⟨SmtValue.Set (SmtMap.default A (SmtValue.Boolean false)), by
    simp [__smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type]⟩

/-- The generated Boolean inhabitation check accepts `bool`. -/
@[simp] theorem native_inhabited_type_bool :
    native_inhabited_type SmtType.Bool = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts `int`. -/
@[simp] theorem native_inhabited_type_int :
    native_inhabited_type SmtType.Int = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts `real`. -/
@[simp] theorem native_inhabited_type_real :
    native_inhabited_type SmtType.Real = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts regular languages. -/
@[simp] theorem native_inhabited_type_reglan :
    native_inhabited_type SmtType.RegLan = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts characters. -/
@[simp] theorem native_inhabited_type_char :
    native_inhabited_type SmtType.Char = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts uninterpreted sorts. -/
@[simp] theorem native_inhabited_type_usort (i : native_Nat) :
    native_inhabited_type (SmtType.USort i) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_value_canonical_bool, native_and]

/-- The generated Boolean inhabitation check accepts sequences. -/
@[simp] theorem native_inhabited_type_seq (T : SmtType) :
    native_inhabited_type (SmtType.Seq T) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_typeof_seq_value, __smtx_value_canonical_bool, __smtx_seq_canonical,
    native_and]

/-- The generated Boolean inhabitation check accepts sets. -/
@[simp] theorem native_inhabited_type_set (A : SmtType) :
    native_inhabited_type (SmtType.Set A) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_typeof_map_value, __smtx_map_to_set_type, __smtx_value_canonical_bool,
    __smtx_map_canonical, __smtx_map_default_canonical, native_and]
  cases __smtx_is_finite_type A <;>
    simp [native_ite, native_veq, __smtx_type_default, __smtx_typeof_value]

/-- Function types have a generated default witness when their codomain does. -/
theorem native_inhabited_type_fun {A B : SmtType}
    (hB : native_inhabited_type B = true) :
    native_inhabited_type (SmtType.FunType A B) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_value_canonical_bool, native_and]

/-- Compatibility name for the former native-function inhabitation helper. -/
@[simp] theorem native_inhabited_type_ifun (A B : SmtType) :
    native_inhabited_type (SmtType.FunType A B) = true := by
  simp [native_inhabited_type, __smtx_type_default, __smtx_typeof_value,
    __smtx_value_canonical_bool, native_and]

end Smtm
