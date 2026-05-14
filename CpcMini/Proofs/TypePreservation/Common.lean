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

/-- Shows that the SMT type `seq` is inhabited. -/
theorem type_inhabited_seq (T : SmtType) : type_inhabited (SmtType.Seq T) :=
  ⟨SmtValue.Seq (SmtSeq.empty T), rfl⟩

/-- Shows that the SMT type `map` is inhabited. -/
theorem type_inhabited_map {A B : SmtType} (hB : type_inhabited B) :
    type_inhabited (SmtType.Map A B) := by
  rcases hB with ⟨v, hv⟩
  exact ⟨SmtValue.Map (SmtMap.default A v), by simp [__smtx_typeof_value, __smtx_typeof_map_value, hv]⟩

/-- Converts semantic inhabitation into the generated Boolean inhabitation test. -/
theorem native_inhabited_type_of_type_inhabited
    {T : SmtType}
    (h : type_inhabited T) :
    native_inhabited_type T = true :=
  (smtx_inhabited_type_eq_true_iff T).2 h

/-- Every well-formed SMT type is semantically inhabited. -/
theorem type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    type_inhabited T := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl⟩
  · have hInh : native_inhabited_type T = true := by
      cases T <;> simp [__smtx_type_wf, native_and] at hWF hReg ⊢
      all_goals first | contradiction | exact hWF.1
    exact (smtx_inhabited_type_eq_true_iff T).1 hInh

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

private theorem value_dt_substitute_canonical
    (s : native_String)
    (d : SmtDatatype) :
    (v : SmtValue) ->
      __smtx_value_canonical v ->
        __smtx_value_canonical (__smtx_value_dt_substitute s d v)
  | SmtValue.NotValue, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Boolean b, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Numeral n, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Rational q, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Binary w n, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Map m, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Fun m, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Set m, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Seq ss, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Char c, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.UValue i e, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.RegLan r, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.DtCons s' d' i, h => by
      simpa [__smtx_value_dt_substitute] using h
  | SmtValue.Apply f a, h => by
      simp [__smtx_value_canonical, __smtx_value_canonical_bool, native_and] at h
      have hOrig : __smtx_value_canonical (SmtValue.Apply f a) := by
        simp [__smtx_value_canonical, __smtx_value_canonical_bool, native_and]
        exact h
      have hf := value_dt_substitute_canonical s d f h.1
      have ha := value_dt_substitute_canonical s d a h.2
      cases hHead : __vsm_apply_head f with
      | DtCons s' d' i =>
          cases hShadow : native_streq s s'
          · simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
              hHead, hShadow, native_ite,
              __smtx_value_canonical, __smtx_value_canonical_bool, native_and]
            exact ⟨by simpa [__smtx_value_canonical] using hf,
              by simpa [__smtx_value_canonical] using ha⟩
          · simpa [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
              hHead, hShadow, native_ite] using hOrig
      | _ =>
          simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
            hHead, __smtx_value_canonical, __smtx_value_canonical_bool,
            native_and] at hf ha ⊢
          exact ⟨hf, ha⟩

private theorem value_dt_substitute_eq_notValue
    (s : native_String)
    (d : SmtDatatype) :
    (v : SmtValue) ->
      __smtx_value_dt_substitute s d v = SmtValue.NotValue ↔
        v = SmtValue.NotValue
  | SmtValue.NotValue => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Boolean b => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Numeral n => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Rational q => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Binary w n => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Map m => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Fun m => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Set m => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Seq ss => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Char c => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.UValue i e => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.RegLan r => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.DtCons s' d' i => by
      simp [__smtx_value_dt_substitute]
  | SmtValue.Apply f a => by
      cases hHead : __vsm_apply_head f with
      | DtCons s' d' i =>
          cases hShadow : native_streq s s' <;>
            simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
              hHead, hShadow, native_ite]
      | _ =>
          simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
            hHead]

private theorem value_dt_substitute_ne_notValue
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    __smtx_value_dt_substitute s d v ≠ SmtValue.NotValue := by
  intro hSub
  exact h ((value_dt_substitute_eq_notValue s d v).1 hSub)

private theorem value_dt_substitute_shadow_of_apply_head
    (s : native_String)
    (d : SmtDatatype) :
    (v : SmtValue) ->
      (∃ dHead i, __vsm_apply_head v = SmtValue.DtCons s dHead i) ->
        __smtx_value_dt_substitute s d v = v
  | SmtValue.NotValue, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean b, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral n, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational q, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary w n, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map m, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Fun m, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Set m, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq ss, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char c, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.UValue u e, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan r, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
  | SmtValue.DtCons s' d' i', hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      simp [__vsm_apply_head] at hHead
      rcases hHead with ⟨rfl, hEq⟩
      rcases hEq with ⟨rfl, rfl⟩
      simp [__smtx_value_dt_substitute, native_streq, native_ite]
  | SmtValue.Apply f a, hHead => by
      rcases hHead with ⟨dHead, i, hHead⟩
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons s dHead i := by
        simpa [__vsm_apply_head] using hHead
      simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
        hHeadF, native_streq, native_ite]

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

private theorem native_veq_value_dt_substitute_notValue_false
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (h : v ≠ SmtValue.NotValue) :
    native_veq (__smtx_value_dt_substitute s d v) SmtValue.NotValue = false := by
  have hSub := value_dt_substitute_ne_notValue s d h
  exact native_veq_notValue_false_of_ne hSub

private theorem value_dt_substitute_type_default_eq_of_not_datatype
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType)
    (hDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d') :
    __smtx_value_dt_substitute s d (__smtx_type_default T) =
      __smtx_type_default T := by
  cases T <;> simp [__smtx_type_default, __smtx_value_dt_substitute]
  case Datatype s' d' =>
    exact False.elim (hDatatype s' d' rfl)

private def smtx_dtc_field_substitute_type
    (s : native_String)
    (d : SmtDatatype) :
    SmtType -> SmtType
  | SmtType.Datatype s' d' =>
      SmtType.Datatype s'
        (native_ite (native_streq s s') d' (__smtx_dt_substitute s d d'))
  | T =>
      native_ite (native_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T

private theorem dtc_substitute_cons_eq
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType)
    (c : SmtDatatypeCons) :
    __smtx_dtc_substitute s d (SmtDatatypeCons.cons T c) =
      SmtDatatypeCons.cons (smtx_dtc_field_substitute_type s d T)
        (__smtx_dtc_substitute s d c) := by
  cases T <;>
    simp [smtx_dtc_field_substitute_type, __smtx_dtc_substitute]

private theorem typeof_dt_cons_value_rec_dtc_substitute_cons_zero
    (s : native_String)
    (d0 : SmtDatatype)
    (T : SmtType)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype) :
    __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
        (SmtDatatype.sum
          (__smtx_dtc_substitute s d0 (SmtDatatypeCons.cons T c))
          dTail)
        native_nat_zero =
      SmtType.DtcAppType (smtx_dtc_field_substitute_type s d0 T)
        (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
          (SmtDatatype.sum (__smtx_dtc_substitute s d0 c) dTail)
          native_nat_zero) := by
  simp [dtc_substitute_cons_eq, __smtx_typeof_dt_cons_value_rec]

private theorem typeof_apply_value_dtc_app
    {f v : SmtValue}
    {A B : SmtType}
    (hA : A ≠ SmtType.None)
    (hf : __smtx_typeof_value f = SmtType.DtcAppType A B)
    (hv : __smtx_typeof_value v = A) :
    __smtx_typeof_value (SmtValue.Apply f v) = B := by
  simp [__smtx_typeof_value, __smtx_typeof_apply_value, __smtx_typeof_guard,
    hf, hv, native_Teq, native_ite, hA]

private theorem value_canonical_apply
    {f v : SmtValue}
    (hf : __smtx_value_canonical f)
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (SmtValue.Apply f v) := by
  simpa [__smtx_value_canonical, __smtx_value_canonical_bool, native_and] using
    And.intro hf hv

private def smt_type_result_not_typeRef : SmtType -> Prop
  | SmtType.DtcAppType _ B => smt_type_result_not_typeRef B
  | SmtType.TypeRef _ => False
  | _ => True

private theorem typeof_dt_cons_value_rec_result_not_typeRef
    {T : SmtType}
    (hT : smt_type_result_not_typeRef T) :
    (d : SmtDatatype) ->
      (n : native_Nat) ->
        smt_type_result_not_typeRef (__smtx_typeof_dt_cons_value_rec T d n)
  | SmtDatatype.null, _ => by
      simp [__smtx_typeof_dt_cons_value_rec, smt_type_result_not_typeRef]
  | SmtDatatype.sum c dTail, native_nat_zero => by
      cases c with
      | unit =>
          simpa [__smtx_typeof_dt_cons_value_rec] using hT
      | cons U cTail =>
          simp [__smtx_typeof_dt_cons_value_rec, smt_type_result_not_typeRef]
          exact typeof_dt_cons_value_rec_result_not_typeRef hT
            (SmtDatatype.sum cTail dTail) native_nat_zero
  | SmtDatatype.sum c dTail, native_nat_succ n => by
      simpa [__smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_result_not_typeRef hT dTail n

private theorem typeof_apply_value_result_not_typeRef
    {A B : SmtType}
    (hA : smt_type_result_not_typeRef A) :
    smt_type_result_not_typeRef (__smtx_typeof_apply_value A B) := by
  cases A with
  | DtcAppType T U =>
      cases hArgNone : native_Teq T SmtType.None <;>
        cases hArgEq : native_Teq T B <;>
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
            smt_type_result_not_typeRef, native_ite, hArgNone, hArgEq] at hA ⊢
      exact hA
  | _ =>
      simp [__smtx_typeof_apply_value, smt_type_result_not_typeRef]

private theorem typeof_map_value_result_not_typeRef :
    (m : SmtMap) ->
      smt_type_result_not_typeRef (__smtx_typeof_map_value m)
  | SmtMap.default T e => by
      simp [__smtx_typeof_map_value, smt_type_result_not_typeRef]
  | SmtMap.cons i e m => by
      have hm := typeof_map_value_result_not_typeRef m
      cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m) <;>
        simp [__smtx_typeof_map_value, native_ite, hEq,
          smt_type_result_not_typeRef] at hm ⊢
      exact hm

private theorem map_to_fun_type_result_not_typeRef
    (T : SmtType) :
    smt_type_result_not_typeRef (__smtx_map_to_fun_type T) := by
  cases T <;> simp [__smtx_map_to_fun_type, smt_type_result_not_typeRef]

private theorem map_to_set_type_result_not_typeRef
    (T : SmtType) :
    smt_type_result_not_typeRef (__smtx_map_to_set_type T) := by
  cases T <;> simp [__smtx_map_to_set_type, smt_type_result_not_typeRef]
  case Map A B =>
    cases B <;> simp [__smtx_map_to_set_type, smt_type_result_not_typeRef]

private theorem typeof_seq_value_result_not_typeRef :
    (ss : SmtSeq) ->
      smt_type_result_not_typeRef (__smtx_typeof_seq_value ss)
  | SmtSeq.empty T => by
      simp [__smtx_typeof_seq_value, smt_type_result_not_typeRef]
  | SmtSeq.cons v ss => by
      have hs := typeof_seq_value_result_not_typeRef ss
      cases hEq :
          native_Teq (SmtType.Seq (__smtx_typeof_value v))
            (__smtx_typeof_seq_value ss) <;>
        simp [__smtx_typeof_seq_value, native_ite, hEq,
          smt_type_result_not_typeRef] at hs ⊢
      exact hs

private theorem typeof_value_result_not_typeRef :
    (v : SmtValue) ->
      smt_type_result_not_typeRef (__smtx_typeof_value v)
  | SmtValue.NotValue => by
      simp [__smtx_typeof_value, smt_type_result_not_typeRef]
  | SmtValue.Boolean _ => by
      simp [__smtx_typeof_value, smt_type_result_not_typeRef]
  | SmtValue.Numeral _ => by
      simp [__smtx_typeof_value, smt_type_result_not_typeRef]
  | SmtValue.Rational _ => by
      simp [__smtx_typeof_value, smt_type_result_not_typeRef]
  | SmtValue.Binary w n => by
      cases hBV :
          native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [__smtx_typeof_value, smt_type_result_not_typeRef,
          native_ite, hBV]
  | SmtValue.Map m => by
      simpa [__smtx_typeof_value] using
        typeof_map_value_result_not_typeRef m
  | SmtValue.Fun m => by
      exact map_to_fun_type_result_not_typeRef (__smtx_typeof_map_value m)
  | SmtValue.Set m => by
      exact map_to_set_type_result_not_typeRef (__smtx_typeof_map_value m)
  | SmtValue.Seq ss => by
      simpa [__smtx_typeof_value] using
        typeof_seq_value_result_not_typeRef ss
  | SmtValue.Char _ => by
      simp [__smtx_typeof_value, smt_type_result_not_typeRef]
  | SmtValue.UValue _ _ => by
      simp [__smtx_typeof_value, smt_type_result_not_typeRef]
  | SmtValue.RegLan _ => by
      simp [__smtx_typeof_value, smt_type_result_not_typeRef]
  | SmtValue.DtCons s d i => by
      simpa [__smtx_typeof_value, smt_type_result_not_typeRef] using
        typeof_dt_cons_value_rec_result_not_typeRef
          (T := SmtType.Datatype s d) (by
            simp [smt_type_result_not_typeRef])
          (__smtx_dt_substitute s d d) i
  | SmtValue.Apply f a => by
      exact typeof_apply_value_result_not_typeRef
        (typeof_value_result_not_typeRef f)

private theorem typeof_value_ne_typeRef
    (v : SmtValue)
    (r : native_String) :
    __smtx_typeof_value v ≠ SmtType.TypeRef r := by
  intro hTy
  have hNo := typeof_value_result_not_typeRef v
  rw [hTy] at hNo
  simpa [smt_type_result_not_typeRef] using hNo

private theorem native_inhabited_type_typeRef_false
    (r : native_String) :
    native_inhabited_type (SmtType.TypeRef r) = false := by
  have hNot : ¬ type_inhabited (SmtType.TypeRef r) := by
    intro h
    rcases h with ⟨v, hv⟩
    exact typeof_value_ne_typeRef v r hv
  exact (smtx_inhabited_type_eq_false_iff (SmtType.TypeRef r)).2 hNot

private def type_chain_result_datatype
    (s : native_String)
    (d : SmtDatatype) :
    SmtType -> Prop
  | SmtType.Datatype s' d' => s' = s ∧ d' = d
  | SmtType.DtcAppType _ B => type_chain_result_datatype s d B
  | _ => False

private theorem typeof_dt_cons_value_rec_chain_result_base_eq
    {s0 s : native_String}
    {d0 dTarget : SmtDatatype} :
    (d : SmtDatatype) ->
      (i : native_Nat) ->
        type_chain_result_datatype s dTarget
          (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s0 d0) d i) ->
          s0 = s ∧ d0 = dTarget
  | SmtDatatype.null, i, h => by
      cases i <;>
        simp [__smtx_typeof_dt_cons_value_rec,
          type_chain_result_datatype] at h
  | SmtDatatype.sum SmtDatatypeCons.unit dTail, native_nat_zero, h => by
      simpa [__smtx_typeof_dt_cons_value_rec,
        type_chain_result_datatype] using h
  | SmtDatatype.sum (SmtDatatypeCons.cons T c) dTail, native_nat_zero, h => by
      exact
        typeof_dt_cons_value_rec_chain_result_base_eq
          (s0 := s0) (s := s) (d0 := d0) (dTarget := dTarget)
          (SmtDatatype.sum c dTail) native_nat_zero
          (by
            simpa [__smtx_typeof_dt_cons_value_rec,
              type_chain_result_datatype] using h)
  | SmtDatatype.sum c dTail, native_nat_succ i, h => by
      exact
        typeof_dt_cons_value_rec_chain_result_base_eq
          (s0 := s0) (s := s) (d0 := d0) (dTarget := dTarget)
          dTail i
          (by
            simpa [__smtx_typeof_dt_cons_value_rec] using h)

private theorem typeof_map_value_not_type_chain_result_datatype
    (s : native_String)
    (d : SmtDatatype) :
    (m : SmtMap) ->
      ¬ type_chain_result_datatype s d (__smtx_typeof_map_value m)
  | SmtMap.default T e, h => by
      simpa [__smtx_typeof_map_value, type_chain_result_datatype] using h
  | SmtMap.cons i e m, h => by
      have hm := typeof_map_value_not_type_chain_result_datatype s d m
      cases hEq :
          native_Teq
            (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m) <;>
        simp [__smtx_typeof_map_value, native_ite, hEq,
          type_chain_result_datatype] at h hm
      exact hm h

private theorem map_to_fun_type_not_type_chain_result_datatype
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType) :
    ¬ type_chain_result_datatype s d (__smtx_map_to_fun_type T) := by
  cases T <;>
    simp [__smtx_map_to_fun_type, type_chain_result_datatype]

private theorem map_to_set_type_not_type_chain_result_datatype
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType) :
    ¬ type_chain_result_datatype s d (__smtx_map_to_set_type T) := by
  cases T <;>
    simp [__smtx_map_to_set_type, type_chain_result_datatype]
  case Map A B =>
    cases B <;>
      simp [__smtx_map_to_set_type, type_chain_result_datatype]

private theorem typeof_seq_value_not_type_chain_result_datatype
    (s : native_String)
    (d : SmtDatatype) :
    (ss : SmtSeq) ->
      ¬ type_chain_result_datatype s d (__smtx_typeof_seq_value ss)
  | SmtSeq.empty T, h => by
      simpa [__smtx_typeof_seq_value, type_chain_result_datatype] using h
  | SmtSeq.cons v ss, h => by
      have hs := typeof_seq_value_not_type_chain_result_datatype s d ss
      cases hEq :
          native_Teq (SmtType.Seq (__smtx_typeof_value v))
            (__smtx_typeof_seq_value ss) <;>
        simp [__smtx_typeof_seq_value, native_ite, hEq,
          type_chain_result_datatype] at h hs
      exact hs h

private theorem value_head_dtCons_of_type_chain_result_datatype
    (s : native_String)
    (d : SmtDatatype) :
    (v : SmtValue) ->
      type_chain_result_datatype s d (__smtx_typeof_value v) ->
        ∃ i, __vsm_apply_head v = SmtValue.DtCons s d i
  | SmtValue.NotValue, h => by
      simp [__smtx_typeof_value, type_chain_result_datatype] at h
  | SmtValue.Boolean b, h => by
      simp [__smtx_typeof_value, type_chain_result_datatype] at h
  | SmtValue.Numeral n, h => by
      simp [__smtx_typeof_value, type_chain_result_datatype] at h
  | SmtValue.Rational q, h => by
      simp [__smtx_typeof_value, type_chain_result_datatype] at h
  | SmtValue.Binary w n, h => by
      cases hBV :
          native_and (native_zleq 0 w)
            (native_zeq n (native_mod_total n (native_int_pow2 w))) <;>
        simp [__smtx_typeof_value, native_ite, hBV,
          type_chain_result_datatype] at h
  | SmtValue.Map m, h => by
      exact False.elim
        ((typeof_map_value_not_type_chain_result_datatype s d m) h)
  | SmtValue.Fun m, h => by
      exact False.elim
        ((map_to_fun_type_not_type_chain_result_datatype s d
          (__smtx_typeof_map_value m)) h)
  | SmtValue.Set m, h => by
      exact False.elim
        ((map_to_set_type_not_type_chain_result_datatype s d
          (__smtx_typeof_map_value m)) h)
  | SmtValue.Seq ss, h => by
      exact False.elim
        ((typeof_seq_value_not_type_chain_result_datatype s d ss) h)
  | SmtValue.Char c, h => by
      simp [__smtx_typeof_value, type_chain_result_datatype] at h
  | SmtValue.UValue i e, h => by
      simp [__smtx_typeof_value, type_chain_result_datatype] at h
  | SmtValue.RegLan r, h => by
      simp [__smtx_typeof_value, type_chain_result_datatype] at h
  | SmtValue.DtCons s0 d0 i, h => by
      have hBase :
          s0 = s ∧ d0 = d :=
        typeof_dt_cons_value_rec_chain_result_base_eq
          (s0 := s0) (s := s) (d0 := d0) (dTarget := d)
          (__smtx_dt_substitute s0 d0 d0) i
          (by simpa [__smtx_typeof_value] using h)
      rcases hBase with ⟨rfl, rfl⟩
      exact ⟨i, rfl⟩
  | SmtValue.Apply f a, h => by
      cases hf : __smtx_typeof_value f <;>
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hf,
          type_chain_result_datatype] at h
      case DtcAppType A B =>
        cases hNone : native_Teq A SmtType.None <;>
          cases hEq : native_Teq A (__smtx_typeof_value a) <;>
          simp [__smtx_typeof_guard, native_ite, hNone, hEq,
            type_chain_result_datatype] at h
        have hfChain :
            type_chain_result_datatype s d (__smtx_typeof_value f) := by
          simpa [hf, type_chain_result_datatype] using h
        rcases value_head_dtCons_of_type_chain_result_datatype s d f hfChain
          with ⟨i, hi⟩
        exact ⟨i, by simpa [__vsm_apply_head] using hi⟩

private theorem value_head_dtCons_of_datatype_type
    {s : native_String}
    {d : SmtDatatype}
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Datatype s d) :
    ∃ i, __vsm_apply_head v = SmtValue.DtCons s d i :=
  value_head_dtCons_of_type_chain_result_datatype s d v
    (by simpa [h, type_chain_result_datatype])

private def dt_result_num_args : SmtType -> Nat
  | SmtType.DtcAppType _ U => Nat.succ (dt_result_num_args U)
  | _ => 0

private def dt_applied_type_rec
    (s : native_String)
    (d0 : SmtDatatype) :
    SmtDatatype -> Nat -> Nat -> SmtType
  | d, i, 0 => __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i
  | SmtDatatype.sum (SmtDatatypeCons.cons _ c) d, 0, Nat.succ n =>
      dt_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n
  | SmtDatatype.sum c d, Nat.succ i, n =>
      dt_applied_type_rec s d0 d i n
  | _, _, _ => SmtType.None

private theorem dt_applied_type_rec_succ_index
    (s : native_String)
    (d0 : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      (d : SmtDatatype) ->
        (i n : Nat) ->
          dt_applied_type_rec s d0 (SmtDatatype.sum c d) (Nat.succ i) n =
            dt_applied_type_rec s d0 d i n
  | c, d, i, 0 => by
      cases c <;>
        simp [dt_applied_type_rec, __smtx_typeof_dt_cons_value_rec]
  | c, d, i, Nat.succ n => by
      cases c <;> simp [dt_applied_type_rec]

private theorem dt_result_num_args_typeof_dt_cons_value_rec
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i,
      dt_result_num_args
          (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i) =
        __smtx_dt_num_sels d i
  | SmtDatatype.null, i => by
      cases i <;>
        simp [dt_result_num_args, __smtx_typeof_dt_cons_value_rec,
          __smtx_dt_num_sels]
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0 => by
      simp [dt_result_num_args, __smtx_typeof_dt_cons_value_rec,
        __smtx_dt_num_sels, __smtx_dtc_num_sels]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0 => by
      simp [dt_result_num_args, __smtx_typeof_dt_cons_value_rec,
        __smtx_dt_num_sels, __smtx_dtc_num_sels,
        dt_result_num_args_typeof_dt_cons_value_rec s d0
          (SmtDatatype.sum c d) 0]
  | SmtDatatype.sum c d, Nat.succ i => by
      simp [__smtx_typeof_dt_cons_value_rec, __smtx_dt_num_sels,
        dt_result_num_args_typeof_dt_cons_value_rec s d0 d i]

private theorem dt_result_num_args_dt_applied_type_rec
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i n,
      dt_result_num_args (dt_applied_type_rec s d0 d i n) =
        __smtx_dt_num_sels d i - n
  | d, i, 0 => by
      simp [dt_applied_type_rec,
        dt_result_num_args_typeof_dt_cons_value_rec]
  | SmtDatatype.null, i, Nat.succ n => by
      cases i <;>
        simp [dt_applied_type_rec, dt_result_num_args, __smtx_dt_num_sels]
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, Nat.succ n => by
      simp [dt_applied_type_rec, dt_result_num_args, __smtx_dt_num_sels,
        __smtx_dtc_num_sels]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n => by
      have ih :=
        dt_result_num_args_dt_applied_type_rec s d0
          (SmtDatatype.sum c d) 0 n
      simpa [dt_applied_type_rec, __smtx_dt_num_sels,
        __smtx_dtc_num_sels] using ih
  | SmtDatatype.sum c d, Nat.succ i, n => by
      cases n with
      | zero =>
          simp [dt_applied_type_rec,
            dt_result_num_args_typeof_dt_cons_value_rec, __smtx_dt_num_sels]
      | succ n =>
          have ih :=
            dt_result_num_args_dt_applied_type_rec s d0 d i (Nat.succ n)
          simpa [dt_applied_type_rec, __smtx_dt_num_sels] using ih

private theorem dt_applied_type_rec_step
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i n,
      n < __smtx_dt_num_sels d i ->
      dt_applied_type_rec s d0 d i n =
        SmtType.DtcAppType (__smtx_ret_typeof_sel_rec d i n)
          (dt_applied_type_rec s d0 d i (Nat.succ n))
  | SmtDatatype.null, i, n, hlt => by
      cases i <;> simp [__smtx_dt_num_sels] at hlt
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, n, hlt => by
      simp [__smtx_dt_num_sels, __smtx_dtc_num_sels] at hlt
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, 0, _hlt => by
      simp [dt_applied_type_rec, __smtx_ret_typeof_sel_rec,
        __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n, hlt => by
      have hlt' : n < __smtx_dt_num_sels (SmtDatatype.sum c d) 0 := by
        simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using hlt
      simpa [dt_applied_type_rec, __smtx_ret_typeof_sel_rec] using
        dt_applied_type_rec_step s d0 (SmtDatatype.sum c d) 0 n hlt'
  | SmtDatatype.sum c d, Nat.succ i, n, hlt => by
      have hlt' : n < __smtx_dt_num_sels d i := by
        simpa [__smtx_dt_num_sels] using hlt
      cases n with
      | zero =>
          simpa [dt_applied_type_rec, __smtx_typeof_dt_cons_value_rec,
            __smtx_ret_typeof_sel_rec] using
            dt_applied_type_rec_step s d0 d i 0 hlt'
      | succ n =>
          simpa [dt_applied_type_rec, __smtx_ret_typeof_sel_rec] using
            dt_applied_type_rec_step s d0 d i (Nat.succ n) hlt'

private theorem dt_applied_type_rec_non_none_implies_le
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i n,
      dt_applied_type_rec s d0 d i n ≠ SmtType.None ->
      n ≤ __smtx_dt_num_sels d i
  | d, i, 0, _h => by
      simp
  | SmtDatatype.null, i, Nat.succ n, h => by
      cases i <;> simp [dt_applied_type_rec] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, Nat.succ n, h => by
      simp [dt_applied_type_rec] at h
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n, h => by
      have ih :=
        dt_applied_type_rec_non_none_implies_le s d0
          (SmtDatatype.sum c d) 0 n
      have h' :
          dt_applied_type_rec s d0 (SmtDatatype.sum c d) 0 n ≠
            SmtType.None := by
        simpa [dt_applied_type_rec] using h
      have hle : n ≤ __smtx_dt_num_sels (SmtDatatype.sum c d) 0 := ih h'
      simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels] using
        Nat.succ_le_succ hle
  | SmtDatatype.sum c d, Nat.succ i, n, h => by
      cases n with
      | zero =>
          simp [__smtx_dt_num_sels]
      | succ n =>
          have ih :=
            dt_applied_type_rec_non_none_implies_le s d0 d i (Nat.succ n)
          have h' :
              dt_applied_type_rec s d0 d i (Nat.succ n) ≠
                SmtType.None := by
            simpa [dt_applied_type_rec] using h
          have hle : Nat.succ n ≤ __smtx_dt_num_sels d i := ih h'
          simpa [__smtx_dt_num_sels] using hle

private def value_num_apply_args : SmtValue -> Nat
  | SmtValue.Apply f _ => Nat.succ (value_num_apply_args f)
  | _ => 0

private theorem value_num_apply_args_dt_substitute
    (s : native_String)
    (d : SmtDatatype) :
    (v : SmtValue) ->
      value_num_apply_args (__smtx_value_dt_substitute s d v) =
        value_num_apply_args v
  | SmtValue.NotValue => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Boolean b => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Numeral n => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Rational q => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Binary w n => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Map m => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Fun m => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Set m => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Seq q => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Char c => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.UValue i e => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.RegLan r => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.DtCons s' d' i => by
      simp [__smtx_value_dt_substitute, value_num_apply_args]
  | SmtValue.Apply f a => by
      cases hHead : __vsm_apply_head f with
      | DtCons s' d' i =>
          cases hShadow : native_streq s s' <;>
            simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
              hHead, hShadow, native_ite, value_num_apply_args,
              value_num_apply_args_dt_substitute s d f]
      | _ =>
          simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
            hHead, value_num_apply_args, value_num_apply_args_dt_substitute s d f]

private theorem value_dt_substitute_apply_head_of_dtCons
    (sub : native_String)
    (base : SmtDatatype) :
    (v : SmtValue) ->
      {s : native_String} ->
      {d : SmtDatatype} ->
      {i : native_Nat} ->
      __vsm_apply_head v = SmtValue.DtCons s d i ->
        __vsm_apply_head (__smtx_value_dt_substitute sub base v) =
          SmtValue.DtCons s
            (native_ite (native_streq sub s) d
              (__smtx_dt_substitute sub base d)) i
  | SmtValue.NotValue, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean b, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral n, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational q, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary w n, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map m, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Fun m, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Set m, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq q, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char c, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.UValue n e, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan r, s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.DtCons s' d' i', s, d, i, hHead => by
      simp [__vsm_apply_head] at hHead
      rcases hHead with ⟨rfl, rfl, rfl⟩
      simp [__smtx_value_dt_substitute, __vsm_apply_head]
  | SmtValue.Apply f a, s, d, i, hHead => by
      have hFunHead :
          __vsm_apply_head f = SmtValue.DtCons s d i := by
        simpa [__vsm_apply_head] using hHead
      cases hShadow : native_streq sub s <;>
        simp [__smtx_value_dt_substitute, __smtx_value_dt_substitute_apply,
          hFunHead, hShadow, native_ite, __vsm_apply_head,
          value_dt_substitute_apply_head_of_dtCons sub base f hFunHead]

private theorem dtc_num_sels_substitute
    (s : native_String)
    (d : SmtDatatype) :
    ∀ c, __smtx_dtc_num_sels (__smtx_dtc_substitute s d c) =
      __smtx_dtc_num_sels c
  | SmtDatatypeCons.unit => by
      simp [__smtx_dtc_substitute, __smtx_dtc_num_sels]
  | SmtDatatypeCons.cons T c => by
      cases T <;>
        simp [__smtx_dtc_substitute, __smtx_dtc_num_sels,
          dtc_num_sels_substitute s d c, native_ite, native_Teq,
          native_streq]

private theorem dt_num_sels_substitute
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i, __smtx_dt_num_sels (__smtx_dt_substitute s d0 d) i =
      __smtx_dt_num_sels d i
  | SmtDatatype.null, i => by
      cases i <;> simp [__smtx_dt_substitute, __smtx_dt_num_sels]
  | SmtDatatype.sum c d, native_nat_zero => by
      simp [__smtx_dt_substitute, __smtx_dt_num_sels,
        dtc_num_sels_substitute]
  | SmtDatatype.sum c d, native_nat_succ i => by
      simp [__smtx_dt_substitute, __smtx_dt_num_sels,
        dt_num_sels_substitute s d0 d i]

private theorem typeof_value_dt_cons_inner_eq_of_eq_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {U : SmtType}
    (h :
      __smtx_typeof_value (SmtValue.DtCons s d i) = U)
    (hU : U ≠ SmtType.None) :
    __smtx_typeof_dt_cons_value_rec
        (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i = U := by
  simpa [__smtx_typeof_value] using h

private theorem typeof_apply_value_non_none_cases
    {F X : SmtType}
    (h : __smtx_typeof_apply_value F X ≠ SmtType.None) :
    ∃ A B,
      F = SmtType.DtcAppType A B ∧
      X = A ∧
      A ≠ SmtType.None ∧
      B ≠ SmtType.None := by
  cases F with
  | DtcAppType A B =>
      cases X <;>
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite,
          native_Teq] at h
      all_goals first |
        contradiction |
        exact ⟨A, B, rfl, h.2.1.symm, h.1, h.2.2⟩
  | _ =>
      simp [__smtx_typeof_apply_value] at h

private theorem typeof_apply_value_eq_non_none_cases
    {F X T : SmtType}
    (h : __smtx_typeof_apply_value F X = T)
    (hT : T ≠ SmtType.None) :
    ∃ A,
      F = SmtType.DtcAppType A T ∧
        X = A ∧
        A ≠ SmtType.None := by
  cases F with
  | DtcAppType A B =>
      by_cases hANone : A = SmtType.None
      · subst A
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_Teq,
          native_ite] at h
        exact False.elim (hT h.symm)
      · by_cases hAX : A = X
        · subst X
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_Teq,
            native_ite, hANone] at h
          subst T
          exact ⟨A, rfl, rfl, hANone⟩
        · simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_Teq,
            native_ite, hANone, hAX] at h
          exact False.elim (hT h.symm)
  | _ =>
      simp [__smtx_typeof_apply_value] at h
      exact False.elim (hT h.symm)

private theorem dt_chain_type_of_non_none :
    ∀ {v : SmtValue} {s : native_String} {d : SmtDatatype}
        {i : native_Nat},
      __vsm_apply_head v = SmtValue.DtCons s d i ->
      __smtx_typeof_value v ≠ SmtType.None ->
      __smtx_typeof_value v =
        dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (value_num_apply_args v)
  | SmtValue.NotValue, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean b, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral n, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational q, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary w n, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map m, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Fun m, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Set m, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq ss, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char c, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.UValue u e, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan r, s, d, i, hHead, _hNN => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.DtCons s' d' i', s, d, i, hHead, hNN => by
      simp [__vsm_apply_head] at hHead
      rcases hHead with ⟨rfl, hEq⟩
      rcases hEq with ⟨rfl, rfl⟩
      have hTy :
          __smtx_typeof_value (SmtValue.DtCons s' d' i') =
            __smtx_typeof_dt_cons_value_rec
              (SmtType.Datatype s' d') (__smtx_dt_substitute s' d' d') i' := by
        symm
        exact typeof_value_dt_cons_inner_eq_of_eq_non_none rfl hNN
      rw [hTy]
      simp [dt_applied_type_rec, value_num_apply_args]
  | SmtValue.Apply f x, s, d, i, hHead, hNN => by
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons s d i := by
        simpa [__vsm_apply_head] using hHead
      have hFunNN : __smtx_typeof_value f ≠ SmtType.None := by
        intro hNone
        apply hNN
        simp [__smtx_typeof_value, hNone, __smtx_typeof_apply_value]
      have ihEq := dt_chain_type_of_non_none hHeadF hFunNN
      have hApplyNN :
          __smtx_typeof_apply_value (__smtx_typeof_value f)
              (__smtx_typeof_value x) ≠
            SmtType.None := by
        intro hNone
        apply hNN
        simp [__smtx_typeof_value, hNone]
      rcases typeof_apply_value_non_none_cases hApplyNN with
        ⟨A, B, hF, hX, hA, _hB⟩
      have hFunEq :
          dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
              (value_num_apply_args f) =
            SmtType.DtcAppType A B := by
        simpa [ihEq] using hF
      have hArgs :
          Nat.succ (dt_result_num_args B) =
            __smtx_dt_num_sels (__smtx_dt_substitute s d d) i -
              value_num_apply_args f := by
        have hArgs := congrArg dt_result_num_args hFunEq
        rw [dt_result_num_args_dt_applied_type_rec] at hArgs
        simpa [dt_result_num_args] using hArgs.symm
      have hlt :
          value_num_apply_args f <
            __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
        omega
      have hStep :=
        dt_applied_type_rec_step s d (__smtx_dt_substitute s d d) i
          (value_num_apply_args f) hlt
      have hB' :
          B =
            dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
              (Nat.succ (value_num_apply_args f)) := by
        have hCmp :
            SmtType.DtcAppType A B =
              SmtType.DtcAppType
                (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
                  (value_num_apply_args f))
                (dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
                  (Nat.succ (value_num_apply_args f))) := by
          calc
            SmtType.DtcAppType A B =
                dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
                  (value_num_apply_args f) := hFunEq.symm
            _ =
                SmtType.DtcAppType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
                    (value_num_apply_args f))
                  (dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
                    (Nat.succ (value_num_apply_args f))) := hStep
        injection hCmp with _ hB''
      simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite,
        native_Teq, __smtx_typeof_value, hF, hX, hA, value_num_apply_args,
        hB']

private theorem value_num_apply_args_eq_dt_num_sels_of_datatype
    {v : SmtValue}
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    value_num_apply_args v = __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
  have hChain := dt_chain_type_of_non_none hHead (by simp [hTy])
  have hEq :
      dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (value_num_apply_args v) =
        SmtType.Datatype s d := by
    calc
      dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (value_num_apply_args v) =
          __smtx_typeof_value v := by
            symm
            exact hChain
      _ = SmtType.Datatype s d := hTy
  have hArgs := congrArg dt_result_num_args hEq
  rw [dt_result_num_args_dt_applied_type_rec] at hArgs
  simp [dt_result_num_args] at hArgs
  have hle :
      value_num_apply_args v ≤ __smtx_dt_num_sels (__smtx_dt_substitute s d d) i :=
    dt_applied_type_rec_non_none_implies_le s d (__smtx_dt_substitute s d d) i
      (value_num_apply_args v) (by rw [hEq]; simp)
  omega

private theorem value_dt_substitute_datatype_head_full_args
    (sub : native_String)
    (base : SmtDatatype)
    {v : SmtValue}
    {s : native_String}
    {d : SmtDatatype}
    (hv : __smtx_typeof_value v = SmtType.Datatype s d)
    (hNe : native_streq sub s = false) :
    ∃ i,
      __vsm_apply_head (__smtx_value_dt_substitute sub base v) =
          SmtValue.DtCons s (__smtx_dt_substitute sub base d) i ∧
        value_num_apply_args (__smtx_value_dt_substitute sub base v) =
          __smtx_dt_num_sels
            (__smtx_dt_substitute s
              (__smtx_dt_substitute sub base d)
              (__smtx_dt_substitute sub base d)) i := by
  rcases value_head_dtCons_of_datatype_type hv with ⟨i, hHead⟩
  refine ⟨i, ?_, ?_⟩
  · have hHeadSub :=
      value_dt_substitute_apply_head_of_dtCons sub base v hHead
    simpa [hNe, native_ite] using hHeadSub
  · have hArgsSub := value_num_apply_args_dt_substitute sub base v
    have hArgsOrig :
        value_num_apply_args v =
          __smtx_dt_num_sels (__smtx_dt_substitute s d d) i :=
      value_num_apply_args_eq_dt_num_sels_of_datatype hHead hv
    calc
      value_num_apply_args (__smtx_value_dt_substitute sub base v) =
          value_num_apply_args v := hArgsSub
      _ = __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := hArgsOrig
      _ = __smtx_dt_num_sels d i := dt_num_sels_substitute s d d i
      _ = __smtx_dt_num_sels (__smtx_dt_substitute sub base d) i := by
          exact (dt_num_sels_substitute sub base d i).symm
      _ =
          __smtx_dt_num_sels
            (__smtx_dt_substitute s
              (__smtx_dt_substitute sub base d)
              (__smtx_dt_substitute sub base d)) i := by
          exact (dt_num_sels_substitute s
            (__smtx_dt_substitute sub base d)
            (__smtx_dt_substitute sub base d) i).symm

private theorem apply_arg_nth_type_of_non_none :
    ∀ {v : SmtValue} {s : native_String} {d : SmtDatatype}
        {i j : Nat},
      __vsm_apply_head v = SmtValue.DtCons s d i ->
      __smtx_typeof_value v ≠ SmtType.None ->
      j < value_num_apply_args v ->
      __smtx_typeof_value
          (__vsm_apply_arg_nth v j (value_num_apply_args v)) =
        __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i j
  | SmtValue.NotValue, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Boolean b, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Numeral n, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Rational q, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Binary w n, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Map m, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Fun m, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Set m, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Seq ss, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.Char c, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.UValue u e, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.RegLan r, s, d, i, j, hHead, _hNN, _hj => by
      simp [__vsm_apply_head] at hHead
  | SmtValue.DtCons s' d' i', s, d, i, j, _hHead, _hNN, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Apply f a, s, d, i, j, hHead, hNN, hj => by
      have hHeadF : __vsm_apply_head f = SmtValue.DtCons s d i := by
        simpa [__vsm_apply_head] using hHead
      have hFunNN : __smtx_typeof_value f ≠ SmtType.None := by
        intro hfNone
        apply hNN
        simp [__smtx_typeof_value, __smtx_typeof_apply_value, hfNone]
      have hChainF := dt_chain_type_of_non_none hHeadF hFunNN
      have hChainV := dt_chain_type_of_non_none hHead hNN
      have hSuccNN :
          dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
              (Nat.succ (value_num_apply_args f)) ≠
            SmtType.None := by
        intro hNone
        apply hNN
        rw [hChainV]
        simpa [value_num_apply_args] using hNone
      have hle :
          Nat.succ (value_num_apply_args f) ≤
            __smtx_dt_num_sels (__smtx_dt_substitute s d d) i :=
        dt_applied_type_rec_non_none_implies_le s d
          (__smtx_dt_substitute s d d) i
          (Nat.succ (value_num_apply_args f)) hSuccNN
      have hlt :
          value_num_apply_args f <
            __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
        omega
      have hStepF :=
        dt_applied_type_rec_step s d (__smtx_dt_substitute s d d) i
          (value_num_apply_args f) hlt
      by_cases hLast : j = value_num_apply_args f
      · subst hLast
        have hTyEq :
            __smtx_typeof_apply_value
                (SmtType.DtcAppType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
                    (value_num_apply_args f))
                  (dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
                    (Nat.succ (value_num_apply_args f))))
                (__smtx_typeof_value a) =
              dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
                (Nat.succ (value_num_apply_args f)) := by
          calc
            __smtx_typeof_apply_value
                (SmtType.DtcAppType
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
                    (value_num_apply_args f))
                  (dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
                    (Nat.succ (value_num_apply_args f))))
                (__smtx_typeof_value a) =
              __smtx_typeof_apply_value (__smtx_typeof_value f)
                (__smtx_typeof_value a) := by
                rw [hChainF, hStepF]
            _ = __smtx_typeof_value (SmtValue.Apply f a) := by
                simp [__smtx_typeof_value]
            _ = dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
                (Nat.succ (value_num_apply_args f)) := by
                simpa [value_num_apply_args] using hChainV
        have hArgTy :
            __smtx_typeof_value a =
              __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
                (value_num_apply_args f) := by
          by_cases hRNone :
              native_Teq
                (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
                  (value_num_apply_args f))
                SmtType.None
          · simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite,
              hRNone] at hTyEq
            exact (hSuccNN hTyEq.symm).elim
          · by_cases hEq :
                native_Teq
                  (__smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
                    (value_num_apply_args f))
                  (__smtx_typeof_value a)
            · have hEq' :
                  __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
                      (value_num_apply_args f) =
                    __smtx_typeof_value a := by
                simpa [native_Teq] using hEq
              exact hEq'.symm
            · simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite,
                hRNone, hEq] at hTyEq
              exact (hSuccNN hTyEq.symm).elim
        have hcond :
            SmtEval.native_nateq (value_num_apply_args f)
              (value_num_apply_args f) =
              true := by
          simp [SmtEval.native_nateq]
        simpa [__vsm_apply_arg_nth, value_num_apply_args, hcond] using hArgTy
      · have hjSucc : j < Nat.succ (value_num_apply_args f) := by
          simpa [value_num_apply_args] using hj
        have hj' : j < value_num_apply_args f := by
          have hle' : j ≤ value_num_apply_args f := Nat.lt_succ_iff.mp hjSucc
          cases Nat.eq_or_lt_of_le hle' with
          | inl hEq' =>
              exact False.elim (hLast hEq')
          | inr hLt =>
              exact hLt
        have hcond :
            SmtEval.native_nateq j (value_num_apply_args f) = false := by
          simp [SmtEval.native_nateq, hLast]
        simpa [__vsm_apply_arg_nth, value_num_apply_args, hcond] using
          apply_arg_nth_type_of_non_none hHeadF hFunNN hj'

private def smt_value_size : SmtValue -> Nat
  | SmtValue.Apply f a => Nat.succ (smt_value_size f + smt_value_size a)
  | _ => 1

private theorem apply_arg_nth_size_lt :
    (v : SmtValue) ->
      ∀ {j : Nat},
        j < value_num_apply_args v ->
          smt_value_size (__vsm_apply_arg_nth v j (value_num_apply_args v)) <
            smt_value_size v
  | SmtValue.NotValue, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Boolean b, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Numeral n, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Rational q, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Binary w n, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Map m, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Fun m, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Set m, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Seq ss, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Char c, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.UValue u e, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.RegLan r, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.DtCons s d i, j, hj => by
      simp [value_num_apply_args] at hj
  | SmtValue.Apply f a, j, hj => by
      by_cases hLast : j = value_num_apply_args f
      · subst j
        have hcond :
            SmtEval.native_nateq (value_num_apply_args f)
              (value_num_apply_args f) =
              true := by
          simp [SmtEval.native_nateq]
        simp [__vsm_apply_arg_nth, value_num_apply_args, hcond,
          native_ite, smt_value_size]
        omega
      · have hjSucc : j < Nat.succ (value_num_apply_args f) := by
          simpa [value_num_apply_args] using hj
        have hj' : j < value_num_apply_args f := by
          have hle : j ≤ value_num_apply_args f := Nat.lt_succ_iff.mp hjSucc
          cases Nat.eq_or_lt_of_le hle with
          | inl hEq =>
              exact False.elim (hLast hEq)
          | inr hLt =>
              exact hLt
        have hcond :
            SmtEval.native_nateq j (value_num_apply_args f) = false := by
          simp [SmtEval.native_nateq, hLast]
        have ih := apply_arg_nth_size_lt f hj'
        have hfLt :
            smt_value_size f < smt_value_size (SmtValue.Apply f a) := by
          simp [smt_value_size]
          omega
        have hArgLt :
            smt_value_size (__vsm_apply_arg_nth f j (value_num_apply_args f)) <
              smt_value_size (SmtValue.Apply f a) :=
          Nat.lt_trans ih hfLt
        simpa [__vsm_apply_arg_nth, value_num_apply_args, hcond,
          native_ite] using hArgLt

private theorem dt_cons_wf_rec_tail_of_true
    {T : SmtType} {c : SmtDatatypeCons} {refs : RefList}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases T <;> simp [__smtx_dt_cons_wf_rec, native_ite] at h ⊢
  all_goals first | exact h.2 | exact h.2.2

private theorem dt_wf_cons_of_wf
    {c : SmtDatatypeCons} {d : SmtDatatype} {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  cases d with
  | null =>
      simpa [__smtx_dt_wf_rec] using h
  | sum cTail dTail =>
      cases hc : __smtx_dt_cons_wf_rec c refs <;>
        simp [__smtx_dt_wf_rec, native_ite, hc] at h ⊢

private theorem dt_wf_tail_of_nonempty_tail_wf
    {c cTail : SmtDatatypeCons}
    {dTail : SmtDatatype}
    {refs : RefList}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum c (SmtDatatype.sum cTail dTail)) refs = true) :
    __smtx_dt_wf_rec (SmtDatatype.sum cTail dTail) refs = true := by
  have hc : __smtx_dt_cons_wf_rec c refs = true :=
    dt_wf_cons_of_wf h
  simpa [__smtx_dt_wf_rec, native_ite, hc] using h

private theorem reflist_contains_singleton_eq
    {s r : native_String}
    (h :
      native_reflist_contains (native_reflist_insert native_reflist_nil s) r =
        true) :
    r = s := by
  simpa [native_reflist_contains, native_reflist_insert, native_reflist_nil]
    using h

private theorem typeRef_head_singleton_cons_wf_eq
    {s r : native_String}
    {c : SmtDatatypeCons}
    (h :
      __smtx_dt_cons_wf_rec
          (SmtDatatypeCons.cons (SmtType.TypeRef r) c)
          (native_reflist_insert native_reflist_nil s) =
        true) :
    r = s := by
  have hContains :
      native_reflist_contains (native_reflist_insert native_reflist_nil s) r =
        true := by
    cases hRef :
        native_reflist_contains (native_reflist_insert native_reflist_nil s) r <;>
      simp [__smtx_dt_cons_wf_rec, native_ite, hRef] at h
    · rfl
  exact reflist_contains_singleton_eq hContains

private theorem typeRef_singleton_cons_wf_eq
    {s r : native_String}
    (h :
      __smtx_dt_cons_wf_rec
          (SmtDatatypeCons.cons (SmtType.TypeRef r) SmtDatatypeCons.unit)
          (native_reflist_insert native_reflist_nil s) =
        true) :
    r = s :=
  typeRef_head_singleton_cons_wf_eq h

private def datatype_cons_typeRef_fields_self
    (s : native_String) : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons (SmtType.TypeRef r) c =>
      r = s ∧ datatype_cons_typeRef_fields_self s c
  | SmtDatatypeCons.cons _ c => datatype_cons_typeRef_fields_self s c

private theorem datatype_cons_typeRef_fields_self_of_wf_singleton
    (s : native_String) :
    (c : SmtDatatypeCons) ->
      __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) =
          true ->
        datatype_cons_typeRef_fields_self s c
  | SmtDatatypeCons.unit, _hWF => by
      simp [datatype_cons_typeRef_fields_self]
  | SmtDatatypeCons.cons T c, hWF => by
      have hTail :
          __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) =
            true :=
        dt_cons_wf_rec_tail_of_true hWF
      cases T with
      | TypeRef r =>
          exact ⟨typeRef_head_singleton_cons_wf_eq hWF,
            datatype_cons_typeRef_fields_self_of_wf_singleton s c hTail⟩
      | _ =>
          simpa [datatype_cons_typeRef_fields_self] using
            datatype_cons_typeRef_fields_self_of_wf_singleton s c hTail

private theorem nested_datatype_field_head_wf_rec_of_cons_wf
    {sNested : native_String}
    {cNested : SmtDatatypeCons}
    {dNestedTail : SmtDatatype}
    {cTail : SmtDatatypeCons}
    {refs : RefList}
    (h :
      __smtx_dt_cons_wf_rec
          (SmtDatatypeCons.cons
            (SmtType.Datatype sNested (SmtDatatype.sum cNested dNestedTail))
            cTail)
          refs =
        true) :
    __smtx_dt_cons_wf_rec cNested
        (native_reflist_insert refs sNested) =
      true := by
  have hParts :
      native_inhabited_type
            (SmtType.Datatype sNested (SmtDatatype.sum cNested dNestedTail)) =
          true ∧
        __smtx_type_wf_rec
            (SmtType.Datatype sNested (SmtDatatype.sum cNested dNestedTail))
            refs =
          true := by
    have hAll :
        native_inhabited_type
              (SmtType.Datatype sNested (SmtDatatype.sum cNested dNestedTail)) =
            true ∧
          __smtx_type_wf_rec
              (SmtType.Datatype sNested (SmtDatatype.sum cNested dNestedTail))
              refs =
            true ∧
          __smtx_dt_cons_wf_rec cTail refs = true := by
      simpa [__smtx_dt_cons_wf_rec, native_ite] using h
    exact ⟨hAll.1, hAll.2.1⟩
  have hNestedWf :
      __smtx_dt_wf_rec (SmtDatatype.sum cNested dNestedTail)
          (native_reflist_insert refs sNested) =
        true := by
    simpa [__smtx_type_wf_rec] using hParts.2
  exact dt_wf_cons_of_wf (d := dNestedTail) hNestedWf

private def datatype_cons_default_productive
    (s : native_String)
    (d : SmtDatatype) :
    SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons T c =>
      __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
        SmtValue.NotValue ∧
      datatype_cons_default_productive s d c

private def datatype_default_productive_from
    (s : native_String)
    (d0 : SmtDatatype) :
    SmtDatatype -> Prop
  | SmtDatatype.null => False
  | SmtDatatype.sum c d =>
      datatype_cons_default_productive s d0 c ∨
      datatype_default_productive_from s d0 d

private def datatype_cons_no_deferred_fields : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons (SmtType.Datatype _ _) _ => False
  | SmtDatatypeCons.cons (SmtType.TypeRef _) _ => False
  | SmtDatatypeCons.cons _ c => datatype_cons_no_deferred_fields c

private def datatype_cons_has_typeRef_field : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => False
  | SmtDatatypeCons.cons (SmtType.TypeRef _) _ => True
  | SmtDatatypeCons.cons _ c => datatype_cons_has_typeRef_field c

private def datatype_cons_has_nonself_typeRef_field
    (s : native_String) : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => False
  | SmtDatatypeCons.cons (SmtType.TypeRef r) c =>
      r ≠ s ∨ datatype_cons_has_nonself_typeRef_field s c
  | SmtDatatypeCons.cons _ c =>
      datatype_cons_has_nonself_typeRef_field s c

private theorem datatype_cons_typeRef_fields_self_or_nonself
    (s : native_String) :
    (c : SmtDatatypeCons) ->
      datatype_cons_typeRef_fields_self s c ∨
        datatype_cons_has_nonself_typeRef_field s c
  | SmtDatatypeCons.unit => by
      exact Or.inl (by simp [datatype_cons_typeRef_fields_self])
  | SmtDatatypeCons.cons T c => by
      cases T with
      | TypeRef r =>
          by_cases hr : r = s
          · cases datatype_cons_typeRef_fields_self_or_nonself s c with
            | inl hTailSelf =>
                exact Or.inl (by
                  simp [datatype_cons_typeRef_fields_self, hr, hTailSelf])
            | inr hTailNonself =>
                exact Or.inr (by
                  simp [datatype_cons_has_nonself_typeRef_field,
                    hTailNonself])
          · exact Or.inr (by
              simp [datatype_cons_has_nonself_typeRef_field, hr])
      | _ =>
          cases datatype_cons_typeRef_fields_self_or_nonself s c with
          | inl hTailSelf =>
              exact Or.inl (by
                simpa [datatype_cons_typeRef_fields_self] using hTailSelf)
          | inr hTailNonself =>
              exact Or.inr (by
                simpa [datatype_cons_has_nonself_typeRef_field] using
                  hTailNonself)

private def datatype_cons_has_datatype_null_field : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => False
  | SmtDatatypeCons.cons (SmtType.Datatype _ SmtDatatype.null) _ => True
  | SmtDatatypeCons.cons _ c => datatype_cons_has_datatype_null_field c

private theorem typeRef_field_selector_type_of_has_typeRef_field
    (s : native_String)
    (d0 : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      (dTail : SmtDatatype) ->
        datatype_cons_typeRef_fields_self s c ->
          datatype_cons_has_typeRef_field c ->
            ∃ j,
              j < __smtx_dtc_num_sels c ∧
                __smtx_ret_typeof_sel_rec
                    (SmtDatatype.sum (__smtx_dtc_substitute s d0 c) dTail)
                    native_nat_zero j =
                  SmtType.Datatype s d0
  | SmtDatatypeCons.unit, dTail, _hSelf, hHas => by
      simp [datatype_cons_has_typeRef_field] at hHas
  | SmtDatatypeCons.cons T c, dTail, hSelf, hHas => by
      cases T with
      | TypeRef r =>
          have hr : r = s := hSelf.1
          exact ⟨0, by simp [__smtx_dtc_num_sels],
            by
              subst hr
              simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
                native_ite, native_Teq]⟩
      | _ =>
          have hTailSelf : datatype_cons_typeRef_fields_self s c := by
            simpa [datatype_cons_typeRef_fields_self] using hSelf
          have hTailHas : datatype_cons_has_typeRef_field c := by
            simpa [datatype_cons_has_typeRef_field] using hHas
          rcases typeRef_field_selector_type_of_has_typeRef_field s d0 c dTail
              hTailSelf hTailHas with
            ⟨j, hjLt, hjTy⟩
          exact ⟨Nat.succ j,
            by simpa [__smtx_dtc_num_sels] using Nat.succ_lt_succ hjLt,
            by
              simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
                native_ite, native_Teq, native_streq] using hjTy⟩

private theorem nonself_typeRef_field_selector_type
    (s : native_String)
    (d0 : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      (dTail : SmtDatatype) ->
        datatype_cons_has_nonself_typeRef_field s c ->
          ∃ j r,
            j < __smtx_dtc_num_sels c ∧
              r ≠ s ∧
                __smtx_ret_typeof_sel_rec
                    (SmtDatatype.sum (__smtx_dtc_substitute s d0 c) dTail)
                    native_nat_zero j =
                  SmtType.TypeRef r
  | SmtDatatypeCons.unit, dTail, hNonself => by
      simp [datatype_cons_has_nonself_typeRef_field] at hNonself
  | SmtDatatypeCons.cons T c, dTail, hNonself => by
      cases T with
      | TypeRef r =>
          cases hNonself with
          | inl hNe =>
              exact ⟨0, r, by simp [__smtx_dtc_num_sels], hNe, by
                simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
                  native_Teq, native_ite, hNe]⟩
          | inr hTailNonself =>
              rcases nonself_typeRef_field_selector_type s d0 c dTail
                  hTailNonself with
                ⟨j, rTail, hjLt, hNe, hjTy⟩
              exact ⟨Nat.succ j, rTail,
                by simpa [__smtx_dtc_num_sels] using Nat.succ_lt_succ hjLt,
                hNe,
                by
                  simpa [__smtx_dtc_substitute,
                    __smtx_ret_typeof_sel_rec, native_Teq, native_ite]
                    using hjTy⟩
      | _ =>
          rcases nonself_typeRef_field_selector_type s d0 c dTail
              (by
                simpa [datatype_cons_has_nonself_typeRef_field] using
                  hNonself) with
            ⟨j, rTail, hjLt, hNe, hjTy⟩
          exact ⟨Nat.succ j, rTail,
            by simpa [__smtx_dtc_num_sels] using Nat.succ_lt_succ hjLt,
            hNe,
            by
              simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec,
                native_Teq, native_ite, native_streq] using hjTy⟩

private def datatype_cons_simple_defaultable_fields : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons (SmtType.TypeRef _) _ => False
  | SmtDatatypeCons.cons (SmtType.Datatype _ SmtDatatype.null) _ => False
  | SmtDatatypeCons.cons
      (SmtType.Datatype _ (SmtDatatype.sum SmtDatatypeCons.unit _)) c =>
      datatype_cons_simple_defaultable_fields c
  | SmtDatatypeCons.cons (SmtType.Datatype _ (SmtDatatype.sum (SmtDatatypeCons.cons _ _) _)) _ =>
      False
  | SmtDatatypeCons.cons _ c => datatype_cons_simple_defaultable_fields c

private theorem dt_cons_wf_rec_false_of_has_datatype_null_field
    {refs : RefList} :
    (c : SmtDatatypeCons) ->
      datatype_cons_has_datatype_null_field c ->
        __smtx_dt_cons_wf_rec c refs = true ->
          False
  | SmtDatatypeCons.unit, hHas, _hWF => by
      simp [datatype_cons_has_datatype_null_field] at hHas
  | SmtDatatypeCons.cons T c, hHas, hWF => by
      cases T with
      | Datatype sNested dNested =>
          cases dNested with
          | null =>
              simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec,
                __smtx_dt_wf_rec, native_ite] at hWF
          | sum cNested dNestedTail =>
              have hTailHas : datatype_cons_has_datatype_null_field c := by
                simpa [datatype_cons_has_datatype_null_field] using hHas
              exact dt_cons_wf_rec_false_of_has_datatype_null_field c
                hTailHas (dt_cons_wf_rec_tail_of_true hWF)
      | _ =>
          have hTailHas : datatype_cons_has_datatype_null_field c := by
            simpa [datatype_cons_has_datatype_null_field] using hHas
          exact dt_cons_wf_rec_false_of_has_datatype_null_field c
            hTailHas (dt_cons_wf_rec_tail_of_true hWF)

private def datatype_cons_default_args_typed
    (s : native_String)
    (d0 : SmtDatatype) :
    SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => True
  | SmtDatatypeCons.cons T c =>
      __smtx_typeof_value
          (__smtx_value_dt_substitute s d0 (__smtx_type_default T)) =
        smtx_dtc_field_substitute_type s d0 T ∧
      smtx_dtc_field_substitute_type s d0 T ≠ SmtType.None ∧
      __smtx_value_canonical
          (__smtx_value_dt_substitute s d0 (__smtx_type_default T)) ∧
      datatype_cons_default_args_typed s d0 c

private theorem datatype_cons_default_args_typed_false_of_has_typeRef_field
    (s : native_String)
    (d0 : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      datatype_cons_has_typeRef_field c ->
        datatype_cons_default_args_typed s d0 c ->
          False
  | SmtDatatypeCons.unit, hHas, _hArgs => by
      simp [datatype_cons_has_typeRef_field] at hHas
  | SmtDatatypeCons.cons T c, hHas, hArgs => by
      cases T <;> try
        exact datatype_cons_default_args_typed_false_of_has_typeRef_field s d0 c
          (by simpa [datatype_cons_has_typeRef_field] using hHas)
          hArgs.2.2.2
      case TypeRef r =>
          have hTy :
              __smtx_typeof_value
                  (__smtx_value_dt_substitute s d0
                    (__smtx_type_default (SmtType.TypeRef r))) =
                smtx_dtc_field_substitute_type s d0 (SmtType.TypeRef r) :=
            hArgs.1
          cases hEq : native_Teq (SmtType.TypeRef r) (SmtType.TypeRef s) <;>
            simp [__smtx_type_default, __smtx_value_dt_substitute,
              __smtx_typeof_value, smtx_dtc_field_substitute_type,
              native_ite, hEq] at hTy

private theorem datatype_cons_default_args_typed_of_no_typeRef_with_field_defaults
    (s : native_String)
    (d0 : SmtDatatype)
    (refs : RefList)
    (hField :
      ∀ T,
        (∀ r, T ≠ SmtType.TypeRef r) ->
          native_inhabited_type T = true ->
            __smtx_type_wf_rec T refs = true ->
              __smtx_typeof_value
                  (__smtx_value_dt_substitute s d0 (__smtx_type_default T)) =
                smtx_dtc_field_substitute_type s d0 T ∧
              smtx_dtc_field_substitute_type s d0 T ≠ SmtType.None ∧
              __smtx_value_canonical
                (__smtx_value_dt_substitute s d0 (__smtx_type_default T))) :
    (c : SmtDatatypeCons) ->
      __smtx_dt_cons_wf_rec c refs = true ->
        ¬ datatype_cons_has_typeRef_field c ->
          datatype_cons_default_args_typed s d0 c
  | SmtDatatypeCons.unit, _hWF, _hNo => by
      simp [datatype_cons_default_args_typed]
  | SmtDatatypeCons.cons T c, hWF, hNo => by
      have hNotTypeRef : ∀ r, T ≠ SmtType.TypeRef r := by
        intro r hEq
        apply hNo
        subst hEq
        simp [datatype_cons_has_typeRef_field]
      have hTailNo : ¬ datatype_cons_has_typeRef_field c := by
        intro hTail
        apply hNo
        cases T <;> simp [datatype_cons_has_typeRef_field, hTail]
      have hParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T refs = true ∧
            __smtx_dt_cons_wf_rec c refs = true := by
        cases T <;>
          simp_all [__smtx_dt_cons_wf_rec, datatype_cons_has_typeRef_field,
            native_ite]
      have hHead := hField T hNotTypeRef hParts.1 hParts.2.1
      have hTail :=
        datatype_cons_default_args_typed_of_no_typeRef_with_field_defaults
          s d0 refs hField c hParts.2.2 hTailNo
      exact ⟨hHead.1, hHead.2.1, hHead.2.2, hTail⟩

private theorem datatype_cons_default_args_typed_of_no_typeRef_with_field_defaults_bounded
    (s : native_String)
    (d0 : SmtDatatype)
    (refs : RefList)
    (limit : Nat)
    (hField :
      ∀ T,
        sizeOf T < limit ->
        (∀ r, T ≠ SmtType.TypeRef r) ->
          native_inhabited_type T = true ->
            __smtx_type_wf_rec T refs = true ->
              __smtx_typeof_value
                  (__smtx_value_dt_substitute s d0 (__smtx_type_default T)) =
                smtx_dtc_field_substitute_type s d0 T ∧
              smtx_dtc_field_substitute_type s d0 T ≠ SmtType.None ∧
              __smtx_value_canonical
                (__smtx_value_dt_substitute s d0 (__smtx_type_default T))) :
    (c : SmtDatatypeCons) ->
      sizeOf c < limit ->
        __smtx_dt_cons_wf_rec c refs = true ->
          ¬ datatype_cons_has_typeRef_field c ->
            datatype_cons_default_args_typed s d0 c
  | SmtDatatypeCons.unit, _hSize, _hWF, _hNo => by
      simp [datatype_cons_default_args_typed]
  | SmtDatatypeCons.cons T c, hSize, hWF, hNo => by
      have hHeadSize : sizeOf T < limit := by
        simp at hSize ⊢
        omega
      have hTailSize : sizeOf c < limit := by
        simp at hSize ⊢
        omega
      have hNotTypeRef : ∀ r, T ≠ SmtType.TypeRef r := by
        intro r hEq
        apply hNo
        subst hEq
        simp [datatype_cons_has_typeRef_field]
      have hTailNo : ¬ datatype_cons_has_typeRef_field c := by
        intro hTail
        apply hNo
        cases T <;> simp [datatype_cons_has_typeRef_field, hTail]
      have hParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T refs = true ∧
            __smtx_dt_cons_wf_rec c refs = true := by
        cases T <;>
          simp_all [__smtx_dt_cons_wf_rec, datatype_cons_has_typeRef_field,
            native_ite]
      have hHead := hField T hHeadSize hNotTypeRef hParts.1 hParts.2.1
      have hTail :=
        datatype_cons_default_args_typed_of_no_typeRef_with_field_defaults_bounded
          s d0 refs limit hField c hTailSize hParts.2.2 hTailNo
      exact ⟨hHead.1, hHead.2.1, hHead.2.2, hTail⟩

private theorem datatype_cons_default_typed_canonical_of_args_typed
    (s : native_String)
    (d0 : SmtDatatype)
    (dTail : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      (v : SmtValue) ->
        datatype_cons_default_args_typed s d0 c ->
          __smtx_typeof_value v =
            __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
              (SmtDatatype.sum (__smtx_dtc_substitute s d0 c) dTail)
              native_nat_zero ->
            __smtx_value_canonical v ->
              __smtx_typeof_value
                    (__smtx_datatype_cons_default s d0 v c) =
                  SmtType.Datatype s d0 ∧
                __smtx_value_canonical
                  (__smtx_datatype_cons_default s d0 v c)
  | SmtDatatypeCons.unit, v, _hArgs, hTy, hCan => by
      simpa [__smtx_datatype_cons_default, __smtx_typeof_dt_cons_value_rec,
        __smtx_dtc_substitute] using
        And.intro hTy hCan
  | SmtDatatypeCons.cons T c, v, hArgs, hTy, hCan => by
      let arg := __smtx_value_dt_substitute s d0 (__smtx_type_default T)
      have hArgTy :
          __smtx_typeof_value arg = smtx_dtc_field_substitute_type s d0 T :=
        hArgs.1
      have hArgNotNone :
          smtx_dtc_field_substitute_type s d0 T ≠ SmtType.None :=
        hArgs.2.1
      have hArgCan : __smtx_value_canonical arg :=
        hArgs.2.2.1
      have hTailArgs : datatype_cons_default_args_typed s d0 c :=
        hArgs.2.2.2
      have hArgNV : arg ≠ SmtValue.NotValue := by
        intro hEq
        have hFieldNone :
            smtx_dtc_field_substitute_type s d0 T = SmtType.None := by
          rw [← hArgTy]
          simpa [hEq, __smtx_typeof_value]
        exact hArgNotNone hFieldNone
      have hArgVeq : native_veq arg SmtValue.NotValue = false :=
        native_veq_notValue_false_of_ne hArgNV
      have hHeadTy :
          __smtx_typeof_value v =
            SmtType.DtcAppType (smtx_dtc_field_substitute_type s d0 T)
              (__smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
                (SmtDatatype.sum (__smtx_dtc_substitute s d0 c) dTail)
                native_nat_zero) := by
        simpa [typeof_dt_cons_value_rec_dtc_substitute_cons_zero] using hTy
      have hApplyTy :
          __smtx_typeof_value (SmtValue.Apply v arg) =
            __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
              (SmtDatatype.sum (__smtx_dtc_substitute s d0 c) dTail)
              native_nat_zero :=
        typeof_apply_value_dtc_app hArgNotNone hHeadTy hArgTy
      have hApplyCan : __smtx_value_canonical (SmtValue.Apply v arg) :=
        value_canonical_apply hCan hArgCan
      simpa [__smtx_datatype_cons_default, arg, hArgVeq, native_ite] using
        datatype_cons_default_typed_canonical_of_args_typed s d0 dTail c
          (SmtValue.Apply v arg) hTailArgs hApplyTy hApplyCan

private theorem datatype_default_typed_canonical_of_first_args_typed
    (s : native_String)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (hArgs :
      datatype_cons_default_args_typed s (SmtDatatype.sum c dTail) c) :
    __smtx_typeof_value
          (__smtx_type_default (SmtType.Datatype s (SmtDatatype.sum c dTail))) =
        SmtType.Datatype s (SmtDatatype.sum c dTail) ∧
      __smtx_value_canonical
        (__smtx_type_default (SmtType.Datatype s (SmtDatatype.sum c dTail))) := by
  let d0 := SmtDatatype.sum c dTail
  let v0 := SmtValue.DtCons s d0 native_nat_zero
  have hvTy :
      __smtx_typeof_value v0 =
        __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
          (SmtDatatype.sum (__smtx_dtc_substitute s d0 c)
            (__smtx_dt_substitute s d0 dTail))
          native_nat_zero := by
    simp [v0, d0, __smtx_typeof_value, __smtx_dt_substitute]
  have hvCan : __smtx_value_canonical v0 := by
    simp [v0, __smtx_value_canonical, __smtx_value_canonical_bool]
  have hCons :=
    datatype_cons_default_typed_canonical_of_args_typed s d0
      (__smtx_dt_substitute s d0 dTail) c v0 hArgs hvTy hvCan
  have hConsNV :
      __smtx_datatype_cons_default s d0 v0 c ≠ SmtValue.NotValue := by
    intro hEq
    have hTyNone :
        __smtx_typeof_value (__smtx_datatype_cons_default s d0 v0 c) =
          SmtType.None := by
      simp [hEq, __smtx_typeof_value]
    have hBad : SmtType.Datatype s d0 = SmtType.None :=
      hCons.1.symm.trans hTyNone
    cases hBad
  have hConsVeq :
      native_veq (__smtx_datatype_cons_default s d0 v0 c) SmtValue.NotValue =
        false :=
    native_veq_notValue_false_of_ne hConsNV
  simpa [__smtx_type_default, __smtx_datatype_default, d0, v0, hConsVeq,
    native_not, native_ite] using hCons

private theorem datatype_default_typed_canonical_of_second_args_typed
    (s : native_String)
    (c0 c1 : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (hFirst :
      __smtx_datatype_cons_default s
          (SmtDatatype.sum c0 (SmtDatatype.sum c1 dTail))
          (SmtValue.DtCons s
            (SmtDatatype.sum c0 (SmtDatatype.sum c1 dTail))
            native_nat_zero)
          c0 =
        SmtValue.NotValue)
    (hArgs :
      datatype_cons_default_args_typed s
        (SmtDatatype.sum c0 (SmtDatatype.sum c1 dTail)) c1) :
    __smtx_typeof_value
          (__smtx_type_default
            (SmtType.Datatype s
              (SmtDatatype.sum c0 (SmtDatatype.sum c1 dTail)))) =
        SmtType.Datatype s
          (SmtDatatype.sum c0 (SmtDatatype.sum c1 dTail)) ∧
      __smtx_value_canonical
        (__smtx_type_default
          (SmtType.Datatype s
            (SmtDatatype.sum c0 (SmtDatatype.sum c1 dTail)))) := by
  let d0 := SmtDatatype.sum c0 (SmtDatatype.sum c1 dTail)
  let v1 := SmtValue.DtCons s d0 (native_nat_succ native_nat_zero)
  have hvTy :
      __smtx_typeof_value v1 =
        __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
          (SmtDatatype.sum (__smtx_dtc_substitute s d0 c1)
            (__smtx_dt_substitute s d0 dTail))
          native_nat_zero := by
    simp [v1, d0, __smtx_typeof_value, __smtx_dt_substitute,
      __smtx_typeof_dt_cons_value_rec]
  have hvCan : __smtx_value_canonical v1 := by
    simp [v1, __smtx_value_canonical, __smtx_value_canonical_bool]
  have hCons :=
    datatype_cons_default_typed_canonical_of_args_typed s d0
      (__smtx_dt_substitute s d0 dTail) c1 v1 hArgs hvTy hvCan
  have hConsNV :
      __smtx_datatype_cons_default s d0 v1 c1 ≠ SmtValue.NotValue := by
    intro hEq
    have hTyNone :
        __smtx_typeof_value (__smtx_datatype_cons_default s d0 v1 c1) =
          SmtType.None := by
      simp [hEq, __smtx_typeof_value]
    have hBad : SmtType.Datatype s d0 = SmtType.None :=
      hCons.1.symm.trans hTyNone
    cases hBad
  have hFirstVeq :
      native_veq
          (__smtx_datatype_cons_default s d0
            (SmtValue.DtCons s d0 native_nat_zero) c0)
          SmtValue.NotValue =
        true := by
    simp [d0, hFirst, native_veq]
  have hConsVeq :
      native_veq (__smtx_datatype_cons_default s d0 v1 c1) SmtValue.NotValue =
        false :=
    native_veq_notValue_false_of_ne hConsNV
  simpa [__smtx_type_default, __smtx_datatype_default, d0, v1, hFirstVeq,
    hConsVeq, native_not, native_ite] using hCons

private theorem datatype_cons_default_eq_notValue_of_has_typeRef_field
    (s : native_String)
    (d0 : SmtDatatype)
    (v : SmtValue) :
    (c : SmtDatatypeCons) ->
      datatype_cons_has_typeRef_field c ->
        __smtx_datatype_cons_default s d0 v c = SmtValue.NotValue
  | SmtDatatypeCons.unit, hHas => by
      simp [datatype_cons_has_typeRef_field] at hHas
  | SmtDatatypeCons.cons T c, hHas => by
      by_cases hTypeRef : ∃ r, T = SmtType.TypeRef r
      · rcases hTypeRef with ⟨r, rfl⟩
        simp [datatype_cons_has_typeRef_field, __smtx_datatype_cons_default,
          __smtx_type_default, __smtx_value_dt_substitute, native_veq,
          native_ite]
      · have hTail : datatype_cons_has_typeRef_field c := by
          cases T <;> simp_all [datatype_cons_has_typeRef_field]
        cases hArg :
            native_veq
              (__smtx_value_dt_substitute s d0 (__smtx_type_default T))
              SmtValue.NotValue
        · simp [__smtx_datatype_cons_default, hArg, native_ite]
          exact datatype_cons_default_eq_notValue_of_has_typeRef_field s d0
            (SmtValue.Apply v
              (__smtx_value_dt_substitute s d0 (__smtx_type_default T)))
            c hTail
        · simp [__smtx_datatype_cons_default, hArg, native_ite]

private def datatype_suffix_at : SmtDatatype -> native_Nat -> SmtDatatype -> Prop
  | d0, native_nat_zero, d => d = d0
  | SmtDatatype.sum _ dTail, native_nat_succ n, d =>
      datatype_suffix_at dTail n d
  | SmtDatatype.null, native_nat_succ _, _ => False

private theorem datatype_suffix_at_self
    (d : SmtDatatype) :
    datatype_suffix_at d native_nat_zero d := by
  simp [datatype_suffix_at]

private theorem datatype_suffix_at_tail
    (d0 : SmtDatatype) :
    (n : native_Nat) ->
      (c : SmtDatatypeCons) ->
        (dTail : SmtDatatype) ->
          datatype_suffix_at d0 n (SmtDatatype.sum c dTail) ->
            datatype_suffix_at d0 (native_nat_succ n) dTail
  | native_nat_zero, c, dTail, h => by
      simp [datatype_suffix_at] at h
      subst h
      simp [datatype_suffix_at]
  | native_nat_succ n, c, dTail, h => by
      cases d0 with
      | null =>
          simp [datatype_suffix_at] at h
      | sum c0 d0Tail =>
          simpa [datatype_suffix_at] using
            datatype_suffix_at_tail d0Tail n c dTail h

private theorem datatype_suffix_at_size_le
    (d0 : SmtDatatype) :
    (n : native_Nat) ->
      (d : SmtDatatype) ->
        datatype_suffix_at d0 n d ->
          sizeOf d ≤ sizeOf d0
  | native_nat_zero, d, h => by
      simp [datatype_suffix_at] at h
      subst h
      simp
  | native_nat_succ n, d, h => by
      cases d0 with
      | null =>
          simp [datatype_suffix_at] at h
      | sum c dTail =>
          have hTail :
              datatype_suffix_at dTail n d := by
            simpa [datatype_suffix_at] using h
          have ih := datatype_suffix_at_size_le dTail n d hTail
          simp at ih ⊢
          omega

private theorem datatype_cons_size_lt_of_suffix
    (d0 : SmtDatatype)
    (n : native_Nat)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (hSuffix : datatype_suffix_at d0 n (SmtDatatype.sum c dTail)) :
    sizeOf c < sizeOf d0 := by
  have hLe :=
    datatype_suffix_at_size_le d0 n (SmtDatatype.sum c dTail) hSuffix
  simp at hLe ⊢
  omega

private theorem datatype_payload_size_lt_of_type_size_lt
    {s : native_String}
    {d d0 : SmtDatatype}
    (h : sizeOf (SmtType.Datatype s d) < sizeOf d0) :
    sizeOf d < sizeOf d0 := by
  simp at h ⊢
  omega

private theorem datatype_suffix_at_unique
    (d0 : SmtDatatype) :
    (n : native_Nat) ->
      (d1 d2 : SmtDatatype) ->
        datatype_suffix_at d0 n d1 ->
          datatype_suffix_at d0 n d2 ->
            d1 = d2
  | native_nat_zero, d1, d2, h1, h2 => by
      simp [datatype_suffix_at] at h1 h2
      subst h1
      subst h2
      rfl
  | native_nat_succ n, d1, d2, h1, h2 => by
      cases d0 with
      | null =>
          simp [datatype_suffix_at] at h1
      | sum c dTail =>
          exact datatype_suffix_at_unique dTail n d1 d2
            (by simpa [datatype_suffix_at] using h1)
            (by simpa [datatype_suffix_at] using h2)

private theorem datatype_suffix_at_null_no_succ
    (d0 : SmtDatatype) :
    (n : native_Nat) ->
      datatype_suffix_at d0 n SmtDatatype.null ->
        (k : native_Nat) ->
          (d : SmtDatatype) ->
            ¬ datatype_suffix_at d0 (n + native_nat_succ k) d
  | native_nat_zero, hNull, k, d, hSuffix => by
      simp [datatype_suffix_at] at hNull
      subst hNull
      cases k <;> simp [datatype_suffix_at] at hSuffix
  | native_nat_succ n, hNull, k, d, hSuffix => by
      cases d0 with
      | null =>
          simp [datatype_suffix_at] at hNull
      | sum c dTail =>
          have hNullTail :
              datatype_suffix_at dTail n SmtDatatype.null := by
            simpa [datatype_suffix_at] using hNull
          have hSuffixTail :
              datatype_suffix_at dTail (n + native_nat_succ k) d := by
            simpa [datatype_suffix_at, Nat.succ_add] using hSuffix
          exact datatype_suffix_at_null_no_succ dTail n hNullTail k d
            hSuffixTail

private theorem typeof_dt_cons_value_rec_substitute_of_suffix_at
    (s : native_String)
    (d0 : SmtDatatype)
    (T : SmtType) :
    (dBase : SmtDatatype) ->
      (n : native_Nat) ->
        (d : SmtDatatype) ->
          datatype_suffix_at dBase n d ->
            __smtx_typeof_dt_cons_value_rec T
                (__smtx_dt_substitute s d0 dBase) n =
              __smtx_typeof_dt_cons_value_rec T
                (__smtx_dt_substitute s d0 d) native_nat_zero
  | SmtDatatype.null, native_nat_zero, d, h => by
      simp [datatype_suffix_at] at h
      subst h
      simp [__smtx_dt_substitute, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.null, native_nat_succ n, d, h => by
      simp [datatype_suffix_at] at h
  | SmtDatatype.sum c dTail, native_nat_zero, d, h => by
      simp [datatype_suffix_at] at h
      subst h
      simp
  | SmtDatatype.sum c dTail, native_nat_succ n, d, h => by
      simpa [datatype_suffix_at, __smtx_dt_substitute,
        __smtx_typeof_dt_cons_value_rec] using
        typeof_dt_cons_value_rec_substitute_of_suffix_at s d0 T dTail n d h

private theorem ret_typeof_sel_rec_substitute_of_suffix_at
    (s : native_String)
    (d0 : SmtDatatype) :
    (dBase : SmtDatatype) ->
      (n : native_Nat) ->
        (d : SmtDatatype) ->
          (j : native_Nat) ->
            datatype_suffix_at dBase n d ->
              __smtx_ret_typeof_sel_rec
                  (__smtx_dt_substitute s d0 dBase) n j =
                __smtx_ret_typeof_sel_rec
                  (__smtx_dt_substitute s d0 d) native_nat_zero j
  | SmtDatatype.null, native_nat_zero, d, j, h => by
      simp [datatype_suffix_at] at h
      subst h
      simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec]
  | SmtDatatype.null, native_nat_succ n, d, j, h => by
      simp [datatype_suffix_at] at h
  | SmtDatatype.sum c dTail, native_nat_zero, d, j, h => by
      simp [datatype_suffix_at] at h
      subst h
      simp
  | SmtDatatype.sum c dTail, native_nat_succ n, d, j, h => by
      simpa [datatype_suffix_at, __smtx_dt_substitute,
        __smtx_ret_typeof_sel_rec] using
        ret_typeof_sel_rec_substitute_of_suffix_at s d0 dTail n d j h

private theorem dt_num_sels_substitute_of_suffix_at
    (s : native_String)
    (d0 : SmtDatatype) :
    (dBase : SmtDatatype) ->
      (n : native_Nat) ->
        (d : SmtDatatype) ->
          datatype_suffix_at dBase n d ->
            __smtx_dt_num_sels (__smtx_dt_substitute s d0 dBase) n =
              __smtx_dt_num_sels (__smtx_dt_substitute s d0 d) native_nat_zero
  | SmtDatatype.null, native_nat_zero, d, h => by
      simp [datatype_suffix_at] at h
      subst h
      simp [__smtx_dt_substitute, __smtx_dt_num_sels]
  | SmtDatatype.null, native_nat_succ n, d, h => by
      simp [datatype_suffix_at] at h
  | SmtDatatype.sum c dTail, native_nat_zero, d, h => by
      simp [datatype_suffix_at] at h
      subst h
      simp
  | SmtDatatype.sum c dTail, native_nat_succ n, d, h => by
      simpa [datatype_suffix_at, __smtx_dt_substitute,
        __smtx_dt_num_sels] using
        dt_num_sels_substitute_of_suffix_at s d0 dTail n d h

private theorem typeof_dt_cons_value_of_suffix_at
    (s : native_String)
    (d0 d : SmtDatatype)
    (n : native_Nat)
    (hSuffix : datatype_suffix_at d0 n d) :
    __smtx_typeof_value (SmtValue.DtCons s d0 n) =
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
        (__smtx_dt_substitute s d0 d) native_nat_zero := by
  simpa [__smtx_typeof_value] using
    typeof_dt_cons_value_rec_substitute_of_suffix_at s d0
      (SmtType.Datatype s d0) d0 n d hSuffix

private theorem dt_applied_type_rec_non_none_base
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i n,
      dt_applied_type_rec s d0 d i n ≠ SmtType.None ->
        __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i ≠
          SmtType.None
  | d, i, 0, h => by
      simpa [dt_applied_type_rec] using h
  | SmtDatatype.null, i, Nat.succ n, h => by
      cases i <;> simp [dt_applied_type_rec] at h
  | SmtDatatype.sum SmtDatatypeCons.unit d, 0, Nat.succ n, h => by
      simp [dt_applied_type_rec] at h
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, 0, Nat.succ n, _h => by
      simp [__smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum c d, Nat.succ i, n, h => by
      cases n with
      | zero =>
          simpa [dt_applied_type_rec] using h
      | succ n =>
          have hTail :
              __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0) d i ≠
                SmtType.None :=
            dt_applied_type_rec_non_none_base s d0 d i (Nat.succ n) (by
              simpa [dt_applied_type_rec] using h)
          simpa [__smtx_typeof_dt_cons_value_rec] using hTail

private theorem dt_applied_type_rec_full_zero
    (s : native_String)
    (d0 : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      (dTail : SmtDatatype) ->
        dt_applied_type_rec s d0 (SmtDatatype.sum c dTail) native_nat_zero
            (__smtx_dtc_num_sels c) =
          SmtType.Datatype s d0
  | SmtDatatypeCons.unit, dTail => by
      simp [dt_applied_type_rec, __smtx_dtc_num_sels,
        __smtx_typeof_dt_cons_value_rec]
  | SmtDatatypeCons.cons T c, dTail => by
      simpa [dt_applied_type_rec, __smtx_dtc_num_sels] using
        dt_applied_type_rec_full_zero s d0 c dTail

private theorem dt_applied_type_rec_full_of_cons_suffix
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      (i : native_Nat) ->
        (c : SmtDatatypeCons) ->
          (dTail : SmtDatatype) ->
            datatype_suffix_at d i (SmtDatatype.sum c dTail) ->
              dt_applied_type_rec s d0 d i (__smtx_dt_num_sels d i) =
                SmtType.Datatype s d0
  | SmtDatatype.null, native_nat_zero, c, dTail, hSuffix => by
      simp [datatype_suffix_at] at hSuffix
  | SmtDatatype.null, native_nat_succ i, c, dTail, hSuffix => by
      simp [datatype_suffix_at] at hSuffix
  | SmtDatatype.sum c0 d0Tail, native_nat_zero, c, dTail, hSuffix => by
      simp [datatype_suffix_at] at hSuffix
      rcases hSuffix with ⟨rfl, rfl⟩
      simpa [__smtx_dt_num_sels] using
        dt_applied_type_rec_full_zero s d0 c dTail
  | SmtDatatype.sum c0 d0Tail, native_nat_succ i, c, dTail, hSuffix => by
      have hTailSuffix :
          datatype_suffix_at d0Tail i (SmtDatatype.sum c dTail) := by
        simpa [datatype_suffix_at] using hSuffix
      have hNum :
          __smtx_dt_num_sels (SmtDatatype.sum c0 d0Tail) (Nat.succ i) =
            __smtx_dt_num_sels d0Tail i := by
        simp [__smtx_dt_num_sels]
      rw [hNum]
      have hReduce :
          dt_applied_type_rec s d0 (SmtDatatype.sum c0 d0Tail) (Nat.succ i)
              (__smtx_dt_num_sels d0Tail i) =
            dt_applied_type_rec s d0 d0Tail i (__smtx_dt_num_sels d0Tail i) := by
        exact dt_applied_type_rec_succ_index s d0 c0 d0Tail i
          (__smtx_dt_num_sels d0Tail i)
      rw [hReduce]
      exact
        dt_applied_type_rec_full_of_cons_suffix s d0 d0Tail i c dTail
          hTailSuffix

private theorem dt_applied_type_rec_substitute_ne_none
    (sub : native_String)
    (base : SmtDatatype)
    (s : native_String)
    (dBase dBase' : SmtDatatype) :
    (d : SmtDatatype) ->
      (i n : native_Nat) ->
        dt_applied_type_rec s dBase d i n ≠ SmtType.None ->
          dt_applied_type_rec s dBase'
              (__smtx_dt_substitute sub base d) i n ≠
            SmtType.None
  | SmtDatatype.null, i, n, hNN => by
      exfalso
      apply hNN
      cases i <;> cases n <;>
        simp [dt_applied_type_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, native_nat_zero,
      _hNN => by
      simp [dt_applied_type_rec, __smtx_dt_substitute,
        __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, native_nat_succ n,
      hNN => by
      simp [dt_applied_type_rec] at hNN
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero,
      native_nat_zero, _hNN => by
      cases U <;>
        simp [dt_applied_type_rec, __smtx_dt_substitute,
          __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero,
      native_nat_succ n, hNN => by
      have hTailNN :
          dt_applied_type_rec s dBase (SmtDatatype.sum c d)
              native_nat_zero n ≠
            SmtType.None := by
        simpa [dt_applied_type_rec] using hNN
      have hRec :=
        dt_applied_type_rec_substitute_ne_none
          sub base s dBase dBase' (SmtDatatype.sum c d)
          native_nat_zero n hTailNN
      cases U <;>
        simpa [dt_applied_type_rec, __smtx_dt_substitute,
          __smtx_dtc_substitute] using hRec
  | SmtDatatype.sum c SmtDatatype.null, native_nat_succ i, n, hNN => by
      exfalso
      apply hNN
      cases n <;>
        simp [dt_applied_type_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum c (SmtDatatype.sum cTail dTail), native_nat_succ i, n,
      hNN => by
      have hTailNN :
          dt_applied_type_rec s dBase
              (SmtDatatype.sum cTail dTail) i n ≠
            SmtType.None := by
        cases n <;>
          simpa [dt_applied_type_rec, __smtx_typeof_dt_cons_value_rec] using
            hNN
      have hRec :=
        dt_applied_type_rec_substitute_ne_none
          sub base s dBase dBase' (SmtDatatype.sum cTail dTail) i n hTailNN
      cases n <;>
        simpa [dt_applied_type_rec, __smtx_dt_substitute,
          __smtx_typeof_dt_cons_value_rec] using hRec

private theorem dt_applied_type_rec_substitute_reflect_ne_none
    (sub : native_String)
    (base : SmtDatatype)
    (s : native_String)
    (dBase dBase' : SmtDatatype) :
    (d : SmtDatatype) ->
      (i n : native_Nat) ->
        dt_applied_type_rec s dBase'
            (__smtx_dt_substitute sub base d) i n ≠
          SmtType.None ->
            dt_applied_type_rec s dBase d i n ≠ SmtType.None
  | SmtDatatype.null, i, n, hNN => by
      exfalso
      apply hNN
      cases i <;> cases n <;>
        simp [dt_applied_type_rec, __smtx_dt_substitute,
          __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, native_nat_zero,
      _hNN => by
      simp [dt_applied_type_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum SmtDatatypeCons.unit d, native_nat_zero, native_nat_succ n,
      hNN => by
      exfalso
      apply hNN
      simp [dt_applied_type_rec, __smtx_dt_substitute,
        __smtx_dtc_substitute]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero,
      native_nat_zero, _hNN => by
      simp [dt_applied_type_rec, __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum (SmtDatatypeCons.cons U c) d, native_nat_zero,
      native_nat_succ n, hNN => by
      have hTailNN :
          dt_applied_type_rec s dBase'
              (__smtx_dt_substitute sub base (SmtDatatype.sum c d))
              native_nat_zero n ≠
            SmtType.None := by
        cases U <;>
          simpa [dt_applied_type_rec, __smtx_dt_substitute,
            __smtx_dtc_substitute] using hNN
      have hRec :=
        dt_applied_type_rec_substitute_reflect_ne_none
          sub base s dBase dBase' (SmtDatatype.sum c d)
          native_nat_zero n hTailNN
      simpa [dt_applied_type_rec] using hRec
  | SmtDatatype.sum c SmtDatatype.null, native_nat_succ i, n, hNN => by
      exfalso
      apply hNN
      cases n <;>
        simp [dt_applied_type_rec, __smtx_dt_substitute,
          __smtx_typeof_dt_cons_value_rec]
  | SmtDatatype.sum c (SmtDatatype.sum cTail dTail), native_nat_succ i, n,
      hNN => by
      have hTailNN :
          dt_applied_type_rec s dBase'
              (__smtx_dt_substitute sub base (SmtDatatype.sum cTail dTail))
              i n ≠
            SmtType.None := by
        cases n <;>
          simpa [dt_applied_type_rec, __smtx_dt_substitute,
            __smtx_typeof_dt_cons_value_rec] using hNN
      have hRec :=
        dt_applied_type_rec_substitute_reflect_ne_none
          sub base s dBase dBase' (SmtDatatype.sum cTail dTail) i n hTailNN
      cases n <;>
        simpa [dt_applied_type_rec, __smtx_typeof_dt_cons_value_rec] using hRec

private theorem dt_applied_type_rec_self_substitute_replace_ne_none
    (sub : native_String)
    (base : SmtDatatype)
    (root : native_String)
    (oldRoot newRoot : SmtDatatype)
    (hNewRoot : newRoot = __smtx_dt_substitute sub base oldRoot)
    (i n : native_Nat)
    (hNN :
      dt_applied_type_rec root oldRoot
          (__smtx_dt_substitute root oldRoot oldRoot) i n ≠
        SmtType.None) :
    dt_applied_type_rec root newRoot
        (__smtx_dt_substitute root newRoot newRoot) i n ≠
      SmtType.None := by
  have hOldRoot :
      dt_applied_type_rec root oldRoot oldRoot i n ≠ SmtType.None :=
    dt_applied_type_rec_substitute_reflect_ne_none
      root oldRoot root oldRoot oldRoot oldRoot i n hNN
  have hNewRootBody :
      dt_applied_type_rec root newRoot
          (__smtx_dt_substitute sub base oldRoot) i n ≠
        SmtType.None :=
    dt_applied_type_rec_substitute_ne_none
      sub base root oldRoot newRoot oldRoot i n hOldRoot
  have hNewRootBody' :
      dt_applied_type_rec root newRoot newRoot i n ≠ SmtType.None := by
    simpa [hNewRoot] using hNewRootBody
  exact
    dt_applied_type_rec_substitute_ne_none
      root newRoot root newRoot newRoot newRoot i n hNewRootBody'

private theorem datatype_suffix_at_of_typeof_dt_cons_value_rec_non_none
    (T : SmtType) :
    ∀ d i,
      __smtx_typeof_dt_cons_value_rec T d i ≠ SmtType.None ->
        ∃ dSuffix, datatype_suffix_at d i dSuffix
  | SmtDatatype.null, i, h => by
      cases i <;> simp [__smtx_typeof_dt_cons_value_rec] at h
  | SmtDatatype.sum c dTail, native_nat_zero, _h => by
      exact ⟨SmtDatatype.sum c dTail,
        datatype_suffix_at_self (SmtDatatype.sum c dTail)⟩
  | SmtDatatype.sum c dTail, native_nat_succ i, h => by
      have hTail :
          __smtx_typeof_dt_cons_value_rec T dTail i ≠ SmtType.None := by
        simpa [__smtx_typeof_dt_cons_value_rec] using h
      rcases datatype_suffix_at_of_typeof_dt_cons_value_rec_non_none T
          dTail i hTail with
        ⟨dSuffix, hSuffix⟩
      exact ⟨dSuffix, by simpa [datatype_suffix_at] using hSuffix⟩

private theorem datatype_cons_suffix_at_of_typeof_dt_cons_value_rec_non_none
    (T : SmtType) :
    ∀ d i,
      __smtx_typeof_dt_cons_value_rec T d i ≠ SmtType.None ->
        ∃ c dTail, datatype_suffix_at d i (SmtDatatype.sum c dTail)
  | SmtDatatype.null, i, h => by
      cases i <;> simp [__smtx_typeof_dt_cons_value_rec] at h
  | SmtDatatype.sum c dTail, native_nat_zero, _h => by
      exact ⟨c, dTail, datatype_suffix_at_self (SmtDatatype.sum c dTail)⟩
  | SmtDatatype.sum c dTail, native_nat_succ i, h => by
      have hTail :
          __smtx_typeof_dt_cons_value_rec T dTail i ≠ SmtType.None := by
        simpa [__smtx_typeof_dt_cons_value_rec] using h
      rcases datatype_cons_suffix_at_of_typeof_dt_cons_value_rec_non_none T
          dTail i hTail with
        ⟨cSuffix, dSuffixTail, hSuffix⟩
      exact ⟨cSuffix, dSuffixTail,
        by simpa [datatype_suffix_at] using hSuffix⟩

private theorem datatype_suffix_at_of_substitute
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i dSubSuffix,
      datatype_suffix_at (__smtx_dt_substitute s d0 d) i dSubSuffix ->
        ∃ dSuffix, datatype_suffix_at d i dSuffix
  | d, native_nat_zero, _dSubSuffix, _hSuffix => by
      exact ⟨d, datatype_suffix_at_self d⟩
  | SmtDatatype.null, native_nat_succ i, dSubSuffix, hSuffix => by
      simp [__smtx_dt_substitute, datatype_suffix_at] at hSuffix
  | SmtDatatype.sum c dTail, native_nat_succ i, dSubSuffix, hSuffix => by
      rcases datatype_suffix_at_of_substitute s d0 dTail i dSubSuffix
          (by simpa [__smtx_dt_substitute, datatype_suffix_at] using hSuffix) with
        ⟨dSuffix, hSuffixTail⟩
      exact ⟨dSuffix, by simpa [datatype_suffix_at] using hSuffixTail⟩

private theorem datatype_suffix_at_substitute
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      (i : native_Nat) ->
        (dSuffix : SmtDatatype) ->
          datatype_suffix_at d i dSuffix ->
            datatype_suffix_at (__smtx_dt_substitute s d0 d) i
              (__smtx_dt_substitute s d0 dSuffix)
  | d, native_nat_zero, dSuffix, hSuffix => by
      simp [datatype_suffix_at] at hSuffix
      subst hSuffix
      simp [datatype_suffix_at]
  | SmtDatatype.null, native_nat_succ i, dSuffix, hSuffix => by
      simp [datatype_suffix_at] at hSuffix
  | SmtDatatype.sum c dTail, native_nat_succ i, dSuffix, hSuffix => by
      have hTail :
          datatype_suffix_at dTail i dSuffix := by
        simpa [datatype_suffix_at] using hSuffix
      simpa [__smtx_dt_substitute, datatype_suffix_at] using
        datatype_suffix_at_substitute s d0 dTail i dSuffix hTail

private theorem datatype_cons_suffix_at_of_substitute
    (s : native_String)
    (d0 : SmtDatatype) :
    ∀ d i cSub dSubTail,
      datatype_suffix_at (__smtx_dt_substitute s d0 d) i
          (SmtDatatype.sum cSub dSubTail) ->
        ∃ c dTail, datatype_suffix_at d i (SmtDatatype.sum c dTail)
  | d, native_nat_zero, cSub, dSubTail, _hSuffix => by
      cases d with
      | null =>
          simp [__smtx_dt_substitute, datatype_suffix_at] at _hSuffix
      | sum c dTail =>
          exact ⟨c, dTail, datatype_suffix_at_self (SmtDatatype.sum c dTail)⟩
  | SmtDatatype.null, native_nat_succ i, cSub, dSubTail, hSuffix => by
      simp [__smtx_dt_substitute, datatype_suffix_at] at hSuffix
  | SmtDatatype.sum c dTail, native_nat_succ i, cSub, dSubTail, hSuffix => by
      rcases datatype_cons_suffix_at_of_substitute s d0 dTail i cSub dSubTail
          (by simpa [__smtx_dt_substitute, datatype_suffix_at] using hSuffix) with
        ⟨cSuffix, dSuffixTail, hSuffixTail⟩
      exact ⟨cSuffix, dSuffixTail,
        by simpa [datatype_suffix_at] using hSuffixTail⟩

private theorem datatype_suffix_at_of_datatype_value_head
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {v : SmtValue}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    ∃ dSuffix, datatype_suffix_at d i dSuffix := by
  have hChain := dt_chain_type_of_non_none hHead (by simp [hTy])
  have hFinalNN :
      dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (value_num_apply_args v) ≠ SmtType.None := by
    rw [← hChain]
    simp [hTy]
  have hRawNN :
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d)
          (__smtx_dt_substitute s d d) i ≠ SmtType.None :=
    dt_applied_type_rec_non_none_base s d (__smtx_dt_substitute s d d) i
      (value_num_apply_args v) hFinalNN
  rcases datatype_suffix_at_of_typeof_dt_cons_value_rec_non_none
      (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i hRawNN with
    ⟨dSubSuffix, hSubSuffix⟩
  exact datatype_suffix_at_of_substitute s d d i dSubSuffix hSubSuffix

private theorem datatype_cons_suffix_at_of_datatype_value_head
    {s : native_String}
    {d : SmtDatatype}
    {i : native_Nat}
    {v : SmtValue}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    ∃ c dTail, datatype_suffix_at d i (SmtDatatype.sum c dTail) := by
  have hChain := dt_chain_type_of_non_none hHead (by simp [hTy])
  have hFinalNN :
      dt_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (value_num_apply_args v) ≠ SmtType.None := by
    rw [← hChain]
    simp [hTy]
  have hRawNN :
      __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d)
          (__smtx_dt_substitute s d d) i ≠ SmtType.None :=
    dt_applied_type_rec_non_none_base s d (__smtx_dt_substitute s d d) i
      (value_num_apply_args v) hFinalNN
  rcases datatype_cons_suffix_at_of_typeof_dt_cons_value_rec_non_none
      (SmtType.Datatype s d) (__smtx_dt_substitute s d d) i hRawNN with
    ⟨cSub, dSubTail, hSubSuffix⟩
  exact datatype_cons_suffix_at_of_substitute s d d i cSub dSubTail
    hSubSuffix

private theorem value_dt_substitute_datatype_type_of_non_none
    (sub : native_String)
    (base : SmtDatatype)
    {v : SmtValue}
    {s : native_String}
    {d : SmtDatatype}
    (hv : __smtx_typeof_value v = SmtType.Datatype s d)
    (hNe : native_streq sub s = false)
    (hNN :
      __smtx_typeof_value (__smtx_value_dt_substitute sub base v) ≠
        SmtType.None) :
    __smtx_typeof_value (__smtx_value_dt_substitute sub base v) =
      SmtType.Datatype s (__smtx_dt_substitute sub base d) := by
  rcases value_head_dtCons_of_datatype_type hv with ⟨i, hHead⟩
  have hHeadSub :=
    value_dt_substitute_apply_head_of_dtCons sub base v hHead
  have hHeadSub' :
      __vsm_apply_head (__smtx_value_dt_substitute sub base v) =
        SmtValue.DtCons s (__smtx_dt_substitute sub base d) i := by
    simpa [hNe, native_ite] using hHeadSub
  have hArgsSub := value_num_apply_args_dt_substitute sub base v
  have hArgsOrig :
      value_num_apply_args v =
        __smtx_dt_num_sels (__smtx_dt_substitute s d d) i :=
    value_num_apply_args_eq_dt_num_sels_of_datatype hHead hv
  have hCount :
      value_num_apply_args (__smtx_value_dt_substitute sub base v) =
        __smtx_dt_num_sels
          (__smtx_dt_substitute s
            (__smtx_dt_substitute sub base d)
            (__smtx_dt_substitute sub base d)) i := by
    calc
      value_num_apply_args (__smtx_value_dt_substitute sub base v) =
          value_num_apply_args v := hArgsSub
      _ = __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := hArgsOrig
      _ = __smtx_dt_num_sels d i := dt_num_sels_substitute s d d i
      _ = __smtx_dt_num_sels (__smtx_dt_substitute sub base d) i := by
          exact (dt_num_sels_substitute sub base d i).symm
      _ =
          __smtx_dt_num_sels
            (__smtx_dt_substitute s
              (__smtx_dt_substitute sub base d)
              (__smtx_dt_substitute sub base d)) i := by
          exact (dt_num_sels_substitute s
            (__smtx_dt_substitute sub base d)
            (__smtx_dt_substitute sub base d) i).symm
  rcases datatype_cons_suffix_at_of_datatype_value_head hHead hv with
    ⟨c, dTail, hSuffix⟩
  have hSubSuffix :
      datatype_suffix_at (__smtx_dt_substitute sub base d) i
        (__smtx_dt_substitute sub base (SmtDatatype.sum c dTail)) :=
    datatype_suffix_at_substitute sub base d i (SmtDatatype.sum c dTail)
      hSuffix
  have hSelfSuffix :
      datatype_suffix_at
        (__smtx_dt_substitute s
          (__smtx_dt_substitute sub base d)
          (__smtx_dt_substitute sub base d)) i
        (__smtx_dt_substitute s
          (__smtx_dt_substitute sub base d)
          (__smtx_dt_substitute sub base (SmtDatatype.sum c dTail))) :=
    datatype_suffix_at_substitute s (__smtx_dt_substitute sub base d)
      (__smtx_dt_substitute sub base d) i
      (__smtx_dt_substitute sub base (SmtDatatype.sum c dTail))
      hSubSuffix
  have hFull :
      dt_applied_type_rec s (__smtx_dt_substitute sub base d)
          (__smtx_dt_substitute s
            (__smtx_dt_substitute sub base d)
            (__smtx_dt_substitute sub base d)) i
          (__smtx_dt_num_sels
            (__smtx_dt_substitute s
              (__smtx_dt_substitute sub base d)
              (__smtx_dt_substitute sub base d)) i) =
        SmtType.Datatype s (__smtx_dt_substitute sub base d) := by
    cases hSub :
        __smtx_dt_substitute s
          (__smtx_dt_substitute sub base d)
          (__smtx_dt_substitute sub base (SmtDatatype.sum c dTail)) with
    | null =>
        simp [__smtx_dt_substitute] at hSub
    | sum cSub dSubTail =>
        exact
          dt_applied_type_rec_full_of_cons_suffix s
            (__smtx_dt_substitute sub base d)
            (__smtx_dt_substitute s
              (__smtx_dt_substitute sub base d)
              (__smtx_dt_substitute sub base d))
            i cSub dSubTail
            (by simpa [hSub] using hSelfSuffix)
  have hChain := dt_chain_type_of_non_none hHeadSub' hNN
  calc
    __smtx_typeof_value (__smtx_value_dt_substitute sub base v) =
        dt_applied_type_rec s (__smtx_dt_substitute sub base d)
          (__smtx_dt_substitute s
            (__smtx_dt_substitute sub base d)
            (__smtx_dt_substitute sub base d)) i
          (value_num_apply_args (__smtx_value_dt_substitute sub base v)) :=
      hChain
    _ =
        dt_applied_type_rec s (__smtx_dt_substitute sub base d)
          (__smtx_dt_substitute s
            (__smtx_dt_substitute sub base d)
            (__smtx_dt_substitute sub base d)) i
          (__smtx_dt_num_sels
            (__smtx_dt_substitute s
              (__smtx_dt_substitute sub base d)
              (__smtx_dt_substitute sub base d)) i) := by
      rw [hCount]
    _ = SmtType.Datatype s (__smtx_dt_substitute sub base d) := hFull

private def datatype_default_has_typed_constructor_from
    (s : native_String)
    (d0 : SmtDatatype) :
    SmtDatatype -> Prop
  | SmtDatatype.null => False
  | SmtDatatype.sum c d =>
      datatype_cons_default_args_typed s d0 c ∨
        datatype_cons_has_typeRef_field c ∧
          datatype_default_has_typed_constructor_from s d0 d

private theorem datatype_default_tail_of_typed_constructor_from_of_has_typeRef
    (s : native_String)
    (d0 : SmtDatatype)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (hHas : datatype_cons_has_typeRef_field c)
    (hTyped :
      datatype_default_has_typed_constructor_from s d0
        (SmtDatatype.sum c dTail)) :
    datatype_default_has_typed_constructor_from s d0 dTail := by
  simp [datatype_default_has_typed_constructor_from] at hTyped
  cases hTyped with
  | inl hArgs =>
      exact False.elim
        (datatype_cons_default_args_typed_false_of_has_typeRef_field s
          d0 c hHas hArgs)
  | inr hTail =>
      exact hTail.2

private theorem datatype_default_has_typed_constructor_from_typeRef_iff
    (s : native_String)
    (d0 : SmtDatatype)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (hHas : datatype_cons_has_typeRef_field c) :
    datatype_default_has_typed_constructor_from s d0 (SmtDatatype.sum c dTail) ↔
      datatype_default_has_typed_constructor_from s d0 dTail := by
  constructor
  · exact datatype_default_tail_of_typed_constructor_from_of_has_typeRef s d0
      c dTail hHas
  · intro hTail
    exact Or.inr ⟨hHas, hTail⟩

private theorem datatype_default_tail_of_typed_constructor_from_self_of_has_typeRef
    (s : native_String)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (hHas : datatype_cons_has_typeRef_field c)
    (hTyped :
      datatype_default_has_typed_constructor_from s (SmtDatatype.sum c dTail)
        (SmtDatatype.sum c dTail)) :
    datatype_default_has_typed_constructor_from s (SmtDatatype.sum c dTail)
      dTail :=
  datatype_default_tail_of_typed_constructor_from_of_has_typeRef s
    (SmtDatatype.sum c dTail) c dTail hHas hTyped

private def datatype_typeRef_prefix_at : SmtDatatype -> native_Nat -> Prop
  | _d, native_nat_zero => True
  | SmtDatatype.sum c dTail, native_nat_succ n =>
      datatype_cons_has_typeRef_field c ∧
        datatype_typeRef_prefix_at dTail n
  | SmtDatatype.null, native_nat_succ _ => False

private theorem datatype_typeRef_prefix_at_succ_of_suffix
    (d0 : SmtDatatype) :
    (n : native_Nat) ->
      (c : SmtDatatypeCons) ->
        (dTail : SmtDatatype) ->
          datatype_typeRef_prefix_at d0 n ->
            datatype_suffix_at d0 n (SmtDatatype.sum c dTail) ->
              datatype_cons_has_typeRef_field c ->
                datatype_typeRef_prefix_at d0 (native_nat_succ n)
  | native_nat_zero, c, dTail, _hPrefix, hSuffix, hHas => by
      simp [datatype_suffix_at] at hSuffix
      subst hSuffix
      simp [datatype_typeRef_prefix_at, hHas]
  | native_nat_succ n, c, dTail, hPrefix, hSuffix, hHas => by
      cases d0 with
      | null =>
          simp [datatype_typeRef_prefix_at] at hPrefix
      | sum c0 d0Tail =>
          have hTailPrefix :
              datatype_typeRef_prefix_at d0Tail n := hPrefix.2
          have hTailSuffix :
              datatype_suffix_at d0Tail n (SmtDatatype.sum c dTail) := by
            simpa [datatype_suffix_at] using hSuffix
          exact ⟨hPrefix.1,
            datatype_typeRef_prefix_at_succ_of_suffix d0Tail n c dTail
              hTailPrefix hTailSuffix hHas⟩

private theorem datatype_default_typed_suffix_of_typeRef_prefix_at
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      (n : native_Nat) ->
        (dSuffix : SmtDatatype) ->
          datatype_typeRef_prefix_at d n ->
            datatype_suffix_at d n dSuffix ->
              datatype_default_has_typed_constructor_from s d0 d ->
                datatype_default_has_typed_constructor_from s d0 dSuffix
  | d, native_nat_zero, dSuffix, _hPrefix, hSuffix, hTyped => by
      simp [datatype_suffix_at] at hSuffix
      subst hSuffix
      exact hTyped
  | SmtDatatype.null, native_nat_succ n, dSuffix, hPrefix, _hSuffix, _hTyped => by
      simp [datatype_typeRef_prefix_at] at hPrefix
  | SmtDatatype.sum c dTail, native_nat_succ n, dSuffix, hPrefix, hSuffix,
      hTyped => by
      have hTailTyped :
          datatype_default_has_typed_constructor_from s d0 dTail :=
        datatype_default_tail_of_typed_constructor_from_of_has_typeRef s d0
          c dTail hPrefix.1 hTyped
      exact datatype_default_typed_suffix_of_typeRef_prefix_at s d0 dTail n
        dSuffix hPrefix.2 (by simpa [datatype_suffix_at] using hSuffix)
        hTailTyped

private theorem datatype_default_typed_of_typeRef_prefix_at_suffix
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      (n : native_Nat) ->
        (dSuffix : SmtDatatype) ->
          datatype_typeRef_prefix_at d n ->
            datatype_suffix_at d n dSuffix ->
              datatype_default_has_typed_constructor_from s d0 dSuffix ->
                datatype_default_has_typed_constructor_from s d0 d
  | d, native_nat_zero, dSuffix, _hPrefix, hSuffix, hTyped => by
      simp [datatype_suffix_at] at hSuffix
      subst hSuffix
      exact hTyped
  | SmtDatatype.null, native_nat_succ n, dSuffix, hPrefix, _hSuffix, _hTyped => by
      simp [datatype_typeRef_prefix_at] at hPrefix
  | SmtDatatype.sum c dTail, native_nat_succ n, dSuffix, hPrefix, hSuffix,
      hTyped => by
      exact Or.inr ⟨hPrefix.1,
        datatype_default_typed_of_typeRef_prefix_at_suffix s d0 dTail n
          dSuffix hPrefix.2 (by simpa [datatype_suffix_at] using hSuffix)
          hTyped⟩

private def datatype_typeRef_prefix_to_no_deferred : SmtDatatype -> Prop
  | SmtDatatype.null => False
  | SmtDatatype.sum c d =>
      datatype_cons_no_deferred_fields c ∨
        datatype_cons_has_typeRef_field c ∧
          datatype_typeRef_prefix_to_no_deferred d

private def datatype_typeRef_prefix_to_simple : SmtDatatype -> Prop
  | SmtDatatype.null => False
  | SmtDatatype.sum c d =>
      datatype_cons_simple_defaultable_fields c ∨
        datatype_cons_has_typeRef_field c ∧
          datatype_typeRef_prefix_to_simple d

private theorem datatype_default_typed_canonical_of_typed_constructor_from
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      (n : native_Nat) ->
        datatype_suffix_at d0 n d ->
          datatype_default_has_typed_constructor_from s d0 d ->
            __smtx_typeof_value (__smtx_datatype_default s d0 d n) =
                SmtType.Datatype s d0 ∧
              __smtx_value_canonical (__smtx_datatype_default s d0 d n)
  | SmtDatatype.null, n, _hSuffix, hTyped => by
      simp [datatype_default_has_typed_constructor_from] at hTyped
  | SmtDatatype.sum c dTail, n, hSuffix, hTyped => by
      cases hTyped with
      | inl hArgs =>
          let v := SmtValue.DtCons s d0 n
          have hvTy :
              __smtx_typeof_value v =
                __smtx_typeof_dt_cons_value_rec (SmtType.Datatype s d0)
                  (SmtDatatype.sum (__smtx_dtc_substitute s d0 c)
                    (__smtx_dt_substitute s d0 dTail))
                  native_nat_zero := by
            simpa [v, __smtx_dt_substitute] using
              typeof_dt_cons_value_of_suffix_at s d0
                (SmtDatatype.sum c dTail) n hSuffix
          have hvCan : __smtx_value_canonical v := by
            simp [v, __smtx_value_canonical, __smtx_value_canonical_bool]
          have hCons :=
            datatype_cons_default_typed_canonical_of_args_typed s d0
              (__smtx_dt_substitute s d0 dTail) c v hArgs hvTy hvCan
          have hConsNV :
              __smtx_datatype_cons_default s d0 v c ≠ SmtValue.NotValue := by
            intro hEq
            have hTyNone :
                __smtx_typeof_value (__smtx_datatype_cons_default s d0 v c) =
                  SmtType.None := by
              simp [hEq, __smtx_typeof_value]
            have hBad : SmtType.Datatype s d0 = SmtType.None :=
              hCons.1.symm.trans hTyNone
            cases hBad
          have hConsVeq :
              native_veq (__smtx_datatype_cons_default s d0 v c)
                  SmtValue.NotValue =
                false :=
            native_veq_notValue_false_of_ne hConsNV
          simpa [__smtx_datatype_default, v, hConsVeq, native_not, native_ite]
            using hCons
      | inr hTail =>
          have hFirst :
              __smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c =
                SmtValue.NotValue :=
            datatype_cons_default_eq_notValue_of_has_typeRef_field s d0
              (SmtValue.DtCons s d0 n) c hTail.1
          have hFirstVeq :
              native_veq
                  (__smtx_datatype_cons_default s d0
                    (SmtValue.DtCons s d0 n) c)
                  SmtValue.NotValue =
                true := by
            simp [hFirst, native_veq]
          have hTailSuffix :
              datatype_suffix_at d0 (native_nat_succ n) dTail :=
            datatype_suffix_at_tail d0 n c dTail hSuffix
          simpa [__smtx_datatype_default, hFirstVeq, native_not, native_ite] using
            datatype_default_typed_canonical_of_typed_constructor_from s d0
              dTail (native_nat_succ n) hTailSuffix hTail.2

private theorem datatype_cons_default_productive_of_args_typed
    (s : native_String)
    (d0 : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      datatype_cons_default_args_typed s d0 c ->
        datatype_cons_default_productive s d0 c
  | SmtDatatypeCons.unit, _hArgs => by
      simp [datatype_cons_default_productive]
  | SmtDatatypeCons.cons T c, hArgs => by
      have hArgTy :
          __smtx_typeof_value
              (__smtx_value_dt_substitute s d0 (__smtx_type_default T)) =
            smtx_dtc_field_substitute_type s d0 T :=
        hArgs.1
      have hArgNotNone :
          smtx_dtc_field_substitute_type s d0 T ≠ SmtType.None :=
        hArgs.2.1
      have hArgNV :
          __smtx_value_dt_substitute s d0 (__smtx_type_default T) ≠
            SmtValue.NotValue := by
        intro hEq
        have hNone :
            smtx_dtc_field_substitute_type s d0 T = SmtType.None := by
          rw [← hArgTy]
          simp [hEq, __smtx_typeof_value]
        exact hArgNotNone hNone
      exact ⟨hArgNV,
        datatype_cons_default_productive_of_args_typed s d0 c hArgs.2.2.2⟩

private theorem datatype_default_productive_from_of_typed_constructor_from
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      datatype_default_has_typed_constructor_from s d0 d ->
        datatype_default_productive_from s d0 d
  | SmtDatatype.null, hTyped => by
      simp [datatype_default_has_typed_constructor_from] at hTyped
  | SmtDatatype.sum c dTail, hTyped => by
      cases hTyped with
      | inl hArgs =>
          exact Or.inl
            (datatype_cons_default_productive_of_args_typed s d0 c hArgs)
      | inr hTail =>
          exact Or.inr
            (datatype_default_productive_from_of_typed_constructor_from s d0
              dTail hTail.2)

private theorem datatype_type_default_typed_canonical_of_typed_constructor_from_self
    (s : native_String)
    (d : SmtDatatype)
    (hTyped : datatype_default_has_typed_constructor_from s d d) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  have hDefault :=
    datatype_default_typed_canonical_of_typed_constructor_from s d d
      native_nat_zero (datatype_suffix_at_self d) hTyped
  simpa [__smtx_type_default] using hDefault

private theorem datatype_cons_head_wf_rec_nil_of_no_deferred
    {T : SmtType}
    {c : SmtDatatypeCons}
    {refs : RefList}
    (hWF : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) refs = true)
    (hNo : datatype_cons_no_deferred_fields (SmtDatatypeCons.cons T c)) :
    native_inhabited_type T = true ∧
      __smtx_type_wf_rec T native_reflist_nil = true := by
  cases T <;>
    simp_all [datatype_cons_no_deferred_fields, __smtx_dt_cons_wf_rec,
      __smtx_type_wf_rec, native_ite, native_and]

private theorem dtc_field_substitute_type_eq_self_of_no_deferred
    (s : native_String)
    (d0 : SmtDatatype)
    {T : SmtType}
    {c : SmtDatatypeCons}
    (hNo : datatype_cons_no_deferred_fields (SmtDatatypeCons.cons T c)) :
    smtx_dtc_field_substitute_type s d0 T = T := by
  cases T <;>
    simp_all [datatype_cons_no_deferred_fields, smtx_dtc_field_substitute_type,
      native_Teq, native_ite]

private theorem value_dt_substitute_type_default_datatype_unit_args_typed
    (s : native_String)
    (d0 : SmtDatatype)
    (sNested : native_String)
    (dNestedTail : SmtDatatype) :
    __smtx_typeof_value
          (__smtx_value_dt_substitute s d0
            (__smtx_type_default
              (SmtType.Datatype sNested
                (SmtDatatype.sum SmtDatatypeCons.unit dNestedTail)))) =
        smtx_dtc_field_substitute_type s d0
          (SmtType.Datatype sNested
            (SmtDatatype.sum SmtDatatypeCons.unit dNestedTail)) ∧
      smtx_dtc_field_substitute_type s d0
          (SmtType.Datatype sNested
            (SmtDatatype.sum SmtDatatypeCons.unit dNestedTail)) ≠
        SmtType.None ∧
      __smtx_value_canonical
        (__smtx_value_dt_substitute s d0
          (__smtx_type_default
            (SmtType.Datatype sNested
              (SmtDatatype.sum SmtDatatypeCons.unit dNestedTail)))) := by
  cases hShadow : native_streq s sNested <;>
    simp [__smtx_type_default, __smtx_datatype_default,
      __smtx_datatype_cons_default, __smtx_value_dt_substitute,
      __smtx_typeof_value, __smtx_dt_substitute, __smtx_dtc_substitute,
      __smtx_typeof_dt_cons_value_rec, __smtx_value_canonical,
      __smtx_value_canonical_bool, smtx_dtc_field_substitute_type,
      native_veq, native_not, native_ite, hShadow]

private theorem datatype_cons_default_ne_notValue_of_productive
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (hv : v ≠ SmtValue.NotValue) :
    (c : SmtDatatypeCons) ->
      datatype_cons_default_productive s d c ->
        __smtx_datatype_cons_default s d v c ≠ SmtValue.NotValue
  | SmtDatatypeCons.unit, _hProd => by
      simpa [__smtx_datatype_cons_default] using hv
  | SmtDatatypeCons.cons T c, hProd => by
      have hArg :
          __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
            SmtValue.NotValue := hProd.1
      have hArgVeq :
          native_veq
              (__smtx_value_dt_substitute s d (__smtx_type_default T))
              SmtValue.NotValue = false :=
        native_veq_notValue_false_of_ne hArg
      have hApply :
          SmtValue.Apply v
              (__smtx_value_dt_substitute s d (__smtx_type_default T)) ≠
            SmtValue.NotValue := by
        intro hEq
        cases hEq
      simpa [__smtx_datatype_cons_default, hArgVeq, native_ite] using
        datatype_cons_default_ne_notValue_of_productive s d hApply c hProd.2

private theorem datatype_default_ne_notValue_of_productive_from
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      (n : native_Nat) ->
        datatype_default_productive_from s d0 d ->
          __smtx_datatype_default s d0 d n ≠ SmtValue.NotValue
  | SmtDatatype.null, n, hProd => by
      simp [datatype_default_productive_from] at hProd
  | SmtDatatype.sum c d, n, hProd => by
      cases hProd with
      | inl hCons =>
          have hConsNV :
              __smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c ≠
                SmtValue.NotValue :=
            datatype_cons_default_ne_notValue_of_productive s d0 (by intro h; cases h) c hCons
          have hConsVeq :
              native_veq
                  (__smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c)
                  SmtValue.NotValue = false :=
            native_veq_notValue_false_of_ne hConsNV
          simpa [__smtx_datatype_default, hConsVeq, native_not, native_ite] using hConsNV
      | inr hTail =>
          cases hConsVeq :
              native_veq
                (__smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c)
                SmtValue.NotValue
          · have hConsNV :
                __smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c ≠
                  SmtValue.NotValue :=
              ne_notValue_of_native_veq_notValue_false hConsVeq
            simpa [__smtx_datatype_default, hConsVeq, native_not, native_ite] using hConsNV
          · simpa [__smtx_datatype_default, hConsVeq, native_not, native_ite] using
              datatype_default_ne_notValue_of_productive_from s d0 d
                (native_nat_succ n) hTail

private theorem datatype_cons_default_productive_of_ne_notValue
    (s : native_String)
    (d : SmtDatatype) :
    (c : SmtDatatypeCons) ->
      (v : SmtValue) ->
        __smtx_datatype_cons_default s d v c ≠ SmtValue.NotValue ->
          datatype_cons_default_productive s d c
  | SmtDatatypeCons.unit, v, _hNV => by
      simp [datatype_cons_default_productive]
  | SmtDatatypeCons.cons T c, v, hNV => by
      cases hArg :
          native_veq
            (__smtx_value_dt_substitute s d (__smtx_type_default T))
            SmtValue.NotValue
      · have hArgNV :
            __smtx_value_dt_substitute s d (__smtx_type_default T) ≠
              SmtValue.NotValue :=
          ne_notValue_of_native_veq_notValue_false hArg
        have hTailNV :
            __smtx_datatype_cons_default s d
                (SmtValue.Apply v
                  (__smtx_value_dt_substitute s d (__smtx_type_default T))) c ≠
              SmtValue.NotValue := by
          simpa [__smtx_datatype_cons_default, hArg, native_ite] using hNV
        exact ⟨hArgNV,
          datatype_cons_default_productive_of_ne_notValue s d c
            (SmtValue.Apply v
              (__smtx_value_dt_substitute s d (__smtx_type_default T)))
            hTailNV⟩
      · have hBad :
            __smtx_datatype_cons_default s d v
                (SmtDatatypeCons.cons T c) =
              SmtValue.NotValue := by
          simp [__smtx_datatype_cons_default, hArg, native_ite]
        exact False.elim (hNV hBad)

private theorem datatype_default_productive_from_of_ne_notValue
    (s : native_String)
    (d0 : SmtDatatype) :
    (d : SmtDatatype) ->
      (n : native_Nat) ->
        __smtx_datatype_default s d0 d n ≠ SmtValue.NotValue ->
          datatype_default_productive_from s d0 d
  | SmtDatatype.null, n, hNV => by
      exact False.elim (hNV (by simp [__smtx_datatype_default]))
  | SmtDatatype.sum c d, n, hNV => by
      cases hConsVeq :
          native_veq
            (__smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c)
            SmtValue.NotValue
      · have hConsNV :
            __smtx_datatype_cons_default s d0 (SmtValue.DtCons s d0 n) c ≠
              SmtValue.NotValue :=
          ne_notValue_of_native_veq_notValue_false hConsVeq
        exact Or.inl
          (datatype_cons_default_productive_of_ne_notValue s d0 c
            (SmtValue.DtCons s d0 n) hConsNV)
      · have hTailNV :
            __smtx_datatype_default s d0 d (native_nat_succ n) ≠
              SmtValue.NotValue := by
          simpa [__smtx_datatype_default, hConsVeq, native_not, native_ite]
            using hNV
        exact Or.inr
          (datatype_default_productive_from_of_ne_notValue s d0 d
            (native_nat_succ n) hTailNV)

private theorem datatype_cons_default_ne_notValue_iff_productive
    (s : native_String)
    (d : SmtDatatype)
    {v : SmtValue}
    (hv : v ≠ SmtValue.NotValue)
    (c : SmtDatatypeCons) :
    __smtx_datatype_cons_default s d v c ≠ SmtValue.NotValue ↔
      datatype_cons_default_productive s d c :=
  ⟨datatype_cons_default_productive_of_ne_notValue s d c v,
    datatype_cons_default_ne_notValue_of_productive s d hv c⟩

private theorem datatype_default_ne_notValue_iff_productive_from
    (s : native_String)
    (d0 d : SmtDatatype)
    (n : native_Nat) :
    __smtx_datatype_default s d0 d n ≠ SmtValue.NotValue ↔
      datatype_default_productive_from s d0 d :=
  ⟨datatype_default_productive_from_of_ne_notValue s d0 d n,
    datatype_default_ne_notValue_of_productive_from s d0 d n⟩

private theorem datatype_type_default_ne_notValue_iff_productive
    (s : native_String)
    (d : SmtDatatype) :
    __smtx_type_default (SmtType.Datatype s d) ≠ SmtValue.NotValue ↔
      datatype_default_productive_from s d d := by
  simpa [__smtx_type_default] using
    datatype_default_ne_notValue_iff_productive_from s d d native_nat_zero

private theorem recursive_arg_progress_of_suffix_typeRef
    (s : native_String)
    (d0 : SmtDatatype)
    (n : native_Nat)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (v : SmtValue)
    (hSuffix : datatype_suffix_at d0 n (SmtDatatype.sum c dTail))
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d0 n)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d0)
    (hSelf : datatype_cons_typeRef_fields_self s c)
    (hHasTypeRef : datatype_cons_has_typeRef_field c) :
    ∃ a,
      __smtx_typeof_value a = SmtType.Datatype s d0 ∧
        smt_value_size a < smt_value_size v := by
  have hArgCount :
      value_num_apply_args v =
        __smtx_dt_num_sels (__smtx_dt_substitute s d0 d0) n :=
    value_num_apply_args_eq_dt_num_sels_of_datatype hHead hTy
  rcases typeRef_field_selector_type_of_has_typeRef_field s d0 c
      (__smtx_dt_substitute s d0 dTail) hSelf hHasTypeRef with
    ⟨j, hjLt, hjTy⟩
  have hNumSuffix :
      __smtx_dt_num_sels (__smtx_dt_substitute s d0 d0) n =
        __smtx_dt_num_sels
          (__smtx_dt_substitute s d0 (SmtDatatype.sum c dTail))
          native_nat_zero :=
    dt_num_sels_substitute_of_suffix_at s d0 d0 n
      (SmtDatatype.sum c dTail) hSuffix
  have hjLtValue : j < value_num_apply_args v := by
    rw [hArgCount, hNumSuffix]
    simpa [__smtx_dt_substitute, __smtx_dt_num_sels,
      dtc_num_sels_substitute] using hjLt
  have hRecursiveArgTy :
      __smtx_typeof_value
          (__vsm_apply_arg_nth v j (value_num_apply_args v)) =
        SmtType.Datatype s d0 := by
    have hArgTy :=
      apply_arg_nth_type_of_non_none hHead (by simp [hTy]) hjLtValue
    have hSelSuffix :
        __smtx_ret_typeof_sel_rec
            (__smtx_dt_substitute s d0 d0) n j =
          __smtx_ret_typeof_sel_rec
            (__smtx_dt_substitute s d0 (SmtDatatype.sum c dTail))
            native_nat_zero j :=
      ret_typeof_sel_rec_substitute_of_suffix_at s d0 d0 n
        (SmtDatatype.sum c dTail) j hSuffix
    rw [hSelSuffix] at hArgTy
    simpa [__smtx_dt_substitute, hjTy] using hArgTy
  have hRecursiveArgSmall :
      smt_value_size
          (__vsm_apply_arg_nth v j (value_num_apply_args v)) <
        smt_value_size v :=
    apply_arg_nth_size_lt v hjLtValue
  exact ⟨__vsm_apply_arg_nth v j (value_num_apply_args v),
    hRecursiveArgTy, hRecursiveArgSmall⟩

private theorem nonself_typeRef_field_impossible_of_suffix
    (s : native_String)
    (d0 : SmtDatatype)
    (n : native_Nat)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (v : SmtValue)
    (hSuffix : datatype_suffix_at d0 n (SmtDatatype.sum c dTail))
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d0 n)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d0)
    (hNonself : datatype_cons_has_nonself_typeRef_field s c) :
    False := by
  have hArgCount :
      value_num_apply_args v =
        __smtx_dt_num_sels (__smtx_dt_substitute s d0 d0) n :=
    value_num_apply_args_eq_dt_num_sels_of_datatype hHead hTy
  rcases nonself_typeRef_field_selector_type s d0 c
      (__smtx_dt_substitute s d0 dTail) hNonself with
    ⟨j, r, hjLt, _hrNe, hjTy⟩
  have hNumSuffix :
      __smtx_dt_num_sels (__smtx_dt_substitute s d0 d0) n =
        __smtx_dt_num_sels
          (__smtx_dt_substitute s d0 (SmtDatatype.sum c dTail))
          native_nat_zero :=
    dt_num_sels_substitute_of_suffix_at s d0 d0 n
      (SmtDatatype.sum c dTail) hSuffix
  have hjLtValue : j < value_num_apply_args v := by
    rw [hArgCount, hNumSuffix]
    simpa [__smtx_dt_substitute, __smtx_dt_num_sels,
      dtc_num_sels_substitute] using hjLt
  have hArgTy :=
    apply_arg_nth_type_of_non_none hHead (by simp [hTy]) hjLtValue
  have hSelSuffix :
      __smtx_ret_typeof_sel_rec
          (__smtx_dt_substitute s d0 d0) n j =
        __smtx_ret_typeof_sel_rec
          (__smtx_dt_substitute s d0 (SmtDatatype.sum c dTail))
          native_nat_zero j :=
    ret_typeof_sel_rec_substitute_of_suffix_at s d0 d0 n
      (SmtDatatype.sum c dTail) j hSuffix
  have hArgTyRef :
      __smtx_typeof_value
          (__vsm_apply_arg_nth v j (value_num_apply_args v)) =
        SmtType.TypeRef r := by
    rw [hSelSuffix] at hArgTy
    simpa [__smtx_dt_substitute, hjTy] using hArgTy
  exact typeof_value_ne_typeRef
    (__vsm_apply_arg_nth v j (value_num_apply_args v)) r hArgTyRef

private theorem datatype_default_has_typed_constructor_from_of_current_witness
    (s : native_String)
    (d0 : SmtDatatype)
    (n : native_Nat)
    (c : SmtDatatypeCons)
    (dTail : SmtDatatype)
    (refs : RefList)
    (v : SmtValue)
    (hPrefix : datatype_typeRef_prefix_at d0 n)
    (hSuffix : datatype_suffix_at d0 n (SmtDatatype.sum c dTail))
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d0 n)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d0)
    (hConsWf :
      __smtx_dt_cons_wf_rec c refs = true)
    (hArgsNoTypeRef :
      datatype_suffix_at d0 n (SmtDatatype.sum c dTail) ->
      __smtx_dt_cons_wf_rec c refs = true ->
        ¬ datatype_cons_has_typeRef_field c ->
          datatype_cons_default_args_typed s d0 c)
    (hSmallTop :
      ∀ a,
        __smtx_typeof_value a = SmtType.Datatype s d0 ->
          smt_value_size a < smt_value_size v ->
            datatype_default_has_typed_constructor_from s d0 d0) :
    datatype_default_has_typed_constructor_from s d0
      (SmtDatatype.sum c dTail) := by
  by_cases hHasTypeRef : datatype_cons_has_typeRef_field c
  · cases datatype_cons_typeRef_fields_self_or_nonself s c with
    | inl hSelf =>
        rcases recursive_arg_progress_of_suffix_typeRef s d0 n c dTail v
            hSuffix hHead hTy hSelf hHasTypeRef with
          ⟨a, hATy, hASmall⟩
        have hTop : datatype_default_has_typed_constructor_from s d0 d0 :=
          hSmallTop a hATy hASmall
        have hCurrent :
            datatype_default_has_typed_constructor_from s d0
              (SmtDatatype.sum c dTail) :=
          datatype_default_typed_suffix_of_typeRef_prefix_at s d0 d0 n
            (SmtDatatype.sum c dTail) hPrefix hSuffix hTop
        exact Or.inr ⟨hHasTypeRef,
          datatype_default_tail_of_typed_constructor_from_of_has_typeRef s d0
            c dTail hHasTypeRef hCurrent⟩
    | inr hNonself =>
        exact False.elim
          (nonself_typeRef_field_impossible_of_suffix s d0 n c dTail v
            hSuffix hHead hTy hNonself)
  · exact Or.inl (hArgsNoTypeRef hSuffix hConsWf hHasTypeRef)

private theorem datatype_default_has_typed_constructor_from_of_witness_scan
    (s : native_String)
    (d0 : SmtDatatype)
    (refs : RefList)
    (v : SmtValue)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d0)
    (hArgsNoTypeRef :
      ∀ n c dTail,
        datatype_suffix_at d0 n (SmtDatatype.sum c dTail) ->
        __smtx_dt_cons_wf_rec c refs = true ->
          ¬ datatype_cons_has_typeRef_field c ->
            datatype_cons_default_args_typed s d0 c)
    (hSmallTop :
      ∀ a,
        __smtx_typeof_value a = SmtType.Datatype s d0 ->
          smt_value_size a < smt_value_size v ->
            datatype_default_has_typed_constructor_from s d0 d0) :
    (d : SmtDatatype) ->
      (n iRel : native_Nat) ->
        datatype_suffix_at d0 n d ->
          datatype_typeRef_prefix_at d0 n ->
            __smtx_dt_wf_rec d refs = true ->
              __vsm_apply_head v = SmtValue.DtCons s d0 (n + iRel) ->
                datatype_default_has_typed_constructor_from s d0 d
  | SmtDatatype.null, n, iRel, _hSuffix, _hPrefix, hWF, _hHead => by
      simp [__smtx_dt_wf_rec] at hWF
  | SmtDatatype.sum c dTail, n, iRel, hSuffix, hPrefix, hWF, hHead => by
      have hConsWf :
          __smtx_dt_cons_wf_rec c refs = true :=
        dt_wf_cons_of_wf hWF
      by_cases hHasTypeRef : datatype_cons_has_typeRef_field c
      · cases iRel with
        | zero =>
            have hHeadCurrent :
                __vsm_apply_head v = SmtValue.DtCons s d0 n := by
              simpa using hHead
            exact datatype_default_has_typed_constructor_from_of_current_witness
              s d0 n c dTail refs v hPrefix hSuffix hHeadCurrent hTy hConsWf
              (hArgsNoTypeRef n c dTail) hSmallTop
        | succ iTail =>
            cases dTail with
            | null =>
                rcases datatype_cons_suffix_at_of_datatype_value_head hHead hTy with
                  ⟨cWitness, dWitnessTail, hWitnessSuffix⟩
                have hIndex :
                    n + Nat.succ iTail = Nat.succ n + iTail := by
                  rw [Nat.add_succ, Nat.succ_add]
                have hWitnessSuffix' :
                    datatype_suffix_at d0 (Nat.succ n + iTail)
                      (SmtDatatype.sum cWitness dWitnessTail) := by
                  simpa [hIndex] using hWitnessSuffix
                have hTailSuffix :
                    datatype_suffix_at d0 (Nat.succ n) SmtDatatype.null :=
                  datatype_suffix_at_tail d0 n c SmtDatatype.null hSuffix
                cases iTail with
                | zero =>
                    have hUniq :
                        SmtDatatype.null =
                          SmtDatatype.sum cWitness dWitnessTail :=
                      datatype_suffix_at_unique d0 (Nat.succ n)
                        SmtDatatype.null
                        (SmtDatatype.sum cWitness dWitnessTail)
                        hTailSuffix (by simpa using hWitnessSuffix')
                    cases hUniq
                | succ k =>
                    exact False.elim
                      ((datatype_suffix_at_null_no_succ d0 (Nat.succ n)
                        hTailSuffix k (SmtDatatype.sum cWitness dWitnessTail))
                        (by
                          simpa [Nat.succ_add] using hWitnessSuffix'))
            | sum cNext dRest =>
                have hTailWf :
                    __smtx_dt_wf_rec (SmtDatatype.sum cNext dRest) refs =
                      true :=
                  dt_wf_tail_of_nonempty_tail_wf
                    (c := c) (cTail := cNext) (dTail := dRest)
                    (refs := refs)
                    hWF
                have hTailSuffix :
                    datatype_suffix_at d0 (Nat.succ n)
                      (SmtDatatype.sum cNext dRest) :=
                  datatype_suffix_at_tail d0 n c
                    (SmtDatatype.sum cNext dRest) hSuffix
                have hTailPrefix :
                    datatype_typeRef_prefix_at d0 (Nat.succ n) :=
                  datatype_typeRef_prefix_at_succ_of_suffix d0 n c
                    (SmtDatatype.sum cNext dRest) hPrefix hSuffix hHasTypeRef
                have hIndex :
                    n + Nat.succ iTail = Nat.succ n + iTail := by
                  rw [Nat.add_succ, Nat.succ_add]
                have hHeadTail :
                    __vsm_apply_head v =
                      SmtValue.DtCons s d0 (Nat.succ n + iTail) := by
                  simpa [hIndex] using hHead
                exact Or.inr ⟨hHasTypeRef,
                  datatype_default_has_typed_constructor_from_of_witness_scan
                    s d0 refs v hTy hArgsNoTypeRef hSmallTop
                    (SmtDatatype.sum cNext dRest) (Nat.succ n) iTail
                    hTailSuffix hTailPrefix hTailWf hHeadTail⟩
      · exact Or.inl (hArgsNoTypeRef n c dTail hSuffix hConsWf hHasTypeRef)

private theorem type_default_typed_canonical_with_datatype_callback
    (hDatatype :
      ∀ s d,
        native_inhabited_type (SmtType.Datatype s d) = true ->
          __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true ->
            __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
                SmtType.Datatype s d ∧
              __smtx_value_canonical
                (__smtx_type_default (SmtType.Datatype s d))) :
    (T : SmtType) ->
      native_inhabited_type T = true ->
        __smtx_type_wf_rec T native_reflist_nil = true ->
          __smtx_typeof_value (__smtx_type_default T) = T ∧
            __smtx_value_canonical (__smtx_type_default T)
  | SmtType.None, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.Bool, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Int, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Real, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.RegLan, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, native_ite, native_and,
          native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total,
          native_nat_to_int, native_int_to_nat]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, native_ite, native_zleq, native_zeq,
          native_mod_total, native_int_pow2, native_zexp_total, native_nat_to_int]
  | SmtType.Map A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB :=
        type_default_typed_canonical_with_datatype_callback hDatatype
          B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.Set A, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq, __smtx_typeof_value, __smtx_type_default]
  | SmtType.Seq A, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_seq_value,
        __smtx_value_canonical, __smtx_value_canonical_bool, __smtx_seq_canonical]
  | SmtType.Char, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Datatype s d, hInh, hRec => by
      exact hDatatype s d hInh hRec
  | SmtType.TypeRef s, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.USort i, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.FunType A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB :=
        type_default_typed_canonical_with_datatype_callback hDatatype
          B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_fun_type, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.DtcAppType A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
termination_by T _ _ => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals omega

private theorem type_default_typed_canonical_with_datatype_bound
    (limit : Nat)
    (hDatatype :
      ∀ s d,
        sizeOf (SmtType.Datatype s d) < limit ->
        native_inhabited_type (SmtType.Datatype s d) = true ->
          __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true ->
            __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
                SmtType.Datatype s d ∧
              __smtx_value_canonical
                (__smtx_type_default (SmtType.Datatype s d))) :
    (T : SmtType) ->
      sizeOf T < limit ->
        native_inhabited_type T = true ->
          __smtx_type_wf_rec T native_reflist_nil = true ->
            __smtx_typeof_value (__smtx_type_default T) = T ∧
              __smtx_value_canonical (__smtx_type_default T)
  | SmtType.None, _hLt, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.Bool, _hLt, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Int, _hLt, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Real, _hLt, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.RegLan, _hLt, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, _hLt, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, native_ite, native_and,
          native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total,
          native_nat_to_int, native_int_to_nat]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, native_ite, native_zleq, native_zeq,
          native_mod_total, native_int_pow2, native_zexp_total, native_nat_to_int]
  | SmtType.Map A B, hLt, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hBLt : sizeOf B < limit := by
        simp at hLt ⊢
        omega
      have hB :=
        type_default_typed_canonical_with_datatype_bound limit hDatatype
          B hBLt hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.Set A, _hLt, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq, __smtx_typeof_value, __smtx_type_default]
  | SmtType.Seq A, _hLt, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_seq_value,
        __smtx_value_canonical, __smtx_value_canonical_bool, __smtx_seq_canonical]
  | SmtType.Char, _hLt, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Datatype s d, hLt, hInh, hRec => by
      exact hDatatype s d hLt hInh hRec
  | SmtType.TypeRef s, _hLt, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.USort i, _hLt, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.FunType A B, hLt, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hBLt : sizeOf B < limit := by
        simp at hLt ⊢
        omega
      have hB :=
        type_default_typed_canonical_with_datatype_bound limit hDatatype
          B hBLt hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_fun_type, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.DtcAppType A B, _hLt, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
termination_by T _ _ _ => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem reflist_contains_insert_congr
    {refs1 refs2 : RefList}
    (h :
      ∀ r,
        native_reflist_contains refs1 r =
          native_reflist_contains refs2 r)
    (s r : native_String) :
    native_reflist_contains (native_reflist_insert refs1 s) r =
      native_reflist_contains (native_reflist_insert refs2 s) r := by
  simp [native_reflist_contains, native_reflist_insert] at h ⊢
  by_cases hs : r = s
  · subst hs
    simp
  · simp [hs, h r]

mutual
private theorem type_wf_rec_ref_equiv :
    (T : SmtType) ->
      (refs1 refs2 : RefList) ->
        (∀ r,
          native_reflist_contains refs1 r =
            native_reflist_contains refs2 r) ->
          __smtx_type_wf_rec T refs1 = __smtx_type_wf_rec T refs2
  | SmtType.Datatype s d, refs1, refs2, h => by
      simp [__smtx_type_wf_rec]
      exact dt_wf_rec_ref_equiv d (native_reflist_insert refs1 s)
        (native_reflist_insert refs2 s) (reflist_contains_insert_congr h s)
  | SmtType.TypeRef s, refs1, refs2, h => by
      simpa [__smtx_type_wf_rec] using h s
  | SmtType.Seq A, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.Map A B, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.FunType A B, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.Set A, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.DtcAppType A B, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.None, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.RegLan, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.Bool, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.Int, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.Real, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.BitVec w, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.Char, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]
  | SmtType.USort i, _refs1, _refs2, _h => by
      simp [__smtx_type_wf_rec]

private theorem dt_wf_rec_ref_equiv :
    (d : SmtDatatype) ->
      (refs1 refs2 : RefList) ->
        (∀ r,
          native_reflist_contains refs1 r =
            native_reflist_contains refs2 r) ->
          __smtx_dt_wf_rec d refs1 = __smtx_dt_wf_rec d refs2
  | SmtDatatype.null, _refs1, _refs2, _h => by
      simp [__smtx_dt_wf_rec]
  | SmtDatatype.sum c SmtDatatype.null, refs1, refs2, h => by
      simp [__smtx_dt_wf_rec]
      exact dt_cons_wf_rec_ref_equiv c refs1 refs2 h
  | SmtDatatype.sum c (SmtDatatype.sum c2 d2), refs1, refs2, h => by
      simp [__smtx_dt_wf_rec, native_ite]
      rw [dt_cons_wf_rec_ref_equiv c refs1 refs2 h]
      rw [dt_wf_rec_ref_equiv (SmtDatatype.sum c2 d2) refs1 refs2 h]

private theorem dt_cons_wf_rec_ref_equiv :
    (c : SmtDatatypeCons) ->
      (refs1 refs2 : RefList) ->
        (∀ r,
          native_reflist_contains refs1 r =
            native_reflist_contains refs2 r) ->
          __smtx_dt_cons_wf_rec c refs1 =
            __smtx_dt_cons_wf_rec c refs2
  | SmtDatatypeCons.unit, _refs1, _refs2, _h => by
      simp [__smtx_dt_cons_wf_rec]
  | SmtDatatypeCons.cons T c, refs1, refs2, h => by
      cases T <;> simp [__smtx_dt_cons_wf_rec, native_ite]
      all_goals try rw [dt_cons_wf_rec_ref_equiv c refs1 refs2 h]
      all_goals try rw [type_wf_rec_ref_equiv _ refs1 refs2 h]
      all_goals try rw [h _]
end

private theorem type_wf_rec_nil_of_non_datatype_non_typeRef_for_field
    (T : SmtType)
    (refs : RefList)
    (hDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d')
    (hTypeRef : ∀ r, T ≠ SmtType.TypeRef r)
    (hRec : __smtx_type_wf_rec T refs = true) :
    __smtx_type_wf_rec T native_reflist_nil = true := by
  cases T <;> simp_all [__smtx_type_wf_rec]

private theorem field_default_substitute_typed_canonical_with_datatype_callback
    (sub : native_String)
    (base : SmtDatatype)
    (refs : RefList)
    (hTypeDatatype :
      ∀ s d,
        native_inhabited_type (SmtType.Datatype s d) = true ->
          __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true ->
            __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
                SmtType.Datatype s d ∧
              __smtx_value_canonical
                (__smtx_type_default (SmtType.Datatype s d)))
    (hFieldDatatype :
      ∀ sNested dNested,
        native_inhabited_type (SmtType.Datatype sNested dNested) = true ->
          __smtx_type_wf_rec (SmtType.Datatype sNested dNested) refs = true ->
            __smtx_typeof_value
                (__smtx_value_dt_substitute sub base
                  (__smtx_type_default (SmtType.Datatype sNested dNested))) =
              smtx_dtc_field_substitute_type sub base
                (SmtType.Datatype sNested dNested) ∧
            smtx_dtc_field_substitute_type sub base
                (SmtType.Datatype sNested dNested) ≠ SmtType.None ∧
            __smtx_value_canonical
              (__smtx_value_dt_substitute sub base
                (__smtx_type_default (SmtType.Datatype sNested dNested)))) :
    (T : SmtType) ->
      (∀ r, T ≠ SmtType.TypeRef r) ->
        native_inhabited_type T = true ->
          __smtx_type_wf_rec T refs = true ->
            __smtx_typeof_value
                (__smtx_value_dt_substitute sub base (__smtx_type_default T)) =
              smtx_dtc_field_substitute_type sub base T ∧
            smtx_dtc_field_substitute_type sub base T ≠ SmtType.None ∧
            __smtx_value_canonical
              (__smtx_value_dt_substitute sub base (__smtx_type_default T))
  | T, hTypeRef, hInh, hRec => by
      by_cases hDatatype : ∃ sNested dNested, T = SmtType.Datatype sNested dNested
      · rcases hDatatype with ⟨sNested, dNested, rfl⟩
        exact hFieldDatatype sNested dNested hInh hRec
      · have hNoDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d' := by
          intro s' d' hEq
          exact hDatatype ⟨s', d', hEq⟩
        have hSubEq :
            __smtx_value_dt_substitute sub base (__smtx_type_default T) =
              __smtx_type_default T :=
          value_dt_substitute_type_default_eq_of_not_datatype sub base T
            hNoDatatype
        have hFieldEq : smtx_dtc_field_substitute_type sub base T = T := by
          cases T <;> simp_all [smtx_dtc_field_substitute_type, native_Teq,
            native_ite]
        have hRecNil :
            __smtx_type_wf_rec T native_reflist_nil = true :=
          type_wf_rec_nil_of_non_datatype_non_typeRef_for_field T refs
            hNoDatatype hTypeRef hRec
        have hDef :=
          type_default_typed_canonical_with_datatype_callback hTypeDatatype
            T hInh hRecNil
        have hTWF : __smtx_type_wf T = true :=
          type_wf_of_inhabited_and_wf_rec hInh hRecNil
        exact ⟨by rw [hSubEq, hFieldEq]; exact hDef.1,
          by rw [hFieldEq]; exact type_wf_non_none hTWF,
          by rw [hSubEq]; exact hDef.2⟩

private theorem field_default_substitute_typed_canonical_with_datatype_bound
    (limit : Nat)
    (sub : native_String)
    (base : SmtDatatype)
    (refs : RefList)
    (hTypeDatatype :
      ∀ s d,
        sizeOf (SmtType.Datatype s d) < limit ->
        native_inhabited_type (SmtType.Datatype s d) = true ->
          __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true ->
            __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
                SmtType.Datatype s d ∧
              __smtx_value_canonical
                (__smtx_type_default (SmtType.Datatype s d)))
    (hFieldDatatype :
      ∀ sNested dNested,
        sizeOf (SmtType.Datatype sNested dNested) < limit ->
        native_inhabited_type (SmtType.Datatype sNested dNested) = true ->
          __smtx_type_wf_rec (SmtType.Datatype sNested dNested) refs = true ->
            __smtx_typeof_value
                (__smtx_value_dt_substitute sub base
                  (__smtx_type_default (SmtType.Datatype sNested dNested))) =
              smtx_dtc_field_substitute_type sub base
                (SmtType.Datatype sNested dNested) ∧
            smtx_dtc_field_substitute_type sub base
                (SmtType.Datatype sNested dNested) ≠ SmtType.None ∧
            __smtx_value_canonical
              (__smtx_value_dt_substitute sub base
                (__smtx_type_default (SmtType.Datatype sNested dNested)))) :
    (T : SmtType) ->
      sizeOf T < limit ->
      (∀ r, T ≠ SmtType.TypeRef r) ->
        native_inhabited_type T = true ->
          __smtx_type_wf_rec T refs = true ->
            __smtx_typeof_value
                (__smtx_value_dt_substitute sub base (__smtx_type_default T)) =
              smtx_dtc_field_substitute_type sub base T ∧
            smtx_dtc_field_substitute_type sub base T ≠ SmtType.None ∧
            __smtx_value_canonical
              (__smtx_value_dt_substitute sub base (__smtx_type_default T))
  | T, hLt, hTypeRef, hInh, hRec => by
      by_cases hDatatype : ∃ sNested dNested, T = SmtType.Datatype sNested dNested
      · rcases hDatatype with ⟨sNested, dNested, rfl⟩
        exact hFieldDatatype sNested dNested hLt hInh hRec
      · have hNoDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d' := by
          intro s' d' hEq
          exact hDatatype ⟨s', d', hEq⟩
        have hSubEq :
            __smtx_value_dt_substitute sub base (__smtx_type_default T) =
              __smtx_type_default T :=
          value_dt_substitute_type_default_eq_of_not_datatype sub base T
            hNoDatatype
        have hFieldEq : smtx_dtc_field_substitute_type sub base T = T := by
          cases T <;> simp_all [smtx_dtc_field_substitute_type, native_Teq,
            native_ite]
        have hRecNil :
            __smtx_type_wf_rec T native_reflist_nil = true :=
          type_wf_rec_nil_of_non_datatype_non_typeRef_for_field T refs
            hNoDatatype hTypeRef hRec
        have hDef :=
          type_default_typed_canonical_with_datatype_bound limit hTypeDatatype
            T hLt hInh hRecNil
        have hTWF : __smtx_type_wf T = true :=
          type_wf_of_inhabited_and_wf_rec hInh hRecNil
        exact ⟨by rw [hSubEq, hFieldEq]; exact hDef.1,
          by rw [hFieldEq]; exact type_wf_non_none hTWF,
          by rw [hSubEq]; exact hDef.2⟩

private theorem datatype_type_default_typed_canonical_of_wf_rec_deferred
    (s : native_String)
    (d : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  have hTyped : datatype_default_has_typed_constructor_from s d d := by
    cases d with
    | null =>
        simp [__smtx_type_wf_rec, __smtx_dt_wf_rec] at hRec
    | sum c dTail =>
        have hDtWf :
            __smtx_dt_wf_rec (SmtDatatype.sum c dTail)
                (native_reflist_insert native_reflist_nil s) =
              true := by
          simpa [__smtx_type_wf_rec] using hRec
        have hWitness : type_inhabited (SmtType.Datatype s (SmtDatatype.sum c dTail)) :=
          (smtx_inhabited_type_eq_true_iff
            (SmtType.Datatype s (SmtDatatype.sum c dTail))).1 hInh
        rcases hWitness with ⟨v, hv⟩
        have hTypedBySize :
            ∀ n,
              ∀ v',
                smt_value_size v' = n ->
                  __smtx_typeof_value v' =
                    SmtType.Datatype s (SmtDatatype.sum c dTail) ->
                    datatype_default_has_typed_constructor_from s
                      (SmtDatatype.sum c dTail)
                      (SmtDatatype.sum c dTail) := by
          intro n
          induction n using Nat.strongRecOn with
          | ind n ih =>
              intro v' hSize hv'
              rcases value_head_dtCons_of_datatype_type hv' with
                ⟨i, hHead⟩
              have hArgsNoTypeRef :
                  ∀ nCur cCur dCurTail,
                    datatype_suffix_at (SmtDatatype.sum c dTail) nCur
                        (SmtDatatype.sum cCur dCurTail) ->
                    __smtx_dt_cons_wf_rec cCur
                        (native_reflist_insert native_reflist_nil s) =
                        true ->
                      ¬ datatype_cons_has_typeRef_field cCur ->
                        datatype_cons_default_args_typed s
                          (SmtDatatype.sum c dTail) cCur := by
                intro nCur cCur dCurTail hCurSuffix hConsWf hNoTypeRef
                let limit := sizeOf (SmtDatatype.sum c dTail)
                have hCurSize : sizeOf cCur < limit := by
                  have hC :=
                    datatype_cons_size_lt_of_suffix
                      (SmtDatatype.sum c dTail) nCur cCur dCurTail
                      hCurSuffix
                  simp [limit] at hC ⊢
                  omega
                exact
                  datatype_cons_default_args_typed_of_no_typeRef_with_field_defaults_bounded
                    s (SmtDatatype.sum c dTail)
                    (native_reflist_insert native_reflist_nil s) limit
                    (by
                      intro T hTLt hNotTypeRef hFieldInh hFieldRec
                      have hDatatypeDefaults :
                          (∀ sD dD,
                            sizeOf (SmtType.Datatype sD dD) < limit ->
                            native_inhabited_type (SmtType.Datatype sD dD) =
                                true ->
                              __smtx_type_wf_rec (SmtType.Datatype sD dD)
                                  native_reflist_nil =
                                true ->
                                __smtx_typeof_value
                                      (__smtx_type_default
                                        (SmtType.Datatype sD dD)) =
                                    SmtType.Datatype sD dD ∧
                                  __smtx_value_canonical
                                    (__smtx_type_default
                                      (SmtType.Datatype sD dD))) ∧
                            (∀ sNested dNested,
                              sizeOf (SmtType.Datatype sNested dNested) <
                                limit ->
                              native_inhabited_type
                                  (SmtType.Datatype sNested dNested) =
                                true ->
                                __smtx_type_wf_rec
                                    (SmtType.Datatype sNested dNested)
                                    (native_reflist_insert native_reflist_nil s) =
                                  true ->
                                  __smtx_typeof_value
                                      (__smtx_value_dt_substitute s
                                        (SmtDatatype.sum c dTail)
                                        (__smtx_type_default
                                          (SmtType.Datatype sNested dNested))) =
                                    smtx_dtc_field_substitute_type s
                                      (SmtDatatype.sum c dTail)
                                      (SmtType.Datatype sNested dNested) ∧
                                  smtx_dtc_field_substitute_type s
                                      (SmtDatatype.sum c dTail)
                                      (SmtType.Datatype sNested dNested) ≠
                                    SmtType.None ∧
                                  __smtx_value_canonical
                                    (__smtx_value_dt_substitute s
                                      (SmtDatatype.sum c dTail)
                                      (__smtx_type_default
                                        (SmtType.Datatype sNested dNested)))) := by
                        constructor
                        · intro sD dD hLt hDInh hDRec
                          have hDLt :
                              sizeOf dD <
                                sizeOf (SmtDatatype.sum c dTail) :=
                            datatype_payload_size_lt_of_type_size_lt
                              (by simpa [limit] using hLt)
                          exact
                            datatype_type_default_typed_canonical_of_wf_rec_deferred
                              sD dD hDInh hDRec
                        · intro sNested dNested hLt hNestedInh hNestedRec
                          by_cases hShadow : native_streq s sNested = true
                          · have hName : s = sNested := by
                              simpa [native_streq] using hShadow
                            subst sNested
                            have hRefs :
                                ∀ r,
                                  native_reflist_contains
                                      (native_reflist_insert
                                        (native_reflist_insert
                                          native_reflist_nil s) s) r =
                                    native_reflist_contains
                                      (native_reflist_insert
                                        native_reflist_nil s) r := by
                              intro r
                              simp [native_reflist_contains,
                                native_reflist_insert]
                            have hDtEq :
                                __smtx_dt_wf_rec dNested
                                    (native_reflist_insert
                                      (native_reflist_insert
                                        native_reflist_nil s) s) =
                                  __smtx_dt_wf_rec dNested
                                    (native_reflist_insert native_reflist_nil s) :=
                              dt_wf_rec_ref_equiv dNested
                                (native_reflist_insert
                                  (native_reflist_insert native_reflist_nil s) s)
                                (native_reflist_insert native_reflist_nil s)
                                hRefs
                            have hNestedDtRec :
                                __smtx_dt_wf_rec dNested
                                    (native_reflist_insert
                                      (native_reflist_insert
                                        native_reflist_nil s) s) =
                                  true := by
                              simpa [__smtx_type_wf_rec] using hNestedRec
                            have hNestedRecNil :
                                __smtx_type_wf_rec
                                    (SmtType.Datatype s dNested)
                                    native_reflist_nil =
                                  true := by
                              have hDtNil :
                                  __smtx_dt_wf_rec dNested
                                      (native_reflist_insert
                                        native_reflist_nil s) =
                                    true := by
                                rw [← hDtEq]
                                exact hNestedDtRec
                              simpa [__smtx_type_wf_rec] using hDtNil
                            have hNestedDLt :
                                sizeOf dNested <
                                  sizeOf (SmtDatatype.sum c dTail) :=
                              datatype_payload_size_lt_of_type_size_lt
                                (by simpa [limit] using hLt)
                            have hDef :=
                              datatype_type_default_typed_canonical_of_wf_rec_deferred
                                s dNested hNestedInh hNestedRecNil
                            rcases value_head_dtCons_of_datatype_type hDef.1 with
                              ⟨iDef, hHeadDef⟩
                            have hSubEq :
                                __smtx_value_dt_substitute s
                                    (SmtDatatype.sum c dTail)
                                    (__smtx_type_default
                                      (SmtType.Datatype s dNested)) =
                                  __smtx_type_default
                                    (SmtType.Datatype s dNested) :=
                              value_dt_substitute_shadow_of_apply_head s
                                (SmtDatatype.sum c dTail)
                                (__smtx_type_default
                                  (SmtType.Datatype s dNested))
                                ⟨dNested, iDef, hHeadDef⟩
                            have hFieldEq :
                                smtx_dtc_field_substitute_type s
                                    (SmtDatatype.sum c dTail)
                                    (SmtType.Datatype s dNested) =
                                  SmtType.Datatype s dNested := by
                              simp [smtx_dtc_field_substitute_type,
                                native_streq, native_ite]
                            have hFieldNotNone :
                                smtx_dtc_field_substitute_type s
                                    (SmtDatatype.sum c dTail)
                                    (SmtType.Datatype s dNested) ≠
                                  SmtType.None := by
                              rw [hFieldEq]
                              intro hNone
                              cases hNone
                            have hSubCanon :
                                __smtx_value_canonical
                                  (__smtx_value_dt_substitute s
                                    (SmtDatatype.sum c dTail)
                                    (__smtx_type_default
                                      (SmtType.Datatype s dNested))) := by
                              rw [hSubEq]
                              exact hDef.2
                            exact ⟨by
                                rw [hSubEq, hFieldEq]
                                exact hDef.1,
                              hFieldNotNone, hSubCanon⟩
                          · -- Remaining non-shadow obligation: this is now the
                            -- generic datatype-value substitution typing step.
                            -- The head/full-arity part is
                            -- `value_dt_substitute_datatype_head_full_args`;
                            -- what remains is showing the substituted default
                            -- cannot typecheck to `None`.
                            have hShadowFalse :
                                native_streq s sNested = false := by
                              cases hEq : native_streq s sNested
                              · rfl
                              · exact False.elim (hShadow hEq)
                            have hFieldEq :
                                smtx_dtc_field_substitute_type s
                                    (SmtDatatype.sum c dTail)
                                    (SmtType.Datatype sNested dNested) =
                                  SmtType.Datatype sNested
                                    (__smtx_dt_substitute s
                                      (SmtDatatype.sum c dTail) dNested) := by
                              simp [smtx_dtc_field_substitute_type,
                                hShadowFalse, native_ite]
                            have hFieldNotNone :
                                smtx_dtc_field_substitute_type s
                                    (SmtDatatype.sum c dTail)
                                    (SmtType.Datatype sNested dNested) ≠
                                  SmtType.None := by
                              rw [hFieldEq]
                              intro hNone
                              cases hNone
                            have hSubTypedAndCanon :
                                __smtx_typeof_value
                                      (__smtx_value_dt_substitute s
                                        (SmtDatatype.sum c dTail)
                                        (__smtx_type_default
                                          (SmtType.Datatype sNested dNested))) =
                                    smtx_dtc_field_substitute_type s
                                      (SmtDatatype.sum c dTail)
                                      (SmtType.Datatype sNested dNested) ∧
                                  __smtx_value_canonical
                                    (__smtx_value_dt_substitute s
                                      (SmtDatatype.sum c dTail)
                                      (__smtx_type_default
                                        (SmtType.Datatype sNested dNested))) := by
                              sorry
                            exact ⟨hSubTypedAndCanon.1, hFieldNotNone,
                              hSubTypedAndCanon.2⟩
                      exact
                        field_default_substitute_typed_canonical_with_datatype_bound
                          limit s (SmtDatatype.sum c dTail)
                          (native_reflist_insert native_reflist_nil s)
                          hDatatypeDefaults.1 hDatatypeDefaults.2
                          T hTLt hNotTypeRef hFieldInh hFieldRec)
                    cCur hCurSize hConsWf hNoTypeRef
              have hSmallTop :
                  ∀ a,
                    __smtx_typeof_value a =
                      SmtType.Datatype s (SmtDatatype.sum c dTail) ->
                      smt_value_size a < smt_value_size v' ->
                        datatype_default_has_typed_constructor_from s
                          (SmtDatatype.sum c dTail)
                          (SmtDatatype.sum c dTail) := by
                intro a hATy hASmall
                exact ih (smt_value_size a) (by omega) a rfl hATy
              have hScan :=
                datatype_default_has_typed_constructor_from_of_witness_scan
                  s (SmtDatatype.sum c dTail)
                  (native_reflist_insert native_reflist_nil s)
                  v' hv' hArgsNoTypeRef hSmallTop
                  (SmtDatatype.sum c dTail) native_nat_zero i
                  (datatype_suffix_at_self (SmtDatatype.sum c dTail))
                  (by simp [datatype_typeRef_prefix_at]) hDtWf
                  (by simpa using hHead)
              exact hScan
        exact hTypedBySize (smt_value_size v) v rfl hv
  exact datatype_type_default_typed_canonical_of_typed_constructor_from_self s d
    hTyped
termination_by sizeOf d
decreasing_by
  all_goals simp_wf
  all_goals try subst_vars
  all_goals try exact hDLt
  all_goals try exact hNestedDLt
  all_goals omega

private theorem type_default_typed_canonical_of_wf_rec_deferred_datatype :
    (T : SmtType) ->
      native_inhabited_type T = true ->
        __smtx_type_wf_rec T native_reflist_nil = true ->
          __smtx_typeof_value (__smtx_type_default T) = T ∧
            __smtx_value_canonical (__smtx_type_default T)
  | SmtType.None, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.Bool, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Int, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Real, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.RegLan, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, native_ite, native_and,
          native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total,
          native_nat_to_int, native_int_to_nat]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, native_ite, native_zleq, native_zeq,
          native_mod_total, native_int_pow2, native_zexp_total, native_nat_to_int]
  | SmtType.Map A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB := type_default_typed_canonical_of_wf_rec_deferred_datatype
        B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.Set A, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq, __smtx_typeof_value, __smtx_type_default]
  | SmtType.Seq A, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_seq_value,
        __smtx_value_canonical, __smtx_value_canonical_bool, __smtx_seq_canonical]
  | SmtType.Char, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Datatype s d, hInh, hRec => by
      exact datatype_type_default_typed_canonical_of_wf_rec_deferred s d hInh hRec
  | SmtType.TypeRef s, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.USort i, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.FunType A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB := type_default_typed_canonical_of_wf_rec_deferred_datatype
        B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_fun_type, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.DtcAppType A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
termination_by T _ _ => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals omega

private theorem non_datatype_type_default_substitute_typed_canonical_of_wf_rec_deferred
    (s : native_String)
    (d : SmtDatatype)
    (T : SmtType)
    (hDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d')
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T native_reflist_nil = true) :
    __smtx_typeof_value
        (__smtx_value_dt_substitute s d (__smtx_type_default T)) = T ∧
      __smtx_value_canonical
        (__smtx_value_dt_substitute s d (__smtx_type_default T)) := by
  have hEq :=
    value_dt_substitute_type_default_eq_of_not_datatype s d T hDatatype
  have hDef :=
    type_default_typed_canonical_of_wf_rec_deferred_datatype T hInh hRec
  constructor
  · simpa [hEq] using hDef.1
  · simpa [hEq] using hDef.2

private theorem type_wf_rec_nil_of_non_datatype_non_typeRef
    (T : SmtType)
    (refs : RefList)
    (hDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d')
    (hTypeRef : ∀ r, T ≠ SmtType.TypeRef r)
    (hRec : __smtx_type_wf_rec T refs = true) :
    __smtx_type_wf_rec T native_reflist_nil = true := by
  cases T <;> simp_all [__smtx_type_wf_rec]

private theorem non_datatype_non_typeRef_field_default_substitute_typed_canonical
    (s : native_String)
    (d : SmtDatatype)
    (refs : RefList)
    (T : SmtType)
    (hDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d')
    (hTypeRef : ∀ r, T ≠ SmtType.TypeRef r)
    (hInh : native_inhabited_type T = true)
    (hRec : __smtx_type_wf_rec T refs = true) :
    __smtx_typeof_value
        (__smtx_value_dt_substitute s d (__smtx_type_default T)) =
      smtx_dtc_field_substitute_type s d T ∧
    smtx_dtc_field_substitute_type s d T ≠ SmtType.None ∧
    __smtx_value_canonical
      (__smtx_value_dt_substitute s d (__smtx_type_default T)) := by
  have hRecNil :
      __smtx_type_wf_rec T native_reflist_nil = true :=
    type_wf_rec_nil_of_non_datatype_non_typeRef T refs hDatatype hTypeRef hRec
  have hDef :=
    non_datatype_type_default_substitute_typed_canonical_of_wf_rec_deferred
      s d T hDatatype hInh hRecNil
  have hField : smtx_dtc_field_substitute_type s d T = T := by
    cases T <;> simp_all [smtx_dtc_field_substitute_type, native_Teq,
      native_ite]
  have hTWF : __smtx_type_wf T = true :=
    type_wf_of_inhabited_and_wf_rec hInh hRecNil
  exact ⟨by rw [hField]; exact hDef.1,
    by rw [hField]; exact type_wf_non_none hTWF,
    hDef.2⟩

private theorem datatype_cons_default_args_typed_of_no_typeRef_with_datatype_defaults
    (s : native_String)
    (d0 : SmtDatatype)
    (refs : RefList)
    (hDatatypeField :
      ∀ sNested dNested,
        native_inhabited_type (SmtType.Datatype sNested dNested) = true ->
          __smtx_type_wf_rec (SmtType.Datatype sNested dNested) refs = true ->
            __smtx_typeof_value
                (__smtx_value_dt_substitute s d0
                  (__smtx_type_default (SmtType.Datatype sNested dNested))) =
              smtx_dtc_field_substitute_type s d0
                (SmtType.Datatype sNested dNested) ∧
            smtx_dtc_field_substitute_type s d0
                (SmtType.Datatype sNested dNested) ≠ SmtType.None ∧
            __smtx_value_canonical
              (__smtx_value_dt_substitute s d0
                (__smtx_type_default (SmtType.Datatype sNested dNested)))) :
    (c : SmtDatatypeCons) ->
      __smtx_dt_cons_wf_rec c refs = true ->
        ¬ datatype_cons_has_typeRef_field c ->
          datatype_cons_default_args_typed s d0 c := by
  apply datatype_cons_default_args_typed_of_no_typeRef_with_field_defaults
  intro T hNoTypeRef hInh hRec
  by_cases hDatatype : ∃ sNested dNested, T = SmtType.Datatype sNested dNested
  · rcases hDatatype with ⟨sNested, dNested, rfl⟩
    exact hDatatypeField sNested dNested hInh hRec
  · exact non_datatype_non_typeRef_field_default_substitute_typed_canonical
      s d0 refs T (by
        intro sNested dNested hEq
        exact hDatatype ⟨sNested, dNested, hEq⟩)
      hNoTypeRef hInh hRec

private theorem datatype_cons_default_args_typed_of_wf_rec_no_deferred
    (s : native_String)
    (d0 : SmtDatatype)
    (refs : RefList) :
    (c : SmtDatatypeCons) ->
      __smtx_dt_cons_wf_rec c refs = true ->
        datatype_cons_no_deferred_fields c ->
          datatype_cons_default_args_typed s d0 c
  | SmtDatatypeCons.unit, _hWF, _hNo => by
      simp [datatype_cons_default_args_typed]
  | SmtDatatypeCons.cons T c, hWF, hNo => by
      have hHead :=
        datatype_cons_head_wf_rec_nil_of_no_deferred (T := T) (c := c)
          (refs := refs) hWF hNo
      have hDef :=
        type_default_typed_canonical_of_wf_rec_deferred_datatype T hHead.1 hHead.2
      have hNoDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d' := by
        intro s' d' hEq
        subst T
        simp [datatype_cons_no_deferred_fields] at hNo
      have hSubEq :
          __smtx_value_dt_substitute s d0 (__smtx_type_default T) =
            __smtx_type_default T :=
        value_dt_substitute_type_default_eq_of_not_datatype s d0 T hNoDatatype
      have hField :
          smtx_dtc_field_substitute_type s d0 T = T :=
        dtc_field_substitute_type_eq_self_of_no_deferred s d0 hNo
      have hTWF : __smtx_type_wf T = true :=
        type_wf_of_inhabited_and_wf_rec hHead.1 hHead.2
      have hTailWF : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWF
      have hTailNo : datatype_cons_no_deferred_fields c := by
        cases T <;> simpa [datatype_cons_no_deferred_fields] using hNo
      have hTail :=
        datatype_cons_default_args_typed_of_wf_rec_no_deferred s d0 refs c
          hTailWF hTailNo
      simp [datatype_cons_default_args_typed]
      exact ⟨by rw [hSubEq, hField]; exact hDef.1,
        by rw [hField]; exact type_wf_non_none hTWF,
        by rw [hSubEq]; exact hDef.2, hTail⟩

private theorem datatype_cons_default_args_typed_of_wf_rec_simple
    (s : native_String)
    (d0 : SmtDatatype)
    (refs : RefList) :
    (c : SmtDatatypeCons) ->
      __smtx_dt_cons_wf_rec c refs = true ->
        datatype_cons_simple_defaultable_fields c ->
          datatype_cons_default_args_typed s d0 c
  | SmtDatatypeCons.unit, _hWF, _hSimple => by
      simp [datatype_cons_default_args_typed]
  | SmtDatatypeCons.cons T c, hWF, hSimple => by
      have hTailWF : __smtx_dt_cons_wf_rec c refs = true :=
        dt_cons_wf_rec_tail_of_true hWF
      by_cases hDatatype : ∃ sNested dNested, T = SmtType.Datatype sNested dNested
      · rcases hDatatype with ⟨sNested, dNested, rfl⟩
        cases dNested with
        | null =>
            simp [datatype_cons_simple_defaultable_fields] at hSimple
        | sum cNested dNestedTail =>
            cases cNested with
            | unit =>
                have hHead :=
                  value_dt_substitute_type_default_datatype_unit_args_typed
                    s d0 sNested dNestedTail
                have hTailSimple :
                    datatype_cons_simple_defaultable_fields c := by
                  simpa [datatype_cons_simple_defaultable_fields] using hSimple
                have hTail :=
                  datatype_cons_default_args_typed_of_wf_rec_simple s d0 refs
                    c hTailWF hTailSimple
                simpa [datatype_cons_default_args_typed] using
                  And.intro hHead.1
                    (And.intro hHead.2.1 (And.intro hHead.2.2 hTail))
            | cons TNested cNestedTail =>
                simp [datatype_cons_simple_defaultable_fields] at hSimple
      · by_cases hTypeRef : ∃ r, T = SmtType.TypeRef r
        · rcases hTypeRef with ⟨r, rfl⟩
          simp [datatype_cons_simple_defaultable_fields] at hSimple
        · have hHead :
              native_inhabited_type T = true ∧
                __smtx_type_wf_rec T native_reflist_nil = true := by
            cases T <;> simp_all [__smtx_dt_cons_wf_rec,
              __smtx_type_wf_rec, native_ite, native_and]
          have hDef :=
            type_default_typed_canonical_of_wf_rec_deferred_datatype T
              hHead.1 hHead.2
          have hNoDatatype : ∀ s' d', T ≠ SmtType.Datatype s' d' := by
            intro s' d' hEq
            exact hDatatype ⟨s', d', hEq⟩
          have hSubEq :
              __smtx_value_dt_substitute s d0 (__smtx_type_default T) =
                __smtx_type_default T :=
            value_dt_substitute_type_default_eq_of_not_datatype s d0 T
              hNoDatatype
          have hField : smtx_dtc_field_substitute_type s d0 T = T := by
            cases T <;> simp_all [smtx_dtc_field_substitute_type, native_Teq,
              native_ite]
          have hTWF : __smtx_type_wf T = true :=
            type_wf_of_inhabited_and_wf_rec hHead.1 hHead.2
          have hTailSimple : datatype_cons_simple_defaultable_fields c := by
            cases T <;> try
              simpa [datatype_cons_simple_defaultable_fields] using hSimple
            case Datatype sD dD =>
              exact False.elim (hDatatype ⟨sD, dD, rfl⟩)
          have hTail :=
            datatype_cons_default_args_typed_of_wf_rec_simple s d0 refs
              c hTailWF hTailSimple
          simp [datatype_cons_default_args_typed]
          exact ⟨by rw [hSubEq, hField]; exact hDef.1,
            by rw [hField]; exact type_wf_non_none hTWF,
            by rw [hSubEq]; exact hDef.2, hTail⟩

private theorem datatype_default_has_typed_constructor_from_of_wf_typeRef_prefix
    (s : native_String)
    (d0 : SmtDatatype)
    (refs : RefList) :
    (d : SmtDatatype) ->
      __smtx_dt_wf_rec d refs = true ->
        datatype_typeRef_prefix_to_no_deferred d ->
          datatype_default_has_typed_constructor_from s d0 d
  | SmtDatatype.null, _hWF, hShape => by
      simp [datatype_typeRef_prefix_to_no_deferred] at hShape
  | SmtDatatype.sum c dTail, hWF, hShape => by
      cases hShape with
      | inl hNoDeferred =>
          exact Or.inl
            (datatype_cons_default_args_typed_of_wf_rec_no_deferred s d0 refs
              c (dt_wf_cons_of_wf hWF) hNoDeferred)
      | inr hPrefix =>
          cases dTail with
          | null =>
              simp [datatype_typeRef_prefix_to_no_deferred] at hPrefix
          | sum cNext dRest =>
              have hTailWf :
                  __smtx_dt_wf_rec (SmtDatatype.sum cNext dRest) refs = true :=
                dt_wf_tail_of_nonempty_tail_wf
                  (c := c) (cTail := cNext) (dTail := dRest)
                  (refs := refs) hWF
              exact Or.inr ⟨hPrefix.1,
                datatype_default_has_typed_constructor_from_of_wf_typeRef_prefix
                  s d0 refs (SmtDatatype.sum cNext dRest) hTailWf hPrefix.2⟩

private theorem datatype_default_has_typed_constructor_from_of_wf_typeRef_prefix_simple
    (s : native_String)
    (d0 : SmtDatatype)
    (refs : RefList) :
    (d : SmtDatatype) ->
      __smtx_dt_wf_rec d refs = true ->
        datatype_typeRef_prefix_to_simple d ->
          datatype_default_has_typed_constructor_from s d0 d
  | SmtDatatype.null, _hWF, hShape => by
      simp [datatype_typeRef_prefix_to_simple] at hShape
  | SmtDatatype.sum c dTail, hWF, hShape => by
      cases hShape with
      | inl hSimple =>
          exact Or.inl
            (datatype_cons_default_args_typed_of_wf_rec_simple s d0 refs
              c (dt_wf_cons_of_wf hWF) hSimple)
      | inr hPrefix =>
          cases dTail with
          | null =>
              simp [datatype_typeRef_prefix_to_simple] at hPrefix
          | sum cNext dRest =>
              have hTailWf :
                  __smtx_dt_wf_rec (SmtDatatype.sum cNext dRest) refs = true :=
                dt_wf_tail_of_nonempty_tail_wf
                  (c := c) (cTail := cNext) (dTail := dRest)
                  (refs := refs) hWF
              exact Or.inr ⟨hPrefix.1,
                datatype_default_has_typed_constructor_from_of_wf_typeRef_prefix_simple
                  s d0 refs (SmtDatatype.sum cNext dRest) hTailWf hPrefix.2⟩

private theorem datatype_type_default_typed_canonical_of_wf_rec
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  cases d with
  | null =>
      simp [__smtx_type_wf_rec, __smtx_dt_wf_rec] at _hRec
  | sum c dTail =>
      by_cases hShapeSimple :
          datatype_typeRef_prefix_to_simple (SmtDatatype.sum c dTail)
      · have hDtWf :
            __smtx_dt_wf_rec (SmtDatatype.sum c dTail)
                (native_reflist_insert native_reflist_nil s) =
              true := by
          simpa [__smtx_type_wf_rec] using _hRec
        have hTypedFrom :=
          datatype_default_has_typed_constructor_from_of_wf_typeRef_prefix_simple s
            (SmtDatatype.sum c dTail)
            (native_reflist_insert native_reflist_nil s)
            (SmtDatatype.sum c dTail) hDtWf hShapeSimple
        have hDefault :=
          datatype_default_typed_canonical_of_typed_constructor_from s
            (SmtDatatype.sum c dTail) (SmtDatatype.sum c dTail)
            native_nat_zero
            (datatype_suffix_at_self (SmtDatatype.sum c dTail))
            hTypedFrom
        simpa [__smtx_type_default] using hDefault
      · by_cases hShape :
          datatype_typeRef_prefix_to_no_deferred (SmtDatatype.sum c dTail)
        · have hDtWf :
            __smtx_dt_wf_rec (SmtDatatype.sum c dTail)
                (native_reflist_insert native_reflist_nil s) =
              true := by
            simpa [__smtx_type_wf_rec] using _hRec
          have hTypedFrom :=
            datatype_default_has_typed_constructor_from_of_wf_typeRef_prefix s
              (SmtDatatype.sum c dTail)
              (native_reflist_insert native_reflist_nil s)
              (SmtDatatype.sum c dTail) hDtWf hShape
          have hDefault :=
            datatype_default_typed_canonical_of_typed_constructor_from s
              (SmtDatatype.sum c dTail) (SmtDatatype.sum c dTail)
              native_nat_zero
              (datatype_suffix_at_self (SmtDatatype.sum c dTail))
              hTypedFrom
          simpa [__smtx_type_default] using hDefault
        · cases c with
      | unit =>
          simp [__smtx_type_default, __smtx_datatype_default,
            __smtx_datatype_cons_default, __smtx_typeof_value,
            __smtx_dt_substitute, __smtx_dtc_substitute,
            __smtx_typeof_dt_cons_value_rec, __smtx_value_canonical,
            __smtx_value_canonical_bool, native_veq, native_not, native_ite]
      | cons T cTail =>
          cases cTail with
          | unit =>
              cases T with
              | None =>
                  have hCons :
                      __smtx_dt_cons_wf_rec
                          (SmtDatatypeCons.cons SmtType.None SmtDatatypeCons.unit)
                          (native_reflist_insert native_reflist_nil s) = true :=
                    dt_wf_cons_of_wf (d := dTail) (by
                      simpa [__smtx_type_wf_rec] using _hRec)
                  simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hCons
              | Bool =>
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_dt_substitute, __smtx_dtc_substitute,
                    __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
                    __smtx_typeof_guard, __smtx_value_canonical,
                    __smtx_value_canonical_bool, native_veq, native_not,
                    native_ite, native_Teq, native_and]
              | Int =>
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_dt_substitute, __smtx_dtc_substitute,
                    __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
                    __smtx_typeof_guard, __smtx_value_canonical,
                    __smtx_value_canonical_bool, native_veq, native_not,
                    native_ite, native_Teq, native_and]
              | Real =>
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_dt_substitute, __smtx_dtc_substitute,
                    __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
                    __smtx_typeof_guard, __smtx_value_canonical,
                    __smtx_value_canonical_bool, native_veq, native_not,
                    native_ite, native_Teq, native_and]
              | RegLan =>
                  have hCons :
                      __smtx_dt_cons_wf_rec
                          (SmtDatatypeCons.cons SmtType.RegLan SmtDatatypeCons.unit)
                          (native_reflist_insert native_reflist_nil s) = true :=
                    dt_wf_cons_of_wf (d := dTail) (by
                      simpa [__smtx_type_wf_rec] using _hRec)
                  simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hCons
              | BitVec w =>
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_dt_substitute, __smtx_dtc_substitute,
                    __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
                    __smtx_typeof_guard, __smtx_value_canonical,
                    __smtx_value_canonical_bool, native_veq, native_not,
                    native_ite, native_Teq, native_and, native_zleq,
                    native_zeq, native_mod_total, native_int_pow2,
                    native_zexp_total, native_nat_to_int, native_int_to_nat]
              | Map A B =>
                  have hCons :
                      __smtx_dt_cons_wf_rec
                          (SmtDatatypeCons.cons (SmtType.Map A B) SmtDatatypeCons.unit)
                          (native_reflist_insert native_reflist_nil s) = true :=
                    dt_wf_cons_of_wf (d := dTail) (by
                      simpa [__smtx_type_wf_rec] using _hRec)
                  have hTRefs :
                      native_inhabited_type (SmtType.Map A B) = true ∧
                        __smtx_type_wf_rec (SmtType.Map A B)
                          (native_reflist_insert native_reflist_nil s) = true := by
                    simpa [__smtx_dt_cons_wf_rec, native_ite] using hCons
                  have hT :
                      native_inhabited_type (SmtType.Map A B) = true ∧
                        __smtx_type_wf_rec (SmtType.Map A B) native_reflist_nil = true := by
                    exact ⟨hTRefs.1, by
                      simpa [__smtx_type_wf_rec] using hTRefs.2⟩
                  have hDef := type_default_typed_canonical_of_wf_rec_deferred_datatype
                    (SmtType.Map A B) hT.1 hT.2
                  have hTy :
                      __smtx_typeof_map_value (SmtMap.default A (__smtx_type_default B)) =
                        SmtType.Map A B := by
                    simpa [__smtx_type_default, __smtx_typeof_value] using hDef.1
                  have hCan :
                      __smtx_map_canonical (SmtMap.default A (__smtx_type_default B)) = true := by
                    simpa [__smtx_value_canonical] using hDef.2
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_dt_substitute, __smtx_dtc_substitute,
                    __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
                    __smtx_typeof_guard, __smtx_value_canonical,
                    __smtx_value_canonical_bool, native_veq, native_not,
                    native_ite, native_Teq, native_and, hTy, hCan]
              | Set A =>
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_typeof_map_value,
                    __smtx_map_to_set_type, __smtx_dt_substitute,
                    __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
                    __smtx_typeof_apply_value, __smtx_typeof_guard,
                    __smtx_value_canonical, __smtx_value_canonical_bool,
                    __smtx_map_canonical, __smtx_map_default_canonical,
                    native_veq, native_not, native_ite, native_Teq,
                    native_and]
              | Seq A =>
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_typeof_seq_value,
                    __smtx_dt_substitute, __smtx_dtc_substitute,
                    __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
                    __smtx_typeof_guard, __smtx_value_canonical,
                    __smtx_value_canonical_bool, __smtx_seq_canonical,
                    native_veq, native_not, native_ite, native_Teq,
                    native_and]
              | Char =>
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_dt_substitute, __smtx_dtc_substitute,
                    __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
                    __smtx_typeof_guard, __smtx_value_canonical,
                    __smtx_value_canonical_bool, native_veq, native_not,
                    native_ite, native_Teq, native_and]
              | USort i =>
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_dt_substitute, __smtx_dtc_substitute,
                    __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
                    __smtx_typeof_guard, __smtx_value_canonical,
                    __smtx_value_canonical_bool, native_veq, native_not,
                    native_ite, native_Teq, native_and]
              | FunType A B =>
                  have hCons :
                      __smtx_dt_cons_wf_rec
                          (SmtDatatypeCons.cons (SmtType.FunType A B) SmtDatatypeCons.unit)
                          (native_reflist_insert native_reflist_nil s) = true :=
                    dt_wf_cons_of_wf (d := dTail) (by
                      simpa [__smtx_type_wf_rec] using _hRec)
                  have hTRefs :
                      native_inhabited_type (SmtType.FunType A B) = true ∧
                        __smtx_type_wf_rec (SmtType.FunType A B)
                          (native_reflist_insert native_reflist_nil s) = true := by
                    simpa [__smtx_dt_cons_wf_rec, native_ite] using hCons
                  have hT :
                      native_inhabited_type (SmtType.FunType A B) = true ∧
                        __smtx_type_wf_rec (SmtType.FunType A B) native_reflist_nil = true := by
                    exact ⟨hTRefs.1, by
                      simpa [__smtx_type_wf_rec] using hTRefs.2⟩
                  have hDef := type_default_typed_canonical_of_wf_rec_deferred_datatype
                    (SmtType.FunType A B) hT.1 hT.2
                  have hTy :
                      __smtx_map_to_fun_type
                          (__smtx_typeof_map_value (SmtMap.default A (__smtx_type_default B))) =
                        SmtType.FunType A B := by
                    simpa [__smtx_type_default, __smtx_typeof_value] using hDef.1
                  have hCan :
                      __smtx_map_canonical (SmtMap.default A (__smtx_type_default B)) = true := by
                    simpa [__smtx_value_canonical] using hDef.2
                  simp [__smtx_type_default, __smtx_datatype_default,
                    __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                    __smtx_typeof_value, __smtx_dt_substitute, __smtx_dtc_substitute,
                    __smtx_typeof_dt_cons_value_rec, __smtx_typeof_apply_value,
                    __smtx_typeof_guard, __smtx_value_canonical,
                    __smtx_value_canonical_bool, native_veq, native_not,
                    native_ite, native_Teq, native_and, hTy, hCan]
              | DtcAppType A B =>
                  have hCons :
                      __smtx_dt_cons_wf_rec
                          (SmtDatatypeCons.cons (SmtType.DtcAppType A B) SmtDatatypeCons.unit)
                          (native_reflist_insert native_reflist_nil s) = true :=
                    dt_wf_cons_of_wf (d := dTail) (by
                      simpa [__smtx_type_wf_rec] using _hRec)
                  simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite] at hCons
              | Datatype sNested dNested =>
                  cases dNested with
                  | null =>
                      have hCons :
                          __smtx_dt_cons_wf_rec
                              (SmtDatatypeCons.cons
                                (SmtType.Datatype sNested SmtDatatype.null)
                                SmtDatatypeCons.unit)
                              (native_reflist_insert native_reflist_nil s) = true :=
                        dt_wf_cons_of_wf (d := dTail) (by
                          simpa [__smtx_type_wf_rec] using _hRec)
                      simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec,
                        __smtx_dt_wf_rec, native_ite] at hCons
                  | sum cNested dNestedTail =>
                      cases cNested with
                      | unit =>
                          cases hShadow : native_streq s sNested <;>
                            simp [__smtx_type_default, __smtx_datatype_default,
                              __smtx_datatype_cons_default, __smtx_value_dt_substitute,
                              __smtx_typeof_value, __smtx_dt_substitute,
                              __smtx_dtc_substitute, __smtx_typeof_dt_cons_value_rec,
                              __smtx_typeof_apply_value, __smtx_typeof_guard,
                              __smtx_value_canonical, __smtx_value_canonical_bool,
                              native_veq, native_not, native_ite, native_Teq,
                              native_and, hShadow]
                      | cons TNested cNestedTail =>
                          cases cNestedTail with
                          | unit =>
                              cases TNested with
                              | None =>
                                  have hOuterCons :
                                      __smtx_dt_cons_wf_rec
                                          (SmtDatatypeCons.cons
                                            (SmtType.Datatype sNested
                                              (SmtDatatype.sum
                                                (SmtDatatypeCons.cons SmtType.None
                                                  SmtDatatypeCons.unit)
                                                dNestedTail))
                                            SmtDatatypeCons.unit)
                                          (native_reflist_insert native_reflist_nil s) = true :=
                                    dt_wf_cons_of_wf (d := dTail) (by
                                      simpa [__smtx_type_wf_rec] using _hRec)
                                  have hNestedCons :=
                                    nested_datatype_field_head_wf_rec_of_cons_wf
                                      (sNested := sNested)
                                      (cNested := SmtDatatypeCons.cons SmtType.None
                                        SmtDatatypeCons.unit)
                                      (dNestedTail := dNestedTail)
                                      (cTail := SmtDatatypeCons.unit)
                                      (refs := native_reflist_insert native_reflist_nil s)
                                      hOuterCons
                                  simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec,
                                    native_ite] at hNestedCons
                              | Bool =>
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_dt_substitute, __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool, native_veq,
                                      native_not, native_ite, native_Teq, native_and,
                                      hShadow]
                              | Int =>
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_dt_substitute, __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool, native_veq,
                                      native_not, native_ite, native_Teq, native_and,
                                      hShadow]
                              | Real =>
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_dt_substitute, __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool, native_veq,
                                      native_not, native_ite, native_Teq, native_and,
                                      hShadow]
                              | BitVec w =>
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_dt_substitute, __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool, native_veq,
                                      native_not, native_ite, native_Teq, native_and,
                                      native_zleq, native_zeq, native_mod_total,
                                      native_int_pow2, native_zexp_total,
                                      native_nat_to_int, native_int_to_nat, hShadow]
                              | Map A B =>
                                  have hOuterCons :
                                      __smtx_dt_cons_wf_rec
                                          (SmtDatatypeCons.cons
                                            (SmtType.Datatype sNested
                                              (SmtDatatype.sum
                                                (SmtDatatypeCons.cons
                                                  (SmtType.Map A B)
                                                  SmtDatatypeCons.unit)
                                                dNestedTail))
                                            SmtDatatypeCons.unit)
                                          (native_reflist_insert native_reflist_nil s) = true :=
                                    dt_wf_cons_of_wf (d := dTail) (by
                                      simpa [__smtx_type_wf_rec] using _hRec)
                                  have hNestedParts :
                                      native_inhabited_type
                                            (SmtType.Datatype sNested
                                              (SmtDatatype.sum
                                                (SmtDatatypeCons.cons
                                                  (SmtType.Map A B)
                                                  SmtDatatypeCons.unit)
                                                dNestedTail)) = true ∧
                                        __smtx_type_wf_rec
                                            (SmtType.Datatype sNested
                                              (SmtDatatype.sum
                                                (SmtDatatypeCons.cons
                                                  (SmtType.Map A B)
                                                  SmtDatatypeCons.unit)
                                                dNestedTail))
                                            (native_reflist_insert native_reflist_nil s) =
                                          true := by
                                    simpa [__smtx_dt_cons_wf_rec, native_ite]
                                      using hOuterCons
                                  have hNestedWf :
                                      __smtx_dt_wf_rec
                                          (SmtDatatype.sum
                                            (SmtDatatypeCons.cons
                                              (SmtType.Map A B)
                                              SmtDatatypeCons.unit)
                                            dNestedTail)
                                          (native_reflist_insert
                                            (native_reflist_insert native_reflist_nil s)
                                            sNested) =
                                        true := by
                                    simpa [__smtx_type_wf_rec] using hNestedParts.2
                                  have hNestedCons :
                                      __smtx_dt_cons_wf_rec
                                          (SmtDatatypeCons.cons
                                            (SmtType.Map A B)
                                            SmtDatatypeCons.unit)
                                          (native_reflist_insert
                                            (native_reflist_insert native_reflist_nil s)
                                            sNested) =
                                        true :=
                                    dt_wf_cons_of_wf (d := dNestedTail) hNestedWf
                                  have hTRefs :
                                      native_inhabited_type (SmtType.Map A B) = true ∧
                                        __smtx_type_wf_rec (SmtType.Map A B)
                                          (native_reflist_insert
                                            (native_reflist_insert native_reflist_nil s)
                                            sNested) =
                                          true := by
                                    simpa [__smtx_dt_cons_wf_rec, native_ite]
                                      using hNestedCons
                                  have hT :
                                      native_inhabited_type (SmtType.Map A B) = true ∧
                                        __smtx_type_wf_rec (SmtType.Map A B)
                                          native_reflist_nil = true := by
                                    exact ⟨hTRefs.1, by
                                      simpa [__smtx_type_wf_rec] using hTRefs.2⟩
                                  have hDef :=
                                    type_default_typed_canonical_of_wf_rec_deferred_datatype
                                      (SmtType.Map A B) hT.1 hT.2
                                  have hTy :
                                      __smtx_typeof_map_value
                                          (SmtMap.default A (__smtx_type_default B)) =
                                        SmtType.Map A B := by
                                    simpa [__smtx_type_default, __smtx_typeof_value]
                                      using hDef.1
                                  have hBType :
                                      __smtx_typeof_value (__smtx_type_default B) = B := by
                                    have hMapEq :
                                        SmtType.Map A
                                            (__smtx_typeof_value (__smtx_type_default B)) =
                                          SmtType.Map A B := by
                                      simpa [__smtx_type_default, __smtx_typeof_value,
                                        __smtx_typeof_map_value] using hDef.1
                                    injection hMapEq with _ hB
                                  have hCan :
                                      __smtx_map_canonical
                                          (SmtMap.default A (__smtx_type_default B)) =
                                        true := by
                                    simpa [__smtx_value_canonical] using hDef.2
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_typeof_map_value, __smtx_dt_substitute,
                                      __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool,
                                      native_veq, native_not, native_ite,
                                      native_Teq, native_and, hTy, hCan, hBType,
                                      hShadow]
                              | RegLan =>
                                  have hOuterCons :
                                      __smtx_dt_cons_wf_rec
                                          (SmtDatatypeCons.cons
                                            (SmtType.Datatype sNested
                                              (SmtDatatype.sum
                                                (SmtDatatypeCons.cons SmtType.RegLan
                                                  SmtDatatypeCons.unit)
                                                dNestedTail))
                                            SmtDatatypeCons.unit)
                                          (native_reflist_insert native_reflist_nil s) = true :=
                                    dt_wf_cons_of_wf (d := dTail) (by
                                      simpa [__smtx_type_wf_rec] using _hRec)
                                  have hNestedCons :=
                                    nested_datatype_field_head_wf_rec_of_cons_wf
                                      (sNested := sNested)
                                      (cNested := SmtDatatypeCons.cons SmtType.RegLan
                                        SmtDatatypeCons.unit)
                                      (dNestedTail := dNestedTail)
                                      (cTail := SmtDatatypeCons.unit)
                                      (refs := native_reflist_insert native_reflist_nil s)
                                      hOuterCons
                                  simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec,
                                    native_ite] at hNestedCons
                              | Set A =>
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_typeof_map_value, __smtx_map_to_set_type,
                                      __smtx_dt_substitute, __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool,
                                      __smtx_map_canonical,
                                      __smtx_map_default_canonical, native_veq,
                                      native_not, native_ite, native_Teq, native_and,
                                      hShadow]
                              | Seq A =>
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_typeof_seq_value, __smtx_dt_substitute,
                                      __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool,
                                      __smtx_seq_canonical, native_veq, native_not,
                                      native_ite, native_Teq, native_and, hShadow]
                              | FunType A B =>
                                  have hOuterCons :
                                      __smtx_dt_cons_wf_rec
                                          (SmtDatatypeCons.cons
                                            (SmtType.Datatype sNested
                                              (SmtDatatype.sum
                                                (SmtDatatypeCons.cons
                                                  (SmtType.FunType A B)
                                                  SmtDatatypeCons.unit)
                                                dNestedTail))
                                            SmtDatatypeCons.unit)
                                          (native_reflist_insert native_reflist_nil s) = true :=
                                    dt_wf_cons_of_wf (d := dTail) (by
                                      simpa [__smtx_type_wf_rec] using _hRec)
                                  have hNestedParts :
                                      native_inhabited_type
                                            (SmtType.Datatype sNested
                                              (SmtDatatype.sum
                                                (SmtDatatypeCons.cons
                                                  (SmtType.FunType A B)
                                                  SmtDatatypeCons.unit)
                                                dNestedTail)) = true ∧
                                        __smtx_type_wf_rec
                                            (SmtType.Datatype sNested
                                              (SmtDatatype.sum
                                                (SmtDatatypeCons.cons
                                                  (SmtType.FunType A B)
                                                  SmtDatatypeCons.unit)
                                                dNestedTail))
                                            (native_reflist_insert native_reflist_nil s) =
                                          true := by
                                    simpa [__smtx_dt_cons_wf_rec, native_ite]
                                      using hOuterCons
                                  have hNestedWf :
                                      __smtx_dt_wf_rec
                                          (SmtDatatype.sum
                                            (SmtDatatypeCons.cons
                                              (SmtType.FunType A B)
                                              SmtDatatypeCons.unit)
                                            dNestedTail)
                                          (native_reflist_insert
                                            (native_reflist_insert native_reflist_nil s)
                                            sNested) =
                                        true := by
                                    simpa [__smtx_type_wf_rec] using hNestedParts.2
                                  have hNestedCons :
                                      __smtx_dt_cons_wf_rec
                                          (SmtDatatypeCons.cons
                                            (SmtType.FunType A B)
                                            SmtDatatypeCons.unit)
                                          (native_reflist_insert
                                            (native_reflist_insert native_reflist_nil s)
                                            sNested) =
                                        true :=
                                    dt_wf_cons_of_wf (d := dNestedTail) hNestedWf
                                  have hTRefs :
                                      native_inhabited_type (SmtType.FunType A B) = true ∧
                                        __smtx_type_wf_rec (SmtType.FunType A B)
                                          (native_reflist_insert
                                            (native_reflist_insert native_reflist_nil s)
                                            sNested) =
                                          true := by
                                    simpa [__smtx_dt_cons_wf_rec, native_ite]
                                      using hNestedCons
                                  have hT :
                                      native_inhabited_type (SmtType.FunType A B) = true ∧
                                        __smtx_type_wf_rec (SmtType.FunType A B)
                                          native_reflist_nil = true := by
                                    exact ⟨hTRefs.1, by
                                      simpa [__smtx_type_wf_rec] using hTRefs.2⟩
                                  have hDef :=
                                    type_default_typed_canonical_of_wf_rec_deferred_datatype
                                      (SmtType.FunType A B) hT.1 hT.2
                                  have hTy :
                                      __smtx_map_to_fun_type
                                          (__smtx_typeof_map_value
                                            (SmtMap.default A (__smtx_type_default B))) =
                                        SmtType.FunType A B := by
                                    simpa [__smtx_type_default, __smtx_typeof_value]
                                      using hDef.1
                                  have hBType :
                                      __smtx_typeof_value (__smtx_type_default B) = B := by
                                    have hFunEq :
                                        SmtType.FunType A
                                            (__smtx_typeof_value (__smtx_type_default B)) =
                                          SmtType.FunType A B := by
                                      simpa [__smtx_type_default, __smtx_typeof_value,
                                        __smtx_typeof_map_value, __smtx_map_to_fun_type]
                                        using hDef.1
                                    injection hFunEq with _ hB
                                  have hCan :
                                      __smtx_map_canonical
                                          (SmtMap.default A (__smtx_type_default B)) =
                                        true := by
                                    simpa [__smtx_value_canonical] using hDef.2
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_typeof_map_value,
                                      __smtx_map_to_fun_type, __smtx_dt_substitute,
                                      __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool,
                                      native_veq, native_not, native_ite,
                                      native_Teq, native_and, hTy, hCan, hBType,
                                      hShadow]
                              | Char =>
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_dt_substitute, __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool, native_veq,
                                      native_not, native_ite, native_Teq, native_and,
                                      hShadow]
                              | USort i =>
                                  cases hShadow : native_streq s sNested <;>
                                    simp [__smtx_type_default, __smtx_datatype_default,
                                      __smtx_datatype_cons_default,
                                      __smtx_value_dt_substitute,
                                      __smtx_value_dt_substitute_apply,
                                      __vsm_apply_head, __smtx_typeof_value,
                                      __smtx_dt_substitute, __smtx_dtc_substitute,
                                      __smtx_typeof_dt_cons_value_rec,
                                      __smtx_typeof_apply_value, __smtx_typeof_guard,
                                      __smtx_value_canonical,
                                      __smtx_value_canonical_bool, native_veq,
                                      native_not, native_ite, native_Teq, native_and,
                                      hShadow]
                              | DtcAppType A B =>
                                  have hOuterCons :
                                      __smtx_dt_cons_wf_rec
                                          (SmtDatatypeCons.cons
                                            (SmtType.Datatype sNested
                                              (SmtDatatype.sum
                                                (SmtDatatypeCons.cons
                                                  (SmtType.DtcAppType A B)
                                                  SmtDatatypeCons.unit)
                                                dNestedTail))
                                            SmtDatatypeCons.unit)
                                          (native_reflist_insert native_reflist_nil s) = true :=
                                    dt_wf_cons_of_wf (d := dTail) (by
                                      simpa [__smtx_type_wf_rec] using _hRec)
                                  have hNestedCons :=
                                    nested_datatype_field_head_wf_rec_of_cons_wf
                                      (sNested := sNested)
                                      (cNested := SmtDatatypeCons.cons
                                        (SmtType.DtcAppType A B) SmtDatatypeCons.unit)
                                      (dNestedTail := dNestedTail)
                                      (cTail := SmtDatatypeCons.unit)
                                      (refs := native_reflist_insert native_reflist_nil s)
                                      hOuterCons
                                  simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec,
                                    native_ite] at hNestedCons
                              | Datatype sDeep dDeep =>
                                  cases dDeep with
                                  | null =>
                                      have hOuterCons :
                                          __smtx_dt_cons_wf_rec
                                              (SmtDatatypeCons.cons
                                                (SmtType.Datatype sNested
                                                  (SmtDatatype.sum
                                                    (SmtDatatypeCons.cons
                                                      (SmtType.Datatype sDeep
                                                        SmtDatatype.null)
                                                      SmtDatatypeCons.unit)
                                                    dNestedTail))
                                                SmtDatatypeCons.unit)
                                              (native_reflist_insert
                                                native_reflist_nil s) = true :=
                                        dt_wf_cons_of_wf (d := dTail) (by
                                          simpa [__smtx_type_wf_rec] using _hRec)
                                      have hNestedCons :=
                                        nested_datatype_field_head_wf_rec_of_cons_wf
                                          (sNested := sNested)
                                          (cNested := SmtDatatypeCons.cons
                                            (SmtType.Datatype sDeep SmtDatatype.null)
                                            SmtDatatypeCons.unit)
                                          (dNestedTail := dNestedTail)
                                          (cTail := SmtDatatypeCons.unit)
                                          (refs := native_reflist_insert native_reflist_nil s)
                                          hOuterCons
                                      exact False.elim
                                        (dt_cons_wf_rec_false_of_has_datatype_null_field
                                          (SmtDatatypeCons.cons
                                            (SmtType.Datatype sDeep SmtDatatype.null)
                                            SmtDatatypeCons.unit)
                                          (by simp [datatype_cons_has_datatype_null_field])
                                          hNestedCons)
                                  | sum cDeep dDeepTail =>
                                      exact datatype_type_default_typed_canonical_of_wf_rec_deferred s
                                        _ _hInh _hRec
                              | _ =>
                                  exact datatype_type_default_typed_canonical_of_wf_rec_deferred s
                                    _ _hInh _hRec
                          | cons _ _ =>
                              exact datatype_type_default_typed_canonical_of_wf_rec_deferred s
                                _ _hInh _hRec
              | TypeRef r =>
                  have hHeadCons :
                      __smtx_dt_cons_wf_rec
                          (SmtDatatypeCons.cons (SmtType.TypeRef r)
                            SmtDatatypeCons.unit)
                          (native_reflist_insert native_reflist_nil s) = true :=
                    dt_wf_cons_of_wf (d := dTail) (by
                      simpa [__smtx_type_wf_rec] using _hRec)
                  have hSelf : r = s :=
                    typeRef_singleton_cons_wf_eq hHeadCons
                  subst r
                  cases dTail with
                  | null =>
                      -- A datatype with only its recursive constructor is
                      -- ruled out by semantic inhabitation, but that is part
                      -- of the remaining productivity proof.
                      exact datatype_type_default_typed_canonical_of_wf_rec_deferred s
                        _ _hInh _hRec
                  | sum cNext dRest =>
                      by_cases hNoDeferred :
                          datatype_cons_no_deferred_fields cNext
                      · let d0 :=
                            SmtDatatype.sum
                              (SmtDatatypeCons.cons (SmtType.TypeRef s)
                                SmtDatatypeCons.unit)
                              (SmtDatatype.sum cNext dRest)
                        have hFirst :
                            __smtx_datatype_cons_default s d0
                                (SmtValue.DtCons s d0 native_nat_zero)
                                (SmtDatatypeCons.cons (SmtType.TypeRef s)
                                  SmtDatatypeCons.unit) =
                              SmtValue.NotValue := by
                          simp [d0, __smtx_datatype_cons_default,
                            __smtx_type_default, __smtx_value_dt_substitute,
                            native_veq, native_ite]
                        have hTailWf :
                            __smtx_dt_wf_rec (SmtDatatype.sum cNext dRest)
                                (native_reflist_insert native_reflist_nil s) =
                              true :=
                          dt_wf_tail_of_nonempty_tail_wf
                            (c := SmtDatatypeCons.cons (SmtType.TypeRef s)
                              SmtDatatypeCons.unit)
                            (cTail := cNext)
                            (dTail := dRest)
                            (refs := native_reflist_insert native_reflist_nil s)
                            (by simpa [__smtx_type_wf_rec] using _hRec)
                        have hNextWf :
                            __smtx_dt_cons_wf_rec cNext
                                (native_reflist_insert native_reflist_nil s) =
                              true :=
                          dt_wf_cons_of_wf (d := dRest) hTailWf
                        have hArgs :
                            datatype_cons_default_args_typed s d0 cNext :=
                          datatype_cons_default_args_typed_of_wf_rec_no_deferred s
                            d0 (native_reflist_insert native_reflist_nil s)
                            cNext hNextWf hNoDeferred
                        exact
                          datatype_default_typed_canonical_of_second_args_typed s
                            (SmtDatatypeCons.cons (SmtType.TypeRef s)
                              SmtDatatypeCons.unit)
                            cNext dRest hFirst hArgs
                      · by_cases hNextSimple :
                            datatype_cons_simple_defaultable_fields cNext
                        · have hPrefix :
                              datatype_typeRef_prefix_to_simple
                                (SmtDatatype.sum
                                  (SmtDatatypeCons.cons (SmtType.TypeRef s)
                                    SmtDatatypeCons.unit)
                                  (SmtDatatype.sum cNext dRest)) := by
                            exact Or.inr ⟨by
                              simp [datatype_cons_has_typeRef_field],
                              Or.inl hNextSimple⟩
                          exact False.elim (hShapeSimple hPrefix)
                        · exact datatype_type_default_typed_canonical_of_wf_rec_deferred s
                            _ _hInh _hRec
          | cons U cRest =>
              by_cases hSimple :
                  datatype_cons_simple_defaultable_fields
                    (SmtDatatypeCons.cons T
                      (SmtDatatypeCons.cons U cRest))
              · have hCons :
                    __smtx_dt_cons_wf_rec
                        (SmtDatatypeCons.cons T
                          (SmtDatatypeCons.cons U cRest))
                        (native_reflist_insert native_reflist_nil s) = true :=
                  dt_wf_cons_of_wf (d := dTail) (by
                    simpa [__smtx_type_wf_rec] using _hRec)
                have hArgs :
                    datatype_cons_default_args_typed s
                        (SmtDatatype.sum
                          (SmtDatatypeCons.cons T
                            (SmtDatatypeCons.cons U cRest))
                          dTail)
                        (SmtDatatypeCons.cons T
                          (SmtDatatypeCons.cons U cRest)) :=
                  datatype_cons_default_args_typed_of_wf_rec_simple s
                    (SmtDatatype.sum
                      (SmtDatatypeCons.cons T
                        (SmtDatatypeCons.cons U cRest))
                      dTail)
                    (native_reflist_insert native_reflist_nil s)
                    (SmtDatatypeCons.cons T
                      (SmtDatatypeCons.cons U cRest))
                    hCons hSimple
                exact datatype_default_typed_canonical_of_first_args_typed s
                  (SmtDatatypeCons.cons T (SmtDatatypeCons.cons U cRest))
                  dTail hArgs
              · by_cases hNoDeferred :
                  datatype_cons_no_deferred_fields
                    (SmtDatatypeCons.cons T
                      (SmtDatatypeCons.cons U cRest))
                · have hCons :
                      __smtx_dt_cons_wf_rec
                          (SmtDatatypeCons.cons T
                            (SmtDatatypeCons.cons U cRest))
                          (native_reflist_insert native_reflist_nil s) = true :=
                    dt_wf_cons_of_wf (d := dTail) (by
                      simpa [__smtx_type_wf_rec] using _hRec)
                  have hArgs :
                      datatype_cons_default_args_typed s
                          (SmtDatatype.sum
                            (SmtDatatypeCons.cons T
                              (SmtDatatypeCons.cons U cRest))
                            dTail)
                          (SmtDatatypeCons.cons T
                            (SmtDatatypeCons.cons U cRest)) :=
                    datatype_cons_default_args_typed_of_wf_rec_no_deferred s
                      (SmtDatatype.sum
                        (SmtDatatypeCons.cons T
                          (SmtDatatypeCons.cons U cRest))
                        dTail)
                      (native_reflist_insert native_reflist_nil s)
                      (SmtDatatypeCons.cons T
                        (SmtDatatypeCons.cons U cRest))
                      hCons hNoDeferred
                  exact datatype_default_typed_canonical_of_first_args_typed s
                    (SmtDatatypeCons.cons T (SmtDatatypeCons.cons U cRest))
                    dTail hArgs
                · by_cases hHasTypeRef :
                    datatype_cons_has_typeRef_field
                      (SmtDatatypeCons.cons T
                        (SmtDatatypeCons.cons U cRest))
                  · cases dTail with
                    | null =>
                        by_cases hHasNull :
                            datatype_cons_has_datatype_null_field
                              (SmtDatatypeCons.cons T
                                (SmtDatatypeCons.cons U cRest))
                        · have hCons :
                              __smtx_dt_cons_wf_rec
                                  (SmtDatatypeCons.cons T
                                    (SmtDatatypeCons.cons U cRest))
                                  (native_reflist_insert native_reflist_nil s) = true :=
                            dt_wf_cons_of_wf (d := SmtDatatype.null) (by
                              simpa [__smtx_type_wf_rec] using _hRec)
                          exact False.elim
                            (dt_cons_wf_rec_false_of_has_datatype_null_field
                              (SmtDatatypeCons.cons T
                                (SmtDatatypeCons.cons U cRest))
                              hHasNull hCons)
                        · exact datatype_type_default_typed_canonical_of_wf_rec_deferred s
                            _ _hInh _hRec
                    | sum cNext dRest =>
                        by_cases hNextNoDeferred :
                            datatype_cons_no_deferred_fields cNext
                        · let c0 :=
                              SmtDatatypeCons.cons T
                                (SmtDatatypeCons.cons U cRest)
                          let d0 := SmtDatatype.sum c0 (SmtDatatype.sum cNext dRest)
                          have hFirst :
                              __smtx_datatype_cons_default s d0
                                  (SmtValue.DtCons s d0 native_nat_zero) c0 =
                                SmtValue.NotValue :=
                            datatype_cons_default_eq_notValue_of_has_typeRef_field
                              s d0 (SmtValue.DtCons s d0 native_nat_zero) c0
                              hHasTypeRef
                          have hTailWf :
                              __smtx_dt_wf_rec (SmtDatatype.sum cNext dRest)
                                  (native_reflist_insert native_reflist_nil s) =
                                true :=
                            dt_wf_tail_of_nonempty_tail_wf
                              (c := SmtDatatypeCons.cons T
                                (SmtDatatypeCons.cons U cRest))
                              (cTail := cNext)
                              (dTail := dRest)
                              (refs := native_reflist_insert native_reflist_nil s)
                              (by simpa [__smtx_type_wf_rec] using _hRec)
                          have hNextWf :
                              __smtx_dt_cons_wf_rec cNext
                                  (native_reflist_insert native_reflist_nil s) =
                                true :=
                            dt_wf_cons_of_wf (d := dRest) hTailWf
                          have hArgs :
                              datatype_cons_default_args_typed s d0 cNext :=
                            datatype_cons_default_args_typed_of_wf_rec_no_deferred s
                              d0 (native_reflist_insert native_reflist_nil s)
                              cNext hNextWf hNextNoDeferred
                          exact
                            datatype_default_typed_canonical_of_second_args_typed s
                              c0 cNext dRest hFirst hArgs
                        · by_cases hNextSimple :
                              datatype_cons_simple_defaultable_fields cNext
                          · have hPrefix :
                                datatype_typeRef_prefix_to_simple
                                  (SmtDatatype.sum
                                    (SmtDatatypeCons.cons T
                                      (SmtDatatypeCons.cons U cRest))
                                    (SmtDatatype.sum cNext dRest)) := by
                              exact Or.inr ⟨hHasTypeRef, Or.inl hNextSimple⟩
                            exact False.elim (hShapeSimple hPrefix)
                          · exact datatype_type_default_typed_canonical_of_wf_rec_deferred s
                              _ _hInh _hRec
                  · -- The remaining multi-argument cases contain a nested
                    -- datatype field but no direct `TypeRef`; they still need
                    -- the semantic descent/productivity argument for nested
                    -- defaults.
                    by_cases hHasNull :
                        datatype_cons_has_datatype_null_field
                          (SmtDatatypeCons.cons T
                            (SmtDatatypeCons.cons U cRest))
                    · have hCons :
                          __smtx_dt_cons_wf_rec
                              (SmtDatatypeCons.cons T
                                (SmtDatatypeCons.cons U cRest))
                              (native_reflist_insert native_reflist_nil s) = true :=
                        dt_wf_cons_of_wf (d := dTail) (by
                          simpa [__smtx_type_wf_rec] using _hRec)
                      exact False.elim
                        (dt_cons_wf_rec_false_of_has_datatype_null_field
                          (SmtDatatypeCons.cons T
                            (SmtDatatypeCons.cons U cRest))
                          hHasNull hCons)
                    · exact datatype_type_default_typed_canonical_of_wf_rec_deferred s
                        _ _hInh _hRec

private theorem type_default_typed_canonical_of_wf_rec :
    (T : SmtType) ->
      native_inhabited_type T = true ->
        __smtx_type_wf_rec T native_reflist_nil = true ->
          __smtx_typeof_value (__smtx_type_default T) = T ∧
            __smtx_value_canonical (__smtx_type_default T)
  | SmtType.None, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.Bool, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Int, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Real, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.RegLan, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, native_ite, native_and,
          native_zleq, native_zeq, native_mod_total, native_int_pow2, native_zexp_total,
          native_nat_to_int, native_int_to_nat]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, native_ite, native_zleq, native_zeq,
          native_mod_total, native_int_pow2, native_zexp_total, native_nat_to_int]
  | SmtType.Map A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB := type_default_typed_canonical_of_wf_rec B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.Set A, _hInh, _hRec => by
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq, __smtx_typeof_value, __smtx_type_default]
  | SmtType.Seq A, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_seq_value,
        __smtx_value_canonical, __smtx_value_canonical_bool, __smtx_seq_canonical]
  | SmtType.Char, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.Datatype s d, hInh, hRec => by
      exact datatype_type_default_typed_canonical_of_wf_rec s d hInh hRec
  | SmtType.TypeRef s, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.USort i, _hInh, _hRec => by
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  | SmtType.FunType A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec, native_and] at hRec
      have hB := type_default_typed_canonical_of_wf_rec B hRec.2.2.1 hRec.2.2.2
      have hBCanon :
          __smtx_value_canonical_bool (__smtx_type_default B) = true := by
        simpa [__smtx_value_canonical] using hB.2
      constructor
      · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_fun_type, hB.1]
      · simp [__smtx_type_default, __smtx_value_canonical,
          __smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, native_and, hB.1, hBCanon]
        cases hFin : __smtx_is_finite_type A <;>
          simp [native_ite, native_veq]
  | SmtType.DtcAppType A B, _hInh, hRec => by
      simp [__smtx_type_wf_rec] at hRec
termination_by T _ _ => sizeOf T
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Every well-formed Mini SMT type has a canonical inhabitant. -/
theorem canonical_type_inhabited_of_type_wf
    (T : SmtType)
    (hWF : __smtx_type_wf T = true) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical v := by
  by_cases hReg : T = SmtType.RegLan
  · subst T
    exact ⟨SmtValue.RegLan native_re_none, rfl, by
      simp [__smtx_value_canonical, __smtx_value_canonical_bool]⟩
  · have hParts :
        native_inhabited_type T = true ∧
          __smtx_type_wf_rec T native_reflist_nil = true := by
      cases T <;> simp [__smtx_type_wf, __smtx_type_wf_rec, native_and] at hWF hReg ⊢ <;>
        exact hWF
    have hDef :=
      type_default_typed_canonical_of_wf_rec T hParts.1 hParts.2
    exact ⟨__smtx_type_default T, hDef.1, hDef.2⟩

/-- Choice-based model that returns a canonical inhabitant for every well-formed SMT type. -/
noncomputable def default_typed_model : SmtModel := by
  classical
  exact fun k =>
    if h : __smtx_type_wf k.ty = true then
      some (Classical.choose (canonical_type_inhabited_of_type_wf k.ty h))
    else
      none

end Smtm
