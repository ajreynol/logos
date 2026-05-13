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

private def datatype_cons_has_datatype_null_field : SmtDatatypeCons -> Prop
  | SmtDatatypeCons.unit => False
  | SmtDatatypeCons.cons (SmtType.Datatype _ SmtDatatype.null) _ => True
  | SmtDatatypeCons.cons _ c => datatype_cons_has_datatype_null_field c

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

private def datatype_default_has_typed_constructor_from
    (s : native_String)
    (d0 : SmtDatatype) :
    SmtDatatype -> Prop
  | SmtDatatype.null => False
  | SmtDatatype.sum c d =>
      datatype_cons_default_args_typed s d0 c ∨
        datatype_cons_has_typeRef_field c ∧
          datatype_default_has_typed_constructor_from s d0 d

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

private theorem datatype_type_default_typed_canonical_of_wf_rec_deferred
    (s : native_String)
    (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true) :
    __smtx_typeof_value (__smtx_type_default (SmtType.Datatype s d)) =
        SmtType.Datatype s d ∧
      __smtx_value_canonical (__smtx_type_default (SmtType.Datatype s d)) := by
  -- Central remaining generated-default completeness fact.
  sorry

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
                  cases dTail with
                  | null =>
                      -- A datatype with only a recursive constructor is
                      -- ruled out by semantic inhabitation, but that is part
                      -- of the remaining productivity proof.
                      exact datatype_type_default_typed_canonical_of_wf_rec_deferred s
                        _ _hInh _hRec
                  | sum cNext dRest =>
                      by_cases hNoDeferred :
                          datatype_cons_no_deferred_fields cNext
                      · let d0 :=
                            SmtDatatype.sum
                              (SmtDatatypeCons.cons (SmtType.TypeRef r)
                                SmtDatatypeCons.unit)
                              (SmtDatatype.sum cNext dRest)
                        have hFirst :
                            __smtx_datatype_cons_default s d0
                                (SmtValue.DtCons s d0 native_nat_zero)
                                (SmtDatatypeCons.cons (SmtType.TypeRef r)
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
                            (c := SmtDatatypeCons.cons (SmtType.TypeRef r)
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
                            (SmtDatatypeCons.cons (SmtType.TypeRef r)
                              SmtDatatypeCons.unit)
                            cNext dRest hFirst hArgs
                      · by_cases hNextSimple :
                            datatype_cons_simple_defaultable_fields cNext
                        · have hPrefix :
                              datatype_typeRef_prefix_to_simple
                                (SmtDatatype.sum
                                  (SmtDatatypeCons.cons (SmtType.TypeRef r)
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
