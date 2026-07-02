import Cpc.Proofs.Translation.Base

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

attribute [local simp] native_ite
attribute [local simp] native_streq
attribute [local simp] native_and

@[simp] private theorem guarded_datatype_type_ne_bool
    (s : native_String) (d : SmtDatatype) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Bool := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_bool
    (s : native_String) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Bool := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_int
    (s : native_String) (d : SmtDatatype) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Int := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_int
    (s : native_String) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Int := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_real
    (s : native_String) (d : SmtDatatype) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Real := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_real
    (s : native_String) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Real := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_reglan
    (s : native_String) (d : SmtDatatype) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.RegLan := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_reglan
    (s : native_String) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.RegLan := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_char
    (s : native_String) (d : SmtDatatype) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Char := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_char
    (s : native_String) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Char := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_bitvec
    (s : native_String) (d : SmtDatatype) (w : native_Nat) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.BitVec w := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_bitvec
    (s : native_String) (w : native_Nat) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.BitVec w := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_seq
    (s : native_String) (d : SmtDatatype) (A : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Seq A := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_seq
    (s : native_String) (A : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Seq A := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_set
    (s : native_String) (d : SmtDatatype) (A : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Set A := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_set
    (s : native_String) (A : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Set A := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_map
    (s : native_String) (d : SmtDatatype) (A B : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.Map A B := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_map
    (s : native_String) (A B : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Map A B := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_fun
    (s : native_String) (d : SmtDatatype) (A B : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.FunType A B := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_fun
    (s : native_String) (A B : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.FunType A B := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_ifun
    (s : native_String) (d : SmtDatatype) (A B : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.FunType A B := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_ifun
    (s : native_String) (A B : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.FunType A B := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_dtc_app
    (s : native_String) (d : SmtDatatype) (A B : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.DtcAppType A B := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_dtc_app
    (s : native_String) (A B : SmtType) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.DtcAppType A B := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_typeref
    (s r : native_String) (d : SmtDatatype) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.TypeRef r := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_datatype
    (s r : native_String) (d : SmtDatatype) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.Datatype r d := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_datatype_type_ne_usort
    (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.Datatype s d) ≠
      SmtType.USort i := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem guarded_typeref_type_ne_usort
    (s : native_String) (i : native_Nat) :
    (if native_reserved_datatype_name s = true then SmtType.None else SmtType.TypeRef s) ≠
      SmtType.USort i := by
  by_cases h : native_reserved_datatype_name s = true <;> simp [h]

@[simp] private theorem smt_fun_choice_if_ne_none
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.None := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_bool
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Bool := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_int
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Int := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_real
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Real := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_reglan
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.RegLan := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_char
    (T U : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Char := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_bitvec
    (T U : SmtType) (w : native_Nat) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.BitVec w := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_seq
    (T U A : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Seq A := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_set
    (T U A : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Set A := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_map
    (T U A B : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Map A B := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_typeref
    (T U : SmtType) (s : native_String) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.TypeRef s := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatype) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.Datatype s d := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_dtc_app
    (T U A B : SmtType) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.DtcAppType A B := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

@[simp] private theorem smt_fun_choice_if_ne_usort
    (T U : SmtType) (i : native_Nat) :
    (if __smtx_is_finite_type (SmtType.FunType T U) = true then SmtType.FunType T U else SmtType.FunType T U) ≠
      SmtType.USort i := by
  by_cases hFin : __smtx_is_finite_type (SmtType.FunType T U) = true <;> simp [hFin]

/-- Field well-formedness for a `Datatype s d` occurring at a field position. Under the new
(reflist-free) `__smtx_type_wf` algorithm, a nested `Datatype s d` occurrence is checked
*independently* of any enclosing context via the diagonal self-check `wf_rec (Datatype s d)
(Datatype s d)`, which unfolds to `dt_wf_rec (dt_substitute s d d) d`. There is no longer an
"`s` not already in scope" (no-aliasing) conjunct to extract — aliasing is permitted. -/
private theorem smtx_datatype_type_wf_rec_parts
    {s : native_String} {d : SmtDatatype}
    (h : __smtx_type_wf_rec (SmtType.Datatype s d) (SmtType.Datatype s d) = true) :
    __smtx_dt_wf_rec (__smtx_dt_substitute s d d) d = true := by
  simpa [__smtx_type_wf_rec] using h

/-- Well-formedness of a type occurring at a *field* position (a datatype-constructor field,
function argument, sequence/set/map element, …). Under the new algorithm this is exactly the
diagonal self-check `__smtx_type_wf_rec T T`; the ambient `refs` parameter is now vestigial
(kept only so existing call sites, many of which threaded a `RefList` that no longer carries any
scoping information, continue to type-check). -/
def smtx_type_field_wf_rec (T : SmtType) (_refs : RefList) : Prop :=
  __smtx_type_wf_rec T T = true

private theorem smtx_datatype_field_wf_rec_parts
    {s : native_String} {d : SmtDatatype} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.Datatype s d) refs) :
    __smtx_dt_wf_rec (__smtx_dt_substitute s d d) d = true :=
  smtx_datatype_type_wf_rec_parts (by
    simpa [smtx_type_field_wf_rec] using h)

theorem smtx_type_field_wf_rec_of_type_wf_rec
    {T : SmtType} {refs : RefList}
    (h : __smtx_type_wf_rec T T = true) :
    smtx_type_field_wf_rec T refs :=
  h

/-- Field well-formedness excludes `RegLan` at field/function-argument positions. -/
theorem smtx_type_field_wf_rec_ne_reglan
    {T : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec T refs) :
    T ≠ SmtType.RegLan := by
  intro hReg
  subst hReg
  simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at h

/-- Extracts field well-formedness for a non-`TypeRef` head field from a well-formed constructor
whose full (substituted) side agrees with the raw head field (i.e. substitution was a no-op on it,
as it always is at non-`TypeRef` field positions since `__smtx_type_substitute` only ever rewrites a
bare `TypeRef` matching the substituted name). -/
theorem smtx_type_field_wf_rec_of_cons_wf
    {T : SmtType} {c : SmtDatatypeCons} {refs : RefList}
    (hNotRef : ∀ s, T ≠ SmtType.TypeRef s)
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) (SmtDatatypeCons.cons T c) = true) :
    smtx_type_field_wf_rec T refs := by
  simp only [smtx_type_field_wf_rec]
  have hgen : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c) (SmtDatatypeCons.cons T c) =
      native_ite (native_and (native_inhabited_type T) (__smtx_type_wf_rec T T))
        (__smtx_dt_cons_wf_rec c c) false := by
    cases T with
    | TypeRef s => exact absurd rfl (hNotRef s)
    | _ => simp [__smtx_dt_cons_wf_rec]
  rw [hgen] at h
  cases hb : native_and (native_inhabited_type T) (__smtx_type_wf_rec T T) with
  | false =>
      rw [hb] at h
      exact absurd h (by simp [native_ite])
  | true =>
      simp only [native_and, Bool.and_eq_true] at hb
      exact hb.2

theorem smtx_type_wf_rec_guard_of_true
    (T U : SmtType)
    (h : __smtx_type_wf_rec (__smtx_typeof_guard T U) (__smtx_typeof_guard T U) = true) :
    __smtx_type_wf_rec U U = true := by
  by_cases hNone : T = SmtType.None
  · exfalso
    simp [__smtx_typeof_guard, hNone, native_ite, native_Teq, __smtx_type_wf_rec] at h
  · have hGuard : __smtx_typeof_guard T U = U := by
      simp [__smtx_typeof_guard, native_ite, native_Teq, hNone]
    simpa [hGuard] using h

theorem seq_type_wf_rec_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf_rec (SmtType.Seq A) (SmtType.Seq A) = true) :
    __smtx_type_wf_rec A A = true := by
  have hA :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A A = true := by
    simpa [__smtx_type_wf_rec, native_and] using h
  exact hA.2

theorem seq_type_field_wf_rec_component_of_wf
    {A : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.Seq A) refs) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  exact smtx_type_field_wf_rec_of_type_wf_rec
    (seq_type_wf_rec_component_of_wf (by
      simpa [smtx_type_field_wf_rec] using h))

theorem set_type_wf_rec_component_of_wf
    {A : SmtType}
    (h : __smtx_type_wf_rec (SmtType.Set A) (SmtType.Set A) = true) :
    __smtx_type_wf_rec A A = true := by
  have hA :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A A = true := by
    simpa [__smtx_type_wf_rec, native_and] using h
  exact hA.2

theorem set_type_field_wf_rec_component_of_wf
    {A : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.Set A) refs) :
    smtx_type_field_wf_rec A native_reflist_nil := by
  exact smtx_type_field_wf_rec_of_type_wf_rec
    (set_type_wf_rec_component_of_wf (by
      simpa [smtx_type_field_wf_rec] using h))

theorem map_type_wf_rec_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf_rec (SmtType.Map A B) (SmtType.Map A B) = true) :
    __smtx_type_wf_rec A A = true ∧
      __smtx_type_wf_rec B B = true := by
  have h' :
      native_inhabited_type A = true ∧
        __smtx_type_wf_rec A A = true ∧
          native_inhabited_type B = true ∧
            __smtx_type_wf_rec B B = true := by
    simpa [__smtx_type_wf_rec, native_and] using h
  exact ⟨h'.2.1, h'.2.2.2⟩

theorem map_type_field_wf_rec_components_of_wf
    {A B : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.Map A B) refs) :
    smtx_type_field_wf_rec A native_reflist_nil ∧
      smtx_type_field_wf_rec B native_reflist_nil := by
  rcases map_type_wf_rec_components_of_wf (by
    simpa [smtx_type_field_wf_rec] using h) with ⟨hA, hB⟩
  exact ⟨smtx_type_field_wf_rec_of_type_wf_rec hA,
    smtx_type_field_wf_rec_of_type_wf_rec hB⟩

theorem fun_type_wf_rec_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf_rec A A = true ∧
      __smtx_type_wf_rec B B = true := by
  have h' :
      (native_inhabited_type A = true ∧
        __smtx_type_wf_rec A A = true) ∧
        (native_inhabited_type B = true ∧
          __smtx_type_wf_rec B B = true) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, native_and] using h
  exact ⟨h'.1.2, h'.2.2⟩

theorem ifun_type_wf_rec_components_of_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_type_wf_rec A A = true ∧
      __smtx_type_wf_rec B B = true := by
  exact fun_type_wf_rec_components_of_wf h

theorem fun_type_field_wf_rec_components_of_wf
    {A B : SmtType} {refs : RefList}
    (h : smtx_type_field_wf_rec (SmtType.FunType A B) refs) :
    smtx_type_field_wf_rec A native_reflist_nil ∧
      smtx_type_field_wf_rec B native_reflist_nil := by
  simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at h

theorem smtx_dt_cons_wf_rec_tail_of_true
    {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF) (SmtDatatypeCons.cons TU cU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true := by
  by_cases hc : __smtx_dt_cons_wf_rec cF cU = true
  · exact hc
  · exfalso
    cases TF <;> cases TU <;>
      simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]

private theorem smtx_dt_wf_tail_of_sum_wf_of_tail_ne_null
    {CF C : SmtDatatypeCons}
    {DtailF Dtail : SmtDatatype}
    (hWF : __smtx_dt_wf_rec (SmtDatatype.sum CF DtailF) (SmtDatatype.sum C Dtail) = true)
    (hTail : Dtail ≠ SmtDatatype.null) :
    __smtx_dt_wf_rec DtailF Dtail = true := by
  cases Dtail with
  | null =>
      exact False.elim (hTail rfl)
  | sum Ctail DtailTail =>
      have hCWF : __smtx_dt_cons_wf_rec CF C = true := by
        cases hC : __smtx_dt_cons_wf_rec CF C <;>
          cases DtailF <;> simp [__smtx_dt_wf_rec, native_ite, hC] at hWF ⊢
      simpa [__smtx_dt_wf_rec, native_ite, hCWF] using hWF

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_bool
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Bool := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_int
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Int := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_real
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Real := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_reglan
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.RegLan := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_char
    (n : native_Int) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Char := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_seq
    (n : native_Int) (A : SmtType) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Seq A := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_set
    (n : native_Int) (A : SmtType) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Set A := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_map
    (n : native_Int) (A B : SmtType) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.Map A B := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_fun
    (n : native_Int) (A B : SmtType) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.FunType A B := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_usort
    (n : native_Int) (i : native_Nat) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.USort i := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_typeref
    (n : native_Int) (s : native_String) :
    native_ite (native_zleq 0 n) (SmtType.BitVec (native_int_to_nat n)) SmtType.None ≠
      SmtType.TypeRef s := by
  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn]

/-- Simplifies EO-to-SMT type translation for `tuple_ne_bool`. -/
theorem eo_to_smt_type_tuple_ne_bool
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Bool := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_int`. -/
theorem eo_to_smt_type_tuple_ne_int
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Int := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_real`. -/
theorem eo_to_smt_type_tuple_ne_real
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Real := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_reglan`. -/
theorem eo_to_smt_type_tuple_ne_reglan
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.RegLan := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_bitvec`. -/
theorem eo_to_smt_type_tuple_ne_bitvec
    (U V : SmtType) (w : native_Nat) :
    __eo_to_smt_type_tuple U V ≠ SmtType.BitVec w := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_char`. -/
theorem eo_to_smt_type_tuple_ne_char
    (U V : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Char := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_seq`. -/
theorem eo_to_smt_type_tuple_ne_seq
    (U V W : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Seq W := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_set`. -/
theorem eo_to_smt_type_tuple_ne_set
    (U V W : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Set W := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_map`. -/
theorem eo_to_smt_type_tuple_ne_map
    (U V W X : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.Map W X := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_fun`. -/
theorem eo_to_smt_type_tuple_ne_fun
    (U V A B : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.FunType A B := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_ifun`. -/
theorem eo_to_smt_type_tuple_ne_ifun
    (U V A B : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.FunType A B := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_usort`. -/
theorem eo_to_smt_type_tuple_ne_usort
    (U V : SmtType) (i : native_Nat) :
    __eo_to_smt_type_tuple U V ≠ SmtType.USort i := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_typeref`. -/
theorem eo_to_smt_type_tuple_ne_typeref
    (U V : SmtType) (s' : native_String) :
    __eo_to_smt_type_tuple U V ≠ SmtType.TypeRef s' := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

/-- Simplifies EO-to-SMT type translation for `tuple_ne_dtc_app`. -/
theorem eo_to_smt_type_tuple_ne_dtc_app
    (U V A B : SmtType) :
    __eo_to_smt_type_tuple U V ≠ SmtType.DtcAppType A B := by
  cases V <;> try simp [__eo_to_smt_type_tuple]
  case Datatype s d =>
    cases d with
    | null =>
        simp
    | sum c d' =>
        cases d' with
        | null =>
            by_cases hs : s = (native_string_lit "@Tuple")
            · subst hs
              by_cases hComp : __smtx_type_wf_component U = true <;>
                simp [hComp]
            · simp [hs]
        | sum c' d'' =>
            simp

private theorem eo_to_smt_type_guarded_tuple_ne_bool
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Bool := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_bool U V]

private theorem eo_to_smt_type_guarded_tuple_ne_int
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Int := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_int U V]

private theorem eo_to_smt_type_guarded_tuple_ne_real
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Real := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_real U V]

private theorem eo_to_smt_type_guarded_tuple_ne_reglan
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.RegLan := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_reglan U V]

private theorem eo_to_smt_type_guarded_tuple_ne_bitvec
    (U V : SmtType) (w : native_Nat) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.BitVec w := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_bitvec U V w]

private theorem eo_to_smt_type_guarded_tuple_ne_char
    (U V : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Char := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_char U V]

private theorem eo_to_smt_type_guarded_tuple_ne_seq
    (U V W : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Seq W := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_seq U V W]

private theorem eo_to_smt_type_guarded_tuple_ne_set
    (U V W : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Set W := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_set U V W]

private theorem eo_to_smt_type_guarded_tuple_ne_map
    (U V W X : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.Map W X := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_map U V W X]

private theorem eo_to_smt_type_guarded_tuple_ne_fun
    (U V A B : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.FunType A B := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_fun U V A B]

private theorem eo_to_smt_type_guarded_tuple_ne_ifun
    (U V A B : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.FunType A B := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_ifun U V A B]

private theorem eo_to_smt_type_guarded_tuple_ne_usort
    (U V : SmtType) (i : native_Nat) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.USort i := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_usort U V i]

private theorem eo_to_smt_type_guarded_tuple_ne_typeref
    (U V : SmtType) (s : native_String) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.TypeRef s := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_typeref U V s]

private theorem eo_to_smt_type_guarded_tuple_ne_dtc_app
    (U V A B : SmtType) :
    native_ite (__smtx_type_wf (__eo_to_smt_type_tuple U V))
      (__eo_to_smt_type_tuple U V) SmtType.None ≠ SmtType.DtcAppType A B := by
  cases hWf : __smtx_type_wf (__eo_to_smt_type_tuple U V) <;>
    simp [native_ite, eo_to_smt_type_tuple_ne_dtc_app U V A B]

/-- Simplifies EO-to-SMT type translation for `fun_ne_bool`. -/
private theorem eo_to_smt_type_fun_ne_bool
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Bool := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_int`. -/
private theorem eo_to_smt_type_fun_ne_int
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Int := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_real`. -/
private theorem eo_to_smt_type_fun_ne_real
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Real := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_reglan`. -/
private theorem eo_to_smt_type_fun_ne_reglan
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.RegLan := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_char`. -/
private theorem eo_to_smt_type_fun_ne_char
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Char := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_bitvec`. -/
private theorem eo_to_smt_type_fun_ne_bitvec
    (T U : Term) (w : native_Nat) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.BitVec w := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_seq`. -/
private theorem eo_to_smt_type_fun_ne_seq
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Seq V := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_set`. -/
private theorem eo_to_smt_type_fun_ne_set
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Set V := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_map`. -/
private theorem eo_to_smt_type_fun_ne_map
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Map V W := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_dtc_app`. -/
private theorem eo_to_smt_type_fun_ne_dtc_app
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.DtcAppType V W := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_usort`. -/
private theorem eo_to_smt_type_fun_ne_usort
    (T U : Term) (i : native_Nat) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.USort i := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_typeref`. -/
private theorem eo_to_smt_type_fun_ne_typeref
    (T U : Term) (s : native_String) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.TypeRef s := by
  by_cases hT : __eo_to_smt_type T = SmtType.None
  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT]
  · by_cases hU : __eo_to_smt_type U = SmtType.None
    · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
    · cases hFin :
        __smtx_is_finite_type
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U)) <;>
        simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_bitvec
    (T U : Term) (w : native_Nat) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.BitVec w := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_seq
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Seq V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_set
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Set V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_map
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Map V W := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_fun
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.FunType V W := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_ifun
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.FunType V W := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_usort
    (T U : Term) (i : native_Nat) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.USort i := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_typeref
    (T U : Term) (s : native_String) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.TypeRef s := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `seq_inner`. -/
private theorem eo_to_smt_type_seq_inner
    (T : Term) {U : SmtType}
    (h : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) = SmtType.Seq U) :
    __eo_to_smt_type T = U := by
  cases hT : __eo_to_smt_type T <;>
    simp [__smtx_typeof_guard, native_ite, native_Teq, hT] at h
  all_goals exact h

/-- Simplifies EO-to-SMT type translation for `set_inner`. -/
private theorem eo_to_smt_type_set_inner
    (T : Term) {U : SmtType}
    (h : __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Set) T) = SmtType.Set U) :
    __eo_to_smt_type T = U := by
  cases hT : __eo_to_smt_type T <;>
    simp [__smtx_typeof_guard, native_ite, native_Teq, hT] at h
  all_goals exact h

/-- Simplifies EO-to-SMT type translation for `array_inners`. -/
private theorem eo_to_smt_type_array_inners
    (T U : Term) {A B : SmtType}
    (h : __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) T) U) = SmtType.Map A B) :
    __eo_to_smt_type T = A ∧ __eo_to_smt_type U = B := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [__smtx_typeof_guard, native_ite, native_Teq, hT, hU] at h
  all_goals exact h

/-- Simplifies EO-to-SMT type translation for `eq_bool`. -/
theorem eo_to_smt_type_eq_bool
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Bool) :
    T = Term.Bool := by
  cases T with
  | Bool =>
      rfl
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_bool y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_bool (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_int`. -/
theorem eo_to_smt_type_eq_int
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Int) :
    T = (Term.UOp UserOp.Int) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> try simp [__eo_to_smt_type] at h
      case Int =>
          rfl
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_int y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_int (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_real`. -/
theorem eo_to_smt_type_eq_real
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Real) :
    T = (Term.UOp UserOp.Real) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> try simp [__eo_to_smt_type] at h
      case Real =>
          rfl
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_real y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_real (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_reglan`. -/
theorem eo_to_smt_type_eq_reglan
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.RegLan) :
    T = (Term.UOp UserOp.RegLan) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> try simp [__eo_to_smt_type] at h
      case RegLan =>
          rfl
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_reglan y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_reglan (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_char`. -/
theorem eo_to_smt_type_eq_char
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Char) :
    T = (Term.UOp UserOp.Char) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> try simp [__eo_to_smt_type] at h
      case Char =>
          rfl
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
          ha, hb] at h
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_char y x h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_char (__eo_to_smt_type y) (__eo_to_smt_type x) h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_bitvec`. -/
theorem eo_to_smt_type_eq_bitvec
    {T : Term} {w : native_Nat}
    (h : __eo_to_smt_type T = SmtType.BitVec w) :
    T = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_bitvec T U w h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  by_cases hn : native_zleq 0 n = true
                  · simp [native_ite, hn] at h
                    cases h
                    have hnNonneg : 0 <= n := by
                      simpa [native_zleq, SmtEval.native_zleq] using hn
                    simp [native_nat_to_int, native_int_to_nat,
                      SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
                      Int.toNat_of_nonneg hnNonneg]
                  · simp [native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_bitvec y x w h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_bitvec (__eo_to_smt_type y) (__eo_to_smt_type x) w h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_seq`. -/
theorem eo_to_smt_type_eq_seq
    {T : Term} {U : SmtType}
    (h : __eo_to_smt_type T = SmtType.Seq U) :
    ∃ V, T = Term.Apply (Term.UOp UserOp.Seq) V ∧ __eo_to_smt_type V = U := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_seq T U _ h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              exact ⟨x, rfl, eo_to_smt_type_seq_inner x h⟩
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_seq y x U h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_seq (__eo_to_smt_type y) (__eo_to_smt_type x) U h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_seq_char`. -/
theorem eo_to_smt_type_eq_seq_char
    {T : Term}
    (h : __eo_to_smt_type T = SmtType.Seq SmtType.Char) :
    T = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  rcases eo_to_smt_type_eq_seq h with ⟨V, rfl, hV⟩
  rw [eo_to_smt_type_eq_char hV]

/-- Simplifies EO-to-SMT type translation for `eq_set`. -/
theorem eo_to_smt_type_eq_set
    {T : Term} {U : SmtType}
    (h : __eo_to_smt_type T = SmtType.Set U) :
    ∃ V, T = Term.Apply (Term.UOp UserOp.Set) V ∧ __eo_to_smt_type V = U := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U' =>
      exact (eo_to_smt_type_dtc_app_ne_set T U' U h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              exact ⟨x, rfl, eo_to_smt_type_set_inner x h⟩
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_set y x U h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_set (__eo_to_smt_type y) (__eo_to_smt_type x) U h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_map`. -/
theorem eo_to_smt_type_eq_map
    {T : Term} {A B : SmtType}
    (h : __eo_to_smt_type T = SmtType.Map A B) :
    ∃ U V, T = Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) V ∧
      __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_map T U A B h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_map y x A B h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_map (__eo_to_smt_type y) (__eo_to_smt_type x) A B h).elim
              case Array =>
                  exact ⟨y, x, rfl, (eo_to_smt_type_array_inners y x h).1,
                    (eo_to_smt_type_array_inners y x h).2⟩
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_fun`. -/
theorem eo_to_smt_type_eq_fun
    {T : Term} {A B : SmtType}
    (h : __eo_to_smt_type T = SmtType.FunType A B) :
    ∃ U V, T = Term.Apply (Term.Apply Term.FunType U) V ∧
      __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_fun T U A B h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              have hParts : __eo_to_smt_type y = A ∧ __eo_to_smt_type x = B := by
                by_cases hy : __eo_to_smt_type y = SmtType.None
                · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq,
                    hy] at h
                · by_cases hx : __eo_to_smt_type x = SmtType.None
                  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq,
                      hy, hx] at h
                  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite,
                      native_Teq, hy, hx] at h
                    exact h
              exact ⟨y, x, rfl, hParts.1, hParts.2⟩
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_fun (__eo_to_smt_type y) (__eo_to_smt_type x) A B h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_ifun`. -/
theorem eo_to_smt_type_eq_ifun
    {T : Term} {A B : SmtType}
    (h : __eo_to_smt_type T = SmtType.FunType A B) :
    ∃ U V, T = Term.Apply (Term.Apply Term.FunType U) V ∧
      __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_ifun T U A B h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              have hParts : __eo_to_smt_type y = A ∧ __eo_to_smt_type x = B := by
                by_cases hy : __eo_to_smt_type y = SmtType.None
                · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq,
                    hy] at h
                · by_cases hx : __eo_to_smt_type x = SmtType.None
                  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq,
                      hy, hx] at h
                  · simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite,
                      native_Teq, hy, hx] at h
                    exact h
              exact ⟨y, x, rfl, hParts.1, hParts.2⟩
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_ifun (__eo_to_smt_type y) (__eo_to_smt_type x) A B h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_dtc_app`. -/
theorem eo_to_smt_type_eq_dtc_app
    {T : Term} {A B : SmtType}
    (h : __eo_to_smt_type T = SmtType.DtcAppType A B) :
    ∃ U V, T = Term.DtcAppType U V ∧
      __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DtcAppType U V =>
      have hParts : __eo_to_smt_type U = A ∧ __eo_to_smt_type V = B := by
        cases hU : __eo_to_smt_type U <;> cases hV : __eo_to_smt_type V <;>
          simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
            hU, hV] at h
        all_goals exact h
      exact ⟨U, V, rfl, hParts.1, hParts.2⟩
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x <;> try simp [__eo_to_smt_type] at h
              case Numeral n =>
                  by_cases hn : native_zleq 0 n = true
                  · simp [hn] at h
                  · simp [hn] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_dtc_app y x A B h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_dtc_app (__eo_to_smt_type y) (__eo_to_smt_type x) A B h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_usort`. -/
theorem eo_to_smt_type_eq_usort
    {T : Term} {i : native_Nat}
    (h : __eo_to_smt_type T = SmtType.USort i) :
    T = Term.USort i := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DatatypeType s d =>
      by_cases hReserved : __eo_reserved_datatype_name s = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
  | DatatypeTypeRef s =>
      by_cases hReserved : __eo_reserved_datatype_name s = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_usort T U i h).elim
  | USort j =>
      simp [__eo_to_smt_type] at h
      cases h
      rfl
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_usort y x i h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_usort (__eo_to_smt_type y) (__eo_to_smt_type x) i h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Simplifies EO-to-SMT type translation for `eq_typeref`. -/
theorem eo_to_smt_type_eq_typeref
    {T : Term} {s : native_String}
    (h : __eo_to_smt_type T = SmtType.TypeRef s) :
    T = Term.DatatypeTypeRef s := by
  cases T with
  | Bool =>
      simp [__eo_to_smt_type] at h
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
  | DatatypeType s' d =>
      by_cases hReserved : __eo_reserved_datatype_name s' = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
  | DatatypeTypeRef s' =>
      by_cases hReserved : __eo_reserved_datatype_name s' = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
        cases h
        rfl
  | DtcAppType T U =>
      exact (eo_to_smt_type_dtc_app_ne_typeref T U s h).elim
  | Apply f x =>
      cases f with
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
              cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
              cases x with
              | Numeral n =>
                  cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
              | _ =>
                  simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              exact (eo_to_smt_type_fun_ne_typeref y x s h).elim
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Tuple =>
                  exact
                    (eo_to_smt_type_guarded_tuple_ne_typeref (__eo_to_smt_type y) (__eo_to_smt_type x) s h).elim
              case Array =>
                  cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                    simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ =>
              simp [__eo_to_smt_type] at h
      | _ =>
          simp [__eo_to_smt_type] at h
  | _ =>
      simp [__eo_to_smt_type] at h

theorem eo_reserved_datatype_name_tuple :
    __eo_reserved_datatype_name (native_string_lit "@Tuple") = true := by
  native_decide

theorem eo_unreserved_datatype_name_ne_tuple
    {s : native_String}
    (hReserved : __eo_reserved_datatype_name s = false) :
    s ≠ (native_string_lit "@Tuple") := by
  intro h
  subst s
  rw [eo_reserved_datatype_name_tuple] at hReserved
  contradiction

/--
Inverts translated user datatype types.

The `@Tuple` datatype is generated by the EO tuple encoding, so excluding it
keeps user datatypes disjoint from tuple types.
-/
theorem eo_to_smt_type_eq_datatype_non_tuple
    {T : Term} {s : native_String} {d : SmtDatatype}
    (hName : s ≠ (native_string_lit "@Tuple"))
    (h : __eo_to_smt_type T = SmtType.Datatype s d) :
    ∃ d0, T = Term.DatatypeType s d0 ∧ __eo_to_smt_datatype d0 = d := by
  cases T with
  | DatatypeType s' d' =>
      by_cases hReserved : __eo_reserved_datatype_name s' = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
        rcases h with ⟨hs, hd⟩
        subst s'
        exact ⟨d', rfl, hd⟩
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
      case UnitTuple =>
        rcases h with ⟨hs, _⟩
        exact False.elim (hName hs.symm)
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Array =>
                cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                  simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
              case Tuple =>
                have hRaw :
                    __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) =
                      SmtType.Datatype s d := by
                  cases hwf :
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                    simp [hwf] at h ⊢
                  exact h
                cases hx : __eo_to_smt_type x <;> simp [__eo_to_smt_type_tuple, hx] at hRaw
                case Datatype s0 d0 =>
                  by_cases hs0 : s0 = (native_string_lit "@Tuple")
                  · subst s0
                    cases d0 with
                    | null => simp at hRaw
                    | sum c rest =>
                        cases rest with
                        | null =>
                            by_cases hComp :
                                __smtx_type_wf_component (__eo_to_smt_type y) = true
                            · simp [hComp] at hRaw
                              rcases hRaw with ⟨hs, _⟩
                              exact False.elim (hName hs.symm)
                            · simp [hComp] at hRaw
                        | sum c' rest' =>
                            simp at hRaw
                  · cases d0 with
                    | null =>
                        simp at hRaw
                    | sum c rest =>
                        cases rest <;> simp [hs0] at hRaw
          | FunType =>
              cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
          | _ => simp [__eo_to_smt_type] at h
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
            cases hx : __eo_to_smt_type x <;>
              simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
            cases hx : __eo_to_smt_type x <;>
              simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
            cases x with
            | Numeral n =>
                cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
            | _ =>
                simp [__eo_to_smt_type] at h
      | _ => simp [__eo_to_smt_type] at h
  | DatatypeTypeRef s' =>
      by_cases hReserved : __eo_reserved_datatype_name s' = true
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
      · simp [__eo_to_smt_type, native_ite, hReserved] at h
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, ha, hb] at h
  | _ =>
      simp [__eo_to_smt_type] at h

/-- Inverts translated EO tuple types. -/
theorem eo_to_smt_type_eq_tuple_datatype
    {T : Term} {d : SmtDatatype}
    (h : __eo_to_smt_type T = SmtType.Datatype (native_string_lit "@Tuple") d) :
    (T = Term.UOp UserOp.UnitTuple ∧
      d = SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null) ∨
    (∃ y x c,
      T = Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) y) x ∧
      __eo_to_smt_type x = SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null) ∧
      d = SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) c) SmtDatatype.null) := by
  cases T with
  | UOp op =>
      cases op <;> simp [__eo_to_smt_type] at h
      case UnitTuple =>
        cases h
        exact Or.inl ⟨rfl, rfl⟩
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;> try simp [__eo_to_smt_type] at h
              case Array =>
                cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                  simp [__smtx_typeof_guard, native_ite, native_Teq, hy, hx] at h
              case Tuple =>
                have hRaw :
                    __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) =
                      SmtType.Datatype (native_string_lit "@Tuple") d := by
                  cases hWf :
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                    simp [hWf] at h ⊢
                  exact h
                cases hx : __eo_to_smt_type x <;> simp [__eo_to_smt_type_tuple, hx] at hRaw
                case Datatype s0 d0 =>
                  by_cases hs0 : s0 = (native_string_lit "@Tuple")
                  · subst s0
                    cases d0 with
                    | null => simp at hRaw
                    | sum c rest =>
                        cases rest with
                        | sum c' rest' => simp at hRaw
                        | null =>
                            by_cases hComp :
                                __smtx_type_wf_component (__eo_to_smt_type y) = true
                            · simp [hComp] at hRaw
                              cases hRaw
                              exact Or.inr ⟨y, x, c, rfl, hx, rfl⟩
                            · simp [hComp] at hRaw
                  · cases d0 with
                    | null =>
                        simp at hRaw
                    | sum c rest =>
                        cases rest <;> simp [hs0] at hRaw
          | FunType =>
              cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard,
                  native_ite, native_Teq, hy, hx] at h
          | _ => simp [__eo_to_smt_type] at h
      | UOp op =>
          cases op <;> try simp [__eo_to_smt_type] at h
          case Seq =>
            cases hx : __eo_to_smt_type x <;>
              simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case Set =>
            cases hx : __eo_to_smt_type x <;>
              simp [__smtx_typeof_guard, native_ite, native_Teq, hx] at h
          case BitVec =>
            cases x with
            | Numeral n =>
                cases hn : native_zleq 0 n <;> simp [__eo_to_smt_type, native_ite, hn] at h
            | _ =>
                simp [__eo_to_smt_type] at h
      | FunType =>
          simp [__eo_to_smt_type] at h
      | _ => simp [__eo_to_smt_type] at h
  | DatatypeType s d0 =>
      by_cases hr : __eo_reserved_datatype_name s = true <;>
        simp [__eo_to_smt_type, native_ite, hr] at h
      rcases h with ⟨hs, _⟩
      subst s
      rw [eo_reserved_datatype_name_tuple] at hr
      contradiction
  | DatatypeTypeRef s =>
      by_cases hr : __eo_reserved_datatype_name s = true <;>
        simp [__eo_to_smt_type, native_ite, hr] at h
  | DtcAppType a b =>
      cases ha : __eo_to_smt_type a <;> cases hb : __eo_to_smt_type b <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, ha, hb] at h
  | _ => simp [__eo_to_smt_type] at h



/-! ## Reserved-name substitution no-op (used by the tuple cases below)
Substituting a *reserved* datatype name (e.g. the synthetic `"@Tuple"`) is a no-op on any
translated type, because translation never emits a `TypeRef` bearing a reserved name at a
substitution-reachable position. This discharges the "substitution is a no-op on tuple field
positions" obligations in the injectivity/well-formedness inversions below.

The block runs with the file's `native_ite`/`native_streq`/`native_and` local-simp lemmas
disabled so the `native_ite`-based no-op proofs stay in their explicit `rw` form. -/
section ReservedNoop
attribute [-simp] native_ite native_streq native_and

/- `noResRefTy T`: no `TypeRef s` with `s` a *reserved* datatype name occurs anywhere in `T`
(recursing unconditionally through datatype bodies AND composite type components). Purely syntactic.
Stronger than the substitution-reachability needed for the no-op, but that extra strength is what
lets tuple-body facts be read directly off `noResRefTy (tr tuple)`. -/
mutual
def noResRefTy : SmtType → Bool
  | SmtType.Datatype _ d => noResRefDt d
  | SmtType.TypeRef s => native_not (native_reserved_datatype_name s)
  | SmtType.Seq a => noResRefTy a
  | SmtType.Set a => noResRefTy a
  | SmtType.Map a b => native_and (noResRefTy a) (noResRefTy b)
  | SmtType.FunType a b => native_and (noResRefTy a) (noResRefTy b)
  | SmtType.DtcAppType a b => native_and (noResRefTy a) (noResRefTy b)
  | _ => true
def noResRefDt : SmtDatatype → Bool
  | SmtDatatype.sum c d => native_and (noResRefDtc c) (noResRefDt d)
  | SmtDatatype.null => true
def noResRefDtc : SmtDatatypeCons → Bool
  | SmtDatatypeCons.cons T c => native_and (noResRefTy T) (noResRefDtc c)
  | SmtDatatypeCons.unit => true
end

/- Substituting a reserved name is a no-op on any `noResRef` structure. -/
mutual
theorem subst_noResRef_ty (r : native_String) (hRes : native_reserved_datatype_name r = true) :
    (T : SmtType) → (X : SmtDatatype) → noResRefTy T = true → __smtx_type_substitute r X T = T
  | SmtType.Datatype s d, X, h => by
      simp only [noResRefTy] at h
      simp only [__smtx_type_substitute]
      by_cases hrs : native_streq r s = true
      · rw [native_ite, if_pos hrs]
      · rw [native_ite, if_neg (by simp [hrs])]
        rw [subst_noResRef_dt r hRes d (__smtx_dt_lift s d X) h]
  | SmtType.TypeRef s, X, h => by
      simp only [noResRefTy, native_not, Bool.not_eq_true'] at h
      have hrs : native_streq r s = false := by
        simp only [native_streq, decide_eq_false_iff_not]
        intro he; rw [he] at hRes; rw [h] at hRes; exact absurd hRes (by decide)
      simp only [__smtx_type_substitute]
      rw [native_ite, if_neg (by simp [hrs])]
  | SmtType.Seq a, X, h => by simp [__smtx_type_substitute]
  | SmtType.Set a, X, h => by simp [__smtx_type_substitute]
  | SmtType.Map a b, X, h => by simp [__smtx_type_substitute]
  | SmtType.FunType a b, X, h => by simp [__smtx_type_substitute]
  | SmtType.DtcAppType a b, X, h => by simp [__smtx_type_substitute]
  | SmtType.None, X, h => by simp [__smtx_type_substitute]
  | SmtType.RegLan, X, h => by simp [__smtx_type_substitute]
  | SmtType.Bool, X, h => by simp [__smtx_type_substitute]
  | SmtType.Int, X, h => by simp [__smtx_type_substitute]
  | SmtType.Real, X, h => by simp [__smtx_type_substitute]
  | SmtType.BitVec n, X, h => by simp [__smtx_type_substitute]
  | SmtType.Char, X, h => by simp [__smtx_type_substitute]
  | SmtType.USort n, X, h => by simp [__smtx_type_substitute]

theorem subst_noResRef_dt (r : native_String) (hRes : native_reserved_datatype_name r = true) :
    (W : SmtDatatype) → (X : SmtDatatype) → noResRefDt W = true → __smtx_dt_substitute r X W = W
  | SmtDatatype.null, X, h => by simp [__smtx_dt_substitute]
  | SmtDatatype.sum c d, X, h => by
      simp only [noResRefDt, native_and, Bool.and_eq_true] at h
      simp only [__smtx_dt_substitute]
      rw [subst_noResRef_dtc r hRes c X h.1, subst_noResRef_dt r hRes d X h.2]

theorem subst_noResRef_dtc (r : native_String) (hRes : native_reserved_datatype_name r = true) :
    (c : SmtDatatypeCons) → (X : SmtDatatype) → noResRefDtc c = true → __smtx_dtc_substitute r X c = c
  | SmtDatatypeCons.unit, X, h => by simp [__smtx_dtc_substitute]
  | SmtDatatypeCons.cons T c, X, h => by
      simp only [noResRefDtc, native_and, Bool.and_eq_true] at h
      simp only [__smtx_dtc_substitute]
      rw [subst_noResRef_ty r hRes T X h.1, subst_noResRef_dtc r hRes c X h.2]
end

/- Helper: `__smtx_typeof_guard A B` is either `None` or `B`. -/
theorem eoTy_guard_cases_res (A B : SmtType) :
    __smtx_typeof_guard A B = SmtType.None ∨ __smtx_typeof_guard A B = B := by
  simp only [__smtx_typeof_guard]
  by_cases h : native_Teq A SmtType.None = true
  · left; simp [native_ite, h]
  · right; simp [native_ite, h]

/- The tuple encoding preserves `noResRef`. -/
theorem noResRef_tuple (A B : SmtType)
    (hA : noResRefTy A = true) (hB : noResRefTy B = true) :
    noResRefTy (__eo_to_smt_type_tuple A B) = true := by
  cases B with
  | Datatype s body =>
      cases body with
      | sum c tail =>
          cases tail with
          | null =>
              simp only [__eo_to_smt_type_tuple]
              by_cases hcond :
                  native_and (native_streq s (native_string_lit "@Tuple"))
                    (__smtx_type_wf_component A) = true
              · rw [native_ite, if_pos hcond]
                simp only [noResRefTy, noResRefDt, native_and, Bool.and_eq_true, noResRefDtc] at hB ⊢
                exact ⟨⟨hA, hB.1⟩, hB.2⟩
              · rw [native_ite, if_neg (by simp [hcond])]; simp [noResRefTy]
          | sum _ _ => simp [__eo_to_smt_type_tuple, noResRefTy]
      | null => simp [__eo_to_smt_type_tuple, noResRefTy]
  | _ => simp [__eo_to_smt_type_tuple, noResRefTy]

/- Translation of any term satisfies `noResRef`. -/
mutual
theorem noResRef_translate_ty : (T : Term) → noResRefTy (__eo_to_smt_type T) = true
  | Term.Bool => by simp [__eo_to_smt_type, noResRefTy]
  | Term.USort i => by simp [__eo_to_smt_type, noResRefTy]
  | Term.DatatypeType s d => by
      by_cases hs : native_reserved_datatype_name s = true
      · simp [__eo_to_smt_type, native_ite, hs, noResRefTy]
      · have hsF : native_reserved_datatype_name s = false := by
          cases h : native_reserved_datatype_name s <;> simp [h] at hs ⊢
        simp only [__eo_to_smt_type, native_ite, hsF, Bool.false_eq_true, if_false, noResRefTy]
        exact noResRef_translate_dt d
  | Term.DatatypeTypeRef s => by
      by_cases hs : native_reserved_datatype_name s = true
      · simp [__eo_to_smt_type, native_ite, hs, noResRefTy]
      · have hsF : native_reserved_datatype_name s = false := by
          cases h : native_reserved_datatype_name s <;> simp [h] at hs ⊢
        simp [__eo_to_smt_type, native_ite, noResRefTy, native_not, hsF]
  | Term.DtcAppType T U => by
      simp only [__eo_to_smt_type]
      rcases eoTy_guard_cases_res (__eo_to_smt_type T)
          (__smtx_typeof_guard (__eo_to_smt_type U) (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U))) with h | h
        <;> rw [h]
      · simp [noResRefTy]
      · rcases eoTy_guard_cases_res (__eo_to_smt_type U) (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)) with h2 | h2
          <;> rw [h2]
        · simp [noResRefTy]
        · simp only [noResRefTy, native_and, Bool.and_eq_true]
          exact ⟨noResRef_translate_ty T, noResRef_translate_ty U⟩
  | Term.UOp op => by
      cases op with
      | Int => simp [__eo_to_smt_type, noResRefTy]
      | Real => simp [__eo_to_smt_type, noResRefTy]
      | Char => simp [__eo_to_smt_type, noResRefTy]
      | UnitTuple => simp [__eo_to_smt_type, noResRefTy, noResRefDt, noResRefDtc, native_and]
      | _ => simp [__eo_to_smt_type, noResRefTy]
  | Term.Apply (Term.Apply Term.FunType T1) T2 => by
      simp only [__eo_to_smt_type]
      rcases eoTy_guard_cases_res (__eo_to_smt_type T1)
          (__smtx_typeof_guard (__eo_to_smt_type T2) (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2))) with h | h
        <;> rw [h]
      · simp [noResRefTy]
      · rcases eoTy_guard_cases_res (__eo_to_smt_type T2) (SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2)) with h2 | h2
          <;> rw [h2]
        · simp [noResRefTy]
        · simp only [noResRefTy, native_and, Bool.and_eq_true]
          exact ⟨noResRef_translate_ty T1, noResRef_translate_ty T2⟩
  | Term.Apply f x => by
      cases f with
      | UOp op =>
          cases op with
          | BitVec =>
              cases x with
              | Numeral n =>
                  simp only [__eo_to_smt_type]
                  by_cases hn : native_zleq 0 n = true <;> simp [native_ite, hn, noResRefTy]
              | _ => simp [__eo_to_smt_type, noResRefTy]
          | Seq =>
              simp only [__eo_to_smt_type]
              rcases eoTy_guard_cases_res (__eo_to_smt_type x) (SmtType.Seq (__eo_to_smt_type x)) with h | h
                <;> rw [h]
              · simp [noResRefTy]
              · simp only [noResRefTy]; exact noResRef_translate_ty x
          | Set =>
              simp only [__eo_to_smt_type]
              rcases eoTy_guard_cases_res (__eo_to_smt_type x) (SmtType.Set (__eo_to_smt_type x)) with h | h
                <;> rw [h]
              · simp [noResRefTy]
              · simp only [noResRefTy]; exact noResRef_translate_ty x
          | _ => simp [__eo_to_smt_type, noResRefTy]
      | Apply g y =>
          cases g with
          | FunType =>
              simp only [__eo_to_smt_type]
              rcases eoTy_guard_cases_res (__eo_to_smt_type y)
                  (__smtx_typeof_guard (__eo_to_smt_type x) (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))) with h | h
                <;> rw [h]
              · simp [noResRefTy]
              · rcases eoTy_guard_cases_res (__eo_to_smt_type x) (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) with h2 | h2
                  <;> rw [h2]
                · simp [noResRefTy]
                · simp only [noResRefTy, native_and, Bool.and_eq_true]
                  exact ⟨noResRef_translate_ty y, noResRef_translate_ty x⟩
          | UOp op =>
              cases op with
              | Array =>
                  simp only [__eo_to_smt_type]
                  rcases eoTy_guard_cases_res (__eo_to_smt_type y)
                      (__smtx_typeof_guard (__eo_to_smt_type x) (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x))) with h | h
                    <;> rw [h]
                  · simp [noResRefTy]
                  · rcases eoTy_guard_cases_res (__eo_to_smt_type x) (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x)) with h2 | h2
                      <;> rw [h2]
                    · simp [noResRefTy]
                    · simp only [noResRefTy, native_and, Bool.and_eq_true]
                      exact ⟨noResRef_translate_ty y, noResRef_translate_ty x⟩
              | Tuple =>
                  simp only [__eo_to_smt_type]
                  by_cases hWf :
                      __smtx_type_wf (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) = true
                  · rw [native_ite, if_pos hWf]
                    exact noResRef_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)
                      (noResRef_translate_ty y) (noResRef_translate_ty x)
                  · rw [native_ite, if_neg (by simp [hWf])]; simp [noResRefTy]
              | _ => simp [__eo_to_smt_type, noResRefTy]
          | _ => simp [__eo_to_smt_type, noResRefTy]
      | _ => simp [__eo_to_smt_type, noResRefTy]
  | Term.__eo_List => by simp [__eo_to_smt_type, noResRefTy]
  | Term.__eo_List_nil => by simp [__eo_to_smt_type, noResRefTy]
  | Term.__eo_List_cons => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Boolean b => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Numeral n => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Rational q => by simp [__eo_to_smt_type, noResRefTy]
  | Term.String s => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Binary w n => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Type => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Stuck => by simp [__eo_to_smt_type, noResRefTy]
  | Term.FunType => by simp [__eo_to_smt_type, noResRefTy]
  | Term.Var name T => by simp [__eo_to_smt_type, noResRefTy]
  | Term.DtCons s d i => by simp [__eo_to_smt_type, noResRefTy]
  | Term.DtSel s d i j => by simp [__eo_to_smt_type, noResRefTy]
  | Term.UConst i T => by simp [__eo_to_smt_type, noResRefTy]
  | Term.UOp1 op x => by cases op <;> simp [__eo_to_smt_type, noResRefTy]
  | Term.UOp2 op x y => by cases op <;> simp [__eo_to_smt_type, noResRefTy]
  | Term.UOp3 op x y z => by cases op <;> simp [__eo_to_smt_type, noResRefTy]

theorem noResRef_translate_dt : (d : Datatype) → noResRefDt (__eo_to_smt_datatype d) = true
  | Datatype.null => by simp [__eo_to_smt_datatype, noResRefDt]
  | Datatype.sum c d => by
      simp only [__eo_to_smt_datatype, noResRefDt, native_and, Bool.and_eq_true]
      exact ⟨noResRef_translate_dtc c, noResRef_translate_dt d⟩

theorem noResRef_translate_dtc : (c : DatatypeCons) → noResRefDtc (__eo_to_smt_datatype_cons c) = true
  | DatatypeCons.unit => by simp [__eo_to_smt_datatype_cons, noResRefDtc]
  | DatatypeCons.cons T c => by
      simp only [__eo_to_smt_datatype_cons, noResRefDtc, native_and, Bool.and_eq_true]
      exact ⟨noResRef_translate_ty T, noResRef_translate_dtc c⟩
end

/- Substituting a reserved name is a no-op on translated content. -/
theorem subst_reserved_noop_ty (r : native_String) (hRes : native_reserved_datatype_name r = true)
    (T : Term) (X : SmtDatatype) :
    __smtx_type_substitute r X (__eo_to_smt_type T) = __eo_to_smt_type T :=
  subst_noResRef_ty r hRes (__eo_to_smt_type T) X (noResRef_translate_ty T)

theorem subst_reserved_noop_dt (r : native_String) (hRes : native_reserved_datatype_name r = true)
    (d : Datatype) (X : SmtDatatype) :
    __smtx_dt_substitute r X (__eo_to_smt_datatype d) = __eo_to_smt_datatype d :=
  subst_noResRef_dt r hRes (__eo_to_smt_datatype d) X (noResRef_translate_dt d)

end ReservedNoop

section TupleDiagWf
attribute [-simp] native_ite native_streq native_and
/-- Component well-formedness of a (non-`None`) tuple type: from the diagonal well-formedness
of `__eo_to_smt_type_tuple (tr y) (tr x)`, both `tr y` and `tr x` are themselves diagonally
well-formed. Uses the reserved-name substitution no-op to collapse the tuple's self-substitution. -/
theorem tuple_diag_wf_components (y x : Term)
    (hWf : __smtx_type_wf_rec (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x))
        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) = true)
    (hNN : __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) ≠ SmtType.None) :
    __smtx_type_wf_rec (__eo_to_smt_type y) (__eo_to_smt_type y) = true ∧
    __smtx_type_wf_rec (__eo_to_smt_type x) (__eo_to_smt_type x) = true := by
  have hResTuple : native_reserved_datatype_name (native_string_lit "@Tuple") = true := by
    native_decide
  cases hxShape : __eo_to_smt_type x with
  | Datatype sx bx =>
    cases bx with
    | sum cx tx =>
      cases tx with
      | null =>
        by_cases hsx : native_streq sx (native_string_lit "@Tuple") = true
        · by_cases hyc : __smtx_type_wf_component (__eo_to_smt_type y) = true
          · have hsxeq : sx = native_string_lit "@Tuple" := by simpa [native_streq] using hsx
            subst hsxeq
            have hEq :
                __eo_to_smt_type_tuple (__eo_to_smt_type y)
                    (SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum cx SmtDatatype.null)) =
                  SmtType.Datatype (native_string_lit "@Tuple")
                    (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) SmtDatatype.null) := by
              simp [__eo_to_smt_type_tuple, native_ite, native_and, hsx, hyc]
            rw [hxShape, hEq] at hWf
            have hcxNoRes : noResRefDtc cx = true := by
              have hnr := noResRef_translate_ty x
              rw [hxShape] at hnr
              simpa [noResRefTy, noResRefDt, noResRefDtc, native_and] using hnr
            have hbodyNoRes :
                noResRefDt (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx)
                    SmtDatatype.null) = true := by
              simp [noResRefDt, noResRefDtc, native_and, noResRef_translate_ty y, hcxNoRes]
            have hAwf :
                __smtx_dt_wf_rec
                    (__smtx_dt_substitute (native_string_lit "@Tuple")
                      (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) SmtDatatype.null)
                      (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) SmtDatatype.null))
                    (SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) SmtDatatype.null) = true := by
              simpa [__smtx_type_wf_rec] using hWf
            rw [subst_noResRef_dt (native_string_lit "@Tuple") hResTuple _ _ hbodyNoRes] at hAwf
            have hConsWF :
                __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons (__eo_to_smt_type y) cx)
                    (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) = true := by
              simp only [__smtx_dt_wf_rec, native_ite] at hAwf
              by_cases hc :
                  __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons (__eo_to_smt_type y) cx)
                    (SmtDatatypeCons.cons (__eo_to_smt_type y) cx) = true
              · exact hc
              · rw [if_neg (by simpa using hc)] at hAwf; simp at hAwf
            have hyNotRef : ∀ s, __eo_to_smt_type y ≠ SmtType.TypeRef s := by
              intro s he
              rw [he] at hConsWF
              simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, native_and] at hConsWF
            have hyWF : __smtx_type_wf_rec (__eo_to_smt_type y) (__eo_to_smt_type y) = true :=
              smtx_type_field_wf_rec_of_cons_wf (refs := native_reflist_nil) hyNotRef hConsWF
            have hcxWF : __smtx_dt_cons_wf_rec cx cx = true :=
              smtx_dt_cons_wf_rec_tail_of_true hConsWF
            have hxWF :
                __smtx_type_wf_rec
                    (SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum cx SmtDatatype.null))
                    (SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum cx SmtDatatype.null)) = true := by
              have h2 :
                  __smtx_dt_wf_rec (SmtDatatype.sum cx SmtDatatype.null)
                    (SmtDatatype.sum cx SmtDatatype.null) = true := by
                simp only [__smtx_dt_wf_rec, hcxWF]; decide
              simp only [__smtx_type_wf_rec]
              rw [subst_noResRef_dt (native_string_lit "@Tuple") hResTuple
                (SmtDatatype.sum cx SmtDatatype.null) (SmtDatatype.sum cx SmtDatatype.null)
                (by simp [noResRefDt, hcxNoRes, native_and])]
              exact h2
            exact ⟨hyWF, hxWF⟩
          · exfalso; apply hNN
            have hyc' : __smtx_type_wf_component (__eo_to_smt_type y) = false := by
              cases hh : __smtx_type_wf_component (__eo_to_smt_type y) <;> simp_all
            simp [__eo_to_smt_type_tuple, hxShape, native_ite, native_and, hyc']
        · exfalso; apply hNN
          have hsxF : native_streq sx (native_string_lit "@Tuple") = false := by
            cases hh : native_streq sx (native_string_lit "@Tuple")
            · rfl
            · exact absurd hh hsx
          simp [__eo_to_smt_type_tuple, hxShape, native_ite, native_and, hsxF]
      | sum _ _ => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
    | null => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Bool => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Int => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Real => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | RegLan => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | BitVec n => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Map a b => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Set a => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Seq a => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | Char => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | TypeRef s3 => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | USort i => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | FunType a b => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | DtcAppType a b => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
  | None => exfalso; apply hNN; simp [__eo_to_smt_type_tuple, hxShape]
end TupleDiagWf



mutual

/-- EO-to-SMT type translation is injective on well-formed type fields. -/
theorem eo_to_smt_type_injective_of_field_wf_rec
    {T U : Term} {A : SmtType} {refs : RefList}
    (hT : __eo_to_smt_type T = A)
    (hU : __eo_to_smt_type U = A)
    (hWF : smtx_type_field_wf_rec A refs) :
    T = U := by
  cases A with
  | None =>
      simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hWF
  | Bool =>
      rw [eo_to_smt_type_eq_bool hT, eo_to_smt_type_eq_bool hU]
  | Int =>
      rw [eo_to_smt_type_eq_int hT, eo_to_smt_type_eq_int hU]
  | Real =>
      rw [eo_to_smt_type_eq_real hT, eo_to_smt_type_eq_real hU]
  | RegLan =>
      rw [eo_to_smt_type_eq_reglan hT, eo_to_smt_type_eq_reglan hU]
  | BitVec w =>
      rw [eo_to_smt_type_eq_bitvec hT, eo_to_smt_type_eq_bitvec hU]
  | Map A B =>
      rcases eo_to_smt_type_eq_map hT with ⟨T1, T2, rfl, hT1, hT2⟩
      rcases eo_to_smt_type_eq_map hU with ⟨U1, U2, rfl, hU1, hU2⟩
      have hComps := map_type_field_wf_rec_components_of_wf
        (A := A) (B := B) (refs := refs) hWF
      have h1 : T1 = U1 :=
        eo_to_smt_type_injective_of_field_wf_rec hT1 hU1 hComps.1
      have h2 : T2 = U2 :=
        eo_to_smt_type_injective_of_field_wf_rec hT2 hU2 hComps.2
      subst U1
      subst U2
      rfl
  | Set A =>
      rcases eo_to_smt_type_eq_set hT with ⟨T0, rfl, hT0⟩
      rcases eo_to_smt_type_eq_set hU with ⟨U0, rfl, hU0⟩
      have hA := set_type_field_wf_rec_component_of_wf
        (A := A) (refs := refs) hWF
      have h0 : T0 = U0 :=
        eo_to_smt_type_injective_of_field_wf_rec hT0 hU0 hA
      subst U0
      rfl
  | Seq A =>
      rcases eo_to_smt_type_eq_seq hT with ⟨T0, rfl, hT0⟩
      rcases eo_to_smt_type_eq_seq hU with ⟨U0, rfl, hU0⟩
      have hA := seq_type_field_wf_rec_component_of_wf
        (A := A) (refs := refs) hWF
      have h0 : T0 = U0 :=
        eo_to_smt_type_injective_of_field_wf_rec hT0 hU0 hA
      subst U0
      rfl
  | Char =>
      rw [eo_to_smt_type_eq_char hT, eo_to_smt_type_eq_char hU]
  | Datatype s d =>
      by_cases hs : s = (native_string_lit "@Tuple")
      · subst s
        rcases eo_to_smt_type_eq_tuple_datatype hT with hUnitT | hTupleT
        · rcases hUnitT with ⟨rfl, hD⟩
          rcases eo_to_smt_type_eq_tuple_datatype hU with hUnitU | hTupleU
          · rcases hUnitU with ⟨rfl, _⟩
            rfl
          · rcases hTupleU with ⟨y, x, c, hUShape, hxU, hDU⟩
            subst U
            simp [hD] at hDU
        · rcases hTupleT with ⟨yT, xT, cT, rfl, hxT, hDT⟩
          rcases eo_to_smt_type_eq_tuple_datatype hU with hUnitU | hTupleU
          · rcases hUnitU with ⟨hUShape, hDU⟩
            subst U
            simp [hDU] at hDT
          · rcases hTupleU with ⟨yU, xU, cU, hUShape, hxU, hDU⟩
            subst U
            have hDsum :
                SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type yT) cT)
                    SmtDatatype.null =
                  SmtDatatype.sum (SmtDatatypeCons.cons (__eo_to_smt_type yU) cU)
                    SmtDatatype.null :=
              hDT.symm.trans hDU
            injection hDsum with hCons _
            injection hCons with hY hC
            subst cU
            -- The reserved-name "@Tuple" substitution is a no-op on translated content
            -- (`subst_noResRef_dt`), so the tuple's diagonal well-formedness collapses to the plain
            -- `dt_wf_rec` of its (self-contained) body, from which the head/tail field diagonal
            -- well-formedness — and hence injectivity on the tuple elements — follows.
            have hResTuple : native_reserved_datatype_name (native_string_lit "@Tuple") = true := by
              native_decide
            have hcTNoRes : noResRefDtc cT = true := by
              have hx := noResRef_translate_ty xT
              rw [hxT] at hx
              simpa [noResRefTy, noResRefDt, noResRefDtc, native_and] using hx
            have hnoResD : noResRefDt d = true := by
              rw [hDT]
              simp [noResRefDt, noResRefDtc, native_and, noResRef_translate_ty yT, hcTNoRes]
            have hAwf : __smtx_dt_wf_rec (__smtx_dt_substitute (native_string_lit "@Tuple") d d) d = true :=
              smtx_datatype_field_wf_rec_parts hWF
            rw [subst_noResRef_dt (native_string_lit "@Tuple") hResTuple d d hnoResD, hDT] at hAwf
            have hConsWF :
                __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons (__eo_to_smt_type yT) cT)
                    (SmtDatatypeCons.cons (__eo_to_smt_type yT) cT) = true := by
              simp only [__smtx_dt_wf_rec, native_ite] at hAwf
              by_cases hc :
                  __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons (__eo_to_smt_type yT) cT)
                    (SmtDatatypeCons.cons (__eo_to_smt_type yT) cT) = true
              · exact hc
              · rw [if_neg (by simpa using hc)] at hAwf; simp at hAwf
            have hyNotRef : ∀ s, __eo_to_smt_type yT ≠ SmtType.TypeRef s := by
              intro s he
              rw [he] at hConsWF
              simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, native_ite, native_and] at hConsWF
            have hyFieldWF : smtx_type_field_wf_rec (__eo_to_smt_type yT) native_reflist_nil :=
              smtx_type_field_wf_rec_of_cons_wf (refs := native_reflist_nil) hyNotRef hConsWF
            have hyEq : yT = yU :=
              eo_to_smt_type_injective_of_field_wf_rec rfl hY.symm hyFieldWF
            have hcTWF : __smtx_dt_cons_wf_rec cT cT = true :=
              smtx_dt_cons_wf_rec_tail_of_true hConsWF
            have hxWF :
                __smtx_type_wf_rec (__eo_to_smt_type xT) (__eo_to_smt_type xT) = true := by
              rw [hxT]
              simp only [__smtx_type_wf_rec]
              rw [subst_noResRef_dt (native_string_lit "@Tuple") hResTuple
                (SmtDatatype.sum cT SmtDatatype.null) (SmtDatatype.sum cT SmtDatatype.null)
                (by simp [noResRefDt, hcTNoRes])]
              simp [__smtx_dt_wf_rec, native_ite, hcTWF]
            have hxEq : xT = xU :=
              eo_to_smt_type_injective_of_field_wf_rec (refs := native_reflist_nil) rfl
                (hxU.trans hxT.symm) hxWF
            subst yU
            subst xU
            rfl
      · rcases eo_to_smt_type_eq_datatype_non_tuple hs hT with ⟨dT, rfl, hDT⟩
        rcases eo_to_smt_type_eq_datatype_non_tuple hs hU with ⟨dU, rfl, hDU⟩
        have hDWF : __smtx_dt_wf_rec (__smtx_dt_substitute s d d) d = true :=
          smtx_datatype_field_wf_rec_parts hWF
        have hD : dT = dU :=
          eo_to_smt_datatype_injective_of_wf_rec hDT hDU hDWF
        subst dU
        rfl
  | TypeRef s =>
      rw [eo_to_smt_type_eq_typeref hT, eo_to_smt_type_eq_typeref hU]
  | USort i =>
      rw [eo_to_smt_type_eq_usort hT, eo_to_smt_type_eq_usort hU]
  | FunType A B =>
      rcases eo_to_smt_type_eq_fun hT with ⟨T1, T2, rfl, hT1, hT2⟩
      rcases eo_to_smt_type_eq_fun hU with ⟨U1, U2, rfl, hU1, hU2⟩
      have hComps := fun_type_field_wf_rec_components_of_wf
        (A := A) (B := B) (refs := refs) hWF
      have h1 : T1 = U1 :=
        eo_to_smt_type_injective_of_field_wf_rec hT1 hU1 hComps.1
      have h2 : T2 = U2 :=
        eo_to_smt_type_injective_of_field_wf_rec hT2 hU2 hComps.2
      subst U1
      subst U2
      rfl
  | DtcAppType A B =>
      simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hWF
termination_by sizeOf T

/-- EO datatype translation is injective for well-formed datatypes. `DF` is the "full" (once
self-substituted) counterpart of `D`, decomposing alongside it: at the top of a `Datatype s _`
field, `DF = __smtx_dt_substitute s D D`; the substitution's own `sum`/`cons` structure mirrors
`D`'s, so `DF`'s tail is always the substitute of `D`'s tail (see `__smtx_dt_substitute`). -/
theorem eo_to_smt_datatype_injective_of_wf_rec
    {d e : Datatype} {DF D : SmtDatatype}
    (hd : __eo_to_smt_datatype d = D)
    (he : __eo_to_smt_datatype e = D)
    (hWF : __smtx_dt_wf_rec DF D = true) :
    d = e := by
  cases D with
  | null =>
      cases d <;> cases e <;> simp [__eo_to_smt_datatype] at hd he ⊢
  | sum C Dtail =>
      cases hDF : DF with
      | null =>
          exfalso
          rw [hDF] at hWF
          simp [__smtx_dt_wf_rec] at hWF
      | sum CF DtailF =>
          rw [hDF] at hWF
          cases d with
          | null => simp [__eo_to_smt_datatype] at hd
          | sum c dt =>
              cases e with
              | null => simp [__eo_to_smt_datatype] at he
              | sum c' dt' =>
                  simp [__eo_to_smt_datatype] at hd he
                  rcases hd with ⟨hc, hdTail⟩
                  rcases he with ⟨hc', heTail⟩
                  have hCWF : __smtx_dt_cons_wf_rec CF C = true := by
                    cases hC : __smtx_dt_cons_wf_rec CF C <;>
                      cases Dtail <;> cases DtailF <;>
                        simp [__smtx_dt_wf_rec, native_ite, hC] at hWF ⊢
                  have hcEq : c = c' :=
                    eo_to_smt_datatype_cons_injective_of_wf_rec hc hc' hCWF
                  have hdEq : dt = dt' := by
                    by_cases hDtail : Dtail = SmtDatatype.null
                    · cases dt <;> cases dt' <;>
                        simp [__eo_to_smt_datatype, hDtail] at hdTail heTail ⊢
                    · have hDtailWF : __smtx_dt_wf_rec DtailF Dtail = true :=
                        smtx_dt_wf_tail_of_sum_wf_of_tail_ne_null hWF hDtail
                      exact eo_to_smt_datatype_injective_of_wf_rec hdTail heTail hDtailWF
                  subst c'
                  subst dt'
                  rfl
termination_by sizeOf d

/-- EO datatype constructor translation is injective for well-formed constructors. -/
theorem eo_to_smt_datatype_cons_injective_of_wf_rec
    {c e : DatatypeCons} {CF C : SmtDatatypeCons}
    (hc : __eo_to_smt_datatype_cons c = C)
    (he : __eo_to_smt_datatype_cons e = C)
    (hWF : __smtx_dt_cons_wf_rec CF C = true) :
    c = e := by
  cases C with
  | unit =>
      cases c <;> cases e <;> simp [__eo_to_smt_datatype_cons] at hc he ⊢
  | cons A Ctail =>
      cases hCF : CF with
      | unit =>
          exfalso
          rw [hCF] at hWF
          cases A <;> simp [__smtx_dt_cons_wf_rec, native_ite] at hWF
      | cons AF CtailF =>
          rw [hCF] at hWF
          cases c with
          | unit => simp [__eo_to_smt_datatype_cons] at hc
          | cons T ct =>
              cases e with
              | unit => simp [__eo_to_smt_datatype_cons] at he
              | cons U cu =>
                  simp [__eo_to_smt_datatype_cons] at hc he
                  rcases hc with ⟨hT, hct⟩
                  rcases he with ⟨hU, hcu⟩
                  have hTU : T = U := by
                    by_cases hRef : ∃ s, A = SmtType.TypeRef s
                    · -- Head field consumed via the substitution recursion point: `A` is a bare
                      -- `TypeRef s`, so `T`/`U` are both forced to be `DatatypeTypeRef s` directly
                      -- (no well-formedness reasoning needed for this shortcut).
                      obtain ⟨s, hAs⟩ := hRef
                      have hTeq : T = Term.DatatypeTypeRef s :=
                        eo_to_smt_type_eq_typeref (by rw [hT, hAs])
                      have hUeq : U = Term.DatatypeTypeRef s :=
                        eo_to_smt_type_eq_typeref (by rw [hU, hAs])
                      rw [hTeq, hUeq]
                    · -- `A` is not a bare `TypeRef`. Recovering the *diagonal* field
                      -- well-formedness `wf_rec A A` from the "full" `wf_rec AF A` is only sound
                      -- when `AF` is a genuine one-step unfold of `A` (i.e. `AF = subst s d0 A` for
                      -- the enclosing datatype `(s, d0)`): otherwise a pathological `CF` breaks it.
                      -- Concretely, with `CF`/`AF` unconstrained, `AF = SmtType.Bool` and
                      -- `A = SmtType.Datatype sA dA` (with `dA` carrying a `None` field) satisfies
                      -- `dt_cons_wf_rec (cons AF _) (cons A _) = true` (second pattern:
                      -- `inhabited Bool && wf_rec Bool (Datatype …) = true && true`), yet `A = tr T`
                      -- is not injective there — so `wf_rec A A` is genuinely *false* while `hWF`
                      -- holds. Making this branch sound requires restating the whole injective
                      -- cluster to thread the enclosing `(s, d0)` (so the full sides are provably
                      -- `subst s d0 _`), which cascades to its 40+ external call sites; it is the
                      -- same "relate the unfolded form to the original under mutual recursion" gap
                      -- as the `eo_to_smt_*_substitute` cluster in `EoTypeofCore`. Left as `sorry`.
                      have hDiag : __smtx_dt_cons_wf_rec
                          (SmtDatatypeCons.cons A Ctail) (SmtDatatypeCons.cons A Ctail) = true := by
                        sorry
                      have hFieldWF : smtx_type_field_wf_rec A native_reflist_nil :=
                        smtx_type_field_wf_rec_of_cons_wf (fun s => by
                          rintro rfl; exact hRef ⟨s, rfl⟩) hDiag
                      exact eo_to_smt_type_injective_of_field_wf_rec hT hU hFieldWF
                  have hTailWF : __smtx_dt_cons_wf_rec CtailF Ctail = true :=
                    smtx_dt_cons_wf_rec_tail_of_true hWF
                  have hTail : ct = cu :=
                    eo_to_smt_datatype_cons_injective_of_wf_rec hct hcu hTailWF
                  subst U
                  subst cu
                  rfl
termination_by sizeOf c

end

/-- EO type translation never produces a tuple-private type reference. -/
theorem eo_to_smt_type_ne_tuple_typeref
    (T : Term) :
    __eo_to_smt_type T ≠ SmtType.TypeRef (native_string_lit "@Tuple") := by
  intro h
  have hT : T = Term.DatatypeTypeRef (native_string_lit "@Tuple") := eo_to_smt_type_eq_typeref h
  subst T
  change native_ite (__eo_reserved_datatype_name (native_string_lit "@Tuple")) SmtType.None
      (SmtType.TypeRef (native_string_lit "@Tuple")) = SmtType.TypeRef (native_string_lit "@Tuple") at h
  rw [show __eo_reserved_datatype_name (native_string_lit "@Tuple") = true by native_decide] at h
  simp [native_ite] at h

/--
If an EO term translates as a well-formed SMT type, the EO term itself has EO
type `Type`.

Datatype fields are the one place where SMT permits recursive `TypeRef`s, so
the tuple case handles `TypeRef` fields by inverting `__eo_to_smt_type`
directly and uses recursive well-formedness for all other field types.
-/
theorem eo_typeof_type_of_smt_type_wf_rec :
    (T : Term) ->
    __smtx_type_wf_rec (__eo_to_smt_type T) (__eo_to_smt_type T) = true ->
    __eo_typeof T = Term.Type
  | Term.UOp op, hWF => by
      cases op <;> simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF ⊢ <;>
        first | rfl | contradiction
  | Term.__eo_List, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.__eo_List_nil, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.__eo_List_cons, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Bool, hWF => rfl
  | Term.Boolean b, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Numeral n, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Rational r, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.String s, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Binary w n, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Type, hWF => rfl
  | Term.Stuck, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Apply f x, hWF => by
      cases f with
      | UOp op =>
          cases op <;> try (simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF)
          case BitVec =>
            cases x <;> try (simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF)
            case Numeral n =>
              change __eo_typeof_BitVec (__eo_typeof (Term.Numeral n)) = Term.Type
              rfl
          case Seq =>
            have hSeqWf := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
              (SmtType.Seq (__eo_to_smt_type x)) (by
                simpa [__eo_to_smt_type] using hWF)
            have hxWF := seq_type_wf_rec_component_of_wf hSeqWf
            have hx := eo_typeof_type_of_smt_type_wf_rec x hxWF
            change __eo_typeof_Seq (__eo_typeof x) = Term.Type
            rw [hx]
            rfl
          case Set =>
            have hSetWf := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
              (SmtType.Set (__eo_to_smt_type x)) (by
                simpa [__eo_to_smt_type] using hWF)
            have hxWF := set_type_wf_rec_component_of_wf hSetWf
            have hx := eo_typeof_type_of_smt_type_wf_rec x hxWF
            change __eo_typeof_Seq (__eo_typeof x) = Term.Type
            rw [hx]
            rfl
          all_goals try contradiction
      | Apply g y =>
          cases g with
          | FunType =>
              have hOuter := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type y)
                (__smtx_typeof_guard (__eo_to_smt_type x)
                  (native_ite
                    (__smtx_is_finite_type
                      (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))) (by
                  simpa [__eo_to_smt_type] using hWF)
              have hFun := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
                (native_ite
                  (__smtx_is_finite_type
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)))
                  (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))
                  (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))) hOuter
              cases hFin :
                  __smtx_is_finite_type
                    (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                simp [native_ite, hFin, __smtx_type_wf_rec] at hFun
          | UOp op =>
              cases op <;> try (simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF)
              case Array =>
                have hOuter := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type y)
                  (__smtx_typeof_guard (__eo_to_smt_type x)
                    (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x))) (by
                    simpa [__eo_to_smt_type] using hWF)
                have hMap := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type x)
                  (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x)) hOuter
                rcases map_type_wf_rec_components_of_wf hMap with ⟨hyWF, hxWF⟩
                have hy := eo_typeof_type_of_smt_type_wf_rec y hyWF
                have hx := eo_typeof_type_of_smt_type_wf_rec x hxWF
                change __eo_typeof__at__at_Pair (__eo_typeof y) (__eo_typeof x) = Term.Type
                rw [hy, hx]
                rfl
              case Tuple =>
                have hRawWf :
                    __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) =
                      true := by
                  cases hRaw :
                      __smtx_type_wf
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) <;>
                    simp [hRaw, __smtx_type_wf_rec, __eo_to_smt_type] at hWF ⊢
                have hRawRec :
                    __smtx_type_wf_rec
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x))
                        (__eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x)) =
                      true := by
                  have hNotReg :
                      __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) ≠
                        SmtType.RegLan :=
                    eo_to_smt_type_tuple_ne_reglan (__eo_to_smt_type y) (__eo_to_smt_type x)
                  have hNotFun :
                      ∀ A B : SmtType,
                        __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) ≠
                          SmtType.FunType A B := by
                    intro A B
                    exact eo_to_smt_type_tuple_ne_fun (__eo_to_smt_type y) (__eo_to_smt_type x) A B
                  have hNotIFun :
                      ∀ A B : SmtType,
                        __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) ≠
                          SmtType.FunType A B := by
                    intro A B
                    exact eo_to_smt_type_tuple_ne_ifun (__eo_to_smt_type y) (__eo_to_smt_type x) A B
                  cases hTuple :
                      __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) <;>
                    simp [hTuple, __smtx_type_wf, __smtx_type_wf_component,
                      native_and] at hRawWf hNotReg ⊢
                  case FunType A B =>
                    exact False.elim (hNotFun A B hTuple)
                  all_goals first | contradiction | exact hRawWf.2
                -- Substitution is a no-op on the tuple's fields (`translate y`/`translate x`), because
                -- a validly-typed argument never translates to something bearing a reserved-name
                -- `TypeRef` at a substitution-reachable position. `tuple_diag_wf_components` packages
                -- this to hand back the component diagonal well-formedness, from which the elements
                -- have EO type `Type` by recursion.
                have hNN :
                    __eo_to_smt_type_tuple (__eo_to_smt_type y) (__eo_to_smt_type x) ≠
                      SmtType.None := by
                  intro hNone
                  rw [hNone] at hRawWf
                  simp [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
                    native_and] at hRawWf
                obtain ⟨hyWF, hxWF⟩ := tuple_diag_wf_components y x hRawRec hNN
                have hy := eo_typeof_type_of_smt_type_wf_rec y hyWF
                have hx := eo_typeof_type_of_smt_type_wf_rec x hxWF
                change __eo_typeof__at__at_Pair (__eo_typeof y) (__eo_typeof x) = Term.Type
                rw [hy, hx]
                rfl
          | _ => simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
      | _ => simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.FunType, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.Var name T, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.DatatypeType s d, hWF => rfl
  | Term.DatatypeTypeRef s, hWF => rfl
  | Term.DtcAppType T U, hWF => by
      have hInner := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type T)
        (__smtx_typeof_guard (__eo_to_smt_type U)
          (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U))) (by
          simpa [__eo_to_smt_type] using hWF)
      have hDtc := smtx_type_wf_rec_guard_of_true (__eo_to_smt_type U)
        (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)) hInner
      simp [__smtx_type_wf_rec] at hDtc
  | Term.DtCons s d i, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.DtSel s d i j, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.USort i, hWF => rfl
  | Term.UConst i T, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.seq_empty T, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term.set_empty T, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term._at_quantifiers_skolemize q idx, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
  | Term._at_const v T, hWF => by
      simp [__eo_to_smt_type, __smtx_type_wf_rec] at hWF
termination_by T => sizeOf T

theorem eo_typeof_type_of_smt_type_wf
    (T : Term)
    (h : __smtx_type_wf (__eo_to_smt_type T) = true) :
    __eo_typeof T = Term.Type := by
  by_cases hReg : __eo_to_smt_type T = SmtType.RegLan
  · rw [eo_to_smt_type_eq_reglan hReg]
    rfl
  · by_cases hFun : ∃ A B : SmtType, __eo_to_smt_type T = SmtType.FunType A B
    · rcases hFun with ⟨A, B, hTy⟩
      rcases eo_to_smt_type_eq_fun hTy with ⟨U, V, rfl, hU, hV⟩
      rcases fun_type_wf_rec_components_of_wf (by simpa [hTy] using h) with ⟨hURec, hVRec⟩
      have hUType := eo_typeof_type_of_smt_type_wf_rec U (by
        simpa [hU] using hURec)
      have hVType := eo_typeof_type_of_smt_type_wf_rec V (by
        simpa [hV] using hVRec)
      change __eo_typeof_fun_type (__eo_typeof U) (__eo_typeof V) = Term.Type
      rw [hUType, hVType]
      rfl
    · by_cases hIFun : ∃ A B : SmtType, __eo_to_smt_type T = SmtType.FunType A B
      · rcases hIFun with ⟨A, B, hTy⟩
        rcases eo_to_smt_type_eq_ifun hTy with ⟨U, V, rfl, hU, hV⟩
        rcases ifun_type_wf_rec_components_of_wf (by simpa [hTy] using h) with ⟨hURec, hVRec⟩
        have hUType := eo_typeof_type_of_smt_type_wf_rec U (by
          simpa [hU] using hURec)
        have hVType := eo_typeof_type_of_smt_type_wf_rec V (by
          simpa [hV] using hVRec)
        change __eo_typeof_fun_type (__eo_typeof U) (__eo_typeof V) = Term.Type
        rw [hUType, hVType]
        rfl
      · exact eo_typeof_type_of_smt_type_wf_rec T (by
          cases hTy : __eo_to_smt_type T <;>
            simp [hTy, __smtx_type_wf, __smtx_type_wf_component,
              native_and] at h hReg hFun hIFun ⊢
          all_goals first | contradiction | exact h.2)

theorem eo_typeof_type_of_smt_type_field_wf_rec
    (T : Term) (refs : RefList)
    (h : smtx_type_field_wf_rec (__eo_to_smt_type T) refs) :
    __eo_typeof T = Term.Type := by
  cases hTy : __eo_to_smt_type T
  case TypeRef s =>
    have hT : T = Term.DatatypeTypeRef s := eo_to_smt_type_eq_typeref hTy
    subst T
    rfl
  all_goals
    exact eo_typeof_type_of_smt_type_wf_rec T (by
      simpa [smtx_type_field_wf_rec, hTy] using h)

/-- Recovers the translated EO type from an SMT typing equality using an explicit IH. -/
theorem eo_to_smt_type_typeof_of_smt_type_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof t) = T := by
  have hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [h]
    exact hT
  exact (ih hNN).symm.trans h

/-- Recovers the exact EO type from an SMT typing equality and field well-formedness. -/
theorem eo_typeof_eq_of_smt_type_from_ih_field_wf
    (t U : Term) {T : SmtType} {refs : RefList}
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = T)
    (hU : __eo_to_smt_type U = T)
    (hWF : smtx_type_field_wf_rec T refs) :
    __eo_typeof t = U := by
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    cases T <;> simp [smtx_type_field_wf_rec, __smtx_type_wf_rec] at hWF hNone
  have hType :=
    eo_to_smt_type_typeof_of_smt_type_from_ih t ih h hTNN
  exact eo_to_smt_type_injective_of_field_wf_rec hType hU hWF

/-- An explicit IH plus SMT `Bool` typing recovers EO `Bool`. -/
theorem eo_typeof_eq_bool_of_smt_bool_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Bool) :
    __eo_typeof t = Term.Bool := by
  exact eo_to_smt_type_eq_bool
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT `Int` typing recovers EO `Int`. -/
theorem eo_typeof_eq_int_of_smt_int_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    __eo_typeof t = Term.UOp UserOp.Int := by
  exact eo_to_smt_type_eq_int
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT `Real` typing recovers EO `Real`. -/
theorem eo_typeof_eq_real_of_smt_real_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __eo_typeof t = Term.UOp UserOp.Real := by
  exact eo_to_smt_type_eq_real
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT regular-language typing recovers EO `RegLan`. -/
theorem eo_typeof_eq_reglan_of_smt_reglan_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.RegLan) :
    __eo_typeof t = Term.UOp UserOp.RegLan := by
  exact eo_to_smt_type_eq_reglan
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT `Seq Char` typing recovers EO string type. -/
theorem eo_typeof_eq_seq_char_of_smt_seq_char_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  exact eo_to_smt_type_eq_seq_char
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT sequence typing recovers the EO sequence shape. -/
theorem eo_typeof_eq_seq_of_smt_seq_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    ∃ U, __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U ∧ __eo_to_smt_type U = T := by
  exact eo_to_smt_type_eq_seq
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT set typing recovers the EO set shape. -/
theorem eo_typeof_eq_set_of_smt_set_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Set T) :
    ∃ U, __eo_typeof t = Term.Apply (Term.UOp UserOp.Set) U ∧ __eo_to_smt_type U = T := by
  exact eo_to_smt_type_eq_set
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

/-- An explicit IH plus SMT bitvector typing recovers EO `BitVec`. -/
theorem eo_typeof_eq_bitvec_of_smt_bitvec_from_ih
    (t : Term)
    (ih :
      __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
      __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t))
    (w : native_Nat)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) := by
  exact eo_to_smt_type_eq_bitvec
    (eo_to_smt_type_typeof_of_smt_type_from_ih t ih h (by simp))

end TranslationProofs
