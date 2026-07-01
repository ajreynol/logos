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
            -- TODO(typeWf-0701 aliasing refactor): re-derive without the old reflist-scoped
            -- `native_reflist_insert refs "@Tuple"` device (no longer meaningful under the new
            -- two-argument `__smtx_type_wf_rec`/`__smtx_dt_wf_rec`). Needs the same "substitution
            -- is a no-op on tuple field positions" argument as the `sorry` above and in
            -- `eo_typeof_type_of_smt_type_wf_rec`'s Tuple case.
            have hyEq : yT = yU := by sorry
            have hxEq : xT = xU := by sorry
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
termination_by sizeOf A

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
termination_by sizeOf D

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
                    · -- `A` is not a bare `TypeRef`, so the substitution at this field is a no-op
                      -- (`__smtx_type_substitute` only ever rewrites a `TypeRef` matching the
                      -- substituted name) and `AF`'s head coincides with `A`.
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
termination_by sizeOf C

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
                -- TODO(typeWf-0701 aliasing refactor): re-derive without the old reflist-scoped
                -- `smtx_dt_cons_wf_rec_tail_of_true`/`smtx_type_field_wf_rec_of_cons_wf` device.
                -- The natural replacement needs "substitution is a no-op on the tuple's head field
                -- `translate y`", which holds because a validly-typed `y` never translates to
                -- something containing `TypeRef "@Tuple"` (that name is reserved and therefore
                -- never a valid `DatatypeTypeRef`, at any depth) — a genuinely different, purely
                -- structural argument than the old reflist "well-formed ⟹ no aliasing" one. Left as
                -- `sorry`, matching the SmtFreeRefs.lift_noop_of_wf_no_dt_* gap this feeds into.
                sorry
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
