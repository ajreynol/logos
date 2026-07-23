module

public import Cpc.SmtModel
import all Cpc.SmtModel

public section

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Smtm

/-!
Basic facts about the declaration-based default generator.

The refactored datatype walk validates a completed constructor before selecting
it.  The mutual induction below proves the corresponding invariant: every
generated default is either unavailable, or both well-typed and canonical.
-/

private def typeDefaultChain : SmtDatatypeCons → SmtType → SmtType
  | SmtDatatypeCons.unit, base => base
  | SmtDatatypeCons.cons T c, base => SmtType.DtcAppType T (typeDefaultChain c base)

private theorem type_default_kernel_strong : ∀ T : SmtType,
    __smtx_type_default T = SmtValue.NotValue ∨
      (__smtx_typeof_value (__smtx_type_default T) = T ∧
       __smtx_value_canonical_bool (__smtx_type_default T) = true) := by
  refine __smtx_type_default.induct
    (motive1 := fun T =>
      __smtx_type_default T = SmtValue.NotValue ∨
        (__smtx_typeof_value (__smtx_type_default T) = T ∧
         __smtx_value_canonical_bool (__smtx_type_default T) = true))
    (motive2 := fun s dd ddF =>
      __smtx_datatype_decl_default s dd ddF = SmtValue.NotValue ∨
        (__smtx_typeof_value (__smtx_datatype_decl_default s dd ddF) =
            SmtType.Datatype s dd ∧
         __smtx_value_canonical_bool
            (__smtx_datatype_decl_default s dd ddF) = true))
    (motive3 := fun s dd n dF ddF =>
      __smtx_datatype_default s dd n dF ddF = SmtValue.NotValue ∨
        (__smtx_typeof_value (__smtx_datatype_default s dd n dF ddF) =
            SmtType.Datatype s dd ∧
         __smtx_value_canonical_bool
            (__smtx_datatype_default s dd n dF ddF) = true))
    (motive4 := fun v dd c ddF => ∀ base,
      __smtx_value_canonical_bool v = true →
      (__smtx_datatype_cons_default v dd c ddF = SmtValue.NotValue ∨
       __smtx_value_canonical_bool
          (__smtx_datatype_cons_default v dd c ddF) = true) ∧
      (__smtx_typeof_value v = typeDefaultChain (__smtx_dtc_resolve c dd) base →
       __smtx_datatype_cons_default v dd c ddF = SmtValue.NotValue ∨
       __smtx_typeof_value (__smtx_datatype_cons_default v dd c ddF) = base))
    (motive5 := fun dd T ddF =>
      __smtx_field_type_default dd T ddF = SmtValue.NotValue ∨
        (__smtx_typeof_value (__smtx_field_type_default dd T ddF) =
            (match T with
             | SmtType.TypeRef s => SmtType.Datatype s dd
             | other => other) ∧
         __smtx_value_canonical_bool
            (__smtx_field_type_default dd T ddF) = true))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro s dd ih
    simpa [__smtx_type_default] using ih
  · right; constructor <;>
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical_bool]
  · right; constructor <;>
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical_bool]
  · right; constructor <;>
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical_bool]
  · right; constructor <;>
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical_bool,
        native_re_canonical, native_re_none]
  · intro w
    right; constructor <;>
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical_bool,
        native_nat_to_int, native_and, native_zleq, native_zeq, native_mod_total,
        native_int_to_nat, native_ite]
  · right; constructor <;>
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical_bool,
        native_char_valid, native_ite]
  · intro T U ih
    rw [__smtx_type_default]
    let field := __smtx_type_default U
    by_cases hv : native_veq field SmtValue.NotValue = true
    · left
      rw [native_ite, if_pos hv]
    · rw [native_ite, if_neg hv]
      rcases ih with hnv | ⟨hty, hcan⟩
      · exact absurd (by simp [field, native_veq, hnv]) hv
      · right
        refine ⟨by simp [__smtx_typeof_value, __smtx_typeof_map_value, hty], ?_⟩
        simp [__smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, hty, hcan, native_ite, native_veq,
          native_and]
  · intro T
    right; constructor
    · simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_map_value,
        __smtx_map_to_set_type]
    · simp [__smtx_type_default, __smtx_value_canonical_bool,
        __smtx_map_canonical, __smtx_map_default_canonical,
        __smtx_msm_get_default, native_and, native_veq, native_ite,
        __smtx_typeof_value]
  · intro T
    right; constructor <;>
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_typeof_seq_value,
        __smtx_value_canonical_bool, __smtx_seq_canonical]
  · intro i
    right; constructor <;>
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro T U
    right; constructor <;>
      simp [__smtx_type_default, __smtx_typeof_value, __smtx_value_canonical_bool]
  · intro T h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    left
    cases T <;> simp_all [__smtx_type_default]
  · intro s dd sF dF ddF ihDt ihDecl
    rw [__smtx_datatype_decl_default]
    by_cases hs : native_streq s sF = true
    · simpa [native_ite, hs] using ihDt
    · simpa [native_ite, hs] using ihDecl
  · intro s dd ddF hnone
    left
    cases ddF with
    | nil => simp [__smtx_datatype_decl_default]
    | cons sF dF tail => exact (hnone sF dF tail rfl).elim
  · intro s dd n cF dF ddF ihCons ihTail
    rw [__smtx_datatype_default]
    let result := __smtx_datatype_cons_default (SmtValue.DtCons s dd n) dd cF ddF
    by_cases hg : native_and (native_not (native_veq result SmtValue.NotValue))
        (native_Teq (__smtx_typeof_value result) (SmtType.Datatype s dd)) = true
    · rw [native_ite, if_pos hg]
      have hparts : result ≠ SmtValue.NotValue ∧
          __smtx_typeof_value result = SmtType.Datatype s dd := by
        simpa [native_and, native_not, native_veq, native_Teq] using hg
      rcases (ihCons (SmtType.Datatype s dd)
          (by simp [__smtx_value_canonical_bool])).1 with hnv | hcan
      · exact (hparts.1 hnv).elim
      · exact Or.inr ⟨hparts.2, hcan⟩
    · rw [native_ite, if_neg hg]
      exact ihTail
  · intro s dd n dF ddF hnone
    left
    cases dF with
    | null => simp [__smtx_datatype_default]
    | sum c tail => exact (hnone c tail rfl).elim
  · intro v dd ddF base hcan
    constructor
    · exact Or.inr (by simpa [__smtx_datatype_cons_default] using hcan)
    · intro hty
      exact Or.inr (by simpa [__smtx_datatype_cons_default, typeDefaultChain] using hty)
  · intro v dd T c ddF field ihField ihTail base hcan
    let R := match T with
      | SmtType.TypeRef s => SmtType.Datatype s dd
      | other => other
    let result := __smtx_datatype_cons_default (SmtValue.Apply v field) dd c ddF
    rw [__smtx_datatype_cons_default.eq_def]
    change
      (native_ite (native_veq field SmtValue.NotValue)
          SmtValue.NotValue result = SmtValue.NotValue ∨
        __smtx_value_canonical_bool
          (native_ite (native_veq field SmtValue.NotValue)
            SmtValue.NotValue result) = true) ∧
      (__smtx_typeof_value v =
          typeDefaultChain (__smtx_dtc_resolve (SmtDatatypeCons.cons T c) dd) base →
        native_ite (native_veq field SmtValue.NotValue)
            SmtValue.NotValue result = SmtValue.NotValue ∨
          __smtx_typeof_value
            (native_ite (native_veq field SmtValue.NotValue)
              SmtValue.NotValue result) = base)
    by_cases hv : native_veq field SmtValue.NotValue = true
    · rw [native_ite, if_pos hv]
      exact ⟨Or.inl rfl, fun _ => Or.inl rfl⟩
    · rw [native_ite, if_neg hv]
      rcases ihField with hnv | ⟨hty, hfieldCan⟩
      · exact absurd (by simp [field, native_veq, hnv]) hv
      · have hfieldCan' : __smtx_value_canonical_bool field = true := by
          simpa only [field] using hfieldCan
        have hty' : __smtx_typeof_value field = R := by
          simpa only [field, R] using hty
        have happCan : __smtx_value_canonical_bool (SmtValue.Apply v field) = true := by
          simp [__smtx_value_canonical_bool, hcan, hfieldCan', native_and]
        have htail := ihTail base happCan
        refine ⟨htail.1, ?_⟩
        intro hvType
        apply htail.2
        have hRne : R ≠ SmtType.None := by
          cases T <;> simp_all [R, field, __smtx_field_type_default,
            __smtx_type_default, native_veq]
        have hchain :
            typeDefaultChain (__smtx_dtc_resolve (SmtDatatypeCons.cons T c) dd) base =
              SmtType.DtcAppType R
                (typeDefaultChain (__smtx_dtc_resolve c dd) base) := by
          cases T <;> rfl
        rw [hchain] at hvType
        rw [__smtx_typeof_value, hvType, hty']
        simp [__smtx_typeof_apply_value, __smtx_typeof_guard,
          native_ite, native_Teq, hRne]
  · intro dd s ddF ih
    simpa [__smtx_field_type_default] using ih
  · intro dd T ddF hnotref ih
    simpa [__smtx_field_type_default, hnotref] using ih


/-- Combined typing and canonicity invariant for generated defaults. -/
theorem type_default_kernel (T : SmtType) :
    (__smtx_type_default T = SmtValue.NotValue ∨
      __smtx_typeof_value (__smtx_type_default T) = T) ∧
    (native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true →
      __smtx_value_canonical_bool (__smtx_type_default T) = true) := by
  rcases type_default_kernel_strong T with hnv | ⟨hty, hcan⟩
  · refine ⟨Or.inl hnv, ?_⟩
    intro _
    simp [hnv, __smtx_value_canonical_bool]
  · exact ⟨Or.inr hty, fun _ => hcan⟩

/-- A default is either unavailable or has the requested type. -/
theorem type_default_notvalue_or_typed (T : SmtType) :
    __smtx_type_default T = SmtValue.NotValue ∨
      __smtx_typeof_value (__smtx_type_default T) = T :=
  (type_default_kernel T).1

/-- A well-typed default value is canonical. -/
theorem type_default_canonical_of_typed (T : SmtType)
    (h : native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true) :
    __smtx_value_canonical_bool (__smtx_type_default T) = true :=
  (type_default_kernel T).2 h

end Smtm
