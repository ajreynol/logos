import CpcMini.Proofs.Translation.Datatypes

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Computes `__smtx_typeof_guard` under a non-`None` premise. -/
theorem smtx_typeof_guard_of_non_none
    (T U : SmtType) (h : T ≠ SmtType.None) :
    __smtx_typeof_guard T U = U := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq] at h ⊢

/-- A translated sequence type is never an SMT type reference. -/
theorem smtx_typeof_guard_seq_ne_typeref
    (T : SmtType) (s : native_String) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.TypeRef s := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated sequence type is never an SMT datatype. -/
theorem smtx_typeof_guard_seq_ne_datatype
    (T : SmtType) (s : native_String) (d : SmtDatatype) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.Datatype s d := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT type reference. -/
theorem smtx_typeof_guard_fun_ne_typeref
    (T U : SmtType) (s : native_String) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠
      SmtType.TypeRef s := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT datatype. -/
theorem smtx_typeof_guard_fun_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatype) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠
      SmtType.Datatype s d := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT type reference. -/
theorem smtx_typeof_guard_dtc_app_ne_typeref
    (T U : SmtType) (s : native_String) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠
      SmtType.TypeRef s := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT datatype. -/
theorem smtx_typeof_guard_dtc_app_ne_datatype
    (T U : SmtType) (s : native_String) (d : SmtDatatype) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠
      SmtType.Datatype s d := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT function type. -/
theorem smtx_typeof_guard_dtc_app_ne_fun
    (T U A B : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠
      SmtType.FunType A B := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated function type is never an SMT constructor-application type. -/
theorem smtx_typeof_guard_fun_ne_dtc_app
    (T U A B : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠
      SmtType.DtcAppType A B := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated sequence type is never an SMT constructor-application type. -/
theorem smtx_typeof_guard_seq_ne_dtc_app
    (T A B : SmtType) :
    __smtx_typeof_guard T (SmtType.Seq T) ≠ SmtType.DtcAppType A B := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- An EO application never translates to an SMT type reference. -/
theorem eo_to_smt_type_apply_ne_typeref
    (f x : Term) (s : native_String) :
    __eo_to_smt_type (Term.Apply f x) ≠ SmtType.TypeRef s := by
  cases f with
  | BitVec =>
      cases x with
      | Numeral n =>
          by_cases hz : native_zleq 0 n = true
          · simp [__eo_to_smt_type, native_ite, hz]
          · simp [__eo_to_smt_type, native_ite, hz]
      | _ =>
          simp [__eo_to_smt_type]
  | Seq =>
      simpa [__eo_to_smt_type] using
        smtx_typeof_guard_seq_ne_typeref (__eo_to_smt_type x) s
  | Apply f1 x1 =>
      cases f1 <;>
        simp [__eo_to_smt_type, smtx_typeof_guard_fun_ne_typeref]
  | _ =>
      simp [__eo_to_smt_type]

/-- An EO application never translates to an SMT datatype. -/
theorem eo_to_smt_type_apply_ne_datatype
    (f x : Term) (s : native_String) (d : SmtDatatype) :
    __eo_to_smt_type (Term.Apply f x) ≠ SmtType.Datatype s d := by
  cases f with
  | BitVec =>
      cases x with
      | Numeral n =>
          by_cases hz : native_zleq 0 n = true
          · simp [__eo_to_smt_type, native_ite, hz]
          · simp [__eo_to_smt_type, native_ite, hz]
      | _ =>
          simp [__eo_to_smt_type]
  | Seq =>
      simpa [__eo_to_smt_type] using
        smtx_typeof_guard_seq_ne_datatype (__eo_to_smt_type x) s d
  | Apply f1 x1 =>
      cases f1 <;>
        simp [__eo_to_smt_type, smtx_typeof_guard_fun_ne_datatype]
  | _ =>
      simp [__eo_to_smt_type]

/-- A translated EO datatype-constructor application type is never an SMT datatype. -/
theorem eo_to_smt_type_dtc_app_ne_datatype
    (T U : Term) (s : native_String) (d : SmtDatatype) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Datatype s d := by
  simpa [__eo_to_smt_type] using
    smtx_typeof_guard_dtc_app_ne_datatype (__eo_to_smt_type T) (__eo_to_smt_type U) s d

/-- Characterizes `__smtx_typeof_guard` producing a function type. -/
private theorem smtx_typeof_guard_eq_fun_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.FunType A B ↔
      T ≠ SmtType.None ∧ U = SmtType.FunType A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, native_ite, native_Teq]
  · simp [hT, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT function type. -/
theorem eo_to_smt_type_eq_fun_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.FunType A B ↔
      ∃ T1 T2,
        T = Term.Apply (Term.Apply Term.FunType T1) T2 ∧
        __eo_to_smt_type T1 = A ∧
        __eo_to_smt_type T2 = B ∧
        __eo_to_smt_type T1 ≠ SmtType.None ∧
        __eo_to_smt_type T2 ≠ SmtType.None := by
  constructor
  · intro h
    cases T with
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | FunType =>
                have hOuter :
                    __smtx_typeof_guard (__eo_to_smt_type y)
                      (__smtx_typeof_guard (__eo_to_smt_type x)
                        (SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x))) =
                      SmtType.FunType A B := by
                  simpa [__eo_to_smt_type] using h
                rcases smtx_typeof_guard_eq_fun_iff.mp hOuter with ⟨hyNN, hInner⟩
                rcases smtx_typeof_guard_eq_fun_iff.mp hInner with ⟨hxNN, hFun⟩
                injection hFun with hA hB
                exact ⟨y, x, rfl, hA, hB, hyNN, hxNN⟩
            | _ =>
                simp [__eo_to_smt_type] at h
        | BitVec =>
            cases x with
            | Numeral n =>
                by_cases hz : native_zleq 0 n = true <;>
                  simp [__eo_to_smt_type, native_ite, hz] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | Seq =>
            by_cases hx : __eo_to_smt_type x = SmtType.None
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | DtcAppType T1 T2 =>
        exact False.elim
          ((smtx_typeof_guard_dtc_app_ne_fun
              (__eo_to_smt_type T1) (__eo_to_smt_type T2) A B)
            (by simpa [__eo_to_smt_type] using h))
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨T1, T2, rfl, hT1, hT2, hT1NN, hT2NN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hT1]
    have hBNN : B ≠ SmtType.None := by
      rwa [← hT2]
    simp [eo_to_smt_type_fun, hT1, hT2, hANN, hBNN,
      __smtx_typeof_guard, native_ite, native_Teq]

/-- Characterizes `__smtx_typeof_guard` producing a constructor-application type. -/
private theorem smtx_typeof_guard_eq_dtc_app_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.DtcAppType A B ↔
      T ≠ SmtType.None ∧ U = SmtType.DtcAppType A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, native_ite, native_Teq]
  · simp [hT, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT constructor-application type. -/
theorem eo_to_smt_type_eq_dtc_app_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.DtcAppType A B ↔
      ∃ T1 T2,
        T = Term.DtcAppType T1 T2 ∧
        __eo_to_smt_type T1 = A ∧
        __eo_to_smt_type T2 = B ∧
        __eo_to_smt_type T1 ≠ SmtType.None ∧
        __eo_to_smt_type T2 ≠ SmtType.None := by
  constructor
  · intro h
    cases T with
    | DtcAppType T1 T2 =>
        have hOuter :
            __smtx_typeof_guard (__eo_to_smt_type T1)
              (__smtx_typeof_guard (__eo_to_smt_type T2)
                (SmtType.DtcAppType (__eo_to_smt_type T1) (__eo_to_smt_type T2))) =
              SmtType.DtcAppType A B := by
          simpa [__eo_to_smt_type] using h
        rcases smtx_typeof_guard_eq_dtc_app_iff.mp hOuter with ⟨hT1NN, hInner⟩
        rcases smtx_typeof_guard_eq_dtc_app_iff.mp hInner with ⟨hT2NN, hDtc⟩
        injection hDtc with hA hB
        exact ⟨T1, T2, rfl, hA, hB, hT1NN, hT2NN⟩
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | FunType =>
                exact False.elim
                  ((smtx_typeof_guard_fun_ne_dtc_app
                      (__eo_to_smt_type y) (__eo_to_smt_type x) A B)
                    (by simpa [__eo_to_smt_type] using h))
            | _ =>
                simp [__eo_to_smt_type] at h
        | BitVec =>
            cases x with
            | Numeral n =>
                by_cases hz : native_zleq 0 n = true <;>
                  simp [__eo_to_smt_type, native_ite, hz] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | Seq =>
            exact False.elim
              ((smtx_typeof_guard_seq_ne_dtc_app (__eo_to_smt_type x) A B)
                (by simpa [__eo_to_smt_type] using h))
        | _ =>
            simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨T1, T2, rfl, hT1, hT2, hT1NN, hT2NN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hT1]
    have hBNN : B ≠ SmtType.None := by
      rwa [← hT2]
    simp [__eo_to_smt_type, hT1, hT2, hANN, hBNN,
      __smtx_typeof_guard, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT datatype. -/
theorem eo_to_smt_type_eq_datatype_iff
    {T : Term} {s : native_String} {d : SmtDatatype} :
    __eo_to_smt_type T = SmtType.Datatype s d ↔
      ∃ d0,
        T = Term.DatatypeType s d0 ∧
        __eo_to_smt_datatype d0 = d := by
  constructor
  · intro h
    cases T with
    | DatatypeType s0 d0 =>
        injection h with hs hd
        subst hs
        exact ⟨d0, rfl, hd⟩
    | Apply f x =>
        exact False.elim (eo_to_smt_type_apply_ne_datatype f x s d h)
    | DtcAppType T1 T2 =>
        exact False.elim (eo_to_smt_type_dtc_app_ne_datatype T1 T2 s d h)
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨d0, rfl, hd⟩
    simp [__eo_to_smt_type, hd]

/-- Characterizes translated EO types equal to an SMT type reference. -/
theorem eo_to_smt_type_eq_typeref_iff
    {T : Term} {s : native_String} :
    __eo_to_smt_type T = SmtType.TypeRef s ↔
      T = Term.DatatypeTypeRef s := by
  constructor
  · intro h
    cases T with
    | DatatypeTypeRef s0 =>
        simpa [__eo_to_smt_type] using h
    | Apply f x =>
        exact False.elim (eo_to_smt_type_apply_ne_typeref f x s h)
    | DtcAppType T1 T2 =>
        exact False.elim
          ((smtx_typeof_guard_dtc_app_ne_typeref
              (__eo_to_smt_type T1) (__eo_to_smt_type T2) s)
            (by simpa [__eo_to_smt_type] using h))
    | _ =>
        simp [__eo_to_smt_type] at h
  · intro h
    simp [h, __eo_to_smt_type]

/-- A translated function type is never an SMT sequence type. -/
private theorem smtx_typeof_guard_fun_ne_seq
    (T U V : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U)) ≠ SmtType.Seq V := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- A translated datatype-constructor application type is never an SMT sequence type. -/
private theorem smtx_typeof_guard_dtc_app_ne_seq
    (T U V : SmtType) :
    __smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.DtcAppType T U)) ≠ SmtType.Seq V := by
  cases T <;> cases U <;> simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- Characterizes translated EO types equal to an SMT sequence type. -/
theorem eo_to_smt_type_eq_seq_iff
    {T : Term} {A : SmtType} :
    __eo_to_smt_type T = SmtType.Seq A ↔
      ∃ U,
        T = Term.Apply Term.Seq U ∧
        __eo_to_smt_type U = A ∧
        __eo_to_smt_type U ≠ SmtType.None := by
  constructor
  · intro h
    cases T with
    | Apply f x =>
        cases f with
        | Seq =>
            by_cases hx : __eo_to_smt_type x = SmtType.None
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, native_ite, native_Teq] at h
              exact ⟨x, rfl, h, hx⟩
        | Apply g y =>
            cases g with
            | FunType =>
                exact False.elim
                  ((smtx_typeof_guard_fun_ne_seq (__eo_to_smt_type y) (__eo_to_smt_type x) A)
                    (by simpa [__eo_to_smt_type] using h))
            | _ =>
                simp [__eo_to_smt_type] at h
        | BitVec =>
            cases x with
            | Numeral n =>
                by_cases hz : native_zleq 0 n = true <;>
                  simp [__eo_to_smt_type, native_ite, hz] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | DtcAppType T1 T2 =>
        exact False.elim
          ((smtx_typeof_guard_dtc_app_ne_seq (__eo_to_smt_type T1) (__eo_to_smt_type T2) A)
            (by simpa [__eo_to_smt_type] using h))
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨U, rfl, hU, hUNN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hU]
    simp [__eo_to_smt_type, hU, hANN, __smtx_typeof_guard, native_ite, native_Teq]

/-- Characterizes translated EO types equal to SMT `Bool`. -/
theorem eo_to_smt_type_eq_bool
    {T : Term} :
    __eo_to_smt_type T = SmtType.Bool ->
    T = Term.Bool := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x with
          | Numeral n =>
              by_cases hz : native_zleq 0 n = true <;>
                simp [__eo_to_smt_type, native_ite, hz]
          | _ =>
              simp [__eo_to_smt_type]
      | Seq =>
          cases hX : __eo_to_smt_type x <;>
            simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to SMT `Int`. -/
theorem eo_to_smt_type_eq_int
    {T : Term} :
    __eo_to_smt_type T = SmtType.Int ->
    T = Term.Int := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x with
          | Numeral n =>
              by_cases hz : native_zleq 0 n = true <;>
                simp [__eo_to_smt_type, native_ite, hz]
          | _ =>
              simp [__eo_to_smt_type]
      | Seq =>
          cases hX : __eo_to_smt_type x <;>
            simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to SMT `Real`. -/
theorem eo_to_smt_type_eq_real
    {T : Term} :
    __eo_to_smt_type T = SmtType.Real ->
    T = Term.Real := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x with
          | Numeral n =>
              by_cases hz : native_zleq 0 n = true <;>
                simp [__eo_to_smt_type, native_ite, hz]
          | _ =>
              simp [__eo_to_smt_type]
      | Seq =>
          cases hX : __eo_to_smt_type x <;>
            simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to SMT `Char`. -/
theorem eo_to_smt_type_eq_char
    {T : Term} :
    __eo_to_smt_type T = SmtType.Char ->
    T = Term.Char := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x with
          | Numeral n =>
              by_cases hz : native_zleq 0 n = true <;>
                simp [__eo_to_smt_type, native_ite, hz]
          | _ =>
              simp [__eo_to_smt_type]
      | Seq =>
          cases hX : __eo_to_smt_type x <;>
            simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to SMT `USort`. -/
theorem eo_to_smt_type_eq_usort
    {T : Term} {i : native_Nat} :
    __eo_to_smt_type T = SmtType.USort i ->
    T = Term.USort i := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x with
          | Numeral n =>
              by_cases hz : native_zleq 0 n = true <;>
                simp [__eo_to_smt_type, native_ite, hz]
          | _ =>
              simp [__eo_to_smt_type]
      | Seq =>
          cases hX : __eo_to_smt_type x <;>
            simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX]
      | _ =>
          simp [__eo_to_smt_type]
  | DtcAppType T U =>
      cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
        simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]
  | _ =>
      simp [__eo_to_smt_type]

/-- Characterizes translated EO types equal to an SMT bit-vector type. -/
theorem eo_to_smt_type_eq_bitvec_iff
    {T : Term} {w : native_Nat} :
    __eo_to_smt_type T = SmtType.BitVec w ↔
      ∃ n : native_Int,
        T = Term.Apply Term.BitVec (Term.Numeral n) ∧
        native_zleq 0 n = true ∧
        native_int_to_nat n = w := by
  constructor
  · intro h
    cases T with
    | Apply f x =>
        cases f with
        | BitVec =>
            cases x with
            | Numeral n =>
                by_cases hz : native_zleq 0 n = true
                · simp [__eo_to_smt_type, native_ite, hz] at h
                  exact ⟨n, rfl, hz, h⟩
                · simp [__eo_to_smt_type, native_ite, hz] at h
            | _ =>
                simp [__eo_to_smt_type] at h
        | Apply g y =>
            cases g with
            | FunType =>
                exact False.elim
                  (by
                    cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                      simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hY, hX] at h)
            | _ =>
                simp [__eo_to_smt_type] at h
        | Seq =>
            cases hX : __eo_to_smt_type x <;>
              simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hX] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | DtcAppType T1 T2 =>
        cases hT : __eo_to_smt_type T1 <;> cases hU : __eo_to_smt_type T2 <;>
          simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq, hT, hU] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨n, rfl, hz, hw⟩
    simp [__eo_to_smt_type, native_ite, hz, hw]

/--
Extracts the EO datatype witness carried by a translated SMT datatype typing
equality.
-/
theorem eo_typeof_eq_translated_eo_datatype_of_smt_datatype
    {x : Term} {s : native_String} {d : SmtDatatype}
    (hRec : __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s d) :
    ∃ d0,
      __eo_typeof x = Term.DatatypeType s d0 ∧
      __eo_to_smt_datatype d0 = d := by
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.Datatype s d := by
    rw [← hRec, hx]
  exact eo_to_smt_type_eq_datatype_iff.mp hTy

/--
Extracts the EO function-type witness carried by a translated SMT function
typing equality.
-/
theorem eo_typeof_eq_translated_eo_fun_of_smt_fun
    {x : Term} {A B : SmtType}
    (hRec : __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.FunType A B) :
    ∃ T1 T2,
      __eo_typeof x = Term.Apply (Term.Apply Term.FunType T1) T2 ∧
      __eo_to_smt_type T1 = A ∧
      __eo_to_smt_type T2 = B ∧
      __eo_to_smt_type T1 ≠ SmtType.None ∧
      __eo_to_smt_type T2 ≠ SmtType.None := by
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.FunType A B := by
    rw [← hRec, hx]
  exact eo_to_smt_type_eq_fun_iff.mp hTy

/--
Extracts the EO constructor-application-type witness carried by a translated
SMT constructor-application typing equality.
-/
theorem eo_typeof_eq_translated_eo_dtc_app_of_smt_dtc_app
    {x : Term} {A B : SmtType}
    (hRec : __smtx_typeof (__eo_to_smt x) = __eo_to_smt_type (__eo_typeof x))
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.DtcAppType A B) :
    ∃ T1 T2,
      __eo_typeof x = Term.DtcAppType T1 T2 ∧
      __eo_to_smt_type T1 = A ∧
      __eo_to_smt_type T2 = B ∧
      __eo_to_smt_type T1 ≠ SmtType.None ∧
      __eo_to_smt_type T2 ≠ SmtType.None := by
  have hTy : __eo_to_smt_type (__eo_typeof x) = SmtType.DtcAppType A B := by
    rw [← hRec, hx]
  exact eo_to_smt_type_eq_dtc_app_iff.mp hTy

/- Proof-side validity predicates for the EO type fragment meant to survive translation. -/
mutual

def eo_type_valid_rec (refs : List native_String) : Term -> Prop
  | Term.Bool => True
  | Term.DatatypeType s d => eo_datatype_valid_rec (s :: refs) d
  | Term.DatatypeTypeRef s => s ∈ refs
  | Term.DtcAppType T U => eo_type_valid_rec [] T ∧ eo_type_valid_rec [] U
  | Term.USort _ => True
  | Term.Apply (Term.Apply Term.FunType T1) T2 =>
      eo_type_valid_rec [] T1 ∧ eo_type_valid_rec [] T2
  | Term.Int => True
  | Term.Real => True
  | Term.Apply Term.BitVec (Term.Numeral n) => 0 <= n
  | Term.Char => True
  | Term.Apply Term.Seq x => eo_type_valid_rec [] x
  | _ => False

def eo_datatype_cons_valid_rec (refs : List native_String) : DatatypeCons -> Prop
  | DatatypeCons.unit => True
  | DatatypeCons.cons T c =>
      eo_type_valid_rec refs T ∧ eo_datatype_cons_valid_rec refs c

def eo_datatype_valid_rec (refs : List native_String) : Datatype -> Prop
  | Datatype.null => True
  | Datatype.sum c d =>
      eo_datatype_cons_valid_rec refs c ∧ eo_datatype_valid_rec refs d

end

/-- Valid EO types always translate to a non-`None` SMT type. -/
theorem eo_type_valid_rec_non_none :
    ∀ {refs : List native_String} {T : Term},
      eo_type_valid_rec refs T -> __eo_to_smt_type T ≠ SmtType.None
  | refs, Term.__eo_pf t, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Int, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.Real, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.BitVec, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Char, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.Seq, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_nil, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.__eo_List_cons, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Bool, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.Boolean b, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Numeral n, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Rational q, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.String s, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Binary w n, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Type, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Stuck, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.USort i, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.FunType, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.Var name ty, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.DatatypeType s d, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.DatatypeTypeRef s, _ => by
      simp [__eo_to_smt_type]
  | refs, Term.DtcAppType T U, h => by
      rcases h with ⟨hT, hU⟩
      have hTNN : __eo_to_smt_type T ≠ SmtType.None := eo_type_valid_rec_non_none hT
      have hUNN : __eo_to_smt_type U ≠ SmtType.None := eo_type_valid_rec_non_none hU
      simp [__eo_to_smt_type, hTNN, hUNN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply (Term.Apply Term.FunType T1) T2, h => by
      rcases h with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None := eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None := eo_type_valid_rec_non_none hT2
      simp [eo_to_smt_type_fun, hT1NN, hT2NN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply Term.BitVec (Term.Numeral n), h => by
      have hz : native_zleq 0 n = true := by
        simpa [native_zleq] using h
      simp [__eo_to_smt_type, native_ite, hz]
  | refs, Term.Apply Term.Seq x, h => by
      have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none h
      simp [__eo_to_smt_type, hxNN, __smtx_typeof_guard, native_ite, native_Teq]
  | refs, Term.Apply f x, h => by
      cases f with
      | BitVec =>
          cases x with
          | Numeral n =>
              have hz : native_zleq 0 n = true := by
                simpa [eo_type_valid_rec, native_zleq] using h
              simp [__eo_to_smt_type, native_ite, hz]
          | _ =>
              simp [eo_type_valid_rec] at h
      | Seq =>
          have hxNN : __eo_to_smt_type x ≠ SmtType.None := by
            have hx : eo_type_valid_rec [] x := by
              simpa [eo_type_valid_rec] using h
            exact eo_type_valid_rec_non_none hx
          simp [__eo_to_smt_type, hxNN, __smtx_typeof_guard, native_ite, native_Teq]
      | Apply g y =>
          cases g with
          | FunType =>
              rcases (by simpa [eo_type_valid_rec] using h :
                eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
              have hyNN : __eo_to_smt_type y ≠ SmtType.None := eo_type_valid_rec_non_none hy
              have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none hx
              simp [eo_to_smt_type_fun, hyNN, hxNN, __smtx_typeof_guard, native_ite, native_Teq]
          | _ =>
              simp [eo_type_valid_rec] at h
      | _ =>
          simp [eo_type_valid_rec] at h
  | refs, Term.DtCons s d i, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.DtSel s d i j, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.UConst i T, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.not, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.or, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.and, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.imp, h => by
      simp [eo_type_valid_rec] at h
  | refs, Term.eq, h => by
      simp [eo_type_valid_rec] at h

/-- `native_int_to_nat` is injective on nonnegative integers. -/
private theorem native_int_to_nat_injective_of_nonneg
    {m n : native_Int}
    (hm : 0 <= m) (hn : 0 <= n)
    (h : native_int_to_nat m = native_int_to_nat n) :
    m = n := by
  rw [← Int.toNat_of_nonneg hm, ← Int.toNat_of_nonneg hn]
  exact congrArg Int.ofNat h

/- On valid EO types, `__eo_to_smt_type` is injective. -/
mutual

private theorem eo_to_smt_type_unique_of_valid_rec
    (refs : List native_String) :
    ∀ {T U : Term},
      eo_type_valid_rec refs T ->
      __eo_to_smt_type T = __eo_to_smt_type U ->
      T = U
  | Term.__eo_pf t, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Int, U, _, hEq => by
      have hU : __eo_to_smt_type U = SmtType.Int := by
        simpa using hEq.symm
      exact (eo_to_smt_type_eq_int hU).symm
  | Term.Real, U, _, hEq => by
      have hU : __eo_to_smt_type U = SmtType.Real := by
        simpa using hEq.symm
      exact (eo_to_smt_type_eq_real hU).symm
  | Term.BitVec, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Char, U, _, hEq => by
      have hU : __eo_to_smt_type U = SmtType.Char := by
        simpa using hEq.symm
      exact (eo_to_smt_type_eq_char hU).symm
  | Term.Seq, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.__eo_List, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.__eo_List_nil, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.__eo_List_cons, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Bool, U, _, hEq => by
      have hU : __eo_to_smt_type U = SmtType.Bool := by
        simpa using hEq.symm
      exact (eo_to_smt_type_eq_bool hU).symm
  | Term.Boolean b, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Numeral n, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Rational q, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.String s, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Binary w n, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Type, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Stuck, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.USort i, U, _, hEq => by
      have hU : __eo_to_smt_type U = SmtType.USort i := by
        simpa using hEq.symm
      exact (eo_to_smt_type_eq_usort hU).symm
  | Term.FunType, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.Var name ty, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.DatatypeType s d, U, hValid, hEq => by
      have hU : __eo_to_smt_type U = SmtType.Datatype s (__eo_to_smt_datatype d) := by
        simpa [__eo_to_smt_type] using hEq.symm
      rcases eo_to_smt_type_eq_datatype_iff.mp hU with ⟨d0, hU', hd0⟩
      subst hU'
      have hd : d = d0 :=
        eo_to_smt_datatype_unique_of_valid_rec (s :: refs) hValid hd0.symm
      cases hd
      rfl
  | Term.DatatypeTypeRef s, U, hValid, hEq => by
      have hU : __eo_to_smt_type U = SmtType.TypeRef s := by
        simpa [__eo_to_smt_type] using hEq.symm
      exact (eo_to_smt_type_eq_typeref_iff.mp hU).symm
  | Term.Apply Term.BitVec (Term.Numeral n), U, hValid, hEq => by
      have hz : native_zleq 0 n = true := by
        simpa [native_zleq] using hValid
      have hU : __eo_to_smt_type U = SmtType.BitVec (native_int_to_nat n) := by
        simpa [__eo_to_smt_type, native_ite, hz] using hEq.symm
      rcases eo_to_smt_type_eq_bitvec_iff.mp hU with ⟨m, hU', hm, hmn⟩
      subst hU'
      have hm' : 0 <= m := by
        simpa [native_zleq] using hm
      have hmn' : m = n :=
        native_int_to_nat_injective_of_nonneg hm' hValid hmn
      cases hmn'
      rfl
  | Term.Apply Term.Seq T1, U, hValid, hEq => by
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None := eo_type_valid_rec_non_none hValid
      have hU : __eo_to_smt_type U = SmtType.Seq (__eo_to_smt_type T1) := by
        simp [__eo_to_smt_type, hT1NN, __smtx_typeof_guard, native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_seq_iff.mp hU with ⟨U1, hU', hU1, _⟩
      subst hU'
      have hSub : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec [] hValid hU1.symm
      cases hSub
      rfl
  | Term.Apply (Term.Apply Term.FunType T1) T2, U, hValid, hEq => by
      rcases hValid with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None := eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None := eo_type_valid_rec_non_none hT2
      have hU :
          __eo_to_smt_type U =
            SmtType.FunType (__eo_to_smt_type T1) (__eo_to_smt_type T2) := by
        simp [eo_to_smt_type_fun, hT1NN, hT2NN, __smtx_typeof_guard,
          native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_fun_iff.mp hU with
        ⟨U1, U2, hU', hU1, hU2, _, _⟩
      subst hU'
      have hSub1 : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec [] hT1 hU1.symm
      have hSub2 : T2 = U2 :=
        eo_to_smt_type_unique_of_valid_rec [] hT2 hU2.symm
      cases hSub1
      cases hSub2
      rfl
  | Term.DtcAppType T1 T2, U, hValid, hEq => by
      rcases hValid with ⟨hT1, hT2⟩
      have hT1NN : __eo_to_smt_type T1 ≠ SmtType.None := eo_type_valid_rec_non_none hT1
      have hT2NN : __eo_to_smt_type T2 ≠ SmtType.None := eo_type_valid_rec_non_none hT2
      have hU :
          __eo_to_smt_type U =
            SmtType.DtcAppType (__eo_to_smt_type T1) (__eo_to_smt_type T2) := by
        simp [__eo_to_smt_type, hT1NN, hT2NN, __smtx_typeof_guard,
          native_ite, native_Teq] at hEq
        simp [hEq]
      rcases eo_to_smt_type_eq_dtc_app_iff.mp hU with
        ⟨U1, U2, hU', hU1, hU2, _, _⟩
      subst hU'
      have hSub1 : T1 = U1 :=
        eo_to_smt_type_unique_of_valid_rec [] hT1 hU1.symm
      have hSub2 : T2 = U2 :=
        eo_to_smt_type_unique_of_valid_rec [] hT2 hU2.symm
      cases hSub1
      cases hSub2
      rfl
  | Term.Apply f x, U, hValid, hEq => by
      cases f with
      | BitVec =>
          cases x with
          | Numeral n =>
              have hz : native_zleq 0 n = true := by
                simpa [eo_type_valid_rec, native_zleq] using hValid
              have hU : __eo_to_smt_type U = SmtType.BitVec (native_int_to_nat n) := by
                simpa [__eo_to_smt_type, native_ite, hz] using hEq.symm
              rcases eo_to_smt_type_eq_bitvec_iff.mp hU with ⟨m, hU', hm, hmn⟩
              subst hU'
              have hm' : 0 <= m := by
                simpa [native_zleq] using hm
              have hmn' : m = n :=
                native_int_to_nat_injective_of_nonneg hm'
                  (by simpa [eo_type_valid_rec] using hValid) hmn
              cases hmn'
              rfl
          | _ =>
              simp [eo_type_valid_rec] at hValid
      | Seq =>
          have hx : eo_type_valid_rec [] x := by
            simpa [eo_type_valid_rec] using hValid
          have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none hx
          have hU : __eo_to_smt_type U = SmtType.Seq (__eo_to_smt_type x) := by
            simpa [__eo_to_smt_type, hxNN, __smtx_typeof_guard, native_ite, native_Teq] using hEq.symm
          rcases eo_to_smt_type_eq_seq_iff.mp hU with ⟨U1, hU', hU1, _⟩
          subst hU'
          have hSub : x = U1 := eo_to_smt_type_unique_of_valid_rec [] hx hU1.symm
          cases hSub
          rfl
      | Apply g y =>
          cases g with
          | FunType =>
              rcases (by simpa [eo_type_valid_rec] using hValid :
                eo_type_valid_rec [] y ∧ eo_type_valid_rec [] x) with ⟨hy, hx⟩
              have hyNN : __eo_to_smt_type y ≠ SmtType.None := eo_type_valid_rec_non_none hy
              have hxNN : __eo_to_smt_type x ≠ SmtType.None := eo_type_valid_rec_non_none hx
              have hU :
                  __eo_to_smt_type U =
                    SmtType.FunType (__eo_to_smt_type y) (__eo_to_smt_type x) := by
                simpa [eo_to_smt_type_fun, hyNN, hxNN, __smtx_typeof_guard,
                  native_ite, native_Teq] using hEq.symm
              rcases eo_to_smt_type_eq_fun_iff.mp hU with
                ⟨U1, U2, hU', hU1, hU2, _, _⟩
              subst hU'
              have hSub1 : y = U1 := eo_to_smt_type_unique_of_valid_rec [] hy hU1.symm
              have hSub2 : x = U2 := eo_to_smt_type_unique_of_valid_rec [] hx hU2.symm
              cases hSub1
              cases hSub2
              rfl
          | _ =>
              simp [eo_type_valid_rec] at hValid
      | _ =>
          simp [eo_type_valid_rec] at hValid
  | Term.DtCons s d i, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.DtSel s d i j, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.UConst i T, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.not, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.or, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.and, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.imp, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid
  | Term.eq, U, hValid, hEq => by
      simp [eo_type_valid_rec] at hValid

private theorem eo_to_smt_datatype_cons_unique_of_valid_rec
    (refs : List native_String) :
    ∀ {c c' : DatatypeCons},
      eo_datatype_cons_valid_rec refs c ->
      __eo_to_smt_datatype_cons c = __eo_to_smt_datatype_cons c' ->
      c = c'
  | DatatypeCons.unit, c', _, hEq => by
      cases c' <;> simp [__eo_to_smt_datatype_cons] at hEq
      rfl
  | DatatypeCons.cons T c, c', hValid, hEq => by
      rcases hValid with ⟨hT, hC⟩
      cases c' with
      | unit =>
          simp [__eo_to_smt_datatype_cons] at hEq
      | cons U c' =>
          simp [__eo_to_smt_datatype_cons] at hEq
          rcases hEq with ⟨hTU, hCC⟩
          have hT' : T = U := eo_to_smt_type_unique_of_valid_rec refs hT hTU
          have hC' : c = c' := eo_to_smt_datatype_cons_unique_of_valid_rec refs hC hCC
          cases hT'
          cases hC'
          rfl

private theorem eo_to_smt_datatype_unique_of_valid_rec
    (refs : List native_String) :
    ∀ {d d' : Datatype},
      eo_datatype_valid_rec refs d ->
      __eo_to_smt_datatype d = __eo_to_smt_datatype d' ->
      d = d'
  | Datatype.null, d', _, hEq => by
      cases d' <;> simp [__eo_to_smt_datatype] at hEq
      rfl
  | Datatype.sum c d, d', hValid, hEq => by
      rcases hValid with ⟨hC, hD⟩
      cases d' with
      | null =>
          simp [__eo_to_smt_datatype] at hEq
      | sum c' d' =>
          simp [__eo_to_smt_datatype] at hEq
          rcases hEq with ⟨hCC, hDD⟩
          have hC' : c = c' := eo_to_smt_datatype_cons_unique_of_valid_rec refs hC hCC
          have hD' : d = d' := eo_to_smt_datatype_unique_of_valid_rec refs hD hDD
          cases hC'
          cases hD'
          rfl

end

/-- Injectivity of EO-to-SMT type translation on the proof-side valid fragment. -/
theorem eo_to_smt_type_eq_of_valid_rec
    {refs : List native_String} {T U : Term}
    (hValid : eo_type_valid_rec refs T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_unique_of_valid_rec refs hValid hEq

/-- Top-level specialization of `eo_to_smt_type_eq_of_valid_rec`. -/
theorem eo_to_smt_type_eq_of_valid
    {T U : Term}
    (hValid : eo_type_valid_rec [] T)
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U) :
    T = U := by
  exact eo_to_smt_type_eq_of_valid_rec hValid hEq

/-- Converts a reflected ref-list membership test into propositional membership. -/
private theorem native_reflist_contains_true
    {refs : List native_String} {s : native_String}
    (h : native_reflist_contains refs s = true) :
    s ∈ refs := by
  simpa [native_reflist_contains] using h

/-- Decomposes `if a then b else false = true` into its two boolean witnesses. -/
private theorem native_ite_false_eq_true
    {a b : native_Bool}
    (h : native_ite a b false = true) :
    a = true ∧ b = true := by
  cases ha : a <;> cases hb : b <;> simp [native_ite, ha, hb] at h
  exact ⟨rfl, rfl⟩

/-- A well-formed guarded sequence type has a well-formed element type. -/
private theorem smtx_type_wf_rec_guard_seq_true
    (refs : List native_String) (T : SmtType)
    (h : __smtx_type_wf_rec (__smtx_typeof_guard T (SmtType.Seq T)) refs = true) :
    __smtx_type_wf_rec T [] = true := by
  cases T <;>
    simp [__smtx_typeof_guard, __smtx_type_wf_rec, native_ite, native_Teq] at h ⊢ <;>
    simpa using h

/-- A well-formed guarded function type has well-formed domain and codomain. -/
private theorem smtx_type_wf_rec_guard_fun_true
    (refs : List native_String) (T U : SmtType)
    (h :
      __smtx_type_wf_rec
        (__smtx_typeof_guard T (__smtx_typeof_guard U (SmtType.FunType T U))) refs = true) :
    __smtx_type_wf_rec T [] = true ∧
      __smtx_type_wf_rec U [] = true := by
  cases T <;> cases U <;>
    simp [__smtx_typeof_guard, __smtx_type_wf_rec, native_ite, native_Teq,
      SmtEval.native_and] at h ⊢ <;>
    simpa using h

/- Well-formed translated EO datatypes have valid EO field shapes. -/
mutual

theorem eo_type_valid_of_smt_wf_rec
    (refs : List native_String) :
    ∀ {T : Term},
      __smtx_type_wf_rec (__eo_to_smt_type T) refs = true ->
      eo_type_valid_rec refs T
  | T, h => by
      cases T with
      | Bool =>
          simp [eo_type_valid_rec]
      | Int =>
          simp [eo_type_valid_rec]
      | Real =>
          simp [eo_type_valid_rec]
      | Char =>
          simp [eo_type_valid_rec]
      | USort i =>
          simp [eo_type_valid_rec]
      | DatatypeType s d =>
          simpa [eo_type_valid_rec, __eo_to_smt_type, __smtx_type_wf_rec] using
            eo_datatype_valid_of_smt_wf_rec (s :: refs) h
      | DatatypeTypeRef s =>
          have : False := by
            simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
          exact False.elim this
      | DtcAppType T U =>
          have : False := by
            cases hT : __eo_to_smt_type T <;>
            cases hU : __eo_to_smt_type U <;>
              simp [__eo_to_smt_type, __smtx_type_wf_rec, __smtx_typeof_guard, native_ite,
                native_Teq, hT, hU] at h
          exact False.elim this
      | Apply f x =>
          cases f with
          | Seq =>
              have hx : __smtx_type_wf_rec (__eo_to_smt_type x) [] = true := by
                exact smtx_type_wf_rec_guard_seq_true refs (__eo_to_smt_type x)
                  (by simpa [__eo_to_smt_type] using h)
              exact eo_type_valid_of_smt_wf_rec [] hx
          | BitVec =>
              cases x with
              | Numeral n =>
                  have hz : native_zleq 0 n = true := by
                    by_cases hz : native_zleq 0 n = true
                    · exact hz
                    · exfalso
                      simp [__eo_to_smt_type, __smtx_type_wf_rec, native_ite, hz] at h
                  simpa [eo_type_valid_rec, native_zleq] using hz
              | _ =>
                  have : False := by
                    simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
                  exact False.elim this
          | Apply g y =>
              cases g with
              | FunType =>
                  have hPair :
                      __smtx_type_wf_rec (__eo_to_smt_type y) [] = true ∧
                        __smtx_type_wf_rec (__eo_to_smt_type x) [] = true := by
                    exact smtx_type_wf_rec_guard_fun_true refs (__eo_to_smt_type y) (__eo_to_smt_type x)
                      (by simpa [eo_to_smt_type_fun] using h)
                  exact ⟨eo_type_valid_of_smt_wf_rec [] hPair.1, eo_type_valid_of_smt_wf_rec [] hPair.2⟩
              | _ =>
                  have : False := by
                    simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
                  exact False.elim this
          | _ =>
              have : False := by
                simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
              exact False.elim this
      | _ =>
          have : False := by
            simp [__eo_to_smt_type, __smtx_type_wf_rec] at h
          exact False.elim this

theorem eo_datatype_cons_valid_of_smt_wf_rec
    (refs : List native_String) :
    ∀ {c : DatatypeCons},
      __smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs = true ->
      eo_datatype_cons_valid_rec refs c
  | DatatypeCons.unit, _ => by
      simp [eo_datatype_cons_valid_rec]
  | DatatypeCons.cons T c, h => by
      cases hTy : __eo_to_smt_type T
      case None =>
        have : False := by
          simp [__eo_to_smt_datatype_cons, __smtx_dt_cons_wf_rec, __smtx_type_wf_rec,
            native_ite, hTy] at h
        exact False.elim this
      case TypeRef s =>
        have hT : T = Term.DatatypeTypeRef s :=
          eo_to_smt_type_eq_typeref_iff.mp hTy
        subst hT
        have h' :
            native_ite (native_reflist_contains refs s)
              (__smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs) false = true := by
          simpa [__eo_to_smt_datatype_cons, __eo_to_smt_type, __smtx_dt_cons_wf_rec] using h
        rcases native_ite_false_eq_true h' with ⟨hs, hC⟩
        exact ⟨native_reflist_contains_true hs, eo_datatype_cons_valid_of_smt_wf_rec refs hC⟩
      all_goals
        have h' :
            native_ite (__smtx_type_wf_rec (__eo_to_smt_type T) refs)
              (__smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs) false = true := by
          simpa [__eo_to_smt_datatype_cons, __smtx_dt_cons_wf_rec, hTy] using h
        rcases native_ite_false_eq_true h' with ⟨hT, hC⟩
        exact ⟨eo_type_valid_of_smt_wf_rec refs hT, eo_datatype_cons_valid_of_smt_wf_rec refs hC⟩

theorem eo_datatype_valid_of_smt_wf_rec
    (refs : List native_String) :
    ∀ {d : Datatype},
      __smtx_dt_wf_rec (__eo_to_smt_datatype d) refs = true ->
      eo_datatype_valid_rec refs d
  | Datatype.null, _ => by
      simp [eo_datatype_valid_rec]
  | Datatype.sum c d, h => by
      have h' :
          native_ite (__smtx_dt_cons_wf_rec (__eo_to_smt_datatype_cons c) refs)
            (__smtx_dt_wf_rec (__eo_to_smt_datatype d) refs) false = true := by
        simpa [__eo_to_smt_datatype, __smtx_dt_wf_rec] using h
      rcases native_ite_false_eq_true h' with ⟨hC, hD⟩
      exact ⟨eo_datatype_cons_valid_of_smt_wf_rec refs hC, eo_datatype_valid_of_smt_wf_rec refs hD⟩

end

/-- A non-`None` well-formedness guard witnesses proof-side EO type validity. -/
theorem eo_type_valid_of_guard_wf_non_none
    {T U : Term}
    (h : __smtx_typeof_guard_wf (__eo_to_smt_type T) (__eo_to_smt_type U) ≠ SmtType.None) :
    eo_type_valid_rec [] T := by
  unfold __smtx_typeof_guard_wf at h
  cases hInh : native_inhabited_type (__eo_to_smt_type T) <;>
    simp [native_ite, hInh] at h
  have hWf : __smtx_type_wf (__eo_to_smt_type T) = true := by
    by_cases h1 : __smtx_type_wf (__eo_to_smt_type T) = true
    · exact h1
    · exfalso
      simp [h1] at h
  change __smtx_type_wf_rec (__eo_to_smt_type T) [] = true at hWf
  exact eo_type_valid_of_smt_wf_rec [] hWf

/-- Translating EO type-reference substitution matches the corresponding SMT substitution step. -/
theorem eo_to_smt_type_substitute_typeref
    (s : native_String) (d : Datatype) :
    ∀ T : Term,
      __eo_to_smt_type
          (native_ite (native_teq T (Term.DatatypeTypeRef s))
            (Term.DatatypeType s d) T) =
        native_ite (native_Teq (__eo_to_smt_type T) (SmtType.TypeRef s))
          (SmtType.Datatype s (__eo_to_smt_datatype d))
          (__eo_to_smt_type T)
  | Term.__eo_pf t => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Int => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Real => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.BitVec => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Char => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Seq => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List_nil => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.__eo_List_cons => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Bool => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Boolean b => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Numeral n => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Rational q => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.String str => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Binary w n => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Type => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Stuck => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Apply f x => by
      have hneq : __eo_to_smt_type (Term.Apply f x) ≠ SmtType.TypeRef s :=
        eo_to_smt_type_apply_ne_typeref f x s
      simp [native_ite, native_teq, native_Teq, hneq]
  | Term.FunType => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.Var name ty => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DatatypeType s2 d2 => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DatatypeTypeRef s2 => by
      by_cases hs : s2 = s
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hs]
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, hs]
  | Term.DtcAppType T U => by
      let V :=
        __smtx_typeof_guard (__eo_to_smt_type T)
          (__smtx_typeof_guard (__eo_to_smt_type U)
            (SmtType.DtcAppType (__eo_to_smt_type T) (__eo_to_smt_type U)))
      have hneq : V ≠ SmtType.TypeRef s := by
        dsimp [V]
        exact smtx_typeof_guard_dtc_app_ne_typeref (__eo_to_smt_type T) (__eo_to_smt_type U) s
      by_cases hV : V = SmtType.TypeRef s
      · exact False.elim (hneq hV)
      · simp [__eo_to_smt_type, native_ite, native_teq, native_Teq, V, hV]
  | Term.DtCons s2 d2 i => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.DtSel s2 d2 i j => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.USort u => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.UConst i T => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.not => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.or => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.and => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.imp => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]
  | Term.eq => by
      simp [__eo_to_smt_type, native_ite, native_teq, native_Teq]

/-- Constructor congruence for SMT datatype constructors. -/
private theorem smt_datatype_cons_congr
    {T1 T2 : SmtType} {c1 c2 : SmtDatatypeCons}
    (hT : T1 = T2) (hc : c1 = c2) :
    SmtDatatypeCons.cons T1 c1 = SmtDatatypeCons.cons T2 c2 := by
  cases hT
  cases hc
  rfl

/-- `__smtx_dtc_substitute` takes its generic branch when the head type is not a datatype. -/
private theorem smtx_dtc_substitute_non_datatype
    (s : native_String) (d : SmtDatatype) (T : SmtType) (c : SmtDatatypeCons)
    (hT : ∀ s2 d2, T ≠ SmtType.Datatype s2 d2) :
    __smtx_dtc_substitute s d (SmtDatatypeCons.cons T c) =
      SmtDatatypeCons.cons
        (native_ite (native_Teq T (SmtType.TypeRef s)) (SmtType.Datatype s d) T)
        (__smtx_dtc_substitute s d c) := by
  cases T <;> simp [__smtx_dtc_substitute, native_ite, native_Teq] at hT ⊢

/-- Recursive calls from a datatype-constructor tail decrease the `Sum` measure. -/
private theorem sum_size_inl_lt_cons (T : Term) (c : DatatypeCons) :
    Sum.elim sizeOf sizeOf ((Sum.inl c : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf (Sum.inl (DatatypeCons.cons T c) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.DatatypeCons.cons.sizeOf_spec]
  omega

/-- Recursive calls into a datatype-valued field decrease the `Sum` measure. -/
private theorem sum_size_inr_lt_datatype_cons
    (s : native_String) (d : Datatype) (c : DatatypeCons) :
    Sum.elim sizeOf sizeOf ((Sum.inr d : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf
        (Sum.inl (DatatypeCons.cons (Term.DatatypeType s d) c) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.DatatypeCons.cons.sizeOf_spec, Eo.Term.DatatypeType.sizeOf_spec]
  omega

/-- Recursive calls from the constructor part of a datatype sum decrease the `Sum` measure. -/
private theorem sum_size_inl_lt_sum (c : DatatypeCons) (d : Datatype) :
    Sum.elim sizeOf sizeOf ((Sum.inl c : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf (Sum.inr (Datatype.sum c d) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.Datatype.sum.sizeOf_spec]
  omega

/-- Recursive calls from the tail part of a datatype sum decrease the `Sum` measure. -/
private theorem sum_size_inr_lt_sum (c : DatatypeCons) (d : Datatype) :
    Sum.elim sizeOf sizeOf ((Sum.inr d : Sum DatatypeCons Datatype)) <
      Sum.elim sizeOf sizeOf (Sum.inr (Datatype.sum c d) : Sum DatatypeCons Datatype) := by
  simp [Sum.elim, Eo.Datatype.sum.sizeOf_spec]
  omega

/--
Auxiliary commutation theorem for EO/SMT datatype substitution, indexed over the
sum of datatype constructors and datatypes so the recursion can descend into
nested datatype fields.
-/
private theorem eo_to_smt_substitute_aux
    (s : native_String) (d : Datatype) :
    ∀ x : Sum DatatypeCons Datatype,
      Sum.elim
        (fun c =>
          __eo_to_smt_datatype_cons (__eo_dtc_substitute s d c) =
            __smtx_dtc_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype_cons c))
        (fun d0 =>
          __eo_to_smt_datatype (__eo_dt_substitute s d d0) =
            __smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d0))
        x
  | .inl DatatypeCons.unit => by
      simp [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute]
  | .inl (DatatypeCons.cons T c) => by
      cases T
      case DatatypeType s2 d2 =>
        by_cases hst : native_streq s s2 = true
        · have hc := eo_to_smt_substitute_aux s d (.inl c)
          simpa [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute,
            native_ite, hst] using hc
        · have hd2 := eo_to_smt_substitute_aux s d (.inr d2)
          have hc := eo_to_smt_substitute_aux s d (.inl c)
          simpa [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute,
            native_ite, hst] using And.intro hd2 hc
      case Apply f x =>
        have hc := eo_to_smt_substitute_aux s d (.inl c)
        dsimp [Sum.elim, __eo_dtc_substitute, __eo_to_smt_datatype_cons]
        rw [smtx_dtc_substitute_non_datatype s (__eo_to_smt_datatype d)
          (__eo_to_smt_type (Term.Apply f x)) (__eo_to_smt_datatype_cons c)]
        · exact smt_datatype_cons_congr
            (eo_to_smt_type_substitute_typeref s d (Term.Apply f x))
            (by simpa using hc)
        · intro s2 d2
          exact eo_to_smt_type_apply_ne_datatype f x s2 d2
      case DtcAppType T1 T2 =>
        have hc := eo_to_smt_substitute_aux s d (.inl c)
        dsimp [Sum.elim, __eo_dtc_substitute, __eo_to_smt_datatype_cons]
        rw [smtx_dtc_substitute_non_datatype s (__eo_to_smt_datatype d)
          (__eo_to_smt_type (Term.DtcAppType T1 T2)) (__eo_to_smt_datatype_cons c)]
        · exact smt_datatype_cons_congr
            (eo_to_smt_type_substitute_typeref s d (Term.DtcAppType T1 T2))
            (by simpa using hc)
        · intro s2 d2
          exact eo_to_smt_type_dtc_app_ne_datatype T1 T2 s2 d2
      all_goals
        have hc := eo_to_smt_substitute_aux s d (.inl c)
        dsimp [__eo_dtc_substitute, __eo_to_smt_datatype_cons, __smtx_dtc_substitute]
        exact smt_datatype_cons_congr
          (eo_to_smt_type_substitute_typeref s d _)
          (by simpa using hc)
  | .inr Datatype.null => by
      simp [__eo_dt_substitute, __eo_to_smt_datatype, __smtx_dt_substitute]
  | .inr (Datatype.sum c d0) => by
      have hc := eo_to_smt_substitute_aux s d (.inl c)
      have hd0 := eo_to_smt_substitute_aux s d (.inr d0)
      simpa [__eo_dt_substitute, __eo_to_smt_datatype, __smtx_dt_substitute] using
        And.intro hc hd0
termination_by x => Sum.elim sizeOf sizeOf x
decreasing_by
  all_goals
    first
    | exact sum_size_inl_lt_cons _ _
    | exact sum_size_inr_lt_datatype_cons _ _ _
    | exact sum_size_inl_lt_sum _ _
    | exact sum_size_inr_lt_sum _ _

/-- EO datatype-constructor substitution commutes with type translation. -/
theorem eo_to_smt_datatype_cons_substitute
    (s : native_String) (d : Datatype) (c : DatatypeCons) :
    __eo_to_smt_datatype_cons (__eo_dtc_substitute s d c) =
      __smtx_dtc_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype_cons c) := by
  simpa using eo_to_smt_substitute_aux s d (.inl c)

/-- EO datatype substitution commutes with type translation. -/
theorem eo_to_smt_datatype_substitute
    (s : native_String) (d : Datatype) (d0 : Datatype) :
    __eo_to_smt_datatype (__eo_dt_substitute s d d0) =
      __smtx_dt_substitute s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d0) := by
  simpa using eo_to_smt_substitute_aux s d (.inr d0)

/-- Selector return typing commutes with EO-to-SMT type translation. -/
theorem eo_to_smt_type_typeof_dt_sel_return :
    ∀ d : Datatype, ∀ i j : native_Nat,
      __eo_to_smt_type (__eo_typeof_dt_sel_return d i j) =
        __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_zero => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons]
  | Datatype.sum (DatatypeCons.cons T c) d, native_nat_zero, native_nat_succ j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return (Datatype.sum c d) native_nat_zero j
  | Datatype.sum c d, native_nat_succ i, j => by
      simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype,
        __eo_to_smt_datatype_cons] using
        eo_to_smt_type_typeof_dt_sel_return d i j
  | Datatype.null, i, j => by
      simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_type]
  | Datatype.sum DatatypeCons.unit d, native_nat_zero, j => by
      cases j <;> simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
        __eo_to_smt_datatype, __eo_to_smt_datatype_cons, __eo_to_smt_type]
termination_by d i j => sizeOf d + i + j

/-- Selector return typing commutes with EO-to-SMT type translation on the EO-side substituted datatype. -/
theorem eo_to_smt_type_typeof_dt_sel_return_on_substituted_datatype
    (s : native_String) (d : Datatype) (i j : native_Nat) :
    __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  simp [__smtx_ret_typeof_sel, eo_to_smt_datatype_substitute,
    eo_to_smt_type_typeof_dt_sel_return]

/--
If the EO argument already has the exact datatype expected by a selector, the
translated EO result type matches the SMT selector return type.
-/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_exact_eo_datatype
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hx : __eo_typeof x = Term.DatatypeType s d) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  simp [__eo_typeof, __eo_typeof_apply, __eo_requires, hx,
    eo_to_smt_type_typeof_dt_sel_return_on_substituted_datatype,
    native_ite, native_teq, native_not]

end TranslationProofs
