import CpcMicro.Spec

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-- Shows that EO translation never produces the bare SMT term `not`. -/
theorem eo_to_smt_ne_not (t : Term) :
    __eo_to_smt t ≠ SmtTerm.not := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `or`. -/
theorem eo_to_smt_ne_or (t : Term) :
    __eo_to_smt t ≠ SmtTerm.or := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `and`. -/
theorem eo_to_smt_ne_and (t : Term) :
    __eo_to_smt t ≠ SmtTerm.and := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `imp`. -/
theorem eo_to_smt_ne_imp (t : Term) :
    __eo_to_smt t ≠ SmtTerm.imp := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `eq`. -/
theorem eo_to_smt_ne_eq (t : Term) :
    __eo_to_smt t ≠ SmtTerm.eq := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `ite`. -/
theorem eo_to_smt_ne_ite (t : Term) :
    __eo_to_smt t ≠ SmtTerm.ite := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `exists`. -/
theorem eo_to_smt_ne_exists (t : Term) (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt t ≠ SmtTerm.exists s T := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `forall`. -/
theorem eo_to_smt_ne_forall (t : Term) (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt t ≠ SmtTerm.forall s T := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `choice`. -/
theorem eo_to_smt_ne_choice (t : Term) (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt t ≠ SmtTerm.choice s T := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `or_partial`. -/
theorem eo_to_smt_ne_or_partial (t : Term) (u : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply SmtTerm.or u := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
      case Apply a b =>
        rw [__eo_to_smt.eq_def] at h
        injection h with hHead _
        exact eo_to_smt_ne_or ((Term.Apply a b).Apply y) hHead

/-- Shows that EO translation never produces the bare SMT term `and_partial`. -/
theorem eo_to_smt_ne_and_partial (t : Term) (u : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply SmtTerm.and u := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
      case Apply a b =>
        rw [__eo_to_smt.eq_def] at h
        injection h with hHead _
        exact eo_to_smt_ne_and ((Term.Apply a b).Apply y) hHead

/-- Shows that EO translation never produces the bare SMT term `imp_partial`. -/
theorem eo_to_smt_ne_imp_partial (t : Term) (u : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply SmtTerm.imp u := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
      case Apply a b =>
        rw [__eo_to_smt.eq_def] at h
        injection h with hHead _
        exact eo_to_smt_ne_imp ((Term.Apply a b).Apply y) hHead

/-- Establishes an equality relating `eo_to_smt_ne` and `partial`. -/
theorem eo_to_smt_ne_eq_partial (t : Term) (u : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply SmtTerm.eq u := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
      case Apply a b =>
        rw [__eo_to_smt.eq_def] at h
        injection h with hHead _
        exact eo_to_smt_ne_eq ((Term.Apply a b).Apply y) hHead

/-- Shows that EO translation never produces the bare SMT term `ite_partial`. -/
theorem eo_to_smt_ne_ite_partial (t : Term) (c : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply SmtTerm.ite c := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
      case Apply a b =>
        rw [__eo_to_smt.eq_def] at h
        injection h with hHead _
        exact eo_to_smt_ne_ite ((Term.Apply a b).Apply y) hHead

/-- Shows that EO translation never produces the bare SMT term `ite_partial2`. -/
theorem eo_to_smt_ne_ite_partial2 (t : Term) (c u : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) u := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
      case Apply a b =>
        rw [__eo_to_smt.eq_def] at h
        injection h with hHead _
        exact eo_to_smt_ne_ite_partial ((Term.Apply a b).Apply y) c hHead

@[simp] theorem eo_to_smt_type_fun (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) =
      __smtx_typeof_guard (__eo_to_smt_type T)
        (__smtx_typeof_guard (__eo_to_smt_type U)
          (SmtType.Map (__eo_to_smt_type T) (__eo_to_smt_type U))) := by
  simp [__eo_to_smt_type]

/-- Shows that `smt_lit_ite` cannot produce a map type when neither branch is a map type. -/
private theorem smt_lit_ite_ne_map
    {c : smt_lit_Bool} {T U A B : SmtType}
    (hT : T ≠ SmtType.Map A B)
    (hU : U ≠ SmtType.Map A B) :
    smt_lit_ite c T U ≠ SmtType.Map A B := by
  cases c
  · simpa [smt_lit_ite] using hU
  · simpa [smt_lit_ite] using hT

/-- Establishes an equality relating `smtx_typeof_guard` and `map_iff`. -/
private theorem smtx_typeof_guard_eq_map_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.Map A B ↔
      T ≠ SmtType.None ∧ U = SmtType.Map A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, smt_lit_ite, smt_lit_Teq]
  · simp [hT, smt_lit_ite, smt_lit_Teq]

/-- Establishes an equality relating `eo_to_smt_type` and `map_iff`. -/
theorem eo_to_smt_type_eq_map_iff
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T = SmtType.Map A B ↔
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
                        (SmtType.Map (__eo_to_smt_type y) (__eo_to_smt_type x))) =
                      SmtType.Map A B := by
                  simpa using h
                rcases smtx_typeof_guard_eq_map_iff.mp hOuter with ⟨hyNN, hInner⟩
                rcases smtx_typeof_guard_eq_map_iff.mp hInner with ⟨hxNN, hMap⟩
                injection hMap with hA hB
                exact ⟨y, x, rfl, hA, hB, hyNN, hxNN⟩
            | _ =>
                simp [__eo_to_smt_type] at h
        | BitVec =>
            cases x <;> simp [__eo_to_smt_type] at h
        | Seq =>
            by_cases hx : __eo_to_smt_type x = SmtType.None
            · simp [__eo_to_smt_type, hx] at h
            · simp [__eo_to_smt_type, hx] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨T1, T2, rfl, hT1, hT2, hT1NN, hT2NN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hT1]
    have hBNN : B ≠ SmtType.None := by
      rwa [← hT2]
    simp [eo_to_smt_type_fun, hT1, hT2, hANN, hBNN,
      __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]

/-- Shows that translated function types never reduce to `bool`. -/
private theorem eo_to_smt_type_fun_ne_bool
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Bool := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

/-- Shows that translated function types never reduce to `int`. -/
private theorem eo_to_smt_type_fun_ne_int
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Int := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

/-- Shows that translated function types never reduce to `real`. -/
private theorem eo_to_smt_type_fun_ne_real
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Real := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

/-- Shows that translated function types never reduce to `reglan`. -/
private theorem eo_to_smt_type_fun_ne_reglan
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.RegLan := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

/-- Shows that translated function types never reduce to `char`. -/
private theorem eo_to_smt_type_fun_ne_char
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Char := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

/-- Shows that translated function types never reduce to `usort`. -/
private theorem eo_to_smt_type_fun_ne_usort
    (T U : Term) (i : eo_lit_Nat) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.USort i := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

/-- Shows that translated function types never reduce to `bitvec`. -/
private theorem eo_to_smt_type_fun_ne_bitvec
    (T U : Term) (w : eo_lit_Int) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.BitVec w := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

/-- Shows that translated function types never reduce to `seq`. -/
private theorem eo_to_smt_type_fun_ne_seq
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Seq V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

/-- Shows that translated function types never reduce to `set`. -/
private theorem eo_to_smt_type_fun_ne_set
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Set V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hT, hU]

/-- Establishes an equality relating `eo_to_smt_type` and `seq_iff`. -/
private theorem eo_to_smt_type_eq_seq_iff
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
            · simp [__eo_to_smt_type, hx] at h
            · simp [__eo_to_smt_type, hx] at h
              exact ⟨x, rfl, h, hx⟩
        | Apply g y =>
            cases g with
            | FunType =>
                exact False.elim (eo_to_smt_type_fun_ne_seq y x A h)
            | _ =>
                simp [__eo_to_smt_type] at h
        | BitVec =>
            cases x <;> simp [__eo_to_smt_type] at h
        | _ =>
            simp [__eo_to_smt_type] at h
    | _ =>
        simp [__eo_to_smt_type] at h
  · rintro ⟨U, rfl, hU, hUNN⟩
    have hANN : A ≠ SmtType.None := by
      rwa [← hU]
    simp [__eo_to_smt_type, hANN, hU]

/-- Establishes an equality relating `eo_to_smt_type` and `bool`. -/
private theorem eo_to_smt_type_eq_bool
    {T : Term} :
    __eo_to_smt_type T = SmtType.Bool ->
    T = Term.Bool := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              intro h
              exact False.elim (eo_to_smt_type_fun_ne_bool y x h)
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x <;> simp [__eo_to_smt_type]
      | Seq =>
          by_cases hx : __eo_to_smt_type x = SmtType.None <;> simp [__eo_to_smt_type, hx]
      | _ =>
          simp [__eo_to_smt_type]
  | _ =>
      simp [__eo_to_smt_type]

/-- Establishes an equality relating `eo_to_smt_type` and `int`. -/
private theorem eo_to_smt_type_eq_int
    {T : Term} :
    __eo_to_smt_type T = SmtType.Int ->
    T = Term.Int := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              intro h
              exact False.elim (eo_to_smt_type_fun_ne_int y x h)
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x <;> simp [__eo_to_smt_type]
      | Seq =>
          by_cases hx : __eo_to_smt_type x = SmtType.None <;> simp [__eo_to_smt_type, hx]
      | _ =>
          simp [__eo_to_smt_type]
  | _ =>
      simp [__eo_to_smt_type]

/-- Establishes an equality relating `eo_to_smt_type` and `real`. -/
private theorem eo_to_smt_type_eq_real
    {T : Term} :
    __eo_to_smt_type T = SmtType.Real ->
    T = Term.Real := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              intro h
              exact False.elim (eo_to_smt_type_fun_ne_real y x h)
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x <;> simp [__eo_to_smt_type]
      | Seq =>
          by_cases hx : __eo_to_smt_type x = SmtType.None <;> simp [__eo_to_smt_type, hx]
      | _ =>
          simp [__eo_to_smt_type]
  | _ =>
      simp [__eo_to_smt_type]

/-- Establishes an equality relating `eo_to_smt_type` and `char`. -/
private theorem eo_to_smt_type_eq_char
    {T : Term} :
    __eo_to_smt_type T = SmtType.Char ->
    T = Term.Char := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              intro h
              exact False.elim (eo_to_smt_type_fun_ne_char y x h)
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x <;> simp [__eo_to_smt_type]
      | Seq =>
          by_cases hx : __eo_to_smt_type x = SmtType.None <;> simp [__eo_to_smt_type, hx]
      | _ =>
          simp [__eo_to_smt_type]
  | _ =>
      simp [__eo_to_smt_type]

/-- Establishes an equality relating `eo_to_smt_type` and `usort`. -/
private theorem eo_to_smt_type_eq_usort
    {T : Term} {i : eo_lit_Nat} :
    __eo_to_smt_type T = SmtType.USort i ->
    T = Term.USort i := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              intro h
              exact False.elim (eo_to_smt_type_fun_ne_usort y x i h)
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x <;> simp [__eo_to_smt_type]
      | Seq =>
          by_cases hx : __eo_to_smt_type x = SmtType.None <;> simp [__eo_to_smt_type, hx]
      | _ =>
          simp [__eo_to_smt_type]
  | _ =>
      simp [__eo_to_smt_type]

/-- Establishes an equality relating `eo_to_smt_type` and `bitvec`. -/
private theorem eo_to_smt_type_eq_bitvec
    {T : Term} {w : eo_lit_Int} :
    __eo_to_smt_type T = SmtType.BitVec w ->
    T = Term.Apply Term.BitVec (Term.Numeral w) := by
  cases T with
  | Apply f x =>
      cases f with
      | BitVec =>
          cases x <;> simp [__eo_to_smt_type]
      | Seq =>
          by_cases hx : __eo_to_smt_type x = SmtType.None <;> simp [__eo_to_smt_type, hx]
      | Apply g y =>
          cases g with
          | FunType =>
              intro h
              exact False.elim (eo_to_smt_type_fun_ne_bitvec y x w h)
          | _ =>
              simp [__eo_to_smt_type]
      | _ =>
          simp [__eo_to_smt_type]
  | _ =>
      simp [__eo_to_smt_type]

/-- Shows that non-`None` SMT target types determine a unique EO source type under `__eo_to_smt_type`. -/
private theorem eo_to_smt_type_non_none_unique :
    ∀ {S : SmtType} {T U : Term},
      __eo_to_smt_type T = S ->
      __eo_to_smt_type U = S ->
      S ≠ SmtType.None ->
      T = U := by
  intro S T U hT hU hNN
  let rec go (S : SmtType) :
      ∀ {T U : Term},
        __eo_to_smt_type T = S ->
        __eo_to_smt_type U = S ->
        S ≠ SmtType.None ->
        T = U := by
    cases S with
    | None =>
        intro T U hT _ hNN
        exact False.elim (hNN rfl)
    | Bool =>
        intro T U hT hU _
        rw [eo_to_smt_type_eq_bool hT, eo_to_smt_type_eq_bool hU]
    | Int =>
        intro T U hT hU _
        rw [eo_to_smt_type_eq_int hT, eo_to_smt_type_eq_int hU]
    | Real =>
        intro T U hT hU _
        rw [eo_to_smt_type_eq_real hT, eo_to_smt_type_eq_real hU]
    | RegLan =>
        intro T U hT _ _
        cases T with
        | Apply f x =>
            cases f with
            | Apply g y =>
                cases g with
                | FunType =>
                    exact False.elim (eo_to_smt_type_fun_ne_reglan y x hT)
                | _ =>
                    simp [__eo_to_smt_type] at hT
            | BitVec =>
                cases x <;> simp [__eo_to_smt_type] at hT
            | Seq =>
                by_cases hx : __eo_to_smt_type x = SmtType.None <;> simp [__eo_to_smt_type, hx] at hT
            | _ =>
                simp [__eo_to_smt_type] at hT
        | _ =>
            simp [__eo_to_smt_type] at hT
    | BitVec w =>
        intro T U hT hU _
        rw [eo_to_smt_type_eq_bitvec hT, eo_to_smt_type_eq_bitvec hU]
    | Set A =>
        intro T U hT _ _
        cases T with
        | Apply f x =>
            cases f with
            | Apply g y =>
                cases g with
                | FunType =>
                    exact False.elim (eo_to_smt_type_fun_ne_set y x A hT)
                | _ =>
                    simp [__eo_to_smt_type] at hT
            | BitVec =>
                cases x <;> simp [__eo_to_smt_type] at hT
            | Seq =>
                by_cases hx : __eo_to_smt_type x = SmtType.None <;> simp [__eo_to_smt_type, hx] at hT
            | _ =>
                simp [__eo_to_smt_type] at hT
        | _ =>
            simp [__eo_to_smt_type] at hT
    | Seq A =>
        intro T U hT hU _
        rcases eo_to_smt_type_eq_seq_iff.mp hT with ⟨T1, rfl, hT1, hT1NN⟩
        rcases eo_to_smt_type_eq_seq_iff.mp hU with ⟨U1, rfl, hU1, hU1NN⟩
        rw [go A hT1 hU1 (by rwa [← hT1])]
    | Char =>
        intro T U hT hU _
        rw [eo_to_smt_type_eq_char hT, eo_to_smt_type_eq_char hU]
    | USort i =>
        intro T U hT hU _
        rw [eo_to_smt_type_eq_usort hT, eo_to_smt_type_eq_usort hU]
    | Map A B =>
        intro T U hT hU _
        rcases eo_to_smt_type_eq_map_iff.mp hT with
          ⟨T1, T2, hT', hT1, hT2, hT1NN, hT2NN⟩
        rcases eo_to_smt_type_eq_map_iff.mp hU with
          ⟨U1, U2, hU', hU1, hU2, hU1NN, hU2NN⟩
        rw [hT', hU', go A hT1 hU1 (by rwa [← hT1]), go B hT2 hU2 (by rwa [← hT2])]
  exact go S hT hU hNN

/-- Derives `eo_to_smt_type_eq` from `non_none`. -/
theorem eo_to_smt_type_eq_of_non_none
    {T U : Term}
    (hEq : __eo_to_smt_type T = __eo_to_smt_type U)
    (hNN : __eo_to_smt_type T ≠ SmtType.None) :
    T = U := by
  exact eo_to_smt_type_non_none_unique rfl hEq.symm hNN

/-- Derives `smtx_typeof_guard_inhabited` from `non_none`. -/
private theorem smtx_typeof_guard_inhabited_of_non_none
    (T U : SmtType) :
    __smtx_typeof_guard_inhabited T U ≠ SmtType.None ->
    __smtx_typeof_guard_inhabited T U = U := by
  intro h
  unfold __smtx_typeof_guard_inhabited at h ⊢
  cases hInh : smt_lit_inhabited_type T <;> simp [smt_lit_ite, hInh] at h ⊢

/-- Derives `smtx_typeof_var` from `non_none`. -/
theorem smtx_typeof_var_of_non_none
    (s : smt_lit_String) (T : SmtType) :
    __smtx_typeof (SmtTerm.Var s T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.Var s T) = T := by
  intro h
  change __smtx_typeof_guard_inhabited T T = T
  exact smtx_typeof_guard_inhabited_of_non_none T T (by simpa [__smtx_typeof] using h)

/-- Derives `smtx_typeof_uconst` from `non_none`. -/
theorem smtx_typeof_uconst_of_non_none
    (s : smt_lit_String) (T : SmtType) :
    __smtx_typeof (SmtTerm.UConst s T) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.UConst s T) = T := by
  intro h
  change __smtx_typeof_guard_inhabited T T = T
  exact smtx_typeof_guard_inhabited_of_non_none T T (by simpa [__smtx_typeof] using h)

/-- Derives `smtx_binary_well_formed` from `non_none`. -/
private theorem smtx_binary_well_formed_of_non_none
    (w n : smt_lit_Int) :
    __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None ->
    smt_lit_zleq 0 w = true ∧
      smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)) = true := by
  intro h
  let g :=
    smt_lit_and (smt_lit_zleq 0 w)
      (smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)))
  have hg : g = true := by
    by_cases h' : g = true
    · exact h'
    · exfalso
      apply h
      change smt_lit_ite g (SmtType.BitVec w) SmtType.None = SmtType.None
      simp [smt_lit_ite, h']
  have hWidth : smt_lit_zleq 0 w = true := by
    cases hw : smt_lit_zleq 0 w <;> simp [g, SmtEval.smt_lit_and, hw] at hg
    rfl
  have hMod : smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)) = true := by
    cases hm : smt_lit_zeq n (smt_lit_mod_total n (smt_lit_int_pow2 w)) <;>
      simp [g, SmtEval.smt_lit_and, hWidth, hm] at hg
    rfl
  exact ⟨hWidth, hMod⟩

/-- Derives `smtx_typeof_binary` from `non_none`. -/
theorem smtx_typeof_binary_of_non_none
    (w n : smt_lit_Int) :
    __smtx_typeof (SmtTerm.Binary w n) ≠ SmtType.None ->
    __smtx_typeof (SmtTerm.Binary w n) = SmtType.BitVec w := by
  intro h
  obtain ⟨hWidth, hMod⟩ := smtx_binary_well_formed_of_non_none w n h
  simp [__smtx_typeof, smt_lit_ite, SmtEval.smt_lit_and, hWidth, hMod]

end TranslationProofs
