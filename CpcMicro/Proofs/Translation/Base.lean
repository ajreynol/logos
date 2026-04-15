import CpcMicro.Spec

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

private theorem eo_to_smt_var_ne
    (name T : Term) (u : SmtTerm)
    (hNone : SmtTerm.None ≠ u)
    (hString : ∀ s, SmtTerm.Var s (__eo_to_smt_type T) ≠ u) :
    __eo_to_smt (Term.Var name T) ≠ u := by
  intro h
  cases name with
  | String s =>
      change SmtTerm.Var s (__eo_to_smt_type T) = u at h
      exact hString s h
  | _ =>
      change SmtTerm.None = u at h
      exact hNone h

private theorem eo_to_smt_apply_var_ne
    (name T x : Term) (u : SmtTerm)
    (hNone : SmtTerm.Apply SmtTerm.None (__eo_to_smt x) ≠ u)
    (hString :
      ∀ s, SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x) ≠ u) :
    __eo_to_smt (Term.Apply (Term.Var name T) x) ≠ u := by
  intro h
  cases name with
  | String s =>
      change SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x) = u at h
      exact hString s h
  | _ =>
      change SmtTerm.Apply SmtTerm.None (__eo_to_smt x) = u at h
      exact hNone h

private theorem eo_to_smt_double_apply_var_ne
    (name T y x : Term) (u : SmtTerm)
    (hNone :
      SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y)) (__eo_to_smt x) ≠ u)
    (hString :
      ∀ s,
        SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt y))
          (__eo_to_smt x) ≠ u) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Var name T) y) x) ≠ u := by
  intro h
  cases name with
  | String s =>
      change
        SmtTerm.Apply (SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt y))
          (__eo_to_smt x) = u at h
      exact hString s h
  | _ =>
      change SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y)) (__eo_to_smt x) = u at h
      exact hNone h

/-- Shows that EO translation never produces the bare SMT term `eq`. -/
theorem eo_to_smt_ne_eq (t : Term) :
    __eo_to_smt t ≠ SmtTerm.eq := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Var name T =>
    exact eo_to_smt_var_ne name T SmtTerm.eq (by intro hEq; cases hEq)
      (by intro s hEq; cases hEq) h
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `ite`. -/
theorem eo_to_smt_ne_ite (t : Term) :
    __eo_to_smt t ≠ SmtTerm.ite := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Var name T =>
    exact eo_to_smt_var_ne name T SmtTerm.ite (by intro hEq; cases hEq)
      (by intro s hEq; cases hEq) h
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `exists`. -/
theorem eo_to_smt_ne_exists (t : Term) (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt t ≠ SmtTerm.exists s T := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Var name U =>
    exact eo_to_smt_var_ne name U (SmtTerm.exists s T) (by intro hEq; cases hEq)
      (by intro s' hEq; cases hEq) h
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `forall`. -/
theorem eo_to_smt_ne_forall (t : Term) (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt t ≠ SmtTerm.forall s T := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Var name U =>
    exact eo_to_smt_var_ne name U (SmtTerm.forall s T) (by intro hEq; cases hEq)
      (by intro s' hEq; cases hEq) h
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `choice`. -/
theorem eo_to_smt_ne_choice (t : Term) (s : smt_lit_String) (T : SmtType) :
    __eo_to_smt t ≠ SmtTerm.choice s T := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Var name U =>
    exact eo_to_smt_var_ne name U (SmtTerm.choice s T) (by intro hEq; cases hEq)
      (by intro s' hEq; cases hEq) h
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Apply g y =>
      cases g <;> rw [__eo_to_smt.eq_def] at h <;> cases h

/-- Shows that EO translation never produces the bare SMT term `eq_partial`. -/
theorem eo_to_smt_ne_eq_partial (t : Term) (u : SmtTerm) :
    __eo_to_smt t ≠ SmtTerm.Apply SmtTerm.eq u := by
  intro h
  cases t <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
  case Var name T =>
    exact eo_to_smt_var_ne name T (SmtTerm.Apply SmtTerm.eq u) (by intro hEq; cases hEq)
      (by intro s hEq; cases hEq) h
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Var name T =>
      exact eo_to_smt_apply_var_ne name T x (SmtTerm.Apply SmtTerm.eq u)
        (by intro hEq; cases hEq)
        (by intro s hEq; cases hEq) h
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
  case Var name T =>
    exact eo_to_smt_var_ne name T (SmtTerm.Apply SmtTerm.ite c) (by intro hEq; cases hEq)
      (by intro s hEq; cases hEq) h
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Var name T =>
      exact eo_to_smt_apply_var_ne name T x (SmtTerm.Apply SmtTerm.ite c)
        (by intro hEq; cases hEq)
        (by intro s hEq; cases hEq) h
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
  case Var name T =>
    exact eo_to_smt_var_ne name T (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) u)
      (by intro hEq; cases hEq)
      (by intro s hEq; cases hEq) h
  case Apply f x =>
    cases f <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
    case Var name T =>
      exact eo_to_smt_apply_var_ne name T x (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) u)
        (by intro hEq; cases hEq)
        (by intro s hEq; cases hEq) h
    case Apply g y =>
      cases g <;> try (rw [__eo_to_smt.eq_def] at h; cases h)
      case Var name T =>
        exact eo_to_smt_double_apply_var_ne name T y x
          (SmtTerm.Apply (SmtTerm.Apply SmtTerm.ite c) u)
          (by intro hEq; cases hEq)
          (by intro s hEq; cases hEq) h
      case Apply a b =>
        rw [__eo_to_smt.eq_def] at h
        injection h with hHead _
        exact eo_to_smt_ne_ite_partial ((Term.Apply a b).Apply y) c hHead

/-- Simplifies EO-to-SMT translation for `boolean`. -/
@[simp] theorem eo_to_smt_boolean (b : eo_lit_Bool) :
    __eo_to_smt (Term.Boolean b) = SmtTerm.Boolean b := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `var`. -/
@[simp] theorem eo_to_smt_var (s : eo_lit_String) (T : Term) :
    __eo_to_smt (Term.Var (Term.String s) T) = SmtTerm.Var s (__eo_to_smt_type T) := by
  rw [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT translation for `uconst`. -/
@[simp] theorem eo_to_smt_uconst (i : eo_lit_Nat) (T : Term) :
    __eo_to_smt (Term.UConst i T) = SmtTerm.UConst (smt_lit_uconst_id i) (__eo_to_smt_type T) := by
  simp [__eo_to_smt.eq_def]

/-- Simplifies EO-to-SMT type translation for `bool`. -/
@[simp] theorem eo_to_smt_type_bool :
    __eo_to_smt_type Term.Bool = SmtType.Bool := rfl

/-- Simplifies EO-to-SMT type translation for `int`. -/
@[simp] theorem eo_to_smt_type_int :
    __eo_to_smt_type Term.Int = SmtType.Int := rfl

/-- Simplifies EO-to-SMT type translation for `real`. -/
@[simp] theorem eo_to_smt_type_real :
    __eo_to_smt_type Term.Real = SmtType.Real := rfl

@[simp] theorem eo_to_smt_type_fun (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) =
      __smtx_typeof_guard (__eo_to_smt_type T)
        (__smtx_typeof_guard (__eo_to_smt_type U)
          (SmtType.FunType (__eo_to_smt_type T) (__eo_to_smt_type U))) := by
  simp [__eo_to_smt_type]

/-- Guarded bitvector type literals never translate to `map`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_map
    (n : eo_lit_Int) (A B : SmtType) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.Map A B := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- Guarded bitvector type literals never translate to `fun`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_fun
    (n : eo_lit_Int) (A B : SmtType) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.FunType A B := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- Guarded bitvector type literals never translate to `seq`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_seq
    (n : eo_lit_Int) (A : SmtType) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.Seq A := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- Guarded bitvector type literals never translate to `set`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_set
    (n : eo_lit_Int) (A : SmtType) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.Set A := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- Guarded bitvector type literals never translate to `bool`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_bool
    (n : eo_lit_Int) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.Bool := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- Guarded bitvector type literals never translate to `int`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_int
    (n : eo_lit_Int) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.Int := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- Guarded bitvector type literals never translate to `real`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_real
    (n : eo_lit_Int) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.Real := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- Guarded bitvector type literals never translate to `reglan`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_reglan
    (n : eo_lit_Int) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.RegLan := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- Guarded bitvector type literals never translate to `char`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_char
    (n : eo_lit_Int) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.Char := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- Guarded bitvector type literals never translate to `usort`. -/
@[simp] private theorem eo_to_smt_type_bitvec_lit_ne_usort
    (n : eo_lit_Int) (i : eo_lit_Nat) :
    smt_lit_ite (smt_lit_zleq 0 n) (SmtType.BitVec n) SmtType.None ≠
      SmtType.USort i := by
  by_cases hn : smt_lit_zleq 0 n = true <;> simp [smt_lit_ite, hn]

/-- No EO type translates to an SMT map type. -/
theorem eo_to_smt_type_ne_map
    {T : Term} {A B : SmtType} :
    __eo_to_smt_type T ≠ SmtType.Map A B := by
  cases T with
  | Apply f x =>
      cases f with
      | Apply g y =>
          cases g with
          | FunType =>
              cases hY : __eo_to_smt_type y <;> cases hX : __eo_to_smt_type x <;>
                simp [__eo_to_smt_type, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq, hY, hX]
          | _ =>
              simp [__eo_to_smt_type]
      | BitVec =>
          cases x <;> simp [__eo_to_smt_type]
      | Seq =>
          by_cases hx : __eo_to_smt_type x = SmtType.None
          · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]
          · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]
      | _ =>
          simp [__eo_to_smt_type]
  | _ =>
      simp [__eo_to_smt_type]

/-- Establishes an equality relating `smtx_typeof_guard` and `fun_iff`. -/
private theorem smtx_typeof_guard_eq_fun_iff
    {T U A B : SmtType} :
    __smtx_typeof_guard T U = SmtType.FunType A B ↔
      T ≠ SmtType.None ∧ U = SmtType.FunType A B := by
  unfold __smtx_typeof_guard
  by_cases hT : T = SmtType.None
  · simp [hT, smt_lit_ite, smt_lit_Teq]
  · simp [hT, smt_lit_ite, smt_lit_Teq]

/-- Establishes an equality relating `eo_to_smt_type` and `fun_iff`. -/
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
                  simpa using h
                rcases smtx_typeof_guard_eq_fun_iff.mp hOuter with ⟨hyNN, hInner⟩
                rcases smtx_typeof_guard_eq_fun_iff.mp hInner with ⟨hxNN, hFun⟩
                injection hFun with hA hB
                exact ⟨y, x, rfl, hA, hB, hyNN, hxNN⟩
            | _ =>
                simp [__eo_to_smt_type] at h
        | BitVec =>
            cases x <;> simp [__eo_to_smt_type] at h
        | Seq =>
            by_cases hx : __eo_to_smt_type x = SmtType.None
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at h
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at h
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
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at h
            · simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at h
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
    simp [__eo_to_smt_type, hU, hANN, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]

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
          by_cases hx : __eo_to_smt_type x = SmtType.None <;>
            simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]
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
          by_cases hx : __eo_to_smt_type x = SmtType.None <;>
            simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]
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
          by_cases hx : __eo_to_smt_type x = SmtType.None <;>
            simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]
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
          by_cases hx : __eo_to_smt_type x = SmtType.None <;>
            simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]
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
          by_cases hx : __eo_to_smt_type x = SmtType.None <;>
            simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]
      | _ =>
          simp [__eo_to_smt_type]
  | _ =>
      simp [__eo_to_smt_type]

/-- Establishes an equality relating `eo_to_smt_type` and `bitvec`. -/
private theorem eo_to_smt_type_eq_bitvec
    {T : Term} {w : smt_lit_Nat} :
    __eo_to_smt_type T = SmtType.BitVec w ->
    T = Term.Apply Term.BitVec (Term.Numeral (smt_lit_nat_to_int w)) := by
  cases T with
  | Apply f x =>
      cases f with
      | BitVec =>
          cases x <;> simp [__eo_to_smt_type]
          case Numeral n =>
            intro h
            by_cases hn : smt_lit_zleq 0 n = true
            · simp [smt_lit_ite, hn] at h
              cases h
              have hnNonneg : 0 <= n := by
                simpa [smt_lit_zleq, SmtEval.smt_lit_zleq] using hn
              simp [smt_lit_nat_to_int, smt_lit_int_to_nat,
                SmtEval.smt_lit_nat_to_int, SmtEval.smt_lit_int_to_nat,
                Int.toNat_of_nonneg hnNonneg]
            · simp [smt_lit_ite, hn] at h
      | Seq =>
          by_cases hx : __eo_to_smt_type x = SmtType.None <;>
            simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq]
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
                by_cases hx : __eo_to_smt_type x = SmtType.None <;>
                  simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at hT
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
                by_cases hx : __eo_to_smt_type x = SmtType.None <;>
                  simp [__eo_to_smt_type, hx, __smtx_typeof_guard, smt_lit_ite, smt_lit_Teq] at hT
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
        exact False.elim ((eo_to_smt_type_ne_map (T := T) (A := A) (B := B)) hT)
    | FunType A B =>
        intro T U hT hU _
        rcases eo_to_smt_type_eq_fun_iff.mp hT with
          ⟨T1, T2, hT', hT1, hT2, hT1NN, hT2NN⟩
        rcases eo_to_smt_type_eq_fun_iff.mp hU with
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
