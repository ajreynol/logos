import Cpc.Proofs.TypePreservation.Predicates
import Cpc.Proofs.Canonical.TypeDefaultBasic
import Cpc.Proofs.Canonical.FiniteDefaultable

/-!
Canonical/cardinality and freshness witnesses used by datatype cardinality
reasoning and array extensionality.

This module is the intended boundary for the residual datatype-cardinality
assumptions.  After the `__smtx_type_default` / `native_inhabited_type`
refactor (value-level substitution removed; default canonicality now supplied
unconditionally by `Cpc.Proofs.Canonical.TypeDefaultBasic`), every non-datatype
freshness/non-default witness is discharged directly.  The two genuinely hard
datatype cardinality facts — fresh inhabitants of an infinite datatype, and a
non-default inhabitant of a finite non-unit datatype — are isolated as the only
remaining `sorry`s below (formerly proved via the deleted value-substitution
"pump"/"inhabit" machinery).
-/

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Smtm


private def smt_map_keys : SmtMap -> List SmtValue
  | SmtMap.cons i _ m => i :: smt_map_keys m
  | SmtMap.default _ _ => []

private theorem native_veq_eq_false_of_ne {a b : SmtValue} (h : a ≠ b) :
    native_veq a b = false := by
  simp [native_veq, h]

private theorem native_veq_false_symm {a b : SmtValue}
    (h : native_veq a b = false) :
    native_veq b a = false := by
  simp [native_veq] at h ⊢
  intro hEq
  exact h hEq.symm

private theorem type_default_typed_canonical_of_native_inhabited
    {T : SmtType}
    (h : native_inhabited_type T = true) :
    __smtx_typeof_value (__smtx_type_default T) = T ∧
      __smtx_value_canonical_bool (__smtx_type_default T) = true := by
  have hParts : native_Teq T SmtType.None = false ∧
      native_Teq (__smtx_typeof_value (__smtx_type_default T)) T = true := by
    simpa [native_inhabited_type, native_and, native_not] using h
  have hTyped : __smtx_typeof_value (__smtx_type_default T) = T := by
    simpa [native_Teq] using hParts.2
  exact ⟨hTyped, type_default_canonical_of_typed T hParts.2⟩

private theorem type_default_ne_notValue_of_native_inhabited
    {T : SmtType}
    (hInh : native_inhabited_type T = true)
    (hT : T ≠ SmtType.None) :
    __smtx_type_default T ≠ SmtValue.NotValue := by
  intro hEq
  have hTy := (type_default_typed_canonical_of_native_inhabited hInh).1
  rw [hEq] at hTy
  simp [__smtx_typeof_value] at hTy
  exact hT hTy.symm

private theorem ne_none_of_native_inhabited {T : SmtType}
    (h : native_inhabited_type T = true) : T ≠ SmtType.None := by
  intro hN
  subst T
  simp [native_inhabited_type, native_Teq, native_not, native_and] at h


-- === portable witnesses: bitvec / numeral / rational / usort / size bounds ===

private theorem one_mod_pow2_succ (w : Nat) :
    (1 : Int) % (native_int_pow2 (native_nat_to_int (Nat.succ w))) = 1 := by
  have hnot : ¬ ((w : Int) + 1 < 0) := by omega
  have hpow :
      native_int_pow2 (native_nat_to_int (Nat.succ w)) =
        (2 : Int) ^ (Nat.succ w) := by
    simp [native_int_pow2, native_zexp_total, native_nat_to_int, hnot]
  rw [hpow]
  exact Int.emod_eq_of_lt (by decide) (by
    have hNat : (1 : Nat) < 2 ^ Nat.succ w :=
      Nat.one_lt_pow (by simp) (by decide)
    exact_mod_cast hNat)

private theorem one_mod_pow2_succ_zeq (w : Nat) :
    native_zeq (1 : Int)
      (native_mod_total 1 (native_int_pow2 (native_nat_to_int (Nat.succ w)))) = true := by
  simp [native_zeq, native_mod_total, one_mod_pow2_succ]

private theorem bitvec_succ_one_typeof (w : Nat) :
    __smtx_typeof_value
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1) =
        SmtType.BitVec (Nat.succ w) := by
  have hmod :
      native_zeq (1 : Int)
        (native_mod_total 1 (native_int_pow2 ((w : Int) + 1))) = true := by
    simpa [native_nat_to_int] using one_mod_pow2_succ_zeq w
  have hnonneg : native_zleq 0 ((w : Int) + 1) = true := by
    have hle : (0 : Int) <= (w : Int) + 1 :=
      Int.add_nonneg (Int.natCast_nonneg w) (by decide)
    simpa [native_zleq] using hle
  simp [__smtx_typeof_value, native_and, native_ite, native_int_to_nat,
    native_nat_to_int, Nat.succ_eq_add_one]
  exact ⟨hnonneg, hmod⟩

private theorem bitvec_succ_one_canonical (w : Nat) :
    __smtx_value_canonical_bool
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1) = true := by
  have hmod :
      native_zeq (1 : Int)
        (native_mod_total 1 (native_int_pow2 ((w : Int) + 1))) = true := by
    simpa [native_nat_to_int] using one_mod_pow2_succ_zeq w
  simp [__smtx_value_canonical_bool, native_ite, native_nat_to_int,
    Nat.succ_eq_add_one]
  exact Or.inr hmod

private theorem bitvec_succ_one_ne_default (w : Nat) :
    native_veq
      (SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1)
      (__smtx_type_default (SmtType.BitVec (Nat.succ w))) = false := by
  simp [__smtx_type_default, __smtx_type_default_rec, native_nat_to_int, native_veq]

private def fresh_numeral_index : List SmtValue -> Nat
  | [] => 0
  | SmtValue.Numeral n :: xs => Nat.max (Int.toNat n + 1) (fresh_numeral_index xs)
  | _ :: xs => fresh_numeral_index xs

private theorem fresh_numeral_index_gt_of_mem :
    ∀ {xs : List SmtValue} {n : native_Int},
      SmtValue.Numeral n ∈ xs ->
        Int.toNat n < fresh_numeral_index xs := by
  intro xs
  induction xs with
  | nil =>
      intro n h
      cases h
  | cons v xs ih =>
      intro n h
      cases v <;> simp [fresh_numeral_index] at h ⊢
      case Numeral m =>
        rcases h with hEq | hTail
        · subst n
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
        · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)
      all_goals
        exact ih h

private theorem fresh_numeral_not_mem (xs : List SmtValue) :
    SmtValue.Numeral (Int.ofNat (fresh_numeral_index xs)) ∉ xs := by
  intro h
  have hlt := fresh_numeral_index_gt_of_mem
    (xs := xs) (n := Int.ofNat (fresh_numeral_index xs)) h
  simp at hlt

private theorem fresh_numeral_veq_false_of_mem (xs : List SmtValue) :
    ∀ j : SmtValue, j ∈ xs ->
      native_veq j (SmtValue.Numeral (Int.ofNat (fresh_numeral_index xs))) = false := by
  intro j hj
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst j
    exact fresh_numeral_not_mem xs hj)

private def fresh_rational_index : List SmtValue -> Nat
  | [] => 0
  | SmtValue.Rational q :: xs => Nat.max (Int.toNat (Rat.floor q) + 1) (fresh_rational_index xs)
  | _ :: xs => fresh_rational_index xs

private theorem fresh_rational_index_gt_of_mem :
    ∀ {xs : List SmtValue} {q : native_Rat},
      SmtValue.Rational q ∈ xs ->
        Int.toNat (Rat.floor q) < fresh_rational_index xs := by
  intro xs
  induction xs with
  | nil =>
      intro q h
      cases h
  | cons v xs ih =>
      intro q h
      cases v <;> simp [fresh_rational_index] at h ⊢
      case Rational r =>
        rcases h with hEq | hTail
        · subst q
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
        · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)
      all_goals
        exact ih h

private theorem fresh_rational_not_mem (xs : List SmtValue) :
    SmtValue.Rational (Int.ofNat (fresh_rational_index xs)) ∉ xs := by
  intro h
  have hlt := fresh_rational_index_gt_of_mem
    (xs := xs) (q := (Int.ofNat (fresh_rational_index xs) : native_Rat)) h
  simp at hlt

private theorem fresh_rational_veq_false_of_mem (xs : List SmtValue) :
    ∀ j : SmtValue, j ∈ xs ->
      native_veq j
        (SmtValue.Rational (Int.ofNat (fresh_rational_index xs))) = false := by
  intro j hj
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst j
    exact fresh_rational_not_mem xs hj)

private def fresh_usort_index (sort : native_Nat) : List SmtValue -> Nat
  | [] => 0
  | SmtValue.UValue i n :: xs =>
      if i = sort then Nat.max (n + 1) (fresh_usort_index sort xs)
      else fresh_usort_index sort xs
  | _ :: xs => fresh_usort_index sort xs

private theorem fresh_usort_index_gt_of_mem (sort : native_Nat) :
    ∀ {xs : List SmtValue} {n : native_Nat},
      SmtValue.UValue sort n ∈ xs ->
        n < fresh_usort_index sort xs := by
  intro xs
  induction xs with
  | nil =>
      intro n h
      cases h
  | cons v xs ih =>
      intro n h
      cases v
      case UValue i m =>
        by_cases hi : i = sort
        · subst i
          simp [fresh_usort_index] at h ⊢
          rcases h with hEq | hTail
          · subst n
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
          · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)
        · have hNe : sort ≠ i := fun hEq => hi hEq.symm
          simp [fresh_usort_index, hi, hNe] at h ⊢
          exact ih h
      all_goals
        simp [fresh_usort_index] at h ⊢
        exact ih h

private theorem fresh_usort_not_mem (sort : native_Nat) (xs : List SmtValue) :
    SmtValue.UValue sort (fresh_usort_index sort xs) ∉ xs := by
  intro h
  have hlt := fresh_usort_index_gt_of_mem sort
    (xs := xs) (n := fresh_usort_index sort xs) h
  exact Nat.lt_irrefl _ hlt

private theorem fresh_usort_veq_false_of_mem (sort : native_Nat) (xs : List SmtValue) :
    ∀ j : SmtValue, j ∈ xs ->
      native_veq j (SmtValue.UValue sort (fresh_usort_index sort xs)) = false := by
  intro j hj
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst j
    exact fresh_usort_not_mem sort xs hj)

private noncomputable def smt_value_size_bound : List SmtValue -> Nat
  | [] => 0
  | v :: vs => Nat.max (sizeOf v + 1) (smt_value_size_bound vs)

private theorem smt_value_size_lt_bound_of_mem :
    ∀ {xs : List SmtValue} {v : SmtValue},
      v ∈ xs -> sizeOf v < smt_value_size_bound xs := by
  intro xs
  induction xs with
  | nil =>
      intro v h
      cases h
  | cons x xs ih =>
      intro v h
      simp [smt_value_size_bound] at h ⊢
      rcases h with hEq | hTail
      · subst v
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (ih hTail) (Nat.le_max_right _ _)

private theorem native_veq_false_of_mem_and_size_bound
    {xs : List SmtValue}
    {j i : SmtValue}
    (hj : j ∈ xs)
    (hi : smt_value_size_bound xs ≤ sizeOf i) :
    native_veq j i = false := by
  exact native_veq_eq_false_of_ne (by
    intro hEq
    subst i
    have hLt := smt_value_size_lt_bound_of_mem (xs := xs) hj
    exact Nat.not_lt_of_ge hi hLt)

private theorem int_large_witness (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Int ∧
        __smtx_value_canonical_bool i = true ∧
          minSize ≤ sizeOf i := by
  refine ⟨SmtValue.Numeral (Int.ofNat minSize), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value]
  · simp [__smtx_value_canonical_bool]
  · rw [show sizeOf (SmtValue.Numeral (Int.ofNat minSize)) =
        1 + sizeOf (Int.ofNat minSize) by rfl]
    rw [show sizeOf (Int.ofNat minSize) = 1 + minSize by rfl]
    omega

private theorem real_large_witness (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Real ∧
        __smtx_value_canonical_bool i = true ∧
          minSize ≤ sizeOf i := by
  refine ⟨SmtValue.Rational (Int.ofNat minSize : native_Rat), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value]
  · simp [__smtx_value_canonical_bool]
  · rw [show sizeOf (SmtValue.Rational (Int.ofNat minSize : native_Rat)) =
        1 + sizeOf (Int.ofNat minSize : native_Rat) by rfl]
    rw [show sizeOf (Int.ofNat minSize : native_Rat) =
        1 + sizeOf (Int.ofNat minSize) + sizeOf (1 : Nat) +
          sizeOf (by decide : (1 : Nat) ≠ 0) by rfl]
    rw [show sizeOf (Int.ofNat minSize) = 1 + minSize by rfl]
    omega

private theorem usort_large_witness (u : native_Nat) (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.USort u ∧
        __smtx_value_canonical_bool i = true ∧
          minSize ≤ sizeOf i := by
  refine ⟨SmtValue.UValue u minSize, ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value]
  · simp [__smtx_value_canonical_bool]
  · rw [show sizeOf (SmtValue.UValue u minSize) =
        1 + sizeOf u + sizeOf minSize by rfl]
    simp [sizeOf]

private theorem sizeOf_lt_apply_left (f a : SmtValue) :
    sizeOf f < sizeOf (SmtValue.Apply f a) := by
  rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
  omega

private theorem sizeOf_lt_apply_right (f a : SmtValue) :
    sizeOf a < sizeOf (SmtValue.Apply f a) := by
  rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
  omega

private theorem datatype_fresh_of_size_bound
    {s : native_String}
    {d : SmtDatatype}
    {avoid : List SmtValue}
    (hLarge :
      ∃ i : SmtValue,
        __smtx_typeof_value i = SmtType.Datatype s d ∧
          __smtx_value_canonical_bool i = true ∧
            smt_value_size_bound avoid ≤ sizeOf i) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool i = true ∧
          ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false := by
  rcases hLarge with ⟨i, hiTy, hiCan, hiSize⟩
  refine ⟨i, hiTy, hiCan, ?_⟩
  intro j hj
  exact native_veq_false_of_mem_and_size_bound hj hiSize

-- === portable seq witnesses ===

private def smt_seq_repeat (T : SmtType) (x : SmtValue) : Nat -> SmtSeq
  | 0 => SmtSeq.empty T
  | Nat.succ n => SmtSeq.cons x (smt_seq_repeat T x n)

private theorem smt_seq_repeat_typeof
    (T : SmtType) (x : SmtValue) (hx : __smtx_typeof_value x = T) :
    ∀ n : Nat,
      __smtx_typeof_seq_value (smt_seq_repeat T x n) = SmtType.Seq T
  | 0 => by
      simp [smt_seq_repeat, __smtx_typeof_seq_value]
  | Nat.succ n => by
      simp [smt_seq_repeat, __smtx_typeof_seq_value,
        smt_seq_repeat_typeof T x hx n, hx, native_ite, native_Teq]

private theorem smt_seq_repeat_canonical
    (T : SmtType) (x : SmtValue) (hx : __smtx_value_canonical_bool x = true) :
    ∀ n : Nat,
      __smtx_seq_canonical (smt_seq_repeat T x n) = true
  | 0 => by
      simp [smt_seq_repeat, __smtx_seq_canonical]
  | Nat.succ n => by
      simp [smt_seq_repeat, __smtx_seq_canonical, native_and, hx,
        smt_seq_repeat_canonical T x hx n]

private theorem smt_seq_repeat_size_ge
    (T : SmtType) (x : SmtValue) :
    ∀ n : Nat, n ≤ sizeOf (smt_seq_repeat T x n)
  | 0 => Nat.zero_le _
  | Nat.succ n => by
      have hRec := smt_seq_repeat_size_ge T x n
      rw [show smt_seq_repeat T x (Nat.succ n) =
        SmtSeq.cons x (smt_seq_repeat T x n) by rfl]
      rw [show sizeOf (SmtSeq.cons x (smt_seq_repeat T x n)) =
        1 + sizeOf x + sizeOf (smt_seq_repeat T x n) by rfl]
      omega

/--
A sequence type over any inhabited element type has typed canonical values of
arbitrarily large size: repeat the default element.
-/
private theorem seq_inhabited_large_witness
    (T : SmtType)
    (hInh : native_inhabited_type T = true)
    (minSize : Nat) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Seq T ∧
        __smtx_value_canonical_bool i = true ∧
          minSize ≤ sizeOf i := by
  have hDef := type_default_typed_canonical_of_native_inhabited hInh
  refine
    ⟨SmtValue.Seq (smt_seq_repeat T (__smtx_type_default T) minSize),
      ?_, ?_, ?_⟩
  · simpa [__smtx_typeof_value] using
      smt_seq_repeat_typeof T (__smtx_type_default T) hDef.1 minSize
  · simpa [__smtx_value_canonical_bool] using
      smt_seq_repeat_canonical T (__smtx_type_default T) hDef.2 minSize
  · rw [show
      sizeOf
          (SmtValue.Seq (smt_seq_repeat T (__smtx_type_default T) minSize)) =
        1 + sizeOf (smt_seq_repeat T (__smtx_type_default T) minSize) by rfl]
    have := smt_seq_repeat_size_ge T (__smtx_type_default T) minSize
    omega

-- === portable map/set/seq head-key helpers ===

private def smt_seq_heads : List SmtValue -> List SmtValue
  | SmtValue.Seq (SmtSeq.cons v _) :: xs => v :: smt_seq_heads xs
  | _ :: xs => smt_seq_heads xs
  | [] => []

private theorem smt_seq_head_mem_of_mem (x : SmtValue) (s : SmtSeq) :
    ∀ {xs : List SmtValue},
      SmtValue.Seq (SmtSeq.cons x s) ∈ xs ->
        x ∈ smt_seq_heads xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_seq_heads] at h ⊢
      case Seq s' =>
        cases s' <;> simp [smt_seq_heads] at h ⊢
        case empty T' =>
          exact ih h
        case cons y ys =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨hHead, _hTailEq⟩
            subst x
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

private def smt_set_head_keys : List SmtValue -> List SmtValue
  | SmtValue.Set (SmtMap.cons k _ _) :: xs => k :: smt_set_head_keys xs
  | _ :: xs => smt_set_head_keys xs
  | [] => []

private theorem smt_set_head_key_mem_of_mem (k e : SmtValue) (m : SmtMap) :
    ∀ {xs : List SmtValue},
      SmtValue.Set (SmtMap.cons k e m) ∈ xs ->
        k ∈ smt_set_head_keys xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_set_head_keys] at h ⊢
      case Set m' =>
        cases m' <;> simp [smt_set_head_keys] at h ⊢
        case default T' e' =>
          exact ih h
        case cons k' e' m'' =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨hKey, _hRest⟩
            subst k
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

private def smt_map_head_values : List SmtValue -> List SmtValue
  | SmtValue.Map (SmtMap.cons _ e _) :: xs => e :: smt_map_head_values xs
  | _ :: xs => smt_map_head_values xs
  | [] => []

private theorem smt_map_head_value_mem_of_mem (k e : SmtValue) (m : SmtMap) :
    ∀ {xs : List SmtValue},
      SmtValue.Map (SmtMap.cons k e m) ∈ xs ->
        e ∈ smt_map_head_values xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_map_head_values] at h ⊢
      case Map m' =>
        cases m' <;> simp [smt_map_head_values] at h ⊢
        case default T' e' =>
          exact ih h
        case cons k' e' m'' =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨_hKey, hValue, _hRest⟩
            subst e
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h

private def smt_map_head_keys : List SmtValue -> List SmtValue
  | SmtValue.Map (SmtMap.cons k _ _) :: xs => k :: smt_map_head_keys xs
  | _ :: xs => smt_map_head_keys xs
  | [] => []

private theorem smt_map_head_key_mem_of_mem (k e : SmtValue) (m : SmtMap) :
    ∀ {xs : List SmtValue},
      SmtValue.Map (SmtMap.cons k e m) ∈ xs ->
        k ∈ smt_map_head_keys xs := by
  intro xs
  induction xs with
  | nil =>
      intro h
      cases h
  | cons v xs ih =>
      intro h
      cases v <;> simp [smt_map_head_keys] at h ⊢
      case Map m' =>
        cases m' <;> simp [smt_map_head_keys] at h ⊢
        case default T' e' =>
          exact ih h
        case cons k' e' m'' =>
          rcases h with hEq | hTail
          · rcases hEq with ⟨hKey, _hRest⟩
            subst k
            simp
          · exact Or.inr (ih hTail)
      all_goals
        exact ih h


/-! ### Foundation for the residual datatype-cardinality proofs

Reusable facts re-established on the refactored two-datatype default machinery
(`TypeDefaultBasic`).  These replace the deleted value-substitution scaffolding
and are the building blocks for discharging the two `sorry`s below: typedness +
canonicality of a generated constructor value (`datatype_cons_default_kernel`),
selection of a constructor by the datatype default (`datatype_default_select`),
and stability of the constructor head (`cons_default_head`). -/

/-- Cons-default kernel (exposes `TypeDefaultBasic.datatype_kernel_rec` motive3):
a constructor's generated value is `NotValue`, or it is typed `base` and canonical. -/
theorem datatype_cons_default_kernel :
    ∀ (cF cU : SmtDatatypeCons), DtcSubstStar cF cU →
      ∀ (v : SmtValue) (base : SmtType),
        __smtx_typeof_value v = chainType cF base →
        __smtx_value_canonical_bool v = true →
          __smtx_datatype_cons_default v cF cU = SmtValue.NotValue ∨
          (__smtx_typeof_value (__smtx_datatype_cons_default v cF cU) = base ∧
           __smtx_value_canonical_bool (__smtx_datatype_cons_default v cF cU) = true)
  | SmtDatatypeCons.unit, cU, hc, v, base, htypeof, hcanon => by
      cases hc
      right
      refine ⟨?_, ?_⟩
      · simpa [__smtx_datatype_cons_default, chainType] using htypeof
      · simpa [__smtx_datatype_cons_default] using hcanon
  | SmtDatatypeCons.cons TF cF, cU, hc, v, base, htypeof, hcanon => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        rw [__smtx_datatype_cons_default]
        by_cases hv : native_veq (__smtx_type_default_rec TF TU) SmtValue.NotValue = true
        · left; rw [native_ite, if_pos hv]
        · rw [native_ite, if_neg hv]
          have hss : SubstStar TF TU := by
            cases hfr with
            | rel h => exact h
            | forcesNV h => exact absurd (by simp [native_veq, h TF]) hv
          rcases datatype_kernel_rec TF TU hss with hNV | ⟨hTy, hCanonField⟩
          · exact absurd (by simp [native_veq, hNV]) hv
          · have hTFne : TF ≠ SmtType.None := by
              cases hss with
              | refl => intro hNone; rw [hNone] at hv; simp [__smtx_type_default_rec, native_veq] at hv
              | dt _ => intro hNone; cases hNone
            have htypeofApply :
                __smtx_typeof_value (SmtValue.Apply v (__smtx_type_default_rec TF TU)) =
                  chainType cF base := by
              have hchain : chainType (SmtDatatypeCons.cons TF cF) base =
                  SmtType.DtcAppType TF (chainType cF base) := rfl
              rw [hchain] at htypeof
              simp only [__smtx_typeof_value, htypeof, hTy, __smtx_typeof_apply_value,
                         __smtx_typeof_guard, native_Teq, native_ite, decide_true, if_true]
              simp [hTFne]
            have hcanonApply :
                __smtx_value_canonical_bool (SmtValue.Apply v (__smtx_type_default_rec TF TU)) = true := by
              simp [__smtx_value_canonical_bool, hcanon, hCanonField, native_and]
            exact datatype_cons_default_kernel cF cU hcc
              (SmtValue.Apply v (__smtx_type_default_rec TF TU)) base htypeofApply hcanonApply
  termination_by cF _ _ _ _ _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

/-- The datatype-default picks constructor `n`'s value when it is defaultable. -/
theorem datatype_default_select
    (s : native_String) (d : SmtDatatype) (n : native_Nat)
    (cF cU : SmtDatatypeCons) (DF DU : SmtDatatype)
    (hNe : __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU ≠ SmtValue.NotValue) :
    __smtx_datatype_default s d n (SmtDatatype.sum cF DF) (SmtDatatype.sum cU DU) =
      __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU := by
  have hf : native_veq (__smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU)
      SmtValue.NotValue = false := native_veq_eq_false_of_ne hNe
  rw [__smtx_datatype_default]
  simp [native_ite, native_not, hf]

/-- The apply-head of a (non-`NotValue`) constructor default is the head of the seed value. -/
theorem cons_default_head :
    ∀ (cF cU : SmtDatatypeCons) (v : SmtValue),
      __smtx_datatype_cons_default v cF cU ≠ SmtValue.NotValue ->
        __vsm_apply_head (__smtx_datatype_cons_default v cF cU) = __vsm_apply_head v
  | SmtDatatypeCons.unit, cU, v, _hNe => by
      cases cU <;> simp [__smtx_datatype_cons_default] at *
  | SmtDatatypeCons.cons TF cF, cU, v, hNe => by
      cases cU with
      | unit => simp [__smtx_datatype_cons_default] at hNe
      | cons TU cU =>
        rw [__smtx_datatype_cons_default] at hNe ⊢
        by_cases hv : native_veq (__smtx_type_default_rec TF TU) SmtValue.NotValue = true
        · rw [native_ite, if_pos hv] at hNe; exact absurd rfl hNe
        · rw [native_ite, if_neg hv] at hNe ⊢
          have hrec := cons_default_head cF cU
            (SmtValue.Apply v (__smtx_type_default_rec TF TU)) hNe
          rw [hrec]; simp [__vsm_apply_head]
  termination_by cF _ _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

private theorem dt_wf_cons_of_wf {cF cU : SmtDatatypeCons} {dF dU : SmtDatatype}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum cF dF) (SmtDatatype.sum cU dU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true := by
  cases hc : __smtx_dt_cons_wf_rec cF cU <;>
    simp [__smtx_dt_wf_rec, native_ite, hc] at h ⊢

private theorem dt_wf_tail_of_nonempty_tail_wf
    {cF cU cTailF cTailU : SmtDatatypeCons} {dTailF dTailU : SmtDatatype}
    (h : __smtx_dt_wf_rec (SmtDatatype.sum cF (SmtDatatype.sum cTailF dTailF))
        (SmtDatatype.sum cU (SmtDatatype.sum cTailU dTailU)) = true) :
    __smtx_dt_wf_rec (SmtDatatype.sum cTailF dTailF) (SmtDatatype.sum cTailU dTailU) = true := by
  have hc : __smtx_dt_cons_wf_rec cF cU = true := dt_wf_cons_of_wf h
  simpa [__smtx_dt_wf_rec, native_ite, hc] using h

private theorem finite_dt_cons_of_finite_sum {c : SmtDatatypeCons} {d : SmtDatatype}
    (hFin : __smtx_is_finite_datatype (SmtDatatype.sum c d) = true) :
    __smtx_is_finite_datatype_cons c = true := by
  have hP : __smtx_is_finite_datatype_cons c = true ∧ __smtx_is_finite_datatype d = true := by
    simpa [__smtx_is_finite_datatype, native_and] using hFin
  exact hP.1

private theorem finite_dt_tail_of_finite_sum {c : SmtDatatypeCons} {d : SmtDatatype}
    (hFin : __smtx_is_finite_datatype (SmtDatatype.sum c d) = true) :
    __smtx_is_finite_datatype d = true := by
  have hP : __smtx_is_finite_datatype_cons c = true ∧ __smtx_is_finite_datatype d = true := by
    simpa [__smtx_is_finite_datatype, native_and] using hFin
  exact hP.2

/-- Seed injectivity: a non-`NotValue` constructor default determines its seed. -/
private theorem cons_default_seed_inj :
    ∀ (cF cU : SmtDatatypeCons) (v v' : SmtValue),
      __smtx_datatype_cons_default v cF cU ≠ SmtValue.NotValue →
      __smtx_datatype_cons_default v cF cU = __smtx_datatype_cons_default v' cF cU →
      v = v'
  | SmtDatatypeCons.unit, cU, v, v', hne, heq => by
      cases cU <;> simp [__smtx_datatype_cons_default] at hne heq
      exact heq
  | SmtDatatypeCons.cons TF cF, cU, v, v', hne, heq => by
      cases cU with
      | unit => simp [__smtx_datatype_cons_default] at hne
      | cons TU cU =>
        by_cases hv : native_veq (__smtx_type_default_rec TF TU) SmtValue.NotValue = true
        · rw [__smtx_datatype_cons_default, native_ite, if_pos hv] at hne
          exact absurd rfl hne
        · have unf : ∀ w, __smtx_datatype_cons_default w (SmtDatatypeCons.cons TF cF)
                  (SmtDatatypeCons.cons TU cU) =
                __smtx_datatype_cons_default (SmtValue.Apply w (__smtx_type_default_rec TF TU)) cF cU := by
            intro w; rw [__smtx_datatype_cons_default, native_ite, if_neg hv]
          rw [unf v] at hne
          rw [unf v, unf v'] at heq
          have hh := cons_default_seed_inj cF cU
            (SmtValue.Apply v (__smtx_type_default_rec TF TU))
            (SmtValue.Apply v' (__smtx_type_default_rec TF TU)) hne heq
          exact (SmtValue.Apply.inj hh).1
  termination_by cF _ _ _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

/-! ### Value-construction machinery for the infinite large-witness -/

/-- Build a constructor value: inject `w` at self-recursive fields (folded type `Datatype s d`),
default elsewhere. -/
def build_cons (s : native_String) (d : SmtDatatype) (w : SmtValue) :
    SmtDatatypeCons → SmtDatatypeCons → SmtValue → SmtValue
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU, seed =>
      build_cons s d w cF cU
        (SmtValue.Apply seed
          (native_ite (native_Teq TF (SmtType.Datatype s d)) w (__smtx_type_default_rec TF TU)))
  | _, _, seed => seed

/-- Each field is self-recursive or its default is non-`NotValue` (defaultable). -/
def fields_ok (s : native_String) (d : SmtDatatype) :
    SmtDatatypeCons → SmtDatatypeCons → Prop
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU =>
      (native_Teq TF (SmtType.Datatype s d) = true ∨
        __smtx_type_default_rec TF TU ≠ SmtValue.NotValue) ∧ fields_ok s d cF cU
  | SmtDatatypeCons.unit, SmtDatatypeCons.unit => True
  | _, _ => False

theorem build_cons_typeof (s : native_String) (d : SmtDatatype) (w : SmtValue)
    (hw : __smtx_typeof_value w = SmtType.Datatype s d) :
    ∀ (cF cU : SmtDatatypeCons), DtcSubstStar cF cU → fields_ok s d cF cU →
      ∀ (seed : SmtValue) (base : SmtType),
        __smtx_typeof_value seed = chainType cF base →
        __smtx_typeof_value (build_cons s d w cF cU seed) = base
  | SmtDatatypeCons.unit, cU, hc, hok, seed, base, hseed => by
      cases hc
      simpa [build_cons, chainType] using hseed
  | SmtDatatypeCons.cons TF cF, cU, hc, hok, seed, base, hseed => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        have hokP : (native_Teq TF (SmtType.Datatype s d) = true ∨
            __smtx_type_default_rec TF TU ≠ SmtValue.NotValue) ∧ fields_ok s d cF cU := by
          simpa [fields_ok] using hok
        -- the injected value and its type
        have hinjTy : __smtx_typeof_value
            (native_ite (native_Teq TF (SmtType.Datatype s d)) w (__smtx_type_default_rec TF TU)) = TF
            ∧ TF ≠ SmtType.None := by
          by_cases hself : native_Teq TF (SmtType.Datatype s d) = true
          · have hTFeq : TF = SmtType.Datatype s d := by simpa [native_Teq] using hself
            refine ⟨?_, ?_⟩
            · rw [native_ite, if_pos hself, hw, hTFeq]
            · rw [hTFeq]; exact fun h => by cases h
          · have hdef : __smtx_type_default_rec TF TU ≠ SmtValue.NotValue :=
              Or.resolve_left hokP.1 hself
            have hss : SubstStar TF TU := by
              cases hfr with
              | rel h => exact h
              | forcesNV h => exact absurd (h TF) hdef
            have hTFne : TF ≠ SmtType.None := by
              intro hNone; rw [hNone] at hss hdef
              cases hss with
              | refl => simp [__smtx_type_default_rec] at hdef
            rcases datatype_kernel_rec TF TU hss with hNV | ⟨hTy, _⟩
            · exact absurd hNV hdef
            · exact ⟨by rw [native_ite, if_neg hself]; exact hTy, hTFne⟩
        have hApply : __smtx_typeof_value
            (SmtValue.Apply seed
              (native_ite (native_Teq TF (SmtType.Datatype s d)) w (__smtx_type_default_rec TF TU)))
            = chainType cF base := by
          have hchain : chainType (SmtDatatypeCons.cons TF cF) base =
              SmtType.DtcAppType TF (chainType cF base) := rfl
          rw [hchain] at hseed
          have h1 : native_Teq TF TF = true := by simp [native_Teq]
          have h2 : native_Teq TF SmtType.None = false := by simp [native_Teq, hinjTy.2]
          show __smtx_typeof_apply_value (__smtx_typeof_value seed)
            (__smtx_typeof_value
              (native_ite (native_Teq TF (SmtType.Datatype s d)) w
                (__smtx_type_default_rec TF TU))) = chainType cF base
          rw [hseed, hinjTy.1]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, h1, h2]
        rw [build_cons]
        exact build_cons_typeof s d w hw cF cU hcc hokP.2 _ base hApply
  termination_by cF _ _ _ _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

theorem build_cons_canonical (s : native_String) (d : SmtDatatype) (w : SmtValue)
    (hw : __smtx_value_canonical_bool w = true) :
    ∀ (cF cU : SmtDatatypeCons), DtcSubstStar cF cU → fields_ok s d cF cU →
      ∀ (seed : SmtValue), __smtx_value_canonical_bool seed = true →
        __smtx_value_canonical_bool (build_cons s d w cF cU seed) = true
  | SmtDatatypeCons.unit, cU, hc, hok, seed, hseed => by
      cases hc; simpa [build_cons] using hseed
  | SmtDatatypeCons.cons TF cF, cU, hc, hok, seed, hseed => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        have hokP : (native_Teq TF (SmtType.Datatype s d) = true ∨
            __smtx_type_default_rec TF TU ≠ SmtValue.NotValue) ∧ fields_ok s d cF cU := by
          simpa [fields_ok] using hok
        have hinjCan : __smtx_value_canonical_bool
            (native_ite (native_Teq TF (SmtType.Datatype s d)) w (__smtx_type_default_rec TF TU)) = true := by
          by_cases hself : native_Teq TF (SmtType.Datatype s d) = true
          · rw [native_ite, if_pos hself]; exact hw
          · have hdef : __smtx_type_default_rec TF TU ≠ SmtValue.NotValue :=
              Or.resolve_left hokP.1 hself
            have hss : SubstStar TF TU := by
              cases hfr with
              | rel h => exact h
              | forcesNV h => exact absurd (h TF) hdef
            rcases datatype_kernel_rec TF TU hss with hNV | ⟨_, hCan⟩
            · exact absurd hNV hdef
            · rw [native_ite, if_neg hself]; exact hCan
        have hApplyCan : __smtx_value_canonical_bool
            (SmtValue.Apply seed
              (native_ite (native_Teq TF (SmtType.Datatype s d)) w (__smtx_type_default_rec TF TU))) = true := by
          simp [__smtx_value_canonical_bool, hseed, hinjCan, native_and]
        rw [build_cons]
        exact build_cons_canonical s d w hw cF cU hcc hokP.2 _ hApplyCan
  termination_by cF _ _ _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

theorem build_cons_mono (s : native_String) (d : SmtDatatype) (w : SmtValue) :
    ∀ (cF cU : SmtDatatypeCons) (seed : SmtValue),
      sizeOf seed ≤ sizeOf (build_cons s d w cF cU seed)
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU, seed => by
      rw [build_cons]
      have hrec := build_cons_mono s d w cF cU (SmtValue.Apply seed
        (native_ite (native_Teq TF (SmtType.Datatype s d)) w (__smtx_type_default_rec TF TU)))
      have happ : sizeOf (SmtValue.Apply seed
          (native_ite (native_Teq TF (SmtType.Datatype s d)) w (__smtx_type_default_rec TF TU))) =
        1 + sizeOf seed + sizeOf
          (native_ite (native_Teq TF (SmtType.Datatype s d)) w (__smtx_type_default_rec TF TU)) := by rfl
      omega
  | SmtDatatypeCons.unit, cU, seed => by simp [build_cons]
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.unit, seed => by simp [build_cons]
  termination_by cF _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

def has_self_rec (s : native_String) (d : SmtDatatype) : SmtDatatypeCons → Prop
  | SmtDatatypeCons.cons TF cF => native_Teq TF (SmtType.Datatype s d) = true ∨ has_self_rec s d cF
  | SmtDatatypeCons.unit => False

theorem build_cons_size (s : native_String) (d : SmtDatatype) (w : SmtValue) :
    ∀ (cF cU : SmtDatatypeCons), DtcSubstStar cF cU → has_self_rec s d cF →
      ∀ (seed : SmtValue), sizeOf w ≤ sizeOf (build_cons s d w cF cU seed)
  | SmtDatatypeCons.unit, cU, hc, hsr, seed => by simp [has_self_rec] at hsr
  | SmtDatatypeCons.cons TF cF, cU, hc, hsr, seed => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        rw [build_cons]
        by_cases hself : native_Teq TF (SmtType.Datatype s d) = true
        · have hINJ : native_ite (native_Teq TF (SmtType.Datatype s d)) w
              (__smtx_type_default_rec TF TU) = w := by rw [native_ite, if_pos hself]
          rw [hINJ]
          have hmono := build_cons_mono s d w cF cU (SmtValue.Apply seed w)
          have happ : sizeOf (SmtValue.Apply seed w) = 1 + sizeOf seed + sizeOf w := by rfl
          omega
        · have hsrTail : has_self_rec s d cF := Or.resolve_left hsr hself
          exact build_cons_size s d w cF cU hcc hsrTail _
  termination_by cF _ _ _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

/-- The core growth step: from any canonical typed value, build a strictly larger one.
This is where the constructor-selection combinatorics (self-recursive nesting vs.
base-infinite field) lives. -/
private theorem grow_witness
    (s : native_String) (d : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (hWf : __smtx_type_wf_rec (SmtType.Datatype s d) (SmtType.Datatype s d) = true)
    (hInf : __smtx_is_finite_datatype d = false)
    (w : SmtValue) (hwTy : __smtx_typeof_value w = SmtType.Datatype s d)
    (hwCan : __smtx_value_canonical_bool w = true) :
    ∃ w' : SmtValue, __smtx_typeof_value w' = SmtType.Datatype s d ∧
      __smtx_value_canonical_bool w' = true ∧ sizeOf w < sizeOf w' := by
  sorry

private theorem infinite_datatype_large_witness :
    ∀ (N : Nat) (s : native_String) (d : SmtDatatype),
      native_inhabited_type (SmtType.Datatype s d) = true →
      __smtx_type_wf_rec (SmtType.Datatype s d) (SmtType.Datatype s d) = true →
      __smtx_is_finite_datatype d = false →
      ∃ i : SmtValue, __smtx_typeof_value i = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool i = true ∧ N ≤ sizeOf i := by
  intro N
  induction N with
  | zero =>
      intro s d hInh hWf hInf
      have hd := type_default_typed_canonical_of_native_inhabited hInh
      exact ⟨__smtx_type_default (SmtType.Datatype s d), hd.1, hd.2, Nat.zero_le _⟩
  | succ k ih =>
      intro s d hInh hWf hInf
      rcases ih s d hInh hWf hInf with ⟨w, hwTy, hwCan, hwSize⟩
      rcases grow_witness s d hInh hWf hInf w hwTy hwCan with ⟨w', hw'Ty, hw'Can, hw'Size⟩
      exact ⟨w', hw'Ty, hw'Can, by omega⟩

/-- RESIDUAL: an inhabited, well-formed, infinite datatype has typed canonical
inhabitants avoiding any finite list — reduced to `infinite_datatype_large_witness`. -/
theorem cpc_infinite_datatype_fresh_value_assumption
    (s : native_String) (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) (SmtType.Datatype s d) = true)
    (_hInfinite : __smtx_is_finite_type (SmtType.Datatype s d) = false)
    (avoid : List SmtValue) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool i = true ∧
          ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false := by
  have hInf : __smtx_is_finite_datatype d = false := by
    simpa [__smtx_is_finite_type] using _hInfinite
  exact datatype_fresh_of_size_bound
    (infinite_datatype_large_witness (smt_value_size_bound avoid) s d _hInh _hRec hInf)

private theorem inhabited_of_finite_wf {T : SmtType}
    (hfin : __smtx_is_finite_type T = true) (hwf : __smtx_type_wf_rec T T = true) :
    native_inhabited_type T = true := by
  have hne : __smtx_type_default T ≠ SmtValue.NotValue := by
    have := fin_defaultable T T (ShT.refl T) hfin hwf
    simpa [__smtx_type_default] using this
  have hTyped : __smtx_typeof_value (__smtx_type_default T) = T :=
    (type_default_notvalue_or_typed T).resolve_left hne
  have hTne : T ≠ SmtType.None := by intro h; subst T; simp [__smtx_is_finite_type] at hfin
  simp only [native_inhabited_type, native_and, native_not, native_Teq, hTyped]
  simp [native_Teq, hTne]

/-- typeof of a constructor tag `DtCons s d n` of a finite datatype `d`, as a `chainType`. -/
private theorem typeof_dtcons_chain {s : native_String} {d : SmtDatatype} (n : native_Nat)
    {cF : SmtDatatypeCons} {dRest : SmtDatatype}
    (hFinD : __smtx_is_finite_datatype d = true)
    (hdrop : drop_cons d n = SmtDatatype.sum cF dRest) :
    __smtx_typeof_value (SmtValue.DtCons s d n) = chainType cF (SmtType.Datatype s d) := by
  have hsub : __smtx_dt_substitute s d d = d := subst_D_fin_id s d d hFinD
  simp only [__smtx_typeof_value, hsub]
  exact drop_lemma (SmtType.Datatype s d) d n cF dRest hdrop

private theorem apply_seed_typeof {v arg : SmtValue} {TU : SmtType} {c' : SmtDatatypeCons}
    {base : SmtType}
    (hv : __smtx_typeof_value v = chainType (SmtDatatypeCons.cons TU c') base)
    (harg : __smtx_typeof_value arg = TU) (hTUne : TU ≠ SmtType.None) :
    __smtx_typeof_value (SmtValue.Apply v arg) = chainType c' base := by
  have hchain : chainType (SmtDatatypeCons.cons TU c') base =
      SmtType.DtcAppType TU (chainType c' base) := rfl
  rw [hchain] at hv
  simp only [__smtx_typeof_value, hv, harg, __smtx_typeof_apply_value,
             __smtx_typeof_guard, native_Teq, native_ite, decide_true, if_true]
  simp [hTUne]

-- TODO(typeWf-0701 aliasing refactor): this mutual block threaded an ambient `RefList`
-- (`refs`/`hRoot : s ∈ refs`) under the old reflist-scoped algorithm to track "which enclosing
-- datatype name we're unfolding under". The new algorithm performs only a single self-substitution
-- per `Datatype` node (no ambient scope at all), so signatures are corrected to the diagonal form
-- and bodies `sorry`'d, matching the `fin_defaultable`/`cons_defaultable` gap in
-- `FiniteDefaultable.lean` that this mutual block builds on. All three are `private` and (besides
-- calling each other) used only by the public `cpc_finite_nonunit_datatype_nondefault_value_assumption`
-- below, whose own signature is unaffected.
mutual

private theorem finite_nonunit_type_nondefault_value :
    ∀ (T : SmtType),
      native_inhabited_type T = true → __smtx_type_wf_rec T T = true →
        __smtx_is_finite_type T = true → __smtx_is_unit_type T = false →
          ∃ e : SmtValue, __smtx_typeof_value e = T ∧ __smtx_value_canonical_bool e = true ∧
            native_veq e (__smtx_type_default T) = false
  | T, hInh, hRec, hFin, hNU => by sorry

private theorem finite_nonunit_datatype_nondefault_value :
    ∀ (s : native_String) (d : SmtDatatype),
      native_inhabited_type (SmtType.Datatype s d) = true →
      __smtx_type_wf_rec (SmtType.Datatype s d) (SmtType.Datatype s d) = true →
      __smtx_is_finite_type (SmtType.Datatype s d) = true →
      __smtx_is_unit_type (SmtType.Datatype s d) = false →
        ∃ e : SmtValue, __smtx_typeof_value e = SmtType.Datatype s d ∧
          __smtx_value_canonical_bool e = true ∧
          native_veq e (__smtx_type_default (SmtType.Datatype s d)) = false
  | s, d, hInh, hRec, hFin, hNU => by sorry

private theorem finite_nonunit_datatype_cons_nondefault_value
    (s : native_String) (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons),
      __smtx_dt_cons_wf_rec c c = true → __smtx_is_finite_datatype_cons c = true →
      __smtx_is_unit_datatype_cons c = false →
      ∀ (v : SmtValue), __smtx_typeof_value v = chainType c (SmtType.Datatype s d) →
        __smtx_value_canonical_bool v = true → v ≠ SmtValue.NotValue →
          ∃ e : SmtValue, __smtx_typeof_value e = SmtType.Datatype s d ∧
            __smtx_value_canonical_bool e = true ∧
            native_veq e (__smtx_datatype_cons_default v c c) = false
  | c, hWf, hFin, hNU, v, hvTy, hvCan, hvNe => by sorry

end

/-- RESIDUAL (sorry): a finite, non-unit, well-formed datatype has a typed
canonical inhabitant distinct from its default.  Formerly proved by the
value-substitution "inhabit" construction. -/
theorem cpc_finite_nonunit_datatype_nondefault_value_assumption
    (s : native_String) (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) (SmtType.Datatype s d) = true)
    (_hFinite : __smtx_is_finite_type (SmtType.Datatype s d) = true)
    (_hNonUnit : __smtx_is_unit_type (SmtType.Datatype s d) = false) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool e = true ∧
          native_veq e (__smtx_type_default (SmtType.Datatype s d)) = false := by
  exact finite_nonunit_datatype_nondefault_value s d _hInh _hRec _hFinite _hNonUnit


-- === non-default typed canonical value (non-datatype cases direct) ===

theorem cpc_nonunit_typed_canonical_nondefault_value
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A A = true)
    (_hNonUnit : __smtx_is_unit_type A = false) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = A ∧
        __smtx_value_canonical_bool e = true ∧
          native_veq e (__smtx_type_default A) = false := by
  classical
  cases A with
  | None =>
      simp [__smtx_type_wf_rec] at _hRec
  | Bool =>
      refine ⟨SmtValue.Boolean true, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, __smtx_type_default_rec, native_veq]
  | Int =>
      refine ⟨SmtValue.Numeral 1, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, __smtx_type_default_rec, native_veq]
  | Real =>
      refine ⟨SmtValue.Rational (1 : native_Rat), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical_bool]
      · exact native_veq_eq_false_of_ne (by native_decide)
  | RegLan =>
      simp [__smtx_type_wf_rec] at _hRec
  | BitVec w =>
      cases w with
      | zero =>
          simp [__smtx_is_unit_type, native_nateq] at _hNonUnit
      | succ w =>
          refine
            ⟨SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1, ?_, ?_, ?_⟩
          · exact bitvec_succ_one_typeof w
          · exact bitvec_succ_one_canonical w
          · exact bitvec_succ_one_ne_default w
  | Map T U =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U U = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      have hUNonUnit : __smtx_is_unit_type U = false := by
        simpa [__smtx_is_unit_type] using _hNonUnit
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      have hUDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.2.2.1
      rcases cpc_nonunit_typed_canonical_nondefault_value
          U hRecParts.2.2.1 hRecParts.2.2.2 hUNonUnit with
        ⟨e, heTy, heCan, heNeDefault⟩
      have heNeDefaultProp : e ≠ __smtx_type_default U := by
        intro hEq
        subst e
        simp [native_veq] at heNeDefault
      refine
        ⟨SmtValue.Map
          (SmtMap.cons (__smtx_type_default T) e
            (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          hTDefault.1, heTy, hUDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_msm_get_default, hTDefault.2, heCan, hUDefault.1,
          hUDefault.2, heNeDefaultProp, native_and, native_ite, native_not,
          native_veq]
      · have hUNV : __smtx_type_default U ≠ SmtValue.NotValue :=
          type_default_ne_notValue_of_native_inhabited hRecParts.2.2.1
            (ne_none_of_native_inhabited hRecParts.2.2.1)
        have hcond :
            decide (__smtx_type_default_rec U U = SmtValue.NotValue) = false := by
          apply decide_eq_false
          simpa [__smtx_type_default] using hUNV
        simp [__smtx_type_default, __smtx_type_default_rec, native_veq, native_ite, hcond]
  | Set T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      refine
        ⟨SmtValue.Set
          (SmtMap.cons (__smtx_type_default T) (SmtValue.Boolean true)
            (SmtMap.default T (SmtValue.Boolean false))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type, hTDefault.1, native_ite, native_Teq]
      · have hBoolDef : __smtx_type_default SmtType.Bool = SmtValue.Boolean false := by
          simp [__smtx_type_default, __smtx_type_default_rec]
        cases hFin : __smtx_is_finite_type T <;>
          simp [__smtx_value_canonical_bool, __smtx_map_canonical,
            __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
            __smtx_msm_get_default, hTDefault.2, hBoolDef, hFin, native_and, native_ite,
            native_not, native_veq, __smtx_typeof_value]
      · simp [__smtx_type_default, __smtx_type_default_rec, native_veq]
  | Seq T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      refine
        ⟨SmtValue.Seq (SmtSeq.cons (__smtx_type_default T) (SmtSeq.empty T)),
          ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_seq_value,
          hTDefault.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_seq_canonical,
          hTDefault.2, native_and]
      · simp [__smtx_type_default, __smtx_type_default_rec, native_veq]
  | Char =>
      exact ⟨SmtValue.Char 1, by native_decide, by native_decide, by native_decide⟩
  | Datatype s d =>
      by_cases hFinite :
          __smtx_is_finite_type (SmtType.Datatype s d) = true
      · exact cpc_finite_nonunit_datatype_nondefault_value_assumption
          s d _hInh _hRec hFinite _hNonUnit
      · have hInfinite :
            __smtx_is_finite_type (SmtType.Datatype s d) = false := by
          cases h : __smtx_is_finite_type (SmtType.Datatype s d) <;>
            simp [h] at hFinite ⊢
        rcases cpc_infinite_datatype_fresh_value_assumption
            s d _hInh _hRec hInfinite
            [__smtx_type_default (SmtType.Datatype s d)] with
          ⟨e, heTy, heCan, heFresh⟩
        refine ⟨e, heTy, heCan, ?_⟩
        exact native_veq_false_symm
          (heFresh (__smtx_type_default (SmtType.Datatype s d)) (by simp))
  | TypeRef s =>
      simp [__smtx_type_wf_rec] at _hRec
  | USort u =>
      refine ⟨SmtValue.UValue u 1, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, __smtx_type_default_rec, native_veq]
  | FunType T U =>
      simp [__smtx_type_wf_rec] at _hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at _hRec
termination_by sizeOf A

-- === fresh typed canonical value for infinite types ===

theorem cpc_fresh_typed_canonical_value_for_infinite_type_assumption
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A A = true)
    (_hInfinite : __smtx_is_finite_type A = false)
    (avoid : List SmtValue) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical_bool i = true ∧
          ∀ j : SmtValue, j ∈ avoid -> native_veq j i = false := by
  classical
  cases A with
  | None =>
      simp [__smtx_type_wf_rec] at _hRec
  | Bool =>
      simp [__smtx_is_finite_type] at _hInfinite
  | Int =>
      refine ⟨SmtValue.Numeral (Int.ofNat (fresh_numeral_index avoid)), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical_bool]
      · exact fresh_numeral_veq_false_of_mem avoid
  | Real =>
      refine ⟨SmtValue.Rational (Int.ofNat (fresh_rational_index avoid)), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical_bool]
      · exact fresh_rational_veq_false_of_mem avoid
  | RegLan =>
      simp [__smtx_type_wf_rec] at _hRec
  | BitVec w =>
      simp [__smtx_is_finite_type] at _hInfinite
  | Map T U =>
      by_cases hUInfinite : __smtx_is_finite_type U = false
      · have hRecParts :
            native_inhabited_type T = true ∧
              __smtx_type_wf_rec T T = true ∧
                native_inhabited_type U = true ∧
                  __smtx_type_wf_rec U U = true := by
          simpa [__smtx_type_wf_rec, native_and] using _hRec
        have hTDefault :
            __smtx_typeof_value (__smtx_type_default T) = T ∧
              __smtx_value_canonical_bool (__smtx_type_default T) = true := by
          exact type_default_typed_canonical_of_native_inhabited hRecParts.1
        have hUDefault :
            __smtx_typeof_value (__smtx_type_default U) = U ∧
              __smtx_value_canonical_bool (__smtx_type_default U) = true := by
          exact type_default_typed_canonical_of_native_inhabited hRecParts.2.2.1
        rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
            U hRecParts.2.2.1 hRecParts.2.2.2 hUInfinite
              (__smtx_type_default U :: smt_map_head_values avoid) with
          ⟨e, heTy, heCan, heFresh⟩
        have hDefaultNe : native_veq (__smtx_type_default U) e = false :=
          heFresh (__smtx_type_default U) (by simp)
        have hEntryNe : native_veq e (__smtx_type_default U) = false :=
          native_veq_false_symm hDefaultNe
        have hEntryNeProp : e ≠ __smtx_type_default U := by
          intro hEq
          subst e
          simp [native_veq] at hEntryNe
        refine
          ⟨SmtValue.Map
            (SmtMap.cons (__smtx_type_default T) e
              (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
        · simp [__smtx_typeof_value, __smtx_typeof_map_value,
            hTDefault.1, hUDefault.1, heTy, native_ite, native_Teq]
        · by_cases hTFinite : __smtx_is_finite_type T = true
          · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
              __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
              __smtx_msm_get_default, hTDefault.2, hUDefault.1, hUDefault.2,
              heCan, hTFinite, hEntryNeProp, native_and, native_ite, native_not,
              native_veq]
          · have hTFiniteFalse : __smtx_is_finite_type T = false := by
              cases hTF : __smtx_is_finite_type T <;> simp [hTF] at hTFinite ⊢
            simp [__smtx_value_canonical_bool, __smtx_map_canonical,
              __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
              __smtx_msm_get_default, hTDefault.2, hUDefault.2, heCan,
              hTFiniteFalse, hEntryNeProp, native_and, native_ite, native_not,
              native_veq]
        · intro j hj
          exact native_veq_eq_false_of_ne (by
            intro hEq
            subst j
            have heMem : e ∈ smt_map_head_values avoid :=
              smt_map_head_value_mem_of_mem (__smtx_type_default T) e
                (SmtMap.default T (__smtx_type_default U)) hj
            have heFalse := heFresh e (by simp [heMem])
            simp [native_veq] at heFalse)
      · exact
          by
            have hRecParts :
                native_inhabited_type T = true ∧
                  __smtx_type_wf_rec T T = true ∧
                    native_inhabited_type U = true ∧
                      __smtx_type_wf_rec U U = true := by
              simpa [__smtx_type_wf_rec, native_and] using _hRec
            have hUFinite : __smtx_is_finite_type U = true := by
              cases hUF : __smtx_is_finite_type U <;> simp [hUF] at hUInfinite ⊢
            have hFiniteParts :
                __smtx_is_unit_type U = false ∧
                  __smtx_is_finite_type T = false := by
              cases hUnit : __smtx_is_unit_type U <;>
                cases hTFin : __smtx_is_finite_type T <;>
                  simp [__smtx_is_finite_type, hUnit, hTFin, hUFinite,
                    native_or, native_and] at _hInfinite ⊢
            have hUDefault :
                __smtx_typeof_value (__smtx_type_default U) = U ∧
                  __smtx_value_canonical_bool (__smtx_type_default U) = true := by
              exact type_default_typed_canonical_of_native_inhabited hRecParts.2.2.1
            rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
                T hRecParts.1 hRecParts.2.1 hFiniteParts.2
                  (smt_map_head_keys avoid) with
              ⟨k, hkTy, hkCan, hkFresh⟩
            rcases cpc_nonunit_typed_canonical_nondefault_value
                U hRecParts.2.2.1 hRecParts.2.2.2 hFiniteParts.1 with
              ⟨e, heTy, heCan, heNeDefault⟩
            have heNeDefaultProp : e ≠ __smtx_type_default U := by
              intro hEq
              subst e
              simp [native_veq] at heNeDefault
            refine
              ⟨SmtValue.Map
                (SmtMap.cons k e
                  (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
            · simp [__smtx_typeof_value, __smtx_typeof_map_value,
                hkTy, heTy, hUDefault.1, native_ite, native_Teq]
            · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
                __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
                __smtx_msm_get_default, hkCan, heCan, hUDefault.2,
                hFiniteParts.2, heNeDefaultProp, native_and, native_ite,
                native_not, native_veq]
            · intro j hj
              exact native_veq_eq_false_of_ne (by
                intro hEq
                subst j
                have hkMem : k ∈ smt_map_head_keys avoid :=
                  smt_map_head_key_mem_of_mem k e
                    (SmtMap.default T (__smtx_type_default U)) hj
                have hkFalse := hkFresh k hkMem
                simp [native_veq] at hkFalse)
  | Set T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      have hTInfinite : __smtx_is_finite_type T = false := by
        simpa [__smtx_is_finite_type] using _hInfinite
      rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
          T hRecParts.1 hRecParts.2 hTInfinite (smt_set_head_keys avoid) with
        ⟨x, hxTy, hxCan, hxFresh⟩
      refine
        ⟨SmtValue.Set
          (SmtMap.cons x (SmtValue.Boolean true)
            (SmtMap.default T (SmtValue.Boolean false))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value,
          __smtx_map_to_set_type, hxTy, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_msm_get_default, hxCan, hTInfinite, native_and, native_ite,
          native_not, native_veq]
      · intro j hj
        exact native_veq_eq_false_of_ne (by
          intro hEq
          subst j
          have hxMem : x ∈ smt_set_head_keys avoid :=
            smt_set_head_key_mem_of_mem x (SmtValue.Boolean true)
              (SmtMap.default T (SmtValue.Boolean false)) hj
          have hxFalse := hxFresh x hxMem
          simp [native_veq] at hxFalse)
  | Seq T =>
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true := by
        simpa [__smtx_type_wf_rec, native_and] using _hRec
      rcases seq_inhabited_large_witness T hRecParts.1
          (smt_value_size_bound avoid) with
        ⟨i, hiTy, hiCan, hiSize⟩
      refine ⟨i, hiTy, hiCan, ?_⟩
      intro j hj
      exact native_veq_false_of_mem_and_size_bound hj hiSize
  | Char =>
      simp [__smtx_is_finite_type] at _hInfinite
  | Datatype s d =>
      exact
        cpc_infinite_datatype_fresh_value_assumption
          s d _hInh _hRec _hInfinite avoid
  | TypeRef s =>
      simp [__smtx_type_wf_rec] at _hRec
  | USort u =>
      refine ⟨SmtValue.UValue u (fresh_usort_index u avoid), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value]
      · simp [__smtx_value_canonical_bool]
      · exact fresh_usort_veq_false_of_mem u avoid
  | FunType T U =>
      simp [__smtx_type_wf_rec] at _hRec
  | DtcAppType T U =>
      simp [__smtx_type_wf_rec] at _hRec
termination_by sizeOf A

-- === map-lookup freshness + the consumed deliverable ===

private theorem msm_lookup_eq_default_of_fresh_keys :
    ∀ (m : SmtMap) (i : SmtValue),
      (∀ j : SmtValue, j ∈ smt_map_keys m -> native_veq j i = false) ->
        __smtx_msm_lookup m i = __smtx_msm_get_default m
  | SmtMap.default T e, i, _hFresh => by
      simp [__smtx_msm_lookup, __smtx_msm_get_default]
  | SmtMap.cons j e m, i, hFresh => by
      have hj : native_veq j i = false := hFresh j (by simp [smt_map_keys])
      have hmFresh :
          ∀ k : SmtValue, k ∈ smt_map_keys m -> native_veq k i = false := by
        intro k hk
        exact hFresh k (by simp [smt_map_keys, hk])
      have hmLookup :
          __smtx_msm_lookup m i = __smtx_msm_get_default m :=
        msm_lookup_eq_default_of_fresh_keys m i hmFresh
      simpa [smt_map_keys, __smtx_msm_lookup, __smtx_msm_get_default,
        native_ite, hj] using hmLookup

/--
Fresh-index theorem for infinite map domains.

When the executable map-difference proof needs to compare the two default
payloads of canonical maps over an infinite domain, it needs a typed canonical
index outside both finite spines.
-/
theorem cpc_fresh_default_lookup_for_infinite_map_domain_assumption
    (m1 m2 : SmtMap)
    (A B : SmtType)
    (_hm1Ty : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (_hm2Ty : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (_hm1Can : __smtx_map_canonical m1 = true)
    (_hm2Can : __smtx_map_canonical m2 = true)
    (hAInh : native_inhabited_type A = true)
    (hARec : __smtx_type_wf_rec A A = true)
    (_hInfinite : __smtx_is_finite_type A = false) :
    ∃ i : SmtValue,
      __smtx_typeof_value i = A ∧
        __smtx_value_canonical_bool i = true ∧
          __smtx_msm_lookup m1 i = __smtx_msm_get_default m1 ∧
            __smtx_msm_lookup m2 i = __smtx_msm_get_default m2 := by
  rcases cpc_fresh_typed_canonical_value_for_infinite_type_assumption
      A hAInh hARec _hInfinite (smt_map_keys m1 ++ smt_map_keys m2) with
    ⟨i, hiTy, hiCan, hiFresh⟩
  refine ⟨i, hiTy, hiCan, ?_, ?_⟩
  · exact msm_lookup_eq_default_of_fresh_keys m1 i (by
      intro j hj
      exact hiFresh j (by simp [hj]))
  · exact msm_lookup_eq_default_of_fresh_keys m2 i (by
      intro j hj
      exact hiFresh j (by simp [hj]))

end Smtm
