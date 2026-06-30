import Cpc.Proofs.TypePreservation.Predicates
import Cpc.Proofs.SmtWfCompat
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

private theorem dt_wf_cons_of_wf {c : SmtDatatypeCons} {d : SmtDatatype} {refs : RefList}
    (h : dtAllWf (SmtDatatype.sum c d) refs = true) :
    __smtx_dt_cons_wf_rec c refs = true := by
  by_cases hc : __smtx_dt_cons_wf_rec c refs = true
  · exact hc
  · have hFalse : dtAllWf (SmtDatatype.sum c d) refs = false := by
      cases d <;> simp [dtAllWf, native_ite, hc]
    rw [hFalse] at h; simp at h

private theorem dt_wf_tail_of_nonempty_tail_wf {c cTail : SmtDatatypeCons} {dTail : SmtDatatype}
    {refs : RefList}
    (h : dtAllWf (SmtDatatype.sum c (SmtDatatype.sum cTail dTail)) refs = true) :
    dtAllWf (SmtDatatype.sum cTail dTail) refs = true := by
  have hc : __smtx_dt_cons_wf_rec c refs = true := dt_wf_cons_of_wf h
  simpa [dtAllWf, native_ite, hc] using h

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

/-- Strict version of `build_cons_size`: with a self-recursive field, the built value is strictly
larger than the injected `w`. -/
theorem build_cons_size_strict (s : native_String) (d : SmtDatatype) (w : SmtValue) :
    ∀ (cF cU : SmtDatatypeCons), DtcSubstStar cF cU → has_self_rec s d cF →
      ∀ (seed : SmtValue), sizeOf w < sizeOf (build_cons s d w cF cU seed)
  | SmtDatatypeCons.unit, cU, _hc, hsr, seed => by simp [has_self_rec] at hsr
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
          exact build_cons_size_strict s d w cF cU hcc hsrTail _
  termination_by cF _ _ _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

/-- `SomeDefaultable s d n DF DU`: some constructor at or after position `n` (in the paired
folded/raw constructor lists `DF`/`DU`) has a non-`NotValue` default. -/
inductive SomeDefaultable (s : native_String) (d : SmtDatatype) :
    native_Nat → SmtDatatype → SmtDatatype → Prop where
  | head {n : native_Nat} {cF cU : SmtDatatypeCons} {DF DU : SmtDatatype} :
      __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU ≠ SmtValue.NotValue →
      SomeDefaultable s d n (SmtDatatype.sum cF DF) (SmtDatatype.sum cU DU)
  | tail {n : native_Nat} {cF cU : SmtDatatypeCons} {DF DU : SmtDatatype} :
      SomeDefaultable s d (native_nat_succ n) DF DU →
      SomeDefaultable s d n (SmtDatatype.sum cF DF) (SmtDatatype.sum cU DU)

/-- If some constructor is defaultable, the datatype default selects a non-`NotValue` value. -/
theorem datatype_default_ne_nv_of_some (s : native_String) (d : SmtDatatype) :
    ∀ (n : native_Nat) (DF DU : SmtDatatype),
      SomeDefaultable s d n DF DU →
      __smtx_datatype_default s d n DF DU ≠ SmtValue.NotValue := by
  intro n DF DU h
  induction h with
  | @head n cF cU DF DU hcF =>
      rw [datatype_default_select s d n cF cU DF DU hcF]; exact hcF
  | @tail n cF cU DF DU _htail ih =>
      by_cases heq : __smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU = SmtValue.NotValue
      · rw [__smtx_datatype_default]
        have hf : native_veq (__smtx_datatype_cons_default (SmtValue.DtCons s d n) cF cU)
            SmtValue.NotValue = true := by simp [native_veq, heq]
        simp [native_ite, native_not, hf]; exact ih
      · rw [datatype_default_select s d n cF cU DF DU heq]; exact heq

/-- Head-field well-formedness from a closed constructor's well-formedness. -/
private theorem cons_wf_nil_head {TU : SmtType} {cU : SmtDatatypeCons}
    (hwf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TU cU) native_reflist_nil = true) :
    __smtx_type_wf_rec TU native_reflist_nil = true := by
  cases TU with
  | TypeRef s =>
      simp [__smtx_dt_cons_wf_rec, native_reflist_contains, native_reflist_nil, native_ite] at hwf
  | None => simp [__smtx_dt_cons_wf_rec, native_ite, __smtx_type_wf_rec] at hwf
  | FunType A B => simp [__smtx_dt_cons_wf_rec, native_ite, __smtx_type_wf_rec] at hwf
  | DtcAppType A B => simp [__smtx_dt_cons_wf_rec, native_ite, __smtx_type_wf_rec] at hwf
  | Bool => simp [__smtx_type_wf_rec]
  | Int => simp [__smtx_type_wf_rec]
  | Real => simp [__smtx_type_wf_rec]
  | RegLan => simp [__smtx_dt_cons_wf_rec, native_ite, __smtx_type_wf_rec] at hwf
  | BitVec w => simp [__smtx_type_wf_rec]
  | Char => simp [__smtx_type_wf_rec]
  | USort i => simp [__smtx_type_wf_rec]
  | Datatype s2 d2 =>
      simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
      split at hwf
      · next h => exact h
      · next h => exact absurd hwf (by simp)
  | Seq A =>
      simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
      split at hwf
      · next h => exact h
      · next h => exact absurd hwf (by simp)
  | Set A =>
      simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
      split at hwf
      · next h => exact h
      · next h => exact absurd hwf (by simp)
  | Map A B =>
      simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
      split at hwf
      · next h => exact h
      · next h => exact absurd hwf (by simp)

/-- Tail well-formedness from a closed constructor's well-formedness. -/
private theorem cons_wf_nil_tail {TU : SmtType} {cU : SmtDatatypeCons}
    (hwf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TU cU) native_reflist_nil = true) :
    __smtx_dt_cons_wf_rec cU native_reflist_nil = true := by
  cases TU with
  | TypeRef s =>
      simp [__smtx_dt_cons_wf_rec, native_reflist_contains, native_reflist_nil, native_ite] at hwf
  | _ =>
      simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
      split at hwf
      · next h => exact hwf
      · next h => exact absurd hwf (by simp)

/-- Name-independent "has a base constructor" (a closed-well-formed constructor). -/
def DtHasBase : SmtDatatype → Prop
  | SmtDatatype.null => False
  | SmtDatatype.sum c d => __smtx_dt_cons_wf_rec c native_reflist_nil = true ∨ DtHasBase d

private theorem dt_has_base_of_wf_gen (s : native_String) :
    ∀ (hb : native_Bool) (d : SmtDatatype),
      __smtx_dt_wf_rec s native_reflist_nil hb d = true → hb = true ∨ DtHasBase d
  | hb, SmtDatatype.null => by intro h; left; simpa [__smtx_dt_wf_rec] using h
  | hb, SmtDatatype.sum c d => by
      intro h
      simp only [__smtx_dt_wf_rec, native_and, Bool.and_eq_true] at h
      rcases dt_has_base_of_wf_gen s (native_or hb (__smtx_dt_cons_wf_rec c native_reflist_nil)) d h.2
        with hb' | hbase
      · simp only [native_or, Bool.or_eq_true] at hb'
        rcases hb' with hh | hc
        · left; exact hh
        · right; left; exact hc
      · right; right; exact hbase

private theorem dt_has_base_of_wf (s : native_String) (d : SmtDatatype)
    (h : __smtx_dt_wf_rec s native_reflist_nil false d = true) : DtHasBase d :=
  (dt_has_base_of_wf_gen s false d h).resolve_left (by simp)

/-! ### Founded-defaultability kernel — the infinite-tolerant analog of `fin_defaultable`.
A well-formed field is defaultable; a well-formed (founded) closed datatype has a defaultable
constructor; a closed well-formed constructor is defaultable.  Mutually recursive on `sizeOf`. -/
mutual

/-- A closed well-formed field type has a non-`NotValue` default. -/
theorem field_default_ne_nv_of_wf (TF TU : SmtType)
    (hfr : FieldRel TF TU) (hwf : __smtx_type_wf_rec TU native_reflist_nil = true) :
    __smtx_type_default_rec TF TU ≠ SmtValue.NotValue := by
  cases TU with
  | None => simp [__smtx_type_wf_rec] at hwf
  | TypeRef s => simp [__smtx_type_wf_rec] at hwf
  | FunType A B => simp [__smtx_type_wf_rec] at hwf
  | DtcAppType A B => simp [__smtx_type_wf_rec] at hwf
  | RegLan => simp [__smtx_type_wf_rec] at hwf
  | Bool => rw [__smtx_type_default_rec]; exact fun h => by cases h
  | Int => rw [__smtx_type_default_rec]; exact fun h => by cases h
  | Real => rw [__smtx_type_default_rec]; exact fun h => by cases h
  | BitVec w => rw [__smtx_type_default_rec]; exact fun h => by cases h
  | Char => rw [__smtx_type_default_rec]; exact fun h => by cases h
  | USort i => rw [__smtx_type_default_rec]; exact fun h => by cases h
  | Seq A => rw [__smtx_type_default_rec]; exact fun h => by cases h
  | Set A => rw [__smtx_type_default_rec]; exact fun h => by cases h
  | Map A B =>
      have hwfB : __smtx_type_wf_rec B native_reflist_nil = true := by
        simp only [__smtx_type_wf_rec, native_and, Bool.and_eq_true] at hwf; exact hwf.2.2.2
      have hB := field_default_ne_nv_of_wf B B (FieldRel.rel (SubstStar.refl B)) hwfB
      have hv : ¬ (native_veq (__smtx_type_default_rec B B) SmtValue.NotValue = true) := by
        rw [native_veq_eq_false_of_ne hB]; simp
      rw [__smtx_type_default_rec, native_ite, if_neg hv]
      exact fun h => by cases h
  | Datatype sU dU =>
      have hbase : DtHasBase dU :=
        dt_has_base_of_wf sU dU (dt_wf_rec_of_type_wf_rec_datatype sU dU native_reflist_nil hwf)
      cases hfr with
      | rel hss =>
          cases hss with
          | refl =>
              rw [__smtx_type_default_rec]
              exact datatype_default_ne_nv_of_some sU dU native_nat_zero
                (__smtx_dt_substitute sU dU dU) dU
                (dt_inhabited_aux sU dU native_nat_zero (__smtx_dt_substitute sU dU dU) dU
                  (dtSubstStar_of_subst sU dU dU) (drop_cons_zero _).symm hbase)
          | @dt sF sU' dF dU' hdt =>
              rw [__smtx_type_default_rec]
              exact datatype_default_ne_nv_of_some sF dF native_nat_zero
                (__smtx_dt_substitute sF dF dF) dU
                (dt_inhabited_aux sF dF native_nat_zero (__smtx_dt_substitute sF dF dF) dU
                  (dtSubstStar_subst sF dF hdt) (drop_cons_zero _).symm hbase)
      | forcesNV hnv =>
          exfalso
          have hdiag : __smtx_type_default_rec (SmtType.Datatype sU dU) (SmtType.Datatype sU dU)
              ≠ SmtValue.NotValue := by
            rw [__smtx_type_default_rec]
            exact datatype_default_ne_nv_of_some sU dU native_nat_zero
              (__smtx_dt_substitute sU dU dU) dU
              (dt_inhabited_aux sU dU native_nat_zero (__smtx_dt_substitute sU dU dU) dU
                (dtSubstStar_of_subst sU dU dU) (drop_cons_zero _).symm hbase)
          exact hdiag (hnv (SmtType.Datatype sU dU))
  termination_by sizeOf TU

/-- A closed founded datatype suffix has a defaultable constructor (in its folded/raw pairing). -/
theorem dt_inhabited_aux (s2 : native_String) (dF2 : SmtDatatype) :
    ∀ (n : native_Nat) (DF DU : SmtDatatype),
      DtSubstStar DF DU →
      DF = drop_cons (__smtx_dt_substitute s2 dF2 dF2) n →
      DtHasBase DU →
      SomeDefaultable s2 dF2 n DF DU
  | n, DF, DU, hdsub, hdrop, hbase => by
    cases hdsub with
    | null => simp [DtHasBase] at hbase
    | @sum cF cU dF' dU' hcc hdd =>
        rcases hbase with hb | hbtail
        · exact SomeDefaultable.head
            (cons_default_ne_nv_of_wf cF cU (SmtValue.DtCons s2 dF2 n) hcc hb (by intro h; cases h))
        · apply SomeDefaultable.tail
          have hdrop' : dF' = drop_cons (__smtx_dt_substitute s2 dF2 dF2) (native_nat_succ n) := by
            rw [drop_cons_succ, ← hdrop]
          exact dt_inhabited_aux s2 dF2 (native_nat_succ n) dF' dU' hdd hdrop' hbtail
  termination_by _ _ DU _ _ _ => sizeOf DU

/-- A closed well-formed constructor (a base) has a non-`NotValue` default. -/
theorem cons_default_ne_nv_of_wf (cF cU : SmtDatatypeCons) (v : SmtValue)
    (hc : DtcSubstStar cF cU)
    (hwf : __smtx_dt_cons_wf_rec cU native_reflist_nil = true)
    (hv : v ≠ SmtValue.NotValue) :
    __smtx_datatype_cons_default v cF cU ≠ SmtValue.NotValue := by
  cases hc with
  | unit => simpa [__smtx_datatype_cons_default] using hv
  | @cons TF TU cF' cU' hfr hcc =>
      have hwfTU : __smtx_type_wf_rec TU native_reflist_nil = true := cons_wf_nil_head hwf
      have hwfTail : __smtx_dt_cons_wf_rec cU' native_reflist_nil = true := cons_wf_nil_tail hwf
      have hfield : __smtx_type_default_rec TF TU ≠ SmtValue.NotValue :=
        field_default_ne_nv_of_wf TF TU hfr hwfTU
      have hv2 : ¬ (native_veq (__smtx_type_default_rec TF TU) SmtValue.NotValue = true) := by
        rw [native_veq_eq_false_of_ne hfield]; simp
      rw [__smtx_datatype_cons_default, native_ite, if_neg hv2]
      exact cons_default_ne_nv_of_wf cF' cU' (SmtValue.Apply v (__smtx_type_default_rec TF TU))
        hcc hwfTail (by intro h; cases h)
  termination_by sizeOf cU

end

/-- Founded ⇒ inhabited: a closed well-formed type has a typed, non-`None` default (the payoff of
the founded-`wf` refactor; the infinite-tolerant analog of `inhabited_of_finite_wf`). -/
theorem inhabited_of_wf (T : SmtType) (hwf : __smtx_type_wf_rec T native_reflist_nil = true) :
    native_inhabited_type T = true := by
  have hne : __smtx_type_default T ≠ SmtValue.NotValue := by
    have := field_default_ne_nv_of_wf T T (FieldRel.rel (SubstStar.refl T)) hwf
    simpa [__smtx_type_default] using this
  have hTyped : __smtx_typeof_value (__smtx_type_default T) = T :=
    (type_default_notvalue_or_typed T).resolve_left hne
  have hTne : T ≠ SmtType.None := by intro h; subst T; simp [__smtx_type_wf_rec] at hwf
  simp only [native_inhabited_type, native_and, native_not, native_Teq, hTyped]
  simp [native_Teq, hTne]

/-- `__smtx_type_wf_rec` reads `refs` only at `Datatype`/`TypeRef`; it is refs-independent
elsewhere.  Hence a non-datatype field that is well-formed in scope `refs` is closed-well-formed. -/
theorem type_wf_rec_refs_irrel_nondt :
    ∀ (T : SmtType) (refs : RefList),
      (∀ s2 d2, T ≠ SmtType.Datatype s2 d2) →
      __smtx_type_wf_rec T refs = __smtx_type_wf_rec T native_reflist_nil := by
  intro T refs hnd
  cases T <;> first | exact absurd rfl (hnd _ _) | rfl

/-- `TU` is a field of constructor `c`. -/
inductive FieldMem : SmtType → SmtDatatypeCons → Prop where
  | head {TU : SmtType} {c : SmtDatatypeCons} : FieldMem TU (SmtDatatypeCons.cons TU c)
  | tail {TU TU' : SmtType} {c : SmtDatatypeCons} :
      FieldMem TU c → FieldMem TU (SmtDatatypeCons.cons TU' c)

/-- Tail well-formedness from a constructor's well-formedness (any scope). -/
private theorem cons_wf_tail_gen {TU : SmtType} {cU : SmtDatatypeCons} {refs : RefList}
    (hwf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TU cU) refs = true) :
    __smtx_dt_cons_wf_rec cU refs = true := by
  cases TU with
  | TypeRef s =>
      simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
      split at hwf
      · next h => exact hwf
      · next h => exact absurd hwf (by simp)
  | _ =>
      simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
      split at hwf
      · next h => exact hwf
      · next h => exact absurd hwf (by simp)

/-- Head-field well-formedness for a non-`TypeRef` head (any scope). -/
private theorem cons_wf_head_gen {T : SmtType} {cU : SmtDatatypeCons} {refs : RefList}
    (hwf : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T cU) refs = true)
    (hnotTR : ∀ s, T ≠ SmtType.TypeRef s) :
    __smtx_type_wf_rec T refs = true := by
  cases T with
  | TypeRef s => exact absurd rfl (hnotTR s)
  | _ =>
      simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
      split at hwf
      · next h => exact h
      · next h => exact absurd hwf (by simp)

/-- A constructor well-formed at scope `{s}` with no nested-datatype fields has every field either
the self-reference `TypeRef s` or a closed (refs-`nil`) well-formed type. -/
theorem cons_fields_self_or_closed (s : native_String) :
    ∀ (c : SmtDatatypeCons),
      __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true →
      (∀ TU, FieldMem TU c → ∀ s2 d2, TU ≠ SmtType.Datatype s2 d2) →
      ∀ TU, FieldMem TU c →
        TU = SmtType.TypeRef s ∨ __smtx_type_wf_rec TU native_reflist_nil = true
  | SmtDatatypeCons.unit, _, _, _, hmem => by cases hmem
  | SmtDatatypeCons.cons T c', hwf, hnd, TU, hmem => by
      cases hmem with
      | head =>
          cases T with
          | TypeRef s'' =>
              left
              simp only [__smtx_dt_cons_wf_rec, native_ite] at hwf
              split at hwf
              · next hc =>
                  have hss : s'' = s := by
                    simpa [native_reflist_contains, native_reflist_insert, native_reflist_nil]
                      using hc
                  rw [hss]
              · next hc => exact absurd hwf (by simp)
          | Datatype s2 d2 => exact absurd rfl (hnd _ FieldMem.head s2 d2)
          | _ =>
              right
              have hTwf := cons_wf_head_gen hwf (by intro s' h; cases h)
              rw [type_wf_rec_refs_irrel_nondt _ (native_reflist_insert native_reflist_nil s)
                (by intro s2 d2 h; cases h)] at hTwf
              exact hTwf
      | tail hmemTail =>
          exact cons_fields_self_or_closed s c' (cons_wf_tail_gen hwf)
            (fun TU' h => hnd TU' (FieldMem.tail h)) TU hmemTail

/-- A folded constructor's fields are all defaultable-or-self, when every non-self field is closed
well-formed.  Provides `fields_ok` for the `build_cons` machinery. -/
theorem fields_ok_of_field_wf (s : native_String) (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons),
      (∀ TU, FieldMem TU c → TU = SmtType.TypeRef s ∨
        __smtx_type_wf_rec TU native_reflist_nil = true) →
      fields_ok s d (__smtx_dtc_substitute s d c) c
  | SmtDatatypeCons.unit, _ => by simp [__smtx_dtc_substitute, fields_ok]
  | SmtDatatypeCons.cons TU c, hfields => by
      simp only [__smtx_dtc_substitute, fields_ok]
      refine ⟨?_, fields_ok_of_field_wf s d c (fun TU' hmem => hfields TU' (FieldMem.tail hmem))⟩
      rcases hfields TU FieldMem.head with hself | hwfTU
      · subst hself
        left
        simp [__smtx_type_substitute, native_streq, native_ite, native_Teq]
      · right
        exact field_default_ne_nv_of_wf (__smtx_type_substitute s d TU) TU
          (fieldRel_of_type_subst s d TU) hwfTU

/-- `drop_cons` commutes with datatype substitution. -/
theorem drop_cons_subst (s : native_String) (d : SmtDatatype) :
    ∀ (n : native_Nat) (D : SmtDatatype),
      drop_cons (__smtx_dt_substitute s d D) n = __smtx_dt_substitute s d (drop_cons D n)
  | Nat.zero, D => by rw [drop_cons_zero, drop_cons_zero]
  | Nat.succ n, SmtDatatype.null => by simp [__smtx_dt_substitute, drop_cons]
  | Nat.succ n, SmtDatatype.sum c D => by
      simp only [__smtx_dt_substitute, drop_cons]
      exact drop_cons_subst s d n D

/-- Default every field of a constructor. -/
def build_inj_rest : SmtDatatypeCons → SmtDatatypeCons → SmtValue → SmtValue
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU, seed =>
      build_inj_rest cF cU (SmtValue.Apply seed (__smtx_type_default_rec TF TU))
  | _, _, seed => seed

/-- Build a constructor value injecting `v` at field position `k`, defaulting elsewhere. -/
def build_inj (v : SmtValue) :
    SmtDatatypeCons → SmtDatatypeCons → Nat → SmtValue → SmtValue
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU, Nat.zero, seed =>
      build_inj_rest cF cU (SmtValue.Apply seed v)
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU, Nat.succ k, seed =>
      build_inj v cF cU k (SmtValue.Apply seed (__smtx_type_default_rec TF TU))
  | _, _, _, seed => seed

/-- Every field is defaultable. -/
def inj_ok_rest : SmtDatatypeCons → SmtDatatypeCons → Prop
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU =>
      __smtx_type_default_rec TF TU ≠ SmtValue.NotValue ∧ inj_ok_rest cF cU
  | SmtDatatypeCons.unit, SmtDatatypeCons.unit => True
  | _, _ => False

/-- Field `k` matches `v`'s type; every other field is defaultable. -/
def inj_ok (v : SmtValue) : Nat → SmtDatatypeCons → SmtDatatypeCons → Prop
  | Nat.zero, SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU =>
      (__smtx_typeof_value v = TF ∧ TF ≠ SmtType.None) ∧ inj_ok_rest cF cU
  | Nat.succ k, SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU =>
      __smtx_type_default_rec TF TU ≠ SmtValue.NotValue ∧ inj_ok v k cF cU
  | _, _, _ => False

/-- Position `k` is a valid field index of the constructor. -/
def injPosValid : Nat → SmtDatatypeCons → Prop
  | Nat.zero, SmtDatatypeCons.cons _ _ => True
  | Nat.succ k, SmtDatatypeCons.cons _ c => injPosValid k c
  | _, SmtDatatypeCons.unit => False

/-- Typing of a fully-defaulted constructor application. -/
theorem build_inj_rest_typeof :
    ∀ (cF cU : SmtDatatypeCons), DtcSubstStar cF cU → inj_ok_rest cF cU →
      ∀ (seed : SmtValue) (base : SmtType),
        __smtx_typeof_value seed = chainType cF base →
        __smtx_typeof_value (build_inj_rest cF cU seed) = base
  | SmtDatatypeCons.unit, cU, hc, _hok, seed, base, hseed => by
      cases hc; simpa [build_inj_rest, chainType] using hseed
  | SmtDatatypeCons.cons TF cF, cU, hc, hok, seed, base, hseed => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        have hokP : __smtx_type_default_rec TF TU ≠ SmtValue.NotValue ∧ inj_ok_rest cF cU := by
          simpa [inj_ok_rest] using hok
        have hss : SubstStar TF TU := by
          cases hfr with
          | rel h => exact h
          | forcesNV h => exact absurd (h TF) hokP.1
        have hTFne : TF ≠ SmtType.None := by
          intro hNone; rw [hNone] at hss hokP
          cases hss with
          | refl => simp [__smtx_type_default_rec] at hokP
        have hTy : __smtx_typeof_value (__smtx_type_default_rec TF TU) = TF := by
          rcases datatype_kernel_rec TF TU hss with hNV | ⟨hTy, _⟩
          · exact absurd hNV hokP.1
          · exact hTy
        have hApply : __smtx_typeof_value
            (SmtValue.Apply seed (__smtx_type_default_rec TF TU)) = chainType cF base := by
          have hchain : chainType (SmtDatatypeCons.cons TF cF) base =
              SmtType.DtcAppType TF (chainType cF base) := rfl
          rw [hchain] at hseed
          have h1 : native_Teq TF TF = true := by simp [native_Teq]
          have h2 : native_Teq TF SmtType.None = false := by simp [native_Teq, hTFne]
          show __smtx_typeof_apply_value (__smtx_typeof_value seed)
            (__smtx_typeof_value (__smtx_type_default_rec TF TU)) = chainType cF base
          rw [hseed, hTy]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, h1, h2]
        rw [build_inj_rest]
        exact build_inj_rest_typeof cF cU hcc hokP.2 _ base hApply
  termination_by cF _ _ _ _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

theorem build_inj_rest_canonical :
    ∀ (cF cU : SmtDatatypeCons), DtcSubstStar cF cU → inj_ok_rest cF cU →
      ∀ (seed : SmtValue), __smtx_value_canonical_bool seed = true →
        __smtx_value_canonical_bool (build_inj_rest cF cU seed) = true
  | SmtDatatypeCons.unit, cU, hc, _hok, seed, hseed => by cases hc; simpa [build_inj_rest] using hseed
  | SmtDatatypeCons.cons TF cF, cU, hc, hok, seed, hseed => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        have hokP : __smtx_type_default_rec TF TU ≠ SmtValue.NotValue ∧ inj_ok_rest cF cU := by
          simpa [inj_ok_rest] using hok
        have hss : SubstStar TF TU := by
          cases hfr with
          | rel h => exact h
          | forcesNV h => exact absurd (h TF) hokP.1
        have hCan : __smtx_value_canonical_bool (__smtx_type_default_rec TF TU) = true := by
          rcases datatype_kernel_rec TF TU hss with hNV | ⟨_, hCan⟩
          · exact absurd hNV hokP.1
          · exact hCan
        rw [build_inj_rest]
        exact build_inj_rest_canonical cF cU hcc hokP.2 _ (by
          simp [__smtx_value_canonical_bool, hseed, hCan, native_and])
  termination_by cF _ _ _ _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

theorem build_inj_rest_mono :
    ∀ (cF cU : SmtDatatypeCons) (seed : SmtValue),
      sizeOf seed ≤ sizeOf (build_inj_rest cF cU seed)
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU, seed => by
      rw [build_inj_rest]
      have hrec := build_inj_rest_mono cF cU
        (SmtValue.Apply seed (__smtx_type_default_rec TF TU))
      have happ : sizeOf (SmtValue.Apply seed (__smtx_type_default_rec TF TU)) =
          1 + sizeOf seed + sizeOf (__smtx_type_default_rec TF TU) := by rfl
      omega
  | SmtDatatypeCons.unit, cU, seed => by simp [build_inj_rest]
  | SmtDatatypeCons.cons TF cF, SmtDatatypeCons.unit, seed => by simp [build_inj_rest]
  termination_by cF _ => sizeOf cF
  decreasing_by all_goals (try simp_wf); all_goals omega

theorem build_inj_typeof (v : SmtValue) :
    ∀ (k : Nat) (cF cU : SmtDatatypeCons), DtcSubstStar cF cU → inj_ok v k cF cU →
      ∀ (seed : SmtValue) (base : SmtType),
        __smtx_typeof_value seed = chainType cF base →
        __smtx_typeof_value (build_inj v cF cU k seed) = base
  | Nat.zero, SmtDatatypeCons.cons TF cF, cU, hc, hok, seed, base, hseed => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        have hokP : (__smtx_typeof_value v = TF ∧ TF ≠ SmtType.None) ∧ inj_ok_rest cF cU := by
          simpa [inj_ok] using hok
        have hApply : __smtx_typeof_value (SmtValue.Apply seed v) = chainType cF base := by
          have hchain : chainType (SmtDatatypeCons.cons TF cF) base =
              SmtType.DtcAppType TF (chainType cF base) := rfl
          rw [hchain] at hseed
          have h1 : native_Teq TF TF = true := by simp [native_Teq]
          have h2 : native_Teq TF SmtType.None = false := by simp [native_Teq, hokP.1.2]
          show __smtx_typeof_apply_value (__smtx_typeof_value seed)
            (__smtx_typeof_value v) = chainType cF base
          rw [hseed, hokP.1.1]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, h1, h2]
        rw [build_inj]
        exact build_inj_rest_typeof cF cU hcc hokP.2 _ base hApply
  | Nat.succ k, SmtDatatypeCons.cons TF cF, cU, hc, hok, seed, base, hseed => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        have hokP : __smtx_type_default_rec TF TU ≠ SmtValue.NotValue ∧ inj_ok v k cF cU := by
          simpa [inj_ok] using hok
        have hss : SubstStar TF TU := by
          cases hfr with
          | rel h => exact h
          | forcesNV h => exact absurd (h TF) hokP.1
        have hTFne : TF ≠ SmtType.None := by
          intro hNone; rw [hNone] at hss hokP
          cases hss with
          | refl => simp [__smtx_type_default_rec] at hokP
        have hTy : __smtx_typeof_value (__smtx_type_default_rec TF TU) = TF := by
          rcases datatype_kernel_rec TF TU hss with hNV | ⟨hTy, _⟩
          · exact absurd hNV hokP.1
          · exact hTy
        have hApply : __smtx_typeof_value
            (SmtValue.Apply seed (__smtx_type_default_rec TF TU)) = chainType cF base := by
          have hchain : chainType (SmtDatatypeCons.cons TF cF) base =
              SmtType.DtcAppType TF (chainType cF base) := rfl
          rw [hchain] at hseed
          have h1 : native_Teq TF TF = true := by simp [native_Teq]
          have h2 : native_Teq TF SmtType.None = false := by simp [native_Teq, hTFne]
          show __smtx_typeof_apply_value (__smtx_typeof_value seed)
            (__smtx_typeof_value (__smtx_type_default_rec TF TU)) = chainType cF base
          rw [hseed, hTy]
          simp [__smtx_typeof_apply_value, __smtx_typeof_guard, native_ite, h1, h2]
        rw [build_inj]
        exact build_inj_typeof v k cF cU hcc hokP.2 _ base hApply
  | k, SmtDatatypeCons.unit, cU, hc, hok, seed, base, hseed => by
      cases k <;> simp [inj_ok] at hok
  termination_by k _ _ _ _ _ _ => sizeOf k
  decreasing_by all_goals (try simp_wf); all_goals omega

theorem build_inj_canonical (v : SmtValue) (hvCan : __smtx_value_canonical_bool v = true) :
    ∀ (k : Nat) (cF cU : SmtDatatypeCons), DtcSubstStar cF cU → inj_ok v k cF cU →
      ∀ (seed : SmtValue), __smtx_value_canonical_bool seed = true →
        __smtx_value_canonical_bool (build_inj v cF cU k seed) = true
  | Nat.zero, SmtDatatypeCons.cons TF cF, cU, hc, hok, seed, hseed => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        have hokP : (__smtx_typeof_value v = TF ∧ TF ≠ SmtType.None) ∧ inj_ok_rest cF cU := by
          simpa [inj_ok] using hok
        rw [build_inj]
        exact build_inj_rest_canonical cF cU hcc hokP.2 _ (by
          simp [__smtx_value_canonical_bool, hseed, hvCan, native_and])
  | Nat.succ k, SmtDatatypeCons.cons TF cF, cU, hc, hok, seed, hseed => by
      cases hc with
      | @cons _ TU _ cU hfr hcc =>
        have hokP : __smtx_type_default_rec TF TU ≠ SmtValue.NotValue ∧ inj_ok v k cF cU := by
          simpa [inj_ok] using hok
        have hss : SubstStar TF TU := by
          cases hfr with
          | rel h => exact h
          | forcesNV h => exact absurd (h TF) hokP.1
        have hCan : __smtx_value_canonical_bool (__smtx_type_default_rec TF TU) = true := by
          rcases datatype_kernel_rec TF TU hss with hNV | ⟨_, hCan⟩
          · exact absurd hNV hokP.1
          · exact hCan
        rw [build_inj]
        exact build_inj_canonical v hvCan k cF cU hcc hokP.2 _ (by
          simp [__smtx_value_canonical_bool, hseed, hCan, native_and])
  | k, SmtDatatypeCons.unit, cU, hc, hok, seed, hseed => by
      cases k <;> simp [inj_ok] at hok
  termination_by k _ _ _ _ _ => sizeOf k
  decreasing_by all_goals (try simp_wf); all_goals omega

theorem build_inj_size (v : SmtValue) :
    ∀ (k : Nat) (cF cU : SmtDatatypeCons), DtcSubstStar cF cU → injPosValid k cU →
      ∀ (seed : SmtValue), sizeOf v ≤ sizeOf (build_inj v cF cU k seed)
  | k, SmtDatatypeCons.cons TF cF, SmtDatatypeCons.cons TU cU, hc, hpos, seed => by
      cases k with
      | zero =>
          rw [build_inj]
          have hmono := build_inj_rest_mono cF cU (SmtValue.Apply seed v)
          have happ : sizeOf (SmtValue.Apply seed v) = 1 + sizeOf seed + sizeOf v := by rfl
          omega
      | succ k =>
          rw [build_inj]
          cases hc with
          | @cons _ _ _ _ hfr hcc =>
            have hposTail : injPosValid k cU := by simpa [injPosValid] using hpos
            exact build_inj_size v k cF cU hcc hposTail _
  | Nat.zero, _, SmtDatatypeCons.unit, _, hpos, seed => by simp [injPosValid] at hpos
  | Nat.succ k, _, SmtDatatypeCons.unit, _, hpos, seed => by simp [injPosValid] at hpos
  termination_by k => sizeOf k
  decreasing_by all_goals (try simp_wf); all_goals omega

/-- "Simply infinite" non-datatype types with cleanly size-unbounded canonical values whose
substitution is the identity (so the folded field type equals the raw one). -/
def simplyInf : SmtType → Bool
  | SmtType.Int => true
  | SmtType.USort _ => true
  | _ => false

/-- Substitution is the identity on a `simplyInf` type. -/
theorem subst_id_simplyInf (s : native_String) (d : SmtDatatype) (T : SmtType)
    (hsi : simplyInf T = true) : __smtx_type_substitute s d T = T := by
  cases T with
  | Int => simp [__smtx_type_substitute]
  | USort i => simp [__smtx_type_substitute]
  | _ => simp [simplyInf] at hsi

/-- A `simplyInf` type is not `None`. -/
theorem simplyInf_ne_none (T : SmtType) (hsi : simplyInf T = true) : T ≠ SmtType.None := by
  cases T with
  | Int => simp
  | USort i => simp
  | _ => simp [simplyInf] at hsi

/-- A closed `simplyInf` type has canonical values of arbitrary size. -/
theorem simply_inf_large_witness (T : SmtType) (hsi : simplyInf T = true)
    (hwf : __smtx_type_wf_rec T native_reflist_nil = true) (M : Nat) :
    ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical_bool v = true ∧ M ≤ sizeOf v := by
  cases T with
  | Int =>
      refine ⟨SmtValue.Numeral (Int.ofNat M), by simp [__smtx_typeof_value],
        by simp [__smtx_value_canonical_bool], ?_⟩
      have h1 : sizeOf (Int.ofNat M) = 1 + M := by rfl
      have h2 : sizeOf (SmtValue.Numeral (Int.ofNat M)) = 1 + sizeOf (Int.ofNat M) := by rfl
      omega
  | USort i =>
      exact ⟨SmtValue.UValue i M, by simp [__smtx_typeof_value],
        by simp [__smtx_value_canonical_bool], by simp⟩
  | _ => simp [simplyInf] at hsi

/-- Self-recursive growth: with a located self-recursive constructor whose every field is either
the self-reference or a closed well-formed type, `build_cons` yields a strictly larger value. -/
theorem grow_via_self_rec (s : native_String) (d : SmtDatatype)
    (n : native_Nat) (c : SmtDatatypeCons) (rest : SmtDatatype)
    (hdrop : drop_cons d n = SmtDatatype.sum c rest)
    (hself : has_self_rec s d (__smtx_dtc_substitute s d c))
    (hfields : ∀ TU, FieldMem TU c →
      TU = SmtType.TypeRef s ∨ __smtx_type_wf_rec TU native_reflist_nil = true)
    (w : SmtValue) (hwTy : __smtx_typeof_value w = SmtType.Datatype s d)
    (hwCan : __smtx_value_canonical_bool w = true) :
    ∃ w' : SmtValue, __smtx_typeof_value w' = SmtType.Datatype s d ∧
      __smtx_value_canonical_bool w' = true ∧ sizeOf w < sizeOf w' := by
  have hDtcSS : DtcSubstStar (__smtx_dtc_substitute s d c) c := dtcSubstStar_of_subst s d c
  have hfok : fields_ok s d (__smtx_dtc_substitute s d c) c := fields_ok_of_field_wf s d c hfields
  have hseedTy : __smtx_typeof_value (SmtValue.DtCons s d n) =
      chainType (__smtx_dtc_substitute s d c) (SmtType.Datatype s d) := by
    simp only [__smtx_typeof_value]
    have hdropS : drop_cons (__smtx_dt_substitute s d d) n =
        SmtDatatype.sum (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d rest) := by
      rw [drop_cons_subst, hdrop]; simp [__smtx_dt_substitute]
    exact drop_lemma (SmtType.Datatype s d) (__smtx_dt_substitute s d d) n
      (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d rest) hdropS
  have hseedCan : __smtx_value_canonical_bool (SmtValue.DtCons s d n) = true := by
    simp [__smtx_value_canonical_bool]
  refine ⟨build_cons s d w (__smtx_dtc_substitute s d c) c (SmtValue.DtCons s d n), ?_, ?_, ?_⟩
  · exact build_cons_typeof s d w hwTy (__smtx_dtc_substitute s d c) c hDtcSS hfok
      (SmtValue.DtCons s d n) (SmtType.Datatype s d) hseedTy
  · exact build_cons_canonical s d w hwCan (__smtx_dtc_substitute s d c) c hDtcSS hfok
      (SmtValue.DtCons s d n) hseedCan
  · exact build_cons_size_strict s d w (__smtx_dtc_substitute s d c) c hDtcSS hself
      (SmtValue.DtCons s d n)

/-- Non-self growth: with a located constructor, a position-`k` injection of a large value `v`
(`inj_ok`/`injPosValid`) and all other fields defaultable, `build_inj` yields a larger value. -/
theorem grow_via_inj (s : native_String) (d : SmtDatatype)
    (n : native_Nat) (c : SmtDatatypeCons) (rest : SmtDatatype) (k : Nat) (v : SmtValue)
    (hdrop : drop_cons d n = SmtDatatype.sum c rest)
    (hinj : inj_ok v k (__smtx_dtc_substitute s d c) c)
    (hpos : injPosValid k c)
    (hvCan : __smtx_value_canonical_bool v = true)
    (w : SmtValue) (hwTy : __smtx_typeof_value w = SmtType.Datatype s d)
    (hwCan : __smtx_value_canonical_bool w = true)
    (hvSize : sizeOf w < sizeOf v) :
    ∃ w' : SmtValue, __smtx_typeof_value w' = SmtType.Datatype s d ∧
      __smtx_value_canonical_bool w' = true ∧ sizeOf w < sizeOf w' := by
  have hDtcSS : DtcSubstStar (__smtx_dtc_substitute s d c) c := dtcSubstStar_of_subst s d c
  have hseedTy : __smtx_typeof_value (SmtValue.DtCons s d n) =
      chainType (__smtx_dtc_substitute s d c) (SmtType.Datatype s d) := by
    simp only [__smtx_typeof_value]
    have hdropS : drop_cons (__smtx_dt_substitute s d d) n =
        SmtDatatype.sum (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d rest) := by
      rw [drop_cons_subst, hdrop]; simp [__smtx_dt_substitute]
    exact drop_lemma (SmtType.Datatype s d) (__smtx_dt_substitute s d d) n
      (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d rest) hdropS
  refine ⟨build_inj v (__smtx_dtc_substitute s d c) c k (SmtValue.DtCons s d n), ?_, ?_, ?_⟩
  · exact build_inj_typeof v k (__smtx_dtc_substitute s d c) c hDtcSS hinj
      (SmtValue.DtCons s d n) (SmtType.Datatype s d) hseedTy
  · exact build_inj_canonical v hvCan k (__smtx_dtc_substitute s d c) c hDtcSS hinj
      (SmtValue.DtCons s d n) (by simp [__smtx_value_canonical_bool])
  · have hsize := build_inj_size v k (__smtx_dtc_substitute s d c) c hDtcSS hpos (SmtValue.DtCons s d n)
    omega

/-- Every field closed-well-formed ⇒ the folded constructor is fully defaultable. -/
theorem inj_ok_rest_of_closed (s : native_String) (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons),
      (∀ TU, FieldMem TU c → __smtx_type_wf_rec TU native_reflist_nil = true) →
      inj_ok_rest (__smtx_dtc_substitute s d c) c
  | SmtDatatypeCons.unit, _ => by simp [__smtx_dtc_substitute, inj_ok_rest]
  | SmtDatatypeCons.cons TU c', hfields => by
      simp only [__smtx_dtc_substitute, inj_ok_rest]
      exact ⟨field_default_ne_nv_of_wf (__smtx_type_substitute s d TU) TU
          (fieldRel_of_type_subst s d TU) (hfields TU FieldMem.head),
        inj_ok_rest_of_closed s d c' (fun TU' h => hfields TU' (FieldMem.tail h))⟩

/-- `v`'s type matches the folded `k`-th field. -/
def MatchAt (s : native_String) (d : SmtDatatype) (v : SmtValue) :
    Nat → SmtDatatypeCons → Prop
  | Nat.zero, SmtDatatypeCons.cons TU _ =>
      __smtx_typeof_value v = __smtx_type_substitute s d TU ∧
        __smtx_type_substitute s d TU ≠ SmtType.None
  | Nat.succ k, SmtDatatypeCons.cons _ c => MatchAt s d v k c
  | _, SmtDatatypeCons.unit => False

/-- With every field closed-well-formed and `v` matching the `k`-th field, `inj_ok` holds. -/
theorem inj_ok_of_closed (s : native_String) (d : SmtDatatype) (v : SmtValue) :
    ∀ (k : Nat) (c : SmtDatatypeCons),
      (∀ TU, FieldMem TU c → __smtx_type_wf_rec TU native_reflist_nil = true) →
      MatchAt s d v k c →
      inj_ok v k (__smtx_dtc_substitute s d c) c
  | Nat.zero, SmtDatatypeCons.cons TU c', hfields, hmatch => by
      simp only [__smtx_dtc_substitute, inj_ok]
      refine ⟨?_, inj_ok_rest_of_closed s d c' (fun TU' h => hfields TU' (FieldMem.tail h))⟩
      simpa [MatchAt] using hmatch
  | Nat.succ k, SmtDatatypeCons.cons TU c', hfields, hmatch => by
      simp only [__smtx_dtc_substitute, inj_ok]
      refine ⟨field_default_ne_nv_of_wf (__smtx_type_substitute s d TU) TU
          (fieldRel_of_type_subst s d TU) (hfields TU FieldMem.head), ?_⟩
      exact inj_ok_of_closed s d v k c' (fun TU' h => hfields TU' (FieldMem.tail h))
        (by simpa [MatchAt] using hmatch)
  | Nat.zero, SmtDatatypeCons.unit, _, hmatch => by simp [MatchAt] at hmatch
  | Nat.succ k, SmtDatatypeCons.unit, _, hmatch => by simp [MatchAt] at hmatch

/-- Find the position of the first `simplyInf` field. -/
def findSimplyInfPos : SmtDatatypeCons → Option (Nat × SmtType)
  | SmtDatatypeCons.cons TU c =>
      if simplyInf TU then some (0, TU)
      else (findSimplyInfPos c).map (fun p => (p.1 + 1, p.2))
  | SmtDatatypeCons.unit => none

/-- Value-independent correctness of `findSimplyInfPos`. -/
theorem findpos_props :
    ∀ (c : SmtDatatypeCons) (k : Nat) (Tk : SmtType),
      findSimplyInfPos c = some (k, Tk) →
      injPosValid k c ∧ FieldMem Tk c ∧ simplyInf Tk = true
  | SmtDatatypeCons.unit, k, Tk, hfind => by simp [findSimplyInfPos] at hfind
  | SmtDatatypeCons.cons TU c', k, Tk, hfind => by
      simp only [findSimplyInfPos] at hfind
      by_cases hsi : simplyInf TU = true
      · rw [if_pos hsi] at hfind
        obtain ⟨hk, hT⟩ := Prod.mk.inj (Option.some.inj hfind)
        subst hk; subst hT
        exact ⟨by simp [injPosValid], FieldMem.head, hsi⟩
      · rw [if_neg hsi] at hfind
        rcases hp : findSimplyInfPos c' with _ | ⟨k', Tk'⟩
        · rw [hp] at hfind; simp at hfind
        · rw [hp] at hfind
          simp only [Option.map_some] at hfind
          obtain ⟨hk, hT⟩ := Prod.mk.inj (Option.some.inj hfind)
          subst hk; subst hT
          have hrec := findpos_props c' k' Tk' hp
          exact ⟨by simp only [injPosValid]; exact hrec.1, FieldMem.tail hrec.2.1, hrec.2.2⟩

/-- Given `v` typed as the found field, `MatchAt` holds. -/
theorem findpos_matchat (s : native_String) (d : SmtDatatype) (v : SmtValue) :
    ∀ (c : SmtDatatypeCons) (k : Nat) (Tk : SmtType),
      findSimplyInfPos c = some (k, Tk) → __smtx_typeof_value v = Tk → MatchAt s d v k c
  | SmtDatatypeCons.unit, k, Tk, hfind, _ => by simp [findSimplyInfPos] at hfind
  | SmtDatatypeCons.cons TU c', k, Tk, hfind, hvTy => by
      simp only [findSimplyInfPos] at hfind
      by_cases hsi : simplyInf TU = true
      · rw [if_pos hsi] at hfind
        obtain ⟨hk, hT⟩ := Prod.mk.inj (Option.some.inj hfind)
        subst hk; subst hT
        simp only [MatchAt]
        rw [subst_id_simplyInf s d TU hsi]
        exact ⟨hvTy, simplyInf_ne_none TU hsi⟩
      · rw [if_neg hsi] at hfind
        rcases hp : findSimplyInfPos c' with _ | ⟨k', Tk'⟩
        · rw [hp] at hfind; simp at hfind
        · rw [hp] at hfind
          simp only [Option.map_some] at hfind
          obtain ⟨hk, hT⟩ := Prod.mk.inj (Option.some.inj hfind)
          subst hk; subst hT
          simp only [MatchAt]
          exact findpos_matchat s d v c' k' Tk' hp hvTy

/-- Per-constructor non-self growth: a constructor with all-closed fields and a `simplyInf` field. -/
theorem grow_via_field_search (s : native_String) (d : SmtDatatype)
    (n : native_Nat) (c : SmtDatatypeCons) (rest : SmtDatatype) (k : Nat) (Tk : SmtType)
    (hdrop : drop_cons d n = SmtDatatype.sum c rest)
    (hallclosed : ∀ TU, FieldMem TU c → __smtx_type_wf_rec TU native_reflist_nil = true)
    (hfind : findSimplyInfPos c = some (k, Tk))
    (w : SmtValue) (hwTy : __smtx_typeof_value w = SmtType.Datatype s d)
    (hwCan : __smtx_value_canonical_bool w = true) :
    ∃ w' : SmtValue, __smtx_typeof_value w' = SmtType.Datatype s d ∧
      __smtx_value_canonical_bool w' = true ∧ sizeOf w < sizeOf w' := by
  obtain ⟨hpos, hmem, hsi⟩ := findpos_props c k Tk hfind
  have hwfTk : __smtx_type_wf_rec Tk native_reflist_nil = true := hallclosed Tk hmem
  rcases simply_inf_large_witness Tk hsi hwfTk (sizeOf w + 1) with ⟨v, hvTy, hvCan, hvSize⟩
  exact grow_via_inj s d n c rest k v hdrop
    (inj_ok_of_closed s d v k c hallclosed (findpos_matchat s d v c k Tk hfind hvTy))
    hpos hvCan w hwTy hwCan (by omega)

/-- A constructor has a `TypeRef s` (self-reference) field. -/
def hasTypeRefS (s : native_String) : SmtDatatypeCons → Bool
  | SmtDatatypeCons.cons (SmtType.TypeRef s') c => native_streq s' s || hasTypeRefS s c
  | SmtDatatypeCons.cons _ c => hasTypeRefS s c
  | SmtDatatypeCons.unit => false

/-- A constructor has no nested-`Datatype` field. -/
def noNestedDt : SmtDatatypeCons → Bool
  | SmtDatatypeCons.cons (SmtType.Datatype _ _) _ => false
  | SmtDatatypeCons.cons _ c => noNestedDt c
  | SmtDatatypeCons.unit => true

/-- A self-reference field makes the folded constructor self-recursive. -/
theorem has_self_rec_of_hasTypeRefS (s : native_String) (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons), hasTypeRefS s c = true →
      has_self_rec s d (__smtx_dtc_substitute s d c)
  | SmtDatatypeCons.unit, h => by simp [hasTypeRefS] at h
  | SmtDatatypeCons.cons TU c', h => by
      simp only [__smtx_dtc_substitute, has_self_rec]
      cases TU with
      | TypeRef s' =>
          simp only [hasTypeRefS, Bool.or_eq_true] at h
          rcases h with hs | htail
          · left
            have hss : s' = s := by simpa [native_streq] using hs
            subst hss
            simp [__smtx_type_substitute, native_streq, native_ite, native_Teq]
          · right; exact has_self_rec_of_hasTypeRefS s d c' htail
      | _ =>
          right
          have htail : hasTypeRefS s c' = true := by simpa [hasTypeRefS] using h
          exact has_self_rec_of_hasTypeRefS s d c' htail

/-- `noNestedDt` ⇒ no field is a nested datatype. -/
theorem noNested_no_datatype :
    ∀ (c : SmtDatatypeCons), noNestedDt c = true →
      ∀ TU, FieldMem TU c → ∀ s2 d2, TU ≠ SmtType.Datatype s2 d2
  | SmtDatatypeCons.unit, _, _, hmem, _, _ => by cases hmem
  | SmtDatatypeCons.cons T c', h, TU, hmem, s2, d2 => by
      cases hmem with
      | head =>
          intro heq; subst heq
          simp [noNestedDt] at h
      | tail hmemTail =>
          have htail : noNestedDt c' = true := by
            cases T with
            | Datatype a b => simp [noNestedDt] at h
            | _ => simpa [noNestedDt] using h
          exact noNested_no_datatype c' htail TU hmemTail s2 d2

/-- The `n`-th constructor of a `dtAllWf` datatype is well-formed. -/
theorem dtAllWf_cons_at (refs : RefList) :
    ∀ (n : native_Nat) (d : SmtDatatype),
      dtAllWf d refs = true →
      ∀ (c : SmtDatatypeCons) (rest : SmtDatatype),
        drop_cons d n = SmtDatatype.sum c rest → __smtx_dt_cons_wf_rec c refs = true
  | Nat.zero, d, hwf, c, rest, hdrop => by
      rw [drop_cons_zero] at hdrop; subst hdrop; exact dt_wf_cons_of_wf hwf
  | Nat.succ n, SmtDatatype.null, hwf, c, rest, hdrop => by simp [dtAllWf] at hwf
  | Nat.succ n, SmtDatatype.sum c0 d', hwf, c, rest, hdrop => by
      simp only [drop_cons] at hdrop
      cases d' with
      | null => cases n <;> simp [drop_cons] at hdrop
      | sum cT dT =>
          exact dtAllWf_cons_at refs n (SmtDatatype.sum cT dT)
            (dt_wf_tail_of_nonempty_tail_wf hwf) c rest hdrop

/-- Search the constructors of `d` for a good self-recursive one (a `TypeRef s` field, no nested
datatype field); if found, grow via `grow_via_self_rec`. -/
theorem grow_search (s : native_String) (d : SmtDatatype)
    (w : SmtValue) (hwTy : __smtx_typeof_value w = SmtType.Datatype s d)
    (hwCan : __smtx_value_canonical_bool w = true)
    (hWfAll : ∀ (n : native_Nat) (c : SmtDatatypeCons) (rest : SmtDatatype),
      drop_cons d n = SmtDatatype.sum c rest →
      __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true) :
    ∀ (n : native_Nat) (D : SmtDatatype),
      drop_cons d n = D →
      (∃ w' : SmtValue, __smtx_typeof_value w' = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool w' = true ∧ sizeOf w < sizeOf w') ∨ True
  | _, SmtDatatype.null, _ => Or.inr trivial
  | n, SmtDatatype.sum c rest, hdrop => by
      by_cases hgood : hasTypeRefS s c = true ∧ noNestedDt c = true
      · left
        have hwfc : __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true :=
          hWfAll n c rest hdrop
        exact grow_via_self_rec s d n c rest hdrop
          (has_self_rec_of_hasTypeRefS s d c hgood.1)
          (cons_fields_self_or_closed s c hwfc (noNested_no_datatype c hgood.2)) w hwTy hwCan
      · have hdrop' : drop_cons d (Nat.succ n) = rest := by rw [drop_cons_succ, hdrop]
        exact grow_search s d w hwTy hwCan hWfAll (Nat.succ n) rest hdrop'
  termination_by _ D _ => sizeOf D

/-- No self-reference field ⇒ no field is `TypeRef s`. -/
theorem field_not_typeref_of_no_self (s : native_String) :
    ∀ (c : SmtDatatypeCons), hasTypeRefS s c = false →
      ∀ TU, FieldMem TU c → TU ≠ SmtType.TypeRef s
  | SmtDatatypeCons.unit, _, _, hmem => by cases hmem
  | SmtDatatypeCons.cons T c', h, TU, hmem => by
      cases hmem with
      | head =>
          intro heq; subst heq
          simp [hasTypeRefS, native_streq] at h
      | tail hmemTail =>
          have htail : hasTypeRefS s c' = false := by
            cases T with
            | TypeRef s' => simp only [hasTypeRefS, Bool.or_eq_false_iff] at h; exact h.2
            | _ => simpa [hasTypeRefS] using h
          exact field_not_typeref_of_no_self s c' htail TU hmemTail

/-- A `{s}`-well-formed constructor with no self-ref and no nested-datatype fields has all fields
closed-well-formed. -/
theorem all_closed_of_no_self (s : native_String) (c : SmtDatatypeCons)
    (hwf : __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true)
    (hnodt : noNestedDt c = true) (hnoself : hasTypeRefS s c = false) :
    ∀ TU, FieldMem TU c → __smtx_type_wf_rec TU native_reflist_nil = true := by
  intro TU hmem
  rcases cons_fields_self_or_closed s c hwf (noNested_no_datatype c hnodt) TU hmem with hself | hclosed
  · exact absurd hself (field_not_typeref_of_no_self s c hnoself TU hmem)
  · exact hclosed

/-- Search the constructors of `d` for a non-self constructor (no self-ref, no nested datatype)
with a `simplyInf` field; if found, grow via `grow_via_field_search`. -/
theorem grow_search_b (s : native_String) (d : SmtDatatype)
    (w : SmtValue) (hwTy : __smtx_typeof_value w = SmtType.Datatype s d)
    (hwCan : __smtx_value_canonical_bool w = true)
    (hWfAll : ∀ (n : native_Nat) (c : SmtDatatypeCons) (rest : SmtDatatype),
      drop_cons d n = SmtDatatype.sum c rest →
      __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true) :
    ∀ (n : native_Nat) (D : SmtDatatype),
      drop_cons d n = D →
      (∃ w' : SmtValue, __smtx_typeof_value w' = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool w' = true ∧ sizeOf w < sizeOf w') ∨ True
  | _, SmtDatatype.null, _ => Or.inr trivial
  | n, SmtDatatype.sum c rest, hdrop => by
      by_cases hb : hasTypeRefS s c = false ∧ noNestedDt c = true
      · rcases hfind : findSimplyInfPos c with _ | ⟨k, Tk⟩
        · have hdrop' : drop_cons d (Nat.succ n) = rest := by rw [drop_cons_succ, hdrop]
          exact grow_search_b s d w hwTy hwCan hWfAll (Nat.succ n) rest hdrop'
        · exact Or.inl (grow_via_field_search s d n c rest k Tk hdrop
            (all_closed_of_no_self s c (hWfAll n c rest hdrop) hb.2 hb.1) hfind w hwTy hwCan)
      · have hdrop' : drop_cons d (Nat.succ n) = rest := by rw [drop_cons_succ, hdrop]
        exact grow_search_b s d w hwTy hwCan hWfAll (Nat.succ n) rest hdrop'
  termination_by _ D _ => sizeOf D

/-- The core growth step: from any canonical typed value, build a strictly larger one.
This is where the constructor-selection combinatorics (self-recursive nesting vs.
base-infinite field) lives. -/
private theorem grow_witness
    (s : native_String) (d : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (hWf : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true)
    (hInf : __smtx_is_finite_datatype d = false)
    (w : SmtValue) (hwTy : __smtx_typeof_value w = SmtType.Datatype s d)
    (hwCan : __smtx_value_canonical_bool w = true) :
    ∃ w' : SmtValue, __smtx_typeof_value w' = SmtType.Datatype s d ∧
      __smtx_value_canonical_bool w' = true ∧ sizeOf w < sizeOf w' := by
  have hWfAll : ∀ (n : native_Nat) (c : SmtDatatypeCons) (rest : SmtDatatype),
      drop_cons d n = SmtDatatype.sum c rest →
      __smtx_dt_cons_wf_rec c (native_reflist_insert native_reflist_nil s) = true := by
    intro n c rest hdrop
    exact dtAllWf_cons_at (native_reflist_insert native_reflist_nil s) n d
      (dtAllWf_of_type_wf_rec_datatype s d native_reflist_nil hWf).2 c rest hdrop
  rcases grow_search s d w hwTy hwCan hWfAll native_nat_zero d (drop_cons_zero d) with hfound | _
  · exact hfound
  · rcases grow_search_b s d w hwTy hwCan hWfAll native_nat_zero d (drop_cons_zero d) with hfound | _
    · exact hfound
    · -- Neither a self-recursive constructor with only closed non-self fields, nor a non-self
      -- constructor with a `simplyInf` (Int/USort) field: the datatype is infinite only via a
      -- non-`simplyInf` infinite field (Real/Set/Map/Seq) or genuine mutual recursion (the "pump").
      -- These require additional builders; deferred.
      sorry

private theorem infinite_datatype_large_witness :
    ∀ (N : Nat) (s : native_String) (d : SmtDatatype),
      native_inhabited_type (SmtType.Datatype s d) = true →
      __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true →
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
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true)
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

private theorem inhabited_of_finite_wf {T : SmtType} {refs : RefList}
    (hfin : __smtx_is_finite_type T = true) (hwf : __smtx_type_wf_rec T refs = true) :
    native_inhabited_type T = true := by
  have hne : __smtx_type_default T ≠ SmtValue.NotValue := by
    have := fin_defaultable T T (ShT.refl T) hfin refs hwf
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

mutual

private theorem finite_nonunit_type_nondefault_value :
    ∀ (T : SmtType) (refs : RefList),
      native_inhabited_type T = true → __smtx_type_wf_rec T refs = true →
        __smtx_is_finite_type T = true → __smtx_is_unit_type T = false →
          ∃ e : SmtValue, __smtx_typeof_value e = T ∧ __smtx_value_canonical_bool e = true ∧
            native_veq e (__smtx_type_default T) = false
  | SmtType.None, _refs, _hInh, hRec, _hFin, _hNU => by simp [__smtx_type_wf_rec] at hRec
  | SmtType.Bool, _refs, _hInh, _hRec, _hFin, _hNU => by
      refine ⟨SmtValue.Boolean true, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool, __smtx_type_default,
          __smtx_type_default_rec, native_veq]
  | SmtType.Int, _refs, _hInh, _hRec, hFin, _hNU => by simp [__smtx_is_finite_type] at hFin
  | SmtType.Real, _refs, _hInh, _hRec, hFin, _hNU => by simp [__smtx_is_finite_type] at hFin
  | SmtType.RegLan, _refs, _hInh, hRec, _hFin, _hNU => by simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, _refs, _hInh, _hRec, _hFin, hNU => by
      cases w with
      | zero => simp [__smtx_is_unit_type, native_nateq] at hNU
      | succ w =>
          refine ⟨SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1, ?_, ?_, ?_⟩
          · exact bitvec_succ_one_typeof w
          · exact bitvec_succ_one_canonical w
          · exact bitvec_succ_one_ne_default w
  | SmtType.Char, _refs, _hInh, _hRec, _hFin, _hNU => by
      exact ⟨SmtValue.Char 1, by native_decide, by native_decide, by native_decide⟩
  | SmtType.USort u, _refs, _hInh, _hRec, hFin, _hNU => by simp [__smtx_is_finite_type] at hFin
  | SmtType.TypeRef r, _refs, _hInh, hRec, _hFin, _hNU => by simp [__smtx_type_wf_rec] at hRec
  | SmtType.FunType A B, _refs, _hInh, hRec, _hFin, _hNU => by simp [__smtx_type_wf_rec] at hRec
  | SmtType.DtcAppType A B, _refs, _hInh, hRec, _hFin, _hNU => by simp [__smtx_type_wf_rec] at hRec
  | SmtType.Seq A, _refs, _hInh, _hRec, hFin, _hNU => by simp [__smtx_is_finite_type] at hFin
  | SmtType.Map T U, _refs, _hInh, hRec, hFin, hNU => by
      have hP : native_inhabited_type T = true ∧ __smtx_type_wf_rec T native_reflist_nil = true ∧
          native_inhabited_type U = true ∧ __smtx_type_wf_rec U native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hRec
      have hUNU : __smtx_is_unit_type U = false := by simpa [__smtx_is_unit_type] using hNU
      have hUFin : __smtx_is_finite_type U = true := by
        cases hTF : __smtx_is_finite_type T <;> cases hUF : __smtx_is_finite_type U <;>
          simp [__smtx_is_finite_type, hUNU, hTF, hUF, native_or, native_and] at hFin ⊢
      have hTFin : __smtx_is_finite_type T = true := by
        cases hTF : __smtx_is_finite_type T <;> cases hUF : __smtx_is_finite_type U <;>
          simp [__smtx_is_finite_type, hUNU, hTF, hUF, native_or, native_and] at hFin ⊢
      have hTD := type_default_typed_canonical_of_native_inhabited hP.1
      have hUD := type_default_typed_canonical_of_native_inhabited hP.2.2.1
      rcases finite_nonunit_type_nondefault_value U native_reflist_nil hP.2.2.1 hP.2.2.2 hUFin hUNU with
        ⟨e, heTy, heCan, heNe⟩
      have heNeP : e ≠ __smtx_type_default U := by intro h; subst e; simp [native_veq] at heNe
      refine ⟨SmtValue.Map (SmtMap.cons (__smtx_type_default T) e
          (SmtMap.default T (__smtx_type_default U))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value, hTD.1, heTy, hUD.1, native_ite, native_Teq]
      · simp [__smtx_value_canonical_bool, __smtx_map_canonical, __smtx_map_default_canonical,
          __smtx_map_entries_ordered_after, __smtx_msm_get_default, hTD.2, heCan, hUD.1, hUD.2,
          hTFin, heNeP, native_and, native_ite, native_not, native_veq]
      · have hUNV : __smtx_type_default U ≠ SmtValue.NotValue :=
          type_default_ne_notValue_of_native_inhabited hP.2.2.1 (ne_none_of_native_inhabited hP.2.2.1)
        have hcond : decide (__smtx_type_default_rec U U = SmtValue.NotValue) = false := by
          apply decide_eq_false; simpa [__smtx_type_default] using hUNV
        simp [__smtx_type_default, __smtx_type_default_rec, native_veq, native_ite, hcond]
  | SmtType.Set T, _refs, _hInh, hRec, hFin, _hNU => by
      have hP : native_inhabited_type T = true ∧ __smtx_type_wf_rec T native_reflist_nil = true := by
        simpa [__smtx_type_wf_rec, native_and] using hRec
      have hTFin : __smtx_is_finite_type T = true := by simpa [__smtx_is_finite_type] using hFin
      have hTD := type_default_typed_canonical_of_native_inhabited hP.1
      refine ⟨SmtValue.Set (SmtMap.cons (__smtx_type_default T) (SmtValue.Boolean true)
          (SmtMap.default T (SmtValue.Boolean false))), ?_, ?_, ?_⟩
      · simp [__smtx_typeof_value, __smtx_typeof_map_value, __smtx_map_to_set_type, hTD.1,
          native_ite, native_Teq]
      · have hBoolDef : __smtx_type_default SmtType.Bool = SmtValue.Boolean false := by
          simp [__smtx_type_default, __smtx_type_default_rec]
        simp [__smtx_value_canonical_bool, __smtx_map_canonical, __smtx_map_default_canonical,
          __smtx_map_entries_ordered_after, __smtx_msm_get_default, hTD.2, hBoolDef, hTFin, native_and,
          native_ite, native_not, native_veq, __smtx_typeof_value]
      · simp [__smtx_type_default, __smtx_type_default_rec, native_veq]
  | SmtType.Datatype s d, refs, hInh, hRec, hFin, hNU => by
      exact finite_nonunit_datatype_nondefault_value s d refs hInh hRec hFin hNU
  termination_by T _ _ _ _ _ => sizeOf T
  decreasing_by all_goals (try simp_wf); all_goals (try simp [sizeOf]); all_goals omega

private theorem finite_nonunit_datatype_nondefault_value :
    ∀ (s : native_String) (d : SmtDatatype) (refs : RefList),
      native_inhabited_type (SmtType.Datatype s d) = true →
      __smtx_type_wf_rec (SmtType.Datatype s d) refs = true →
      __smtx_is_finite_type (SmtType.Datatype s d) = true →
      __smtx_is_unit_type (SmtType.Datatype s d) = false →
        ∃ e : SmtValue, __smtx_typeof_value e = SmtType.Datatype s d ∧
          __smtx_value_canonical_bool e = true ∧
          native_veq e (__smtx_type_default (SmtType.Datatype s d)) = false
  | s, SmtDatatype.null, refs, _hInh, hRec, _hFin, _hNU => by
      simp [__smtx_type_wf_rec, __smtx_dt_wf_rec, native_ite] at hRec
  | s, SmtDatatype.sum c SmtDatatype.null, refs, _hInh, hRec, hFin, hNU => by
      have hFinD : __smtx_is_finite_datatype (SmtDatatype.sum c SmtDatatype.null) = true := by
        simpa [__smtx_is_finite_type] using hFin
      have hRoot : native_reflist_contains (native_reflist_insert refs s) s = true := by
        simp [native_reflist_contains, native_reflist_insert]
      have hDtWf : dtAllWf (SmtDatatype.sum c SmtDatatype.null)
          (native_reflist_insert refs s) = true :=
        (dtAllWf_of_type_wf_rec_datatype s (SmtDatatype.sum c SmtDatatype.null) refs hRec).2
      have hcWf : __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true :=
        dt_wf_cons_of_wf hDtWf
      have hcFin : __smtx_is_finite_datatype_cons c = true := finite_dt_cons_of_finite_sum hFinD
      have hcNU : __smtx_is_unit_datatype_cons c = false := by
        simpa [__smtx_is_unit_type, __smtx_is_unit_datatype] using hNU
      have hTy0 : __smtx_typeof_value (SmtValue.DtCons s (SmtDatatype.sum c SmtDatatype.null) 0) =
          chainType c (SmtType.Datatype s (SmtDatatype.sum c SmtDatatype.null)) := by
        apply typeof_dtcons_chain 0 hFinD
        exact drop_cons_zero _
      rcases finite_nonunit_datatype_cons_nondefault_value s (SmtDatatype.sum c SmtDatatype.null)
        (native_reflist_insert refs s) hRoot c hcWf hcFin hcNU
        (SmtValue.DtCons s (SmtDatatype.sum c SmtDatatype.null) 0) hTy0
        (by simp [__smtx_value_canonical_bool]) (by intro h; cases h) with ⟨e, heTy, heCan, heNe⟩
      have hcons0 : __smtx_datatype_cons_default
          (SmtValue.DtCons s (SmtDatatype.sum c SmtDatatype.null) 0) c c ≠ SmtValue.NotValue :=
        cons_defaultable c c (ShC_refl c) hcFin (native_reflist_insert refs s) hcWf _
          (by intro h; cases h)
      have hDefEq : __smtx_type_default (SmtType.Datatype s (SmtDatatype.sum c SmtDatatype.null)) =
          __smtx_datatype_cons_default
            (SmtValue.DtCons s (SmtDatatype.sum c SmtDatatype.null) 0) c c := by
        have hsub : __smtx_dt_substitute s (SmtDatatype.sum c SmtDatatype.null)
            (SmtDatatype.sum c SmtDatatype.null) = SmtDatatype.sum c SmtDatatype.null :=
          subst_D_fin_id s _ _ hFinD
        simp only [__smtx_type_default, __smtx_type_default_rec, hsub]
        exact datatype_default_select s (SmtDatatype.sum c SmtDatatype.null) 0 c c
          SmtDatatype.null SmtDatatype.null hcons0
      exact ⟨e, heTy, heCan, by rw [hDefEq]; exact heNe⟩
  | s, SmtDatatype.sum c (SmtDatatype.sum cTail dTail), refs, _hInh, hRec, hFin, _hNU => by
      let d := SmtDatatype.sum c (SmtDatatype.sum cTail dTail)
      have hFinD : __smtx_is_finite_datatype d = true := by simpa [d, __smtx_is_finite_type] using hFin
      have hRoot : native_reflist_contains (native_reflist_insert refs s) s = true := by
        simp [native_reflist_contains, native_reflist_insert]
      have hDtWf : dtAllWf d (native_reflist_insert refs s) = true :=
        (dtAllWf_of_type_wf_rec_datatype s d refs hRec).2
      have hTailWf : dtAllWf (SmtDatatype.sum cTail dTail) (native_reflist_insert refs s) = true :=
        dt_wf_tail_of_nonempty_tail_wf hDtWf
      have hcTailWf : __smtx_dt_cons_wf_rec cTail (native_reflist_insert refs s) = true :=
        dt_wf_cons_of_wf hTailWf
      have hcTailFin : __smtx_is_finite_datatype_cons cTail = true :=
        finite_dt_cons_of_finite_sum (finite_dt_tail_of_finite_sum hFinD)
      have hcFin : __smtx_is_finite_datatype_cons c = true := finite_dt_cons_of_finite_sum hFinD
      have hcWf : __smtx_dt_cons_wf_rec c (native_reflist_insert refs s) = true := dt_wf_cons_of_wf hDtWf
      -- default = constructor 0's value
      have hcons0 : __smtx_datatype_cons_default (SmtValue.DtCons s d 0) c c ≠ SmtValue.NotValue :=
        cons_defaultable c c (ShC_refl c) hcFin (native_reflist_insert refs s) hcWf _ (by intro h; cases h)
      have hDefEq : __smtx_type_default (SmtType.Datatype s d) =
          __smtx_datatype_cons_default (SmtValue.DtCons s d 0) c c := by
        have hsub : __smtx_dt_substitute s d d = d := subst_D_fin_id s d d hFinD
        simp only [__smtx_type_default, __smtx_type_default_rec, hsub]
        exact datatype_default_select s d 0 c c (SmtDatatype.sum cTail dTail) (SmtDatatype.sum cTail dTail) hcons0
      -- witness = constructor 1's value
      have hTy1 : __smtx_typeof_value (SmtValue.DtCons s d 1) = chainType cTail (SmtType.Datatype s d) := by
        apply typeof_dtcons_chain 1 hFinD
        show drop_cons d 1 = SmtDatatype.sum cTail dTail
        simp [d, drop_cons]
      have he_ne : __smtx_datatype_cons_default (SmtValue.DtCons s d 1) cTail cTail ≠ SmtValue.NotValue :=
        cons_defaultable cTail cTail (ShC_refl cTail) hcTailFin (native_reflist_insert refs s) hcTailWf _
          (by intro h; cases h)
      have hker := datatype_cons_default_kernel cTail cTail (dtcSubstStar_refl cTail)
        (SmtValue.DtCons s d 1) (SmtType.Datatype s d) hTy1 (by simp [__smtx_value_canonical_bool])
      rcases hker with hNV | ⟨heTy, heCan⟩
      · exact absurd hNV he_ne
      refine ⟨__smtx_datatype_cons_default (SmtValue.DtCons s d 1) cTail cTail, heTy, heCan, ?_⟩
      rw [hDefEq]
      apply native_veq_eq_false_of_ne
      intro hEq
      have hHeadE : __vsm_apply_head (__smtx_datatype_cons_default (SmtValue.DtCons s d 1) cTail cTail) =
          SmtValue.DtCons s d 1 := by rw [cons_default_head cTail cTail _ he_ne]; simp [__vsm_apply_head]
      have hHead0 : __vsm_apply_head (__smtx_datatype_cons_default (SmtValue.DtCons s d 0) c c) =
          SmtValue.DtCons s d 0 := by rw [cons_default_head c c _ hcons0]; simp [__vsm_apply_head]
      have := congrArg __vsm_apply_head hEq
      rw [hHeadE, hHead0] at this
      injection this with h1 h2 h3
      simp at h3
  termination_by s d _ _ _ _ _ => sizeOf d
  decreasing_by all_goals (try simp_wf); all_goals (try simp [sizeOf]); all_goals omega

private theorem finite_nonunit_datatype_cons_nondefault_value
    (s : native_String) (d : SmtDatatype) (refs : RefList)
    (hRoot : native_reflist_contains refs s = true) :
    ∀ (c : SmtDatatypeCons),
      __smtx_dt_cons_wf_rec c refs = true → __smtx_is_finite_datatype_cons c = true →
      __smtx_is_unit_datatype_cons c = false →
      ∀ (v : SmtValue), __smtx_typeof_value v = chainType c (SmtType.Datatype s d) →
        __smtx_value_canonical_bool v = true → v ≠ SmtValue.NotValue →
          ∃ e : SmtValue, __smtx_typeof_value e = SmtType.Datatype s d ∧
            __smtx_value_canonical_bool e = true ∧
            native_veq e (__smtx_datatype_cons_default v c c) = false
  | SmtDatatypeCons.unit, _hWf, _hFin, hNU, _v, _hvTy, _hvCan, _hvNe => by
      simp [__smtx_is_unit_datatype_cons] at hNU
  | SmtDatatypeCons.cons TU c', hWf, hFin, hNU, v, hvTy, hvCan, hvNe => by
      have hp : __smtx_is_finite_type TU = true ∧ __smtx_is_finite_datatype_cons c' = true := by
        simpa [__smtx_is_finite_datatype_cons, native_and] using hFin
      have hwfTU : __smtx_type_wf_rec TU refs = true := by
        by_cases h : __smtx_type_wf_rec TU refs = true
        · exact h
        · exfalso; cases TU <;>
            simp_all [__smtx_dt_cons_wf_rec, native_ite, __smtx_is_finite_type, __smtx_type_wf_rec]
      have hwfTail : __smtx_dt_cons_wf_rec c' refs = true := by
        by_cases h : __smtx_dt_cons_wf_rec c' refs = true
        · exact h
        · exfalso; cases TU <;> simp_all [__smtx_dt_cons_wf_rec, native_ite, __smtx_is_finite_type]
      have hInhTU : native_inhabited_type TU = true := inhabited_of_finite_wf hp.1 hwfTU
      have hTUne : TU ≠ SmtType.None := by intro h; subst TU; simp [__smtx_is_finite_type] at hp
      have hTUD := type_default_typed_canonical_of_native_inhabited hInhTU
      have hv0eq : __smtx_type_default_rec TU TU = __smtx_type_default TU := rfl
      -- v0 = field default; Apply v v0 is the default seed for the tail
      have hSeed0Ty : __smtx_typeof_value (SmtValue.Apply v (__smtx_type_default TU)) =
          chainType c' (SmtType.Datatype s d) :=
        apply_seed_typeof hvTy hTUD.1 hTUne
      have hSeed0Can : __smtx_value_canonical_bool (SmtValue.Apply v (__smtx_type_default TU)) = true := by
        simp [__smtx_value_canonical_bool, hvCan, hTUD.2, native_and]
      have hUnfold : __smtx_datatype_cons_default v (SmtDatatypeCons.cons TU c')
          (SmtDatatypeCons.cons TU c') =
          __smtx_datatype_cons_default (SmtValue.Apply v (__smtx_type_default TU)) c' c' := by
        have hv0ne : native_veq (__smtx_type_default_rec TU TU) SmtValue.NotValue = false := by
          apply native_veq_eq_false_of_ne
          have := fin_defaultable TU TU (ShT.refl TU) hp.1 refs hwfTU
          exact this
        rw [__smtx_datatype_cons_default, native_ite, if_neg (by simp [hv0ne]), hv0eq]
      by_cases hUnitTU : __smtx_is_unit_type TU = false
      · -- head field is non-unit: inject a non-default value there
        rcases finite_nonunit_type_nondefault_value TU refs hInhTU hwfTU hp.1 hUnitTU with
          ⟨arg, hargTy, hargCan, hargNe⟩
        have hSeedTy : __smtx_typeof_value (SmtValue.Apply v arg) = chainType c' (SmtType.Datatype s d) :=
          apply_seed_typeof hvTy hargTy hTUne
        have hSeedCan : __smtx_value_canonical_bool (SmtValue.Apply v arg) = true := by
          simp [__smtx_value_canonical_bool, hvCan, hargCan, native_and]
        have hSeedNe : SmtValue.Apply v arg ≠ SmtValue.NotValue := by intro h; cases h
        have heNe : __smtx_datatype_cons_default (SmtValue.Apply v arg) c' c' ≠ SmtValue.NotValue :=
          cons_defaultable c' c' (ShC_refl c') hp.2 refs hwfTail _ hSeedNe
        have hker := datatype_cons_default_kernel c' c' (dtcSubstStar_refl c')
          (SmtValue.Apply v arg) (SmtType.Datatype s d) hSeedTy hSeedCan
        rcases hker with hNV | ⟨heTy, heCan⟩
        · exact absurd hNV heNe
        refine ⟨__smtx_datatype_cons_default (SmtValue.Apply v arg) c' c', heTy, heCan, ?_⟩
        rw [hUnfold]
        apply native_veq_eq_false_of_ne
        intro hEq
        have hseedEq : SmtValue.Apply v arg = SmtValue.Apply v (__smtx_type_default TU) :=
          cons_default_seed_inj c' c' _ _ heNe hEq
        have : arg = __smtx_type_default TU := (SmtValue.Apply.inj hseedEq).2
        rw [this] at hargNe
        simp [native_veq] at hargNe
      · -- head field is unit: recurse into the (non-unit) tail
        have hUnitTUt : __smtx_is_unit_type TU = true := by
          cases h : __smtx_is_unit_type TU <;> simp [h] at hUnitTU ⊢
        have hTailNU : __smtx_is_unit_datatype_cons c' = false := by
          cases hc : __smtx_is_unit_datatype_cons c' <;>
            simp [__smtx_is_unit_datatype_cons, hUnitTUt, hc, native_and] at hNU ⊢
        have hSeedNe : SmtValue.Apply v (__smtx_type_default TU) ≠ SmtValue.NotValue := by intro h; cases h
        rcases finite_nonunit_datatype_cons_nondefault_value s d refs hRoot c' hwfTail hp.2 hTailNU
          (SmtValue.Apply v (__smtx_type_default TU)) hSeed0Ty hSeed0Can hSeedNe with ⟨e, heTy, heCan, heNe⟩
        exact ⟨e, heTy, heCan, by rw [hUnfold]; exact heNe⟩
  termination_by c _ _ _ _ _ _ _ => sizeOf c
  decreasing_by all_goals (try simp_wf); all_goals (try simp [sizeOf]); all_goals omega

end

/-- RESIDUAL (sorry): a finite, non-unit, well-formed datatype has a typed
canonical inhabitant distinct from its default.  Formerly proved by the
value-substitution "inhabit" construction. -/
theorem cpc_finite_nonunit_datatype_nondefault_value_assumption
    (s : native_String) (d : SmtDatatype)
    (_hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (_hRec : __smtx_type_wf_rec (SmtType.Datatype s d) native_reflist_nil = true)
    (_hFinite : __smtx_is_finite_type (SmtType.Datatype s d) = true)
    (_hNonUnit : __smtx_is_unit_type (SmtType.Datatype s d) = false) :
    ∃ e : SmtValue,
      __smtx_typeof_value e = SmtType.Datatype s d ∧
        __smtx_value_canonical_bool e = true ∧
          native_veq e (__smtx_type_default (SmtType.Datatype s d)) = false := by
  exact finite_nonunit_datatype_nondefault_value s d native_reflist_nil _hInh _hRec _hFinite _hNonUnit


-- === non-default typed canonical value (non-datatype cases direct) ===

theorem cpc_nonunit_typed_canonical_nondefault_value
    (A : SmtType)
    (_hInh : native_inhabited_type A = true)
    (_hRec : __smtx_type_wf_rec A native_reflist_nil = true)
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
            __smtx_type_wf_rec T native_reflist_nil = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U native_reflist_nil = true := by
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
            __smtx_type_wf_rec T native_reflist_nil = true := by
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
            __smtx_type_wf_rec T native_reflist_nil = true := by
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
    (_hRec : __smtx_type_wf_rec A native_reflist_nil = true)
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
              __smtx_type_wf_rec T native_reflist_nil = true ∧
                native_inhabited_type U = true ∧
                  __smtx_type_wf_rec U native_reflist_nil = true := by
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
                  __smtx_type_wf_rec T native_reflist_nil = true ∧
                    native_inhabited_type U = true ∧
                      __smtx_type_wf_rec U native_reflist_nil = true := by
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
            __smtx_type_wf_rec T native_reflist_nil = true := by
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
            __smtx_type_wf_rec T native_reflist_nil = true := by
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
    (hARec : __smtx_type_wf_rec A native_reflist_nil = true)
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
