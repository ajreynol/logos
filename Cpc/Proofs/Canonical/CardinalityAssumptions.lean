import Cpc.Proofs.TypePreservation.Predicates
import Cpc.Proofs.Canonical.TypeDefaultBasic
import Cpc.Proofs.Canonical.FiniteDefaultable
import Cpc.Proofs.Canonical.WfDiag

/-!
Canonical/cardinality and freshness witnesses used by datatype cardinality
reasoning and array extensionality.

This module is the intended boundary for the residual datatype-cardinality
assumptions.  After the `__smtx_type_default` / `native_inhabited_type`
refactor (value-level substitution removed; default canonicality now supplied
unconditionally by `Cpc.Proofs.Canonical.TypeDefaultBasic`), non-datatype
freshness/non-default witnesses and finite datatype non-default witnesses are
discharged directly.  The remaining hard datatype cardinality fact is the
infinite datatype pump.
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

private theorem singleton_set_large_of_witness
    (A : SmtType) (w x : SmtValue)
    (hxTy : __smtx_typeof_value x = A)
    (hxCan : __smtx_value_canonical_bool x = true)
    (hxSize : sizeOf w < sizeOf x) :
    ∃ y : SmtValue,
      __smtx_typeof_value y = SmtType.Set A ∧
        __smtx_value_canonical_bool y = true ∧ sizeOf w < sizeOf y := by
  refine
    ⟨SmtValue.Set
      (SmtMap.cons x (SmtValue.Boolean true)
        (SmtMap.default A (SmtValue.Boolean false))), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value, __smtx_typeof_map_value,
      __smtx_map_to_set_type, hxTy, native_Teq, native_ite]
  · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
      __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
      __smtx_msm_get_default, hxCan, __smtx_typeof_value,
      __smtx_type_default, __smtx_type_default_rec, native_veq,
      native_and, native_not, native_ite]
  · have hxSet :
        sizeOf x <
          sizeOf
            (SmtValue.Set
              (SmtMap.cons x (SmtValue.Boolean true)
                (SmtMap.default A (SmtValue.Boolean false)))) := by
      rw [show
          sizeOf
              (SmtValue.Set
                (SmtMap.cons x (SmtValue.Boolean true)
                  (SmtMap.default A (SmtValue.Boolean false)))) =
            1 + (1 + sizeOf x + sizeOf (SmtValue.Boolean true) +
              sizeOf (SmtMap.default A (SmtValue.Boolean false))) by rfl]
      omega
    omega

private theorem singleton_map_large_of_value_witness
    (A B : SmtType) (w x : SmtValue)
    (hAInh : native_inhabited_type A = true)
    (hBInh : native_inhabited_type B = true)
    (hxTy : __smtx_typeof_value x = B)
    (hxCan : __smtx_value_canonical_bool x = true)
    (hxSize : sizeOf w < sizeOf x)
    (hxDefSize : sizeOf (__smtx_type_default B) < sizeOf x) :
    ∃ y : SmtValue,
      __smtx_typeof_value y = SmtType.Map A B ∧
        __smtx_value_canonical_bool y = true ∧ sizeOf w < sizeOf y := by
  have hADefault :=
    type_default_typed_canonical_of_native_inhabited hAInh
  have hBDefault :=
    type_default_typed_canonical_of_native_inhabited hBInh
  have hxNeDefaultProp : x ≠ __smtx_type_default B := by
    intro hEq
    subst x
    exact (Nat.lt_irrefl _) hxDefSize
  refine
    ⟨SmtValue.Map
      (SmtMap.cons (__smtx_type_default A) x
        (SmtMap.default A (__smtx_type_default B))), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value, __smtx_typeof_map_value,
      hADefault.1, hxTy, hBDefault.1, native_ite, native_Teq]
  · cases hAFin : __smtx_is_finite_type A
    · have hDefaultCan :
          __smtx_map_default_canonical A (__smtx_type_default B) = true := by
        simp [__smtx_map_default_canonical, hAFin, native_ite]
      simp [__smtx_value_canonical_bool, __smtx_map_canonical,
        __smtx_map_entries_ordered_after, __smtx_msm_get_default,
        hADefault.2, hBDefault.2, hDefaultCan, hxCan, hxNeDefaultProp,
        native_and, native_not, native_veq]
    · have hDefaultCan :
          __smtx_map_default_canonical A (__smtx_type_default B) = true := by
        simp [__smtx_map_default_canonical, hAFin, hBDefault.1,
          native_ite, native_veq]
      simp [__smtx_value_canonical_bool, __smtx_map_canonical,
        __smtx_map_entries_ordered_after, __smtx_msm_get_default,
        hADefault.2, hBDefault.2, hDefaultCan, hxCan, hxNeDefaultProp,
        native_and, native_not, native_veq]
  · have hxMap :
        sizeOf x <
          sizeOf
            (SmtValue.Map
              (SmtMap.cons (__smtx_type_default A) x
                (SmtMap.default A (__smtx_type_default B)))) := by
      rw [show
          sizeOf
              (SmtValue.Map
                (SmtMap.cons (__smtx_type_default A) x
                  (SmtMap.default A (__smtx_type_default B)))) =
            1 + (1 + sizeOf (__smtx_type_default A) + sizeOf x +
              sizeOf (SmtMap.default A (__smtx_type_default B))) by rfl]
      omega
    omega

private theorem singleton_bool_map_large_of_key_witness
    (A : SmtType) (w k : SmtValue)
    (hkTy : __smtx_typeof_value k = A)
    (hkCan : __smtx_value_canonical_bool k = true)
    (hkSize : sizeOf w < sizeOf k) :
    ∃ y : SmtValue,
      __smtx_typeof_value y = SmtType.Map A SmtType.Bool ∧
        __smtx_value_canonical_bool y = true ∧ sizeOf w < sizeOf y := by
  refine
    ⟨SmtValue.Map
      (SmtMap.cons k (SmtValue.Boolean true)
        (SmtMap.default A (SmtValue.Boolean false))), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value, __smtx_typeof_map_value,
      hkTy, native_ite, native_Teq]
  · cases hAFin : __smtx_is_finite_type A
    · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
        __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
        __smtx_msm_get_default, hkCan, hAFin, __smtx_type_default,
        __smtx_type_default_rec, __smtx_typeof_value, native_and, native_ite, native_not,
        native_veq]
    · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
        __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
        __smtx_msm_get_default, hkCan, hAFin, __smtx_type_default,
        __smtx_type_default_rec, __smtx_typeof_value, native_and, native_ite, native_not,
        native_veq]
  · have hkMap :
        sizeOf k <
          sizeOf
            (SmtValue.Map
              (SmtMap.cons k (SmtValue.Boolean true)
                (SmtMap.default A (SmtValue.Boolean false)))) := by
      rw [show
          sizeOf
              (SmtValue.Map
                (SmtMap.cons k (SmtValue.Boolean true)
                  (SmtMap.default A (SmtValue.Boolean false)))) =
            1 + (1 + sizeOf k + sizeOf (SmtValue.Boolean true) +
              sizeOf (SmtMap.default A (SmtValue.Boolean false))) by rfl]
      omega
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
(`TypeDefaultBasic`).  These replace the deleted value-substitution scaffolding:
typedness + canonicality of a generated constructor value
(`datatype_cons_default_kernel`), selection of a constructor by the datatype
default (`datatype_default_select`), and stability of the constructor head
(`cons_default_head`). -/

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

private theorem dt_wf_tail_of_sum_wf_of_tail_ne_null
    {cF cU : SmtDatatypeCons} {dF dU : SmtDatatype}
    (hTail : dU ≠ SmtDatatype.null)
    (h : __smtx_dt_wf_rec (SmtDatatype.sum cF dF)
        (SmtDatatype.sum cU dU) = true) :
    __smtx_dt_wf_rec dF dU = true := by
  cases dU with
  | null =>
      exact False.elim (hTail rfl)
  | sum cTail dTail =>
      cases hC : __smtx_dt_cons_wf_rec cF cU <;>
        simp only [__smtx_dt_wf_rec, native_ite, hC] at h
      · exact absurd h (by simp)
      · exact h

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

private theorem finite_datatype_sum_false_cases {c : SmtDatatypeCons} {d : SmtDatatype}
    (hFin : __smtx_is_finite_datatype (SmtDatatype.sum c d) = false) :
    __smtx_is_finite_datatype_cons c = false ∨
      __smtx_is_finite_datatype d = false := by
  cases hc : __smtx_is_finite_datatype_cons c <;>
    cases hd : __smtx_is_finite_datatype d <;>
      simp [__smtx_is_finite_datatype, native_and, hc, hd] at hFin ⊢

private theorem finite_datatype_cons_cons_false_cases {T : SmtType} {c : SmtDatatypeCons}
    (hFin : __smtx_is_finite_datatype_cons (SmtDatatypeCons.cons T c) = false) :
    __smtx_is_finite_type T = false ∨
      __smtx_is_finite_datatype_cons c = false := by
  cases hT : __smtx_is_finite_type T <;>
    cases hc : __smtx_is_finite_datatype_cons c <;>
      simp [__smtx_is_finite_datatype_cons, native_and, hT, hc] at hFin ⊢

private theorem dt_cons_wf_diag_parts {T : SmtType} {c : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T c)
        (SmtDatatypeCons.cons T c) = true) :
    native_inhabited_type T = true ∧ __smtx_type_wf_rec T T = true ∧
      __smtx_dt_cons_wf_rec c c = true := by
  cases T <;> simp [__smtx_dt_cons_wf_rec, native_and, native_ite] at h ⊢
  all_goals exact ⟨h.1.1, h.1.2, h.2⟩

private theorem dt_cons_wf_same_head_parts {T : SmtType} {cF cU : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons T cF)
        (SmtDatatypeCons.cons T cU) = true) :
    native_inhabited_type T = true ∧ __smtx_type_wf_rec T T = true ∧
      __smtx_dt_cons_wf_rec cF cU = true := by
  cases T <;> simp [__smtx_dt_cons_wf_rec, native_and, native_ite] at h ⊢
  all_goals exact ⟨h.1.1, h.1.2, h.2⟩

private theorem dt_cons_wf_rec_tail_of_true {TF TU : SmtType} {cF cU : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons TF cF)
        (SmtDatatypeCons.cons TU cU) = true) :
    __smtx_dt_cons_wf_rec cF cU = true := by
  by_cases hc : __smtx_dt_cons_wf_rec cF cU = true
  · exact hc
  · exfalso
    cases TF <;> cases TU <;>
      simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]

private theorem dt_cons_wf_subst_head_parts_of_nonself
    (s : native_String) (d : SmtDatatype) {T : SmtType} {c : SmtDatatypeCons}
    (h : __smtx_dt_cons_wf_rec
        (__smtx_dtc_substitute s d (SmtDatatypeCons.cons T c))
        (SmtDatatypeCons.cons T c) = true)
    (hNonself :
      native_Teq (__smtx_type_substitute s d T) (SmtType.Datatype s d) = false) :
    native_inhabited_type (__smtx_type_substitute s d T) = true ∧
      __smtx_type_wf_rec (__smtx_type_substitute s d T) T = true ∧
        __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s d c) c = true := by
  cases T <;>
    simp [__smtx_dtc_substitute, __smtx_type_substitute,
      __smtx_dt_cons_wf_rec, native_and, native_ite] at h hNonself ⊢
  case TypeRef r =>
    by_cases hs : native_streq s r = true
    · simp [native_ite, hs, native_Teq] at hNonself
    · simp [native_ite, hs, __smtx_dt_cons_wf_rec, native_inhabited_type,
        __smtx_type_wf_rec, __smtx_type_default, __smtx_type_default_rec,
        __smtx_typeof_value, native_Teq, native_not, native_and] at h
  all_goals
    exact ⟨h.1.1, h.1.2, h.2⟩

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

private theorem apply_seed_typeof_chain
    {seed arg : SmtValue} {TF : SmtType} {cF : SmtDatatypeCons} {base : SmtType}
    (hSeed : __smtx_typeof_value seed =
      chainType (SmtDatatypeCons.cons TF cF) base)
    (hArg : __smtx_typeof_value arg = TF)
    (hTFne : TF ≠ SmtType.None) :
    __smtx_typeof_value (SmtValue.Apply seed arg) = chainType cF base := by
  have hchain :
      chainType (SmtDatatypeCons.cons TF cF) base =
        SmtType.DtcAppType TF (chainType cF base) := rfl
  rw [hchain] at hSeed
  have h1 : native_Teq TF TF = true := by simp [native_Teq]
  have h2 : native_Teq TF SmtType.None = false := by
    simp [native_Teq, hTFne]
  simp only [__smtx_typeof_value, hSeed, hArg, __smtx_typeof_apply_value,
    __smtx_typeof_guard]
  simp [native_ite, h1, h2]

/-!
Diagnostic facts for the generalized infinite-field proof.  The positive lemmas
show what substitution data can be recovered at the top level; the counterexamples
show that arbitrary `DtSubstStar`/`FieldRel` is too weak for the datatype pump,
because raw `TypeRef` fields can make the raw side infinite without making the
folded value type infinite.
-/

private theorem type_substitute_nonself_substStar
    (s : native_String) (d : SmtDatatype) (T : SmtType)
    (hNonself :
      native_Teq (__smtx_type_substitute s d T) (SmtType.Datatype s d) = false) :
    SubstStar (__smtx_type_substitute s d T) T := by
  cases T with
  | None =>
      simpa [__smtx_type_substitute] using SubstStar.refl SmtType.None
  | Bool =>
      simpa [__smtx_type_substitute] using SubstStar.refl SmtType.Bool
  | Int =>
      simpa [__smtx_type_substitute] using SubstStar.refl SmtType.Int
  | Real =>
      simpa [__smtx_type_substitute] using SubstStar.refl SmtType.Real
  | RegLan =>
      simpa [__smtx_type_substitute] using SubstStar.refl SmtType.RegLan
  | BitVec w =>
      simpa [__smtx_type_substitute] using SubstStar.refl (SmtType.BitVec w)
  | Map A B =>
      simpa [__smtx_type_substitute] using SubstStar.refl (SmtType.Map A B)
  | Set A =>
      simpa [__smtx_type_substitute] using SubstStar.refl (SmtType.Set A)
  | Seq A =>
      simpa [__smtx_type_substitute] using SubstStar.refl (SmtType.Seq A)
  | Char =>
      simpa [__smtx_type_substitute] using SubstStar.refl SmtType.Char
  | Datatype s2 d2 =>
      simp only [__smtx_type_substitute]
      by_cases hEq : native_streq s s2 = true
      · rw [native_ite, if_pos hEq]
        exact SubstStar.dt (dtSubstStar_refl d2)
      · rw [native_ite, if_neg hEq]
        exact SubstStar.dt (dtSubstStar_of_subst s (__smtx_dt_lift s2 d2 d) d2)
  | TypeRef r =>
      by_cases hEq : native_streq s r = true
      · simp [__smtx_type_substitute, native_ite, hEq, native_Teq] at hNonself
      · have hEqFalse : native_streq s r = false := by
          cases h : native_streq s r <;> simp [h] at hEq ⊢
        simpa [__smtx_type_substitute, native_ite, hEqFalse] using
          SubstStar.refl (SmtType.TypeRef r)
  | USort u =>
      simpa [__smtx_type_substitute] using SubstStar.refl (SmtType.USort u)
  | FunType A B =>
      simpa [__smtx_type_substitute] using SubstStar.refl (SmtType.FunType A B)
  | DtcAppType A B =>
      simpa [__smtx_type_substitute] using SubstStar.refl (SmtType.DtcAppType A B)

private theorem substStar_datatype_full_rel
    {sF sU : native_String} {dF dU : SmtDatatype}
    (hRel : SubstStar (SmtType.Datatype sF dF) (SmtType.Datatype sU dU)) :
    DtSubstStar (__smtx_dt_substitute sF dF dF) dU := by
  cases hRel with
  | refl T =>
      exact dtSubstStar_subst sF dF (dtSubstStar_refl dF)
  | dt hD =>
      exact dtSubstStar_subst sF dF hD

private theorem fieldRel_typeref_forces_any
    (TF : SmtType) (r : native_String) :
    FieldRel TF (SmtType.TypeRef r) :=
  FieldRel.forcesNV (fun V => rec_typeref_nv r V)

private theorem dt_cons_wf_rec_typeref_head_skips
    {sF r : native_String} {dF : SmtDatatype} {cF cU : SmtDatatypeCons}
    (hTail : __smtx_dt_cons_wf_rec cF cU = true) :
    __smtx_dt_cons_wf_rec
        (SmtDatatypeCons.cons (SmtType.Datatype sF dF) cF)
        (SmtDatatypeCons.cons (SmtType.TypeRef r) cU) = true := by
  simpa [__smtx_dt_cons_wf_rec] using hTail

private theorem dtcSubstStar_wf_typeref_head_not_inhabited
    (s r : native_String) :
    DtcSubstStar
        (SmtDatatypeCons.cons (SmtType.Datatype s SmtDatatype.null)
          SmtDatatypeCons.unit)
        (SmtDatatypeCons.cons (SmtType.TypeRef r) SmtDatatypeCons.unit) ∧
      __smtx_dt_cons_wf_rec
          (SmtDatatypeCons.cons (SmtType.Datatype s SmtDatatype.null)
            SmtDatatypeCons.unit)
          (SmtDatatypeCons.cons (SmtType.TypeRef r) SmtDatatypeCons.unit) = true ∧
      native_inhabited_type (SmtType.Datatype s SmtDatatype.null) = false := by
  refine ⟨?_, ?_, ?_⟩
  · exact DtcSubstStar.cons
      (fieldRel_typeref_forces_any (SmtType.Datatype s SmtDatatype.null) r)
      DtcSubstStar.unit
  · exact dt_cons_wf_rec_typeref_head_skips
      (cF := SmtDatatypeCons.unit) (cU := SmtDatatypeCons.unit) (by rfl)
  · simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec,
      __smtx_datatype_default, __smtx_typeof_value, native_Teq, native_not,
      native_and]

private theorem dtSubstStar_wf_raw_infinite_folded_finite_counterexample
    (s r : native_String) :
    let dF :=
      SmtDatatype.sum SmtDatatypeCons.unit
        (SmtDatatype.sum
          (SmtDatatypeCons.cons (SmtType.Datatype s SmtDatatype.null)
            SmtDatatypeCons.unit)
          SmtDatatype.null)
    let dU :=
      SmtDatatype.sum SmtDatatypeCons.unit
        (SmtDatatype.sum
          (SmtDatatypeCons.cons (SmtType.TypeRef r) SmtDatatypeCons.unit)
          SmtDatatype.null)
    DtSubstStar (__smtx_dt_substitute s dF dF) dU ∧
      native_inhabited_type (SmtType.Datatype s dF) = true ∧
      __smtx_type_wf_rec (SmtType.Datatype s dF)
        (SmtType.Datatype s dU) = true ∧
      __smtx_is_finite_type (SmtType.Datatype s dU) = false ∧
      __smtx_is_finite_type (SmtType.Datatype s dF) = true := by
  intro dF dU
  have hSub : __smtx_dt_substitute s dF dF = dF := by
    simp [dF, __smtx_dt_substitute, __smtx_dtc_substitute,
      __smtx_type_substitute, native_streq, native_ite]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hSub]
    exact DtSubstStar.sum DtcSubstStar.unit
      (DtSubstStar.sum
        (DtcSubstStar.cons
          (fieldRel_typeref_forces_any (SmtType.Datatype s SmtDatatype.null) r)
          DtcSubstStar.unit)
        DtSubstStar.null)
  · simp [dF, hSub, native_inhabited_type, __smtx_type_default, __smtx_type_default_rec,
      __smtx_datatype_default, __smtx_datatype_cons_default,
      __smtx_typeof_value, __smtx_typeof_dt_cons_value_rec, chainType,
      native_Teq, native_not, native_and, native_veq, native_ite]
  · simp [dF, dU, hSub, __smtx_type_wf_rec, __smtx_dt_wf_rec,
      __smtx_dt_cons_wf_rec, native_ite]
  · simp [dU, __smtx_is_finite_type, __smtx_is_finite_datatype,
      __smtx_is_finite_datatype_cons, native_and]
  · simp [dF, __smtx_is_finite_type, __smtx_is_finite_datatype,
      __smtx_is_finite_datatype_cons, native_and]

private theorem actual_substitution_nonself_not_diagonal_wf_counterexample
    (s t : native_String) (hst : native_streq s t = false) :
    let dOuter := SmtDatatype.null
    let dRaw :=
      SmtDatatype.sum SmtDatatypeCons.unit
        (SmtDatatype.sum
          (SmtDatatypeCons.cons (SmtType.TypeRef s) SmtDatatypeCons.unit)
          SmtDatatype.null)
    let TF := __smtx_type_substitute s dOuter (SmtType.Datatype t dRaw)
    native_Teq TF (SmtType.Datatype s dOuter) = false ∧
      __smtx_is_finite_type (SmtType.Datatype t dRaw) = false ∧
      native_inhabited_type TF = true ∧
      __smtx_type_wf_rec TF (SmtType.Datatype t dRaw) = true ∧
      __smtx_type_wf_rec TF TF = false := by
  intro dOuter dRaw TF
  have hne : s ≠ t := by
    simpa [native_streq] using hst
  have hne' : t ≠ s := by
    intro h
    exact hne h.symm
  have hts : native_streq t s = false := by
    simp [native_streq, eq_comm, hne]
  simp [TF, dOuter, dRaw, __smtx_type_substitute, hst, hts,
    __smtx_dt_substitute, __smtx_dtc_substitute, __smtx_type_lift,
    __smtx_dtc_lift, __smtx_dt_lift, native_ite, native_Teq,
    native_streq, hne, hne',
    __smtx_is_finite_type, __smtx_is_finite_datatype,
    __smtx_is_finite_datatype_cons, native_and, native_inhabited_type,
    __smtx_type_default, __smtx_type_default_rec, __smtx_datatype_default,
    __smtx_datatype_cons_default, __smtx_typeof_value,
    __smtx_typeof_dt_cons_value_rec, __smtx_type_wf_rec, __smtx_dt_wf_rec,
    __smtx_dt_cons_wf_rec, native_not, native_veq]

mutual

private theorem type_lift_infinite_of_infinite
    (s : native_String) (d : SmtDatatype) :
    ∀ (T : SmtType),
      __smtx_is_finite_type T = false →
        __smtx_is_finite_type (__smtx_type_lift s d T) = false
  | SmtType.Bool, h => by simp [__smtx_is_finite_type] at h
  | SmtType.BitVec w, h => by simp [__smtx_is_finite_type] at h
  | SmtType.Char, h => by simp [__smtx_is_finite_type] at h
  | SmtType.Datatype s2 d2, h => by
      simp only [__smtx_type_lift]
      by_cases hEq :
          native_Teq (SmtType.Datatype s d) (SmtType.Datatype s2 d2) = true
      · rw [native_ite, if_pos hEq]
        simp [__smtx_is_finite_type]
      · rw [native_ite, if_neg hEq]
        have hD : __smtx_is_finite_datatype d2 = false := by
          simpa [__smtx_is_finite_type] using h
        simpa [__smtx_is_finite_type] using
          dt_lift_infinite_of_infinite s d d2 hD
  | SmtType.Map A B, h => by
      simpa [__smtx_type_lift] using h
  | SmtType.Set A, h => by
      simpa [__smtx_type_lift] using h
  | SmtType.None, h => by
      simp [__smtx_type_lift, __smtx_is_finite_type]
  | SmtType.Int, h => by
      simp [__smtx_type_lift, __smtx_is_finite_type]
  | SmtType.Real, h => by
      simp [__smtx_type_lift, __smtx_is_finite_type]
  | SmtType.RegLan, h => by
      simp [__smtx_type_lift, __smtx_is_finite_type]
  | SmtType.Seq A, h => by
      simp [__smtx_type_lift, __smtx_is_finite_type]
  | SmtType.TypeRef r, h => by
      simp [__smtx_type_lift, __smtx_is_finite_type]
  | SmtType.USort u, h => by
      simp [__smtx_type_lift, __smtx_is_finite_type]
  | SmtType.FunType A B, h => by
      simp [__smtx_type_lift, __smtx_is_finite_type]
  | SmtType.DtcAppType A B, h => by
      simp [__smtx_type_lift, __smtx_is_finite_type]

private theorem dtc_lift_infinite_of_infinite
    (s : native_String) (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons),
      __smtx_is_finite_datatype_cons c = false →
        __smtx_is_finite_datatype_cons (__smtx_dtc_lift s d c) = false
  | SmtDatatypeCons.unit, h => by
      simp [__smtx_is_finite_datatype_cons] at h
  | SmtDatatypeCons.cons T c, h => by
      cases hT : __smtx_is_finite_type T
      · have hTLift :=
          type_lift_infinite_of_infinite s d T hT
        simp [__smtx_dtc_lift, __smtx_is_finite_datatype_cons,
          hTLift, native_and]
      · have hc : __smtx_is_finite_datatype_cons c = false := by
          cases hC : __smtx_is_finite_datatype_cons c <;>
            simp [__smtx_is_finite_datatype_cons, hT, hC, native_and] at h ⊢
        have hCLift := dtc_lift_infinite_of_infinite s d c hc
        simp [__smtx_dtc_lift, __smtx_is_finite_datatype_cons,
          hCLift, native_and]

private theorem dt_lift_infinite_of_infinite
    (s : native_String) (d : SmtDatatype) :
    ∀ (D : SmtDatatype),
      __smtx_is_finite_datatype D = false →
        __smtx_is_finite_datatype (__smtx_dt_lift s d D) = false
  | SmtDatatype.null, h => by
      simp [__smtx_is_finite_datatype] at h
  | SmtDatatype.sum c D, h => by
      cases hC : __smtx_is_finite_datatype_cons c
      · have hCLift := dtc_lift_infinite_of_infinite s d c hC
        simp [__smtx_dt_lift, __smtx_is_finite_datatype, hCLift, native_and]
      · have hD : __smtx_is_finite_datatype D = false := by
          cases hD : __smtx_is_finite_datatype D <;>
            simp [__smtx_is_finite_datatype, hC, hD, native_and] at h ⊢
        have hDLift := dt_lift_infinite_of_infinite s d D hD
        simp [__smtx_dt_lift, __smtx_is_finite_datatype, hDLift, native_and]

end

mutual

private theorem type_substitute_infinite_of_infinite_replacement
    (s : native_String) (d : SmtDatatype)
    (hDInf : __smtx_is_finite_datatype d = false) :
    ∀ (T : SmtType),
      __smtx_is_finite_type T = false →
        __smtx_is_finite_type (__smtx_type_substitute s d T) = false
  | SmtType.Bool, h => by simp [__smtx_is_finite_type] at h
  | SmtType.BitVec w, h => by simp [__smtx_is_finite_type] at h
  | SmtType.Char, h => by simp [__smtx_is_finite_type] at h
  | SmtType.Datatype s2 d2, h => by
      have hd2 : __smtx_is_finite_datatype d2 = false := by
        simpa [__smtx_is_finite_type] using h
      simp only [__smtx_type_substitute]
      by_cases hEq : native_streq s s2 = true
      · rw [native_ite, if_pos hEq]
        simpa [__smtx_is_finite_type] using hd2
      · rw [native_ite, if_neg hEq]
        have hLiftInf :
            __smtx_is_finite_datatype (__smtx_dt_lift s2 d2 d) = false :=
          dt_lift_infinite_of_infinite s2 d2 d hDInf
        simpa [__smtx_is_finite_type] using
          dt_substitute_infinite_of_infinite_replacement
            s (__smtx_dt_lift s2 d2 d) hLiftInf d2 hd2
  | SmtType.Map A B, h => by
      simpa [__smtx_type_substitute] using h
  | SmtType.Set A, h => by
      simpa [__smtx_type_substitute] using h
  | SmtType.TypeRef r, h => by
      simp only [__smtx_type_substitute]
      by_cases hEq : native_streq s r = true
      · rw [native_ite, if_pos hEq]
        simpa [__smtx_is_finite_type] using hDInf
      · have hEqFalse : native_streq s r = false := by
          cases hsr : native_streq s r <;> simp [hsr] at hEq ⊢
        rw [native_ite, if_neg hEq]
        simp [__smtx_is_finite_type]
  | SmtType.None, h => by
      simp [__smtx_type_substitute, __smtx_is_finite_type]
  | SmtType.Int, h => by
      simp [__smtx_type_substitute, __smtx_is_finite_type]
  | SmtType.Real, h => by
      simp [__smtx_type_substitute, __smtx_is_finite_type]
  | SmtType.RegLan, h => by
      simp [__smtx_type_substitute, __smtx_is_finite_type]
  | SmtType.Seq A, h => by
      simp [__smtx_type_substitute, __smtx_is_finite_type]
  | SmtType.USort u, h => by
      simp [__smtx_type_substitute, __smtx_is_finite_type]
  | SmtType.FunType A B, h => by
      simp [__smtx_type_substitute, __smtx_is_finite_type]
  | SmtType.DtcAppType A B, h => by
      simp [__smtx_type_substitute, __smtx_is_finite_type]

private theorem dtc_substitute_infinite_of_infinite_replacement
    (s : native_String) (d : SmtDatatype)
    (hDInf : __smtx_is_finite_datatype d = false) :
    ∀ (c : SmtDatatypeCons),
      __smtx_is_finite_datatype_cons c = false →
        __smtx_is_finite_datatype_cons (__smtx_dtc_substitute s d c) = false
  | SmtDatatypeCons.unit, h => by
      simp [__smtx_is_finite_datatype_cons] at h
  | SmtDatatypeCons.cons T c, h => by
      cases hT : __smtx_is_finite_type T
      · have hTSub :=
          type_substitute_infinite_of_infinite_replacement s d hDInf T hT
        simp [__smtx_dtc_substitute, __smtx_is_finite_datatype_cons,
          hTSub, native_and]
      · have hC : __smtx_is_finite_datatype_cons c = false := by
          cases hC : __smtx_is_finite_datatype_cons c <;>
            simp [__smtx_is_finite_datatype_cons, hT, hC, native_and] at h ⊢
        have hCSub :=
          dtc_substitute_infinite_of_infinite_replacement s d hDInf c hC
        simp [__smtx_dtc_substitute, __smtx_is_finite_datatype_cons,
          hCSub, native_and]

private theorem dt_substitute_infinite_of_infinite_replacement
    (s : native_String) (d : SmtDatatype)
    (hDInf : __smtx_is_finite_datatype d = false) :
    ∀ (D : SmtDatatype),
      __smtx_is_finite_datatype D = false →
        __smtx_is_finite_datatype (__smtx_dt_substitute s d D) = false
  | SmtDatatype.null, h => by
      simp [__smtx_is_finite_datatype] at h
  | SmtDatatype.sum c D, h => by
      cases hC : __smtx_is_finite_datatype_cons c
      · have hCSub :=
          dtc_substitute_infinite_of_infinite_replacement s d hDInf c hC
        simp [__smtx_dt_substitute, __smtx_is_finite_datatype,
          hCSub, native_and]
      · have hD : __smtx_is_finite_datatype D = false := by
          cases hD : __smtx_is_finite_datatype D <;>
            simp [__smtx_is_finite_datatype, hC, hD, native_and] at h ⊢
        have hDSub :=
          dt_substitute_infinite_of_infinite_replacement s d hDInf D hD
        simp [__smtx_dt_substitute, __smtx_is_finite_datatype,
          hDSub, native_and]

end

private theorem datatype_type_substitute_infinite_of_outer_infinite
    (s : native_String) (d : SmtDatatype)
    (hDInf : __smtx_is_finite_datatype d = false)
    (s2 : native_String) (d2 : SmtDatatype)
    (hRawInf : __smtx_is_finite_datatype d2 = false) :
    __smtx_is_finite_type
        (__smtx_type_substitute s d (SmtType.Datatype s2 d2)) = false := by
  exact type_substitute_infinite_of_infinite_replacement s d hDInf
    (SmtType.Datatype s2 d2) (by simpa [__smtx_is_finite_type] using hRawInf)

private theorem type_substitute_infinite_of_current_infinite
    (s : native_String) (d : SmtDatatype)
    (hDInf : __smtx_is_finite_datatype d = false)
    (T : SmtType)
    (hTInf : __smtx_is_finite_type T = false) :
    __smtx_is_finite_type (__smtx_type_substitute s d T) = false :=
  type_substitute_infinite_of_infinite_replacement s d hDInf T hTInf
private theorem finite_wf_inhabited_default_ne {T : SmtType}
    (hInh : native_inhabited_type T = true)
    (hfin : __smtx_is_finite_type T = true)
    (hwf : __smtx_type_wf_rec T T = true) :
    __smtx_type_default T ≠ SmtValue.NotValue := by
  have hne := fin_defaultable T T (ShT.refl T) hfin hwf hInh
  simpa [__smtx_type_default] using hne

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

-- Finite non-unit datatype inhabitants. This block mirrors the old value-substitution
-- "inhabit" construction using the refactored diagonal well-formedness/defaultability
-- facts. All three theorems are private and feed only the public wrapper below.
mutual

private theorem finite_nonunit_type_nondefault_value :
    ∀ (T : SmtType),
      native_inhabited_type T = true → __smtx_type_wf_rec T T = true →
        __smtx_is_finite_type T = true → __smtx_is_unit_type T = false →
          ∃ e : SmtValue, __smtx_typeof_value e = T ∧ __smtx_value_canonical_bool e = true ∧
            native_veq e (__smtx_type_default T) = false
  | SmtType.None, hInh, hRec, hFin, hNU => by
      simp [native_inhabited_type, native_Teq, native_not, native_and] at hInh
  | SmtType.Bool, hInh, hRec, hFin, hNU => by
      refine ⟨SmtValue.Boolean true, ?_, ?_, ?_⟩ <;>
        simp [__smtx_typeof_value, __smtx_value_canonical_bool,
          __smtx_type_default, __smtx_type_default_rec, native_veq]
  | SmtType.Int, hInh, hRec, hFin, hNU => by
      simp [__smtx_is_finite_type] at hFin
  | SmtType.Real, hInh, hRec, hFin, hNU => by
      simp [__smtx_is_finite_type] at hFin
  | SmtType.RegLan, hInh, hRec, hFin, hNU => by
      simp [__smtx_type_wf_rec] at hRec
  | SmtType.BitVec w, hInh, hRec, hFin, hNU => by
      cases w with
      | zero =>
          simp [__smtx_is_unit_type, native_nateq] at hNU
      | succ w =>
          refine ⟨SmtValue.Binary (native_nat_to_int (Nat.succ w)) 1, ?_, ?_, ?_⟩
          · exact bitvec_succ_one_typeof w
          · exact bitvec_succ_one_canonical w
          · exact bitvec_succ_one_ne_default w
  | SmtType.Map T U, hInh, hRec, hFin, hNU => by
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true ∧
              native_inhabited_type U = true ∧
                __smtx_type_wf_rec U U = true := by
        have h9 :
            ((native_inhabited_type T = true ∧ __smtx_type_wf_rec T T = true) ∧
              __smtx_type_names_consistent T = true) ∧
              ((native_inhabited_type U = true ∧ __smtx_type_wf_rec U U = true) ∧
                __smtx_type_names_consistent U = true) := by
          simpa [__smtx_type_wf_rec, native_and] using hRec
        exact ⟨h9.1.1.1, h9.1.1.2, h9.2.1.1, h9.2.1.2⟩
      have hUNonUnit : __smtx_is_unit_type U = false := by
        simpa [__smtx_is_unit_type] using hNU
      have hUFinite : __smtx_is_finite_type U = true := by
        cases hUnit : __smtx_is_unit_type U <;>
          cases hTFin : __smtx_is_finite_type T <;>
            cases hUFin : __smtx_is_finite_type U <;>
              simp [__smtx_is_finite_type, hUnit, hTFin, hUFin, native_or,
                native_and] at hFin hUNonUnit ⊢
      have hTDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.1
      have hUDefault :=
        type_default_typed_canonical_of_native_inhabited hRecParts.2.2.1
      rcases finite_nonunit_type_nondefault_value
          U hRecParts.2.2.1 hRecParts.2.2.2 hUFinite hUNonUnit with
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
      · have hTFinite : __smtx_is_finite_type T = true := by
          cases hUnit : __smtx_is_unit_type U <;>
            cases hTFin : __smtx_is_finite_type T <;>
              cases hUFin : __smtx_is_finite_type U <;>
                simp [__smtx_is_finite_type, hUnit, hTFin, hUFin, native_or,
                  native_and] at hFin hUNonUnit ⊢
        simp [__smtx_value_canonical_bool, __smtx_map_canonical,
          __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
          __smtx_msm_get_default, hTDefault.2, heCan, hUDefault.1,
          hUDefault.2, hTFinite, heNeDefaultProp, native_and, native_ite,
          native_not, native_veq]
      · have hUNV : __smtx_type_default U ≠ SmtValue.NotValue :=
          type_default_ne_notValue_of_native_inhabited hRecParts.2.2.1
            (ne_none_of_native_inhabited hRecParts.2.2.1)
        have hcond :
            decide (__smtx_type_default_rec U U = SmtValue.NotValue) = false := by
          apply decide_eq_false
          simpa [__smtx_type_default] using hUNV
        simp [__smtx_type_default, __smtx_type_default_rec, native_veq, native_ite, hcond]
  | SmtType.Set T, hInh, hRec, hFin, hNU => by
      have hRecParts :
          native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true := by
        have h3 : (native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true) ∧
            __smtx_type_names_consistent T = true := by
          simpa [__smtx_type_wf_rec, native_and] using hRec
        exact h3.1
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
        cases hFinT : __smtx_is_finite_type T <;>
          simp [__smtx_value_canonical_bool, __smtx_map_canonical,
            __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
            __smtx_msm_get_default, hTDefault.2, hBoolDef, hFinT, native_and, native_ite,
            native_not, native_veq, __smtx_typeof_value]
      · simp [__smtx_type_default, __smtx_type_default_rec, native_veq]
  | SmtType.Seq T, hInh, hRec, hFin, hNU => by
      simp [__smtx_is_finite_type] at hFin
  | SmtType.Char, hInh, hRec, hFin, hNU => by
      exact ⟨SmtValue.Char 1, by native_decide, by native_decide, by native_decide⟩
  | SmtType.Datatype s d, hInh, hRec, hFin, hNU => by
      exact finite_nonunit_datatype_nondefault_value s d hInh hRec hFin hNU
  | SmtType.TypeRef s, hInh, hRec, hFin, hNU => by
      simp [__smtx_is_finite_type] at hFin
  | SmtType.USort u, hInh, hRec, hFin, hNU => by
      simp [__smtx_is_finite_type] at hFin
  | SmtType.FunType T U, hInh, hRec, hFin, hNU => by
      simp [__smtx_is_finite_type] at hFin
  | SmtType.DtcAppType T U, hInh, hRec, hFin, hNU => by
      simp [__smtx_is_finite_type] at hFin

private theorem finite_nonunit_datatype_nondefault_value :
    ∀ (s : native_String) (d : SmtDatatype),
      native_inhabited_type (SmtType.Datatype s d) = true →
      __smtx_type_wf_rec (SmtType.Datatype s d) (SmtType.Datatype s d) = true →
      __smtx_is_finite_type (SmtType.Datatype s d) = true →
      __smtx_is_unit_type (SmtType.Datatype s d) = false →
        ∃ e : SmtValue, __smtx_typeof_value e = SmtType.Datatype s d ∧
          __smtx_value_canonical_bool e = true ∧
          native_veq e (__smtx_type_default (SmtType.Datatype s d)) = false
  | s, SmtDatatype.null, hInh, hRec, hFin, hNU => by
      simp [native_inhabited_type, __smtx_type_default, __smtx_type_default_rec,
        __smtx_datatype_default, __smtx_typeof_value, native_Teq, native_not,
        native_and] at hInh
  | s, SmtDatatype.sum c SmtDatatype.null, hInh, hRec, hFin, hNU => by
      let d := SmtDatatype.sum c SmtDatatype.null
      have hFinD : __smtx_is_finite_datatype d = true := by
        simpa [d, __smtx_is_finite_type] using hFin
      have hSubD : __smtx_dt_substitute s d d = d :=
        subst_D_fin_id s d d hFinD
      have hWfD : __smtx_dt_wf_rec d d = true := by
        simpa [d, __smtx_type_wf_rec, hSubD] using hRec
      have hConsWf : __smtx_dt_cons_wf_rec c c = true :=
        dt_wf_cons_of_wf (cF := c) (cU := c)
          (dF := SmtDatatype.null) (dU := SmtDatatype.null) hWfD
      have hConsFin : __smtx_is_finite_datatype_cons c = true :=
        finite_dt_cons_of_finite_sum (c := c) (d := SmtDatatype.null) hFinD
      have hConsNonUnit : __smtx_is_unit_datatype_cons c = false := by
        simpa [d, __smtx_is_unit_type, __smtx_is_unit_datatype] using hNU
      have hSeedTy :
          __smtx_typeof_value (SmtValue.DtCons s d 0) =
            chainType c (SmtType.Datatype s d) := by
        exact typeof_dtcons_chain (s := s) (d := d) 0 hFinD (by rfl)
      have hSeedCan :
          __smtx_value_canonical_bool (SmtValue.DtCons s d 0) = true := by
        simp [__smtx_value_canonical_bool]
      have hSeedNe : SmtValue.DtCons s d 0 ≠ SmtValue.NotValue := by
        intro h; cases h
      rcases finite_nonunit_datatype_cons_nondefault_value s d c
          hConsWf hConsFin hConsNonUnit (SmtValue.DtCons s d 0)
          hSeedTy hSeedCan hSeedNe with
        ⟨e, heTy, heCan, heNeConsDefault⟩
      have hConsDefaultNe :
          __smtx_datatype_cons_default (SmtValue.DtCons s d 0) c c ≠
            SmtValue.NotValue :=
        cons_defaultable c c (ShC_refl c) hConsFin hConsWf
          (SmtValue.DtCons s d 0) hSeedNe
      refine ⟨e, heTy, heCan, ?_⟩
      rw [__smtx_type_default, __smtx_type_default_rec, hSubD]
      rw [datatype_default_select s d 0 c c SmtDatatype.null SmtDatatype.null hConsDefaultNe]
      exact heNeConsDefault
  | s, SmtDatatype.sum c0 (SmtDatatype.sum c1 dRest), hInh, hRec, hFin, hNU => by
      let d := SmtDatatype.sum c0 (SmtDatatype.sum c1 dRest)
      have hFinD : __smtx_is_finite_datatype d = true := by
        simpa [d, __smtx_is_finite_type] using hFin
      have hSubD : __smtx_dt_substitute s d d = d :=
        subst_D_fin_id s d d hFinD
      have hWfD : __smtx_dt_wf_rec d d = true := by
        simpa [d, __smtx_type_wf_rec, hSubD] using hRec
      have hTailWf :
          __smtx_dt_wf_rec (SmtDatatype.sum c1 dRest) (SmtDatatype.sum c1 dRest) = true := by
        exact dt_wf_tail_of_nonempty_tail_wf
          (cF := c0) (cU := c0) (cTailF := c1) (cTailU := c1)
          (dTailF := dRest) (dTailU := dRest) hWfD
      have hCons0Wf : __smtx_dt_cons_wf_rec c0 c0 = true :=
        dt_wf_cons_of_wf (cF := c0) (cU := c0)
          (dF := SmtDatatype.sum c1 dRest) (dU := SmtDatatype.sum c1 dRest) hWfD
      have hCons1Wf : __smtx_dt_cons_wf_rec c1 c1 = true :=
        dt_wf_cons_of_wf (cF := c1) (cU := c1)
          (dF := dRest) (dU := dRest) hTailWf
      have hCons0Fin : __smtx_is_finite_datatype_cons c0 = true :=
        finite_dt_cons_of_finite_sum (c := c0) (d := SmtDatatype.sum c1 dRest) hFinD
      have hTailFin : __smtx_is_finite_datatype (SmtDatatype.sum c1 dRest) = true :=
        finite_dt_tail_of_finite_sum (c := c0) (d := SmtDatatype.sum c1 dRest) hFinD
      have hCons1Fin : __smtx_is_finite_datatype_cons c1 = true :=
        finite_dt_cons_of_finite_sum (c := c1) (d := dRest) hTailFin
      have hSeed0Ne : SmtValue.DtCons s d 0 ≠ SmtValue.NotValue := by
        intro h; cases h
      have hSeed1Ne : SmtValue.DtCons s d 1 ≠ SmtValue.NotValue := by
        intro h; cases h
      have hCons0DefaultNe :
          __smtx_datatype_cons_default (SmtValue.DtCons s d 0) c0 c0 ≠
            SmtValue.NotValue :=
        cons_defaultable c0 c0 (ShC_refl c0) hCons0Fin hCons0Wf
          (SmtValue.DtCons s d 0) hSeed0Ne
      have hCons1DefaultNe :
          __smtx_datatype_cons_default (SmtValue.DtCons s d 1) c1 c1 ≠
            SmtValue.NotValue :=
        cons_defaultable c1 c1 (ShC_refl c1) hCons1Fin hCons1Wf
          (SmtValue.DtCons s d 1) hSeed1Ne
      have hSeed1Ty :
          __smtx_typeof_value (SmtValue.DtCons s d 1) =
            chainType c1 (SmtType.Datatype s d) := by
        exact typeof_dtcons_chain (s := s) (d := d) 1 hFinD (by rfl)
      have hSeed1Can :
          __smtx_value_canonical_bool (SmtValue.DtCons s d 1) = true := by
        simp [__smtx_value_canonical_bool]
      have hVal1TyCan :
          __smtx_typeof_value
              (__smtx_datatype_cons_default (SmtValue.DtCons s d 1) c1 c1) =
                SmtType.Datatype s d ∧
            __smtx_value_canonical_bool
              (__smtx_datatype_cons_default (SmtValue.DtCons s d 1) c1 c1) = true := by
        rcases datatype_cons_default_kernel c1 c1 (dtcSubstStar_refl c1)
            (SmtValue.DtCons s d 1) (SmtType.Datatype s d)
            hSeed1Ty hSeed1Can with hNV | hTyCan
        · exact False.elim (hCons1DefaultNe hNV)
        · exact hTyCan
      have hDefaultEq :
          __smtx_type_default (SmtType.Datatype s d) =
            __smtx_datatype_cons_default (SmtValue.DtCons s d 0) c0 c0 := by
        rw [__smtx_type_default, __smtx_type_default_rec, hSubD]
        exact datatype_default_select s d 0 c0 c0
          (SmtDatatype.sum c1 dRest) (SmtDatatype.sum c1 dRest) hCons0DefaultNe
      refine
        ⟨__smtx_datatype_cons_default (SmtValue.DtCons s d 1) c1 c1,
          hVal1TyCan.1, hVal1TyCan.2, ?_⟩
      exact native_veq_eq_false_of_ne (by
        intro hEq
        rw [hDefaultEq] at hEq
        have hHeadEq :
            __vsm_apply_head
                (__smtx_datatype_cons_default (SmtValue.DtCons s d 1) c1 c1) =
              __vsm_apply_head
                (__smtx_datatype_cons_default (SmtValue.DtCons s d 0) c0 c0) := by
          exact congrArg __vsm_apply_head hEq
        rw [cons_default_head c1 c1 (SmtValue.DtCons s d 1) hCons1DefaultNe,
          cons_default_head c0 c0 (SmtValue.DtCons s d 0) hCons0DefaultNe] at hHeadEq
        simp [__vsm_apply_head] at hHeadEq)

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
  | SmtDatatypeCons.unit, hWf, hFin, hNU, v, hvTy, hvCan, hvNe => by
      simp [__smtx_is_unit_datatype_cons] at hNU
  | SmtDatatypeCons.cons T c, hWf, hFin, hNU, v, hvTy, hvCan, hvNe => by
      have hFinParts :
          __smtx_is_finite_type T = true ∧ __smtx_is_finite_datatype_cons c = true := by
        simpa [__smtx_is_finite_datatype_cons, native_and] using hFin
      have hWfParts := dt_cons_wf_diag_parts hWf
      by_cases hTUnit : __smtx_is_unit_type T = true
      · have hTailNonUnit : __smtx_is_unit_datatype_cons c = false := by
          cases hTailUnit : __smtx_is_unit_datatype_cons c <;>
            simp [__smtx_is_unit_datatype_cons, hTUnit, hTailUnit, native_and] at hNU ⊢
        have hDefaultT := type_default_typed_canonical_of_native_inhabited hWfParts.1
        have hDefaultTNe :
            __smtx_type_default_rec T T ≠ SmtValue.NotValue := by
          have hne := fin_defaultable T T (ShT.refl T)
            hFinParts.1 hWfParts.2.1 hWfParts.1
          exact hne
        have hTne : T ≠ SmtType.None := ne_none_of_native_inhabited hWfParts.1
        have hSeedTy :
            __smtx_typeof_value (SmtValue.Apply v (__smtx_type_default_rec T T)) =
              chainType c (SmtType.Datatype s d) := by
          apply apply_seed_typeof hvTy
          · simpa [__smtx_type_default] using hDefaultT.1
          · exact hTne
        have hSeedCan :
            __smtx_value_canonical_bool
              (SmtValue.Apply v (__smtx_type_default_rec T T)) = true := by
          have hDefaultTCanRec :
              __smtx_value_canonical_bool (__smtx_type_default_rec T T) = true := by
            simpa [__smtx_type_default] using hDefaultT.2
          simp [__smtx_value_canonical_bool, hvCan, hDefaultTCanRec, native_and]
        have hSeedNe :
            SmtValue.Apply v (__smtx_type_default_rec T T) ≠ SmtValue.NotValue := by
          intro h; cases h
        rcases finite_nonunit_datatype_cons_nondefault_value s d c
            hWfParts.2.2 hFinParts.2 hTailNonUnit
            (SmtValue.Apply v (__smtx_type_default_rec T T))
            hSeedTy hSeedCan hSeedNe with
          ⟨e, heTy, heCan, heNeTailDefault⟩
        refine ⟨e, heTy, heCan, ?_⟩
        have hDefaultUnfold :
            __smtx_datatype_cons_default v
                (SmtDatatypeCons.cons T c) (SmtDatatypeCons.cons T c) =
              __smtx_datatype_cons_default
                (SmtValue.Apply v (__smtx_type_default_rec T T)) c c := by
          rw [__smtx_datatype_cons_default]
          have hFieldVeq :
              native_veq (__smtx_type_default_rec T T) SmtValue.NotValue = false :=
            native_veq_eq_false_of_ne hDefaultTNe
          simp [native_ite, hFieldVeq]
        rw [hDefaultUnfold]
        exact heNeTailDefault
      · have hTNonUnit : __smtx_is_unit_type T = false := by
          cases h : __smtx_is_unit_type T <;> simp [h] at hTUnit ⊢
        rcases finite_nonunit_type_nondefault_value T
            hWfParts.1 hWfParts.2.1 hFinParts.1 hTNonUnit with
          ⟨field, hFieldTy, hFieldCan, hFieldNeDefault⟩
        have hFieldNeDefaultProp : field ≠ __smtx_type_default T := by
          intro hEq
          subst field
          simp [native_veq] at hFieldNeDefault
        have hTne : T ≠ SmtType.None := ne_none_of_native_inhabited hWfParts.1
        have hNewSeedTy :
            __smtx_typeof_value (SmtValue.Apply v field) =
              chainType c (SmtType.Datatype s d) :=
          apply_seed_typeof hvTy hFieldTy hTne
        have hNewSeedCan :
            __smtx_value_canonical_bool (SmtValue.Apply v field) = true := by
          simp [__smtx_value_canonical_bool, hvCan, hFieldCan, native_and]
        have hNewSeedNe : SmtValue.Apply v field ≠ SmtValue.NotValue := by
          intro h; cases h
        have hNewTailNe :
            __smtx_datatype_cons_default (SmtValue.Apply v field) c c ≠
              SmtValue.NotValue :=
          cons_defaultable c c (ShC_refl c) hFinParts.2 hWfParts.2.2
            (SmtValue.Apply v field) hNewSeedNe
        have hNewTyCan :
            __smtx_typeof_value
                (__smtx_datatype_cons_default (SmtValue.Apply v field) c c) =
                  SmtType.Datatype s d ∧
              __smtx_value_canonical_bool
                (__smtx_datatype_cons_default (SmtValue.Apply v field) c c) = true := by
          rcases datatype_cons_default_kernel c c (dtcSubstStar_refl c)
              (SmtValue.Apply v field) (SmtType.Datatype s d)
              hNewSeedTy hNewSeedCan with hNV | hTyCan
          · exact False.elim (hNewTailNe hNV)
          · exact hTyCan
        have hDefaultTNe :
            __smtx_type_default_rec T T ≠ SmtValue.NotValue := by
          exact fin_defaultable T T (ShT.refl T)
            hFinParts.1 hWfParts.2.1 hWfParts.1
        have hDefaultSeedNe :
            SmtValue.Apply v (__smtx_type_default_rec T T) ≠ SmtValue.NotValue := by
          intro h; cases h
        have hDefaultTailNe :
            __smtx_datatype_cons_default
                (SmtValue.Apply v (__smtx_type_default_rec T T)) c c ≠
              SmtValue.NotValue :=
          cons_defaultable c c (ShC_refl c) hFinParts.2 hWfParts.2.2
            (SmtValue.Apply v (__smtx_type_default_rec T T)) hDefaultSeedNe
        have hDefaultUnfold :
            __smtx_datatype_cons_default v
                (SmtDatatypeCons.cons T c) (SmtDatatypeCons.cons T c) =
              __smtx_datatype_cons_default
                (SmtValue.Apply v (__smtx_type_default_rec T T)) c c := by
          rw [__smtx_datatype_cons_default]
          have hFieldVeq :
              native_veq (__smtx_type_default_rec T T) SmtValue.NotValue = false :=
            native_veq_eq_false_of_ne hDefaultTNe
          simp [native_ite, hFieldVeq]
        refine
          ⟨__smtx_datatype_cons_default (SmtValue.Apply v field) c c,
            hNewTyCan.1, hNewTyCan.2, ?_⟩
        rw [hDefaultUnfold]
        exact native_veq_eq_false_of_ne (by
          intro hEq
          have hSeedEq :
              SmtValue.Apply v field =
                SmtValue.Apply v (__smtx_type_default_rec T T) :=
            cons_default_seed_inj c c
              (SmtValue.Apply v field)
              (SmtValue.Apply v (__smtx_type_default_rec T T))
              hNewTailNe hEq
          have hFieldEq : field = __smtx_type_default T := by
            simpa [__smtx_type_default] using (SmtValue.Apply.inj hSeedEq).2
          exact hFieldNeDefaultProp hFieldEq)

end

/-- A finite, non-unit, well-formed datatype has a typed canonical inhabitant
distinct from its default. -/
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

/-!
### The diagonal infinite-datatype pump

Fuel-indexed oracle over *diagonal* datatype entries (inhabited,
self-well-formed, infinite raw body).  The successor step builds a fresh
value with one designated infinite field filled by an oracle value of the
previous fuel level: self-referencing fields re-use the same entry, nested
datatype fields re-root at the folded field via `wf_diag_push`
(`Cpc.Proofs.Canonical.WfDiag`), and container/base fields — which are fixed
by substitution — use direct large witnesses.  No environment/stack of
enclosing datatypes is needed.
-/

private def DiagOracle (n : Nat) : Prop :=
  ∀ (s : native_String) (d : SmtDatatype),
    native_inhabited_type (SmtType.Datatype s d) = true →
    __smtx_type_wf_rec (SmtType.Datatype s d) (SmtType.Datatype s d) = true →
    __smtx_is_finite_datatype d = false →
      ∃ v : SmtValue,
        __smtx_typeof_value v = SmtType.Datatype s d ∧
          __smtx_value_canonical_bool v = true ∧ n ≤ sizeOf v

private theorem diag_oracle_zero : DiagOracle 0 := by
  intro s d hInh _hWf _hInf
  have hDef := type_default_typed_canonical_of_native_inhabited hInh
  exact ⟨__smtx_type_default (SmtType.Datatype s d), hDef.1, hDef.2,
    Nat.zero_le _⟩

/-- `n`-form singleton-set witness. -/
private theorem set_large_of_elem_witness_n
    (A : SmtType) (x : SmtValue) (n : Nat)
    (hxTy : __smtx_typeof_value x = A)
    (hxCan : __smtx_value_canonical_bool x = true)
    (hxSize : n ≤ sizeOf x) :
    ∃ y : SmtValue,
      __smtx_typeof_value y = SmtType.Set A ∧
        __smtx_value_canonical_bool y = true ∧ n ≤ sizeOf y := by
  refine
    ⟨SmtValue.Set
      (SmtMap.cons x (SmtValue.Boolean true)
        (SmtMap.default A (SmtValue.Boolean false))), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value, __smtx_typeof_map_value,
      __smtx_map_to_set_type, hxTy, native_Teq, native_ite]
  · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
      __smtx_map_default_canonical, __smtx_map_entries_ordered_after,
      __smtx_msm_get_default, hxCan, __smtx_typeof_value,
      __smtx_type_default, __smtx_type_default_rec, native_veq,
      native_and, native_not, native_ite]
  · rw [show
      sizeOf
          (SmtValue.Set
            (SmtMap.cons x (SmtValue.Boolean true)
              (SmtMap.default A (SmtValue.Boolean false)))) =
        1 + (1 + sizeOf x + sizeOf (SmtValue.Boolean true) +
          sizeOf (SmtMap.default A (SmtValue.Boolean false))) by rfl]
    omega

/-- `n`-form singleton-map witness with a large range value. -/
private theorem map_large_of_value_witness_n
    (A B : SmtType) (x : SmtValue) (n : Nat)
    (hAInh : native_inhabited_type A = true)
    (hBInh : native_inhabited_type B = true)
    (hxTy : __smtx_typeof_value x = B)
    (hxCan : __smtx_value_canonical_bool x = true)
    (hxSize : n ≤ sizeOf x)
    (hxDef : native_veq x (__smtx_type_default B) = false) :
    ∃ y : SmtValue,
      __smtx_typeof_value y = SmtType.Map A B ∧
        __smtx_value_canonical_bool y = true ∧ n ≤ sizeOf y := by
  have hADefault :=
    type_default_typed_canonical_of_native_inhabited hAInh
  have hBDefault :=
    type_default_typed_canonical_of_native_inhabited hBInh
  have hxNeDefaultProp : x ≠ __smtx_type_default B := by
    intro hEq
    subst x
    simp [native_veq] at hxDef
  refine
    ⟨SmtValue.Map
      (SmtMap.cons (__smtx_type_default A) x
        (SmtMap.default A (__smtx_type_default B))), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value, __smtx_typeof_map_value,
      hADefault.1, hxTy, hBDefault.1, native_ite, native_Teq]
  · cases hAFin : __smtx_is_finite_type A
    · have hDefaultCan :
          __smtx_map_default_canonical A (__smtx_type_default B) = true := by
        simp [__smtx_map_default_canonical, hAFin, native_ite]
      simp [__smtx_value_canonical_bool, __smtx_map_canonical,
        __smtx_map_entries_ordered_after, __smtx_msm_get_default,
        hADefault.2, hBDefault.2, hDefaultCan, hxCan, hxNeDefaultProp,
        native_and, native_not, native_veq]
    · have hDefaultCan :
          __smtx_map_default_canonical A (__smtx_type_default B) = true := by
        simp [__smtx_map_default_canonical, hAFin, hBDefault.1,
          native_ite, native_veq]
      simp [__smtx_value_canonical_bool, __smtx_map_canonical,
        __smtx_map_entries_ordered_after, __smtx_msm_get_default,
        hADefault.2, hBDefault.2, hDefaultCan, hxCan, hxNeDefaultProp,
        native_and, native_not, native_veq]
  · rw [show
      sizeOf
          (SmtValue.Map
            (SmtMap.cons (__smtx_type_default A) x
              (SmtMap.default A (__smtx_type_default B)))) =
        1 + (1 + sizeOf (__smtx_type_default A) + sizeOf x +
          sizeOf (SmtMap.default A (__smtx_type_default B))) by rfl]
    omega

/-- `n`-form singleton-map witness with a large key over an infinite domain;
the entry value is any canonical value distinct from the range default. -/
private theorem map_large_of_key_witness_n
    (A B : SmtType) (k e : SmtValue) (n : Nat)
    (hAInf : __smtx_is_finite_type A = false)
    (hBInh : native_inhabited_type B = true)
    (hkTy : __smtx_typeof_value k = A)
    (hkCan : __smtx_value_canonical_bool k = true)
    (hkSize : n ≤ sizeOf k)
    (heTy : __smtx_typeof_value e = B)
    (heCan : __smtx_value_canonical_bool e = true)
    (heNe : native_veq e (__smtx_type_default B) = false) :
    ∃ y : SmtValue,
      __smtx_typeof_value y = SmtType.Map A B ∧
        __smtx_value_canonical_bool y = true ∧ n ≤ sizeOf y := by
  have hBDefault :=
    type_default_typed_canonical_of_native_inhabited hBInh
  have heNeProp : e ≠ __smtx_type_default B := by
    intro hEq
    subst e
    simp [native_veq] at heNe
  refine
    ⟨SmtValue.Map
      (SmtMap.cons k e (SmtMap.default A (__smtx_type_default B))), ?_, ?_, ?_⟩
  · simp [__smtx_typeof_value, __smtx_typeof_map_value,
      hkTy, heTy, hBDefault.1, native_ite, native_Teq]
  · have hDefaultCan :
        __smtx_map_default_canonical A (__smtx_type_default B) = true := by
      simp [__smtx_map_default_canonical, hAInf, native_ite]
    simp [__smtx_value_canonical_bool, __smtx_map_canonical,
      __smtx_map_entries_ordered_after, __smtx_msm_get_default,
      hkCan, heCan, hBDefault.2, hDefaultCan, heNeProp,
      native_and, native_not, native_veq]
  · rw [show
      sizeOf
          (SmtValue.Map
            (SmtMap.cons k e (SmtMap.default A (__smtx_type_default B)))) =
        1 + (1 + sizeOf k + sizeOf e +
          sizeOf (SmtMap.default A (__smtx_type_default B))) by rfl]
    omega

/-- Large witnesses for *closed* (diagonally well-formed) infinite types,
given the datatype oracle at the same fuel level. -/
private theorem closed_infinite_large_witness_from_oracle
    (n : Nat) (hOracle : DiagOracle n) :
    ∀ (T : SmtType),
      native_inhabited_type T = true →
      __smtx_type_wf_rec T T = true →
      __smtx_is_finite_type T = false →
        ∃ x : SmtValue,
          __smtx_typeof_value x = T ∧
            __smtx_value_canonical_bool x = true ∧ n ≤ sizeOf x
  | SmtType.None, hInh, _hWf, _hInf => by
      simp [native_inhabited_type, native_Teq, native_not, native_and,
        __smtx_type_default, __smtx_type_default_rec,
        __smtx_typeof_value] at hInh
  | SmtType.Bool, _hInh, _hWf, hInf => by
      simp [__smtx_is_finite_type] at hInf
  | SmtType.BitVec w, _hInh, _hWf, hInf => by
      simp [__smtx_is_finite_type] at hInf
  | SmtType.Char, _hInh, _hWf, hInf => by
      simp [__smtx_is_finite_type] at hInf
  | SmtType.RegLan, _hInh, hWf, _hInf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.TypeRef r, _hInh, hWf, _hInf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.FunType A B, _hInh, hWf, _hInf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.DtcAppType A B, _hInh, hWf, _hInf => by
      simp [__smtx_type_wf_rec] at hWf
  | SmtType.Int, _hInh, _hWf, _hInf =>
      int_large_witness n
  | SmtType.Real, _hInh, _hWf, _hInf =>
      real_large_witness n
  | SmtType.USort u, _hInh, _hWf, _hInf =>
      usort_large_witness u n
  | SmtType.Seq U, _hInh, hWf, _hInf => by
      have hParts :
          (native_inhabited_type U = true ∧
            __smtx_type_wf_rec U U = true) ∧
            __smtx_type_names_consistent U = true := by
        simpa [__smtx_type_wf_rec, native_and] using hWf
      exact seq_inhabited_large_witness U hParts.1.1 n
  | SmtType.Set A, hInh, hWf, hInf => by
      have hParts :
          (native_inhabited_type A = true ∧
            __smtx_type_wf_rec A A = true) ∧
            __smtx_type_names_consistent A = true := by
        simpa [__smtx_type_wf_rec, native_and] using hWf
      have hAInf : __smtx_is_finite_type A = false := by
        simpa [__smtx_is_finite_type] using hInf
      rcases closed_infinite_large_witness_from_oracle n hOracle A
          hParts.1.1 hParts.1.2 hAInf with ⟨x, hxTy, hxCan, hxSize⟩
      exact set_large_of_elem_witness_n A x n hxTy hxCan hxSize
  | SmtType.Map A B, hInh, hWf, hInf => by
      have hParts :
          ((native_inhabited_type A = true ∧
            __smtx_type_wf_rec A A = true) ∧
            __smtx_type_names_consistent A = true) ∧
          ((native_inhabited_type B = true ∧
            __smtx_type_wf_rec B B = true) ∧
            __smtx_type_names_consistent B = true) := by
        simpa [__smtx_type_wf_rec, native_and] using hWf
      have hMapInf :
          __smtx_is_unit_type B = false ∧
            (__smtx_is_finite_type A = true →
              __smtx_is_finite_type B = false) := by
        cases hU : __smtx_is_unit_type B <;>
          cases hA : __smtx_is_finite_type A <;>
            cases hB : __smtx_is_finite_type B <;>
              simp_all [__smtx_is_finite_type, native_or, native_and]
      cases hBFin : __smtx_is_finite_type B
      · rcases closed_infinite_large_witness_from_oracle n hOracle B
            hParts.2.1.1 hParts.2.1.2 hBFin with ⟨x, hxTy, hxCan, hxSize⟩
        cases hxDef : native_veq x (__smtx_type_default B)
        · exact map_large_of_value_witness_n A B x n hParts.1.1.1
            hParts.2.1.1 hxTy hxCan hxSize hxDef
        · -- the large value coincides with the range default: the
          -- default-only map is canonical and just as large.
          refine ⟨SmtValue.Map (SmtMap.default A x), ?_, ?_, ?_⟩
          · simp [__smtx_typeof_value, __smtx_typeof_map_value, hxTy]
          · simp [__smtx_value_canonical_bool, __smtx_map_canonical,
              __smtx_map_default_canonical, hxTy, hxCan, hxDef,
              native_and, native_ite]
          · rw [show sizeOf (SmtValue.Map (SmtMap.default A x)) =
                1 + (1 + sizeOf A + sizeOf x) by rfl]
            omega
      · have hAInf : __smtx_is_finite_type A = false := by
          cases hA : __smtx_is_finite_type A
          · rfl
          · exact absurd (hMapInf.2 hA) (by simp [hBFin])
        rcases closed_infinite_large_witness_from_oracle n hOracle A
            hParts.1.1.1 hParts.1.1.2 hAInf with ⟨k, hkTy, hkCan, hkSize⟩
        rcases finite_nonunit_type_nondefault_value B hParts.2.1.1
            hParts.2.1.2 hBFin hMapInf.1 with ⟨e, heTy, heCan, heNe⟩
        exact map_large_of_key_witness_n A B k e n hAInf hParts.2.1.1
          hkTy hkCan hkSize heTy heCan heNe
  | SmtType.Datatype s2 d2, hInh, hWf, hInf => by
      have hd2 : __smtx_is_finite_datatype d2 = false := by
        simpa [__smtx_is_finite_type] using hInf
      exact hOracle s2 d2 hInh hWf hd2
  termination_by T => sizeOf T

/-- A large value for the folded form of a single infinite raw field of a
diagonal entry. -/
private theorem diag_pump_field_large
    (n : Nat) (hOracle : DiagOracle n)
    (s : native_String) (d : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (hWfD : __smtx_type_wf_rec (SmtType.Datatype s d)
        (SmtType.Datatype s d) = true)
    (hNC : __smtx_type_names_consistent (SmtType.Datatype s d) = true)
    (hDInf : __smtx_is_finite_datatype d = false)
    (TU : SmtType)
    (hFieldNC : __smtx_type_names_consistent_rec d TU = true)
    (hFieldEmb : RootEmbeddedTy d TU)
    (hTUInf : __smtx_is_finite_type TU = false)
    (hFInh : native_inhabited_type (__smtx_type_substitute s d TU) = true)
    (hFWf : __smtx_type_wf_rec (__smtx_type_substitute s d TU) TU = true) :
    ∃ x : SmtValue,
      __smtx_typeof_value x = __smtx_type_substitute s d TU ∧
        __smtx_value_canonical_bool x = true ∧ n ≤ sizeOf x := by
  cases TU with
  | Bool => simp [__smtx_is_finite_type] at hTUInf
  | BitVec w => simp [__smtx_is_finite_type] at hTUInf
  | Char => simp [__smtx_is_finite_type] at hTUInf
  | None =>
      simp [__smtx_type_substitute, native_inhabited_type, native_Teq,
        native_not, native_and, __smtx_type_default, __smtx_type_default_rec,
        __smtx_typeof_value] at hFInh
  | RegLan =>
      simp [__smtx_type_wf_rec] at hFWf
  | FunType A B =>
      simp [__smtx_type_wf_rec] at hFWf
  | DtcAppType A B =>
      simp [__smtx_type_wf_rec] at hFWf
  | TypeRef r =>
      cases hs : native_streq s r
      · simp [__smtx_type_substitute, native_ite, hs, native_inhabited_type,
          native_Teq, native_not, native_and, __smtx_type_default,
          __smtx_type_default_rec, __smtx_typeof_value] at hFInh
      · have hSub :
            __smtx_type_substitute s d (SmtType.TypeRef r) =
              SmtType.Datatype s d := by
          simp [__smtx_type_substitute, native_ite, hs]
        rw [hSub]
        exact hOracle s d hInh hWfD hDInf
  | Int =>
      simpa [__smtx_type_substitute] using
        closed_infinite_large_witness_from_oracle n hOracle SmtType.Int
          (by simpa [__smtx_type_substitute] using hFInh)
          (by simpa [__smtx_type_substitute] using hFWf)
          (by simp [__smtx_is_finite_type])
  | Real =>
      simpa [__smtx_type_substitute] using
        closed_infinite_large_witness_from_oracle n hOracle SmtType.Real
          (by simpa [__smtx_type_substitute] using hFInh)
          (by simpa [__smtx_type_substitute] using hFWf)
          (by simp [__smtx_is_finite_type])
  | USort u =>
      simpa [__smtx_type_substitute] using
        closed_infinite_large_witness_from_oracle n hOracle (SmtType.USort u)
          (by simpa [__smtx_type_substitute] using hFInh)
          (by simpa [__smtx_type_substitute] using hFWf)
          (by simp [__smtx_is_finite_type])
  | Seq U =>
      simpa [__smtx_type_substitute] using
        closed_infinite_large_witness_from_oracle n hOracle (SmtType.Seq U)
          (by simpa [__smtx_type_substitute] using hFInh)
          (by simpa [__smtx_type_substitute] using hFWf)
          (by simp [__smtx_is_finite_type])
  | Set A =>
      simpa [__smtx_type_substitute] using
        closed_infinite_large_witness_from_oracle n hOracle (SmtType.Set A)
          (by simpa [__smtx_type_substitute] using hFInh)
          (by simpa [__smtx_type_substitute] using hFWf)
          (by simpa [__smtx_is_finite_type] using hTUInf)
  | Map A B =>
      simpa [__smtx_type_substitute] using
        closed_infinite_large_witness_from_oracle n hOracle (SmtType.Map A B)
          (by simpa [__smtx_type_substitute] using hFInh)
          (by simpa [__smtx_type_substitute] using hFWf)
          (by simpa [__smtx_is_finite_type] using hTUInf)
  | Datatype s2 d2 =>
      have hDiag := wf_diag_push s d hInh hWfD hNC s2 d2
        hFieldNC hFieldEmb hFInh hFWf
      have hSubInf :
          __smtx_is_finite_type
            (__smtx_type_substitute s d (SmtType.Datatype s2 d2)) = false :=
        type_substitute_infinite_of_current_infinite s d hDInf
          (SmtType.Datatype s2 d2) hTUInf
      cases hs : native_streq s s2 with
      | true =>
          have hSub :
              __smtx_type_substitute s d (SmtType.Datatype s2 d2) =
                SmtType.Datatype s2 d2 := by
            simp [__smtx_type_substitute, native_ite, hs]
          rw [hSub] at hDiag hSubInf hFInh ⊢
          exact hOracle s2 d2 hFInh hDiag
            (by simpa [__smtx_is_finite_type] using hSubInf)
      | false =>
          have hSub :
              __smtx_type_substitute s d (SmtType.Datatype s2 d2) =
                SmtType.Datatype s2
                  (__smtx_dt_substitute s (__smtx_dt_lift s2 d2 d) d2) := by
            simp [__smtx_type_substitute, native_ite, hs]
          rw [hSub] at hDiag hSubInf hFInh ⊢
          exact hOracle s2 _ hFInh hDiag
            (by simpa [__smtx_is_finite_type] using hSubInf)

/-- Fill the remaining fields of a constructor with defaults, preserving the
seed's size. -/
private theorem diag_pump_cons_defaults
    (s : native_String) (d : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s d) = true) :
    ∀ (cU : SmtDatatypeCons) (seed : SmtValue) (base : SmtType),
      __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s d cU) cU = true →
      __smtx_typeof_value seed =
        chainType (__smtx_dtc_substitute s d cU) base →
      __smtx_value_canonical_bool seed = true →
        ∃ v : SmtValue, __smtx_typeof_value v = base ∧
          __smtx_value_canonical_bool v = true ∧ sizeOf seed ≤ sizeOf v
  | SmtDatatypeCons.unit, seed, base, _hWf, hSeedTy, hSeedCan => by
      refine ⟨seed, ?_, hSeedCan, Nat.le_refl _⟩
      simpa [__smtx_dtc_substitute, chainType] using hSeedTy
  | SmtDatatypeCons.cons TU cU, seed, base, hWf, hSeedTy, hSeedCan => by
      have hWf' :
          __smtx_dt_cons_wf_rec
            (SmtDatatypeCons.cons (__smtx_type_substitute s d TU)
              (__smtx_dtc_substitute s d cU))
            (SmtDatatypeCons.cons TU cU) = true := by
        simpa [__smtx_dtc_substitute] using hWf
      have hTail : __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s d cU) cU = true :=
        dt_cons_wf_rec_tail_of_true hWf'
      have hSeedTy' :
          __smtx_typeof_value seed =
            chainType
              (SmtDatatypeCons.cons (__smtx_type_substitute s d TU)
                (__smtx_dtc_substitute s d cU)) base := by
        simpa [__smtx_dtc_substitute] using hSeedTy
      have hField :
          ∃ xd : SmtValue,
            __smtx_typeof_value xd = __smtx_type_substitute s d TU ∧
              __smtx_value_canonical_bool xd = true := by
        by_cases hSelf :
            native_Teq (__smtx_type_substitute s d TU)
              (SmtType.Datatype s d) = true
        · have hEq : __smtx_type_substitute s d TU = SmtType.Datatype s d := by
            simpa [native_Teq] using hSelf
          have hDef := type_default_typed_canonical_of_native_inhabited hInh
          exact ⟨__smtx_type_default (SmtType.Datatype s d),
            by rw [hEq]; exact hDef.1, hDef.2⟩
        · have hSelfF :
              native_Teq (__smtx_type_substitute s d TU)
                (SmtType.Datatype s d) = false := by
            cases h : native_Teq (__smtx_type_substitute s d TU)
                (SmtType.Datatype s d) <;> simp_all
          have hParts :=
            dt_cons_wf_subst_head_parts_of_nonself s d
              (T := TU) (c := cU) hWf hSelfF
          have hDef := type_default_typed_canonical_of_native_inhabited hParts.1
          exact ⟨__smtx_type_default (__smtx_type_substitute s d TU),
            hDef.1, hDef.2⟩
      rcases hField with ⟨xd, hxdTy, hxdCan⟩
      have hTFne : __smtx_type_substitute s d TU ≠ SmtType.None := by
        by_cases hSelf :
            native_Teq (__smtx_type_substitute s d TU)
              (SmtType.Datatype s d) = true
        · have hEq : __smtx_type_substitute s d TU = SmtType.Datatype s d := by
            simpa [native_Teq] using hSelf
          rw [hEq]
          exact fun h => SmtType.noConfusion h
        · have hSelfF :
              native_Teq (__smtx_type_substitute s d TU)
                (SmtType.Datatype s d) = false := by
            cases h : native_Teq (__smtx_type_substitute s d TU)
                (SmtType.Datatype s d) <;> simp_all
          exact ne_none_of_native_inhabited
            (dt_cons_wf_subst_head_parts_of_nonself s d
              (T := TU) (c := cU) hWf hSelfF).1
      have hApplyTy :
          __smtx_typeof_value (SmtValue.Apply seed xd) =
            chainType (__smtx_dtc_substitute s d cU) base :=
        apply_seed_typeof_chain hSeedTy' hxdTy hTFne
      have hApplyCan :
          __smtx_value_canonical_bool (SmtValue.Apply seed xd) = true := by
        simp [__smtx_value_canonical_bool, hSeedCan, hxdCan, native_and]
      rcases diag_pump_cons_defaults s d hInh cU (SmtValue.Apply seed xd)
          base hTail hApplyTy hApplyCan with ⟨v, hvTy, hvCan, hvSize⟩
      refine ⟨v, hvTy, hvCan, ?_⟩
      have : sizeOf seed < sizeOf (SmtValue.Apply seed xd) := by
        rw [show sizeOf (SmtValue.Apply seed xd) =
          1 + sizeOf seed + sizeOf xd by rfl]
        omega
      omega

/-- Walk a constructor with an infinite raw field: fill fields with defaults
until the first infinite field, fill that with an oracle-large value, then
defaults for the rest.  Produces a strictly-larger-than-`n` value. -/
private theorem diag_pump_cons_target
    (n : Nat) (hOracle : DiagOracle n)
    (s : native_String) (d : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (hWfD : __smtx_type_wf_rec (SmtType.Datatype s d)
        (SmtType.Datatype s d) = true)
    (hNC : __smtx_type_names_consistent (SmtType.Datatype s d) = true)
    (hDInf : __smtx_is_finite_datatype d = false) :
    ∀ (cU : SmtDatatypeCons) (seed : SmtValue) (base : SmtType),
      __smtx_dt_cons_names_consistent_rec d cU = true →
      RootEmbeddedDtc d cU →
      __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s d cU) cU = true →
      __smtx_typeof_value seed =
        chainType (__smtx_dtc_substitute s d cU) base →
      __smtx_value_canonical_bool seed = true →
      __smtx_is_finite_datatype_cons cU = false →
        ∃ v : SmtValue, __smtx_typeof_value v = base ∧
          __smtx_value_canonical_bool v = true ∧ n < sizeOf v
  | SmtDatatypeCons.unit, _seed, _base, _hCons, _hEmb, _hWf, _hSeedTy,
      _hSeedCan, hConsInf => by
      simp [__smtx_is_finite_datatype_cons] at hConsInf
  | SmtDatatypeCons.cons TU cU, seed, base, hCons, hEmb, hWf, hSeedTy,
      hSeedCan, hConsInf => by
      have hConsParts := namesConsDtc_parts d TU cU hCons
      have hEmbParts := RootEmbeddedDtc_parts d TU cU hEmb
      have hWf' :
          __smtx_dt_cons_wf_rec
            (SmtDatatypeCons.cons (__smtx_type_substitute s d TU)
              (__smtx_dtc_substitute s d cU))
            (SmtDatatypeCons.cons TU cU) = true := by
        simpa [__smtx_dtc_substitute] using hWf
      have hTail : __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s d cU) cU = true :=
        dt_cons_wf_rec_tail_of_true hWf'
      have hSeedTy' :
          __smtx_typeof_value seed =
            chainType
              (SmtDatatypeCons.cons (__smtx_type_substitute s d TU)
                (__smtx_dtc_substitute s d cU)) base := by
        simpa [__smtx_dtc_substitute] using hSeedTy
      cases hTU : __smtx_is_finite_type TU with
      | false =>
          -- the head is the designated infinite field
          have hField :
              ∃ x : SmtValue,
                __smtx_typeof_value x = __smtx_type_substitute s d TU ∧
                  __smtx_value_canonical_bool x = true ∧ n ≤ sizeOf x := by
            by_cases hSelf :
                native_Teq (__smtx_type_substitute s d TU)
                  (SmtType.Datatype s d) = true
            · have hEq :
                  __smtx_type_substitute s d TU = SmtType.Datatype s d := by
                simpa [native_Teq] using hSelf
              rw [hEq]
              exact hOracle s d hInh hWfD hDInf
            · have hSelfF :
                  native_Teq (__smtx_type_substitute s d TU)
                    (SmtType.Datatype s d) = false := by
                cases h : native_Teq (__smtx_type_substitute s d TU)
                    (SmtType.Datatype s d) <;> simp_all
              have hParts :=
                dt_cons_wf_subst_head_parts_of_nonself s d
                  (T := TU) (c := cU) hWf hSelfF
              exact diag_pump_field_large n hOracle s d hInh hWfD hNC hDInf
                TU hConsParts.1 hEmbParts.1 hTU hParts.1 hParts.2.1
          rcases hField with ⟨x, hxTy, hxCan, hxSize⟩
          have hTFne : __smtx_type_substitute s d TU ≠ SmtType.None := by
            by_cases hSelf :
                native_Teq (__smtx_type_substitute s d TU)
                  (SmtType.Datatype s d) = true
            · have hEq :
                  __smtx_type_substitute s d TU = SmtType.Datatype s d := by
                simpa [native_Teq] using hSelf
              rw [hEq]
              exact fun h => SmtType.noConfusion h
            · have hSelfF :
                  native_Teq (__smtx_type_substitute s d TU)
                    (SmtType.Datatype s d) = false := by
                cases h : native_Teq (__smtx_type_substitute s d TU)
                    (SmtType.Datatype s d) <;> simp_all
              exact ne_none_of_native_inhabited
                (dt_cons_wf_subst_head_parts_of_nonself s d
                  (T := TU) (c := cU) hWf hSelfF).1
          have hApplyTy :
              __smtx_typeof_value (SmtValue.Apply seed x) =
                chainType (__smtx_dtc_substitute s d cU) base :=
            apply_seed_typeof_chain hSeedTy' hxTy hTFne
          have hApplyCan :
              __smtx_value_canonical_bool (SmtValue.Apply seed x) = true := by
            simp [__smtx_value_canonical_bool, hSeedCan, hxCan, native_and]
          rcases diag_pump_cons_defaults s d hInh cU (SmtValue.Apply seed x)
              base hTail hApplyTy hApplyCan with ⟨v, hvTy, hvCan, hvSize⟩
          refine ⟨v, hvTy, hvCan, ?_⟩
          have : n < sizeOf (SmtValue.Apply seed x) := by
            rw [show sizeOf (SmtValue.Apply seed x) =
              1 + sizeOf seed + sizeOf x by rfl]
            omega
          omega
      | true =>
          -- the head is finite; the tail must contain the infinite field
          have hTailInf : __smtx_is_finite_datatype_cons cU = false := by
            cases hcU : __smtx_is_finite_datatype_cons cU <;>
              simp_all [__smtx_is_finite_datatype_cons, native_and]
          have hField :
              ∃ xd : SmtValue,
                __smtx_typeof_value xd = __smtx_type_substitute s d TU ∧
                  __smtx_value_canonical_bool xd = true := by
            by_cases hSelf :
                native_Teq (__smtx_type_substitute s d TU)
                  (SmtType.Datatype s d) = true
            · have hEq :
                  __smtx_type_substitute s d TU = SmtType.Datatype s d := by
                simpa [native_Teq] using hSelf
              have hDef := type_default_typed_canonical_of_native_inhabited hInh
              exact ⟨__smtx_type_default (SmtType.Datatype s d),
                by rw [hEq]; exact hDef.1, hDef.2⟩
            · have hSelfF :
                  native_Teq (__smtx_type_substitute s d TU)
                    (SmtType.Datatype s d) = false := by
                cases h : native_Teq (__smtx_type_substitute s d TU)
                    (SmtType.Datatype s d) <;> simp_all
              have hParts :=
                dt_cons_wf_subst_head_parts_of_nonself s d
                  (T := TU) (c := cU) hWf hSelfF
              have hDef :=
                type_default_typed_canonical_of_native_inhabited hParts.1
              exact ⟨__smtx_type_default (__smtx_type_substitute s d TU),
                hDef.1, hDef.2⟩
          rcases hField with ⟨xd, hxdTy, hxdCan⟩
          have hTFne : __smtx_type_substitute s d TU ≠ SmtType.None := by
            by_cases hSelf :
                native_Teq (__smtx_type_substitute s d TU)
                  (SmtType.Datatype s d) = true
            · have hEq :
                  __smtx_type_substitute s d TU = SmtType.Datatype s d := by
                simpa [native_Teq] using hSelf
              rw [hEq]
              exact fun h => SmtType.noConfusion h
            · have hSelfF :
                  native_Teq (__smtx_type_substitute s d TU)
                    (SmtType.Datatype s d) = false := by
                cases h : native_Teq (__smtx_type_substitute s d TU)
                    (SmtType.Datatype s d) <;> simp_all
              exact ne_none_of_native_inhabited
                (dt_cons_wf_subst_head_parts_of_nonself s d
                  (T := TU) (c := cU) hWf hSelfF).1
          have hApplyTy :
              __smtx_typeof_value (SmtValue.Apply seed xd) =
                chainType (__smtx_dtc_substitute s d cU) base :=
            apply_seed_typeof_chain hSeedTy' hxdTy hTFne
          have hApplyCan :
              __smtx_value_canonical_bool (SmtValue.Apply seed xd) = true := by
            simp [__smtx_value_canonical_bool, hSeedCan, hxdCan, native_and]
          exact diag_pump_cons_target n hOracle s d hInh hWfD hNC hDInf cU
            (SmtValue.Apply seed xd) base hConsParts.2 hEmbParts.2 hTail
            hApplyTy hApplyCan hTailInf
  termination_by cU _ _ _ _ _ _ _ _ => sizeOf cU
  decreasing_by all_goals (try simp_wf); all_goals omega

private theorem diag_typeof_dtcons_drop
    {s : native_String} {d : SmtDatatype} {k : native_Nat}
    {cF : SmtDatatypeCons} {dRest : SmtDatatype}
    (hdrop : drop_cons (__smtx_dt_substitute s d d) k =
        SmtDatatype.sum cF dRest) :
    __smtx_typeof_value (SmtValue.DtCons s d k) =
      chainType cF (SmtType.Datatype s d) := by
  simp only [__smtx_typeof_value]
  exact drop_lemma (SmtType.Datatype s d)
    (__smtx_dt_substitute s d d) k cF dRest hdrop

/-- Walk the constructors of a diagonal entry, locating one with an infinite
raw field and building a value larger than `n` from it. -/
private theorem diag_pump_dt_walk
    (n : Nat) (hOracle : DiagOracle n)
    (s : native_String) (d : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (hWfD : __smtx_type_wf_rec (SmtType.Datatype s d)
        (SmtType.Datatype s d) = true)
    (hNC : __smtx_type_names_consistent (SmtType.Datatype s d) = true)
    (hDInf : __smtx_is_finite_datatype d = false) :
    ∀ (dSuf : SmtDatatype) (k : native_Nat),
      __smtx_dt_names_consistent_rec d dSuf = true →
      RootEmbeddedDt d dSuf →
      drop_cons (__smtx_dt_substitute s d d) k =
        __smtx_dt_substitute s d dSuf →
      __smtx_dt_wf_rec (__smtx_dt_substitute s d dSuf) dSuf = true →
      __smtx_is_finite_datatype dSuf = false →
        ∃ v : SmtValue, __smtx_typeof_value v = SmtType.Datatype s d ∧
          __smtx_value_canonical_bool v = true ∧ n < sizeOf v
  | SmtDatatype.null, _k, _hCons, _hEmb, _hDrop, _hWf, hInf => by
      simp [__smtx_is_finite_datatype] at hInf
  | SmtDatatype.sum c dTail, k, hCons, hEmb, hDrop, hWf, hInf => by
      have hConsParts := namesConsDt_parts d c dTail hCons
      have hEmbParts := RootEmbeddedDt_parts d c dTail hEmb
      cases hConsFin : __smtx_is_finite_datatype_cons c with
      | false =>
          have hConsWf :
              __smtx_dt_cons_wf_rec (__smtx_dtc_substitute s d c) c = true := by
            simpa [__smtx_dt_substitute] using dt_wf_cons_of_wf hWf
          have hDropCons :
              drop_cons (__smtx_dt_substitute s d d) k =
                SmtDatatype.sum (__smtx_dtc_substitute s d c)
                  (__smtx_dt_substitute s d dTail) := by
            simpa [__smtx_dt_substitute] using hDrop
          exact diag_pump_cons_target n hOracle s d hInh hWfD hNC hDInf c
            (SmtValue.DtCons s d k) (SmtType.Datatype s d)
            hConsParts.1 hEmbParts.1 hConsWf
            (diag_typeof_dtcons_drop (s := s) (d := d) (k := k)
              (cF := __smtx_dtc_substitute s d c)
              (dRest := __smtx_dt_substitute s d dTail) hDropCons)
            (by simp [__smtx_value_canonical_bool])
            hConsFin
      | true =>
          have hTailInf : __smtx_is_finite_datatype dTail = false := by
            rcases finite_datatype_sum_false_cases hInf with hHead | hTail
            · rw [hConsFin] at hHead
              simp at hHead
            · exact hTail
          have hTailNe : dTail ≠ SmtDatatype.null := by
            intro hEq
            subst dTail
            simp [__smtx_is_finite_datatype] at hTailInf
          have hTailWf :
              __smtx_dt_wf_rec (__smtx_dt_substitute s d dTail) dTail = true := by
            exact dt_wf_tail_of_sum_wf_of_tail_ne_null
              (cF := __smtx_dtc_substitute s d c) (cU := c)
              (dF := __smtx_dt_substitute s d dTail) (dU := dTail)
              hTailNe (by simpa [__smtx_dt_substitute] using hWf)
          have hDropTail :
              drop_cons (__smtx_dt_substitute s d d) (Nat.succ k) =
                __smtx_dt_substitute s d dTail := by
            rw [drop_cons_succ, hDrop]
            simp [__smtx_dt_substitute]
          exact diag_pump_dt_walk n hOracle s d hInh hWfD hNC hDInf dTail
            (Nat.succ k) hConsParts.2 hEmbParts.2 hDropTail hTailWf hTailInf
  termination_by dSuf _ _ _ _ _ _ => sizeOf dSuf
  decreasing_by all_goals (try simp_wf); all_goals omega

private theorem diag_oracle_succ (n : Nat) (hOracle : DiagOracle n) :
    DiagOracle (Nat.succ n) := by
  intro s d hInh hWfD hInf
  have hDtWf :
      __smtx_dt_wf_rec (__smtx_dt_substitute s d d) d = true := by
    simpa [__smtx_type_wf_rec] using hWfD
  rcases diag_pump_dt_walk n hOracle s d hInh hWfD hInf d 0
      (by simp [drop_cons_zero]) hDtWf hInf with ⟨v, hvTy, hvCan, hvSize⟩
  exact ⟨v, hvTy, hvCan, hvSize⟩

private theorem diag_oracle_all : ∀ n : Nat, DiagOracle n
  | 0 => diag_oracle_zero
  | Nat.succ n => diag_oracle_succ n (diag_oracle_all n)

/-- An inhabited, well-formed, infinite datatype has typed canonical
inhabitants of arbitrarily large size. -/
private theorem infinite_datatype_large_witness
    (N : Nat) (s : native_String) (d : SmtDatatype)
    (hInh : native_inhabited_type (SmtType.Datatype s d) = true)
    (hWf : __smtx_type_wf_rec (SmtType.Datatype s d)
        (SmtType.Datatype s d) = true)
    (hInf : __smtx_is_finite_datatype d = false) :
    ∃ i : SmtValue, __smtx_typeof_value i = SmtType.Datatype s d ∧
      __smtx_value_canonical_bool i = true ∧ N ≤ sizeOf i :=
  diag_oracle_all N s d hInh hWf hInf

/-- An inhabited, well-formed, infinite datatype has typed canonical
inhabitants avoiding any finite list. -/
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
        have h9 :
            ((native_inhabited_type T = true ∧ __smtx_type_wf_rec T T = true) ∧
              __smtx_type_names_consistent T = true) ∧
              ((native_inhabited_type U = true ∧ __smtx_type_wf_rec U U = true) ∧
                __smtx_type_names_consistent U = true) := by
          simpa [__smtx_type_wf_rec, native_and] using _hRec
        exact ⟨h9.1.1.1, h9.1.1.2, h9.2.1.1, h9.2.1.2⟩
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
        have h3 : (native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true) ∧
            __smtx_type_names_consistent T = true := by
          simpa [__smtx_type_wf_rec, native_and] using _hRec
        exact h3.1
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
        have h3 : (native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true) ∧
            __smtx_type_names_consistent T = true := by
          simpa [__smtx_type_wf_rec, native_and] using _hRec
        exact h3.1
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
          have h9 :
              ((native_inhabited_type T = true ∧ __smtx_type_wf_rec T T = true) ∧
                __smtx_type_names_consistent T = true) ∧
                ((native_inhabited_type U = true ∧ __smtx_type_wf_rec U U = true) ∧
                  __smtx_type_names_consistent U = true) := by
            simpa [__smtx_type_wf_rec, native_and] using _hRec
          exact ⟨h9.1.1.1, h9.1.1.2, h9.2.1.1, h9.2.1.2⟩
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
              have h9 :
                  ((native_inhabited_type T = true ∧ __smtx_type_wf_rec T T = true) ∧
                    __smtx_type_names_consistent T = true) ∧
                    ((native_inhabited_type U = true ∧ __smtx_type_wf_rec U U = true) ∧
                      __smtx_type_names_consistent U = true) := by
                simpa [__smtx_type_wf_rec, native_and] using _hRec
              exact ⟨h9.1.1.1, h9.1.1.2, h9.2.1.1, h9.2.1.2⟩
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
        have h3 : (native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true) ∧
            __smtx_type_names_consistent T = true := by
          simpa [__smtx_type_wf_rec, native_and] using _hRec
        exact h3.1
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
        have h3 : (native_inhabited_type T = true ∧
            __smtx_type_wf_rec T T = true) ∧
            __smtx_type_names_consistent T = true := by
          simpa [__smtx_type_wf_rec, native_and] using _hRec
        exact h3.1
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
