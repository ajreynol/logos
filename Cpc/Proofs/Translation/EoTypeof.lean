import Cpc.Proofs.Translation.Base

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

/-!
These lemmas isolate the EO-side `__eo_typeof` facts that are awkward to
reduce directly because `__eo_typeof` is compiled as an opaque definition.

They let the main translation theorem make progress on the direct constructor
cases while we continue filling in the EO typing story separately.
-/

/-- Computes `__smtx_typeof_guard` under a non-`None` premise. -/
theorem smtx_typeof_guard_of_non_none
    (T U : SmtType) (h : T ≠ SmtType.None) :
    __smtx_typeof_guard T U = U := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq] at h ⊢

/-- Simplifies EO-to-SMT type translation for `typeof_numeral`. -/
theorem eo_to_smt_type_typeof_numeral
    (n : native_Int) :
    __eo_to_smt_type (__eo_typeof (Term.Numeral n)) = SmtType.Int := by
  change __eo_to_smt_type Term.Int = SmtType.Int
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_rational`. -/
theorem eo_to_smt_type_typeof_rational
    (q : native_Rat) :
    __eo_to_smt_type (__eo_typeof (Term.Rational q)) = SmtType.Real := by
  change __eo_to_smt_type Term.Real = SmtType.Real
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_string`. -/
theorem eo_to_smt_type_typeof_string
    (s : native_String) :
    __eo_to_smt_type (__eo_typeof (Term.String s)) = SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (Term.Apply Term.Seq Term.Char) = SmtType.Seq SmtType.Char
  simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]

/-- Simplifies EO-to-SMT type translation for `typeof_binary`. -/
theorem eo_to_smt_type_typeof_binary
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __eo_to_smt_type (__eo_typeof (Term.Binary w n)) =
      SmtType.BitVec (native_int_to_nat w) := by
  change __eo_to_smt_type (Term.Apply Term.BitVec (Term.Numeral w)) =
    SmtType.BitVec (native_int_to_nat w)
  simp [__eo_to_smt_type, native_ite, hWidth]

/-- Simplifies EO-to-SMT type translation for `typeof_var`. -/
theorem eo_to_smt_type_typeof_var
    (s : native_String) (T : Term) :
    __eo_to_smt_type (__eo_typeof (Term.Var (Term.String s) T)) = __eo_to_smt_type T := by
  change __eo_to_smt_type T = __eo_to_smt_type T
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_uconst`. -/
theorem eo_to_smt_type_typeof_uconst
    (i : native_Nat) (T : Term) :
    __eo_to_smt_type (__eo_typeof (Term.UConst i T)) = __eo_to_smt_type T := by
  change __eo_to_smt_type T = __eo_to_smt_type T
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_var_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_var_of_smt_apply
    (x T : Term) (s : native_String) (A B : SmtType)
    (hT :
      __eo_to_smt_type T = SmtType.Map A B ∨
        __eo_to_smt_type T = SmtType.FunType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Var (Term.String s) T) x)) = B := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_uconst_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_uconst_of_smt_apply
    (x T : Term) (i : native_Nat) (A B : SmtType)
    (hT :
      __eo_to_smt_type T = SmtType.Map A B ∨
        __eo_to_smt_type T = SmtType.FunType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UConst i T) x)) = B := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_of_smt_apply
    (x f : Term) (A B : SmtType)
    (hF :
      __eo_to_smt_type (__eo_typeof f) = SmtType.Map A B ∨
        __eo_to_smt_type (__eo_typeof f) = SmtType.FunType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A) :
    __eo_to_smt_type (__eo_typeof (Term.Apply f x)) = B := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_dt_cons`. -/
theorem eo_to_smt_type_typeof_dt_cons
    (s : native_String) (d : Datatype) (i : native_Nat) :
    __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_dt_cons_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_dt_cons_of_smt_apply
    (x : Term) (s : native_String) (d : Datatype) (i : native_Nat) (A B : SmtType)
    (hHead :
      __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = SmtType.Map A B ∨
        __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) = SmtType.FunType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtCons s d i) x)) = B := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_dt_sel_of_smt_datatype`. -/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s (__eo_to_smt_datatype d)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_select_of_smt_map`. -/
theorem eo_to_smt_type_typeof_apply_apply_select_of_smt_map
    (x y : Term) (A B : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Map A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.select y) x)) = B := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_store_of_smt_map`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_store_of_smt_map
    (x y z : Term) (A B : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Map A B)
    (hy : __smtx_typeof (__eo_to_smt y) = A)
    (hx : __smtx_typeof (__eo_to_smt x) = B) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.store z) y) x)) =
      SmtType.Map A B := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_update_of_smt_dt_sel`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_update_of_smt_dt_sel
    (x y z : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat)
    (hz : __eo_to_smt z = SmtTerm.DtSel s d i j)
    (h :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.update z) y) x)) ≠
        SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.update z) y) x)) =
      SmtType.Datatype s d := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_tuple_update_of_smt_numeral_tuple`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_tuple_update_of_smt_numeral_tuple
    (x y z : Term) (d : SmtDatatype) (n : native_Int)
    (hy : __eo_to_smt_type (__eo_typeof y) = SmtType.Datatype "_at_Tuple" d)
    (hz : __eo_to_smt z = SmtTerm.Numeral n)
    (h :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.tuple_update z) y) x)) ≠
        SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.tuple_update z) y) x)) =
      SmtType.Datatype "_at_Tuple" d := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_seq_empty`. -/
theorem eo_to_smt_type_typeof_seq_empty
    (x : Term)
    (h : __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type x)) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.seq_empty x)) =
      __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type x)) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_set_empty`. -/
theorem eo_to_smt_type_typeof_set_empty
    (x : Term)
    (h : __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type x)) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.set_empty x)) =
      __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type x)) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_purify`. -/
theorem eo_to_smt_type_typeof_purify
    (x : Term) :
    __eo_to_smt_type (__eo_typeof (Term._at_purify x)) =
      __eo_to_smt_type (__eo_typeof x) := by
  change __eo_to_smt_type (__eo_typeof__at_purify (__eo_typeof x)) =
      __eo_to_smt_type (__eo_typeof x)
  cases h : __eo_typeof x <;> rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_purify_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_purify_of_smt_apply
    (x y : Term) (A B : SmtType)
    (hHead :
      __eo_to_smt_type (__eo_typeof y) = SmtType.Map A B ∨
        __eo_to_smt_type (__eo_typeof y) = SmtType.FunType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_purify y) x)) = B := by
  have hHead' :
      __eo_to_smt_type (__eo_typeof (Term._at_purify y)) = SmtType.Map A B ∨
        __eo_to_smt_type (__eo_typeof (Term._at_purify y)) = SmtType.FunType A B := by
    rw [eo_to_smt_type_typeof_purify]
    exact hHead
  simpa using
    eo_to_smt_type_typeof_apply_of_smt_apply x (Term._at_purify y) A B hHead' hx

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_array_deq_diff_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_at_array_deq_diff_of_smt_apply
    (x x1 x2 : Term) (A B : SmtType)
    (hHead :
      __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) = SmtType.Map A B ∨
        __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2)) = SmtType.FunType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_array_deq_diff x1 x2) x)) = B := by
  simpa using
    eo_to_smt_type_typeof_apply_of_smt_apply x (Term._at_array_deq_diff x1 x2) A B hHead hx

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_bvsize`. -/
theorem eo_to_smt_type_typeof_apply_at_bvsize
    (x : Term) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term._at_bvsize x)) = SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_not_of_bool`. -/
theorem eo_to_smt_type_typeof_apply_not_of_bool
    (x : Term)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.not x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_not (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_abs_of_int`. -/
theorem eo_to_smt_type_typeof_apply_abs_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.abs x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_abs (__eo_typeof x)) = SmtType.Int
  rw [hx]
  native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_len_of_seq`. -/
theorem eo_to_smt_type_typeof_apply_str_len_of_seq
    (x V : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq V) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_len x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_len (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_rev_of_seq`. -/
theorem eo_to_smt_type_typeof_apply_str_rev_of_seq
    (x V : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq V) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_rev x)) =
      SmtType.Seq (__eo_to_smt_type V) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_seq_unit_of_non_none`. -/
theorem eo_to_smt_type_typeof_apply_seq_unit_of_non_none
    (x : Term)
    (hx : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.seq_unit x)) =
      SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
  change __eo_to_smt_type (__eo_typeof_seq_unit (__eo_typeof x)) =
    SmtType.Seq (__eo_to_smt_type (__eo_typeof x))
  cases hTy : __eo_typeof x <;> simp [__eo_typeof_seq_unit, __eo_to_smt_type, hTy] at hx ⊢
  case Apply =>
    exact smtx_typeof_guard_of_non_none _ _ hx
  case DtcAppType a b =>
    cases hA : __eo_to_smt_type a <;> cases hB : __eo_to_smt_type b <;>
      simp [__smtx_typeof_guard, native_ite, native_Teq, hA, hB] at hx ⊢
  all_goals simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_set_singleton_of_non_none`. -/
theorem eo_to_smt_type_typeof_apply_set_singleton_of_non_none
    (x : Term)
    (hx : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.set_singleton x)) =
      SmtType.Set (__eo_to_smt_type (__eo_typeof x)) := by
  change __eo_to_smt_type (__eo_typeof_set_singleton (__eo_typeof x)) =
    SmtType.Set (__eo_to_smt_type (__eo_typeof x))
  cases hTy : __eo_typeof x <;> simp [__eo_typeof_set_singleton, __eo_to_smt_type, hTy] at hx ⊢
  case Apply =>
    exact smtx_typeof_guard_of_non_none _ _ hx
  case DtcAppType a b =>
    cases hA : __eo_to_smt_type a <;> cases hB : __eo_to_smt_type b <;>
      simp [__smtx_typeof_guard, native_ite, native_Teq, hA, hB] at hx ⊢
  all_goals simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_set_is_singleton_of_smt_set`. -/
theorem eo_to_smt_type_typeof_apply_set_is_singleton_of_smt_set
    (x : Term)
    (hx :
      __smtx_typeof (__eo_to_smt x) =
        SmtType.Set (__eo_to_smt_type (__eo_typeof (Term.Apply Term.set_choose x)))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.set_is_singleton x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_sets_deq_diff_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_at_sets_deq_diff_of_smt_apply
    (x x1 x2 : Term) (A B : SmtType)
    (hHead :
      __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) = SmtType.Map A B ∨
        __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2)) = SmtType.FunType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_sets_deq_diff x1 x2) x)) = B := by
  simpa using
    eo_to_smt_type_typeof_apply_of_smt_apply x (Term._at_sets_deq_diff x1 x2) A B hHead hx

/-- Simplifies EO-to-SMT type translation for `typeof_apply_to_real_of_int`. -/
theorem eo_to_smt_type_typeof_apply_to_real_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.to_real x)) = SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_to_real (__eo_typeof x)) = SmtType.Real
  rw [hx]
  native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_to_real_of_real`. -/
theorem eo_to_smt_type_typeof_apply_to_real_of_real
    (x : Term)
    (hx : __eo_typeof x = Term.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.to_real x)) = SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_to_real (__eo_typeof x)) = SmtType.Real
  rw [hx]
  native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_to_int_of_real`. -/
theorem eo_to_smt_type_typeof_apply_to_int_of_real
    (x : Term)
    (hx : __eo_typeof x = Term.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.to_int x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_to_int (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_int_pow2_of_int`. -/
theorem eo_to_smt_type_typeof_apply_int_pow2_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.int_pow2 x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_int_log2_of_int`. -/
theorem eo_to_smt_type_typeof_apply_int_log2_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.int_log2 x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_int_ispow2_of_int`. -/
theorem eo_to_smt_type_typeof_apply_int_ispow2_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.int_ispow2 x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_int_ispow2 (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_int_div_by_zero_of_int`. -/
theorem eo_to_smt_type_typeof_apply_at_int_div_by_zero_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term._at_int_div_by_zero x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_mod_by_zero_of_int`. -/
theorem eo_to_smt_type_typeof_apply_at_mod_by_zero_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term._at_mod_by_zero x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_div_by_zero_of_real`. -/
theorem eo_to_smt_type_typeof_apply_at_div_by_zero_of_real
    (x : Term)
    (hx : __eo_typeof x = Term.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term._at_div_by_zero x)) = SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof__at_div_by_zero (__eo_typeof x)) = SmtType.Real
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_is_int_of_real`. -/
theorem eo_to_smt_type_typeof_apply_is_int_of_real
    (x : Term)
    (hx : __eo_typeof x = Term.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.is_int x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_is_int (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_lower_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_lower_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_lower x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_to_lower (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_upper_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_upper_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_upper x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_to_lower (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_code_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_code_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_code x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_to_code (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_from_code_of_int`. -/
theorem eo_to_smt_type_typeof_apply_str_from_code_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_from_code x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_from_code (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_is_digit_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_is_digit_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_is_digit x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_is_digit (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_int_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_int_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_int x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_to_code (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_from_int_of_int`. -/
theorem eo_to_smt_type_typeof_apply_str_from_int_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_from_int x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_from_code (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_strings_stoi_non_digit_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_at_strings_stoi_non_digit_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term._at_strings_stoi_non_digit x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_to_code (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_at_strings_stoi_result_of_smt_seq_char_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_at_strings_stoi_result_of_smt_seq_char_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term._at_strings_stoi_result y) x)) =
      SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_re_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_re_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_re x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_str_to_re (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_mult_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_mult_of_reglan
    (x : Term)
    (hx : __eo_typeof x = Term.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.re_mult x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_plus_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_plus_of_reglan
    (x : Term)
    (hx : __eo_typeof x = Term.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.re_plus x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_opt_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_opt_of_reglan
    (x : Term)
    (hx : __eo_typeof x = Term.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.re_opt x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_comp_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_comp_of_reglan
    (x : Term)
    (hx : __eo_typeof x = Term.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.re_comp x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvnot_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvnot_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.bvnot x)) = SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvnot (__eo_typeof x)) = SmtType.BitVec w
  rw [hx]
  change __eo_to_smt_type (Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w))) =
    SmtType.BitVec w
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
    native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvneg_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvneg_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.bvneg x)) = SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvnot (__eo_typeof x)) = SmtType.BitVec w
  rw [hx]
  change __eo_to_smt_type (Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w))) =
    SmtType.BitVec w
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
    native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvredand_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvredand_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.bvredand x)) = SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvredand (__eo_typeof x)) = SmtType.BitVec 1
  rw [hx]
  change __eo_to_smt_type (Term.Apply Term.BitVec (Term.Numeral 1)) = SmtType.BitVec 1
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq, native_int_to_nat,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvredor_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvredor_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.bvredor x)) = SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvredand (__eo_typeof x)) = SmtType.BitVec 1
  rw [hx]
  change __eo_to_smt_type (Term.Apply Term.BitVec (Term.Numeral 1)) = SmtType.BitVec 1
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq, native_int_to_nat,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_ubv_to_int_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_ubv_to_int_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.ubv_to_int x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_sbv_to_int_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_sbv_to_int_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.sbv_to_int x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_contains_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_contains_of_smt_seq
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_contains y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_prefixof_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_prefixof_of_smt_seq
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_prefixof y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_suffixof_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_suffixof_of_smt_seq
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_suffixof y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_lt_of_smt_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_lt_of_smt_seq_char
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_lt y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_leq_of_smt_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_leq_of_smt_seq_char
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_leq y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_range_of_smt_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_range_of_smt_seq_char
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_range y) x)) =
      SmtType.RegLan := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_concat_of_smt_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_concat_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_concat y) x)) =
      SmtType.RegLan := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_inter_of_smt_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_inter_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_inter y) x)) =
      SmtType.RegLan := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_union_of_smt_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_union_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_union y) x)) =
      SmtType.RegLan := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_diff_of_smt_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_diff_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_diff y) x)) =
      SmtType.RegLan := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_in_re_of_smt_seq_char_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_in_re_of_smt_seq_char_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_in_re y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_seq_nth_of_smt_seq_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_seq_nth_of_smt_seq_int
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.seq_nth y) x)) = T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_or_of_smt_bool`. -/
theorem eo_to_smt_type_typeof_apply_apply_or_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.or y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_and_of_smt_bool`. -/
theorem eo_to_smt_type_typeof_apply_apply_and_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.and y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_imp_of_smt_bool`. -/
theorem eo_to_smt_type_typeof_apply_apply_imp_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.imp y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_xor_of_smt_bool`. -/
theorem eo_to_smt_type_typeof_apply_apply_xor_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.xor y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_eq_of_smt_same_non_none`. -/
theorem eo_to_smt_type_typeof_apply_apply_eq_of_smt_same_non_none
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.eq y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_distinct_of_smt_same_non_none`. -/
theorem eo_to_smt_type_typeof_apply_apply_distinct_of_smt_same_non_none
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.distinct y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_plus_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_plus_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.plus y) x)) = T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_neg_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_neg_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.neg y) x)) = T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_mult_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_mult_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.mult y) x)) = T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_lt_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_lt_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.lt y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_leq_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_leq_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.leq y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_gt_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_gt_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.gt y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_geq_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_geq_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.geq y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_div_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_div_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.div y) x)) = SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_mod_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_mod_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.mod y) x)) = SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_multmult_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_multmult_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.multmult y) x)) = SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_divisible_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_divisible_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.divisible y) x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_div_total_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_div_total_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.div_total y) x)) = SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_mod_total_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_mod_total_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.mod_total y) x)) = SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_multmult_total_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_multmult_total_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.multmult_total y) x)) =
      SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_qdiv_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_qdiv_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.qdiv y) x)) =
      SmtType.Real := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_qdiv_total_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_qdiv_total_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.qdiv_total y) x)) =
      SmtType.Real := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_concat_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_concat_of_smt_bitvec
    (x y : Term) (w1 w2 : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w1)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w2) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.concat y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvand_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvand_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvand y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvor_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvor_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvor y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvnand_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvnand_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvnand y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvnor_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvnor_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvnor y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvxor_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvxor_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvxor y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvxnor_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvxnor_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvxnor y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvcomp_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvcomp_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvcomp y) x)) =
      SmtType.BitVec 1 := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvadd_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvadd_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvadd y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvmul_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvmul_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvmul y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvudiv_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvudiv_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvudiv y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvurem_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvurem_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvurem y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsub_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsub_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsub y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsdiv_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsdiv_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsdiv y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsrem_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsrem_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsrem y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsmod_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsmod_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsmod y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvult_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvult_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvult y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvule_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvule_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvule y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvugt_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvugt_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvugt y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvuge_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvuge_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvuge y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvslt_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvslt_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvslt y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsle_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsle_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsle y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsgt_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsgt_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsgt y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsge_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsge_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsge y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvshl_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvshl_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvshl y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvlshr_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvlshr_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvlshr y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvashr_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvashr_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvashr y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvuaddo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvuaddo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvuaddo y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsaddo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsaddo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsaddo y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvumulo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvumulo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvumulo y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsmulo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsmulo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsmulo y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvusubo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvusubo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvusubo y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvssubo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvssubo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvssubo y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsdivo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsdivo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsdivo y) x)) =
      SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_repeat_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_repeat_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 1 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.repeat y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zmult i (native_nat_to_int w))) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_zero_extend_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_zero_extend_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.zero_extend y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_sign_extend_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_sign_extend_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.sign_extend y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_rotate_left_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_rotate_left_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.rotate_left y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_rotate_right_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_rotate_right_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.rotate_right y) x)) =
      SmtType.BitVec w := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_int_to_bv_of_smt_numeral_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_int_to_bv_of_smt_numeral_int
    (x y : Term) (i : native_Int)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.int_to_bv y) x)) =
      SmtType.BitVec (native_int_to_nat i) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvnego_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvnego_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.bvnego x)) = SmtType.Bool := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_concat_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_concat_of_smt_seq
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_concat y) x)) =
      SmtType.Seq T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_at_of_smt_seq_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_at_of_smt_seq_int
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_at y) x)) =
      SmtType.Seq T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_extract_of_smt_numeral_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_extract_of_smt_numeral_numeral_bitvec
    (x y z : Term) (i j : native_Int) (w : native_Nat)
    (hz : __eo_to_smt z = SmtTerm.Numeral i)
    (hy : __eo_to_smt y = SmtTerm.Numeral j)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hj0 : native_zleq 0 j = true)
    (hji : native_zleq j i = true)
    (hiw : native_zlt i (native_nat_to_int w) = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.extract z) y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus (native_zplus i (native_zneg j)) 1)) := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_substr_of_smt_seq_int_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_substr_of_smt_seq_int_int
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.str_substr z) y) x)) =
      SmtType.Seq T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_indexof_of_smt_seq_seq_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_indexof_of_smt_seq_seq_int
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.str_indexof z) y) x)) =
      SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_update_of_smt_seq_int_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_update_of_smt_seq_int_seq
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.str_update z) y) x)) =
      SmtType.Seq T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_replace_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_smt_seq
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.str_replace z) y) x)) =
      SmtType.Seq T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_replace_all_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_smt_seq
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.str_replace_all z) y) x)) =
      SmtType.Seq T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_replace_re_of_smt_seq_char_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_of_smt_seq_char_reglan
    (x y z : Term)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re z) y) x)) =
      SmtType.Seq SmtType.Char := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_replace_re_all_of_smt_seq_char_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_all_of_smt_seq_char_reglan
    (x y z : Term)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.str_replace_re_all z) y) x)) =
      SmtType.Seq SmtType.Char := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_indexof_re_of_smt_seq_char_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_indexof_re_of_smt_seq_char_reglan
    (x y z : Term)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.str_indexof_re z) y) x)) =
      SmtType.Int := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_re_loop_of_smt_numeral_numeral_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_re_loop_of_smt_numeral_numeral_reglan
    (x y z : Term) (n1 n2 : native_Int)
    (hz : __eo_to_smt z = SmtTerm.Numeral n1)
    (hy : __eo_to_smt y = SmtTerm.Numeral n2)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hn1 : native_zleq 0 n1)
    (hn2 : native_zleq 0 n2) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.re_loop z) y) x)) =
      SmtType.RegLan := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_bvite_of_smt_bitvec1_same_non_none`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_bvite_of_smt_bitvec1_same_non_none
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec 1)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.bvite z) y) x)) = T := by
  sorry

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_ite_of_smt_bool_same_non_none`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_ite_of_smt_bool_same_non_none
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Bool)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply Term.ite z) y) x)) = T := by
  sorry

end TranslationProofs
