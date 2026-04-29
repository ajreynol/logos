import Cpc.Proofs.Translation.Base
import Cpc.Proofs.Translation.Datatypes
import Cpc.Proofs.Translation.Inversions
import Cpc.Proofs.TypePreservation.BitVecPrep
import Cpc.Proofs.TypePreservation.Common
import Cpc.Proofs.TypePreservation.CoreArith
import Cpc.Proofs.TypePreservation.Datatypes
import Cpc.Proofs.TypePreservation.SeqStringRegex

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

/-!
These lemmas isolate EO-side `__eo_typeof` facts that are awkward to reduce
directly inside the translation proofs.

They let the main translation theorem make progress on the direct constructor
cases while we continue filling in the EO typing story separately.
-/

/-- Computes `__smtx_typeof_guard` under a non-`None` premise. -/
theorem smtx_typeof_guard_of_non_none
    (T U : SmtType) (h : T ≠ SmtType.None) :
    __smtx_typeof_guard T U = U := by
  cases T <;> simp [__smtx_typeof_guard, native_ite, native_Teq] at h ⊢

/-- A translated EO type cannot be non-`None` if the EO term is `Stuck`. -/
theorem eo_term_ne_stuck_of_smt_type_non_none
    (T : Term) (h : __eo_to_smt_type T ≠ SmtType.None) :
    T ≠ Term.Stuck := by
  intro hStuck
  subst hStuck
  exact h rfl

/-- Reduces `__eo_requires` when the compared EO types are definitionally equal. -/
theorem eo_requires_self_of_non_stuck
    (T U : Term) (h : T ≠ Term.Stuck) :
    __eo_requires T T U = U := by
  simp [__eo_requires, native_ite, native_not, native_teq, h]

/-- Computes EO self-equality for non-`Stuck` terms. -/
theorem eo_eq_self_of_non_stuck
    (T : Term) (h : T ≠ Term.Stuck) :
    __eo_eq T T = Term.Boolean true := by
  cases T <;> simp [__eo_eq, native_teq] at h ⊢

/-- Reduces `__eo_requires` after discharging an EO self-equality check. -/
theorem eo_requires_eo_eq_self_of_non_stuck
    (T U : Term) (h : T ≠ Term.Stuck) :
    __eo_requires (__eo_eq T T) (Term.Boolean true) U = U := by
  rw [eo_eq_self_of_non_stuck T h]
  simpa using eo_requires_self_of_non_stuck (Term.Boolean true) U (by simp)

/-- Reduces `__eo_requires` after discharging two EO self-equality checks. -/
theorem eo_requires_eo_and_eq_self_of_non_stuck
    (T U V : Term) (hT : T ≠ Term.Stuck) (hU : U ≠ Term.Stuck) :
    __eo_requires (__eo_and (__eo_eq T T) (__eo_eq U U)) (Term.Boolean true) V = V := by
  rw [eo_eq_self_of_non_stuck T hT, eo_eq_self_of_non_stuck U hU]
  simpa [__eo_and] using eo_requires_self_of_non_stuck (Term.Boolean true) V (by simp)

/--
Temporary internal bridge mirroring the lightweight public translation layer.

This stays private so we can discharge SMT-hypothesis wrapper lemmas without
threading the public stub through imports and colliding with the eventual full
theorem name.
-/
private axiom eo_to_smt_typeof_matches_translation_bridge
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt t) = __eo_to_smt_type (__eo_typeof t)

/-- Recovers the EO translated type from an SMT typing equality. -/
private theorem eo_to_smt_type_typeof_of_smt_type
    (t : Term) {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof t) = T := by
  have hNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [h]
    exact hT
  exact (eo_to_smt_typeof_matches_translation_bridge t hNN).symm.trans h

/-- A translated SMT `Bool` recovers EO `Bool`. -/
private theorem eo_typeof_eq_bool_of_smt_bool
    (t : Term)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Bool) :
    __eo_typeof t = Term.Bool := by
  exact eo_to_smt_type_eq_bool (eo_to_smt_type_typeof_of_smt_type t h (by simp))

/-- A translated SMT `Int` recovers EO `Int`. -/
private theorem eo_typeof_eq_int_of_smt_int
    (t : Term)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Int) :
    __eo_typeof t = Term.UOp UserOp.Int := by
  exact eo_to_smt_type_eq_int (eo_to_smt_type_typeof_of_smt_type t h (by simp))

/-- A translated SMT `Real` recovers EO `Real`. -/
private theorem eo_typeof_eq_real_of_smt_real
    (t : Term)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Real) :
    __eo_typeof t = Term.UOp UserOp.Real := by
  exact eo_to_smt_type_eq_real (eo_to_smt_type_typeof_of_smt_type t h (by simp))

/-- A translated SMT regular language recovers EO `RegLan`. -/
private theorem eo_typeof_eq_reglan_of_smt_reglan
    (t : Term)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.RegLan) :
    __eo_typeof t = Term.UOp UserOp.RegLan := by
  exact eo_to_smt_type_eq_reglan (eo_to_smt_type_typeof_of_smt_type t h (by simp))

/-- A translated SMT `Seq Char` recovers EO `Seq Char`. -/
private theorem eo_typeof_eq_seq_char_of_smt_seq_char
    (t : Term)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Seq SmtType.Char) :
    __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char) := by
  exact eo_to_smt_type_eq_seq_char (eo_to_smt_type_typeof_of_smt_type t h (by simp))

/-- A translated SMT sequence recovers EO `Seq` with the same translated element type. -/
private theorem eo_typeof_eq_seq_of_smt_seq
    (t : Term) {T : SmtType}
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T) :
    ∃ U, __eo_typeof t = Term.Apply (Term.UOp UserOp.Seq) U ∧ __eo_to_smt_type U = T := by
  exact eo_to_smt_type_eq_seq (eo_to_smt_type_typeof_of_smt_type t h (by simp))

/-- A translated SMT bitvector recovers EO `BitVec`. -/
private theorem eo_typeof_eq_bitvec_of_smt_bitvec
    (t : Term) (w : native_Nat)
    (h : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w) :
    __eo_typeof t = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w)) := by
  exact eo_to_smt_type_eq_bitvec (eo_to_smt_type_typeof_of_smt_type t h (by simp))

/-- A translated SMT numeral always recovers EO `Int`. -/
private theorem eo_typeof_eq_int_of_smt_numeral
    (t : Term) (n : native_Int)
    (h : __eo_to_smt t = SmtTerm.Numeral n) :
    __eo_typeof t = Term.UOp UserOp.Int := by
  exact eo_typeof_eq_int_of_smt_int t (by rw [h]; simp [__smtx_typeof])

/-- Computes the type of the one-bit literal used by `bvite`. -/
private theorem typeof_binary_one_eq :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 := by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    unfold __smtx_typeof
    simp [native_ite, SmtEval.native_and, native_zleq, native_zeq, native_mod_total,
      native_int_pow2]
    native_decide
  simpa using smtx_typeof_binary_of_non_none 1 1 hNN

/-- Computes `__smtx_typeof_apply` for function-like apply heads. -/
private theorem smtx_typeof_apply_of_head_cases
    {F X A B : SmtType}
    (hHead : F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B)
    (hX : X = A)
    (hA : A ≠ SmtType.None) :
    __smtx_typeof_apply F X = B := by
  rcases hHead with hHead | hHead
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq, hA]

/-- Rewrites `generic_apply_type` for heads that are not datatype selectors/testers. -/
private theorem generic_apply_type_of_non_special_head
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  simpa using
    (__smtx_typeof.eq_140 f x
      (by
        intro s d i j h
        exact hSel s d i j h)
      (by
        intro s d i h
        exact hTester s d i h))

/-- EO bitvector types at natural widths translate back to the matching SMT width. -/
private theorem eo_to_smt_type_bitvec_nat
    (w : native_Nat) :
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) =
      SmtType.BitVec w := by
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
    native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_numeral`. -/
theorem eo_to_smt_type_typeof_numeral
    (n : native_Int) :
    __eo_to_smt_type (__eo_typeof (Term.Numeral n)) = SmtType.Int := by
  change __eo_to_smt_type (Term.UOp UserOp.Int) = SmtType.Int
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_rational`. -/
theorem eo_to_smt_type_typeof_rational
    (q : native_Rat) :
    __eo_to_smt_type (__eo_typeof (Term.Rational q)) = SmtType.Real := by
  change __eo_to_smt_type (Term.UOp UserOp.Real) = SmtType.Real
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_string`. -/
theorem eo_to_smt_type_typeof_string
    (s : native_String) :
    __eo_to_smt_type (__eo_typeof (Term.String s)) = SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) = SmtType.Seq SmtType.Char
  simp [__eo_to_smt_type, __smtx_typeof_guard, native_ite, native_Teq]

/-- Simplifies EO-to-SMT type translation for `typeof_binary`. -/
theorem eo_to_smt_type_typeof_binary
    (w n : native_Int)
    (hWidth : native_zleq 0 w = true) :
    __eo_to_smt_type (__eo_typeof (Term.Binary w n)) =
      SmtType.BitVec (native_int_to_nat w) := by
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral w)) =
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
    (hHead :
      __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) = SmtType.FunType A B ∨
        __smtx_typeof (SmtTerm.Var s (__eo_to_smt_type T)) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hA : A ≠ SmtType.None)
    (hB : B ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Var (Term.String s) T) x)) = B := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x) =
        SmtTerm.Apply (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x) := by
    have hGeneric :
        __eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x) =
          SmtTerm.Apply (__eo_to_smt (Term.Var (Term.String s) T)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    simpa [eo_to_smt_var] using hGeneric
  have hGeneric :
      generic_apply_type (SmtTerm.Var s (__eo_to_smt_type T)) (__eo_to_smt x) := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s' d i j h; cases h)
      (by intro s' d i h; cases h)
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Var (Term.String s) T) x)) = B := by
    rw [hTranslate, hGeneric]
    exact smtx_typeof_apply_of_head_cases hHead hx hA
  exact eo_to_smt_type_typeof_of_smt_type _ hSmt hB

/-- Simplifies EO-to-SMT type translation for `typeof_apply_uconst_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_uconst_of_smt_apply
    (x T : Term) (i : native_Nat) (A B : SmtType)
    (hHead :
      __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) =
          SmtType.FunType A B ∨
        __smtx_typeof (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) =
          SmtType.DtcAppType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hA : A ≠ SmtType.None)
    (hB : B ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UConst i T) x)) = B := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.UConst i T) x) =
        SmtTerm.Apply (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) (__eo_to_smt x) := by
    have hGeneric :
        __eo_to_smt (Term.Apply (Term.UConst i T) x) =
          SmtTerm.Apply (__eo_to_smt (Term.UConst i T)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    simpa [eo_to_smt_uconst] using hGeneric
  have hGeneric :
      generic_apply_type (SmtTerm.UConst (native_uconst_id i) (__eo_to_smt_type T)) (__eo_to_smt x) := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s' d i' j h; cases h)
      (by intro s' d i' h; cases h)
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UConst i T) x)) = B := by
    rw [hTranslate, hGeneric]
    exact smtx_typeof_apply_of_head_cases hHead hx hA
  exact eo_to_smt_type_typeof_of_smt_type _ hSmt hB

/-- Simplifies EO-to-SMT type translation for `typeof_apply_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_of_smt_apply
    (x f : Term) (A B : SmtType)
    (hHead :
      __smtx_typeof (__eo_to_smt f) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt f) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hTranslate :
      __eo_to_smt (Term.Apply f x) = SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hGeneric : generic_apply_type (__eo_to_smt f) (__eo_to_smt x))
    (hA : A ≠ SmtType.None)
    (hB : B ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply f x)) = B := by
  have hSmt : __smtx_typeof (__eo_to_smt (Term.Apply f x)) = B := by
    rw [hTranslate, hGeneric]
    exact smtx_typeof_apply_of_head_cases hHead hx hA
  exact eo_to_smt_type_typeof_of_smt_type _ hSmt hB

/-- Stronger EO-side helper for successful function-like application. -/
theorem eo_to_smt_type_typeof_apply_of_fun_like
    (x f T U : Term)
    (hApply :
      __eo_typeof (Term.Apply f x) = __eo_typeof_apply (__eo_typeof f) (__eo_typeof x))
    (hf :
      __eo_typeof f = Term.Apply (Term.Apply Term.FunType T) U ∨
        __eo_typeof f = Term.DtcAppType T U)
    (hx : __eo_typeof x = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply f x)) = __eo_to_smt_type U := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hApply]
  rcases hf with hFun | hDtc
  · rw [hFun, hx]
    simp [__eo_typeof_apply, eo_requires_self_of_non_stuck T U hTNS]
  · rw [hDtc, hx]
    simp [__eo_typeof_apply, eo_requires_self_of_non_stuck T U hTNS]

/-- Stronger EO-side helper for `typeof_apply_var`. -/
theorem eo_to_smt_type_typeof_apply_var_of_fun_like
    (x T U V : Term) (s : native_String)
    (hT :
      T = Term.Apply (Term.Apply Term.FunType U) V ∨
        T = Term.DtcAppType U V)
    (hx : __eo_typeof x = U)
    (hU : __eo_to_smt_type U ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Var (Term.String s) T) x)) =
      __eo_to_smt_type V := by
  apply eo_to_smt_type_typeof_apply_of_fun_like
    (f := Term.Var (Term.String s) T) (T := U) (U := V)
  · change __eo_typeof (Term.Apply (Term.Var (Term.String s) T) x) =
      __eo_typeof_apply T (__eo_typeof x)
    rfl
  · change T = Term.Apply (Term.Apply Term.FunType U) V ∨ T = Term.DtcAppType U V
    exact hT
  · exact hx
  · exact hU

/-- Stronger EO-side helper for `typeof_apply_uconst`. -/
theorem eo_to_smt_type_typeof_apply_uconst_of_fun_like
    (x T U V : Term) (i : native_Nat)
    (hT :
      T = Term.Apply (Term.Apply Term.FunType U) V ∨
        T = Term.DtcAppType U V)
    (hx : __eo_typeof x = U)
    (hU : __eo_to_smt_type U ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UConst i T) x)) =
      __eo_to_smt_type V := by
  apply eo_to_smt_type_typeof_apply_of_fun_like
    (f := Term.UConst i T) (T := U) (U := V)
  · change __eo_typeof (Term.Apply (Term.UConst i T) x) =
      __eo_typeof_apply T (__eo_typeof x)
    rfl
  · change T = Term.Apply (Term.Apply Term.FunType U) V ∨ T = Term.DtcAppType U V
    exact hT
  · exact hx
  · exact hU

/-- Temporary internal bridge for `typeof_dt_cons`. -/
axiom eo_to_smt_type_typeof_dt_cons
    (s : native_String) (d : Datatype) (i : native_Nat) :
    __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_dt_cons_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_dt_cons_of_smt_apply
    (x : Term) (s : native_String) (d : Datatype) (i : native_Nat) (A B : SmtType)
    (hHead :
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) = SmtType.FunType A B ∨
        __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hA : A ≠ SmtType.None)
    (hB : B ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtCons s d i) x)) = B := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
        SmtTerm.Apply (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) (__eo_to_smt x) := by
    have hGeneric :
        __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
          SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    simpa [eo_to_smt_term_dt_cons] using hGeneric
  have hGeneric :
      generic_apply_type (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) (__eo_to_smt x) := by
    exact generic_apply_type_of_non_special_head _ _
      (by intro s' d' i' j h; cases h)
      (by intro s' d' i' h; cases h)
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtCons s d i) x)) = B := by
    rw [hTranslate, hGeneric]
    exact smtx_typeof_apply_of_head_cases hHead hx hA
  exact eo_to_smt_type_typeof_of_smt_type _ hSmt hB

/-- Stronger EO-side helper for `typeof_apply_dt_cons`. -/
theorem eo_to_smt_type_typeof_apply_dt_cons_of_fun_like
    (x U V : Term) (s : native_String) (d : Datatype) (i : native_Nat)
    (hHead :
      __eo_typeof (Term.DtCons s d i) = Term.Apply (Term.Apply Term.FunType U) V ∨
        __eo_typeof (Term.DtCons s d i) = Term.DtcAppType U V)
    (hx : __eo_typeof x = U)
    (hU : __eo_to_smt_type U ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtCons s d i) x)) =
      __eo_to_smt_type V := by
  apply eo_to_smt_type_typeof_apply_of_fun_like
    (f := Term.DtCons s d i) (T := U) (U := V)
  · change __eo_typeof (Term.Apply (Term.DtCons s d i) x) =
      __eo_typeof_apply (__eo_typeof (Term.DtCons s d i)) (__eo_typeof x)
    rfl
  · exact hHead
  · exact hx
  · exact hU

/-- Simplifies EO-to-SMT type translation for `typeof_apply_dt_sel_of_smt_datatype`. -/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_smt_datatype
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Datatype s (__eo_to_smt_datatype d))
    (hApplyNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) (__eo_to_smt x))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
  have hTranslate :
      __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
        SmtTerm.Apply (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j) (__eo_to_smt x) := by
    have hGeneric :
        __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
          SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) := by
      rw [__eo_to_smt.eq_def]
    simpa [eo_to_smt_term_dt_sel] using hGeneric
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) =
        __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j := by
    rw [hTranslate]
    exact dt_sel_term_typeof_of_non_none hApplyNN
  have hApplyNN' :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) x)) ≠ SmtType.None := by
    simpa [hTranslate] using hApplyNN
  have hRet :
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j ≠ SmtType.None := by
    rw [hSmt] at hApplyNN'
    exact hApplyNN'
  exact eo_to_smt_type_typeof_of_smt_type _ hSmt hRet

/-- Stronger EO-side helper for `typeof_apply_dt_sel`. -/
theorem eo_to_smt_type_typeof_apply_dt_sel_of_datatype_type
    (x : Term) (s : native_String) (d : Datatype) (i j : native_Nat)
    (hx : __eo_typeof x = Term.DatatypeType s d) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.DtSel s d i j) x)) =
      __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) := by
  have hDt : Term.DatatypeType s d ≠ Term.Stuck := by
    intro hStuck
    cases hStuck
  have hReq :
      __eo_requires (Term.DatatypeType s d) (Term.DatatypeType s d)
        (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) =
      __eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j :=
    eo_requires_self_of_non_stuck (Term.DatatypeType s d)
      (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) hDt
  change
    __eo_to_smt_type
        (__eo_typeof_apply (__eo_typeof (Term.DtSel s d i j)) (__eo_typeof x)) =
      __eo_to_smt_type (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j)
  rw [hx]
  simpa [__eo_typeof_apply, hDt] using congrArg __eo_to_smt_type hReq

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_select_of_smt_map`. -/
theorem eo_to_smt_type_typeof_apply_apply_select_of_smt_map
    (x y : Term) (A B : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Map A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hApplyNN : term_has_non_none_type (SmtTerm.select (__eo_to_smt y) (__eo_to_smt x))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) = B := by
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) = B := by
    rw [__eo_to_smt.eq_def, typeof_select_eq (__eo_to_smt y) (__eo_to_smt x), hy, hx]
    simp [__smtx_typeof_select, native_ite, native_Teq]
  have hApplyNN' :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) ≠
        SmtType.None := by
    rw [__eo_to_smt.eq_def]
    exact hApplyNN
  have hBNN : B ≠ SmtType.None := by
    rw [hSmt] at hApplyNN'
    exact hApplyNN'
  exact eo_to_smt_type_typeof_of_smt_type _ hSmt hBNN

/-- Stronger EO-side helper for `typeof_apply_apply_select`. -/
theorem eo_to_smt_type_typeof_apply_apply_select_of_array
    (x y U T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T)
    (hx : __eo_typeof x = U)
    (hU : __eo_to_smt_type U ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.select) y) x)) =
      __eo_to_smt_type T := by
  have hUNS : U ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none U hU
  have hReq : __eo_requires (__eo_eq U U) (Term.Boolean true) T = T :=
    eo_requires_eo_eq_self_of_non_stuck U T hUNS
  change __eo_to_smt_type (__eo_typeof_select (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type T
  rw [hy, hx]
  simpa [__eo_typeof_select, hUNS] using congrArg __eo_to_smt_type hReq

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_store_of_smt_map`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_store_of_smt_map
    (x y z : Term) (A B : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Map A B)
    (hy : __smtx_typeof (__eo_to_smt y) = A)
    (hx : __smtx_typeof (__eo_to_smt x) = B)
    (hApplyNN : term_has_non_none_type (SmtTerm.store (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
      SmtType.Map A B := by
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
        SmtType.Map A B := by
    rw [__eo_to_smt.eq_def, typeof_store_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x)]
    simp [__smtx_typeof_store, native_ite, native_Teq, hz, hy, hx]
  exact eo_to_smt_type_typeof_of_smt_type _ hSmt (by simp)

/-- Stronger EO-side helper for `typeof_apply_apply_apply_store`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_store_of_array
    (x y z U T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T)
    (hy : __eo_typeof y = U)
    (hx : __eo_typeof x = T)
    (hU : __eo_to_smt_type U ≠ SmtType.None)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) z) y) x)) =
      SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T) := by
  have hUNS : U ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none U hU
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  have hReq :
      __eo_requires (__eo_and (__eo_eq U U) (__eo_eq T T)) (Term.Boolean true)
        (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) =
      Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T :=
    eo_requires_eo_and_eq_self_of_non_stuck U T
      (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) hUNS hTNS
  have hArrayTy :
      __eo_to_smt_type (Term.Apply (Term.Apply (Term.UOp UserOp.Array) U) T) =
        SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T) := by
    change
      __smtx_typeof_guard (__eo_to_smt_type U)
          (__smtx_typeof_guard (__eo_to_smt_type T)
            (SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T))) =
        SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T)
    rw [smtx_typeof_guard_of_non_none _ _ hU, smtx_typeof_guard_of_non_none _ _ hT]
  change
    __eo_to_smt_type (__eo_typeof_store (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Map (__eo_to_smt_type U) (__eo_to_smt_type T)
  rw [hz, hy, hx]
  simpa [__eo_typeof_store, hUNS, hTNS, hReq] using hArrayTy

/-- Private EO-side helper for `is`. -/
private theorem eo_typeof_is_of_non_stuck
    (C D : Term)
    (hC : C ≠ Term.Stuck)
    (hD : D ≠ Term.Stuck) :
    __eo_typeof_is C D = Term.Bool := by
  cases C <;> cases D <;> simp [__eo_typeof_is] at hC hD ⊢

/-- Private EO-side helper for `update`. -/
private theorem eo_typeof_update_of_non_stuck
    (S D T : Term)
    (hS : S ≠ Term.Stuck)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof_update S D T = D := by
  cases S <;> cases D <;> cases T <;> simp [__eo_typeof_update] at hS hT ⊢

/-- Private EO-side helper for `tuple_select`. -/
private theorem eo_typeof_tuple_select_of_non_stuck
    (i T : Term)
    (hi : i ≠ Term.Stuck)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof_tuple_select (Term.UOp UserOp.Int) i T =
      __eo_list_nth (Term.UOp UserOp.Tuple) T i := by
  cases i <;> cases T <;> simp [__eo_typeof_tuple_select] at hi hT ⊢

/-- Private EO-side helper for `tuple_update`. -/
private theorem eo_typeof_tuple_update_of_non_stuck
    (i T U : Term)
    (hi : i ≠ Term.Stuck)
    (hT : T ≠ Term.Stuck)
    (hU : U ≠ Term.Stuck) :
    __eo_typeof_tuple_update (Term.UOp UserOp.Int) i T U =
      __eo_requires U (__eo_list_nth (Term.UOp UserOp.Tuple) T i) T := by
  cases i <;> cases T <;> cases U <;>
    simp [__eo_typeof_tuple_update] at hi hT hU ⊢

/-- Private EO-side helper for `_at_witness_string_length`. -/
private theorem eo_typeof_at_witness_string_length_of_non_stuck
    (T : Term)
    (hT : T ≠ Term.Stuck) :
    __eo_typeof__at_witness_string_length Term.Type T (Term.UOp UserOp.Int) (Term.UOp UserOp.Int) = T := by
  cases T <;> simp [__eo_typeof__at_witness_string_length] at hT ⊢

/-- Stronger EO-side helper for `typeof_apply_apply_is`. -/
theorem eo_to_smt_type_typeof_apply_apply_is_of_non_stuck
    (x y : Term)
    (hy : __eo_typeof y ≠ Term.Stuck)
    (hx : __eo_typeof x ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.is) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_is (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_is_of_non_stuck (__eo_typeof y) (__eo_typeof x) hy hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_update`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_update_of_middle_type
    (x y z D : Term)
    (hz : __eo_typeof z ≠ Term.Stuck)
    (hy : __eo_typeof y = D)
    (hx : __eo_typeof x ≠ Term.Stuck) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.update) z) y) x)) =
      __eo_to_smt_type D := by
  change __eo_to_smt_type (__eo_typeof_update (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type D
  rw [hy]
  rw [eo_typeof_update_of_non_stuck (__eo_typeof z) D (__eo_typeof x) hz hx]

/-- Stronger EO-side helper for `typeof_apply_apply_tuple_select`. -/
theorem eo_to_smt_type_typeof_apply_apply_tuple_select_of_int
    (x y T : Term)
    (hx : __eo_typeof x = Term.UOp UserOp.Int)
    (hy : __eo_typeof y = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_select) x) y)) =
      __eo_to_smt_type (__eo_list_nth (Term.UOp UserOp.Tuple) T x) := by
  have hXNS : x ≠ Term.Stuck := by
    intro hX
    subst x
    have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
      rfl
    rw [hStuckTy] at hx
    cases hx
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  change __eo_to_smt_type (__eo_typeof_tuple_select (__eo_typeof x) x (__eo_typeof y)) =
    __eo_to_smt_type (__eo_list_nth (Term.UOp UserOp.Tuple) T x)
  rw [hx, hy]
  rw [eo_typeof_tuple_select_of_non_stuck x T hXNS hTNS]

/-- Stronger EO-side helper for `typeof_apply_apply_apply_tuple_update`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_tuple_update_of_int_list_nth_type
    (x y z T : Term)
    (hz : __eo_typeof z = Term.UOp UserOp.Int)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = __eo_list_nth (Term.UOp UserOp.Tuple) T z)
    (hT : __eo_to_smt_type T ≠ SmtType.None)
    (hNth : __eo_to_smt_type (__eo_list_nth (Term.UOp UserOp.Tuple) T z) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_update) z) y) x)) =
      __eo_to_smt_type T := by
  have hZNS : z ≠ Term.Stuck := by
    intro hZ
    subst z
    have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
      rfl
    rw [hStuckTy] at hz
    cases hz
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  have hNthNS : __eo_list_nth (Term.UOp UserOp.Tuple) T z ≠ Term.Stuck :=
    eo_term_ne_stuck_of_smt_type_non_none
      (__eo_list_nth (Term.UOp UserOp.Tuple) T z) hNth
  change
    __eo_to_smt_type (__eo_typeof_tuple_update (__eo_typeof z) z (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type T
  rw [hz, hy, hx]
  rw [eo_typeof_tuple_update_of_non_stuck z T (__eo_list_nth (Term.UOp UserOp.Tuple) T z) hZNS hTNS hNthNS]
  simpa using
    congrArg __eo_to_smt_type
      (eo_requires_self_of_non_stuck (__eo_list_nth (Term.UOp UserOp.Tuple) T z) T hNthNS)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_update_of_smt_dt_sel`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_update_of_smt_dt_sel
    (x y z : Term) (s : native_String) (d : SmtDatatype) (i j : native_Nat)
    (hz : __eo_to_smt z = SmtTerm.DtSel s d i j)
    (h :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.update) z) y) x)) ≠
        SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.update) z) y) x)) =
      SmtType.Datatype s d := by
  let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.update) z) y) x
  have hTranslate :
      __eo_to_smt t =
        __eo_to_smt_updater (SmtTerm.DtSel s d i j) (__eo_to_smt y) (__eo_to_smt x) := by
    change
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.update) z) y) x) =
        __eo_to_smt_updater (SmtTerm.DtSel s d i j) (__eo_to_smt y) (__eo_to_smt x)
    rw (occs := .pos [1]) [__eo_to_smt.eq_def]
    simp only
    rw [hz]
  have hUpdaterNN :
      __smtx_typeof
          (__eo_to_smt_updater (SmtTerm.DtSel s d i j) (__eo_to_smt y) (__eo_to_smt x)) ≠
        SmtType.None := by
    rw [← hTranslate]
    exact h
  have hIteNN :
      term_has_non_none_type
        (SmtTerm.ite
          (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt y))
          (__eo_to_smt_updater_rec
            (SmtTerm.DtSel s d i j) (__smtx_dt_num_sels d i) (__eo_to_smt y)
            (__eo_to_smt x) (SmtTerm.DtCons s d i))
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    simpa [__eo_to_smt_updater] using hUpdaterNN
  rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
  have hCondNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.DtTester s d i) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hCond]
    simp
  have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype s d := by
    exact dt_tester_arg_datatype_of_non_none hCondNN
  have hTTy : T = SmtType.Datatype s d := by
    exact hElse.symm.trans hYTy
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Datatype s d := by
    rw [hTranslate, __eo_to_smt_updater]
    rw [typeof_ite_eq]
    rw [hCond, hThen, hElse, hTTy]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_tuple_update_of_smt_numeral_tuple`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_tuple_update_of_smt_numeral_tuple
    (x y z : Term) (d : SmtDatatype) (n : native_Int)
    (hy : __eo_to_smt_type (__eo_typeof y) = SmtType.Datatype "_at_Tuple" d)
    (hz : __eo_to_smt z = SmtTerm.Numeral n)
    (h :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_update) z) y) x)) ≠
        SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_update) z) y) x)) =
      SmtType.Datatype "_at_Tuple" d := by
  let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_update) z) y) x
  have hTranslate :
      __eo_to_smt t =
        __eo_to_smt_tuple_update (SmtType.Datatype "_at_Tuple" d)
          (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x) := by
    change
      __eo_to_smt (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.tuple_update) z) y) x) =
        __eo_to_smt_tuple_update (SmtType.Datatype "_at_Tuple" d)
          (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x)
    rw (occs := .pos [1]) [__eo_to_smt.eq_def]
    simp only
    rw [hy, hz]
  have hTupleNN :
      __smtx_typeof
          (__eo_to_smt_tuple_update (SmtType.Datatype "_at_Tuple" d)
            (SmtTerm.Numeral n) (__eo_to_smt y) (__eo_to_smt x)) ≠
        SmtType.None := by
    rw [← hTranslate]
    exact h
  have hGe : native_zleq 0 n = true := by
    cases hTest : native_zleq 0 n <;>
      simp [__eo_to_smt_tuple_update, hTest, native_ite] at hTupleNN
    simpa using hTest
  have hUpdaterNN :
      __smtx_typeof
          (__eo_to_smt_updater
            (SmtTerm.DtSel "_at_Tuple" d native_nat_zero (native_int_to_nat n))
            (__eo_to_smt y) (__eo_to_smt x)) ≠
        SmtType.None := by
    simpa [__eo_to_smt_tuple_update, hGe, native_ite] using hTupleNN
  have hIteNN :
      term_has_non_none_type
        (SmtTerm.ite
          (SmtTerm.Apply (SmtTerm.DtTester "_at_Tuple" d native_nat_zero) (__eo_to_smt y))
          (__eo_to_smt_updater_rec
            (SmtTerm.DtSel "_at_Tuple" d native_nat_zero (native_int_to_nat n))
            (__smtx_dt_num_sels d native_nat_zero) (__eo_to_smt y)
            (__eo_to_smt x) (SmtTerm.DtCons "_at_Tuple" d native_nat_zero))
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    simpa [__eo_to_smt_updater] using hUpdaterNN
  rcases ite_args_of_non_none hIteNN with ⟨T, hCond, hThen, hElse, hT⟩
  have hCondNN :
      term_has_non_none_type
        (SmtTerm.Apply (SmtTerm.DtTester "_at_Tuple" d native_nat_zero) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [hCond]
    simp
  have hYTy : __smtx_typeof (__eo_to_smt y) = SmtType.Datatype "_at_Tuple" d := by
    exact dt_tester_arg_datatype_of_non_none hCondNN
  have hTTy : T = SmtType.Datatype "_at_Tuple" d := by
    exact hElse.symm.trans hYTy
  have hInnerTy :
      __smtx_typeof
          (__eo_to_smt_updater
            (SmtTerm.DtSel "_at_Tuple" d native_nat_zero (native_int_to_nat n))
            (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.Datatype "_at_Tuple" d := by
    rw [__eo_to_smt_updater]
    rw [typeof_ite_eq]
    rw [hCond, hThen, hElse, hTTy]
    simp [__smtx_typeof_ite, native_ite, native_Teq]
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Datatype "_at_Tuple" d := by
    rw [hTranslate]
    simpa [__eo_to_smt_tuple_update, hGe, native_ite] using hInnerTy
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_seq_empty`. -/
theorem eo_to_smt_type_typeof_seq_empty
    (x : Term)
    (h : __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type x)) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.seq_empty x)) =
      __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type x)) := by
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.seq_empty x)) =
        __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type x)) := by
    rw [__eo_to_smt.eq_def]
  exact eo_to_smt_type_typeof_of_smt_type
    (Term.seq_empty x) hSmt (by simpa [__eo_to_smt.eq_def] using h)

/-- Stronger EO-side helper for `typeof_seq_empty`. -/
theorem eo_to_smt_type_typeof_seq_empty_of_seq_type
    (T : Term)
    (hType : __eo_typeof T = Term.Type)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.seq_empty (Term.Apply (Term.UOp UserOp.Seq) T))) =
      SmtType.Seq (__eo_to_smt_type T) := by
  have hSeqType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.Seq) T) = Term.Type := by
    change __eo_typeof_Seq (__eo_typeof T) = Term.Type
    rw [hType]
    rfl
  change
    __eo_to_smt_type
        (__eo_typeof_seq_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.Seq) T))
          (Term.Apply (Term.UOp UserOp.Seq) T)) =
      SmtType.Seq (__eo_to_smt_type T)
  rw [hSeqType]
  change __eo_to_smt_type (__eo_disamb_type_seq_empty (Term.Apply (Term.UOp UserOp.Seq) T)) =
    SmtType.Seq (__eo_to_smt_type T)
  simp [__eo_disamb_type_seq_empty]
  exact smtx_typeof_guard_of_non_none _ _ hT

/-- Simplifies EO-to-SMT type translation for `typeof_set_empty`. -/
theorem eo_to_smt_type_typeof_set_empty
    (x : Term)
    (h : __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type x)) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.set_empty x)) =
      __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type x)) := by
  have hSmt :
      __smtx_typeof (__eo_to_smt (Term.set_empty x)) =
        __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type x)) := by
    rw [__eo_to_smt.eq_def]
  exact eo_to_smt_type_typeof_of_smt_type
    (Term.set_empty x) hSmt (by simpa [__eo_to_smt.eq_def] using h)

/-- Stronger EO-side helper for `typeof_set_empty`. -/
theorem eo_to_smt_type_typeof_set_empty_of_set_type
    (T : Term)
    (hType : __eo_typeof T = Term.Type)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.set_empty (Term.Apply (Term.UOp UserOp.Set) T))) =
      SmtType.Set (__eo_to_smt_type T) := by
  have hSetType :
      __eo_typeof (Term.Apply (Term.UOp UserOp.Set) T) = Term.Type := by
    change __eo_typeof_Seq (__eo_typeof T) = Term.Type
    rw [hType]
    rfl
  change
    __eo_to_smt_type
        (__eo_typeof_set_empty (__eo_typeof (Term.Apply (Term.UOp UserOp.Set) T))
          (Term.Apply (Term.UOp UserOp.Set) T)) =
      SmtType.Set (__eo_to_smt_type T)
  rw [hSetType]
  change __eo_to_smt_type (__eo_disamb_type_set_empty (Term.Apply (Term.UOp UserOp.Set) T)) =
    SmtType.Set (__eo_to_smt_type T)
  simp [__eo_disamb_type_set_empty]
  exact smtx_typeof_guard_of_non_none _ _ hT

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
      __smtx_typeof (__eo_to_smt y) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt y) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hA : A ≠ SmtType.None)
    (hB : B ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_purify y) x)) = B := by
  have hHeadTranslate : __eo_to_smt (Term._at_purify y) = __eo_to_smt y := by
    rw [__eo_to_smt.eq_def]
  have hHead' :
      __smtx_typeof (__eo_to_smt (Term._at_purify y)) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt (Term._at_purify y)) = SmtType.DtcAppType A B := by
    rw [hHeadTranslate]
    exact hHead
  have hNonSel :
      ∀ s d i j, __eo_to_smt (Term._at_purify y) ≠ SmtTerm.DtSel s d i j := by
    intro s d i j hSel
    have hNone : __smtx_typeof (__eo_to_smt (Term._at_purify y)) = SmtType.None := by
      rw [hSel]
      simp
    rw [hHeadTranslate] at hNone
    rcases hHead with hHead | hHead <;> rw [hHead] at hNone <;> cases hNone
  have hNonTester :
      ∀ s d i, __eo_to_smt (Term._at_purify y) ≠ SmtTerm.DtTester s d i := by
    intro s d i hTester
    have hNone : __smtx_typeof (__eo_to_smt (Term._at_purify y)) = SmtType.None := by
      rw [hTester]
      simp
    rw [hHeadTranslate] at hNone
    rcases hHead with hHead | hHead <;> rw [hHead] at hNone <;> cases hNone
  have hTranslate :
      __eo_to_smt (Term.Apply (Term._at_purify y) x) =
        SmtTerm.Apply (__eo_to_smt (Term._at_purify y)) (__eo_to_smt x) := by
    rw [__eo_to_smt.eq_def]
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term._at_purify y)) (__eo_to_smt x) := by
    exact generic_apply_type_of_non_special_head _ _ hNonSel hNonTester
  simpa using
    eo_to_smt_type_typeof_apply_of_smt_apply
      x (Term._at_purify y) A B hHead' hx hTranslate hGeneric hA hB

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_array_deq_diff_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_at_array_deq_diff_of_smt_apply
    (x x1 x2 : Term) (A B : SmtType)
    (hHead :
      __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt (Term._at_array_deq_diff x1 x2)) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hA : A ≠ SmtType.None)
    (hB : B ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_array_deq_diff x1 x2) x)) = B := by
  have hHeadTranslate :
      __eo_to_smt (Term._at_array_deq_diff x1 x2) =
        let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_array_deq_diff x1 x2))
        let _v2 := SmtTerm.Var "_at_x" _v0
        SmtTerm.choice_nth "_at_x" _v0
          (SmtTerm.not (SmtTerm.eq (SmtTerm.select (__eo_to_smt x1) _v2) (SmtTerm.select (__eo_to_smt x2) _v2))) 0 := by
    rw [__eo_to_smt.eq_def]
  have hTranslate :
      __eo_to_smt (Term.Apply (Term._at_array_deq_diff x1 x2) x) =
        SmtTerm.Apply (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x) := by
    rw [__eo_to_smt.eq_def]
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term._at_array_deq_diff x1 x2)) (__eo_to_smt x) := by
    rw [hHeadTranslate]
    exact generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  simpa using
    eo_to_smt_type_typeof_apply_of_smt_apply
      x (Term._at_array_deq_diff x1 x2) A B hHead hx hTranslate hGeneric hA hB

/-- Stronger EO-side helper for `typeof_apply_at_bvsize`. -/
theorem eo_to_smt_type_typeof_apply_at_bvsize_of_bitvec_type
    (x w : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_bvsize) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_not_of_bool`. -/
theorem eo_to_smt_type_typeof_apply_not_of_bool
    (x : Term)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.not) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_not (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_abs_of_int`. -/
theorem eo_to_smt_type_typeof_apply_abs_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.abs) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_abs (__eo_typeof x)) = SmtType.Int
  rw [hx]
  native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_len_of_seq`. -/
theorem eo_to_smt_type_typeof_apply_str_len_of_seq
    (x V : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) V) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_len) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_len (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_rev_of_seq`. -/
theorem eo_to_smt_type_typeof_apply_str_rev_of_seq
    (x V : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) V)
    (hV : __eo_to_smt_type V ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_rev) x)) =
      SmtType.Seq (__eo_to_smt_type V) := by
  change __eo_to_smt_type (__eo_typeof_str_rev (__eo_typeof x)) =
    SmtType.Seq (__eo_to_smt_type V)
  rw [hx]
  exact smtx_typeof_guard_of_non_none _ _ hV

/-- Simplifies EO-to-SMT type translation for `typeof_apply_seq_unit_of_non_none`. -/
theorem eo_to_smt_type_typeof_apply_seq_unit_of_non_none
    (x : Term)
    (hx : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.seq_unit) x)) =
      SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
  change __eo_to_smt_type (__eo_typeof_seq_unit (__eo_typeof x)) =
    SmtType.Seq (__eo_to_smt_type (__eo_typeof x))
  cases hTy : __eo_typeof x <;> simp [__eo_typeof_seq_unit, __eo_to_smt_type, hTy] at hx ⊢
  case UOp a =>
    exact smtx_typeof_guard_of_non_none _ _ hx
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
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_singleton) x)) =
      SmtType.Set (__eo_to_smt_type (__eo_typeof x)) := by
  change __eo_to_smt_type (__eo_typeof_set_singleton (__eo_typeof x)) =
    SmtType.Set (__eo_to_smt_type (__eo_typeof x))
  cases hTy : __eo_typeof x <;> simp [__eo_typeof_set_singleton, __eo_to_smt_type, hTy] at hx ⊢
  case UOp a =>
    exact smtx_typeof_guard_of_non_none _ _ hx
  case Apply =>
    exact smtx_typeof_guard_of_non_none _ _ hx
  case DtcAppType a b =>
    cases hA : __eo_to_smt_type a <;> cases hB : __eo_to_smt_type b <;>
      simp [__smtx_typeof_guard, native_ite, native_Teq, hA, hB] at hx ⊢
  all_goals simp [__smtx_typeof_guard, native_ite, native_Teq]

/-- Stronger EO-side helper for `typeof_apply_at_bvsize`. -/
theorem eo_to_smt_type_typeof_apply_at_bvsize_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_bvsize) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_set_choose`. -/
theorem eo_to_smt_type_typeof_apply_set_choose_of_set
    (x T : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_choose) x)) = __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_set_choose (__eo_typeof x)) = __eo_to_smt_type T
  rw [hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_set_is_singleton`. -/
theorem eo_to_smt_type_typeof_apply_set_is_singleton_of_set
    (x T : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Set) T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.set_is_singleton) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_set_is_empty (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_sets_deq_diff_of_smt_apply`. -/
theorem eo_to_smt_type_typeof_apply_at_sets_deq_diff_of_smt_apply
    (x x1 x2 : Term) (A B : SmtType)
    (hHead :
      __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) = SmtType.FunType A B ∨
        __smtx_typeof (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) = SmtType.DtcAppType A B)
    (hx : __smtx_typeof (__eo_to_smt x) = A)
    (hA : A ≠ SmtType.None)
    (hB : B ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term._at_sets_deq_diff x1 x2) x)) = B := by
  have hHeadTranslate :
      __eo_to_smt (Term._at_sets_deq_diff x1 x2) =
        let _v0 := __eo_to_smt_type (__eo_typeof (Term._at_sets_deq_diff x1 x2))
        let _v2 := SmtTerm.Var "_at_x" _v0
        SmtTerm.choice_nth "_at_x" _v0
          (SmtTerm.not
            (SmtTerm.eq
              (SmtTerm.set_member _v2 (__eo_to_smt x1))
              (SmtTerm.set_member _v2 (__eo_to_smt x2)))) 0 := by
    rw [__eo_to_smt.eq_def]
  have hTranslate :
      __eo_to_smt (Term.Apply (Term._at_sets_deq_diff x1 x2) x) =
        SmtTerm.Apply (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x) := by
    rw [__eo_to_smt.eq_def]
  have hGeneric :
      generic_apply_type (__eo_to_smt (Term._at_sets_deq_diff x1 x2)) (__eo_to_smt x) := by
    rw [hHeadTranslate]
    exact generic_apply_type_of_non_special_head _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  simpa using
    eo_to_smt_type_typeof_apply_of_smt_apply
      x (Term._at_sets_deq_diff x1 x2) A B hHead hx hTranslate hGeneric hA hB

/-- Simplifies EO-to-SMT type translation for `typeof_apply_to_real_of_int`. -/
theorem eo_to_smt_type_typeof_apply_to_real_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.to_real) x)) = SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_to_real (__eo_typeof x)) = SmtType.Real
  rw [hx]
  native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_to_real_of_real`. -/
theorem eo_to_smt_type_typeof_apply_to_real_of_real
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Real)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.to_real) x)) = SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_to_real (__eo_typeof x)) = SmtType.Real
  rw [hx]
  native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_to_int_of_real`. -/
theorem eo_to_smt_type_typeof_apply_to_int_of_real
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Real)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.to_int) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_to_int (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_int_pow2_of_int`. -/
theorem eo_to_smt_type_typeof_apply_int_pow2_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.int_pow2) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_int_log2_of_int`. -/
theorem eo_to_smt_type_typeof_apply_int_log2_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.int_log2) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_int_ispow2_of_int`. -/
theorem eo_to_smt_type_typeof_apply_int_ispow2_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.int_ispow2) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_int_ispow2 (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_int_div_by_zero_of_int`. -/
theorem eo_to_smt_type_typeof_apply_at_int_div_by_zero_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_int_div_by_zero) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_mod_by_zero_of_int`. -/
theorem eo_to_smt_type_typeof_apply_at_mod_by_zero_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_mod_by_zero) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_int_pow2 (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_div_by_zero_of_real`. -/
theorem eo_to_smt_type_typeof_apply_at_div_by_zero_of_real
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Real)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_div_by_zero) x)) = SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof__at_div_by_zero (__eo_typeof x)) = SmtType.Real
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_is_int_of_real`. -/
theorem eo_to_smt_type_typeof_apply_is_int_of_real
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Real)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.is_int) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_is_int (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_lower_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_lower_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_lower) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_to_lower (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_upper_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_upper_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_upper) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_to_lower (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_code_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_code_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_code) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_to_code (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_from_code_of_int`. -/
theorem eo_to_smt_type_typeof_apply_str_from_code_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_from_code) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_from_code (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_is_digit_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_is_digit_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_is_digit) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_is_digit (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_int_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_int_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_int) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_to_code (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_from_int_of_int`. -/
theorem eo_to_smt_type_typeof_apply_str_from_int_of_int
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.Int)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_from_int) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_from_code (__eo_typeof x)) = SmtType.Seq SmtType.Char
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_at_strings_stoi_non_digit_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_at_strings_stoi_non_digit_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp._at_strings_stoi_non_digit) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_to_code (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_at_strings_stoi_result_of_smt_seq_char_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_at_strings_stoi_result_of_smt_seq_char_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp._at_strings_stoi_result) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_strings_stoi_result (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Int
  rw [eo_typeof_eq_seq_char_of_smt_seq_char y hy, eo_typeof_eq_int_of_smt_int x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_str_to_re_of_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_str_to_re_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.str_to_re) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_str_to_re (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_mult_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_mult_of_reglan
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.RegLan)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.re_mult) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_plus_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_plus_of_reglan
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.RegLan)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.re_plus) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_opt_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_opt_of_reglan
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.RegLan)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.re_opt) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_re_comp_of_reglan`. -/
theorem eo_to_smt_type_typeof_apply_re_comp_of_reglan
    (x : Term)
    (hx : __eo_typeof x = (Term.UOp UserOp.RegLan)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.re_comp) x)) = SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_mult (__eo_typeof x)) = SmtType.RegLan
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvnot_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvnot_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnot) x)) = SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvnot (__eo_typeof x)) = SmtType.BitVec w
  rw [hx]
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) =
    SmtType.BitVec w
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
    native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvneg_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvneg_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvneg) x)) = SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvnot (__eo_typeof x)) = SmtType.BitVec w
  rw [hx]
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) =
    SmtType.BitVec w
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq,
    native_nat_to_int, native_int_to_nat, SmtEval.native_nat_to_int,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvredand_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvredand_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvredand) x)) = SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvredand (__eo_typeof x)) = SmtType.BitVec 1
  rw [hx]
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) = SmtType.BitVec 1
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq, native_int_to_nat,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvredor_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvredor_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvredor) x)) = SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvredand (__eo_typeof x)) = SmtType.BitVec 1
  rw [hx]
  change __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) = SmtType.BitVec 1
  simp [__eo_to_smt_type, native_ite, native_zleq, SmtEval.native_zleq, native_int_to_nat,
    SmtEval.native_int_to_nat]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_ubv_to_int_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_ubv_to_int_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.ubv_to_int) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_sbv_to_int_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_sbv_to_int_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.sbv_to_int) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof__at_bvsize (__eo_typeof x)) = SmtType.Int
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_contains_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_contains_of_smt_seq
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) y) x)) =
      SmtType.Bool := by
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) y) x
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_str_contains_eq (__eo_to_smt y) (__eo_to_smt x), hy, hx]
    simp [__smtx_typeof_seq_op_2_ret, native_ite, native_Teq]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_prefixof_of_smt_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_prefixof_of_smt_seq
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_seq_char_of_smt_seq_char y hy, eo_typeof_eq_seq_char_of_smt_seq_char x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_suffixof_of_smt_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_suffixof_of_smt_seq
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_seq_char_of_smt_seq_char y hy, eo_typeof_eq_seq_char_of_smt_seq_char x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_lt_of_smt_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_lt_of_smt_seq_char
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_seq_char_of_smt_seq_char y hy, eo_typeof_eq_seq_char_of_smt_seq_char x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_leq_of_smt_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_leq_of_smt_seq_char
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_seq_char_of_smt_seq_char y hy, eo_typeof_eq_seq_char_of_smt_seq_char x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_range_of_smt_seq_char`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_range_of_smt_seq_char
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_range (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [eo_typeof_eq_seq_char_of_smt_seq_char y hy, eo_typeof_eq_seq_char_of_smt_seq_char x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_concat_of_smt_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_concat_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [eo_typeof_eq_reglan_of_smt_reglan y hy, eo_typeof_eq_reglan_of_smt_reglan x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_inter_of_smt_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_inter_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [eo_typeof_eq_reglan_of_smt_reglan y hy, eo_typeof_eq_reglan_of_smt_reglan x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_union_of_smt_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_union_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [eo_typeof_eq_reglan_of_smt_reglan y hy, eo_typeof_eq_reglan_of_smt_reglan x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_re_diff_of_smt_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_diff_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [eo_typeof_eq_reglan_of_smt_reglan y hy, eo_typeof_eq_reglan_of_smt_reglan x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_in_re_of_smt_seq_char_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_in_re_of_smt_seq_char_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_in_re (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_seq_char_of_smt_seq_char y hy, eo_typeof_eq_reglan_of_smt_reglan x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_seq_nth_of_smt_seq_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_seq_nth_of_smt_seq_int
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x)) = T := by
  rcases eo_typeof_eq_seq_of_smt_seq y hy with ⟨U, hy', hU⟩
  change __eo_to_smt_type (__eo_typeof_seq_nth (__eo_typeof y) (__eo_typeof x)) = T
  rw [hy', eo_typeof_eq_int_of_smt_int x hx]
  simpa [hU]

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_or_of_smt_bool`. -/
theorem eo_to_smt_type_typeof_apply_apply_or_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bool_of_smt_bool y hy, eo_typeof_eq_bool_of_smt_bool x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_and_of_smt_bool`. -/
theorem eo_to_smt_type_typeof_apply_apply_and_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bool_of_smt_bool y hy, eo_typeof_eq_bool_of_smt_bool x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_imp_of_smt_bool`. -/
theorem eo_to_smt_type_typeof_apply_apply_imp_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.imp) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bool_of_smt_bool y hy, eo_typeof_eq_bool_of_smt_bool x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_xor_of_smt_bool`. -/
theorem eo_to_smt_type_typeof_apply_apply_xor_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.xor) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bool_of_smt_bool y hy, eo_typeof_eq_bool_of_smt_bool x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_eq_of_smt_same_non_none`. -/
theorem eo_to_smt_type_typeof_apply_apply_eq_of_smt_same_non_none
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) = SmtType.Bool := by
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Bool := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_eq_eq (__eo_to_smt y) (__eo_to_smt x), hy, hx]
    simpa [__smtx_typeof_eq, native_ite, native_Teq] using
      smtx_typeof_guard_of_non_none T SmtType.Bool hT
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_plus_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_plus_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.plus) y) x)) = T := by
  rcases hT with rfl | rfl
  · change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
    rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
    native_decide
  · change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
    rw [eo_typeof_eq_real_of_smt_real y hy, eo_typeof_eq_real_of_smt_real x hx]
    native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_neg_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_neg_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x)) = T := by
  rcases hT with rfl | rfl
  · change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
    rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
    native_decide
  · change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
    rw [eo_typeof_eq_real_of_smt_real y hy, eo_typeof_eq_real_of_smt_real x hx]
    native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_mult_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_mult_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x)) = T := by
  rcases hT with rfl | rfl
  · change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
    rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
    native_decide
  · change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
    rw [eo_typeof_eq_real_of_smt_real y hy, eo_typeof_eq_real_of_smt_real x hx]
    native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_lt_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_lt_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) y) x)) = SmtType.Bool := by
  rcases hT with rfl | rfl
  · change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
    rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
    native_decide
  · change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
    rw [eo_typeof_eq_real_of_smt_real y hy, eo_typeof_eq_real_of_smt_real x hx]
    native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_leq_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_leq_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) y) x)) = SmtType.Bool := by
  rcases hT with rfl | rfl
  · change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
    rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
    native_decide
  · change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
    rw [eo_typeof_eq_real_of_smt_real y hy, eo_typeof_eq_real_of_smt_real x hx]
    native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_gt_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_gt_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) y) x)) = SmtType.Bool := by
  rcases hT with rfl | rfl
  · change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
    rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
    native_decide
  · change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
    rw [eo_typeof_eq_real_of_smt_real y hy, eo_typeof_eq_real_of_smt_real x hx]
    native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_geq_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_geq_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) y) x)) = SmtType.Bool := by
  rcases hT with rfl | rfl
  · change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
    rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
    native_decide
  · change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
    rw [eo_typeof_eq_real_of_smt_real y hy, eo_typeof_eq_real_of_smt_real x hx]
    native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_div_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_div_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.div) y) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_mod_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_mod_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mod) y) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_multmult_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_multmult_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) y) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_divisible_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_divisible_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_divisible (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_div_total_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_div_total_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) y) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_mod_total_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_mod_total_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) y) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_multmult_total_of_smt_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_multmult_total_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_qdiv_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_qdiv_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) x)) =
      SmtType.Real := by
  rcases hT with rfl | rfl
  · change __eo_to_smt_type (__eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
    rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
    native_decide
  · change __eo_to_smt_type (__eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
    rw [eo_typeof_eq_real_of_smt_real y hy, eo_typeof_eq_real_of_smt_real x hx]
    native_decide

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_qdiv_total_of_smt_arith`. -/
theorem eo_to_smt_type_typeof_apply_apply_qdiv_total_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) x)) =
      SmtType.Real := by
  rcases hT with rfl | rfl
  · change __eo_to_smt_type (__eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
    rw [eo_typeof_eq_int_of_smt_int y hy, eo_typeof_eq_int_of_smt_int x hx]
    native_decide
  · change __eo_to_smt_type (__eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
    rw [eo_typeof_eq_real_of_smt_real y hy, eo_typeof_eq_real_of_smt_real x hx]
    native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_or`. -/
theorem eo_to_smt_type_typeof_apply_apply_or_of_bool
    (x y : Term)
    (hy : __eo_typeof y = Term.Bool)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_and`. -/
theorem eo_to_smt_type_typeof_apply_apply_and_of_bool
    (x y : Term)
    (hy : __eo_typeof y = Term.Bool)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_imp`. -/
theorem eo_to_smt_type_typeof_apply_apply_imp_of_bool
    (x y : Term)
    (hy : __eo_typeof y = Term.Bool)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.imp) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_xor`. -/
theorem eo_to_smt_type_typeof_apply_apply_xor_of_bool
    (x y : Term)
    (hy : __eo_typeof y = Term.Bool)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.xor) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_or (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_eq`. -/
theorem eo_to_smt_type_typeof_apply_apply_eq_of_same_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x)) =
      SmtType.Bool := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  change __eo_to_smt_type (__eo_typeof_eq (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  simpa [__eo_typeof_eq] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T Term.Bool hTNS)

/-- Stronger EO-side helper for `typeof_apply_apply_plus`. -/
theorem eo_to_smt_type_typeof_apply_apply_plus_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.plus) y) x)) =
      __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = __eo_to_smt_type T
  rw [hy, hx]
  rcases hT with rfl | rfl <;> native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_neg`. -/
theorem eo_to_smt_type_typeof_apply_apply_neg_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.neg) y) x)) =
      __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = __eo_to_smt_type T
  rw [hy, hx]
  rcases hT with rfl | rfl <;> native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_mult`. -/
theorem eo_to_smt_type_typeof_apply_apply_mult_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mult) y) x)) =
      __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_plus (__eo_typeof y) (__eo_typeof x)) = __eo_to_smt_type T
  rw [hy, hx]
  rcases hT with rfl | rfl <;> native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_lt`. -/
theorem eo_to_smt_type_typeof_apply_apply_lt_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.lt) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rcases hT with rfl | rfl <;> native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_leq`. -/
theorem eo_to_smt_type_typeof_apply_apply_leq_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.leq) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rcases hT with rfl | rfl <;> native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_gt`. -/
theorem eo_to_smt_type_typeof_apply_apply_gt_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.gt) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rcases hT with rfl | rfl <;> native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_geq`. -/
theorem eo_to_smt_type_typeof_apply_apply_geq_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.geq) y) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rcases hT with rfl | rfl <;> native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_div`. -/
theorem eo_to_smt_type_typeof_apply_apply_div_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.div) y) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_mod`. -/
theorem eo_to_smt_type_typeof_apply_apply_mod_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mod) y) x)) = SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_multmult`. -/
theorem eo_to_smt_type_typeof_apply_apply_multmult_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_divisible`. -/
theorem eo_to_smt_type_typeof_apply_apply_divisible_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_divisible (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_div_total`. -/
theorem eo_to_smt_type_typeof_apply_apply_div_total_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_mod_total`. -/
theorem eo_to_smt_type_typeof_apply_apply_mod_total_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_multmult_total`. -/
theorem eo_to_smt_type_typeof_apply_apply_multmult_total_of_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_div (__eo_typeof y) (__eo_typeof x)) = SmtType.Int
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_qdiv`. -/
theorem eo_to_smt_type_typeof_apply_apply_qdiv_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) y) x)) =
      SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
  rw [hy, hx]
  rcases hT with rfl | rfl <;> native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_qdiv_total`. -/
theorem eo_to_smt_type_typeof_apply_apply_qdiv_total_of_arith_type
    (x y T : Term)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : T = Term.UOp UserOp.Int ∨ T = Term.UOp UserOp.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) y) x)) =
      SmtType.Real := by
  change __eo_to_smt_type (__eo_typeof_qdiv (__eo_typeof y) (__eo_typeof x)) = SmtType.Real
  rw [hy, hx]
  rcases hT with rfl | rfl <;> native_decide

/-- Stronger EO-side helper for `typeof_apply_apply_apply_ite`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_ite_of_bool_same_type
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Bool)
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) =
      __eo_to_smt_type T := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  change __eo_to_smt_type (__eo_typeof_ite (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type T
  rw [hz, hy, hx]
  simpa [__eo_typeof_ite] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T T hTNS)

/-- Private EO-side helper for sequence binops with a same-element-type check. -/
private theorem eo_to_smt_type_typeof_seq_same_elem_ret_bool
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hy, hx]
  simpa [__eo_typeof_str_contains] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T Term.Bool hTNS)

/-- Private EO-side helper for sequence binops returning the same sequence type. -/
private theorem eo_to_smt_type_typeof_seq_same_elem_ret_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_concat (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hy, hx]
  simpa [__eo_typeof_str_concat] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_eq_self_of_non_stuck T (Term.Apply (Term.UOp UserOp.Seq) T) hTNS)

/-- Private EO-side helper for ternary string ops with two same-element-type checks. -/
private theorem eo_to_smt_type_typeof_seq_same_elem_same_elem_ret_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_replace (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hz, hy, hx]
  simpa [__eo_typeof_str_replace] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_and_eq_self_of_non_stuck T T (Term.Apply (Term.UOp UserOp.Seq) T) hTNS hTNS)

/-- Private EO-side helper for string `indexof`-style typing. -/
private theorem eo_to_smt_type_typeof_seq_same_elem_int_ret_int
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.UOp UserOp.Int)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_indexof (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
      SmtType.Int := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hz, hy, hx]
  simpa [__eo_typeof_str_indexof] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T (Term.UOp UserOp.Int) hTNS)

/-- Private EO-side helper for string `update`-style typing. -/
private theorem eo_to_smt_type_typeof_seq_int_same_elem_ret_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_str_update (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  rw [hz, hy, hx]
  simpa [__eo_typeof_str_update] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_eq_self_of_non_stuck T (Term.Apply (Term.UOp UserOp.Seq) T) hTNS)

/-- Stronger EO-side helper for `typeof_apply_apply_str_contains`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_contains_of_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_contains) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_seq_same_elem_ret_bool x y T hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_str_prefixof`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_prefixof_of_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_prefixof) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_seq_same_elem_ret_bool x y T hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_str_suffixof`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_suffixof_of_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_suffixof) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_contains (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_seq_same_elem_ret_bool x y T hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_str_lt`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_lt_of_seq_char
    (x y : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_lt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_str_leq`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_leq_of_seq_char
    (x y : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_leq) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_lt (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_range`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_range_of_seq_char
    (x y : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_range) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_range (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_concat`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_concat_of_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_inter`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_inter_of_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_union`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_union_of_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_re_diff`. -/
theorem eo_to_smt_type_typeof_apply_apply_re_diff_of_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.re_diff) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_concat (__eo_typeof y) (__eo_typeof x)) = SmtType.RegLan
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_str_in_re`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_in_re_of_seq_char_reglan
    (x y : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_in_re) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_str_in_re (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_seq_nth`. -/
theorem eo_to_smt_type_typeof_apply_apply_seq_nth_of_seq_int
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) y) x)) =
      __eo_to_smt_type T := by
  change __eo_to_smt_type (__eo_typeof_seq_nth (__eo_typeof y) (__eo_typeof x)) = __eo_to_smt_type T
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_str_concat`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_concat_of_seq
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_concat (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  exact eo_to_smt_type_typeof_seq_same_elem_ret_seq x y T hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_str_at`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_at_of_seq_int
    (x y T : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_at (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_substr`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_substr_of_seq_int_int
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_substr (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  rw [hz, hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_indexof`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_indexof_of_seq_seq_int
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.UOp UserOp.Int)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_indexof (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Int
  exact eo_to_smt_type_typeof_seq_same_elem_int_ret_int x y z T hz hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_update`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_update_of_seq_int_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_update (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  exact eo_to_smt_type_typeof_seq_int_same_elem_ret_seq x y z T hz hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_replace`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) z) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_replace (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  exact eo_to_smt_type_typeof_seq_same_elem_same_elem_ret_seq x y z T hz hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_replace_all`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_seq
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) T)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.Seq) T)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) z) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T) := by
  change __eo_to_smt_type (__eo_typeof_str_replace (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.Seq) T)
  exact eo_to_smt_type_typeof_seq_same_elem_same_elem_ret_seq x y z T hz hy hx hT

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_replace_re`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_of_seq_char_reglan
    (x y z : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) z) y) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_replace_re (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Seq SmtType.Char
  rw [hz, hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_replace_re_all`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_all_of_seq_char_reglan
    (x y z : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) z) y) x)) =
      SmtType.Seq SmtType.Char := by
  change __eo_to_smt_type (__eo_typeof_str_replace_re (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Seq SmtType.Char
  rw [hz, hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_str_indexof_re`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_indexof_re_of_seq_char_reglan
    (x y z : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.Seq) (Term.UOp UserOp.Char))
    (hy : __eo_typeof y = Term.UOp UserOp.RegLan)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
      SmtType.Int := by
  change __eo_to_smt_type (__eo_typeof_str_indexof_re (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    SmtType.Int
  rw [hz, hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_re_loop`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_re_loop_of_int_int_reglan
    (x y z : Term)
    (hz : __eo_typeof z = Term.UOp UserOp.Int)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.re_loop) z) y) x)) =
      SmtType.RegLan := by
  change __eo_to_smt_type (__eo_typeof_re_loop (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    SmtType.RegLan
  rw [hz, hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_at_witness_string_length`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_at_witness_string_length_of_type_int_int
    (x y z : Term)
    (hz : __eo_typeof z = Term.Type)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type
        (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp._at_witness_string_length) z) y) x)) =
      __eo_to_smt_type z := by
  change
    __eo_to_smt_type
        (__eo_typeof__at_witness_string_length (__eo_typeof z) z (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type z
  have hZNS : z ≠ Term.Stuck := by
    intro hZ
    subst z
    have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
      rfl
    rw [hStuckTy] at hz
    cases hz
  rw [hz, hy, hx]
  rw [eo_typeof_at_witness_string_length_of_non_stuck z hZNS]

/-- Private EO-side helper for same-width bitvector operators returning a bitvector. -/
private theorem eo_to_smt_type_typeof_bv_same_width_ret_bitvec
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  have hWNS : w ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none w hW
  rw [hy, hx]
  simpa [__eo_typeof_bvand] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_eq_self_of_non_stuck w (Term.Apply (Term.UOp UserOp.BitVec) w) hWNS)

/-- Private EO-side helper for same-width bitvector comparisons. -/
private theorem eo_to_smt_type_typeof_bv_same_width_ret_bool
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool := by
  have hWNS : w ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none w hW
  rw [hy, hx]
  simpa [__eo_typeof_bvult] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck w Term.Bool hWNS)

/-- Private EO-side helper for same-width bitvector comparison-to-bv1 operators. -/
private theorem eo_to_smt_type_typeof_bv_same_width_ret_bv1
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof_bvcomp (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec 1 := by
  have hWNS : w ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none w hW
  rw [hy, hx]
  simpa [__eo_typeof_bvcomp, __eo_to_smt_type, native_ite, native_zleq] using
    congrArg __eo_to_smt_type
      (eo_requires_eo_eq_self_of_non_stuck w (Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1)) hWNS)

/-- Stronger EO-side helper for `typeof_apply_apply_concat`. -/
theorem eo_to_smt_type_typeof_apply_apply_concat_of_bitvec_types
    (x y w1 w2 : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w1)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w2) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) =
      __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add w1 w2)) := by
  change __eo_to_smt_type (__eo_typeof_concat (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add w1 w2))
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for same-width bitvector binops returning a bitvector. -/
theorem eo_to_smt_type_typeof_apply_apply_bvand_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvor`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvor_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvxor`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvxor_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvadd`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvadd_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvult`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvult_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvcomp`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvcomp_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) y) x)) =
      SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvcomp (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec 1
  exact eo_to_smt_type_typeof_bv_same_width_ret_bv1 x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvnand`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvnand_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvnand) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvnor`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvnor_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvnor) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvxnor`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvxnor_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvmul`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvmul_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvudiv`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvudiv_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvurem`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvurem_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsub`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsub_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsdiv`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsdiv_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdiv) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsrem`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsrem_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsrem) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsmod`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsmod_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvule`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvule_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvugt`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvugt_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvuge`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvuge_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvslt`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvslt_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsle`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsle_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsgt`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsgt_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsge`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsge_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvshl`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvshl_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvlshr`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvlshr_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvashr`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvashr_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w) := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) w)
  exact eo_to_smt_type_typeof_bv_same_width_ret_bitvec x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvuaddo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvuaddo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvuaddo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsaddo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsaddo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsaddo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvumulo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvumulo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsmulo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsmulo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvusubo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvusubo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvusubo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvssubo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvssubo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvssubo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsdivo`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsdivo_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  exact eo_to_smt_type_typeof_bv_same_width_ret_bool x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvultbv`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvultbv_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvultbv) y) x)) =
      SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvcomp (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec 1
  exact eo_to_smt_type_typeof_bv_same_width_ret_bv1 x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_bvsltbv`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsltbv_of_bitvec_type
    (x y w : Term)
    (hy : __eo_typeof y = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) w)
    (hW : __eo_to_smt_type w ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsltbv) y) x)) =
      SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvcomp (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec 1
  exact eo_to_smt_type_typeof_bv_same_width_ret_bv1 x y w hy hx hW

/-- Stronger EO-side helper for `typeof_apply_apply_repeat`. -/
theorem eo_to_smt_type_typeof_apply_apply_repeat_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.repeat) y) x)) =
      __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_mul y n)) := by
  change __eo_to_smt_type (__eo_typeof_repeat (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_mul y n))
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y with
  | _ =>
      rfl

/-- Stronger EO-side helper for `typeof_apply_apply_zero_extend`. -/
theorem eo_to_smt_type_typeof_apply_apply_zero_extend_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.zero_extend) y) x)) =
      __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add n y)) := by
  change __eo_to_smt_type (__eo_typeof_zero_extend (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add n y))
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y with
  | Stuck =>
      have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
        rfl
      rw [hStuckTy] at hy
      cases hy
  | _ =>
      rfl

/-- Stronger EO-side helper for `typeof_apply_apply_sign_extend`. -/
theorem eo_to_smt_type_typeof_apply_apply_sign_extend_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.sign_extend) y) x)) =
      __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add n y)) := by
  change __eo_to_smt_type (__eo_typeof_zero_extend (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type (__eo_mk_apply (Term.UOp UserOp.BitVec) (__eo_add n y))
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y with
  | Stuck =>
      have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
        rfl
      rw [hStuckTy] at hy
      cases hy
  | _ =>
      rfl

/-- Stronger EO-side helper for `typeof_apply_apply_rotate_left`. -/
theorem eo_to_smt_type_typeof_apply_apply_rotate_left_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_left) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) n) := by
  change __eo_to_smt_type (__eo_typeof_rotate_left (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) n)
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_rotate_right`. -/
theorem eo_to_smt_type_typeof_apply_apply_rotate_right_of_int_bitvec_type
    (x y n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_right) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) n) := by
  change __eo_to_smt_type (__eo_typeof_rotate_left (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) n)
  rw [hy, hx]
  rfl

/-- Stronger EO-side helper for `typeof_apply_apply_int_to_bv`. -/
theorem eo_to_smt_type_typeof_apply_apply_int_to_bv_of_int_int
    (x y : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.UOp UserOp.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.int_to_bv) y) x)) =
      __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) y) := by
  change __eo_to_smt_type (__eo_typeof_int_to_bv (__eo_typeof y) y (__eo_typeof x)) =
    __eo_to_smt_type (Term.Apply (Term.UOp UserOp.BitVec) y)
  rw [hy, hx]
  apply congrArg __eo_to_smt_type
  cases y with
  | Stuck =>
      have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
        rfl
      rw [hStuckTy] at hy
      cases hy
  | _ =>
      rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_extract`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_extract_of_int_int_bitvec_type
    (x y z n : Term)
    (hy : __eo_typeof y = Term.UOp UserOp.Int)
    (hz : __eo_typeof z = Term.UOp UserOp.Int)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) n) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.extract) y) z) x)) =
      __eo_to_smt_type
        (__eo_mk_apply
          (Term.UOp UserOp.BitVec)
          (__eo_requires (__eo_gt (__eo_add z (Term.Numeral 1)) (Term.Numeral 0)) (Term.Boolean true)
            (__eo_requires (__eo_gt n y) (Term.Boolean true)
              (__eo_add (__eo_add y (__eo_neg z)) (Term.Numeral 1))))) := by
  change __eo_to_smt_type (__eo_typeof_extract (__eo_typeof y) y (__eo_typeof z) z (__eo_typeof x)) =
    __eo_to_smt_type
      (__eo_mk_apply
        (Term.UOp UserOp.BitVec)
        (__eo_requires (__eo_gt (__eo_add z (Term.Numeral 1)) (Term.Numeral 0)) (Term.Boolean true)
          (__eo_requires (__eo_gt n y) (Term.Boolean true)
            (__eo_add (__eo_add y (__eo_neg z)) (Term.Numeral 1)))))
  rw [hy, hz, hx]
  apply congrArg __eo_to_smt_type
  cases y with
  | Stuck =>
      have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
        rfl
      rw [hStuckTy] at hy
      cases hy
  | _ =>
      cases z with
      | Stuck =>
          have hStuckTy : __eo_typeof Term.Stuck = Term.Stuck := by
            rfl
          rw [hStuckTy] at hz
          cases hz
      | _ =>
          rfl

/-- Stronger EO-side helper for `typeof_apply_apply_apply_bvite`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_bvite_of_bitvec1_same_type
    (x y z T : Term)
    (hz : __eo_typeof z = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral 1))
    (hy : __eo_typeof y = T)
    (hx : __eo_typeof x = T)
    (hT : __eo_to_smt_type T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) =
      __eo_to_smt_type T := by
  have hTNS : T ≠ Term.Stuck := eo_term_ne_stuck_of_smt_type_non_none T hT
  change __eo_to_smt_type (__eo_typeof_bvite (__eo_typeof z) (__eo_typeof y) (__eo_typeof x)) =
    __eo_to_smt_type T
  rw [hz, hy, hx]
  simpa [__eo_typeof_bvite] using
    congrArg __eo_to_smt_type (eo_requires_eo_eq_self_of_non_stuck T T hTNS)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_concat_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_concat_of_smt_bitvec
    (x y : Term) (w1 w2 : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w1)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w2) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2))) := by
  change __eo_to_smt_type (__eo_typeof_concat (__eo_typeof y) (__eo_typeof x)) =
    SmtType.BitVec (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2)))
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w1 hy, eo_typeof_eq_bitvec_of_smt_bitvec x w2 hx]
  simpa [__eo_typeof_concat, __eo_mk_apply, __eo_add] using
    eo_to_smt_type_bitvec_nat
      (native_int_to_nat (native_zplus (native_nat_to_int w1) (native_nat_to_int w2)))

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvand_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvand_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvor_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvor_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvnand_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvnand_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvnand) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvnor_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvnor_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvnor) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvxor_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvxor_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvxnor_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvxnor_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvxnor) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvcomp_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvcomp_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvcomp) y) x)) =
      SmtType.BitVec 1 := by
  change __eo_to_smt_type (__eo_typeof_bvcomp (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec 1
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvcomp, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat 1

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvadd_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvadd_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvadd) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvmul_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvmul_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvmul) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvudiv_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvudiv_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvudiv) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvurem_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvurem_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvurem) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsub_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsub_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsub) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsdiv_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsdiv_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdiv) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsrem_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsrem_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsrem) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsmod_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsmod_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmod) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvult_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvult_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvult) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvule_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvule_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvule) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvugt_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvugt_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvugt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvuge_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvuge_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvuge) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvslt_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvslt_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvslt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsle_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsle_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsle) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsgt_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsgt_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsgt) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsge_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsge_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsge) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvshl_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvshl_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvshl) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvlshr_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvlshr_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvlshr) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvashr_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvashr_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvashr) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_bvand (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvand, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvuaddo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvuaddo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvuaddo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsaddo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsaddo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsaddo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvumulo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvumulo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvumulo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsmulo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsmulo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsmulo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvusubo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvusubo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvusubo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvssubo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvssubo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvssubo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_bvsdivo_of_smt_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_bvsdivo_of_smt_bitvec
    (x y : Term) (w : native_Nat)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.bvsdivo) y) x)) =
      SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvult (__eo_typeof y) (__eo_typeof x)) = SmtType.Bool
  rw [eo_typeof_eq_bitvec_of_smt_bitvec y w hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  simpa [__eo_typeof_bvult, __eo_eq, __eo_requires, native_teq, native_not, native_ite] using
    (rfl : __eo_to_smt_type Term.Bool = SmtType.Bool)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_repeat_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_repeat_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 1 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.repeat) y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zmult i (native_nat_to_int w))) := by
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.repeat) y) x
  have hSmt :
      __smtx_typeof (__eo_to_smt t) =
        SmtType.BitVec (native_int_to_nat (native_zmult i (native_nat_to_int w))) := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_repeat_eq, hy, hx]
    simp [__smtx_typeof_repeat, native_ite, hi]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_zero_extend_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_zero_extend_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.zero_extend) y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.zero_extend) y) x
  have hSmt :
      __smtx_typeof (__eo_to_smt t) =
        SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_zero_extend_eq, hy, hx]
    simp [__smtx_typeof_zero_extend, native_ite, hi]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_sign_extend_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_sign_extend_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.sign_extend) y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.sign_extend) y) x
  have hSmt :
      __smtx_typeof (__eo_to_smt t) =
        SmtType.BitVec (native_int_to_nat (native_zplus i (native_nat_to_int w))) := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_sign_extend_eq, hy, hx]
    simp [__smtx_typeof_sign_extend, native_ite, hi]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_rotate_left_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_rotate_left_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_left) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_rotate_left (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_int_of_smt_numeral y i hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  exact eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_rotate_right_of_smt_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_rotate_right_of_smt_numeral_bitvec
    (x y : Term) (i : native_Int) (w : native_Nat)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.rotate_right) y) x)) =
      SmtType.BitVec w := by
  change __eo_to_smt_type (__eo_typeof_rotate_left (__eo_typeof y) (__eo_typeof x)) = SmtType.BitVec w
  rw [eo_typeof_eq_int_of_smt_numeral y i hy, eo_typeof_eq_bitvec_of_smt_bitvec x w hx]
  exact eo_to_smt_type_bitvec_nat w

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_int_to_bv_of_smt_numeral_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_int_to_bv_of_smt_numeral_int
    (x y : Term) (i : native_Int)
    (hy : __eo_to_smt y = SmtTerm.Numeral i)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int)
    (hi : native_zleq 0 i = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.int_to_bv) y) x)) =
      SmtType.BitVec (native_int_to_nat i) := by
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.int_to_bv) y) x
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec (native_int_to_nat i) := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_int_to_bv_eq, hy, hx]
    simp [__smtx_typeof_int_to_bv, native_ite, hi]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_bvnego_of_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_bvnego_of_bitvec
    (x : Term) (w : native_Nat)
    (hx : __eo_typeof x = Term.Apply (Term.UOp UserOp.BitVec) (Term.Numeral (native_nat_to_int w))) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.UOp UserOp.bvnego) x)) = SmtType.Bool := by
  change __eo_to_smt_type (__eo_typeof_bvnego (__eo_typeof x)) = SmtType.Bool
  rw [hx]
  rfl

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_concat_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_concat_of_smt_seq
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x)) =
      SmtType.Seq T := by
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) y) x
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_str_concat_eq (__eo_to_smt y) (__eo_to_smt x), hy, hx]
    simp [__smtx_typeof_seq_op_2, native_ite, native_Teq]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_str_at_of_smt_seq_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_str_at_of_smt_seq_int
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) y) x)) =
      SmtType.Seq T := by
  rcases eo_typeof_eq_seq_of_smt_seq y hy with ⟨U, hy', hU⟩
  have hT :
      __smtx_typeof_guard T (SmtType.Seq T) = SmtType.Seq T := by
    simpa [hy', hU, __eo_to_smt_type] using
      eo_to_smt_type_typeof_of_smt_type y hy (by simp)
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hT
    simp [__smtx_typeof_guard, native_ite, native_Teq] at hT
  simpa [hU, smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN] using
    eo_to_smt_type_typeof_apply_apply_str_at_of_seq_int
      x y U hy' (eo_typeof_eq_int_of_smt_int x hx)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_extract_of_smt_numeral_numeral_bitvec`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_extract_of_smt_numeral_numeral_bitvec
    (x y z : Term) (i j : native_Int) (w : native_Nat)
    (hz : __eo_to_smt z = SmtTerm.Numeral i)
    (hy : __eo_to_smt y = SmtTerm.Numeral j)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w)
    (hj0 : native_zleq 0 j = true)
    (hji : native_zleq j i = true)
    (hiw : native_zlt i (native_nat_to_int w) = true) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.extract) z) y) x)) =
      SmtType.BitVec (native_int_to_nat (native_zplus (native_zplus i (native_zneg j)) 1)) := by
  let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.extract) z) y) x
  have hSmt :
      __smtx_typeof (__eo_to_smt t) =
        SmtType.BitVec (native_int_to_nat (native_zplus (native_zplus i (native_zneg j)) 1)) := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_extract_eq, hz, hy, hx]
    simp [__smtx_typeof_extract, native_ite, hj0, hji, hiw]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_substr_of_smt_seq_int_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_substr_of_smt_seq_int_int
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) z) y) x)) =
      SmtType.Seq T := by
  rcases eo_typeof_eq_seq_of_smt_seq z hz with ⟨U, hz', hU⟩
  have hT :
      __smtx_typeof_guard T (SmtType.Seq T) = SmtType.Seq T := by
    simpa [hz', hU, __eo_to_smt_type] using
      eo_to_smt_type_typeof_of_smt_type z hz (by simp)
  have hTNN : T ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hT
    simp [__smtx_typeof_guard, native_ite, native_Teq] at hT
  simpa [hU, smtx_typeof_guard_of_non_none T (SmtType.Seq T) hTNN] using
    eo_to_smt_type_typeof_apply_apply_apply_str_substr_of_seq_int_int
      x y z U hz' (eo_typeof_eq_int_of_smt_int y hy) (eo_typeof_eq_int_of_smt_int x hx)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_indexof_of_smt_seq_seq_int`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_indexof_of_smt_seq_seq_int
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x)) =
      SmtType.Int := by
  let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) z) y) x
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Int := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_str_indexof_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x), hz, hy, hx]
    simp [__smtx_typeof_str_indexof, native_ite, native_Teq]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_update_of_smt_seq_int_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_update_of_smt_seq_int_seq
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x)) =
      SmtType.Seq T := by
  let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) z) y) x
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_str_update_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x), hz, hy, hx]
    simp [__smtx_typeof_str_update, native_ite, native_Teq]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_replace_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_of_smt_seq
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) z) y) x)) =
      SmtType.Seq T := by
  let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace) z) y) x
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_str_replace_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x), hz, hy, hx]
    simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_replace_all_of_smt_seq`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_all_of_smt_seq
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq T)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) z) y) x)) =
      SmtType.Seq T := by
  let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_all) z) y) x
  have hSmt : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_str_replace_all_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x), hz, hy, hx]
    simp [__smtx_typeof_seq_op_3, native_ite, native_Teq]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt (by simp)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_replace_re_of_smt_seq_char_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_of_smt_seq_char_reglan
    (x y z : Term)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re) z) y) x)) =
      SmtType.Seq SmtType.Char := by
  simpa using
    eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_of_seq_char_reglan
      x y z
      (eo_typeof_eq_seq_char_of_smt_seq_char z hz)
      (eo_typeof_eq_reglan_of_smt_reglan y hy)
      (eo_typeof_eq_seq_char_of_smt_seq_char x hx)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_replace_re_all_of_smt_seq_char_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_all_of_smt_seq_char_reglan
    (x y z : Term)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_replace_re_all) z) y) x)) =
      SmtType.Seq SmtType.Char := by
  simpa using
    eo_to_smt_type_typeof_apply_apply_apply_str_replace_re_all_of_seq_char_reglan
      x y z
      (eo_typeof_eq_seq_char_of_smt_seq_char z hz)
      (eo_typeof_eq_reglan_of_smt_reglan y hy)
      (eo_typeof_eq_seq_char_of_smt_seq_char x hx)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_str_indexof_re_of_smt_seq_char_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_str_indexof_re_of_smt_seq_char_reglan
    (x y z : Term)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Seq SmtType.Char)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) z) y) x)) =
      SmtType.Int := by
  simpa using
    eo_to_smt_type_typeof_apply_apply_apply_str_indexof_re_of_seq_char_reglan
      x y z
      (eo_typeof_eq_seq_char_of_smt_seq_char z hz)
      (eo_typeof_eq_reglan_of_smt_reglan y hy)
      (eo_typeof_eq_int_of_smt_int x hx)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_re_loop_of_smt_numeral_numeral_reglan`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_re_loop_of_smt_numeral_numeral_reglan
    (x y z : Term) (n1 n2 : native_Int)
    (hz : __eo_to_smt z = SmtTerm.Numeral n1)
    (hy : __eo_to_smt y = SmtTerm.Numeral n2)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan)
    (hn1 : native_zleq 0 n1)
    (hn2 : native_zleq 0 n2) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.re_loop) z) y) x)) =
      SmtType.RegLan := by
  simpa using
    eo_to_smt_type_typeof_apply_apply_apply_re_loop_of_int_int_reglan
      x y z
      (eo_typeof_eq_int_of_smt_numeral z n1 hz)
      (eo_typeof_eq_int_of_smt_numeral y n2 hy)
      (eo_typeof_eq_reglan_of_smt_reglan x hx)

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_bvite_of_smt_bitvec1_same_non_none`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_bvite_of_smt_bitvec1_same_non_none
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.BitVec 1)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x)) = T := by
  let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.bvite) z) y) x
  have hCond :
      __smtx_typeof (SmtTerm.eq (__eo_to_smt z) (SmtTerm.Binary 1 1)) = SmtType.Bool := by
    rw [typeof_eq_eq (__eo_to_smt z) (SmtTerm.Binary 1 1), hz, typeof_binary_one_eq]
    simpa [__smtx_typeof_eq, native_ite, native_Teq] using
      smtx_typeof_guard_of_non_none (SmtType.BitVec 1) SmtType.Bool (by simp)
  have hSmt : __smtx_typeof (__eo_to_smt t) = T := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_ite_eq]
    rw [hCond, hy, hx]
    simpa [__smtx_typeof_ite, native_ite, native_Teq] using
      smtx_typeof_guard_of_non_none T T hT
  exact eo_to_smt_type_typeof_of_smt_type t hSmt hT

/-- Simplifies EO-to-SMT type translation for `typeof_apply_apply_apply_ite_of_smt_bool_same_non_none`. -/
theorem eo_to_smt_type_typeof_apply_apply_apply_ite_of_smt_bool_same_non_none
    (x y z : Term) (T : SmtType)
    (hz : __smtx_typeof (__eo_to_smt z) = SmtType.Bool)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x)) = T := by
  let t := Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) z) y) x
  have hSmt : __smtx_typeof (__eo_to_smt t) = T := by
    rw [__eo_to_smt.eq_def]
    rw [typeof_ite_eq (__eo_to_smt z) (__eo_to_smt y) (__eo_to_smt x), hz, hy, hx]
    simp [__smtx_typeof_ite, native_ite, native_Teq, hT]
  exact eo_to_smt_type_typeof_of_smt_type t hSmt hT

end TranslationProofs
