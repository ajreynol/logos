import Cpc.Proofs.Translation.Base

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace TranslationProofs

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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
            by_cases hs : s = "_at_Tuple"
            · subst hs
              simp
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
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_int`. -/
private theorem eo_to_smt_type_fun_ne_int
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Int := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_real`. -/
private theorem eo_to_smt_type_fun_ne_real
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Real := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_reglan`. -/
private theorem eo_to_smt_type_fun_ne_reglan
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.RegLan := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_char`. -/
private theorem eo_to_smt_type_fun_ne_char
    (T U : Term) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Char := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_bitvec`. -/
private theorem eo_to_smt_type_fun_ne_bitvec
    (T U : Term) (w : native_Nat) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.BitVec w := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_seq`. -/
private theorem eo_to_smt_type_fun_ne_seq
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Seq V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_set`. -/
private theorem eo_to_smt_type_fun_ne_set
    (T U : Term) (V : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Set V := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_map`. -/
private theorem eo_to_smt_type_fun_ne_map
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.Map V W := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for `fun_ne_dtc_app`. -/
private theorem eo_to_smt_type_fun_ne_dtc_app
    (T U : Term) (V W : SmtType) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.FunType T) U) ≠ SmtType.DtcAppType V W := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_bool
    (T U : Term) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Bool := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_int
    (T U : Term) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Int := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_real
    (T U : Term) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Real := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_reglan
    (T U : Term) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.RegLan := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

/-- Simplifies EO-to-SMT type translation for datatype-constructor application types. -/
private theorem eo_to_smt_type_dtc_app_ne_char
    (T U : Term) :
    __eo_to_smt_type (Term.DtcAppType T U) ≠ SmtType.Char := by
  cases hT : __eo_to_smt_type T <;> cases hU : __eo_to_smt_type U <;>
    simp [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq, hT, hU]

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
              cases x <;> simp [__eo_to_smt_type] at h
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
              cases x <;> simp [__eo_to_smt_type] at h
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
              cases x <;> simp [__eo_to_smt_type] at h
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
              cases x <;> simp [__eo_to_smt_type] at h
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
              cases x <;> simp [__eo_to_smt_type] at h
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
              cases x <;> simp [__eo_to_smt_type] at h
              case Numeral n =>
                  by_cases hn : native_zleq 0 n = true
                  · simp [native_ite, hn] at h
                    cases h
                    have hnNonneg : 0 <= n := by
                      simpa [native_zleq, SmtEval.native_zleq] using hn
                    simp [native_nat_to_int, native_int_to_nat,
                      SmtEval.native_nat_to_int, SmtEval.native_int_to_nat,
                      Int.toNat_of_nonneg hnNonneg]
                  · simp [native_ite, hn] at h
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
              cases x <;> simp [__eo_to_smt_type] at h
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
              cases x <;> simp [__eo_to_smt_type] at h
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
              cases x <;> simp [__eo_to_smt_type] at h
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
              cases x <;> simp [__eo_to_smt_type] at h
      | Apply f y =>
          cases f with
          | FunType =>
              have hParts : __eo_to_smt_type y = A ∧ __eo_to_smt_type x = B := by
                cases hy : __eo_to_smt_type y <;> cases hx : __eo_to_smt_type x <;>
                  simpa [eo_to_smt_type_fun, __smtx_typeof_guard, native_ite, native_Teq,
                    hy, hx] using h
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
          simpa [eo_to_smt_type_dtc_app, __smtx_typeof_guard, native_ite, native_Teq,
            hU, hV] using h
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
                  · simp [__eo_to_smt_type, native_ite, hn] at h
                  · simp [__eo_to_smt_type, native_ite, hn] at h
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

end TranslationProofs
