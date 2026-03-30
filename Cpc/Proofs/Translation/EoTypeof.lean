import Cpc.Proofs.Translation.Base

open Eo
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

theorem eo_to_smt_type_typeof_numeral
    (n : eo_lit_Int) :
    __eo_to_smt_type (__eo_typeof (Term.Numeral n)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_rational
    (q : eo_lit_Rat) :
    __eo_to_smt_type (__eo_typeof (Term.Rational q)) = SmtType.Real := by
  sorry

theorem eo_to_smt_type_typeof_string
    (s : eo_lit_String) :
    __eo_to_smt_type (__eo_typeof (Term.String s)) = SmtType.Seq SmtType.Char := by
  sorry

theorem eo_to_smt_type_typeof_binary
    (w n : eo_lit_Int) :
    __eo_to_smt_type (__eo_typeof (Term.Binary w n)) = SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_var
    (s : eo_lit_String) (T : Term) :
    __eo_to_smt_type (__eo_typeof (Term.Var s T)) = __eo_to_smt_type T := by
  sorry

theorem eo_to_smt_type_typeof_uconst
    (i : eo_lit_Nat) (T : Term) :
    __eo_to_smt_type (__eo_typeof (Term.UConst i T)) = __eo_to_smt_type T := by
  sorry

theorem eo_to_smt_type_typeof_seq_empty
    (x : Term)
    (h : __smtx_typeof (SmtTerm.seq_empty (__eo_to_smt_type x)) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.seq_empty x)) = SmtType.Seq (__eo_to_smt_type x) := by
  sorry

theorem eo_to_smt_type_typeof_set_empty
    (x : Term)
    (h : __smtx_typeof (SmtTerm.set_empty (__eo_to_smt_type x)) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.set_empty x)) = SmtType.Map (__eo_to_smt_type x) SmtType.Bool := by
  sorry

end TranslationProofs
