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

theorem eo_to_smt_type_typeof_dt_cons
    (s : eo_lit_String) (d : Datatype) (i : eo_lit_Nat) :
    __eo_to_smt_type (__eo_typeof (Term.DtCons s d i)) =
      __smtx_typeof (SmtTerm.DtCons s (__eo_to_smt_datatype d) i) := by
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

theorem eo_to_smt_type_typeof_purify
    (x : Term) :
    __eo_to_smt_type (__eo_typeof (Term._at_purify x)) =
      __eo_to_smt_type (__eo_typeof x) := by
  sorry

theorem eo_to_smt_type_typeof_apply_not_of_bool
    (x : Term)
    (hx : __eo_typeof x = Term.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.not x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_abs_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.abs x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_len_of_seq
    (x V : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq V) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_len x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_rev_of_seq
    (x V : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq V) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_rev x)) =
      SmtType.Seq (__eo_to_smt_type V) := by
  sorry

theorem eo_to_smt_type_typeof_apply_seq_unit_of_non_none
    (x : Term)
    (hx : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.seq_unit x)) =
      SmtType.Seq (__eo_to_smt_type (__eo_typeof x)) := by
  sorry

theorem eo_to_smt_type_typeof_apply_set_singleton_of_non_none
    (x : Term)
    (hx : __eo_to_smt_type (__eo_typeof x) ≠ SmtType.None) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.set_singleton x)) =
      SmtType.Map (__eo_to_smt_type (__eo_typeof x)) SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_to_real_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.to_real x)) = SmtType.Real := by
  sorry

theorem eo_to_smt_type_typeof_apply_to_real_of_real
    (x : Term)
    (hx : __eo_typeof x = Term.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.to_real x)) = SmtType.Real := by
  sorry

theorem eo_to_smt_type_typeof_apply_to_int_of_real
    (x : Term)
    (hx : __eo_typeof x = Term.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.to_int x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_int_pow2_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.int_pow2 x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_int_log2_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.int_log2 x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_int_ispow2_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.int_ispow2 x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_at_int_div_by_zero_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term._at_int_div_by_zero x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_at_mod_by_zero_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term._at_mod_by_zero x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_at_div_by_zero_of_real
    (x : Term)
    (hx : __eo_typeof x = Term.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term._at_div_by_zero x)) = SmtType.Real := by
  sorry

theorem eo_to_smt_type_typeof_apply_is_int_of_real
    (x : Term)
    (hx : __eo_typeof x = Term.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.is_int x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_to_lower_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_lower x)) =
      SmtType.Seq SmtType.Char := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_to_upper_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_upper x)) =
      SmtType.Seq SmtType.Char := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_to_code_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_code x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_from_code_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_from_code x)) =
      SmtType.Seq SmtType.Char := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_is_digit_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_is_digit x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_to_int_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_int x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_from_int_of_int
    (x : Term)
    (hx : __eo_typeof x = Term.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_from_int x)) =
      SmtType.Seq SmtType.Char := by
  sorry

theorem eo_to_smt_type_typeof_apply_at_strings_stoi_non_digit_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term._at_strings_stoi_non_digit x)) =
      SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_str_to_re_of_seq_char
    (x : Term)
    (hx : __eo_typeof x = Term.Apply Term.Seq Term.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.str_to_re x)) = SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_re_mult_of_reglan
    (x : Term)
    (hx : __eo_typeof x = Term.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.re_mult x)) = SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_re_plus_of_reglan
    (x : Term)
    (hx : __eo_typeof x = Term.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.re_plus x)) = SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_re_opt_of_reglan
    (x : Term)
    (hx : __eo_typeof x = Term.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.re_opt x)) = SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_re_comp_of_reglan
    (x : Term)
    (hx : __eo_typeof x = Term.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.re_comp x)) = SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_bvnot_of_bitvec
    (x : Term) (w : eo_lit_Int)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.bvnot x)) = SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_bvneg_of_bitvec
    (x : Term) (w : eo_lit_Int)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.bvneg x)) = SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_bvredand_of_bitvec
    (x : Term) (w : eo_lit_Int)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.bvredand x)) = SmtType.BitVec 1 := by
  sorry

theorem eo_to_smt_type_typeof_apply_bvredor_of_bitvec
    (x : Term) (w : eo_lit_Int)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.bvredor x)) = SmtType.BitVec 1 := by
  sorry

theorem eo_to_smt_type_typeof_apply_ubv_to_int_of_bitvec
    (x : Term) (w : eo_lit_Int)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.ubv_to_int x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_sbv_to_int_of_bitvec
    (x : Term) (w : eo_lit_Int)
    (hx : __eo_typeof x = Term.Apply Term.BitVec (Term.Numeral w)) :
    __eo_to_smt_type (__eo_typeof (Term.Apply Term.sbv_to_int x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_str_contains_of_smt_seq
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_contains y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_str_prefixof_of_smt_seq
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_prefixof y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_str_suffixof_of_smt_seq
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq T) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_suffixof y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_str_lt_of_smt_seq_char
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_lt y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_str_leq_of_smt_seq_char
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_leq y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_re_range_of_smt_seq_char
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_range y) x)) =
      SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_re_concat_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_concat y) x)) =
      SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_re_inter_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_inter y) x)) =
      SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_re_union_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_union y) x)) =
      SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_re_diff_of_smt_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.RegLan)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.re_diff y) x)) =
      SmtType.RegLan := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_str_in_re_of_smt_seq_char_reglan
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq SmtType.Char)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.str_in_re y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_seq_nth_of_smt_seq_int
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Seq T)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.seq_nth y) x)) = T := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_or_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.or y) x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_and_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.and y) x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_imp_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.imp y) x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_xor_of_smt_bool
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Bool)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Bool) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.xor y) x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_plus_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.plus y) x)) = T := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_neg_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.neg y) x)) = T := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_mult_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.mult y) x)) = T := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_lt_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.lt y) x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_leq_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.leq y) x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_gt_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.gt y) x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_geq_of_smt_arith
    (x y : Term) (T : SmtType)
    (hy : __smtx_typeof (__eo_to_smt y) = T)
    (hx : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T = SmtType.Int ∨ T = SmtType.Real) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.geq y) x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_div_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.div y) x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_mod_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.mod y) x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_multmult_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.multmult y) x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_divisible_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.divisible y) x)) = SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_div_total_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.div_total y) x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_mod_total_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.mod_total y) x)) = SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_multmult_total_of_smt_int
    (x y : Term)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.Int)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.Int) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.multmult_total y) x)) =
      SmtType.Int := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_concat_of_smt_bitvec
    (x y : Term) (w1 w2 : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w1)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w2) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.concat y) x)) =
      SmtType.BitVec (smt_lit_zplus w1 w2) := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvand_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvand y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvor_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvor y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvnand_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvnand y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvnor_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvnor y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvxor_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvxor y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvxnor_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvxnor y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvcomp_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvcomp y) x)) =
      SmtType.BitVec 1 := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvadd_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvadd y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvmul_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvmul y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvudiv_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvudiv y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvurem_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvurem y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsub_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsub y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsdiv_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsdiv y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsrem_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsrem y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsmod_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsmod y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvult_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvult y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvule_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvule y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvugt_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvugt y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvuge_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvuge y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvslt_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvslt y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsle_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsle y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsgt_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsgt y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsge_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsge y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvshl_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvshl y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvlshr_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvlshr y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvashr_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvashr y) x)) =
      SmtType.BitVec w := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvuaddo_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvuaddo y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsaddo_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsaddo y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvumulo_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvumulo y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsmulo_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsmulo y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvusubo_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvusubo y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvssubo_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvssubo y) x)) =
      SmtType.Bool := by
  sorry

theorem eo_to_smt_type_typeof_apply_apply_bvsdivo_of_smt_bitvec
    (x y : Term) (w : smt_lit_Int)
    (hy : __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w)
    (hx : __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w) :
    __eo_to_smt_type (__eo_typeof (Term.Apply (Term.Apply Term.bvsdivo y) x)) =
      SmtType.Bool := by
  sorry

end TranslationProofs
