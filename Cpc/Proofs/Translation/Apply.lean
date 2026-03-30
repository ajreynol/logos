import Cpc.Proofs.Translation.Quantifiers
import Cpc.Proofs.Translation.Special
import Cpc.Proofs.Translation.Inversions
import Cpc.Proofs.Translation.Heads

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

theorem eo_to_smt_typeof_matches_translation_apply
    (f x : Term) :
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) ≠ SmtType.None ->
    __smtx_typeof (__eo_to_smt (Term.Apply f x)) =
      __eo_to_smt_type (__eo_typeof (Term.Apply f x)) := by
  cases f <;> intro hNonNone
  case Var s T =>
    sorry
  case DtCons s d i =>
    sorry
  case DtSel s d i j =>
    sorry
  case UConst i T =>
    sorry
  case Apply f y =>
    sorry
  case not =>
    sorry
  case _at_purify y =>
    sorry
  case to_real =>
    sorry
  case to_int =>
    sorry
  case is_int =>
    sorry
  case abs =>
    sorry
  case int_pow2 =>
    sorry
  case int_log2 =>
    sorry
  case int_ispow2 =>
    sorry
  case _at_int_div_by_zero =>
    sorry
  case _at_mod_by_zero =>
    sorry
  case _at_array_deq_diff x1 x2 =>
    sorry
  case _at_bvsize =>
    sorry
  case bvnot =>
    sorry
  case bvneg =>
    sorry
  case bvredand =>
    sorry
  case bvredor =>
    sorry
  case str_len =>
    sorry
  case str_rev =>
    sorry
  case str_to_lower =>
    sorry
  case str_to_upper =>
    sorry
  case str_to_code =>
    sorry
  case str_from_code =>
    sorry
  case str_is_digit =>
    sorry
  case str_to_int =>
    sorry
  case str_from_int =>
    sorry
  case _at_strings_stoi_non_digit =>
    sorry
  case str_to_re =>
    sorry
  case re_mult =>
    sorry
  case re_plus =>
    sorry
  case re_opt =>
    sorry
  case re_comp =>
    sorry
  case seq_unit =>
    sorry
  case is =>
    sorry
  case set_empty T =>
    sorry
  case set_singleton =>
    sorry
  case set_is_empty =>
    sorry
  case set_is_singleton =>
    sorry
  case _at_sets_deq_diff x1 x2 =>
    sorry
  case _at_div_by_zero =>
    sorry
  case _at_quantifiers_skolemize x1 x2 =>
    sorry
  case ubv_to_int =>
    sorry
  case sbv_to_int =>
    sorry
  all_goals
    sorry

end TranslationProofs
