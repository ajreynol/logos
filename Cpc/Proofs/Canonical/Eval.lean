import Cpc.Proofs.Canonical.Ops

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

theorem model_eval_boolean_canonical
    (M : SmtModel)
    (b : native_Bool) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.Boolean b)) := by
  simpa [__smtx_model_eval] using value_canonical_boolean b

theorem model_eval_numeral_canonical
    (M : SmtModel)
    (n : native_Int) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.Numeral n)) := by
  simpa [__smtx_model_eval] using value_canonical_numeral n

theorem model_eval_rational_canonical
    (M : SmtModel)
    (q : native_Rat) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.Rational q)) := by
  simpa [__smtx_model_eval] using value_canonical_rational q

theorem model_eval_string_canonical
    (M : SmtModel)
    (s : native_String) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.String s)) := by
  simpa [__smtx_model_eval] using model_eval_string_value_canonical s

theorem model_eval_var_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : type_inhabited T) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.Var s T)) := by
  simpa [__smtx_model_eval] using model_total_typed_lookup_canonical hM s T hT

theorem model_eval_uconst_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (T : SmtType)
    (hT : type_inhabited T) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.UConst s T)) := by
  simpa [__smtx_model_eval] using model_total_typed_lookup_canonical hM s T hT

theorem model_eval_eq_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.eq t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_eq_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_not_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.not t)) := by
  simpa [__smtx_model_eval] using
    model_eval_not_canonical (__smtx_model_eval M t)

theorem model_eval_or_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.or t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_or_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_and_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.and t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_and_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_imp_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.imp t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_imp_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_xor_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.xor t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_xor_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_plus_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.plus t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_plus_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_sub_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.neg t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_sub_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_mult_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.mult t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_mult_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_lt_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.lt t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_lt_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_leq_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.leq t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_leq_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_gt_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.gt t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_gt_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_geq_term_canonical
    (M : SmtModel)
    (t1 t2 : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.geq t1 t2)) := by
  simpa [__smtx_model_eval] using
    model_eval_geq_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)

theorem model_eval_to_real_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.to_real t)) := by
  simpa [__smtx_model_eval] using
    model_eval_to_real_canonical (__smtx_model_eval M t)

theorem model_eval_to_int_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.to_int t)) := by
  simpa [__smtx_model_eval] using
    model_eval_to_int_canonical (__smtx_model_eval M t)

theorem model_eval_is_int_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.is_int t)) := by
  simpa [__smtx_model_eval] using
    model_eval_is_int_canonical (__smtx_model_eval M t)

theorem model_eval_abs_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.abs t)) := by
  simpa [__smtx_model_eval] using
    model_eval_abs_canonical (__smtx_model_eval M t)

theorem model_eval_uneg_term_canonical
    (M : SmtModel)
    (t : SmtTerm) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.uneg t)) := by
  simpa [__smtx_model_eval] using
    model_eval_uneg_canonical (__smtx_model_eval M t)

theorem model_eval_ite_term_canonical
    (M : SmtModel)
    (c t e : SmtTerm)
    (ht : __smtx_value_canonical (__smtx_model_eval M t))
    (he : __smtx_value_canonical (__smtx_model_eval M e)) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.ite c t e)) := by
  simpa [__smtx_model_eval] using
    model_eval_ite_canonical
      (c := __smtx_model_eval M c)
      (t := __smtx_model_eval M t)
      (e := __smtx_model_eval M e) ht he

theorem model_eval_select_term_canonical
    (M : SmtModel)
    (a i : SmtTerm)
    (ha : __smtx_value_canonical (__smtx_model_eval M a)) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.select a i)) := by
  simpa [__smtx_model_eval] using
    model_eval_select_canonical
      (v := __smtx_model_eval M a)
      (i := __smtx_model_eval M i) ha

theorem model_eval_seq_empty_term_canonical
    (M : SmtModel)
    (T : SmtType) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.seq_empty T)) := by
  simpa [__smtx_model_eval] using model_eval_seq_empty_value_canonical T

theorem model_eval_seq_unit_term_canonical
    (M : SmtModel)
    (t : SmtTerm)
    (ht : __smtx_value_canonical (__smtx_model_eval M t)) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.seq_unit t)) := by
  simpa [__smtx_model_eval] using
    model_eval_seq_unit_value_canonical (v := __smtx_model_eval M t) ht

theorem model_eval_set_empty_term_canonical
    (M : SmtModel)
    (T : SmtType) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.set_empty T)) := by
  simpa [__smtx_model_eval] using model_eval_set_empty_value_canonical T

theorem model_eval_set_singleton_term_canonical
    (M : SmtModel)
    (t : SmtTerm)
    (ht : __smtx_value_canonical (__smtx_model_eval M t)) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.set_singleton t)) := by
  simpa [__smtx_model_eval] using
    model_eval_set_singleton_value_canonical (v := __smtx_model_eval M t) ht

/-- Term-level store preserves canonicality modulo the strict-order laws of `native_vcmp`. -/
theorem model_eval_store_term_canonical_of_order_laws
    (hFlip :
      ∀ {a b : SmtValue},
        native_veq a b = false ->
          native_vcmp a b = false ->
            native_vcmp b a = true)
    (hTrans :
      ∀ {a b c : SmtValue},
        native_vcmp a b = true ->
          native_vcmp b c = true ->
            native_vcmp a c = true)
    (M : SmtModel)
    (a i e : SmtTerm)
    (ha : __smtx_value_canonical (__smtx_model_eval M a))
    (hi : __smtx_value_canonical (__smtx_model_eval M i))
    (he : __smtx_value_canonical (__smtx_model_eval M e)) :
    __smtx_value_canonical (__smtx_model_eval M (SmtTerm.store a i e)) := by
  simpa [__smtx_model_eval] using
    model_eval_store_canonical_of_order_laws
      hFlip hTrans
      (v := __smtx_model_eval M a)
      (i := __smtx_model_eval M i)
      (e := __smtx_model_eval M e) ha hi he

end Smtm
