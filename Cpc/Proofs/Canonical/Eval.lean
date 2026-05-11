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
