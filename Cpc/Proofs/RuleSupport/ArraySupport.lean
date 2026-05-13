import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Canonical
import Cpc.Proofs.TypePreservation.Helpers

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace RuleProofs

/-- `smtTermKeyFree s T t` means the model key `(s,T)` does not occur free in `t`.
Binders for the same key shadow occurrences in their bodies. -/
def smtTermKeyFree (s : native_String) (T : SmtType) : SmtTerm -> Prop
  | SmtTerm.None => True
  | SmtTerm.Boolean _ => True
  | SmtTerm.Numeral _ => True
  | SmtTerm.Rational _ => True
  | SmtTerm.String _ => True
  | SmtTerm.Binary _ _ => True
  | SmtTerm.Apply f a => smtTermKeyFree s T f ∧ smtTermKeyFree s T a
  | SmtTerm.Var s' T' => __smtx_model_key s T ≠ __smtx_model_key s' T'
  | SmtTerm.ite c t e =>
      smtTermKeyFree s T c ∧ smtTermKeyFree s T t ∧ smtTermKeyFree s T e
  | SmtTerm.eq a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.exists s' T' body =>
      __smtx_model_key s T = __smtx_model_key s' T' ∨ smtTermKeyFree s T body
  | SmtTerm.forall s' T' body =>
      __smtx_model_key s T = __smtx_model_key s' T' ∨ smtTermKeyFree s T body
  | SmtTerm.choice_nth s' T' body _ =>
      __smtx_model_key s T = __smtx_model_key s' T' ∨ smtTermKeyFree s T body
  | SmtTerm.DtCons _ _ _ => True
  | SmtTerm.DtSel _ _ _ _ => True
  | SmtTerm.DtTester _ _ _ => True
  | SmtTerm.UConst s' T' => __smtx_model_key s T ≠ __smtx_model_key s' T'
  | SmtTerm.not t => smtTermKeyFree s T t
  | SmtTerm.or a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.and a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.imp a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.xor a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm._at_purify t => smtTermKeyFree s T t
  | SmtTerm.plus a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.neg a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.mult a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.lt a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.leq a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.gt a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.geq a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.to_real t => smtTermKeyFree s T t
  | SmtTerm.to_int t => smtTermKeyFree s T t
  | SmtTerm.is_int t => smtTermKeyFree s T t
  | SmtTerm.abs t => smtTermKeyFree s T t
  | SmtTerm.uneg t => smtTermKeyFree s T t
  | SmtTerm.div a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.mod a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.multmult a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.divisible a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.int_pow2 t => smtTermKeyFree s T t
  | SmtTerm.int_log2 t => smtTermKeyFree s T t
  | SmtTerm.div_total a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.mod_total a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.multmult_total a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.select a i => smtTermKeyFree s T a ∧ smtTermKeyFree s T i
  | SmtTerm.store a i e =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T i ∧ smtTermKeyFree s T e
  | SmtTerm.concat a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.extract a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.repeat a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvnot t => smtTermKeyFree s T t
  | SmtTerm.bvand a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvor a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvnand a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvnor a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvxor a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvxnor a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvcomp a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvneg t => smtTermKeyFree s T t
  | SmtTerm.bvadd a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvmul a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvudiv a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvurem a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvsub a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvsdiv a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvsrem a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvsmod a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvult a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvule a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvugt a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvuge a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvslt a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvsle a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvsgt a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvsge a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvshl a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvlshr a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvashr a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.zero_extend a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.sign_extend a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.rotate_left a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.rotate_right a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvuaddo a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvnego t => smtTermKeyFree s T t
  | SmtTerm.bvsaddo a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvumulo a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvsmulo a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvusubo a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvssubo a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.bvsdivo a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.seq_empty _ => True
  | SmtTerm.str_len t => smtTermKeyFree s T t
  | SmtTerm.str_concat a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.str_substr a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.str_contains a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.str_replace a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.str_indexof a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.str_at a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.str_prefixof a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.str_suffixof a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.str_rev t => smtTermKeyFree s T t
  | SmtTerm.str_update a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.str_to_lower t => smtTermKeyFree s T t
  | SmtTerm.str_to_upper t => smtTermKeyFree s T t
  | SmtTerm.str_to_code t => smtTermKeyFree s T t
  | SmtTerm.str_from_code t => smtTermKeyFree s T t
  | SmtTerm.str_is_digit t => smtTermKeyFree s T t
  | SmtTerm.str_to_int t => smtTermKeyFree s T t
  | SmtTerm.str_from_int t => smtTermKeyFree s T t
  | SmtTerm.str_lt a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.str_leq a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.str_replace_all a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.str_replace_re a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.str_replace_re_all a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.str_indexof_re a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.re_allchar => True
  | SmtTerm.re_none => True
  | SmtTerm.re_all => True
  | SmtTerm.str_to_re t => smtTermKeyFree s T t
  | SmtTerm.re_mult t => smtTermKeyFree s T t
  | SmtTerm.re_plus t => smtTermKeyFree s T t
  | SmtTerm.re_exp a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.re_opt t => smtTermKeyFree s T t
  | SmtTerm.re_comp t => smtTermKeyFree s T t
  | SmtTerm.re_range a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.re_concat a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.re_inter a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.re_union a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.re_diff a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.re_loop a b c =>
      smtTermKeyFree s T a ∧ smtTermKeyFree s T b ∧ smtTermKeyFree s T c
  | SmtTerm.str_in_re a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.seq_unit t => smtTermKeyFree s T t
  | SmtTerm.seq_nth a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.set_empty _ => True
  | SmtTerm.set_singleton t => smtTermKeyFree s T t
  | SmtTerm.set_union a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.set_inter a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.set_minus a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.set_member a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.set_subset a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.qdiv a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.qdiv_total a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.int_to_bv a b => smtTermKeyFree s T a ∧ smtTermKeyFree s T b
  | SmtTerm.ubv_to_int t => smtTermKeyFree s T t
  | SmtTerm.sbv_to_int t => smtTermKeyFree s T t

theorem smt_model_lookup_push_of_ne
    (M : SmtModel) (s s' : native_String) (T T' : SmtType) (v : SmtValue)
    (hne : __smtx_model_key s T ≠ __smtx_model_key s' T') :
    __smtx_model_lookup (__smtx_model_push M s T v) s' T' =
      __smtx_model_lookup M s' T' := by
  simp [__smtx_model_lookup, __smtx_model_push, hne.symm]

theorem smt_model_key_ne_of_reserved_left
    {s s' : native_String} {T T' : SmtType}
    (hReserved : native_reserved_var_name s = true)
    (hOther : native_reserved_var_name s' = false) :
    __smtx_model_key s T ≠ __smtx_model_key s' T' := by
  intro hKey
  have hName : s = s' := by
    cases hKey
    rfl
  subst s
  rw [hOther] at hReserved
  cases hReserved

theorem smt_model_lookup_push_reserved_of_unreserved_name
    (M : SmtModel) (s s' : native_String) (T T' : SmtType) (v : SmtValue)
    (hReserved : native_reserved_var_name s = true)
    (hOther : native_reserved_var_name s' = false) :
    __smtx_model_lookup (__smtx_model_push M s T v) s' T' =
      __smtx_model_lookup M s' T' :=
  smt_model_lookup_push_of_ne M s s' T T' v
    (smt_model_key_ne_of_reserved_left hReserved hOther)

theorem smt_model_push_shadow_same
    (M : SmtModel) (s : native_String) (T : SmtType) (v w : SmtValue) :
    __smtx_model_push (__smtx_model_push M s T v) s T w =
      __smtx_model_push M s T w := by
  funext k
  by_cases hk : k = __smtx_model_key s T <;>
    simp [__smtx_model_push, hk]

theorem smt_model_push_commute_of_ne
    (M : SmtModel) (s s' : native_String) (T T' : SmtType) (v w : SmtValue)
    (hne : __smtx_model_key s T ≠ __smtx_model_key s' T') :
    __smtx_model_push (__smtx_model_push M s T v) s' T' w =
      __smtx_model_push (__smtx_model_push M s' T' w) s T v := by
  funext k
  by_cases hk' : k = __smtx_model_key s' T'
  · subst k
    simp [__smtx_model_push, hne.symm]
  · by_cases hk : k = __smtx_model_key s T
    · subst k
      simp [__smtx_model_push, hk']
    · simp [__smtx_model_push, hk, hk']

theorem smt_model_push_shadow_of_key_eq
    (M : SmtModel) (s s' : native_String) (T T' : SmtType) (v w : SmtValue)
    (hKey : __smtx_model_key s T = __smtx_model_key s' T') :
    __smtx_model_push (__smtx_model_push M s T v) s' T' w =
      __smtx_model_push M s' T' w := by
  cases hKey
  exact smt_model_push_shadow_same M s T v w

theorem smt_model_eval_dt_sel_push_reserved_eq
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue)
    (hReserved : native_reserved_var_name s = true)
    (name : native_String) (d : SmtDatatype) (n m : native_Nat) (x : SmtValue) :
    __smtx_model_eval_dt_sel (__smtx_model_push M s T v) name d n m x =
      __smtx_model_eval_dt_sel M name d n m x := by
  simp [__smtx_model_eval_dt_sel,
    smt_model_lookup_push_reserved_of_unreserved_name M s native_wrong_apply_sel_id T
      (SmtType.Map SmtType.Int
        (SmtType.Map SmtType.Int
          (SmtType.Map (SmtType.Datatype name d) (__smtx_ret_typeof_sel name d n m))))
      v hReserved (by native_decide)]

theorem smt_seq_nth_wrong_push_reserved_eq
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue)
    (hReserved : native_reserved_var_name s = true)
    (ss : SmtSeq) (n : native_Int) (U : SmtType) :
    __smtx_seq_nth_wrong (__smtx_model_push M s T v) ss n U =
      __smtx_seq_nth_wrong M ss n U := by
  cases U <;>
    simp [__smtx_seq_nth_wrong,
      smt_model_lookup_push_reserved_of_unreserved_name M s native_oob_seq_nth_id T
        (SmtType.Map (SmtType.Seq ‹SmtType›)
          (SmtType.Map SmtType.Int ‹SmtType›))
        v hReserved (by native_decide)]

theorem smt_seq_nth_push_reserved_eq
    (M : SmtModel) (s : native_String) (T : SmtType) (v : SmtValue)
    (hReserved : native_reserved_var_name s = true) (x y : SmtValue) :
    __smtx_seq_nth (__smtx_model_push M s T v) x y =
      __smtx_seq_nth M x y := by
  cases x <;> cases y <;>
    simp [__smtx_seq_nth, smt_seq_nth_wrong_push_reserved_eq M s T v hReserved]

theorem eo_to_smt_true_eq :
    __eo_to_smt (Term.Boolean true) = SmtTerm.Boolean true := by
  rfl

theorem eo_to_smt_false_eq :
    __eo_to_smt (Term.Boolean false) = SmtTerm.Boolean false := by
  rfl

theorem eo_to_smt_not_eq (t : Term) :
    __eo_to_smt (Term.Apply Term.not t) = SmtTerm.not (__eo_to_smt t) := by
  rfl

theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

theorem eo_to_smt_select_eq (a i : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.select a) i) =
      SmtTerm.select (__eo_to_smt a) (__eo_to_smt i) := by
  rfl

theorem eo_to_smt_store_eq (a i e : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.Apply Term.store a) i) e) =
      SmtTerm.store (__eo_to_smt a) (__eo_to_smt i) (__eo_to_smt e) := by
  rfl

theorem model_eval_eo_to_smt_canonical
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (hTrans : eo_has_smt_translation t) :
    __smtx_value_canonical (__smtx_model_eval M (__eo_to_smt t)) := by
  exact Smtm.model_eval_canonical M hM (__eo_to_smt t) (by
    simpa [eo_has_smt_translation, term_has_non_none_type] using hTrans)

theorem eo_to_smt_type_array_of_non_none (A B : Term)
    (h : __eo_to_smt_type (Term.Apply (Term.Apply Term.Array A) B) ≠ SmtType.None) :
    __eo_to_smt_type (Term.Apply (Term.Apply Term.Array A) B) =
      SmtType.Map (__eo_to_smt_type A) (__eo_to_smt_type B) := by
  cases hA : __eo_to_smt_type A <;> cases hB : __eo_to_smt_type B <;>
    simp [TranslationProofs.eo_to_smt_type_array, __smtx_typeof_guard,
      native_ite, native_Teq, hA, hB] at h ⊢

theorem eo_typeof_eq_bool_operands_not_stuck (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A ≠ Term.Stuck ∧ B ≠ Term.Stuck := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · exact ⟨hA, hB⟩

theorem eo_typeof_eq_bool_operands_eq (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

theorem eq_of_eo_eq_true (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

theorem eq_of_requires_eq_true_not_stuck (x y B : Term) :
    __eo_requires (__eo_eq x y) (Term.Boolean true) B ≠ Term.Stuck ->
    y = x := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
    SmtEval.native_not] at hProg'
  exact eq_of_eo_eq_true x y hProg'.1

theorem eqs_of_requires_and_eq_true_not_stuck (x1 y1 x2 y2 B : Term) :
    __eo_requires (__eo_and (__eo_eq x1 x2) (__eo_eq y1 y2))
      (Term.Boolean true) B ≠ Term.Stuck ->
    x2 = x1 ∧ y2 = y1 := by
  intro hProg
  have hProg' := hProg
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hProg'
  have hAnd : __eo_and (__eo_eq x1 x2) (__eo_eq y1 y2) = Term.Boolean true := hProg'.1
  have hBoth :
      __eo_eq x1 x2 = Term.Boolean true ∧ __eo_eq y1 y2 = Term.Boolean true := by
    have eq_stuck_or_bool :
        ∀ a b : Term, __eo_eq a b = Term.Stuck ∨
          ∃ c : native_Bool, __eo_eq a b = Term.Boolean c := by
      intro a b
      by_cases ha : a = Term.Stuck
      · subst a
        exact Or.inl (by simp [__eo_eq])
      · by_cases hb : b = Term.Stuck
        · subst b
          exact Or.inl (by simp [__eo_eq])
        · exact Or.inr ⟨native_teq b a, by simp [__eo_eq, ha, hb]⟩
    rcases eq_stuck_or_bool x1 x2 with hX | ⟨b1, hX⟩
    · simp [__eo_and, hX] at hAnd
    rcases eq_stuck_or_bool y1 y2 with hY | ⟨b2, hY⟩
    · simp [__eo_and, hX, hY] at hAnd
    cases b1 <;> cases b2 <;> simp [__eo_and, hX, hY, native_and] at hAnd ⊢
  exact ⟨eq_of_eo_eq_true x1 x2 hBoth.1, eq_of_eo_eq_true y1 y2 hBoth.2⟩

theorem eo_typeof_store_not_stuck_implies_array (A I E : Term)
    (h : __eo_typeof_store A I E ≠ Term.Stuck) :
    A = Term.Apply (Term.Apply Term.Array I) E := by
  by_cases hI : I = Term.Stuck
  · subst I
    simp [__eo_typeof_store] at h
  · by_cases hE : E = Term.Stuck
    · subst E
      simp [__eo_typeof_store] at h
    · cases A with
      | Apply f x =>
          cases f with
          | Apply g y =>
              cases g with
              | UOp op =>
                  cases op with
                  | Array =>
                      have hReq :
                          __eo_requires (__eo_and (__eo_eq y I) (__eo_eq x E))
                            (Term.Boolean true) (Term.Apply (Term.Apply Term.Array y) x) ≠
                            Term.Stuck := by
                        simpa [__eo_typeof_store, hI, hE] using h
                      have hEqs :
                          I = y ∧ E = x :=
                        eqs_of_requires_and_eq_true_not_stuck y x I E
                          (Term.Apply (Term.Apply Term.Array y) x) hReq
                      simpa [hEqs.1, hEqs.2]
                  | _ =>
                      simp [__eo_typeof_store, hI, hE] at h
              | _ =>
                  simp [__eo_typeof_store, hI, hE] at h
          | _ =>
              simp [__eo_typeof_store, hI, hE] at h
      | _ =>
          simp [__eo_typeof_store, hI, hE] at h

theorem eo_typeof_select_not_stuck_implies_array (A I : Term)
    (h : __eo_typeof_select A I ≠ Term.Stuck) :
    ∃ E : Term, A = Term.Apply (Term.Apply Term.Array I) E := by
  by_cases hI : I = Term.Stuck
  · subst I
    simp [__eo_typeof_select] at h
  · cases A with
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | UOp op =>
                cases op with
                | Array =>
                    have hReq :
                        __eo_requires (__eo_eq y I) (Term.Boolean true) x ≠ Term.Stuck := by
                      simpa [__eo_typeof_select, hI] using h
                    have hEq : I = y :=
                      eq_of_requires_eq_true_not_stuck y I x hReq
                    exact ⟨x, by simpa [hEq]⟩
                | _ =>
                    simp [__eo_typeof_select, hI] at h
            | _ =>
                simp [__eo_typeof_select, hI] at h
        | _ =>
            simp [__eo_typeof_select, hI] at h
    | _ =>
        simp [__eo_typeof_select, hI] at h

theorem smt_value_rel_map_of_lookup_eq
    (m1 m2 : SmtMap)
    (hm1 : __smtx_map_canonical m1 = true)
    (hm2 : __smtx_map_canonical m2 = true)
    (hDef : Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2)
    (h : ∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v) :
    smt_value_rel (SmtValue.Map m1) (SmtValue.Map m2) := by
  have hEq : m1 = m2 := Smtm.map_ext_of_lookup_eq hm1 hm2 hDef h
  subst m2
  exact smt_value_rel_refl (SmtValue.Map m1)

theorem map_default_leaf_eq_of_canonical_typed :
    ∀ {m : SmtMap} {A B : SmtType},
      __smtx_map_canonical m = true ->
        __smtx_typeof_map_value m = SmtType.Map A B ->
          Smtm.smt_map_default_leaf m =
            SmtMap.default A (__smtx_type_default B)
  | SmtMap.default T e, A, B, hm, hTy => by
      have hParts := hm
      simp [__smtx_map_canonical, __smtx_map_default_canonical,
        SmtEval.native_and] at hParts
      cases hTy
      have hDefault : e = __smtx_type_default (__smtx_typeof_value e) := by
        simpa [native_veq] using hParts.1
      simpa [Smtm.smt_map_default_leaf] using congrArg (SmtMap.default T) hDefault
  | SmtMap.cons i e m, A, B, hm, hTy => by
      have hmTail : __smtx_map_canonical m = true := by
        have hParts := hm
        simp [__smtx_map_canonical, SmtEval.native_and] at hParts
        exact hParts.1.1.2
      by_cases hEq :
          native_Teq (SmtType.Map (__smtx_typeof_value i) (__smtx_typeof_value e))
            (__smtx_typeof_map_value m)
      · have hTailTy : __smtx_typeof_map_value m = SmtType.Map A B := by
          simpa [__smtx_typeof_map_value, native_ite, hEq] using hTy
        simpa [Smtm.smt_map_default_leaf] using
          map_default_leaf_eq_of_canonical_typed hmTail hTailTy
      · simp [__smtx_typeof_map_value, native_ite, hEq] at hTy

theorem smt_value_rel_map_of_lookup_eq_same_type
    (m1 m2 : SmtMap)
    (hm1 : __smtx_map_canonical m1 = true)
    (hm2 : __smtx_map_canonical m2 = true)
    (hTy1 : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hTy2 : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (h : ∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v) :
    smt_value_rel (SmtValue.Map m1) (SmtValue.Map m2) := by
  have hDef1 := map_default_leaf_eq_of_canonical_typed hm1 hTy1
  have hDef2 := map_default_leaf_eq_of_canonical_typed hm2 hTy2
  exact smt_value_rel_map_of_lookup_eq m1 m2 hm1 hm2 (hDef1.trans hDef2.symm) h

theorem exists_lookup_ne_of_map_native_veq_false_same_type
    (m1 m2 : SmtMap)
    (hm1 : __smtx_map_canonical m1 = true)
    (hm2 : __smtx_map_canonical m2 = true)
    (hTy1 : __smtx_typeof_map_value m1 = SmtType.Map A B)
    (hTy2 : __smtx_typeof_map_value m2 = SmtType.Map A B)
    (hNe : native_veq (SmtValue.Map m1) (SmtValue.Map m2) = false) :
    ∃ v : SmtValue, __smtx_msm_lookup m1 v ≠ __smtx_msm_lookup m2 v := by
  classical
  by_cases hExists :
      ∃ v : SmtValue, __smtx_msm_lookup m1 v ≠ __smtx_msm_lookup m2 v
  · exact hExists
  have hLookups : ∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v := by
    intro v
    by_cases hLookup : __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v
    · exact hLookup
    · exfalso
      exact hExists ⟨v, hLookup⟩
  have hRel :
      smt_value_rel (SmtValue.Map m1) (SmtValue.Map m2) :=
    smt_value_rel_map_of_lookup_eq_same_type m1 m2 hm1 hm2 hTy1 hTy2 hLookups
  have hEqTrue : native_veq (SmtValue.Map m1) (SmtValue.Map m2) = true := by
    simpa [smt_value_rel, __smtx_model_eval_eq] using hRel
  rw [hEqTrue] at hNe
  cases hNe

theorem smt_value_rel_set_of_lookup_eq
    (m1 m2 : SmtMap)
    (hm1 : __smtx_map_canonical m1 = true)
    (hm2 : __smtx_map_canonical m2 = true)
    (hDef : Smtm.smt_map_default_leaf m1 = Smtm.smt_map_default_leaf m2)
    (h : ∀ v : SmtValue, __smtx_msm_lookup m1 v = __smtx_msm_lookup m2 v) :
    smt_value_rel (SmtValue.Set m1) (SmtValue.Set m2) := by
  have hEq : m1 = m2 := Smtm.map_ext_of_lookup_eq hm1 hm2 hDef h
  subst m2
  exact smt_value_rel_refl (SmtValue.Set m1)

theorem smt_value_rel_select_store_same_of_map
    (m : SmtMap) (i e : SmtValue)
    (hm : __smtx_map_canonical m = true)
    (hi : __smtx_value_canonical i)
    (he : __smtx_value_canonical e) :
    smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store (SmtValue.Map m) i e) i)
      e := by
  have hLookup :
      __smtx_model_eval_select
          (__smtx_model_eval_store (SmtValue.Map m) i e) i = e := by
    simpa [__smtx_model_eval_select, __smtx_model_eval_store,
      __smtx_map_select, __smtx_map_store] using
      Smtm.map_lookup_update_aux_same (m := m) (i := i) (e := e) hm
  rw [hLookup]
  exact smt_value_rel_refl e

private theorem eq_of_native_veq_true {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = true) :
    v1 = v2 := by
  simpa [native_veq] using h

private theorem ne_of_native_veq_false {v1 v2 : SmtValue}
    (h : native_veq v1 v2 = false) :
    v1 ≠ v2 := by
  intro hEq
  subst v2
  simp [native_veq] at h

theorem smt_value_rel_store_overwrite
    (v i e f : SmtValue)
    (hv : __smtx_value_canonical v)
    (hi : __smtx_value_canonical i)
    (he : __smtx_value_canonical e)
    (hf : __smtx_value_canonical f) :
    smt_value_rel
      (__smtx_model_eval_store (__smtx_model_eval_store v i e) i f)
      (__smtx_model_eval_store v i f) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_store, __smtx_map_store] using
        smt_value_rel_refl SmtValue.NotValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    have hmInner :
        __smtx_map_canonical
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := e) hm hi he
    have hmLeft :
        __smtx_map_canonical
          (__smtx_msm_update_aux
            (__smtx_msm_get_default
              (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e))
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
            i f) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
        (i := i) (e := f) hmInner hi hf
    have hmRight :
        __smtx_map_canonical
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i f) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := f) hm hi hf
    simpa [__smtx_model_eval_store, __smtx_map_store] using
      smt_value_rel_map_of_lookup_eq
        (__smtx_msm_update_aux
          (__smtx_msm_get_default
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e))
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
          i f)
        (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i f)
        hmLeft hmRight
        (by simp [Smtm.map_update_aux_default_leaf])
        (by
          intro x
          exact Smtm.map_lookup_update_aux_overwrite
            (m := ‹SmtMap›) (i := i) (e := e) (f := f) (x := x) hm hi he)
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    have hmInner :
        __smtx_map_canonical
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := e) hm hi he
    have hmLeft :
        __smtx_map_canonical
          (__smtx_msm_update_aux
            (__smtx_msm_get_default
              (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e))
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
            i f) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
        (i := i) (e := f) hmInner hi hf
    have hmRight :
        __smtx_map_canonical
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i f) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := f) hm hi hf
    simpa [__smtx_model_eval_store, __smtx_map_store] using
      smt_value_rel_set_of_lookup_eq
        (__smtx_msm_update_aux
          (__smtx_msm_get_default
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e))
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
          i f)
        (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i f)
        hmLeft hmRight
        (by simp [Smtm.map_update_aux_default_leaf])
        (by
          intro x
          exact Smtm.map_lookup_update_aux_overwrite
            (m := ‹SmtMap›) (i := i) (e := e) (f := f) (x := x) hm hi he)

theorem smt_value_rel_store_swap_of_native_veq_false
    (v i j e f : SmtValue)
    (hv : __smtx_value_canonical v)
    (hi : __smtx_value_canonical i)
    (hj : __smtx_value_canonical j)
    (he : __smtx_value_canonical e)
    (hf : __smtx_value_canonical f)
    (hij : native_veq i j = false) :
    smt_value_rel
      (__smtx_model_eval_store (__smtx_model_eval_store v i e) j f)
      (__smtx_model_eval_store (__smtx_model_eval_store v j f) i e) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_store, __smtx_map_store] using
        smt_value_rel_refl SmtValue.NotValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    have hmi :
        __smtx_map_canonical
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := e) hm hi he
    have hmj :
        __smtx_map_canonical
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := j) (e := f) hm hj hf
    have hmLeft :
        __smtx_map_canonical
          (__smtx_msm_update_aux
            (__smtx_msm_get_default
              (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e))
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
            j f) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
        (i := j) (e := f) hmi hj hf
    have hmRight :
        __smtx_map_canonical
          (__smtx_msm_update_aux
            (__smtx_msm_get_default
              (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f))
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f)
            i e) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f)
        (i := i) (e := e) hmj hi he
    simpa [__smtx_model_eval_store, __smtx_map_store] using
      smt_value_rel_map_of_lookup_eq
        (__smtx_msm_update_aux
          (__smtx_msm_get_default
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e))
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
          j f)
        (__smtx_msm_update_aux
          (__smtx_msm_get_default
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f))
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f)
          i e)
        hmLeft hmRight
        (by simp [Smtm.map_update_aux_default_leaf])
        (by
          intro x
          exact Smtm.map_lookup_update_aux_swap
            (m := ‹SmtMap›) (i := i) (j := j) (e := e) (f := f) (x := x)
            hm hi hj he hf hij)
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    have hmi :
        __smtx_map_canonical
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := i) (e := e) hm hi he
    have hmj :
        __smtx_map_canonical
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f) = true :=
      Smtm.map_update_aux_canonical (m := ‹SmtMap›) (i := j) (e := f) hm hj hf
    have hmLeft :
        __smtx_map_canonical
          (__smtx_msm_update_aux
            (__smtx_msm_get_default
              (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e))
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
            j f) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
        (i := j) (e := f) hmi hj hf
    have hmRight :
        __smtx_map_canonical
          (__smtx_msm_update_aux
            (__smtx_msm_get_default
              (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f))
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f)
            i e) = true :=
      Smtm.map_update_aux_canonical
        (m := __smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f)
        (i := i) (e := e) hmj hi he
    simpa [__smtx_model_eval_store, __smtx_map_store] using
      smt_value_rel_set_of_lookup_eq
        (__smtx_msm_update_aux
          (__smtx_msm_get_default
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e))
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› i e)
          j f)
        (__smtx_msm_update_aux
          (__smtx_msm_get_default
            (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f))
          (__smtx_msm_update_aux (__smtx_msm_get_default ‹SmtMap›) ‹SmtMap› j f)
          i e)
        hmLeft hmRight
        (by simp [Smtm.map_update_aux_default_leaf])
        (by
          intro x
          exact Smtm.map_lookup_update_aux_swap
            (m := ‹SmtMap›) (i := i) (j := j) (e := e) (f := f) (x := x)
            hm hi hj he hf hij)

theorem smt_value_rel_select_store_other_of_native_veq_false
    (v i j e : SmtValue)
    (hv : __smtx_value_canonical v)
    (hi : __smtx_value_canonical i)
    (hj : __smtx_value_canonical j)
    (he : __smtx_value_canonical e)
    (hij : native_veq i j = false) :
    smt_value_rel
      (__smtx_model_eval_select (__smtx_model_eval_store v i e) j)
      (__smtx_model_eval_select v j) := by
  cases v <;>
    try
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        smt_value_rel_refl SmtValue.NotValue
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    have hLookup :
        __smtx_model_eval_select
            (__smtx_model_eval_store (SmtValue.Map ‹SmtMap›) i e) j =
          __smtx_model_eval_select (SmtValue.Map ‹SmtMap›) j := by
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        Smtm.map_lookup_update_aux_other (m := ‹SmtMap›)
          (i := i) (j := j) (e := e) hm hij
    rw [hLookup]
    exact smt_value_rel_refl (__smtx_model_eval_select (SmtValue.Map ‹SmtMap›) j)
  · have hm : __smtx_map_canonical ‹SmtMap› = true := by
      simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using hv
    have hLookup :
        __smtx_model_eval_select
            (__smtx_model_eval_store (SmtValue.Set ‹SmtMap›) i e) j =
          __smtx_model_eval_select (SmtValue.Set ‹SmtMap›) j := by
      simpa [__smtx_model_eval_select, __smtx_model_eval_store,
        __smtx_map_select, __smtx_map_store] using
        Smtm.map_lookup_update_aux_other (m := ‹SmtMap›)
          (i := i) (j := j) (e := e) hm hij
    rw [hLookup]
    exact smt_value_rel_refl (__smtx_model_eval_select (SmtValue.Set ‹SmtMap›) j)

theorem smt_value_rel_store_self_of_map
    (m : SmtMap) (i : SmtValue)
    (hm : __smtx_map_canonical m = true)
    (hi : __smtx_value_canonical i) :
    smt_value_rel
      (__smtx_model_eval_store
        (SmtValue.Map m) i
        (__smtx_model_eval_select (SmtValue.Map m) i))
      (SmtValue.Map m) := by
  have hLookupCanonical : __smtx_value_canonical (__smtx_msm_lookup m i) :=
    Smtm.map_lookup_value_canonical (m := m) (i := i) hm
  have hmLeft :
      __smtx_map_canonical
        (__smtx_msm_update_aux (__smtx_msm_get_default m) m i
          (__smtx_msm_lookup m i)) = true :=
    Smtm.map_update_aux_canonical
      (m := m) (i := i) (e := __smtx_msm_lookup m i) hm hi hLookupCanonical
  simpa [__smtx_model_eval_store, __smtx_model_eval_select,
    __smtx_map_store, __smtx_map_select] using
    smt_value_rel_map_of_lookup_eq
      (__smtx_msm_update_aux (__smtx_msm_get_default m) m i
        (__smtx_msm_lookup m i))
      m
      hmLeft hm
      (by simp [Smtm.map_update_aux_default_leaf])
      (by
        intro x
        exact Smtm.map_lookup_update_aux_self (m := m) (i := i) (x := x) hm)

theorem model_eval_eq_false_of_eo_eq_false
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply (Term.Apply Term.eq x) y) false ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  rw [eo_interprets_iff_smt_interprets, eo_to_smt_eq_eq] at h
  cases h with
  | intro_false _ hEval =>
      rw [__smtx_model_eval.eq_134] at hEval
      exact hEval

theorem native_veq_false_of_model_eval_eq_false
    {v1 v2 : SmtValue}
    (h : __smtx_model_eval_eq v1 v2 = SmtValue.Boolean false) :
    native_veq v1 v2 = false := by
  by_cases hEq : native_veq v1 v2 = false
  · exact hEq
  · have hEqTrue : native_veq v1 v2 = true := by
      cases hV : native_veq v1 v2 with
      | false =>
          exfalso
          exact hEq hV
      | true =>
          rfl
    have hv : v1 = v2 := by
      simpa [native_veq] using hEqTrue
    subst hv
    rw [smtx_model_eval_eq_refl] at h
    cases h

private theorem model_eval_eq_is_boolean (v1 v2 : SmtValue) :
    ∃ b : Bool, __smtx_model_eval_eq v1 v2 = SmtValue.Boolean b :=
  bool_value_canonical (typeof_value_model_eval_eq_value v1 v2)

theorem model_eval_eq_false_of_eq_false_eq_true
    (M : SmtModel) (x y : Term) :
  eo_interprets M
        (Term.Apply (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq x) y))
          (Term.Boolean false)) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  rw [eo_interprets_iff_smt_interprets] at h
  rw [eo_to_smt_eq_eq, eo_to_smt_eq_eq, eo_to_smt_false_eq] at h
  cases h with
  | intro_true _ hEval =>
      rw [__smtx_model_eval.eq_134] at hEval
      have hEqEval :
          __smtx_model_eval M ((__eo_to_smt x).eq (__eo_to_smt y)) =
            __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
              (__smtx_model_eval M (__eo_to_smt y)) := by
        rw [__smtx_model_eval.eq_134]
      have hFalseEval :
          __smtx_model_eval M (SmtTerm.Boolean false) =
            SmtValue.Boolean false := by
        rw [__smtx_model_eval.eq_1]
      rw [hEqEval, hFalseEval] at hEval
      rcases model_eval_eq_is_boolean
          (__smtx_model_eval M (__eo_to_smt x))
          (__smtx_model_eval M (__eo_to_smt y)) with
        ⟨b, hInner⟩
      rw [hInner] at hEval
      cases b
      · exact hInner
      · simp [__smtx_model_eval_eq, native_veq] at hEval

theorem model_eval_eq_false_of_not_eq_true
    (M : SmtModel) (x y : Term) :
    eo_interprets M (Term.Apply Term.not (Term.Apply (Term.Apply Term.eq x) y)) true ->
    __smtx_model_eval_eq (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) = SmtValue.Boolean false := by
  intro h
  exact model_eval_eq_false_of_eo_eq_false M x y
    (eo_interprets_not_true_implies_false M _ h)

end RuleProofs
