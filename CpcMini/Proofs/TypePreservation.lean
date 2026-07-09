import CpcMini.Proofs.TypePreservation.CoreArith
import CpcMini.Proofs.TypePreservation.Datatypes

open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

namespace Smtm

attribute [local simp] __smtx_type_wf_component

private theorem type_default_typed_canonical_of_map_domain_wf
    {A B : SmtType}
    (h : __smtx_type_wf (SmtType.Map A B) = true) :
    __smtx_typeof_value (__smtx_type_default A) = A ∧
      __smtx_value_canonical (__smtx_type_default A) := by
  have hAll :
      native_inhabited_type (SmtType.Map A B) = true ∧
        (((native_inhabited_type A = true ∧
          __smtx_type_wf_rec A A = true) ∧
          __smtx_type_no_alias_rec native_reflist_nil A = true) ∧
          ((native_inhabited_type B = true ∧
            __smtx_type_wf_rec B B = true) ∧
            __smtx_type_no_alias_rec native_reflist_nil B = true)) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      __smtx_type_no_alias_rec, native_and] using h
  exact type_default_typed_canonical_of_inhabited_wf_rec A hAll.2.1.1.1 hAll.2.1.1.2

private theorem type_default_typed_canonical_of_set_element_wf
    {A : SmtType}
    (h : __smtx_type_wf (SmtType.Set A) = true) :
    __smtx_typeof_value (__smtx_type_default A) = A ∧
      __smtx_value_canonical (__smtx_type_default A) := by
  have hAll :
      native_inhabited_type (SmtType.Set A) = true ∧
        ((native_inhabited_type A = true ∧
          __smtx_type_wf_rec A A = true) ∧
          __smtx_type_no_alias_rec native_reflist_nil A = true) := by
    simpa [__smtx_type_wf, __smtx_type_wf_component, __smtx_type_wf_rec,
      __smtx_type_no_alias_rec, native_and] using h
  exact type_default_typed_canonical_of_inhabited_wf_rec A hAll.2.1.1 hAll.2.1.2

private theorem map_diff_default_typed_canonical_of_non_none
    {t1 t2 : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.map_diff t1 t2)) :
    ∀ {A : SmtType},
      __smtx_typeof (SmtTerm.map_diff t1 t2) = A ->
        __smtx_typeof_value (__smtx_type_default A) = A ∧
          __smtx_value_canonical (__smtx_type_default A) := by
  intro A hA
  rcases map_diff_args_of_non_none ht with hMap | hSet
  · rcases hMap with ⟨D, R, h1, h2, hRes⟩
    have hMapWf := smt_map_wf_of_non_none_type t1 D R h1
    have hDA : D = A := hRes.symm.trans hA
    rw [← hDA]
    exact type_default_typed_canonical_of_map_domain_wf hMapWf
  · rcases hSet with ⟨D, h1, h2, hRes⟩
    have hSetWf := smt_set_wf_of_non_none_type t1 D h1
    have hDA : D = A := hRes.symm.trans hA
    rw [← hDA]
    exact type_default_typed_canonical_of_set_element_wf hSetWf

/-! ### Value-level canonicality helpers for `canonical_of_supported`. -/

/-- `NotValue` is (vacuously) canonical. -/
private theorem mini_value_canonical_notValue :
    __smtx_value_canonical SmtValue.NotValue := by
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

/-- Boolean-typed values are canonical. -/
private theorem mini_value_canonical_of_bool_type
    {v : SmtValue}
    (h : __smtx_typeof_value v = SmtType.Bool) :
    __smtx_value_canonical v := by
  rcases bool_value_canonical h with ⟨b, rfl⟩
  simp [__smtx_value_canonical, __smtx_value_canonical_bool]

/-- Packing a valid string produces a canonical sequence value. -/
private theorem mini_seq_canonical_pack_string :
    ∀ s : native_String,
      native_string_valid s = true ->
        __smtx_seq_canonical (native_pack_string s) = true
  | [], _ => by
      simp [native_pack_string, native_pack_seq, __smtx_seq_canonical]
  | c :: cs, hValid => by
      have hParts : native_char_valid c = true ∧ native_string_valid cs = true := by
        simpa [native_string_valid, List.all_cons, Bool.and_eq_true] using hValid
      have hTail : __smtx_seq_canonical (native_pack_seq SmtType.Char (cs.map SmtValue.Char)) = true :=
        mini_seq_canonical_pack_string cs hParts.2
      show __smtx_seq_canonical
          (native_pack_seq SmtType.Char (SmtValue.Char c :: cs.map SmtValue.Char)) = true
      simp [native_pack_seq, __smtx_seq_canonical, __smtx_value_canonical_bool,
        SmtEval.native_and, hParts.1, hTail]

/-- Value-level SMT `ite` preserves canonicality of the selected branch. -/
private theorem mini_model_eval_ite_canonical
    {c t e : SmtValue}
    (ht : __smtx_value_canonical t)
    (he : __smtx_value_canonical e) :
    __smtx_value_canonical (__smtx_model_eval_ite c t e) := by
  cases c <;>
    try simpa [__smtx_model_eval_ite] using mini_value_canonical_notValue
  · cases ‹native_Bool› <;>
      simp [__smtx_model_eval_ite, ht, he]

/-- Value-level Boolean negation always returns a canonical value. -/
private theorem mini_model_eval_not_canonical (v : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_not v) := by
  cases v <;>
    simp [__smtx_model_eval_not, __smtx_value_canonical, __smtx_value_canonical_bool]

/-- Value-level Boolean disjunction always returns a canonical value. -/
private theorem mini_model_eval_or_canonical (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_or v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_or, __smtx_value_canonical, __smtx_value_canonical_bool]

/-- Value-level Boolean conjunction always returns a canonical value. -/
private theorem mini_model_eval_and_canonical (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_and v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_and, __smtx_value_canonical, __smtx_value_canonical_bool]

/-- Value-level implication always returns a canonical value. -/
private theorem mini_model_eval_imp_canonical (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_imp v1 v2) := by
  simpa [__smtx_model_eval_imp] using
    mini_model_eval_or_canonical (__smtx_model_eval_not v1) v2

/-- Value-level SMT equality always returns a canonical Boolean value. -/
private theorem mini_model_eval_eq_canonical (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_eq v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp [__smtx_model_eval_eq, __smtx_value_canonical, __smtx_value_canonical_bool]

/-- Value-level `seq_diff` always returns a canonical (`Numeral` / `NotValue`) value. -/
private theorem mini_model_eval_seq_diff_canonical (v1 v2 : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_seq_diff v1 v2) := by
  cases v1 <;> cases v2 <;>
    simp only [__smtx_model_eval_seq_diff, __smtx_value_canonical,
      __smtx_value_canonical_bool] <;>
    first
      | rfl
      | (split <;> rfl)

/-- Choice evaluation always returns a canonical value. -/
private theorem mini_native_eval_tchoice_canonical
    (M : SmtModel)
    (s : native_String)
    (T : SmtType)
    (body : SmtTerm) :
    __smtx_value_canonical (native_eval_tchoice M s T body) := by
  classical
  by_cases hSat :
      ∃ v : SmtValue,
        __smtx_typeof_value v = T ∧
          __smtx_value_canonical_bool v = true ∧
          __smtx_model_eval (native_model_push M s T v) body = SmtValue.Boolean true
  · have hCan : __smtx_value_canonical (Classical.choose hSat) := by
      simpa [__smtx_value_canonical] using (Classical.choose_spec hSat).2.1
    simpa [hSat] using hCan
  · by_cases hTy :
        ∃ v : SmtValue, __smtx_typeof_value v = T ∧ __smtx_value_canonical_bool v
    · have hCan : __smtx_value_canonical (Classical.choose hTy) := by
        simpa [__smtx_value_canonical] using (Classical.choose_spec hTy).2
      simpa [hSat, hTy] using hCan
    · simpa [hSat, hTy] using mini_value_canonical_notValue

/-- Applying a function-typed value to an argument of the domain type yields a
canonical value. -/
private theorem mini_model_eval_apply_fun_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    (fid : native_String)
    (A B : SmtType)
    (x : SmtValue)
    (hxTy : __smtx_typeof_value x = A)
    (hFunWF : __smtx_type_wf (SmtType.FunType A B) = true) :
    __smtx_value_canonical (__smtx_model_eval_apply M (SmtValue.Fun fid A B) x) := by
  by_cases hxNot : x = SmtValue.NotValue
  · subst x
    simp [__smtx_model_eval_apply, __smtx_value_canonical, __smtx_value_canonical_bool]
  · have hCan : __smtx_value_canonical (native_eval_ifun_apply M fid A B x) := by
      have hRaw := (model_total_typed_native_fun_typed hM fid A B x hFunWF hxTy).2
      simpa [__smtx_value_canonical] using hRaw
    have hApply :
        __smtx_model_eval_apply M (SmtValue.Fun fid A B) x =
          native_eval_ifun_apply M fid A B x := by
      cases x <;> simp [__smtx_model_eval_apply] at hxNot ⊢
    simpa [hApply] using hCan

/-- Applying `NotValue` yields a canonical value. -/
private theorem mini_model_eval_apply_not_value_canonical
    (M : SmtModel) (x : SmtValue) :
    __smtx_value_canonical (__smtx_model_eval_apply M SmtValue.NotValue x) := by
  cases x <;>
    simp [__smtx_model_eval_apply, __smtx_value_canonical, __smtx_value_canonical_bool]

/-- Applying a looked-up function-typed value yields a canonical value. -/
private theorem mini_model_eval_apply_lookup_fun_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (A B : SmtType)
    (x : SmtValue)
    (hFunWF : __smtx_type_wf (SmtType.FunType A B) = true)
    (hxTy : __smtx_typeof_value x = A) :
    __smtx_value_canonical
      (__smtx_model_eval_apply M
        (native_model_lookup M s (SmtType.FunType A B)) x) := by
  have hLookupTy :
      __smtx_typeof_value (native_model_lookup M s (SmtType.FunType A B)) =
        SmtType.FunType A B :=
    model_total_typed_lookup hM s (SmtType.FunType A B) hFunWF
  rcases fun_value_canonical hLookupTy with ⟨fid, hLookupEq⟩
  rw [hLookupEq]
  exact mini_model_eval_apply_fun_canonical M hM fid A B x hxTy hFunWF

/-- Value-level generic application preserves canonicality. -/
private theorem mini_model_eval_apply_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    {f x : SmtValue}
    {A B : SmtType}
    (hHead :
      __smtx_typeof_value f = SmtType.FunType A B ∨
        __smtx_typeof_value f = SmtType.DtcAppType A B)
    (hFunWF :
      __smtx_typeof_value f = SmtType.FunType A B ->
        __smtx_type_wf (SmtType.FunType A B) = true)
    (hxTy : __smtx_typeof_value x = A)
    (hf : __smtx_value_canonical f)
    (hx : __smtx_value_canonical x) :
    __smtx_value_canonical (__smtx_model_eval_apply M f x) := by
  cases hHead with
  | inl hFun =>
      rcases fun_value_canonical hFun with ⟨fid, rfl⟩
      exact mini_model_eval_apply_fun_canonical M hM fid A B x hxTy (hFunWF rfl)
  | inr hDtc =>
      cases f <;> cases x <;>
        simp [__smtx_model_eval_apply, __smtx_typeof_value,
          __smtx_value_canonical, __smtx_value_canonical_bool,
          SmtEval.native_and] at hDtc hf hx ⊢
      all_goals
        first
        | assumption
        | (constructor <;> assumption)

/-- Selecting the `n`-th applied argument of a canonical value yields a canonical value. -/
private theorem mini_vsm_apply_arg_nth_canonical :
    ∀ {v : SmtValue} {n npos : native_Nat},
      __smtx_value_canonical v ->
        __smtx_value_canonical (__vsm_apply_arg_nth v n npos)
  | SmtValue.Apply f a, n, npos, hv => by
      cases npos with
      | zero =>
          simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
      | succ npos =>
          have hf : __smtx_value_canonical f := by
            have hParts := hv
            simp [__smtx_value_canonical, __smtx_value_canonical_bool,
              SmtEval.native_and] at hParts
            exact hParts.1
          have ha : __smtx_value_canonical a := by
            have hParts := hv
            simp [__smtx_value_canonical, __smtx_value_canonical_bool,
              SmtEval.native_and] at hParts
            exact hParts.2
          cases hEq : native_nateq n npos
          · simpa [__vsm_apply_arg_nth, hEq] using
              mini_vsm_apply_arg_nth_canonical hf
          · simpa [__vsm_apply_arg_nth, hEq] using ha
  | SmtValue.NotValue, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.Boolean b, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.Numeral k, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.Rational q, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.Binary w k, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.Map m, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.Fun fid A B, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.Set m, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.Seq s, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.Char c, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.UValue u k, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.RegLan r, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue
  | SmtValue.DtCons s d i, n, npos, hv => by
      simpa [__vsm_apply_arg_nth] using mini_value_canonical_notValue

/-- The "wrong selector" fallback branch of `dt_sel` yields a canonical value. -/
private theorem mini_model_eval_dt_sel_wrong_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (d : SmtDatatype)
    (n m : native_Nat)
    (v : SmtValue)
    (hvTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    __smtx_value_canonical
      (__smtx_model_eval_apply M
        (native_model_lookup M (native_wrong_apply_sel_id n m)
          (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)))
        v) := by
  by_cases hFunWF :
      __smtx_type_wf
        (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)) = true
  · exact mini_model_eval_apply_lookup_fun_canonical M hM (native_wrong_apply_sel_id n m)
      (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m) v hFunWF hvTy
  · have hFunWFFalse :
        __smtx_type_wf
          (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)) = false := by
      cases hWF :
          __smtx_type_wf
            (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)) <;>
        simp [hWF] at hFunWF ⊢
    have hLookup :
        native_model_lookup M (native_wrong_apply_sel_id n m)
            (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)) =
          SmtValue.NotValue :=
      model_total_typed_lookup_not_wf hM (native_wrong_apply_sel_id n m)
        (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d n m)) hFunWFFalse
    rw [hLookup]
    exact mini_model_eval_apply_not_value_canonical M v

/-- Value-level `dt_sel` preserves canonicality. -/
private theorem mini_model_eval_dt_sel_canonical
    (M : SmtModel)
    (hM : model_total_typed M)
    (s : native_String)
    (d : SmtDatatype)
    (n m : native_Nat)
    {v : SmtValue}
    (hvTy : __smtx_typeof_value v = SmtType.Datatype s d)
    (hv : __smtx_value_canonical v) :
    __smtx_value_canonical (__smtx_model_eval_dt_sel M s d n m v) := by
  unfold __smtx_model_eval_dt_sel
  cases hEq : native_veq (__vsm_apply_head v) (SmtValue.DtCons s d n)
  · simpa [native_ite, hEq] using
      mini_model_eval_dt_sel_wrong_canonical M hM s d n m v hvTy
  · simpa [native_ite, hEq] using
      mini_vsm_apply_arg_nth_canonical (v := v) (n := m)
        (npos := __smtx_dt_num_sels d n) hv

mutual

/-- Induction lemma proving type preservation for supported SMT terms in total typed models. -/
private theorem supported_type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  cases hs with
  | boolean b =>
      exact typeof_value_model_eval_boolean M b
  | numeral n =>
      exact typeof_value_model_eval_numeral M n
  | rational q =>
      exact typeof_value_model_eval_rational M q
  | string s =>
      exact typeof_value_model_eval_string M s
  | binary w n =>
      exact typeof_value_model_eval_binary M w n ht
  | var s T hT =>
      exact typeof_value_model_eval_var M hM s T hT ht
  | uconst s T hT =>
      exact typeof_value_model_eval_uconst M hM s T hT ht
  | ite htc hsc ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_ite M _ _ _ ht
        (supported_type_preservation M hM _ htc hsc)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «exists» s T body =>
      exact typeof_value_model_eval_exists M s T body ht
  | «forall» s T body =>
      exact typeof_value_model_eval_forall M s T body ht
  | choice s T body hChoice =>
      exact typeof_value_model_eval_choice M hM M s T body ht
  | bind s T x1 x2 hbt hs1 hs2 =>
      have ht1 : term_has_non_none_type x1 := bind_arg1_non_none_of_non_none ht
      have ht2 : term_has_non_none_type x2 := bind_arg2_non_none_of_non_none ht
      have hTx1 : __smtx_typeof x1 = T := bind_arg1_type_of_non_none ht
      have hWf : __smtx_type_wf T = true := bind_binder_type_wf_of_non_none ht
      have hx1ty : __smtx_typeof_value (__smtx_model_eval M x1) = __smtx_typeof x1 :=
        supported_type_preservation M hM x1 ht1 hs1
      have hx1canon : __smtx_value_canonical (__smtx_model_eval M x1) :=
        canonical_of_supported M hM x1 ht1 hs1
      have hM' : model_total_typed (native_model_push M s T (__smtx_model_eval M x1)) :=
        model_total_typed_push hM s T (__smtx_model_eval M x1) hWf (hx1ty.trans hTx1) hx1canon
      exact typeof_value_model_eval_bind M s T x1 x2 ht
        (supported_type_preservation _ hM' x2 ht2 hs2)
  | map_diff ht1 hs1 ht2 hs2 hDefault =>
      exact typeof_value_model_eval_map_diff M _ _ ht
        (fun {A} hA => (hDefault (A := A) hA).1)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | seq_diff ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_seq_diff M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «not» ht1 hs1 =>
      exact typeof_value_model_eval_not M _ ht
        (supported_type_preservation M hM _ ht1 hs1)
  | «or» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_or M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «and» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_and M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | «imp» ht1 hs1 ht2 hs2 =>
      exact typeof_value_model_eval_imp M _ _ ht
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  | eq t1 t2 =>
      exact typeof_value_model_eval_eq M t1 t2 ht
  | dt_cons s d i =>
      exact typeof_value_model_eval_dt_cons M s d i ht
  | dt_sel ht1 hT hWrongMapWF htx hsx =>
      exact typeof_value_model_eval_dt_sel M hM _ _ _ _ _ ht1 hWrongMapWF hT
        (supported_type_preservation M hM _ htx hsx)
  | dt_tester s d i x =>
      exact typeof_value_model_eval_dt_tester M s d i x ht
  | @apply f x hTy hEval htf hsf htx hsx =>
      have hTy' :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTy
        exact hTy
      have hNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTy']
        exact hNone
      rw [hEval M, hTy']
      exact typeof_value_model_eval_apply_generic M hM f x hNN
        (supported_type_preservation M hM f htf hsf)
        (supported_type_preservation M hM x htx hsx)

/-- Canonicity preservation for supported SMT terms in total typed models.  Runs
mutually with `supported_type_preservation` because the `bind` type-preservation
step needs the pushed model to remain `model_total_typed`, which in turn needs
canonicity of the bound value. -/
private theorem canonical_of_supported
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t)
    (hs : supported_preservation_term t) :
    __smtx_value_canonical (__smtx_model_eval M t) := by
  cases hs
  case bind s T x1 x2 hbt hs1 hs2 =>
      have ht1 : term_has_non_none_type x1 := bind_arg1_non_none_of_non_none ht
      have ht2 : term_has_non_none_type x2 := bind_arg2_non_none_of_non_none ht
      have hTx1 : __smtx_typeof x1 = T := bind_arg1_type_of_non_none ht
      have hWf : __smtx_type_wf T = true := bind_binder_type_wf_of_non_none ht
      have hx1ty : __smtx_typeof_value (__smtx_model_eval M x1) = __smtx_typeof x1 :=
        supported_type_preservation M hM x1 ht1 hs1
      have hx1canon : __smtx_value_canonical (__smtx_model_eval M x1) :=
        canonical_of_supported M hM x1 ht1 hs1
      have hM' : model_total_typed (native_model_push M s T (__smtx_model_eval M x1)) :=
        model_total_typed_push hM s T (__smtx_model_eval M x1) hWf (hx1ty.trans hTx1) hx1canon
      rw [smtx_model_eval_bind_eq]
      exact canonical_of_supported _ hM' x2 ht2 hs2
  case boolean b =>
      simp [__smtx_model_eval, __smtx_value_canonical, __smtx_value_canonical_bool]
  case numeral n =>
      simp [__smtx_model_eval, __smtx_value_canonical, __smtx_value_canonical_bool]
  case rational q =>
      simp [__smtx_model_eval, __smtx_value_canonical, __smtx_value_canonical_bool]
  case string s =>
      have hsValid : native_string_valid s = true := by
        by_cases hV : native_string_valid s = true
        · exact hV
        · exfalso
          apply ht
          have hVF : native_string_valid s = false := by
            cases h : native_string_valid s <;> simp [h] at hV ⊢
          rw [__smtx_typeof.eq_4]
          simp [SmtEval.native_ite, hVF]
      have hCan : __smtx_value_canonical (SmtValue.Seq (native_pack_string s)) := by
        simpa [__smtx_value_canonical, __smtx_value_canonical_bool] using
          mini_seq_canonical_pack_string s hsValid
      rw [__smtx_model_eval.eq_4]
      exact hCan
  case binary w n =>
      cases hw : native_zleq 0 w <;>
        cases hn : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_model_eval, __smtx_typeof, __smtx_value_canonical,
            __smtx_value_canonical_bool, term_has_non_none_type,
            native_and, SmtEval.native_and,
            native_ite, hw, hn] at ht ⊢
  case var s T hT =>
      by_cases hWF : __smtx_type_wf T = true
      · simpa [__smtx_model_eval] using model_total_typed_var_lookup_canonical hM s T hWF
      · have hWF' : __smtx_type_wf T = false := by
          cases hb : __smtx_type_wf T <;> simp [hb] at hWF ⊢
        have hLookup : native_model_var_lookup M s T = SmtValue.NotValue :=
          model_total_typed_var_lookup_uninhabited hM s T hWF'
        simpa [__smtx_model_eval, hLookup] using mini_value_canonical_notValue
  case uconst s T hT =>
      by_cases hWF : __smtx_type_wf T = true
      · simpa [__smtx_model_eval] using model_total_typed_lookup_canonical hM s T hWF
      · have hWF' : __smtx_type_wf T = false := by
          cases hb : __smtx_type_wf T <;> simp [hb] at hWF ⊢
        have hLookup : native_model_lookup M s T = SmtValue.NotValue :=
          model_total_typed_lookup_not_wf hM s T hWF'
        simpa [__smtx_model_eval, hLookup] using mini_value_canonical_notValue
  case ite htc hsc ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_ite_canonical
          (c := __smtx_model_eval M _) (t := __smtx_model_eval M _)
          (e := __smtx_model_eval M _)
          (canonical_of_supported M hM _ ht1 hs1)
          (canonical_of_supported M hM _ ht2 hs2)
  case «exists» s T body =>
      exact mini_value_canonical_of_bool_type
        ((typeof_value_model_eval_exists M s T body ht).trans
          (exists_term_typeof_of_non_none ht))
  case «forall» s T body =>
      exact mini_value_canonical_of_bool_type
        ((typeof_value_model_eval_forall M s T body ht).trans
          (forall_term_typeof_of_non_none ht))
  case choice s T body htc =>
      simpa [__smtx_model_eval] using mini_native_eval_tchoice_canonical M s T body
  case map_diff ht1 hs1 ht2 hs2 hDefault =>
      exact model_eval_map_diff_canonical M _ _ ht
        (fun {A} hA => (hDefault (A := A) hA).2)
        (supported_type_preservation M hM _ ht1 hs1)
        (supported_type_preservation M hM _ ht2 hs2)
  case seq_diff ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_seq_diff_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case «not» ht1 hs1 =>
      simpa [__smtx_model_eval] using mini_model_eval_not_canonical (__smtx_model_eval M _)
  case «or» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_or_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case «and» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_and_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case «imp» ht1 hs1 ht2 hs2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_imp_canonical (__smtx_model_eval M _) (__smtx_model_eval M _)
  case eq t1 t2 =>
      simpa [__smtx_model_eval] using
        mini_model_eval_eq_canonical (__smtx_model_eval M t1) (__smtx_model_eval M t2)
  case dt_cons s d i =>
      simp [__smtx_model_eval, __smtx_value_canonical, __smtx_value_canonical_bool]
  case dt_sel s d i j x htSel hT hWrongMapWF htx hsx =>
      have hxTy :=
        (supported_type_preservation M hM _ htx hsx).trans
          (dt_sel_arg_datatype_of_non_none htSel)
      simpa [__smtx_model_eval] using
        mini_model_eval_dt_sel_canonical M hM s d i j hxTy
          (canonical_of_supported M hM _ htx hsx)
  case dt_tester s d i x =>
      simp [__smtx_model_eval, __smtx_model_eval_dt_tester, __smtx_value_canonical,
        __smtx_value_canonical_bool]
  case apply f x hTyApp hEval htf hsf htx hsx =>
      have hf := canonical_of_supported M hM f htf hsf
      have hx := canonical_of_supported M hM x htx hsx
      have hTy' :
          __smtx_typeof (SmtTerm.Apply f x) =
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) := by
        unfold generic_apply_type at hTyApp
        exact hTyApp
      have hApplyNN :
          __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
        intro hNone
        apply ht
        rw [hTy']
        exact hNone
      rcases typeof_apply_non_none_cases hApplyNN with ⟨A, B, hHeadTerm, hX, hA, hB⟩
      have hPresF :
          __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f :=
        supported_type_preservation M hM f htf hsf
      have hPresX :
          __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x :=
        supported_type_preservation M hM x htx hsx
      have hxTy : __smtx_typeof_value (__smtx_model_eval M x) = A := by
        simpa [hX] using hPresX
      have hHeadVal :
          __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B ∨
            __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
        cases hHeadTerm with
        | inl hFun => exact Or.inl (by simpa [hFun] using hPresF)
        | inr hDtc => exact Or.inr (by simpa [hDtc] using hPresF)
      have hFunWF :
          __smtx_typeof_value (__smtx_model_eval M f) = SmtType.FunType A B ->
            __smtx_type_wf (SmtType.FunType A B) = true := by
        intro hValFun
        cases hHeadTerm with
        | inl hFun => exact smt_fun_wf_of_non_none_type f A B hFun
        | inr hDtc =>
            have hValDtc :
                __smtx_typeof_value (__smtx_model_eval M f) = SmtType.DtcAppType A B := by
              simpa [hDtc] using hPresF
            rw [hValFun] at hValDtc
            cases hValDtc
      simpa [hEval M] using
        mini_model_eval_apply_canonical M hM
          (f := __smtx_model_eval M f)
          (x := __smtx_model_eval M x)
          (hHead := hHeadVal)
          (hFunWF := hFunWF)
          (hxTy := hxTy)
          hf hx

end

theorem generic_apply_subterms_non_none
    {f x : SmtTerm}
    (hTy : generic_apply_type f x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x)) :
    term_has_non_none_type f ∧ term_has_non_none_type x := by
  have hApply : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None := by
    unfold generic_apply_type at hTy
    unfold term_has_non_none_type at ht
    rw [hTy] at ht
    exact ht
  rcases typeof_apply_non_none_cases hApply with ⟨A, B, hF, hX, hA, hB⟩
  constructor
  · unfold term_has_non_none_type
    rcases hF with hF | hF <;> rw [hF] <;> simp
  · unfold term_has_non_none_type
    rw [hX]
    exact hA

/-- Derives inhabitedness of the selector result type from a non-`None` selector term. -/
theorem dt_sel_term_inhabited_of_non_none
    {s : native_String}
    {d : SmtDatatype}
    {i j : native_Nat}
    {x : SmtTerm}
    (ht : term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) :
    type_inhabited (__smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x)) := by
  have hResTy :
      __smtx_typeof (SmtTerm.Apply (SmtTerm.DtSel s d i j) x) =
        __smtx_ret_typeof_sel s d i j :=
    dt_sel_term_typeof_of_non_none ht
  have hGuardNN :
      __smtx_typeof_guard_wf
          (__smtx_ret_typeof_sel s d i j)
          (__smtx_typeof_apply
            (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
            (__smtx_typeof x)) ≠
        SmtType.None := by
    simpa [term_has_non_none_type, __smtx_typeof] using ht
  have hResInh : type_inhabited (__smtx_ret_typeof_sel s d i j) :=
    smtx_typeof_guard_wf_inhabited_of_non_none
      (__smtx_ret_typeof_sel s d i j)
      (__smtx_typeof_apply
        (SmtType.FunType (SmtType.Datatype s d) (__smtx_ret_typeof_sel s d i j))
        (__smtx_typeof x))
      hGuardNN
  rwa [hResTy]

/-- Packages the generic-application constructor once the recursive support facts are available. -/
theorem supported_generic_apply_of_non_none
    {f x : SmtTerm}
    (hTy : generic_apply_type f x)
    (hEval : generic_apply_eval f x)
    (ht : term_has_non_none_type (SmtTerm.Apply f x))
    (hsf : supported_preservation_term f)
    (hsx : supported_preservation_term x) :
    supported_preservation_term (SmtTerm.Apply f x) := by
  have hArgs := generic_apply_subterms_non_none hTy ht
  exact supported_preservation_term.apply hTy hEval hArgs.1 hsf hArgs.2 hsx

/-- Generic application facts for heads other than datatype selectors/testers. -/
theorem generic_apply_facts_of_not_special
    {f x : SmtTerm}
    (hNoSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hNoTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x ∧ generic_apply_eval f x := by
  constructor
  · unfold generic_apply_type
    cases f <;> simp [__smtx_typeof]
    · exact False.elim (hNoSel _ _ _ _ rfl)
    · exact False.elim (hNoTester _ _ _ rfl)
  · intro M
    cases f with
    | DtSel s d i j =>
        exact False.elim (hNoSel s d i j rfl)
    | DtTester s d i =>
        exact False.elim (hNoTester s d i rfl)
    | _ =>
        simp [__smtx_model_eval]

/-- Every non-`None` SMT term lies in the supported preservation fragment. -/
theorem supported_preservation_term_of_non_none :
    ∀ t : SmtTerm, term_has_non_none_type t -> supported_preservation_term t := by
  let rec go (t : SmtTerm) (ht : term_has_non_none_type t) : supported_preservation_term t := by
    match t with
    | SmtTerm.None =>
        have hNone : __smtx_typeof SmtTerm.None = SmtType.None := by
          rw [__smtx_typeof.eq_def]
        exact False.elim (ht hNone)
    | SmtTerm.Boolean b =>
        exact supported_preservation_term.boolean b
    | SmtTerm.Numeral n =>
        exact supported_preservation_term.numeral n
    | SmtTerm.Rational q =>
        exact supported_preservation_term.rational q
    | SmtTerm.String s =>
        exact supported_preservation_term.string s
    | SmtTerm.Binary w n =>
        exact supported_preservation_term.binary w n
    | SmtTerm.Var s T =>
        have hTNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
          intro hNone
          apply ht
          simpa [__smtx_typeof] using hNone
        exact supported_preservation_term.var s T
          (smtx_typeof_guard_wf_inhabited_of_non_none T T hTNN)
    | SmtTerm.ite c t1 t2 =>
        rcases ite_args_of_non_none ht with ⟨T, hc, h1, h2, hT⟩
        have htc : term_has_non_none_type c := by
          unfold term_has_non_none_type
          rw [hc]
          simp
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [h1]
          exact hT
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [h2]
          exact hT
        exact supported_preservation_term.ite
          htc (go c htc) ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.eq t1 t2 =>
        exact supported_preservation_term.eq t1 t2
    | SmtTerm.exists s T body =>
        exact supported_preservation_term.exists s T body
    | SmtTerm.forall s T body =>
        exact supported_preservation_term.forall s T body
    | SmtTerm.choice s T body =>
        exact supported_preservation_term.choice s T body ht
    | SmtTerm.bind s T x1 x2 =>
        have ht1 : term_has_non_none_type x1 := bind_arg1_non_none_of_non_none ht
        have ht2 : term_has_non_none_type x2 := bind_arg2_non_none_of_non_none ht
        exact supported_preservation_term.bind s T x1 x2 ht (go x1 ht1) (go x2 ht2)
    | SmtTerm.map_diff t1 t2 =>
        rcases map_diff_args_of_non_none ht with hMap | hSet
        · rcases hMap with ⟨A, B, h1, h2, hTy⟩
          have ht1 : term_has_non_none_type t1 := by
            unfold term_has_non_none_type
            rw [h1]
            simp
          have ht2 : term_has_non_none_type t2 := by
            unfold term_has_non_none_type
            rw [h2]
            simp
          exact supported_preservation_term.map_diff
            ht1 (go t1 ht1) ht2 (go t2 ht2)
            (map_diff_default_typed_canonical_of_non_none ht)
        · rcases hSet with ⟨A, h1, h2, hTy⟩
          have ht1 : term_has_non_none_type t1 := by
            unfold term_has_non_none_type
            rw [h1]
            simp
          have ht2 : term_has_non_none_type t2 := by
            unfold term_has_non_none_type
            rw [h2]
            simp
          exact supported_preservation_term.map_diff
            ht1 (go t1 ht1) ht2 (go t2 ht2)
            (map_diff_default_typed_canonical_of_non_none ht)
    | SmtTerm.seq_diff t1 t2 =>
        rcases seq_diff_args_of_non_none ht with ⟨A, h1, h2, hTy⟩
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [h1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [h2]
          simp
        exact supported_preservation_term.seq_diff
          ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.DtCons s d i =>
        exact supported_preservation_term.dt_cons s d i
    | SmtTerm.DtSel s d i j =>
        have hNone : __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := by
          rw [__smtx_typeof.eq_def]
        exact False.elim (ht hNone)
    | SmtTerm.DtTester s d i =>
        have hNone : __smtx_typeof (SmtTerm.DtTester s d i) = SmtType.None := by
          rw [__smtx_typeof.eq_def]
        exact False.elim (ht hNone)
    | SmtTerm.UConst s T =>
        have hTNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
          intro hNone
          apply ht
          simpa [__smtx_typeof] using hNone
        exact supported_preservation_term.uconst s T
          (smtx_typeof_guard_wf_inhabited_of_non_none T T hTNN)
    | SmtTerm.not t =>
        have hArg : __smtx_typeof t = SmtType.Bool := by
          unfold term_has_non_none_type at ht
          rw [typeof_not_eq] at ht
          cases h : __smtx_typeof t <;>
            simp [native_ite, native_Teq, h] at ht
          rfl
        have hArgNN : term_has_non_none_type t := by
          unfold term_has_non_none_type
          rw [hArg]
          simp
        exact supported_preservation_term.not hArgNN (go t hArgNN)
    | SmtTerm.or t1 t2 =>
        have hArgs :=
          bool_binop_args_bool_of_non_none (op := SmtTerm.or) (typeof_or_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [hArgs.1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [hArgs.2]
          simp
        exact supported_preservation_term.or ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.and t1 t2 =>
        have hArgs :=
          bool_binop_args_bool_of_non_none (op := SmtTerm.and) (typeof_and_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [hArgs.1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [hArgs.2]
          simp
        exact supported_preservation_term.and ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.imp t1 t2 =>
        have hArgs :=
          bool_binop_args_bool_of_non_none (op := SmtTerm.imp) (typeof_imp_eq t1 t2) ht
        have ht1 : term_has_non_none_type t1 := by
          unfold term_has_non_none_type
          rw [hArgs.1]
          simp
        have ht2 : term_has_non_none_type t2 := by
          unfold term_has_non_none_type
          rw [hArgs.2]
          simp
        exact supported_preservation_term.imp ht1 (go t1 ht1) ht2 (go t2 ht2)
    | SmtTerm.Apply f x =>
        cases f with
        | «exists» s T body =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.exists s T body) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.exists s T body) hArgs.1)
              (go x hArgs.2)
        | «forall» s T body =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.forall s T body) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.forall s T body) hArgs.1)
              (go x hArgs.2)
        | choice s T body =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.choice s T body) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.choice s T body) hArgs.1)
              (go x hArgs.2)
        | bind s T x1 x2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.bind s T x1 x2) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.bind s T x1 x2) hArgs.1)
              (go x hArgs.2)
        | map_diff t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.map_diff t1 t2) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.map_diff t1 t2) hArgs.1)
              (go x hArgs.2)
        | seq_diff t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.seq_diff t1 t2) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.seq_diff t1 t2) hArgs.1)
              (go x hArgs.2)
        | DtSel s d i j =>
            have htx : term_has_non_none_type x := by
              have hx : __smtx_typeof x = SmtType.Datatype s d :=
                dt_sel_arg_datatype_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht
              unfold term_has_non_none_type
              rw [hx]
              simp
            exact supported_preservation_term.dt_sel
              ht
              (dt_sel_term_inhabited_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht)
              (dt_sel_wrong_map_type_wf_of_non_none (s := s) (d := d) (i := i) (j := j) (x := x) ht)
              htx
              (go x htx)
        | DtTester s d i =>
            exact supported_preservation_term.dt_tester s d i x
        | None =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.None) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go SmtTerm.None hArgs.1)
              (go x hArgs.2)
        | Boolean b =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Boolean b) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Boolean b) hArgs.1)
              (go x hArgs.2)
        | Numeral n =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Numeral n) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Numeral n) hArgs.1)
              (go x hArgs.2)
        | Rational q =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Rational q) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Rational q) hArgs.1)
              (go x hArgs.2)
        | String s =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.String s) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.String s) hArgs.1)
              (go x hArgs.2)
        | Binary w n =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Binary w n) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Binary w n) hArgs.1)
              (go x hArgs.2)
        | Apply f1 x1 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Apply f1 x1) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Apply f1 x1) hArgs.1)
              (go x hArgs.2)
        | Var s T =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.Var s T) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.Var s T) hArgs.1)
              (go x hArgs.2)
        | ite c t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.ite c t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.ite c t1 t2) hArgs.1)
              (go x hArgs.2)
        | eq t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.eq t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.eq t1 t2) hArgs.1)
              (go x hArgs.2)
        | DtCons s d i =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.DtCons s d i) (x := x)
              (by intro s' d' i' j hEq; cases hEq)
              (by intro s' d' i' hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.DtCons s d i) hArgs.1)
              (go x hArgs.2)
        | UConst s T =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.UConst s T) (x := x)
              (by intro s' d i j hEq; cases hEq)
              (by intro s' d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.UConst s T) hArgs.1)
              (go x hArgs.2)
        | not t =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.not t) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.not t) hArgs.1)
              (go x hArgs.2)
        | or t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.or t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.or t1 t2) hArgs.1)
              (go x hArgs.2)
        | and t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.and t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.and t1 t2) hArgs.1)
              (go x hArgs.2)
        | imp t1 t2 =>
            have hApp := generic_apply_facts_of_not_special (f := SmtTerm.imp t1 t2) (x := x)
              (by intro s d i j hEq; cases hEq)
              (by intro s d i hEq; cases hEq)
            have hArgs := generic_apply_subterms_non_none hApp.1 ht
            exact supported_generic_apply_of_non_none hApp.1 hApp.2 ht
              (go (SmtTerm.imp t1 t2) hArgs.1)
              (go x hArgs.2)
  exact go

/-- Main type-preservation theorem for evaluation of non-`None` SMT terms in total typed models. -/
theorem type_preservation
    (M : SmtModel)
    (hM : model_total_typed M)
    (t : SmtTerm)
    (ht : term_has_non_none_type t) :
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  exact supported_type_preservation M hM t ht
    (supported_preservation_term_of_non_none t ht)

/-- Backwards-compatible wrapper for `type_preservation`. -/
theorem smt_model_eval_preserves_type_of_non_none
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
    term_has_non_none_type t ->
    __smtx_typeof_value (__smtx_model_eval M t) = __smtx_typeof t := by
  intro ht
  exact type_preservation M hM t ht

/-- States that evaluating a Boolean-typed SMT term yields a Boolean value. -/
theorem smt_model_eval_bool_is_boolean
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) :
  __smtx_typeof t = SmtType.Bool ->
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  intro hTy
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t (by
        unfold term_has_non_none_type
        rw [hTy]
        simp)
  exact bool_value_canonical hPres

/-- Derives SMT evaluation type preservation for terms in the supported fragment. -/
theorem smt_model_eval_preserves_type_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm) (T : SmtType)
    (hTy : __smtx_typeof t = T)
    (hNonNone : T ≠ SmtType.None)
    (_hs : supported_preservation_term t) :
  __smtx_typeof_value (__smtx_model_eval M t) = T := by
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact hNonNone
  simpa [hTy] using
    type_preservation M hM t hNN

/-- Derives Boolean-value evaluation for supported Boolean-typed SMT terms. -/
theorem smt_model_eval_bool_is_boolean_of_supported
    (M : SmtModel) (hM : model_total_typed M)
    (t : SmtTerm)
    (hTy : __smtx_typeof t = SmtType.Bool)
    (hs : supported_preservation_term t) :
  ∃ b : Bool, __smtx_model_eval M t = SmtValue.Boolean b := by
  have hPres :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Bool :=
    smt_model_eval_preserves_type_of_supported M hM t SmtType.Bool hTy (by simp) hs
  exact bool_value_canonical hPres


end Smtm
