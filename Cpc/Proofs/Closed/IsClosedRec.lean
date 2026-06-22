import Lean
import Cpc.Proofs.Common
import Cpc.Proofs.Assumptions
import Cpc.Proofs.Closed.Support
import Cpc.Proofs.TypePreservation.Full

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

/-- Raw EO binder lists do not themselves translate to well-typed SMT terms. -/
theorem smtx_typeof_eo_list_cons_eq_none (v vs : Term) :
  __smtx_typeof
      (__eo_to_smt (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) =
    SmtType.None :=
by
  change
    __smtx_typeof
        (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt v))
          (__eo_to_smt vs)) =
      SmtType.None
  exact TranslationProofs.typeof_apply_apply_none_head_eq
    (__eo_to_smt v) (__eo_to_smt vs)

/-- The unfolded SMT translation of a raw EO binder list has type `None`. -/
theorem smtx_typeof_unfolded_eo_list_cons_eq_none (v vs : Term) :
  __smtx_typeof
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt v))
        (__eo_to_smt vs)) =
    SmtType.None :=
by
  exact TranslationProofs.typeof_apply_apply_none_head_eq
    (__eo_to_smt v) (__eo_to_smt vs)

/-- Datatype constructors with a `None` field are not well-formed. -/
theorem smtx_dt_cons_wf_rec_cons_none_eq_false
    (c : SmtDatatypeCons) (refs : RefList) :
  __smtx_dt_cons_wf_rec (SmtDatatypeCons.cons SmtType.None c) refs =
    false :=
by
  by_cases hInhabited : native_inhabited_type SmtType.None = true
  · simp [__smtx_dt_cons_wf_rec, __smtx_type_wf_rec, hInhabited,
      native_ite]
  · simp [__smtx_dt_cons_wf_rec, hInhabited, native_ite]

set_option maxHeartbeats 50000000 in
/--
Non-quantifier `UOp` heads cannot translate to a well-typed SMT term when
the first argument is the raw EO binder-list shape used by `__is_closed_rec`.
-/
theorem smtx_typeof_uop_eo_list_cons_apply_eq_none
    {op : UserOp} (hForall : op ≠ UserOp.forall)
    (hExists : op ≠ UserOp.exists) (v vs body : Term) :
  __smtx_typeof
      (__eo_to_smt
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) =
    SmtType.None :=
by
  cases op
  case «forall» =>
    exact False.elim (hForall rfl)
  case «exists» =>
    exact False.elim (hExists rfl)
  all_goals
    have hNeg : native_zleq 0 (native_zneg 1) = false := by
      native_decide
    dsimp only [__eo_to_smt]
    simp [smtx_typeof_unfolded_eo_list_cons_eq_none, __smtx_typeof,
      __smtx_typeof_apply, __smtx_typeof_eq, __smtx_typeof_guard,
      __smtx_typeof_guard_wf, __smtx_typeof_ite, __smtx_typeof_bv_op_1,
      __smtx_typeof_bv_op_1_ret, __smtx_typeof_bv_op_2,
      __smtx_typeof_bv_op_2_ret, __smtx_typeof_arith_overload_op_1,
      __smtx_typeof_arith_overload_op_2,
      __smtx_typeof_arith_overload_op_2_ret, __smtx_typeof_seq_op_1,
      __smtx_typeof_seq_op_1_ret, __smtx_typeof_seq_op_2,
      __smtx_typeof_seq_op_2_ret, __smtx_typeof_seq_op_3,
      __smtx_typeof_sets_op_2, __smtx_typeof_sets_op_2_ret,
      __smtx_typeof_select, __smtx_typeof_store, __smtx_typeof_concat,
      __smtx_typeof_str_substr, __smtx_typeof_str_indexof,
      __smtx_typeof_str_at, __smtx_typeof_str_update,
      __smtx_typeof_re_exp, __smtx_typeof_re_loop, __smtx_typeof_seq_nth,
      __smtx_typeof_set_member, __smtx_typeof_map_diff,
      __smtx_typeof_int_to_bv, __smtx_typeof_choice_nth,
      __eo_to_smt_array_deq_diff,
      __eo_to_smt_sets_deq_diff, __eo_to_smt_set_insert,
      __eo_to_smt_tuple_prepend, __eo_to_smt_tuple_prepend_of_type,
      __eo_to_smt_set_elem_type, __eo_to_smt_typed_list_elem_type,
      __smtx_bv_sizeof_type, __smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, __smtx_dt_wf_rec, __smtx_dt_cons_wf_rec,
      __smtx_dt_substitute, __smtx_dtc_substitute, __smtx_type_substitute,
      __smtx_typeof_dt_cons_rec, smtx_dt_cons_wf_rec_cons_none_eq_false,
      hNeg, native_ite, native_Teq, native_and]
  case tuple_unit =>
    by_cases hCond :
        native_inhabited_type
              (SmtType.Datatype (native_string_lit "@Tuple")
                (SmtDatatype.sum SmtDatatypeCons.unit SmtDatatype.null)) =
            true ∧
          native_reflist_contains native_reflist_nil
              (native_string_lit "@Tuple") =
            false
    · simp [hCond, __smtx_typeof_apply]
    · simp [hCond, __smtx_typeof_apply]
  case tuple =>
    cases hBody : __smtx_typeof (__eo_to_smt body)
    all_goals
      try
        simp [hBody, smtx_typeof_unfolded_eo_list_cons_eq_none,
          smtx_dt_cons_wf_rec_cons_none_eq_false, __smtx_typeof, native_ite,
          native_Teq, native_and]
    case Datatype s d =>
      cases d
      all_goals
        try
          simp [hBody, smtx_typeof_unfolded_eo_list_cons_eq_none,
            smtx_dt_cons_wf_rec_cons_none_eq_false, __smtx_typeof,
            native_ite, native_Teq, native_and]
      case sum c dTail =>
        cases dTail
        all_goals
          try
            simp [hBody, smtx_typeof_unfolded_eo_list_cons_eq_none,
              smtx_dt_cons_wf_rec_cons_none_eq_false, __smtx_typeof,
              native_ite, native_Teq, native_and]
  case set_member =>
    cases hBody : __smtx_typeof (__eo_to_smt body)
    all_goals simp [hBody, native_Teq]
    case Set a =>
      have hBodyNonNone : term_has_non_none_type (__eo_to_smt body) := by
        unfold term_has_non_none_type
        rw [hBody]
        intro hNone
        cases hNone
      have hNoNone :=
        term_type_has_no_none_components_of_non_none
          (__eo_to_smt body) hBodyNonNone
      have hElemNoNone : type_has_no_none_components a := by
        simpa [hBody, type_has_no_none_components] using hNoNone
      intro hNone
      exact type_has_no_none_components_non_none hElemNoNone hNone.symm

/--
If the broad `__is_closed_rec` binder-list branch sees a term that has a
well-typed SMT translation, then its head is an actual quantifier.
-/
theorem is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  op = UserOp.forall ∨ op = UserOp.exists :=
by
  by_cases hForall : op = UserOp.forall
  · exact Or.inl hForall
  by_cases hExists : op = UserOp.exists
  · exact Or.inr hExists
  exfalso
  unfold eoHasSmtTranslation at hTrans
  exact hTrans
    (smtx_typeof_uop_eo_list_cons_apply_eq_none hForall hExists v vs body)

theorem is_closed_rec_uop_list_branch_head_term_quantifier_of_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  Term.UOp op = Term.UOp UserOp.forall ∨
    Term.UOp op = Term.UOp UserOp.exists :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · exact Or.inl (by rw [hForall])
  · exact Or.inr (by rw [hExists])

/--
On a well-formed EO variable environment, the raw list-indexing test used by
`__is_closed_rec` agrees with `__eo_is_closed_rec`'s direct recursive lookup.
-/
theorem eo_list_find_rec_var_nonneg_eq_eo_is_closed_rec
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (s : native_String) (T : Term) (n : native_Int)
    (hNonneg : 0 ≤ n) :
  __eo_not
      (__eo_is_neg
        (__eo_list_find_rec env (Term.Var (Term.String s) T)
          (Term.Numeral n))) =
    __eo_is_closed_rec (Term.Var (Term.String s) T) env :=
by
  induction hEnv generalizing n with
  | nil =>
      simp [__eo_list_find_rec, __eo_is_neg, __eo_not,
        __eo_is_closed_rec, native_zlt, native_not]
  | cons hTail ih =>
      rename_i s' T' env' vars'
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · have hNotLtProp : ¬ n < 0 := by
          exact Int.not_lt_of_ge hNonneg
        have hNotLt : native_zlt n 0 = false := by
          simp [native_zlt, hNotLtProp]
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq.symm]
        have hClosedEq :
            __eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T') =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq]
        simp [__eo_list_find_rec, __eo_is_closed_rec, hFindEq,
          hClosedEq, __eo_ite, __eo_is_neg, __eo_not, native_ite,
          native_teq, native_not, hNotLt]
      · have hVarEqSymm :
            Term.Var (Term.String s) T ≠
              Term.Var (Term.String s') T' := by
          intro h
          exact hVarEq h.symm
        have hFindEq :
            __eo_eq (Term.Var (Term.String s') T')
                (Term.Var (Term.String s) T) =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEqSymm]
        have hClosedEq :
            __eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T') =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEq]
        have hSuccNonneg : 0 ≤ native_zplus n 1 := by
          simpa [native_zplus] using
            Int.add_nonneg hNonneg (by decide : (0 : Int) ≤ 1)
        simpa [__eo_list_find_rec, __eo_is_closed_rec, __eo_ite,
          __eo_add, native_ite, native_teq, hFindEq, hClosedEq]
          using ih (native_zplus n 1) hSuccNonneg

/--
For variables and well-formed EO variable environments, `__is_closed_rec` and
`__eo_is_closed_rec` are definitionally different but extensionally identical.
-/
theorem is_closed_rec_var_eq_eo_is_closed_rec_var
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (s : native_String) (T : Term) :
  __is_closed_rec (Term.Var (Term.String s) T) env =
    __eo_is_closed_rec (Term.Var (Term.String s) T) env :=
by
  cases hEnv with
  | nil =>
      have hEnvNil : EoSmtVarEnv Term.__eo_List_nil [] :=
        EoSmtVarEnv.nil
      have hList := hEnvNil.is_list
      simpa [__is_closed_rec, __eo_list_find, __eo_requires, hList,
        native_ite, native_teq]
        using
          eo_list_find_rec_var_nonneg_eq_eo_is_closed_rec
            hEnvNil s T 0
            (show (0 : native_Int) ≤ (0 : native_Int) by
              exact Int.le_refl 0)
  | cons hTail =>
      rename_i s' T' env' vars'
      have hEnvCons :
          EoSmtVarEnv
            (Term.Apply
              (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s') T')) env')
            ((s', __eo_to_smt_type T') :: vars') :=
        EoSmtVarEnv.cons hTail
      have hList := hEnvCons.is_list
      simpa [__is_closed_rec, __eo_list_find, __eo_requires, hList,
        native_ite, native_teq]
        using
          eo_list_find_rec_var_nonneg_eq_eo_is_closed_rec
            hEnvCons s T 0
            (show (0 : native_Int) ≤ (0 : native_Int) by
              exact Int.le_refl 0)

theorem eo_is_closed_rec_var_is_boolean
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (s : native_String) (T : Term) :
  ∃ b,
    __eo_is_closed_rec (Term.Var (Term.String s) T) env =
      Term.Boolean b :=
by
  induction hEnv with
  | nil =>
      exact ⟨false, by simp [__eo_is_closed_rec]⟩
  | cons hTail ih =>
      rename_i s' T' env' vars'
      by_cases hVarEq :
          Term.Var (Term.String s') T' =
            Term.Var (Term.String s) T
      · have hClosedEq :
            __eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T') =
              Term.Boolean true := by
          simp [__eo_eq, native_teq, hVarEq]
        exact ⟨true, by
          simp [__eo_is_closed_rec, __eo_ite, hClosedEq, native_ite,
            native_teq]⟩
      · have hClosedEq :
            __eo_eq (Term.Var (Term.String s) T)
                (Term.Var (Term.String s') T') =
              Term.Boolean false := by
          simp [__eo_eq, native_teq, hVarEq]
        rcases ih with ⟨b, hb⟩
        exact ⟨b, by
          simp [__eo_is_closed_rec, __eo_ite, hClosedEq, hb, native_ite,
            native_teq]⟩

theorem is_closed_rec_var_eq_and_bool
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (s : native_String) (T : Term) :
  __is_closed_rec (Term.Var (Term.String s) T) env =
    __eo_is_closed_rec (Term.Var (Term.String s) T) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Var (Term.String s) T) env =
        Term.Boolean b :=
by
  exact ⟨is_closed_rec_var_eq_eo_is_closed_rec_var hEnv s T,
    eo_is_closed_rec_var_is_boolean hEnv s T⟩

/--
A Boolean SMT existential chain can only have come from an EO list of variables.
This strengthens `eo_typeof_var_list_of_exists_bool` with the exact environment
relation used by the closedness proofs.
-/
theorem eo_smt_var_env_of_eo_to_smt_exists_bool
    (xs : Term) (body : SmtTerm) :
  __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool ->
    ∃ vars, EoSmtVarEnv xs vars :=
by
  intro hTy
  cases hxs : xs
  case __eo_List_nil =>
    subst hxs
    exact ⟨[], EoSmtVarEnv.nil⟩
  case Apply f a =>
    subst hxs
    cases hf : f
    case Apply g y =>
      subst hf
      cases hg : g
      case __eo_List_cons =>
        subst hg
        cases hy : y
        case Var name T =>
          subst hy
          cases hname : name
          case String s =>
            subst hname
            have hExistsTy :
                __smtx_typeof
                    (SmtTerm.exists s (__eo_to_smt_type T)
                      (__eo_to_smt_exists a body)) =
                  SmtType.Bool := by
              simpa [__eo_to_smt_exists] using hTy
            have hNN :
                term_has_non_none_type
                  (SmtTerm.exists s (__eo_to_smt_type T)
                    (__eo_to_smt_exists a body)) := by
              unfold term_has_non_none_type
              rw [hExistsTy]
              simp
            have hSub :
                __smtx_typeof (__eo_to_smt_exists a body) =
                  SmtType.Bool := by
              simpa using exists_body_bool_of_non_none hNN
            rcases eo_smt_var_env_of_eo_to_smt_exists_bool a body hSub with
              ⟨vars, hEnv⟩
            exact ⟨(s, __eo_to_smt_type T) :: vars,
              EoSmtVarEnv.cons hEnv⟩
          all_goals
            subst hname
            have hNone := hTy
            simp [__eo_to_smt_exists, __smtx_typeof] at hNone
        all_goals
          subst hy
          have hNone := hTy
          simp [__eo_to_smt_exists, __smtx_typeof] at hNone
      all_goals
        subst hg
        have hNone := hTy
        simp [__eo_to_smt_exists, __smtx_typeof] at hNone
    all_goals
      subst hf
      have hNone := hTy
      simp [__eo_to_smt_exists, __smtx_typeof] at hNone
  all_goals
    subst hxs
    have hNone := hTy
    simp [__eo_to_smt_exists, __smtx_typeof] at hNone

theorem smtx_typeof_exists_eq_bool_of_non_none
    {s : native_String} {T : SmtType} {body : SmtTerm}
    (hNonNone :
      __smtx_typeof (SmtTerm.exists s T body) ≠ SmtType.None) :
  __smtx_typeof (SmtTerm.exists s T body) = SmtType.Bool :=
by
  exact exists_term_typeof_of_non_none (by
    unfold term_has_non_none_type
    exact hNonNone)

/--
For a nonempty raw EO binder list, non-`None` SMT existential-chain typing
recovers the corresponding EO/SMT variable environment.
-/
theorem eo_smt_var_env_of_eo_to_smt_exists_cons_non_none
    (v vs : Term) (body : SmtTerm)
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) body) ≠
        SmtType.None) :
  ∃ vars,
    EoSmtVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  cases v
  case Var name T =>
    cases name
    case String s =>
      have hBool :
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.Var (Term.String s) T)) vs) body) =
            SmtType.Bool := by
        change
          __smtx_typeof
              (SmtTerm.exists s (__eo_to_smt_type T)
                (__eo_to_smt_exists vs body)) =
            SmtType.Bool
        exact smtx_typeof_exists_eq_bool_of_non_none hNonNone
      exact
        eo_smt_var_env_of_eo_to_smt_exists_bool
          (Term.Apply
            (Term.Apply Term.__eo_List_cons
              (Term.Var (Term.String s) T)) vs)
          body hBool
    all_goals
      exfalso
      apply hNonNone
      simp [__eo_to_smt_exists, __smtx_typeof]
  all_goals
    exfalso
    apply hNonNone
    simp [__eo_to_smt_exists, __smtx_typeof]

theorem smtx_typeof_eo_to_smt_exists_cons_eq_bool_of_non_none
    (v vs : Term) (body : SmtTerm)
    (hNonNone :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) body) ≠
        SmtType.None) :
  __smtx_typeof
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) body) =
    SmtType.Bool :=
by
  cases v
  case Var name T =>
    cases name
    case String s =>
      change
        __smtx_typeof
            (SmtTerm.exists s (__eo_to_smt_type T)
              (__eo_to_smt_exists vs body)) =
          SmtType.Bool
      exact smtx_typeof_exists_eq_bool_of_non_none hNonNone
    all_goals
      exfalso
      apply hNonNone
      simp [__eo_to_smt_exists, __smtx_typeof]
  all_goals
    exfalso
    apply hNonNone
    simp [__eo_to_smt_exists, __smtx_typeof]

theorem smtx_typeof_not_eq_bool_of_non_none
    (t : SmtTerm)
    (hNonNone : __smtx_typeof (SmtTerm.not t) ≠ SmtType.None) :
  __smtx_typeof (SmtTerm.not t) = SmtType.Bool :=
by
  cases hTy : __smtx_typeof t <;>
    rw [typeof_not_eq] at hNonNone ⊢ <;>
    simp [hTy, native_ite, native_Teq] at hNonNone ⊢

theorem smtx_typeof_not_arg_eq_bool
    (t : SmtTerm)
    (hTy : __smtx_typeof (SmtTerm.not t) = SmtType.Bool) :
  __smtx_typeof t = SmtType.Bool :=
by
  cases hArg : __smtx_typeof t <;>
    rw [typeof_not_eq] at hTy <;>
    simp [hArg, native_ite, native_Teq] at hTy ⊢

theorem eo_smt_var_env_of_exists_list_branch_has_smt_translation
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.exists)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoSmtVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  unfold eoHasSmtTranslation at hTrans
  exact
    eo_smt_var_env_of_eo_to_smt_exists_cons_non_none
      v vs (__eo_to_smt body) (by
        change
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                (__eo_to_smt body)) ≠
            SmtType.None at hTrans
        exact hTrans)

theorem eo_smt_var_env_of_forall_list_branch_has_smt_translation
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.forall)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoSmtVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  unfold eoHasSmtTranslation at hTrans
  have hNotBool :
      __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body)))) =
        SmtType.Bool :=
    smtx_typeof_not_eq_bool_of_non_none
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        (SmtTerm.not (__eo_to_smt body)))
      (by
        change
          __smtx_typeof
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                  (SmtTerm.not (__eo_to_smt body)))) ≠
            SmtType.None at hTrans
        exact hTrans)
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (SmtTerm.not (__eo_to_smt body))) =
        SmtType.Bool :=
    smtx_typeof_not_arg_eq_bool
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        (SmtTerm.not (__eo_to_smt body)))
      hNotBool
  exact
    eo_smt_var_env_of_eo_to_smt_exists_bool
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (SmtTerm.not (__eo_to_smt body)) hExistsBool

theorem eo_smt_var_env_of_uop_list_branch_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars,
    EoSmtVarEnv
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) vars :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    exact eo_smt_var_env_of_forall_list_branch_has_smt_translation hTrans
  · subst op
    exact eo_smt_var_env_of_exists_list_branch_has_smt_translation hTrans

theorem eo_smt_var_env_concat_of_uop_list_branch_has_smt_translation
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  ∃ vars',
    EoSmtVarEnv
      (__eo_list_concat Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env)
      vars' :=
by
  rcases
    eo_smt_var_env_of_uop_list_branch_has_smt_translation hTrans with
    ⟨binderVars, hBinderEnv⟩
  exact ⟨binderVars ++ vars, EoSmtVarEnv.concat hBinderEnv hEnv⟩

theorem body_has_smt_translation_of_exists_list_branch_has_smt_translation
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.exists)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body :=
by
  unfold eoHasSmtTranslation at hTrans ⊢
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (__eo_to_smt body)) =
        SmtType.Bool :=
    smtx_typeof_eo_to_smt_exists_cons_eq_bool_of_non_none
      v vs (__eo_to_smt body) (by
        change
          __smtx_typeof
              (__eo_to_smt_exists
                (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                (__eo_to_smt body)) ≠
            SmtType.None at hTrans
        exact hTrans)
  have hBodyBool :
      __smtx_typeof (__eo_to_smt body) = SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (__eo_to_smt body) hExistsBool
  rw [hBodyBool]
  intro h
  cases h

theorem body_has_smt_translation_of_forall_list_branch_has_smt_translation
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.forall)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body :=
by
  unfold eoHasSmtTranslation at hTrans ⊢
  have hNotBool :
      __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
              (SmtTerm.not (__eo_to_smt body)))) =
        SmtType.Bool :=
    smtx_typeof_not_eq_bool_of_non_none
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        (SmtTerm.not (__eo_to_smt body)))
      (by
        change
          __smtx_typeof
              (SmtTerm.not
                (__eo_to_smt_exists
                  (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
                  (SmtTerm.not (__eo_to_smt body)))) ≠
            SmtType.None at hTrans
        exact hTrans)
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
            (SmtTerm.not (__eo_to_smt body))) =
        SmtType.Bool :=
    smtx_typeof_not_arg_eq_bool
      (__eo_to_smt_exists
        (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
        (SmtTerm.not (__eo_to_smt body)))
      hNotBool
  have hBodyNotBool :
      __smtx_typeof (SmtTerm.not (__eo_to_smt body)) =
        SmtType.Bool :=
    TranslationProofs.eo_to_smt_exists_body_bool_of_bool
      (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
      (SmtTerm.not (__eo_to_smt body)) hExistsBool
  have hBodyBool :
      __smtx_typeof (__eo_to_smt body) = SmtType.Bool :=
    smtx_typeof_not_arg_eq_bool (__eo_to_smt body) hBodyNotBool
  rw [hBodyBool]
  intro h
  cases h

theorem body_has_smt_translation_of_uop_list_branch_has_smt_translation
    {op : UserOp} {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body :=
by
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    exact body_has_smt_translation_of_forall_list_branch_has_smt_translation
      hTrans
  · subst op
    exact body_has_smt_translation_of_exists_list_branch_has_smt_translation
      hTrans

theorem body_obligations_of_uop_list_branch_has_smt_translation
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)) :
  eoHasSmtTranslation body ∧
    ∃ vars',
      EoSmtVarEnv
        (__eo_list_concat Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env)
        vars' :=
by
  exact
    ⟨body_has_smt_translation_of_uop_list_branch_has_smt_translation
        hTrans,
      eo_smt_var_env_concat_of_uop_list_branch_has_smt_translation
        hEnv hTrans⟩

theorem eo_and_true_left_eq_of_boolean
    {x : Term} {b : Bool} (h : x = Term.Boolean b) :
  __eo_and (Term.Boolean true) x = x :=
by
  subst x
  cases b <;> simp [__eo_and, native_and]

theorem eo_and_true_right_eq_of_boolean
    {x : Term} {b : Bool} (h : x = Term.Boolean b) :
  __eo_and x (Term.Boolean true) = x :=
by
  subst x
  cases b <;> simp [__eo_and, native_and]

theorem eo_and_true_true :
  __eo_and (Term.Boolean true) (Term.Boolean true) =
    Term.Boolean true :=
by
  simp [__eo_and, native_and]

theorem eo_and_eq_boolean_of_boolean
    {x y : Term} {bx bz : Bool}
    (hx : x = Term.Boolean bx) (hy : y = Term.Boolean bz) :
  ∃ b, __eo_and x y = Term.Boolean b :=
by
  subst x
  subst y
  cases bx <;> cases bz <;>
    simp [__eo_and, native_and]

theorem eo_is_closed_rec_eq_true_of_nat_is_valid
    {idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hValid : __eo_to_smt_nat_is_valid idx = true) :
  __eo_is_closed_rec idx env = Term.Boolean true :=
by
  cases idx <;> simp [__eo_to_smt_nat_is_valid] at hValid
  case Numeral n =>
    cases hEnv <;> simp [__eo_is_closed_rec]

theorem eo_is_closed_rec_eq_true_of_eo_type_valid_rec
    {refs : List native_String} {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hValid : TranslationProofs.eo_type_valid_rec refs T) :
  __eo_is_closed_rec T env = Term.Boolean true :=
by
  let rec go (T : Term) :
      ∀ {refs : List native_String} {env : Term} {vars : List SmtVarKey},
        EoSmtVarEnv env vars ->
          TranslationProofs.eo_type_valid_rec refs T ->
            __eo_is_closed_rec T env = Term.Boolean true :=
  by
    intro refs env vars hEnv hValid
    cases T with
    | Bool =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | DatatypeType s d =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | DatatypeTypeRef s =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | DtcAppType T U =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | USort i =>
        cases hEnv <;> simp [__eo_is_closed_rec]
    | UOp op =>
        cases op <;> cases hEnv <;>
          simp [TranslationProofs.eo_type_valid_rec,
            __eo_is_closed_rec] at hValid ⊢
    | Apply f x =>
        cases f with
        | UOp op =>
            cases op <;>
              cases hEnv <;>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_is_closed_rec] at hValid ⊢
            case BitVec.nil =>
              cases x <;>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_is_closed_rec, __eo_and, native_and] at hValid ⊢
            case BitVec.cons =>
              cases x <;>
                simp [TranslationProofs.eo_type_valid_rec,
                  __eo_is_closed_rec, __eo_and, native_and] at hValid ⊢
            case Seq.nil =>
              have hx := go x EoSmtVarEnv.nil hValid
              simpa [__eo_is_closed_rec, hx, eo_and_true_true]
            case Seq.cons hTail =>
              rename_i s' T' env' vars'
              have hEnvCons := EoSmtVarEnv.cons (s := s') (T := T') hTail
              have hx := go x hEnvCons hValid
              simpa [__eo_is_closed_rec, hx, eo_and_true_true]
            case Set.nil =>
              have hx := go x EoSmtVarEnv.nil hValid
              simpa [__eo_is_closed_rec, hx, eo_and_true_true]
            case Set.cons hTail =>
              rename_i s' T' env' vars'
              have hEnvCons := EoSmtVarEnv.cons (s := s') (T := T') hTail
              have hx := go x hEnvCons hValid
              simpa [__eo_is_closed_rec, hx, eo_and_true_true]
        | Apply g y =>
            cases g with
            | FunType =>
                rcases (by
                    simpa [TranslationProofs.eo_type_valid_rec]
                      using hValid :
                    TranslationProofs.eo_type_valid_rec [] y ∧
                      TranslationProofs.eo_type_valid_rec [] x) with
                  ⟨hyValid, hxValid⟩
                cases hEnv with
                | nil =>
                    have hy := go y EoSmtVarEnv.nil hyValid
                    have hx := go x EoSmtVarEnv.nil hxValid
                    simpa [__eo_is_closed_rec, hy, hx, eo_and_true_true]
                | cons hTail =>
                    rename_i s' T' env' vars'
                    have hEnvCons :=
                      EoSmtVarEnv.cons (s := s') (T := T') hTail
                    have hy := go y hEnvCons hyValid
                    have hx := go x hEnvCons hxValid
                    simpa [__eo_is_closed_rec, hy, hx, eo_and_true_true]
            | UOp op =>
                cases op <;>
                  cases hEnv <;>
                    simp [TranslationProofs.eo_type_valid_rec,
                      __eo_is_closed_rec] at hValid ⊢
                case Array.nil =>
                  rcases (by
                      simpa [TranslationProofs.eo_type_valid_rec]
                        using hValid :
                      TranslationProofs.eo_type_valid_rec [] y ∧
                        TranslationProofs.eo_type_valid_rec [] x) with
                    ⟨hyValid, hxValid⟩
                  have hy := go y EoSmtVarEnv.nil hyValid
                  have hx := go x EoSmtVarEnv.nil hxValid
                  simpa [__eo_is_closed_rec, hy, hx, eo_and_true_true]
                case Array.cons hTail =>
                  rename_i s' T' env' vars'
                  rcases (by
                      simpa [TranslationProofs.eo_type_valid_rec]
                        using hValid :
                      TranslationProofs.eo_type_valid_rec [] y ∧
                        TranslationProofs.eo_type_valid_rec [] x) with
                    ⟨hyValid, hxValid⟩
                  have hEnvCons :=
                    EoSmtVarEnv.cons (s := s') (T := T') hTail
                  have hy := go y hEnvCons hyValid
                  have hx := go x hEnvCons hxValid
                  simpa [__eo_is_closed_rec, hy, hx, eo_and_true_true]
                case Tuple.nil =>
                  rcases (by
                      simpa [TranslationProofs.eo_type_valid_rec]
                        using hValid :
                      TranslationProofs.eo_type_valid_rec [] y ∧
                        TranslationProofs.eo_type_valid_rec [] x ∧
                          __smtx_type_wf
                              (__eo_to_smt_type_tuple
                                (__eo_to_smt_type y) (__eo_to_smt_type x)) =
                            true) with
                    ⟨hyValid, hxValid, _hWf⟩
                  have hy := go y EoSmtVarEnv.nil hyValid
                  have hx := go x EoSmtVarEnv.nil hxValid
                  simpa [__eo_is_closed_rec, hy, hx, eo_and_true_true]
                case Tuple.cons hTail =>
                  rename_i s' T' env' vars'
                  rcases (by
                      simpa [TranslationProofs.eo_type_valid_rec]
                        using hValid :
                      TranslationProofs.eo_type_valid_rec [] y ∧
                        TranslationProofs.eo_type_valid_rec [] x ∧
                          __smtx_type_wf
                              (__eo_to_smt_type_tuple
                                (__eo_to_smt_type y) (__eo_to_smt_type x)) =
                            true) with
                    ⟨hyValid, hxValid, _hWf⟩
                  have hEnvCons :=
                    EoSmtVarEnv.cons (s := s') (T := T') hTail
                  have hy := go y hEnvCons hyValid
                  have hx := go x hEnvCons hxValid
                  simpa [__eo_is_closed_rec, hy, hx, eo_and_true_true]
            | _ =>
                cases hEnv <;>
                  simp [TranslationProofs.eo_type_valid_rec,
                    __eo_is_closed_rec] at hValid
        | _ =>
            cases hEnv <;>
              simp [TranslationProofs.eo_type_valid_rec,
                __eo_is_closed_rec] at hValid
    | _ =>
        cases hEnv <;>
          simp [TranslationProofs.eo_type_valid_rec,
            __eo_is_closed_rec] at hValid
  exact go T hEnv hValid

theorem eo_is_closed_rec_eq_true_of_eo_type_valid
    {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hValid : TranslationProofs.eo_type_valid T) :
  __eo_is_closed_rec T env = Term.Boolean true :=
by
  cases T with
  | UOp op =>
      cases op with
      | RegLan =>
          cases hEnv <;> simp [__eo_is_closed_rec]
      | _ =>
          exact eo_is_closed_rec_eq_true_of_eo_type_valid_rec
            hEnv (by simpa [TranslationProofs.eo_type_valid] using hValid)
  | _ =>
      exact eo_is_closed_rec_eq_true_of_eo_type_valid_rec
        hEnv (by simpa [TranslationProofs.eo_type_valid] using hValid)

theorem eo_type_valid_of_seq_empty_has_smt_translation
    {T : Term}
    (hTrans : eoHasSmtTranslation (Term.UOp1 UserOp1.seq_empty T)) :
  TranslationProofs.eo_type_valid T :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (__eo_to_smt_seq_empty (__eo_to_smt_type T)) ≠
        SmtType.None at hTrans
  cases hTy : __eo_to_smt_type T <;> rw [hTy] at hTrans <;>
    simp [__eo_to_smt_seq_empty] at hTrans
  case Seq A =>
    have hSeqWF : __smtx_type_wf (SmtType.Seq A) = true :=
      Smtm.smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Seq A) (SmtType.Seq A) (by
          simpa [__smtx_typeof] using hTrans)
    exact TranslationProofs.eo_type_valid_of_smt_wf T
      (by simpa [hTy] using hSeqWF)

theorem eo_type_valid_of_set_empty_has_smt_translation
    {T : Term}
    (hTrans : eoHasSmtTranslation (Term.UOp1 UserOp1.set_empty T)) :
  TranslationProofs.eo_type_valid T :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (__eo_to_smt_set_empty (__eo_to_smt_type T)) ≠
        SmtType.None at hTrans
  cases hTy : __eo_to_smt_type T <;> rw [hTy] at hTrans <;>
    simp [__eo_to_smt_set_empty] at hTrans
  case Set A =>
    have hSetWF : __smtx_type_wf (SmtType.Set A) = true :=
      Smtm.smtx_typeof_guard_wf_wf_of_non_none
        (SmtType.Set A) (SmtType.Set A) (by
          simpa [__smtx_typeof] using hTrans)
    exact TranslationProofs.eo_type_valid_of_smt_wf T
      (by simpa [hTy] using hSetWF)

theorem is_closed_rec_seq_empty_eq_eo_is_closed_rec_of_has_smt_translation
    {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp1 UserOp1.seq_empty T)) :
  __is_closed_rec (Term.UOp1 UserOp1.seq_empty T) env =
    __eo_is_closed_rec (Term.UOp1 UserOp1.seq_empty T) env :=
by
  have hClosed :
      __eo_is_closed_rec T env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
      (eo_type_valid_of_seq_empty_has_smt_translation hTrans)
  cases hEnv with
  | nil =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hClosed]
  | cons hTail =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hClosed]

theorem is_closed_rec_set_empty_eq_eo_is_closed_rec_of_has_smt_translation
    {T env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp1 UserOp1.set_empty T)) :
  __is_closed_rec (Term.UOp1 UserOp1.set_empty T) env =
    __eo_is_closed_rec (Term.UOp1 UserOp1.set_empty T) env :=
by
  have hClosed :
      __eo_is_closed_rec T env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
      (eo_type_valid_of_set_empty_has_smt_translation hTrans)
  cases hEnv with
  | nil =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hClosed]
  | cons hTail =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hClosed]

theorem is_closed_rec_uop1_eq_and_bool_of_has_smt_translation
    {op : UserOp1} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp1 op x)) :
  __is_closed_rec (Term.UOp1 op x) env =
    __eo_is_closed_rec (Term.UOp1 op x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.UOp1 op x) env = Term.Boolean b :=
by
  cases op
  case seq_empty =>
    refine
      ⟨is_closed_rec_seq_empty_eq_eo_is_closed_rec_of_has_smt_translation
          hEnv hTrans,
        ?_⟩
    have hClosed :
        __eo_is_closed_rec x env = Term.Boolean true :=
      eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
        (eo_type_valid_of_seq_empty_has_smt_translation hTrans)
    exact ⟨true, by
      cases hEnv <;> simpa [__eo_is_closed_rec, hClosed]⟩
  case set_empty =>
    refine
      ⟨is_closed_rec_set_empty_eq_eo_is_closed_rec_of_has_smt_translation
          hEnv hTrans,
        ?_⟩
    have hClosed :
        __eo_is_closed_rec x env = Term.Boolean true :=
      eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
        (eo_type_valid_of_set_empty_has_smt_translation hTrans)
    exact ⟨true, by
      cases hEnv <;> simpa [__eo_is_closed_rec, hClosed]⟩
  all_goals
    exfalso
    unfold eoHasSmtTranslation at hTrans
    change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
    exact hTrans TranslationProofs.smtx_typeof_none

theorem re_unfold_pos_component_zero_args_of_non_none
    (s r1 r2 : SmtTerm)
    (hNN :
      term_has_non_none_type
        (__eo_to_smt_re_unfold_pos_component s (SmtTerm.re_concat r1 r2)
          native_nat_zero)) :
  __smtx_typeof s = SmtType.Seq SmtType.Char ∧
    __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan :=
by
  have hTermNN :
      term_has_non_none_type
        (SmtTerm.str_substr s (SmtTerm.Numeral 0)
          (SmtTerm.str_indexof_re_split s r1 r2)) := by
    simpa [__eo_to_smt_re_unfold_pos_component] using hNN
  rcases str_substr_args_of_non_none hTermNN with
    ⟨T, hS, hStart, hLen⟩
  have hSplitNN :
      term_has_non_none_type (SmtTerm.str_indexof_re_split s r1 r2) := by
    unfold term_has_non_none_type
    rw [hLen]
    simp
  have hSplitArgs := str_indexof_re_split_args_of_non_none hSplitNN
  have hR :
      __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan := by
    rw [typeof_re_concat_eq]
    simp [hSplitArgs.2.1, hSplitArgs.2.2, native_ite, native_Teq]
  exact ⟨hSplitArgs.1, hR⟩

theorem re_unfold_pos_component_args_of_non_none
    (s r : SmtTerm) (n : native_Nat)
    (hNN :
      term_has_non_none_type
        (__eo_to_smt_re_unfold_pos_component s r n)) :
  __smtx_typeof s = SmtType.Seq SmtType.Char ∧
    __smtx_typeof r = SmtType.RegLan :=
by
  induction n generalizing s r with
  | zero =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        exact re_unfold_pos_component_zero_args_of_non_none s r1 r2 (by
          simpa [__eo_to_smt_re_unfold_pos_component] using hNN)
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN TranslationProofs.smtx_typeof_none
  | succ n ih =>
      cases r <;> simp [__eo_to_smt_re_unfold_pos_component] at hNN
      case re_concat r1 r2 =>
        let v0 := SmtTerm.str_indexof_re_split s r1 r2
        let newS :=
          SmtTerm.str_substr s v0 (SmtTerm.neg (SmtTerm.str_len s) v0)
        have hRecArgs :
            __smtx_typeof newS = SmtType.Seq SmtType.Char ∧
              __smtx_typeof r2 = SmtType.RegLan := by
          exact ih newS r2 (by
            simpa [newS, v0, __eo_to_smt_re_unfold_pos_component]
              using hNN)
        have hNewSNN : term_has_non_none_type newS := by
          unfold term_has_non_none_type
          rw [hRecArgs.1]
          simp
        rcases str_substr_args_of_non_none hNewSNN with
          ⟨T, hSRaw, hV0, hLen⟩
        have hSplitNN : term_has_non_none_type v0 := by
          unfold term_has_non_none_type
          rw [hV0]
          simp
        have hSplitArgs := str_indexof_re_split_args_of_non_none hSplitNN
        have hR :
            __smtx_typeof (SmtTerm.re_concat r1 r2) = SmtType.RegLan := by
          rw [typeof_re_concat_eq]
          simp [hSplitArgs.2.1, hSplitArgs.2.2, native_ite, native_Teq]
        exact ⟨hSplitArgs.1, hR⟩
      all_goals
        exfalso
        unfold term_has_non_none_type at hNN
        exact hNN TranslationProofs.smtx_typeof_none

theorem re_unfold_pos_component_parts_have_smt_translation
    {s r idx : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx)) :
  eoHasSmtTranslation s ∧ eoHasSmtTranslation r :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_re_unfold_pos_component
              (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat idx))
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid idx
  · exfalso
    exact hTrans (by
      simp [hValid, native_ite, TranslationProofs.smtx_typeof_none])
  · have hCompNN :
        term_has_non_none_type
          (__eo_to_smt_re_unfold_pos_component
            (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat idx)) := by
      unfold term_has_non_none_type
      intro hNone
      exact hTrans (by simpa [hValid, native_ite, hNone])
    have hArgs :=
      re_unfold_pos_component_args_of_non_none
        (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat idx) hCompNN
    constructor
    · unfold eoHasSmtTranslation
      rw [hArgs.1]
      intro h
      cases h
    · unfold eoHasSmtTranslation
      rw [hArgs.2]
      intro h
      cases h

theorem nat_is_valid_of_re_unfold_pos_component_has_smt_translation
    {s r idx : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx)) :
  __eo_to_smt_nat_is_valid idx = true :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_re_unfold_pos_component
              (__eo_to_smt s) (__eo_to_smt r) (__eo_to_smt_nat idx))
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid idx
  · exfalso
    exact hTrans (by simp [hValid, native_ite, __smtx_typeof])
  · rfl

theorem nat_is_valid_of_quantifiers_skolemize_forall_has_smt_translation
    {vs body idx : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx)) :
  __eo_to_smt_nat_is_valid idx = true :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_quantifiers_skolemize
              (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt body)))
              (__eo_to_smt_nat idx))
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid idx
  · exfalso
    exact hTrans (by simp [hValid, native_ite, __smtx_typeof])
  · rfl

theorem closed_smtx_typeof_choice_nth_succ_eq_skolemize_of_non_none
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat)
    (hNN :
      term_has_non_none_type (SmtTerm.choice_nth s T body n.succ)) :
  __smtx_typeof (SmtTerm.choice_nth s T body n.succ) =
    __smtx_typeof (__eo_to_smt_quantifiers_skolemize body n) :=
by
  cases body
  case «exists» s' U body' =>
    simpa [__eo_to_smt_quantifiers_skolemize] using
      choice_nth_succ_typeof_tail_of_non_none hNN
  all_goals
    exfalso
    unfold term_has_non_none_type at hNN
    apply hNN
    simp [__smtx_typeof, __smtx_typeof_choice_nth]

theorem closed_quantifiers_skolemize_non_none_of_choice_nth_succ_non_none
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat)
    (hNN :
      __smtx_typeof (SmtTerm.choice_nth s T body n.succ) ≠
        SmtType.None) :
  __smtx_typeof (__eo_to_smt_quantifiers_skolemize body n) ≠
    SmtType.None :=
by
  have hTermNN :
      term_has_non_none_type (SmtTerm.choice_nth s T body n.succ) := by
    unfold term_has_non_none_type
    exact hNN
  have hEq :=
    closed_smtx_typeof_choice_nth_succ_eq_skolemize_of_non_none
      (s := s) (T := T) (body := body) (n := n) hTermNN
  intro hNone
  apply hNN
  rw [hEq, hNone]

theorem closed_choice_nth_head_type_wf_of_non_none
    (s : native_String) (T : SmtType) (body : SmtTerm) (n : native_Nat)
    (hNN : __smtx_typeof (SmtTerm.choice_nth s T body n) ≠
      SmtType.None) :
  __smtx_type_wf T = true :=
by
  cases n with
  | zero =>
      have hTermNN :
          term_has_non_none_type (SmtTerm.choice_nth s T body 0) := by
        unfold term_has_non_none_type
        exact hNN
      have hGuardTy :
          __smtx_typeof (SmtTerm.choice_nth s T body 0) =
            __smtx_typeof_guard_wf T T :=
        choice_term_guard_type_of_non_none hTermNN
      have hGuardNN : __smtx_typeof_guard_wf T T ≠ SmtType.None := by
        intro hNone
        apply hNN
        rw [hGuardTy, hNone]
      exact Smtm.smtx_typeof_guard_wf_wf_of_non_none T T hGuardNN
  | succ n =>
      cases body with
      | «exists» s' U body' =>
          have hGuardNN :
              __smtx_typeof_guard_wf T
                  (__smtx_typeof_choice_nth U body' n) ≠
                SmtType.None := by
            intro hNone
            apply hNN
            simp [__smtx_typeof, __smtx_typeof_choice_nth, hNone]
          exact
            Smtm.smtx_typeof_guard_wf_wf_of_non_none
              T (__smtx_typeof_choice_nth U body' n) hGuardNN
      | _ =>
          exfalso
          apply hNN
          simp [__smtx_typeof, __smtx_typeof_choice_nth]

theorem closed_type_wf_of_quantifiers_skolemize_cons_non_none
    (s : native_String) (T a : Term) (body : SmtTerm) (n : native_Nat)
    (hNN :
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize
            (__eo_to_smt_exists
              (Term.Apply
                (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) a)
              body) n) ≠
        SmtType.None) :
  __smtx_type_wf (__eo_to_smt_type T) = true :=
by
  have hChoiceNN :
      __smtx_typeof
          (SmtTerm.choice_nth s (__eo_to_smt_type T)
            (__eo_to_smt_exists a body) n) ≠
        SmtType.None := by
    intro hChoiceNone
    apply hNN
    change
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize
            (__eo_to_smt_exists
              (Term.Apply
                (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) a)
              body) n) =
        SmtType.None
    rw [TranslationProofs.eo_to_smt_exists_cons]
    change
      __smtx_typeof
          (SmtTerm.choice_nth s (__eo_to_smt_type T)
            (__eo_to_smt_exists a body) n) =
        SmtType.None
    exact hChoiceNone
  exact
    closed_choice_nth_head_type_wf_of_non_none
      (s := s) (T := __eo_to_smt_type T)
      (body := __eo_to_smt_exists a body) (n := n) hChoiceNN

theorem closed_choice_nth_non_none_of_quantifiers_skolemize_cons_non_none
    (s : native_String) (T a : Term) (body : SmtTerm) (n : native_Nat)
    (hNN :
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize
            (__eo_to_smt_exists
              (Term.Apply
                (Term.Apply Term.__eo_List_cons
                  (Term.Var (Term.String s) T)) a)
              body) n) ≠
        SmtType.None) :
  __smtx_typeof
      (SmtTerm.choice_nth s (__eo_to_smt_type T)
        (__eo_to_smt_exists a body) n) ≠
    SmtType.None :=
by
  intro hChoiceNone
  apply hNN
  change
    __smtx_typeof
        (__eo_to_smt_quantifiers_skolemize
          (__eo_to_smt_exists
            (Term.Apply
              (Term.Apply Term.__eo_List_cons
                (Term.Var (Term.String s) T)) a)
            body) n) =
      SmtType.None
  rw [TranslationProofs.eo_to_smt_exists_cons]
  change
    __smtx_typeof
        (SmtTerm.choice_nth s (__eo_to_smt_type T)
          (__eo_to_smt_exists a body) n) =
      SmtType.None
  exact hChoiceNone

theorem closed_smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
    (s : native_String) (T a : Term) (body : SmtTerm)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hTailBool : __smtx_typeof (__eo_to_smt_exists a body) = SmtType.Bool) :
  __smtx_typeof
      (__eo_to_smt_exists
        (Term.Apply
          (Term.Apply Term.__eo_List_cons
            (Term.Var (Term.String s) T)) a)
        body) =
    SmtType.Bool :=
by
  rw [TranslationProofs.eo_to_smt_exists_cons]
  change
    __smtx_typeof
        (SmtTerm.exists s (__eo_to_smt_type T)
          (__eo_to_smt_exists a body)) =
      SmtType.Bool
  rw [__smtx_typeof.eq_def] <;> simp only
  simp [hTailBool, native_ite, native_Teq, __smtx_typeof_guard_wf, hWf]

theorem closed_eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
    (xs : Term) (body : SmtTerm) (n : native_Nat)
    (hBodyNoExists : ∀ s T F, body ≠ SmtTerm.exists s T F) :
  __smtx_typeof
      (__eo_to_smt_quantifiers_skolemize (__eo_to_smt_exists xs body) n) ≠
      SmtType.None ->
    __smtx_typeof (__eo_to_smt_exists xs body) = SmtType.Bool :=
by
  induction n generalizing xs body with
  | zero =>
      intro hNN
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          have hChoiceNN :
                              term_has_non_none_type
                                (SmtTerm.choice_nth s (__eo_to_smt_type T)
                                  (__eo_to_smt_exists a body) 0) := by
                            unfold term_has_non_none_type
                            exact
                              closed_choice_nth_non_none_of_quantifiers_skolemize_cons_non_none
                                (s := s) (T := T) (a := a) (body := body)
                                (n := 0) hNN
                          have hBodyBool :
                              __smtx_typeof (__eo_to_smt_exists a body) =
                                SmtType.Bool :=
                            TranslationProofs.choice_nth_body_bool_of_non_none
                              hChoiceNN
                          have hWf :=
                            closed_type_wf_of_quantifiers_skolemize_cons_non_none
                              (s := s) (T := T) (a := a) (body := body)
                              (n := 0) hNN
                          exact
                            closed_smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
                              (s := s) (T := T) (a := a) (body := body)
                              hWf hBodyBool
                      | _ =>
                          exfalso
                          have hNoneNN :
                              __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                            simp [__eo_to_smt_quantifiers_skolemize,
                              __eo_to_smt_exists] at hNN ⊢
                          exact hNoneNN TranslationProofs.smtx_typeof_none
                  | _ =>
                      exfalso
                      have hNoneNN :
                          __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                        simp [__eo_to_smt_quantifiers_skolemize,
                          __eo_to_smt_exists] at hNN ⊢
                      exact hNoneNN TranslationProofs.smtx_typeof_none
              | _ =>
                  exfalso
                  have hNoneNN :
                      __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                    simp [__eo_to_smt_quantifiers_skolemize,
                      __eo_to_smt_exists] at hNN ⊢
                  exact hNoneNN TranslationProofs.smtx_typeof_none
          | _ =>
              exfalso
              have hNoneNN :
                  __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                simp [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
                  at hNN ⊢
              exact hNoneNN TranslationProofs.smtx_typeof_none
      | _ =>
          exfalso
          have hNoneNN :
              __smtx_typeof SmtTerm.None ≠ SmtType.None := by
            simp [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
              at hNN ⊢
          exact hNoneNN TranslationProofs.smtx_typeof_none
  | succ n ih =>
      intro hNN
      cases xs with
      | Apply f a =>
          cases f with
          | Apply g y =>
              cases g with
              | __eo_List_cons =>
                  cases y with
                  | Var name T =>
                      cases name with
                      | String s =>
                          have hTailNN :
                              __smtx_typeof
                                  (__eo_to_smt_quantifiers_skolemize
                                    (__eo_to_smt_exists a body) n) ≠
                                SmtType.None := by
                            have hChoiceSucc :
                                __smtx_typeof
                                    (SmtTerm.choice_nth s (__eo_to_smt_type T)
                                      (__eo_to_smt_exists a body) n.succ) ≠
                                  SmtType.None := by
                              exact
                                closed_choice_nth_non_none_of_quantifiers_skolemize_cons_non_none
                                  (s := s) (T := T) (a := a)
                                  (body := body) (n := n.succ) hNN
                            exact
                              closed_quantifiers_skolemize_non_none_of_choice_nth_succ_non_none
                                (s := s) (T := __eo_to_smt_type T)
                                (body := __eo_to_smt_exists a body)
                                (n := n) hChoiceSucc
                          have hTailBool :
                              __smtx_typeof (__eo_to_smt_exists a body) =
                                SmtType.Bool :=
                            ih a body hBodyNoExists hTailNN
                          have hWf :=
                            closed_type_wf_of_quantifiers_skolemize_cons_non_none
                              (s := s) (T := T) (a := a) (body := body)
                              (n := n.succ) hNN
                          exact
                            closed_smtx_typeof_eo_to_smt_exists_cons_bool_of_tail_bool
                              (s := s) (T := T) (a := a) (body := body)
                              hWf hTailBool
                      | _ =>
                          exfalso
                          have hNoneNN :
                              __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                            simp [__eo_to_smt_quantifiers_skolemize,
                              __eo_to_smt_exists] at hNN ⊢
                          exact hNoneNN TranslationProofs.smtx_typeof_none
                  | _ =>
                      exfalso
                      have hNoneNN :
                          __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                        simp [__eo_to_smt_quantifiers_skolemize,
                          __eo_to_smt_exists] at hNN ⊢
                      exact hNoneNN TranslationProofs.smtx_typeof_none
              | _ =>
                  exfalso
                  have hNoneNN :
                      __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                    simp [__eo_to_smt_quantifiers_skolemize,
                      __eo_to_smt_exists] at hNN ⊢
                  exact hNoneNN TranslationProofs.smtx_typeof_none
          | _ =>
              exfalso
              have hNoneNN :
                  __smtx_typeof SmtTerm.None ≠ SmtType.None := by
                simp [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
                  at hNN ⊢
              exact hNoneNN TranslationProofs.smtx_typeof_none
      | _ =>
          exfalso
          cases body
          case «exists» s T F =>
            exact hBodyNoExists s T F rfl
          all_goals
            have hNoneNN :
                __smtx_typeof SmtTerm.None ≠ SmtType.None := by
              simp [__eo_to_smt_quantifiers_skolemize, __eo_to_smt_exists]
                at hNN ⊢
            exact hNoneNN TranslationProofs.smtx_typeof_none

theorem quantifiers_skolemize_forall_term_has_smt_translation
    {vs body idx : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx)) :
  eoHasSmtTranslation
    (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body) :=
by
  unfold eoHasSmtTranslation at hTrans ⊢
  have hValid :
      __eo_to_smt_nat_is_valid idx = true :=
    nat_is_valid_of_quantifiers_skolemize_forall_has_smt_translation
      hTrans
  have hSkolemNN :
      __smtx_typeof
          (__eo_to_smt_quantifiers_skolemize
            (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt body)))
            (__eo_to_smt_nat idx)) ≠
        SmtType.None := by
    intro hNone
    apply hTrans
    change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid idx)
            (__eo_to_smt_quantifiers_skolemize
              (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt body)))
              (__eo_to_smt_nat idx))
            SmtTerm.None) =
        SmtType.None
    simp [hValid, hNone, native_ite]
  have hNotNoExists :
      ∀ s T F, SmtTerm.not (__eo_to_smt body) ≠
        SmtTerm.exists s T F := by
    intro s T F h
    cases h
  have hExistsBool :
      __smtx_typeof
          (__eo_to_smt_exists vs (SmtTerm.not (__eo_to_smt body))) =
        SmtType.Bool :=
    closed_eo_to_smt_exists_bool_of_quantifiers_skolemize_non_none
      vs (SmtTerm.not (__eo_to_smt body)) (__eo_to_smt_nat idx)
      hNotNoExists hSkolemNN
  cases vs
  case __eo_List_nil =>
      exfalso
      exact hTrans (by
        change
          __smtx_typeof
              (native_ite (__eo_to_smt_nat_is_valid idx)
                (__eo_to_smt_quantifiers_skolemize
                  (SmtTerm.not (__eo_to_smt body))
                  (__eo_to_smt_nat idx))
                SmtTerm.None) =
            SmtType.None
        simp [hValid, __eo_to_smt_quantifiers_skolemize, native_ite,
          TranslationProofs.smtx_typeof_none])
  all_goals
    change
      __smtx_typeof
          (SmtTerm.not
            (__eo_to_smt_exists _ (SmtTerm.not (__eo_to_smt body)))) ≠
        SmtType.None
    rw [typeof_not_eq]
    simp [hExistsBool, native_ite, native_Teq]

theorem is_closed_rec_re_unfold_pos_component_eq_of_has_smt_translation_and_parts
    {s r idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx))
    (hS :
      __is_closed_rec s env = __eo_is_closed_rec s env)
    (hR :
      __is_closed_rec r env = __eo_is_closed_rec r env)
    (hSBool : ∃ b, __eo_is_closed_rec s env = Term.Boolean b)
    (hRBool : ∃ b, __eo_is_closed_rec r env = Term.Boolean b) :
  __is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
    __eo_is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env :=
by
  rcases hSBool with ⟨bs, hSBool⟩
  rcases hRBool with ⟨br, hRBool⟩
  have hIdx :
      __eo_is_closed_rec idx env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_re_unfold_pos_component_has_smt_translation hTrans)
  rcases eo_and_eq_boolean_of_boolean hSBool hRBool with
    ⟨bsr, hSRBool⟩
  cases hEnv with
  | nil =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hS, hR, hIdx,
        hSRBool] using
          (eo_and_true_right_eq_of_boolean hSRBool).symm
  | cons hTail =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hS, hR, hIdx,
        hSRBool] using
          (eo_and_true_right_eq_of_boolean hSRBool).symm

theorem is_closed_rec_quantifiers_skolemize_forall_eq_of_has_smt_translation_and_term
    {vs body idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx))
    (hQ :
      __is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          env =
        __eo_is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          env)
    (hQBool :
      ∃ b,
        __eo_is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
            env =
          Term.Boolean b) :
  __is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env =
    __eo_is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env :=
by
  rcases hQBool with ⟨bq, hQBool⟩
  have hIdx :
      __eo_is_closed_rec idx env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_quantifiers_skolemize_forall_has_smt_translation
        hTrans)
  cases hEnv with
  | nil =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hQ, hIdx]
        using (eo_and_true_right_eq_of_boolean hQBool).symm
  | cons hTail =>
      simpa [__is_closed_rec, __eo_is_closed_rec, hQ, hIdx]
        using (eo_and_true_right_eq_of_boolean hQBool).symm

theorem is_closed_rec_at_bv_eq_eo_is_closed_rec_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp2 UserOp2._at_bv x y)) :
  __is_closed_rec (Term.UOp2 UserOp2._at_bv x y) env =
    __eo_is_closed_rec (Term.UOp2 UserOp2._at_bv x y) env :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (__eo_to_smt__at_bv (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  rcases TranslationProofs.eo_to_smt_at_bv_of_non_none hTrans with
    ⟨nx, ny, hxNum, hyNum, _hyNonneg, _hTy⟩
  have hx : x = Term.Numeral nx :=
    TranslationProofs.eo_to_smt_eq_numeral x nx hxNum
  have hy : y = Term.Numeral ny :=
    TranslationProofs.eo_to_smt_eq_numeral y ny hyNum
  subst x
  subst y
  cases hEnv <;>
    simp [__is_closed_rec, __eo_is_closed_rec, __eo_and, native_and]

theorem is_closed_rec_at_bv_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp2 UserOp2._at_bv x y)) :
  __is_closed_rec (Term.UOp2 UserOp2._at_bv x y) env =
    __eo_is_closed_rec (Term.UOp2 UserOp2._at_bv x y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.UOp2 UserOp2._at_bv x y) env =
        Term.Boolean b :=
by
  refine
    ⟨is_closed_rec_at_bv_eq_eo_is_closed_rec_of_has_smt_translation
        hEnv hTrans,
      ?_⟩
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (__eo_to_smt__at_bv (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  rcases TranslationProofs.eo_to_smt_at_bv_of_non_none hTrans with
    ⟨nx, ny, hxNum, hyNum, _hyNonneg, _hTy⟩
  have hx : x = Term.Numeral nx :=
    TranslationProofs.eo_to_smt_eq_numeral x nx hxNum
  have hy : y = Term.Numeral ny :=
    TranslationProofs.eo_to_smt_eq_numeral y ny hyNum
  subst x
  subst y
  exact ⟨true, by
    cases hEnv <;> simp [__eo_is_closed_rec, __eo_and, native_and]⟩

theorem is_closed_rec_quantifiers_skolemize_forall_eq_and_bool_of_has_smt_translation_and_term
    {vs body idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx))
    (hQ :
      __is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          env =
        __eo_is_closed_rec
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          env)
    (hQBool :
      ∃ b,
        __eo_is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
            env =
          Term.Boolean b) :
  __is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env =
    __eo_is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx)
        env =
      Term.Boolean b :=
by
  refine
    ⟨is_closed_rec_quantifiers_skolemize_forall_eq_of_has_smt_translation_and_term
        hEnv hTrans hQ hQBool,
      ?_⟩
  rcases hQBool with ⟨bq, hQBool⟩
  have hIdx :
      __eo_is_closed_rec idx env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_quantifiers_skolemize_forall_has_smt_translation
        hTrans)
  exact ⟨bq, by
    cases hEnv <;>
      simpa [__eo_is_closed_rec, hIdx] using
        (eo_and_true_right_eq_of_boolean hQBool).trans hQBool⟩

theorem is_closed_rec_quantifiers_skolemize_forall_eq_and_bool_of_has_smt_translation
    {vs body idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx))
    (ihQ :
      eoHasSmtTranslation
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body) ->
        __is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
            env =
          __eo_is_closed_rec
            (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
            env ∧
          ∃ b,
            __eo_is_closed_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
                env =
              Term.Boolean b) :
  __is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env =
    __eo_is_closed_rec
      (Term.UOp2 UserOp2._at_quantifiers_skolemize
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
        idx)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp2 UserOp2._at_quantifiers_skolemize
          (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body)
          idx)
        env =
      Term.Boolean b :=
by
  have hQTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.forall) vs) body) :=
    quantifiers_skolemize_forall_term_has_smt_translation hTrans
  exact
    is_closed_rec_quantifiers_skolemize_forall_eq_and_bool_of_has_smt_translation_and_term
      hEnv hTrans (ihQ hQTrans).1 (ihQ hQTrans).2

theorem is_closed_rec_uop2_eq_and_bool_of_has_smt_translation
    {op : UserOp2} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp2 op x y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.UOp2 op x y) env =
    __eo_is_closed_rec (Term.UOp2 op x y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.UOp2 op x y) env =
        Term.Boolean b :=
by
  cases op
  case _at_bv =>
    exact is_closed_rec_at_bv_eq_and_bool_of_has_smt_translation
      hEnv hTrans
  case _at_quantifiers_skolemize =>
    cases x
    case Apply f body =>
      cases f
      case Apply q vs =>
        cases q
        case UOp qOp =>
          cases qOp
          case «forall» =>
            exact
              is_closed_rec_quantifiers_skolemize_forall_eq_and_bool_of_has_smt_translation
                hEnv hTrans ihX
          all_goals
            exfalso
            unfold eoHasSmtTranslation at hTrans
            change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
            exact hTrans TranslationProofs.smtx_typeof_none
        all_goals
          exfalso
          unfold eoHasSmtTranslation at hTrans
          change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
          exact hTrans TranslationProofs.smtx_typeof_none
      all_goals
        exfalso
        unfold eoHasSmtTranslation at hTrans
        change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
        exact hTrans TranslationProofs.smtx_typeof_none
    all_goals
      exfalso
      unfold eoHasSmtTranslation at hTrans
      change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
      exact hTrans TranslationProofs.smtx_typeof_none
  all_goals
    exfalso
    unfold eoHasSmtTranslation at hTrans
    change __smtx_typeof SmtTerm.None ≠ SmtType.None at hTrans
    exact hTrans TranslationProofs.smtx_typeof_none

theorem is_closed_rec_re_unfold_pos_component_eq_and_bool_of_has_smt_translation_and_parts
    {s r idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx))
    (hS :
      __is_closed_rec s env = __eo_is_closed_rec s env ∧
        ∃ b, __eo_is_closed_rec s env = Term.Boolean b)
    (hR :
      __is_closed_rec r env = __eo_is_closed_rec r env ∧
        ∃ b, __eo_is_closed_rec r env = Term.Boolean b) :
  __is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
    __eo_is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
      Term.Boolean b :=
by
  rcases hS with ⟨hSEq, hSBool⟩
  rcases hR with ⟨hREq, hRBool⟩
  refine
    ⟨is_closed_rec_re_unfold_pos_component_eq_of_has_smt_translation_and_parts
        hEnv hTrans hSEq hREq hSBool hRBool,
      ?_⟩
  rcases hSBool with ⟨bs, hSBool⟩
  rcases hRBool with ⟨br, hRBool⟩
  have hIdx :
      __eo_is_closed_rec idx env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_re_unfold_pos_component_has_smt_translation hTrans)
  rcases eo_and_eq_boolean_of_boolean hSBool hRBool with
    ⟨bsr, hSRBool⟩
  exact ⟨bsr, by
    cases hEnv <;>
      simpa [__eo_is_closed_rec, hIdx, hSRBool] using
        (eo_and_true_right_eq_of_boolean hSRBool).trans hSRBool⟩

theorem is_closed_rec_re_unfold_pos_component_eq_and_bool_of_has_smt_translation
    {s r idx env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx))
    (ihS :
      eoHasSmtTranslation s ->
        __is_closed_rec s env = __eo_is_closed_rec s env ∧
          ∃ b, __eo_is_closed_rec s env = Term.Boolean b)
    (ihR :
      eoHasSmtTranslation r ->
        __is_closed_rec r env = __eo_is_closed_rec r env ∧
          ∃ b, __eo_is_closed_rec r env = Term.Boolean b) :
  __is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
    __eo_is_closed_rec
      (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp3 UserOp3._at_re_unfold_pos_component s r idx) env =
      Term.Boolean b :=
by
  rcases re_unfold_pos_component_parts_have_smt_translation hTrans with
    ⟨hSTrans, hRTrans⟩
  exact
    is_closed_rec_re_unfold_pos_component_eq_and_bool_of_has_smt_translation_and_parts
      hEnv hTrans (ihS hSTrans) (ihR hRTrans)

theorem nat_is_valid_of_witness_string_length_len_has_smt_translation
    {T len id : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_witness_string_length T len id)) :
  __eo_to_smt_nat_is_valid len = true :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid len)
            (native_ite (__eo_to_smt_nat_is_valid id)
              (SmtTerm.choice_nth (native_string_lit "@x")
                (__eo_to_smt_type T)
                (SmtTerm.eq
                  (SmtTerm.str_len
                    (SmtTerm.Var (native_string_lit "@x")
                      (__eo_to_smt_type T)))
                  (__eo_to_smt len))
                native_nat_zero)
              SmtTerm.None)
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid len
  · exfalso
    exact hTrans (by
      simp [hValid, native_ite, TranslationProofs.smtx_typeof_none])
  · rfl

theorem nat_is_valid_of_witness_string_length_id_has_smt_translation
    {T len id : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_witness_string_length T len id)) :
  __eo_to_smt_nat_is_valid id = true :=
by
  have hLen :
      __eo_to_smt_nat_is_valid len = true :=
    nat_is_valid_of_witness_string_length_len_has_smt_translation hTrans
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid len)
            (native_ite (__eo_to_smt_nat_is_valid id)
              (SmtTerm.choice_nth (native_string_lit "@x")
                (__eo_to_smt_type T)
                (SmtTerm.eq
                  (SmtTerm.str_len
                    (SmtTerm.Var (native_string_lit "@x")
                      (__eo_to_smt_type T)))
                  (__eo_to_smt len))
                native_nat_zero)
              SmtTerm.None)
            SmtTerm.None) ≠
        SmtType.None at hTrans
  cases hValid : __eo_to_smt_nat_is_valid id
  · exfalso
    exact hTrans (by
      simp [hLen, hValid, native_ite, TranslationProofs.smtx_typeof_none])
  · rfl

theorem eo_type_valid_of_witness_string_length_has_smt_translation
    {T len id : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_witness_string_length T len id)) :
  TranslationProofs.eo_type_valid T :=
by
  have hLen :
      __eo_to_smt_nat_is_valid len = true :=
    nat_is_valid_of_witness_string_length_len_has_smt_translation hTrans
  have hId :
      __eo_to_smt_nat_is_valid id = true :=
    nat_is_valid_of_witness_string_length_id_has_smt_translation hTrans
  unfold eoHasSmtTranslation at hTrans
  let ST := __eo_to_smt_type T
  let body :=
    SmtTerm.eq
      (SmtTerm.str_len (SmtTerm.Var (native_string_lit "@x") ST))
      (__eo_to_smt len)
  have hChoiceNN :
      term_has_non_none_type
        (SmtTerm.choice_nth (native_string_lit "@x") ST body
          native_nat_zero) := by
    unfold term_has_non_none_type
    intro hNone
    apply hTrans
    change
      __smtx_typeof
          (native_ite (__eo_to_smt_nat_is_valid len)
            (native_ite (__eo_to_smt_nat_is_valid id)
              (SmtTerm.choice_nth (native_string_lit "@x") ST body
                native_nat_zero)
              SmtTerm.None)
            SmtTerm.None) =
        SmtType.None
    simp [hLen, hId, hNone, native_ite]
  have hChoiceGuard :
      __smtx_typeof
          (SmtTerm.choice_nth (native_string_lit "@x") ST body
            native_nat_zero) =
        __smtx_typeof_guard_wf ST ST :=
    choice_term_guard_type_of_non_none hChoiceNN
  have hGuardNN : __smtx_typeof_guard_wf ST ST ≠ SmtType.None := by
    intro hNone
    unfold term_has_non_none_type at hChoiceNN
    exact hChoiceNN (by rw [hChoiceGuard, hNone])
  have hTWF : __smtx_type_wf ST = true :=
    Smtm.smtx_typeof_guard_wf_wf_of_non_none ST ST hGuardNN
  exact TranslationProofs.eo_type_valid_of_smt_wf T
    (by simpa [ST] using hTWF)

theorem is_closed_rec_witness_string_length_eq_and_bool_of_has_smt_translation
    {T len id env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.UOp3 UserOp3._at_witness_string_length T len id)) :
  __is_closed_rec
      (Term.UOp3 UserOp3._at_witness_string_length T len id) env =
    __eo_is_closed_rec
      (Term.UOp3 UserOp3._at_witness_string_length T len id) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.UOp3 UserOp3._at_witness_string_length T len id) env =
      Term.Boolean b :=
by
  have hTClosed :
      __eo_is_closed_rec T env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_eo_type_valid hEnv
      (eo_type_valid_of_witness_string_length_has_smt_translation hTrans)
  have hLenClosed :
      __eo_is_closed_rec len env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_witness_string_length_len_has_smt_translation hTrans)
  have hIdClosed :
      __eo_is_closed_rec id env = Term.Boolean true :=
    eo_is_closed_rec_eq_true_of_nat_is_valid hEnv
      (nat_is_valid_of_witness_string_length_id_has_smt_translation hTrans)
  refine ⟨?_, ?_⟩
  · cases hEnv <;>
      simp [__is_closed_rec, __eo_is_closed_rec, hTClosed, hLenClosed,
        hIdClosed, __eo_and, native_and]
  · exact ⟨true, by
      cases hEnv <;>
        simp [__eo_is_closed_rec, hTClosed, hLenClosed, hIdClosed,
          __eo_and, native_and]⟩

theorem is_closed_rec_uop3_eq_and_bool_of_has_smt_translation
    {op : UserOp3} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.UOp3 op x y z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.UOp3 op x y z) env =
    __eo_is_closed_rec (Term.UOp3 op x y z) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.UOp3 op x y z) env =
        Term.Boolean b :=
by
  cases op
  case _at_re_unfold_pos_component =>
    exact
      is_closed_rec_re_unfold_pos_component_eq_and_bool_of_has_smt_translation
        hEnv hTrans ihX ihY
  case _at_witness_string_length =>
    exact
      is_closed_rec_witness_string_length_eq_and_bool_of_has_smt_translation
        hEnv hTrans

theorem is_closed_rec_apply_uop_eq_and_bool_of_arg
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp op) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean b :=
by
  rcases hX with ⟨hXEq, ⟨b, hXBool⟩⟩
  refine ⟨?_, ?_⟩
  · cases hEnv <;>
      simpa [__is_closed_rec, __eo_is_closed_rec, hXEq] using
        eo_and_true_left_eq_of_boolean hXBool
  · exact ⟨b, by
      cases hEnv <;>
        simpa [__eo_is_closed_rec] using
          (eo_and_true_left_eq_of_boolean hXBool).trans hXBool⟩

theorem term_has_non_none_type_of_eo_has_smt_translation
    {t : Term}
    (hTrans : eoHasSmtTranslation t) :
  term_has_non_none_type (__eo_to_smt t) :=
by
  unfold eoHasSmtTranslation at hTrans
  unfold term_has_non_none_type
  exact hTrans

theorem eo_has_smt_translation_of_smt_type_eq
    {x : Term} {T : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt x) = T)
    (hT : T ≠ SmtType.None) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation
  rw [hTy]
  exact hT

theorem eo_has_smt_translation_of_term_has_non_none_type
    {x : Term}
    (hNN : term_has_non_none_type (__eo_to_smt x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation
  unfold term_has_non_none_type at hNN
  exact hNN

theorem not_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.not) x)) :
  eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans ⊢
  change __smtx_typeof (SmtTerm.not (__eo_to_smt x)) ≠ SmtType.None
    at hTrans
  rw [typeof_not_eq] at hTrans
  cases hX : __smtx_typeof (__eo_to_smt x) <;>
    simp [native_ite, native_Teq, hX] at hTrans ⊢

theorem to_real_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.to_real) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.to_real (__eo_to_smt x)) at hNN
  rcases to_real_arg_of_non_none hNN with hXTy | hXTy
  · exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)
  · exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem to_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.to_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.to_int (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.to_int)
      (typeof_to_int_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem is_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.is_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.is_int (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Real :=
    real_arg_of_non_none (op := SmtTerm.is_int)
      (typeof_is_int_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem abs_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.abs) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.abs (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_arg_of_non_none hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem uneg_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.uneg (__eo_to_smt x)) at hNN
  rcases
      arith_unop_arg_of_non_none (op := SmtTerm.uneg)
        (typeof_uneg_eq (__eo_to_smt x)) hNN with hXTy | hXTy
  · exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)
  · exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem int_pow2_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_pow2) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.int_pow2 (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_pow2)
      (typeof_int_pow2_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem int_log2_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_log2) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.int_log2 (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_ret_arg_of_non_none (op := SmtTerm.int_log2)
      (typeof_int_log2_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem typeof_bvnot_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.bvnot t) =
    __smtx_typeof_bv_op_1 (__smtx_typeof t) :=
by
  rw [__smtx_typeof.eq_38]

theorem bvnot_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvnot) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.bvnot (__eo_to_smt x)) at hNN
  rcases
      bv_unop_arg_of_non_none (op := SmtTerm.bvnot)
        (typeof_bvnot_eq_closed (__eo_to_smt x)) hNN with ⟨w, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem typeof_bvneg_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.bvneg t) =
    __smtx_typeof_bv_op_1 (__smtx_typeof t) :=
by
  rw [__smtx_typeof.eq_46]

theorem typeof_bvnego_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.bvnego t) =
    __smtx_typeof_bv_op_1_ret (__smtx_typeof t) SmtType.Bool :=
by
  rw [__smtx_typeof.eq_71]

theorem bvneg_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvneg) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.bvneg (__eo_to_smt x)) at hNN
  rcases
      bv_unop_arg_of_non_none (op := SmtTerm.bvneg)
        (typeof_bvneg_eq_closed (__eo_to_smt x)) hNN with ⟨w, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem bvnego_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvnego) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.bvnego (__eo_to_smt x)) at hNN
  rcases
      bv_unop_ret_arg_of_non_none (op := SmtTerm.bvnego)
        (ret := SmtType.Bool)
        (typeof_bvnego_eq_closed (__eo_to_smt x)) hNN with ⟨w, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem str_len_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_len) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_len (__eo_to_smt x)) at hNN
  rcases
      seq_arg_of_non_none_ret (op := SmtTerm.str_len)
        (R := SmtType.Int)
        (typeof_str_len_eq (__eo_to_smt x)) hNN with ⟨T, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem str_rev_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_rev) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_rev (__eo_to_smt x)) at hNN
  rcases
      seq_arg_of_non_none (op := SmtTerm.str_rev)
        (typeof_str_rev_eq (__eo_to_smt x)) hNN with ⟨T, hXTy⟩
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem seq_char_unary_arg_has_smt_translation
    {x : Term} {op : SmtTerm -> SmtTerm} {ret : SmtType}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          ret SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x))) :
  eoHasSmtTranslation x :=
by
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Seq SmtType.Char :=
    seq_char_arg_of_non_none (op := op) (ret := ret) hTy hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem str_to_lower_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_lower) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_lower (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_lower_eq (__eo_to_smt x)) hNN

theorem str_to_upper_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_upper) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_upper (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_upper_eq (__eo_to_smt x)) hNN

theorem str_to_code_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_code) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_code (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_code_eq (__eo_to_smt x)) hNN

theorem str_is_digit_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_is_digit) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_is_digit (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_is_digit_eq (__eo_to_smt x)) hNN

theorem str_to_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_int (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_int_eq (__eo_to_smt x)) hNN

theorem str_to_re_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_to_re) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_to_re (__eo_to_smt x)) at hNN
  exact
    seq_char_unary_arg_has_smt_translation
      (typeof_str_to_re_eq (__eo_to_smt x)) hNN

theorem str_from_code_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_from_code) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_from_code (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_code)
      (ret := SmtType.Seq SmtType.Char)
      (typeof_str_from_code_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem str_from_int_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.str_from_int) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.str_from_int (__eo_to_smt x)) at hNN
  have hXTy :
      __smtx_typeof (__eo_to_smt x) = SmtType.Int :=
    int_arg_of_non_none_ret (op := SmtTerm.str_from_int)
      (ret := SmtType.Seq SmtType.Char)
      (typeof_str_from_int_eq (__eo_to_smt x)) hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem reglan_unary_arg_has_smt_translation
    {x : Term} {op : SmtTerm -> SmtTerm}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          SmtType.RegLan SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x))) :
  eoHasSmtTranslation x :=
by
  have hXTy : __smtx_typeof (__eo_to_smt x) = SmtType.RegLan :=
    reglan_arg_of_non_none (op := op) hTy hNN
  exact eo_has_smt_translation_of_smt_type_eq hXTy (by simp)

theorem re_mult_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_mult) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.re_mult (__eo_to_smt x)) at hNN
  exact reglan_unary_arg_has_smt_translation
    (typeof_re_mult_eq (__eo_to_smt x)) hNN

theorem re_plus_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_plus) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.re_plus (__eo_to_smt x)) at hNN
  exact reglan_unary_arg_has_smt_translation
    (typeof_re_plus_eq (__eo_to_smt x)) hNN

theorem re_opt_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_opt) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.re_opt (__eo_to_smt x)) at hNN
  exact reglan_unary_arg_has_smt_translation
    (typeof_re_opt_eq (__eo_to_smt x)) hNN

theorem re_comp_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.re_comp) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.re_comp (__eo_to_smt x)) at hNN
  exact reglan_unary_arg_has_smt_translation
    (typeof_re_comp_eq (__eo_to_smt x)) hNN

theorem typeof_seq_unit_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.seq_unit t) =
    __smtx_typeof_guard_wf (SmtType.Seq (__smtx_typeof t))
      (SmtType.Seq (__smtx_typeof t)) :=
by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem typeof_set_singleton_eq_closed
    (t : SmtTerm) :
  __smtx_typeof (SmtTerm.set_singleton t) =
    __smtx_typeof_guard_wf (SmtType.Set (__smtx_typeof t))
      (SmtType.Set (__smtx_typeof t)) :=
by
  rw [__smtx_typeof.eq_def] <;> simp only

theorem seq_unit_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.seq_unit) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.seq_unit (__eo_to_smt x)) at hNN
  unfold term_has_non_none_type at hNN
  unfold eoHasSmtTranslation
  by_cases hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None
  · exfalso
    apply hNN
    simp [typeof_seq_unit_eq_closed, hNone, __smtx_typeof_guard_wf,
      __smtx_type_wf, __smtx_type_wf_rec, __smtx_type_wf_component,
      native_and, native_ite]
  · exact hNone

theorem set_singleton_arg_has_smt_translation_of_has_smt_translation
    {x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.set_singleton) x)) :
  eoHasSmtTranslation x :=
by
  have hNN := term_has_non_none_type_of_eo_has_smt_translation hTrans
  change term_has_non_none_type (SmtTerm.set_singleton (__eo_to_smt x)) at hNN
  unfold term_has_non_none_type at hNN
  unfold eoHasSmtTranslation
  by_cases hNone : __smtx_typeof (__eo_to_smt x) = SmtType.None
  · exfalso
    apply hNN
    simp [typeof_set_singleton_eq_closed, hNone, __smtx_typeof_guard_wf,
      __smtx_type_wf, __smtx_type_wf_rec, __smtx_type_wf_component,
      native_and, native_ite]
  · exact hNone

theorem is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hXTrans : eoHasSmtTranslation x)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp op) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean b :=
by
  exact is_closed_rec_apply_uop_eq_and_bool_of_arg hEnv (ihX hXTrans)

theorem is_closed_rec_apply_uop_eq_and_bool_of_has_smt_translation_and_arg
    {op : UserOp} {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans : eoHasSmtTranslation (Term.Apply (Term.UOp op) x))
    (hArg :
      eoHasSmtTranslation (Term.Apply (Term.UOp op) x) ->
        eoHasSmtTranslation x)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp op) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv (hArg hTrans) ihX

theorem is_closed_rec_apply_not_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.not) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.not) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.not) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.not) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (not_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_to_real_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.to_real) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.to_real) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.to_real) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.to_real) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (to_real_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_to_int_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.to_int) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.to_int) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.to_int) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.to_int) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (to_int_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_is_int_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.is_int) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.is_int) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.is_int) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.is_int) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (is_int_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_abs_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.abs) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.abs) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.abs) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.abs) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (abs_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_eoo_neg_2_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (uneg_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_int_pow2_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_pow2) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.int_pow2) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_pow2) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_pow2) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (int_pow2_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_int_log2_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.int_log2) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.int_log2) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_log2) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.int_log2) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (int_log2_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem is_closed_rec_apply_bvnot_eq_and_bool_of_has_smt_translation
    {x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp UserOp.bvnot) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp UserOp.bvnot) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvnot) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp UserOp.bvnot) x) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_uop_eq_and_bool_of_arg_has_smt_translation
      hEnv
      (bvnot_arg_has_smt_translation_of_has_smt_translation hTrans)
      ihX

theorem native_zleq_zero_of_one_zleq {i : native_Int}
    (hi : native_zleq 1 i = true) :
  native_zleq 0 i = true :=
by
  have hiProp : (1 : Int) ≤ i := by
    simpa [native_zleq] using hi
  have h0Prop : (0 : Int) ≤ i := by
    calc
      (0 : Int) ≤ 1 := by decide
      _ ≤ i := hiProp
  simpa [native_zleq] using h0Prop

theorem native_zleq_zero_of_zleq_chain {i j : native_Int}
    (hj : native_zleq 0 j = true)
    (hji : native_zleq j i = true) :
  native_zleq 0 i = true :=
by
  have hjProp : (0 : Int) ≤ j := by
    simpa [native_zleq] using hj
  have hjiProp : j ≤ i := by
    simpa [native_zleq] using hji
  have hiProp : (0 : Int) ≤ i := by
    calc
      (0 : Int) ≤ j := hjProp
      _ ≤ i := hjiProp
  simpa [native_zleq] using hiProp

theorem eo_to_smt_nat_is_valid_of_smt_numeral_nonneg
    {idx : Term} {i : native_Int}
    (hIdx : __eo_to_smt idx = SmtTerm.Numeral i)
    (hi : native_zleq 0 i = true) :
  __eo_to_smt_nat_is_valid idx = true :=
by
  have hIdxTerm : idx = Term.Numeral i :=
    TranslationProofs.eo_to_smt_eq_numeral idx i hIdx
  subst idx
  simpa [__eo_to_smt_nat_is_valid, hi]

theorem smtx_typeof_binary_one_eq :
    __smtx_typeof (SmtTerm.Binary 1 1) = SmtType.BitVec 1 :=
by
  have hNN : __smtx_typeof (SmtTerm.Binary 1 1) ≠ SmtType.None := by
    unfold __smtx_typeof
    simp [native_ite, SmtEval.native_and, native_zleq, native_zeq,
      native_mod_total, native_int_pow2]
    rfl
  simpa using TranslationProofs.smtx_typeof_binary_of_non_none 1 1 hNN

theorem is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
    {op : UserOp1} {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hIdx : __eo_is_closed_rec idx env = Term.Boolean true)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 op idx) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp1 op idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp1 op idx) x) env =
        Term.Boolean b :=
by
  rcases hX with ⟨hXEq, ⟨b, hXBool⟩⟩
  refine ⟨?_, ?_⟩
  · cases hEnv <;>
      simpa [__is_closed_rec, __eo_is_closed_rec, hIdx, hXEq] using
        eo_and_true_left_eq_of_boolean hXBool
  · exact ⟨b, by
      cases hEnv <;>
        simpa [__eo_is_closed_rec, hIdx] using
          (eo_and_true_left_eq_of_boolean hXBool).trans hXBool⟩

theorem repeat_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.repeat idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.repeat (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases repeat_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum
      (native_zleq_zero_of_one_zleq hi)
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem zero_extend_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.zero_extend (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases zero_extend_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem sign_extend_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.sign_extend (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases sign_extend_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem rotate_left_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.rotate_left (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases rotate_left_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem rotate_right_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.rotate_right (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases rotate_right_args_of_non_none hNN with ⟨i, w, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem int_to_bv_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.int_to_bv (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases int_to_bv_args_of_non_none hNN with ⟨i, hIdxNum, hXTy, hi⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxNum hi
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem re_exp_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_exp (__eo_to_smt idx) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  cases hIdx : __eo_to_smt idx with
  | Numeral i =>
      have hNN' :
          term_has_non_none_type
            (SmtTerm.re_exp (SmtTerm.Numeral i) (__eo_to_smt x)) := by
        simpa [hIdx] using hNN
      rcases re_exp_arg_of_non_none hNN' with ⟨hi, hXTy⟩
      constructor
      · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdx hi
      · unfold eoHasSmtTranslation
        rw [hXTy]
        intro h
        cases h
  | _ =>
      exfalso
      unfold term_has_non_none_type at hNN
      exact hNN (by
        simp [hIdx, __smtx_typeof, __smtx_typeof_re_exp])

theorem at_bit_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.eq
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x))
            (SmtTerm.Binary 1 1)) ≠
        SmtType.None at hTrans
  have hApplyNN :
      term_has_non_none_type
        (SmtTerm.eq
          (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
            (__eo_to_smt x))
          (SmtTerm.Binary 1 1)) := by
    unfold term_has_non_none_type
    exact hTrans
  have hEqNN :
      __smtx_typeof_eq
          (__smtx_typeof
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x)))
          (SmtType.BitVec 1) ≠
        SmtType.None := by
    unfold term_has_non_none_type at hApplyNN
    rw [typeof_eq_eq, smtx_typeof_binary_one_eq] at hApplyNN
    exact hApplyNN
  have hExtTy :
      __smtx_typeof
          (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
            (__eo_to_smt x)) =
        SmtType.BitVec 1 :=
  by
    by_cases hNone :
        __smtx_typeof
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x)) =
          SmtType.None
    · exfalso
      exact hEqNN (by
        rw [hNone]
        simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
          native_Teq])
    · by_cases hEq :
        __smtx_typeof
            (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
              (__eo_to_smt x)) =
          SmtType.BitVec 1
      · exact hEq
      · exfalso
        exact hEqNN (by
          simp [__smtx_typeof_eq, __smtx_typeof_guard, native_ite,
            native_Teq, hNone, hEq])
  have hExtNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt idx) (__eo_to_smt idx)
          (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hExtTy]
    simp
  rcases extract_args_of_non_none hExtNN with
    ⟨_i, j, w, _hIdxHigh, hIdxLow, hXTy, hj0, _hji, _hiw⟩
  constructor
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdxLow hj0
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem tuple_select_index_nat_valid_and_arg_has_smt_translation
    {idx x : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x)) :
  __eo_to_smt_nat_is_valid idx = true ∧ eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (__eo_to_smt_tuple_select
            (__smtx_typeof (__eo_to_smt x)) (__eo_to_smt idx)
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  cases hTy : __smtx_typeof (__eo_to_smt x) with
  | Datatype s d =>
      by_cases hTuple : s = native_string_lit "@Tuple"
      · subst s
        cases hIdx : __eo_to_smt idx with
        | Numeral n =>
            cases hNonneg : native_zleq 0 n
            · exfalso
              exact hTrans (by
                rw [hTy, hIdx]
                simp [__eo_to_smt_tuple_select, hNonneg, native_streq,
                  native_and, native_ite])
            · constructor
              · exact
                  eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hIdx
                    hNonneg
              · unfold eoHasSmtTranslation
                rw [hTy]
                intro h
                cases h
        | _ =>
            exfalso
            exact hTrans (by
              rw [hTy, hIdx]
              simp [__eo_to_smt_tuple_select])
      · exfalso
        exact hTrans (by
          rw [hTy]
          cases __eo_to_smt idx <;>
            simp [__eo_to_smt_tuple_select, hTuple, native_streq,
              native_and, native_ite])
  | _ =>
      exfalso
      exact hTrans (by
        rw [hTy]
        simp [__eo_to_smt_tuple_select])

theorem is_closed_rec_apply_repeat_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.repeat idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.repeat idx) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.repeat idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.repeat idx) x) env =
        Term.Boolean b :=
by
  rcases repeat_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_zero_extend_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.zero_extend idx) x) env =
        Term.Boolean b :=
by
  rcases zero_extend_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_sign_extend_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.sign_extend idx) x) env =
        Term.Boolean b :=
by
  rcases sign_extend_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_rotate_left_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.rotate_left idx) x) env =
        Term.Boolean b :=
by
  rcases rotate_left_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_rotate_right_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.rotate_right idx) x) env =
        Term.Boolean b :=
by
  rcases rotate_right_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_int_to_bv_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.int_to_bv idx) x) env =
        Term.Boolean b :=
by
  rcases int_to_bv_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_re_exp_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.re_exp idx) x) env =
        Term.Boolean b :=
by
  rcases re_exp_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_at_bit_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1._at_bit idx) x) env =
        Term.Boolean b :=
by
  rcases at_bit_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_tuple_select_eq_and_bool_of_has_smt_translation
    {idx x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) env =
    __eo_is_closed_rec
      (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) x) env =
        Term.Boolean b :=
by
  rcases tuple_select_index_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hIdxValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop1_eq_and_bool_of_index_true_and_arg
      hEnv
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hIdxValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_uop2_eq_and_bool_of_indices_true_and_arg
    {op : UserOp2} {i j x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hHead : __is_closed_rec (Term.UOp2 op i j) env = Term.Boolean true)
    (hI : __eo_is_closed_rec i env = Term.Boolean true)
    (hJ : __eo_is_closed_rec j env = Term.Boolean true)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp2 op i j) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp2 op i j) x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.UOp2 op i j) x) env =
        Term.Boolean b :=
by
  rcases hX with ⟨hXEq, ⟨b, hXBool⟩⟩
  refine ⟨?_, ?_⟩
  · cases hEnv <;>
      simpa [__is_closed_rec, __eo_is_closed_rec, hHead, hI, hJ, hXEq,
        eo_and_true_true] using
        eo_and_true_left_eq_of_boolean hXBool
  · exact ⟨b, by
      cases hEnv <;>
        simpa [__eo_is_closed_rec, hI, hJ, eo_and_true_true] using
          (eo_and_true_left_eq_of_boolean hXBool).trans hXBool⟩

theorem extract_indices_nat_valid_and_arg_has_smt_translation
    {hi lo x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x)) :
  __eo_to_smt_nat_is_valid hi = true ∧
    __eo_to_smt_nat_is_valid lo = true ∧
      eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo)
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.extract (__eo_to_smt hi) (__eo_to_smt lo)
          (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases extract_args_of_non_none hNN with
    ⟨i, j, w, hHiNum, hLoNum, hXTy, hj0, hji, _hiw⟩
  have hi0 : native_zleq 0 i = true :=
    native_zleq_zero_of_zleq_chain hj0 hji
  refine ⟨?_, ?_, ?_⟩
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hHiNum hi0
  · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hLoNum hj0
  · unfold eoHasSmtTranslation
    rw [hXTy]
    intro h
    cases h

theorem re_loop_indices_nat_valid_and_arg_has_smt_translation
    {lo hi x : Term}
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x)) :
  __eo_to_smt_nat_is_valid lo = true ∧
    __eo_to_smt_nat_is_valid hi = true ∧
      eoHasSmtTranslation x :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi)
            (__eo_to_smt x)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.re_loop (__eo_to_smt lo) (__eo_to_smt hi)
          (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    exact hTrans
  cases hLo : __eo_to_smt lo with
  | Numeral n1 =>
      cases hHi : __eo_to_smt hi with
      | Numeral n2 =>
          have hNN' :
              term_has_non_none_type
                (SmtTerm.re_loop (SmtTerm.Numeral n1)
                  (SmtTerm.Numeral n2) (__eo_to_smt x)) := by
            simpa [hLo, hHi] using hNN
          rcases re_loop_arg_of_non_none hNN' with ⟨hn1, hn2, hXTy⟩
          refine ⟨?_, ?_, ?_⟩
          · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hLo hn1
          · exact eo_to_smt_nat_is_valid_of_smt_numeral_nonneg hHi hn2
          · unfold eoHasSmtTranslation
            rw [hXTy]
            intro h
            cases h
      | _ =>
          exfalso
          unfold term_has_non_none_type at hNN
          exact hNN (by
            simp [hLo, hHi, __smtx_typeof, __smtx_typeof_re_loop])
  | _ =>
      exfalso
      unfold term_has_non_none_type at hNN
      exact hNN (by
        simp [hLo, __smtx_typeof, __smtx_typeof_re_loop])

theorem is_closed_rec_apply_extract_eq_and_bool_of_has_smt_translation
    {hi lo x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp2 UserOp2.extract hi lo) x) env =
        Term.Boolean b :=
by
  rcases extract_indices_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hHiValid, hLoValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop2_eq_and_bool_of_indices_true_and_arg
      hEnv
      (by cases hEnv <;> simp [__is_closed_rec])
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hHiValid)
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hLoValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_re_loop_eq_and_bool_of_has_smt_translation
    {lo hi x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) env =
    __eo_is_closed_rec (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) env ∧
    ∃ b,
      __eo_is_closed_rec
          (Term.Apply (Term.UOp2 UserOp2.re_loop lo hi) x) env =
        Term.Boolean b :=
by
  rcases re_loop_indices_nat_valid_and_arg_has_smt_translation hTrans with
    ⟨hLoValid, hHiValid, hXTrans⟩
  exact
    is_closed_rec_apply_uop2_eq_and_bool_of_indices_true_and_arg
      hEnv
      (by cases hEnv <;> simp [__is_closed_rec])
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hLoValid)
      (eo_is_closed_rec_eq_true_of_nat_is_valid hEnv hHiValid)
      (ihX hXTrans)

theorem is_closed_rec_apply_eq_of_not_list_branch
    {f x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotList :
      ∀ q v vs,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs)) :
  __is_closed_rec (Term.Apply f x) env =
    __eo_and (__is_closed_rec f env) (__is_closed_rec x env) :=
by
  cases hEnv <;> cases f <;> simp [__is_closed_rec]

theorem eo_is_closed_rec_apply_eq_of_not_quantifier
    {f x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hNotExists :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs) :
  __eo_is_closed_rec (Term.Apply f x) env =
    __eo_and (__eo_is_closed_rec f env) (__eo_is_closed_rec x env) :=
by
  cases hEnv <;> cases f <;> simp [__eo_is_closed_rec]

theorem is_closed_rec_apply_generic_eq_and_bool_of_parts
    {f x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotList :
      ∀ q v vs,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hNotForall :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hNotExists :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs)
    (hF :
      __is_closed_rec f env = __eo_is_closed_rec f env ∧
        ∃ b, __eo_is_closed_rec f env = Term.Boolean b)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply f x) env =
    __eo_is_closed_rec (Term.Apply f x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply f x) env = Term.Boolean b :=
by
  rcases hF with ⟨hFEq, hFBool⟩
  rcases hX with ⟨hXEq, hXBool⟩
  refine ⟨?_, ?_⟩
  · calc
      __is_closed_rec (Term.Apply f x) env =
          __eo_and (__is_closed_rec f env) (__is_closed_rec x env) := by
            exact is_closed_rec_apply_eq_of_not_list_branch hEnv hNotList
      _ = __eo_and (__eo_is_closed_rec f env)
            (__eo_is_closed_rec x env) := by
            rw [hFEq, hXEq]
      _ = __eo_is_closed_rec (Term.Apply f x) env := by
            exact
              (eo_is_closed_rec_apply_eq_of_not_quantifier
                hEnv hNotForall hNotExists).symm
  · rcases hFBool with ⟨bf, hFBool⟩
    rcases hXBool with ⟨bx, hXBool⟩
    rw [eo_is_closed_rec_apply_eq_of_not_quantifier
      hEnv hNotForall hNotExists]
    exact eo_and_eq_boolean_of_boolean hFBool hXBool

theorem apply_args_have_smt_translation_of_non_none
    {f x : Term}
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt x)))
    (hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))) :
  eoHasSmtTranslation f ∧ eoHasSmtTranslation x :=
by
  unfold term_has_non_none_type at hNN
  have hApplyNN :
      __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt x)) ≠
        SmtType.None := by
    intro hNone
    exact hNN (by rw [hTy, hNone])
  rcases typeof_apply_non_none_cases hApplyNN with
    ⟨A, B, hF, hX, hA, hB⟩
  refine ⟨?_, ?_⟩
  · unfold eoHasSmtTranslation
    rcases hF with hFun | hDtc
    · rw [hFun]
      simp
    · rw [hDtc]
      simp
  · unfold eoHasSmtTranslation
    rw [hX]
    exact hA

theorem is_closed_rec_apply_generic_eq_and_bool_of_has_smt_translation
    {f x env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotList :
      ∀ q v vs,
        f ≠
          Term.Apply q
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
    (hNotForall :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.forall) vs)
    (hNotExists :
      ∀ vs, f ≠ Term.Apply (Term.UOp UserOp.exists) vs)
    (hTranslate :
      __eo_to_smt (Term.Apply f x) =
        SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x))
    (hTy :
      __smtx_typeof
          (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) =
        __smtx_typeof_apply (__smtx_typeof (__eo_to_smt f))
          (__smtx_typeof (__eo_to_smt x)))
    (hTrans : eoHasSmtTranslation (Term.Apply f x))
    (ihF :
      eoHasSmtTranslation f ->
        __is_closed_rec f env = __eo_is_closed_rec f env ∧
          ∃ b, __eo_is_closed_rec f env = Term.Boolean b)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b) :
  __is_closed_rec (Term.Apply f x) env =
    __eo_is_closed_rec (Term.Apply f x) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply f x) env = Term.Boolean b :=
by
  have hNN :
      term_has_non_none_type
        (SmtTerm.Apply (__eo_to_smt f) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  rcases apply_args_have_smt_translation_of_non_none hTy hNN with
    ⟨hFTrans, hXTrans⟩
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv hNotList hNotForall hNotExists
      (ihF hFTrans) (ihX hXTrans)

theorem term_not_eo_list_cons_of_has_smt_translation
    {x : Term}
    (hTrans : eoHasSmtTranslation x) :
  ∀ v vs,
    x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs :=
by
  intro v vs hEq
  subst x
  unfold eoHasSmtTranslation at hTrans
  rw [smtx_typeof_eo_list_cons_eq_none] at hTrans
  exact hTrans rfl

theorem is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_args
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXNotList :
      ∀ v vs,
        x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hYNotList :
      ∀ v vs,
        y ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (hY :
      __is_closed_rec y env = __eo_is_closed_rec y env ∧
        ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (hZ :
      __is_closed_rec z env = __eo_is_closed_rec z env ∧
        ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env =
        Term.Boolean b :=
by
  have hHead1 :
      __is_closed_rec (Term.Apply (Term.UOp op) x) env =
        __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
        ∃ b,
          __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
            Term.Boolean b :=
    is_closed_rec_apply_uop_eq_and_bool_of_arg hEnv hX
  have hMidNotList :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
  by
    intro q v vs hEq
    cases hEq
    exact hXNotList v vs rfl
  have hMidNotForall :
      ∀ vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply (Term.UOp UserOp.forall) vs :=
  by
    intro vs hEq
    cases hEq
    exact hNotForall rfl
  have hMidNotExists :
      ∀ vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply (Term.UOp UserOp.exists) vs :=
  by
    intro vs hEq
    cases hEq
    exact hNotExists rfl
  have hHead2 :
      __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y)
          env =
        __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y)
          env ∧
        ∃ b,
          __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y)
            env =
            Term.Boolean b :=
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv hMidNotList hMidNotForall hMidNotExists hHead1 hY
  have hOuterNotList :
      ∀ q v vs,
        Term.Apply (Term.Apply (Term.UOp op) x) y ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
  by
    intro q v vs hEq
    cases hEq
    exact hYNotList v vs rfl
  have hOuterNotForall :
      ∀ vs,
        Term.Apply (Term.Apply (Term.UOp op) x) y ≠
          Term.Apply (Term.UOp UserOp.forall) vs :=
  by
    intro vs hEq
    cases hEq
  have hOuterNotExists :
      ∀ vs,
        Term.Apply (Term.Apply (Term.UOp op) x) y ≠
          Term.Apply (Term.UOp UserOp.exists) vs :=
  by
    intro vs hEq
    cases hEq
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv hOuterNotList hOuterNotForall hOuterNotExists hHead2 hZ

theorem is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
    {op : UserOp} {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXTrans : eoHasSmtTranslation x)
    (hYTrans : eoHasSmtTranslation y)
    (hZTrans : eoHasSmtTranslation z)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_args
      hEnv hNotForall hNotExists
      (term_not_eo_list_cons_of_has_smt_translation hXTrans)
      (term_not_eo_list_cons_of_has_smt_translation hYTrans)
      (ihX hXTrans) (ihY hYTrans) (ihZ hZTrans)

theorem ite_args_have_smt_translation_of_has_smt_translation
    {c x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)) :
  eoHasSmtTranslation c ∧
    eoHasSmtTranslation x ∧
      eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.ite (__eo_to_smt c) (__eo_to_smt x)
          (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  rcases ite_args_of_non_none hNN with ⟨T, hC, hX, hY, hT⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hC (by simp),
    eo_has_smt_translation_of_smt_type_eq hX hT,
    eo_has_smt_translation_of_smt_type_eq hY hT⟩

theorem is_closed_rec_apply_apply_apply_ite_eq_and_bool_of_has_smt_translation
    {c x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y))
    (ihC :
      eoHasSmtTranslation c ->
        __is_closed_rec c env = __eo_is_closed_rec c env ∧
          ∃ b, __eo_is_closed_rec c env = Term.Boolean b)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.ite) c) x) y)
        env =
        Term.Boolean b :=
by
  rcases ite_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hCTrans, hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hCTrans hXTrans hYTrans ihC ihX ihY

theorem is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_args
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hXNotList :
      ∀ v vs,
        x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs)
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (hY :
      __is_closed_rec y env = __eo_is_closed_rec y env ∧
        ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
    __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean b :=
by
  have hHead :
      __is_closed_rec (Term.Apply (Term.UOp op) x) env =
        __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env ∧
        ∃ b,
          __eo_is_closed_rec (Term.Apply (Term.UOp op) x) env =
            Term.Boolean b :=
    is_closed_rec_apply_uop_eq_and_bool_of_arg hEnv hX
  have hOuterNotList :
      ∀ q v vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply q (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) :=
  by
    intro q v vs hEq
    cases hEq
    exact hXNotList v vs rfl
  have hOuterNotForall :
      ∀ vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply (Term.UOp UserOp.forall) vs :=
  by
    intro vs hEq
    cases hEq
    exact hNotForall rfl
  have hOuterNotExists :
      ∀ vs,
        Term.Apply (Term.UOp op) x ≠
          Term.Apply (Term.UOp UserOp.exists) vs :=
  by
    intro vs hEq
    cases hEq
    exact hNotExists rfl
  exact
    is_closed_rec_apply_generic_eq_and_bool_of_parts
      hEnv hOuterNotList hOuterNotForall hOuterNotExists hHead hY

theorem apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
    {op : UserOp} {x y : Term}
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y)) :
  ∀ v vs,
    x ≠ Term.Apply (Term.Apply Term.__eo_List_cons v) vs :=
by
  intro v vs hX
  subst x
  unfold eoHasSmtTranslation at hTrans
  exact hTrans
    (smtx_typeof_uop_eo_list_cons_apply_eq_none
      hNotForall hNotExists v vs y)

theorem is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_args
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hX :
      __is_closed_rec x env = __eo_is_closed_rec x env ∧
        ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (hY :
      __is_closed_rec y env = __eo_is_closed_rec y env ∧
        ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
    __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_args
      hEnv hNotForall hNotExists
      (apply_apply_uop_arg_not_list_of_nonquantifier_has_smt_translation
        hNotForall hNotExists hTrans)
      hX hY

theorem is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
    {op : UserOp} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : op ≠ UserOp.forall)
    (hNotExists : op ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp op) x) y))
    (hXTrans : eoHasSmtTranslation x)
    (hYTrans : eoHasSmtTranslation y)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
    __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec (Term.Apply (Term.Apply (Term.UOp op) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_args
      hEnv hNotForall hNotExists hTrans (ihX hXTrans) (ihY hYTrans)

theorem bool_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Bool)
          (native_ite (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Bool)
            SmtType.Bool SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases bool_binop_args_bool_of_non_none hTy hNN with ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem and_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.and (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact bool_binop_args_have_smt_translation_of_non_none
    (typeof_and_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem or_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.or (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact bool_binop_args_have_smt_translation_of_non_none
    (typeof_or_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem imp_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.imp (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact bool_binop_args_have_smt_translation_of_non_none
    (typeof_imp_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem xor_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof (SmtTerm.xor (__eo_to_smt x) (__eo_to_smt y)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.xor (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact bool_binop_args_have_smt_translation_of_non_none
    (typeof_xor_eq (__eo_to_smt x) (__eo_to_smt y)) hNN

theorem eq_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  have hEqNN :
      __smtx_typeof_eq (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ≠
        SmtType.None := by
    change
        __smtx_typeof (SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y)) ≠
          SmtType.None at hTrans
    rw [typeof_eq_eq] at hTrans
    exact hTrans
  unfold __smtx_typeof_eq __smtx_typeof_guard at hEqNN
  constructor
  · unfold eoHasSmtTranslation
    intro hX
    exact hEqNN (by simp [hX, native_ite, native_Teq])
  · unfold eoHasSmtTranslation
    intro hY
    cases hX : __smtx_typeof (__eo_to_smt x) <;>
      simp [hX, hY, native_ite, native_Teq] at hEqNN

theorem is_closed_rec_apply_apply_and_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) y) env =
        Term.Boolean b :=
by
  rcases and_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_or_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) y) env =
        Term.Boolean b :=
by
  rcases or_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_imp_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x) y) env =
        Term.Boolean b :=
by
  rcases imp_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_xor_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x) y) env =
        Term.Boolean b :=
by
  rcases xor_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_eq_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y) env =
        Term.Boolean b :=
by
  rcases eq_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y : Term}
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hArgs :
      term_has_non_none_type (smtOp (__eo_to_smt x) (__eo_to_smt y)) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (hTrans :
      eoHasSmtTranslation (Term.Apply (Term.Apply (Term.UOp eoOp) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  unfold eoHasSmtTranslation at hTrans
  have hNN :
      term_has_non_none_type (smtOp (__eo_to_smt x) (__eo_to_smt y)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  exact hArgs hNN

theorem is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hArgs :
      term_has_non_none_type (smtOp (__eo_to_smt x) (__eo_to_smt y)) ->
        eoHasSmtTranslation x ∧ eoHasSmtTranslation y)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  rcases
      apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
        hTranslate hArgs hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv hNotForall hNotExists hTrans hXTrans hYTrans ihX ihY

theorem apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
    {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x y z : Term}
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z) =
        smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))
    (hArgs :
      term_has_non_none_type
          (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) ->
        eoHasSmtTranslation x ∧
          eoHasSmtTranslation y ∧
            eoHasSmtTranslation z)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  unfold eoHasSmtTranslation at hTrans
  have hNN :
      term_has_non_none_type
        (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    rw [← hTranslate]
    exact hTrans
  exact hArgs hNN

theorem is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
    {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z))
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z) =
        smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))
    (hArgs :
      term_has_non_none_type
          (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) ->
        eoHasSmtTranslation x ∧
          eoHasSmtTranslation y ∧
            eoHasSmtTranslation z)
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
        env =
        Term.Boolean b :=
by
  rcases
      apply_apply_apply_uop_args_have_smt_translation_of_smt_triop_non_none
        hTranslate hArgs hTrans with
    ⟨hXTrans, hYTrans, hZTrans⟩
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv hNotForall hNotExists hXTrans hYTrans hZTrans ihX ihY ihZ

theorem arith_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_arith_overload_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases arith_binop_args_of_non_none hTy hNN with hArgs | hArgs
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩

theorem arith_binop_ret_bool_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) SmtType.Bool)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases arith_binop_ret_bool_args_of_non_none hTy hNN with hArgs | hArgs
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩

theorem arith_binop_ret_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases arith_binop_ret_args_of_non_none hTy hNN with hArgs | hArgs
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩
  · exact ⟨eo_has_smt_translation_of_smt_type_eq hArgs.1 (by simp),
      eo_has_smt_translation_of_smt_type_eq hArgs.2 (by simp)⟩

theorem int_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Int)
            ret SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases int_binop_args_of_non_none (op := op) (R := ret) hTy hNN with
    ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem map_type_components_non_none_of_eo_type_eq
    {x : Term} {A B : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt x) = SmtType.Map A B) :
  A ≠ SmtType.None ∧ B ≠ SmtType.None :=
by
  have hNN : term_has_non_none_type (__eo_to_smt x) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hNoNone :
      type_has_no_none_components (__smtx_typeof (__eo_to_smt x)) :=
    term_type_has_no_none_components_of_non_none (__eo_to_smt x) hNN
  have hMapNoNone : type_has_no_none_components (SmtType.Map A B) := by
    simpa [hTy] using hNoNone
  exact ⟨type_has_no_none_components_non_none hMapNoNone.1,
    type_has_no_none_components_non_none hMapNoNone.2⟩

theorem select_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.select (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases select_args_of_non_none hNN with ⟨A, B, hXTy, hYTy⟩
  have hComponents :
      A ≠ SmtType.None ∧ B ≠ SmtType.None :=
    map_type_components_non_none_of_eo_type_eq hXTy
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy hComponents.1⟩

theorem store_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.store (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases store_args_of_non_none hNN with
    ⟨A, B, hXTy, hYTy, hZTy⟩
  have hComponents :
      A ≠ SmtType.None ∧ B ≠ SmtType.None :=
    map_type_components_non_none_of_eo_type_eq hXTy
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy hComponents.1,
    eo_has_smt_translation_of_smt_type_eq hZTy hComponents.2⟩

theorem set_type_component_non_none_of_eo_type_eq
    {x : Term} {A : SmtType}
    (hTy : __smtx_typeof (__eo_to_smt x) = SmtType.Set A) :
  A ≠ SmtType.None :=
by
  have hNN : term_has_non_none_type (__eo_to_smt x) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  have hNoNone :
      type_has_no_none_components (__smtx_typeof (__eo_to_smt x)) :=
    term_type_has_no_none_components_of_non_none (__eo_to_smt x) hNN
  have hSetNoNone : type_has_no_none_components (SmtType.Set A) := by
    simpa [hTy] using hNoNone
  exact type_has_no_none_components_non_none hSetNoNone

theorem seq_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_seq_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_binop_args_of_non_none (op := op) hTy hNN with
    ⟨T, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem seq_binop_ret_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType}
    {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_seq_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_binop_args_of_non_none_ret (op := op) (R := ret) hTy hNN with
    ⟨T, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem seq_triop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm} {x y z : Term}
    (hTy :
      __smtx_typeof
          (op (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) =
        __smtx_typeof_seq_op_3
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt z)))
    (hNN :
      term_has_non_none_type
        (op (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases seq_triop_args_of_non_none (op := op) hTy hNN with
    ⟨T, hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem seq_nth_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.seq_nth (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_nth_args_of_non_none hNN with ⟨T, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem str_substr_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_substr (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_substr_args_of_non_none hNN with ⟨T, hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem str_indexof_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_indexof (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_indexof_args_of_non_none hNN with
    ⟨T, hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem str_at_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_at (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases str_at_args_of_non_none hNN with ⟨T, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem str_update_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_update (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_update_args_of_non_none hNN with ⟨T, hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem reglan_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases reglan_binop_args_of_non_none (op := op) hTy hNN with
    ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem seq_char_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType}
    {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y))
              (SmtType.Seq SmtType.Char))
            ret SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_char_binop_args_of_non_none (op := op) (ret := ret) hTy hNN with
    ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem seq_char_reglan_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType}
    {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            ret SmtType.None)
          SmtType.None)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases seq_char_reglan_args_of_non_none (op := op) (ret := ret) hTy hNN with
    ⟨hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem str_replace_re_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm} {x y z : Term}
    (hTy :
      __smtx_typeof
          (op (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            (native_ite
              (native_Teq (__smtx_typeof (__eo_to_smt z))
                (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (hNN :
      term_has_non_none_type
        (op (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_replace_re_args_of_non_none (op := op) hTy hNN with
    ⟨hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem str_indexof_re_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_indexof_re (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_indexof_re_args_of_non_none hNN with
    ⟨hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem str_indexof_re_split_args_have_smt_translation_of_non_none
    {x y z : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.str_indexof_re_split (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z))) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  rcases str_indexof_re_split_args_of_non_none hNN with
    ⟨hXTy, hYTy, hZTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hZTy (by simp)⟩

theorem set_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_sets_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases set_binop_args_of_non_none (op := op) hTy hNN with
    ⟨A, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem set_binop_ret_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType}
    {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_sets_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases set_binop_ret_args_of_non_none (op := op) (T := ret) hTy hNN with
    ⟨A, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem set_member_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.set_member (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases set_member_args_of_non_none hNN with ⟨A, hXTy, hYTy⟩
  have hANe : A ≠ SmtType.None :=
    set_type_component_non_none_of_eo_type_eq hYTy
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy hANe,
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem plus_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.plus) (smtOp := SmtTerm.plus) (by rfl)
      (fun hNN =>
        arith_binop_args_have_smt_translation_of_non_none
          (typeof_plus_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem neg_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.neg) (smtOp := SmtTerm.neg) (by rfl)
      (fun hNN =>
        arith_binop_args_have_smt_translation_of_non_none
          (typeof_neg_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem mult_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.mult) (smtOp := SmtTerm.mult) (by rfl)
      (fun hNN =>
        arith_binop_args_have_smt_translation_of_non_none
          (typeof_mult_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem lt_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.lt) (smtOp := SmtTerm.lt) (by rfl)
      (fun hNN =>
        arith_binop_ret_bool_args_have_smt_translation_of_non_none
          (typeof_lt_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem leq_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.leq) (smtOp := SmtTerm.leq) (by rfl)
      (fun hNN =>
        arith_binop_ret_bool_args_have_smt_translation_of_non_none
          (typeof_leq_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem gt_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.gt) (smtOp := SmtTerm.gt) (by rfl)
      (fun hNN =>
        arith_binop_ret_bool_args_have_smt_translation_of_non_none
          (typeof_gt_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem geq_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.geq) (smtOp := SmtTerm.geq) (by rfl)
      (fun hNN =>
        arith_binop_ret_bool_args_have_smt_translation_of_non_none
          (typeof_geq_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem div_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.div) (smtOp := SmtTerm.div) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_div_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem mod_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.mod) (smtOp := SmtTerm.mod) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_mod_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem multmult_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.multmult) (smtOp := SmtTerm.multmult) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_multmult_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem div_total_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.div_total) (smtOp := SmtTerm.div_total) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_div_total_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem mod_total_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.mod_total) (smtOp := SmtTerm.mod_total) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_mod_total_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem multmult_total_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.multmult_total) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.multmult_total) (smtOp := SmtTerm.multmult_total)
      (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_multmult_total_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem divisible_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.divisible) (smtOp := SmtTerm.divisible) (by rfl)
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none
          (typeof_divisible_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem qdiv_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.qdiv) (smtOp := SmtTerm.qdiv) (by rfl)
      (fun hNN =>
        arith_binop_ret_args_have_smt_translation_of_non_none
          (typeof_qdiv_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem qdiv_total_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.qdiv_total) (smtOp := SmtTerm.qdiv_total) (by rfl)
      (fun hNN =>
        arith_binop_ret_args_have_smt_translation_of_non_none
          (typeof_qdiv_total_eq (__eo_to_smt x) (__eo_to_smt y)) hNN)
      hTrans

theorem select_args_have_smt_translation_of_has_smt_translation
    {x y : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y)) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  exact
    apply_apply_uop_args_have_smt_translation_of_smt_binop_non_none
      (eoOp := UserOp.select) (smtOp := SmtTerm.select) (by rfl)
      select_args_have_smt_translation_of_non_none hTrans

theorem store_args_have_smt_translation_of_has_smt_translation
    {x y z : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
          z)) :
  eoHasSmtTranslation x ∧
    eoHasSmtTranslation y ∧
      eoHasSmtTranslation z :=
by
  unfold eoHasSmtTranslation at hTrans
  change
      __smtx_typeof
          (SmtTerm.store (__eo_to_smt x) (__eo_to_smt y)
            (__eo_to_smt z)) ≠
        SmtType.None at hTrans
  have hNN :
      term_has_non_none_type
        (SmtTerm.store (__eo_to_smt x) (__eo_to_smt y)
          (__eo_to_smt z)) := by
    unfold term_has_non_none_type
    exact hTrans
  exact store_args_have_smt_translation_of_non_none hNN

theorem is_closed_rec_apply_apply_plus_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x) y) env =
        Term.Boolean b :=
by
  rcases plus_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_neg_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x) y) env =
        Term.Boolean b :=
by
  rcases neg_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_mult_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x) y) env =
        Term.Boolean b :=
by
  rcases mult_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_lt_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x) y) env =
        Term.Boolean b :=
by
  rcases lt_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_leq_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x) y) env =
        Term.Boolean b :=
by
  rcases leq_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_gt_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x) y) env =
        Term.Boolean b :=
by
  rcases gt_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_geq_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x) y) env =
        Term.Boolean b :=
by
  rcases geq_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_div_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.div) x) y) env =
        Term.Boolean b :=
by
  rcases div_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_mod_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x) y) env =
        Term.Boolean b :=
by
  rcases mod_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_multmult_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x) y) env =
        Term.Boolean b :=
by
  rcases multmult_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_div_total_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x) y) env =
        Term.Boolean b :=
by
  rcases div_total_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_mod_total_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x) y) env =
        Term.Boolean b :=
by
  rcases mod_total_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_multmult_total_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.multmult_total) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x) y)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x) y)
        env =
        Term.Boolean b :=
by
  rcases
      multmult_total_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_divisible_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x) y) env =
        Term.Boolean b :=
by
  rcases divisible_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_qdiv_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv) x) y) env =
        Term.Boolean b :=
by
  rcases qdiv_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_qdiv_total_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.qdiv_total) x) y) env =
        Term.Boolean b :=
by
  rcases qdiv_total_args_have_smt_translation_of_has_smt_translation
      hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_select_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.select) x) y) env =
        Term.Boolean b :=
by
  rcases select_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans⟩
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hTrans hXTrans hYTrans ihX ihY

theorem is_closed_rec_apply_apply_apply_store_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
          z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
        z) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp UserOp.store) x) y)
          z) env =
        Term.Boolean b :=
by
  rcases store_args_have_smt_translation_of_has_smt_translation hTrans with
    ⟨hXTrans, hYTrans, hZTrans⟩
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_has_smt_translation_and_arg_trans
      hEnv (by decide) (by decide) hXTrans hYTrans hZTrans ihX ihY ihZ

theorem is_closed_rec_apply_apply_uop_seq_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_seq_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_seq_binop_ret_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_seq_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_binop_ret_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_seq_nth_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.seq_nth) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      seq_nth_args_have_smt_translation_of_non_none ihX ihY

theorem is_closed_rec_apply_apply_str_at_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_at) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_at_args_have_smt_translation_of_non_none ihX ihY

theorem is_closed_rec_apply_apply_uop_reglan_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.RegLan)
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            SmtType.RegLan SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        reglan_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_seq_char_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y))
              (SmtType.Seq SmtType.Char))
            ret SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_char_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_seq_char_reglan_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            ret SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_char_reglan_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_set_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_sets_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        set_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_set_binop_ret_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_sets_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        set_binop_ret_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_set_member_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.set_member) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      set_member_args_have_smt_translation_of_non_none ihX ihY

theorem is_closed_rec_apply_apply_apply_uop_seq_triop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z) =
        smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))
    (hTy :
      __smtx_typeof
          (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) =
        __smtx_typeof_seq_op_3
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt z)))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        seq_triop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_substr_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_substr) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_substr_args_have_smt_translation_of_non_none ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_indexof_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_indexof_args_have_smt_translation_of_non_none ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_update_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_update) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_update_args_have_smt_translation_of_non_none ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_uop_str_replace_re_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp}
    {smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm}
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt
          (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z) =
        smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z))
    (hTy :
      __smtx_typeof
          (smtOp (__eo_to_smt x) (__eo_to_smt y) (__eo_to_smt z)) =
        native_ite
          (native_Teq (__smtx_typeof (__eo_to_smt x))
            (SmtType.Seq SmtType.Char))
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.RegLan)
            (native_ite
              (native_Teq (__smtx_typeof (__eo_to_smt z))
                (SmtType.Seq SmtType.Char))
              (SmtType.Seq SmtType.Char) SmtType.None)
            SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        str_replace_re_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_indexof_re_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y)
          z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y)
        z) env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y)
        z) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.Apply (Term.UOp UserOp.str_indexof_re) x) y)
          z) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_indexof_re_args_have_smt_translation_of_non_none ihX ihY ihZ

theorem is_closed_rec_apply_apply_apply_str_indexof_re_split_eq_and_bool_of_has_smt_translation
    {x y z env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_indexof_re_split) x) y) z))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b)
    (ihZ :
      eoHasSmtTranslation z ->
        __is_closed_rec z env = __eo_is_closed_rec z env ∧
          ∃ b, __eo_is_closed_rec z env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_indexof_re_split) x) y) z)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply
          (Term.Apply (Term.UOp UserOp.str_indexof_re_split) x) y) z)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply
            (Term.Apply (Term.UOp UserOp.str_indexof_re_split) x) y) z)
        env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_triop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      str_indexof_re_split_args_have_smt_translation_of_non_none
      ihX ihY ihZ

theorem is_closed_rec_apply_apply_uop_arith_binop_ret_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_arith_overload_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        arith_binop_ret_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_int_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        native_ite (native_Teq (__smtx_typeof (__eo_to_smt x)) SmtType.Int)
          (native_ite
            (native_Teq (__smtx_typeof (__eo_to_smt y)) SmtType.Int)
            ret SmtType.None)
          SmtType.None)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        int_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem bv_concat_args_have_smt_translation_of_non_none
    {x y : Term}
    (hNN :
      term_has_non_none_type
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases bv_concat_args_of_non_none hNN with ⟨w1, w2, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem bv_binop_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases bv_binop_args_of_non_none (op := op) hTy hNN with
    ⟨w, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem bv_binop_ret_args_have_smt_translation_of_non_none
    {op : SmtTerm -> SmtTerm -> SmtTerm} {ret : SmtType} {x y : Term}
    (hTy :
      __smtx_typeof (op (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hNN : term_has_non_none_type (op (__eo_to_smt x) (__eo_to_smt y))) :
  eoHasSmtTranslation x ∧ eoHasSmtTranslation y :=
by
  rcases bv_binop_ret_args_of_non_none (op := op) (ret := ret) hTy hNN with
    ⟨w, hXTy, hYTy⟩
  exact ⟨eo_has_smt_translation_of_smt_type_eq hXTy (by simp),
    eo_has_smt_translation_of_smt_type_eq hYTy (by simp)⟩

theorem is_closed_rec_apply_apply_concat_eq_and_bool_of_has_smt_translation
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv (by decide) (by decide) hTrans (by rfl)
      bv_concat_args_have_smt_translation_of_non_none ihX ihY

theorem is_closed_rec_apply_apply_uop_bv_binop_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)))
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        bv_binop_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem is_closed_rec_apply_apply_uop_bv_binop_ret_eq_and_bool_of_has_smt_translation
    {eoOp : UserOp} {smtOp : SmtTerm -> SmtTerm -> SmtTerm}
    {ret : SmtType} {x y env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    (hNotForall : eoOp ≠ UserOp.forall)
    (hNotExists : eoOp ≠ UserOp.exists)
    (hTranslate :
      __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) =
        smtOp (__eo_to_smt x) (__eo_to_smt y))
    (hTy :
      __smtx_typeof (smtOp (__eo_to_smt x) (__eo_to_smt y)) =
        __smtx_typeof_bv_op_2_ret
          (__smtx_typeof (__eo_to_smt x))
          (__smtx_typeof (__eo_to_smt y)) ret)
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y))
    (ihX :
      eoHasSmtTranslation x ->
        __is_closed_rec x env = __eo_is_closed_rec x env ∧
          ∃ b, __eo_is_closed_rec x env = Term.Boolean b)
    (ihY :
      eoHasSmtTranslation y ->
        __is_closed_rec y env = __eo_is_closed_rec y env ∧
          ∃ b, __eo_is_closed_rec y env = Term.Boolean b) :
  __is_closed_rec (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp eoOp) x) y) env =
        Term.Boolean b :=
by
  exact
    is_closed_rec_apply_apply_uop_nonquantifier_eq_and_bool_of_smt_binop_non_none
      hEnv hNotForall hNotExists hTrans hTranslate
      (fun hNN =>
        bv_binop_ret_args_have_smt_translation_of_non_none hTy hNN)
      ihX ihY

theorem eo_list_concat_nil_left_eq_of_env
    {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars) :
  __eo_list_concat Term.__eo_List_cons Term.__eo_List_nil env = env :=
by
  have hNilList :
      __eo_is_list Term.__eo_List_cons Term.__eo_List_nil =
        Term.Boolean true := by
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil,
      __eo_requires, __eo_is_ok, native_ite, native_teq, native_not]
  have hEnvList := hEnv.is_list
  cases hEnv <;>
    simp [__eo_list_concat, __eo_list_concat_rec, __eo_requires,
      hNilList, hEnvList, native_ite, native_teq, native_not]

/--
For quantifiers with an empty binder list, `__is_closed_rec` reaches the
generic application branch while `__eo_is_closed_rec` reaches its quantifier
branch. The extra head check is `true`, and concatenating the empty binder
list leaves the environment unchanged.
-/
theorem is_closed_rec_quantifier_nil_branch_eq_and_bool_of_body
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hOp : op = UserOp.forall ∨ op = UserOp.exists)
    (hEnv : EoSmtVarEnv env vars)
    (body : Term)
    (hBody :
      __is_closed_rec body env = __eo_is_closed_rec body env ∧
        ∃ b, __eo_is_closed_rec body env = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp op) Term.__eo_List_nil) body)
      env =
    __eo_is_closed_rec
      (Term.Apply (Term.Apply (Term.UOp op) Term.__eo_List_nil) body)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply (Term.Apply (Term.UOp op) Term.__eo_List_nil) body)
        env =
      Term.Boolean b :=
by
  rcases hBody with ⟨hBodyEq, hBodyBool⟩
  rcases hBodyBool with ⟨b, hBodyBool⟩
  have hConcat := eo_list_concat_nil_left_eq_of_env hEnv
  rcases hOp with hForall | hExists
  · subst op
    refine ⟨?_, ?_⟩
    · cases hEnv <;>
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq, hConcat]
          using eo_and_true_left_eq_of_boolean hBodyBool
    · exact ⟨b, by
        cases hEnv <;> simpa [__eo_is_closed_rec, hConcat] using hBodyBool⟩
  · subst op
    refine ⟨?_, ?_⟩
    · cases hEnv <;>
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq, hConcat]
          using eo_and_true_left_eq_of_boolean hBodyBool
    · exact ⟨b, by
        cases hEnv <;> simpa [__eo_is_closed_rec, hConcat] using hBodyBool⟩

/--
The broad binder-list branch of `__is_closed_rec` agrees with
`__eo_is_closed_rec` for actual quantifier heads, once the recursive body result
is known to agree and to be boolean.
-/
theorem is_closed_rec_quantifier_list_branch_eq_of_body
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hOp : op = UserOp.forall ∨ op = UserOp.exists)
    (hEnv : EoSmtVarEnv env vars)
    (v vs body : Term)
    (hBodyEq :
      __is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env))
    (hBodyBool :
      ∃ b,
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
          Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env :=
by
  rcases hBodyBool with ⟨b, hBodyBool⟩
  rcases hOp with hForall | hExists
  · subst op
    cases hEnv with
    | nil =>
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq]
          using eo_and_true_left_eq_of_boolean hBodyBool
    | cons hTail =>
        rename_i s' T' env' vars'
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq]
          using eo_and_true_left_eq_of_boolean hBodyBool
  · subst op
    cases hEnv with
    | nil =>
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq]
          using eo_and_true_left_eq_of_boolean hBodyBool
    | cons hTail =>
        rename_i s' T' env' vars'
        simpa [__is_closed_rec, __eo_is_closed_rec, hBodyEq]
          using eo_and_true_left_eq_of_boolean hBodyBool

/--
SMT-translatability supplies the quantifier-head fact for the `UOp` binder-list
case; the remaining obligations are exactly the recursive body comparison in
the concatenated environment.
-/
theorem is_closed_rec_uop_list_branch_eq_of_has_smt_translation_and_body
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hBodyEq :
      __is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env))
    (hBodyBool :
      ∃ b,
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
          Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env :=
by
  exact
    is_closed_rec_quantifier_list_branch_eq_of_body
      (is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
        hTrans)
      hEnv v vs body hBodyEq hBodyBool

theorem is_closed_rec_uop_list_branch_eq_and_bool_of_has_smt_translation_and_body
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (hBody :
      __is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
        __eo_is_closed_rec body
          (__eo_list_concat Term.__eo_List_cons
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) ∧
        ∃ b,
          __eo_is_closed_rec body
            (__eo_list_concat Term.__eo_List_cons
              (Term.Apply (Term.Apply Term.__eo_List_cons v) vs) env) =
            Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)
        env =
      Term.Boolean b :=
by
  rcases hBody with ⟨hBodyEq, hBodyBool⟩
  refine ⟨
    is_closed_rec_uop_list_branch_eq_of_has_smt_translation_and_body
      hEnv hTrans hBodyEq hBodyBool,
    ?_⟩
  rcases hBodyBool with ⟨b, hBodyBool⟩
  rcases
    is_closed_rec_uop_list_branch_head_quantifier_of_has_smt_translation
      hTrans with hForall | hExists
  · subst op
    cases hEnv with
    | nil =>
        exact ⟨b, by simpa [__eo_is_closed_rec] using hBodyBool⟩
    | cons hTail =>
        exact ⟨b, by simpa [__eo_is_closed_rec] using hBodyBool⟩
  · subst op
    cases hEnv with
    | nil =>
        exact ⟨b, by simpa [__eo_is_closed_rec] using hBodyBool⟩
    | cons hTail =>
        exact ⟨b, by simpa [__eo_is_closed_rec] using hBodyBool⟩

theorem is_closed_rec_uop_list_branch_eq_and_bool_of_has_smt_translation
    {op : UserOp} {env : Term} {vars : List SmtVarKey}
    (hEnv : EoSmtVarEnv env vars)
    {v vs body : Term}
    (hTrans :
      eoHasSmtTranslation
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body))
    (ihBody :
      ∀ {env' : Term} {vars' : List SmtVarKey},
        EoSmtVarEnv env' vars' ->
          eoHasSmtTranslation body ->
            __is_closed_rec body env' = __eo_is_closed_rec body env' ∧
              ∃ b, __eo_is_closed_rec body env' = Term.Boolean b) :
  __is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env =
    __eo_is_closed_rec
      (Term.Apply
        (Term.Apply (Term.UOp op)
          (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
        body)
      env ∧
    ∃ b,
      __eo_is_closed_rec
        (Term.Apply
          (Term.Apply (Term.UOp op)
            (Term.Apply (Term.Apply Term.__eo_List_cons v) vs))
          body)
        env =
      Term.Boolean b :=
by
  rcases body_obligations_of_uop_list_branch_has_smt_translation
      hEnv hTrans with
    ⟨hBodyTrans, ⟨vars', hBodyEnv⟩⟩
  exact
    is_closed_rec_uop_list_branch_eq_and_bool_of_has_smt_translation_and_body
      hEnv hTrans (ihBody hBodyEnv hBodyTrans)

theorem is_closed_rec_var_eq_eo_is_closed
    (s : native_String) (T : Term) :
  __is_closed_rec (Term.Var (Term.String s) T) Term.__eo_List_nil =
    __eo_is_closed (Term.Var (Term.String s) T) :=
by
  simpa [__eo_is_closed] using
    is_closed_rec_var_eq_eo_is_closed_rec_var
      EoSmtVarEnv.nil s T
