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

theorem is_closed_rec_var_eq_eo_is_closed
    (s : native_String) (T : Term) :
  __is_closed_rec (Term.Var (Term.String s) T) Term.__eo_List_nil =
    __eo_is_closed (Term.Var (Term.String s) T) :=
by
  simpa [__eo_is_closed] using
    is_closed_rec_var_eq_eo_is_closed_rec_var
      EoSmtVarEnv.nil s T
