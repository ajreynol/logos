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

theorem is_closed_rec_var_eq_eo_is_closed
    (s : native_String) (T : Term) :
  __is_closed_rec (Term.Var (Term.String s) T) Term.__eo_List_nil =
    __eo_is_closed (Term.Var (Term.String s) T) :=
by
  simpa [__eo_is_closed] using
    is_closed_rec_var_eq_eo_is_closed_rec_var
      EoSmtVarEnv.nil s T
