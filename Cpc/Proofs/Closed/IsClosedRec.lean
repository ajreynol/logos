import Lean
import Cpc.Proofs.Common
import Cpc.Proofs.Assumptions
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
