import CpcMini.Proofs.Translation.Base

open Eo
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000
set_option allowUnsafeReducibility true
attribute [local reducible] __smtx_typeof

namespace TranslationProofs

def eo_fun_ends_in_bool : Term -> Prop
  | Term.Apply (Term.Apply Term.FunType _) U => U = Term.Bool ∨ eo_fun_ends_in_bool U
  | _ => False

theorem eo_to_smt_type_none_of_fun_ends_in_bool
    {T : Term} :
    eo_fun_ends_in_bool T ->
      __eo_to_smt_type T = SmtType.None := by
  intro h
  cases T with
  | Apply T1 T2 =>
      cases T1 with
      | Apply T11 T12 =>
          cases T11 <;> simp [eo_fun_ends_in_bool, __eo_to_smt_type] at h ⊢
      | _ =>
          simp [eo_fun_ends_in_bool] at h
  | _ =>
      simp [eo_fun_ends_in_bool] at h

theorem eo_typeof_dt_cons_rec_not_bool_and_not_fun_ends_in_bool
    (s : eo_lit_String) (d0 : Datatype) :
    ∀ (d : Datatype) (i : eo_lit_Nat),
      __eo_typeof_dt_cons_rec (Term.DatatypeType s d0) d i ≠ Term.Bool ∧
        ¬ eo_fun_ends_in_bool (__eo_typeof_dt_cons_rec (Term.DatatypeType s d0) d i)
  | Datatype.null, i => by
      cases i <;> simp [__eo_typeof_dt_cons_rec, eo_fun_ends_in_bool]
  | Datatype.sum DatatypeCons.unit d, eo_lit_nat_zero => by
      simp [__eo_typeof_dt_cons_rec, eo_fun_ends_in_bool]
  | Datatype.sum (DatatypeCons.cons U c) d, eo_lit_nat_zero => by
      simpa [__eo_typeof_dt_cons_rec, eo_fun_ends_in_bool] using
        eo_typeof_dt_cons_rec_not_bool_and_not_fun_ends_in_bool
          s d0 (Datatype.sum c d) eo_lit_nat_zero
  | Datatype.sum c d, eo_lit_nat_succ n => by
      simpa [__eo_typeof_dt_cons_rec] using
        eo_typeof_dt_cons_rec_not_bool_and_not_fun_ends_in_bool s d0 d n
termination_by d i => sizeOf d + i
decreasing_by
  all_goals
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    omega

@[simp] theorem eo_to_smt_term_dt_cons
    (s : eo_lit_String) (d : Datatype) (i : eo_lit_Nat) :
    __eo_to_smt (Term.DtCons s d i) = SmtTerm.DtCons s (__eo_to_smt_datatype d) i := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_term_dt_sel
    (s : eo_lit_String) (d : Datatype) (i j : eo_lit_Nat) :
    __eo_to_smt (Term.DtSel s d i j) = SmtTerm.DtSel s (__eo_to_smt_datatype d) i j := by
  simp [__eo_to_smt.eq_def]

@[simp] theorem eo_to_smt_datatype_cons_unit :
    __eo_to_smt_datatype_cons DatatypeCons.unit = SmtDatatypeCons.unit := rfl

@[simp] theorem eo_to_smt_datatype_null :
    __eo_to_smt_datatype Datatype.null = SmtDatatype.null := rfl

@[simp] theorem eo_to_smt_type_datatype (s : eo_lit_String) (d : Datatype) :
    __eo_to_smt_type (Term.DatatypeType s d) = SmtType.Datatype s (__eo_to_smt_datatype d) := by
  simp [__eo_to_smt_type]

@[simp] theorem smtx_typeof_dt_sel_head_none
    (s : smt_lit_String) (d : SmtDatatype) (i j : smt_lit_Nat) :
    __smtx_typeof (SmtTerm.DtSel s d i j) = SmtType.None := rfl

private theorem eo_dt_sel_return_bool_of_substituted_constructor
    (s : eo_lit_String) (d : Datatype) :
    ∀ (c : DatatypeCons) (d0 : Datatype) (j : eo_lit_Nat),
      __eo_typeof_dt_sel_return
          (Datatype.sum (__eo_dtc_substitute s d c) (__eo_dt_substitute s d d0))
          eo_lit_nat_zero j = Term.Bool ->
        __eo_typeof_dt_sel_return (Datatype.sum c d0) eo_lit_nat_zero j = Term.Bool := by
  intro c d0 j
  induction j generalizing c d0 with
  | zero =>
      cases c with
      | unit =>
          simp [__eo_dtc_substitute, __eo_typeof_dt_sel_return]
      | cons T c =>
          cases T with
          | DatatypeTypeRef a =>
              by_cases hEq : a = s <;>
                simp [__eo_typeof_dt_sel_return, __eo_dtc_substitute, eo_lit_ite,
                  eo_lit_teq, hEq]
          | _ =>
              simp [__eo_typeof_dt_sel_return, __eo_dtc_substitute, eo_lit_ite,
                eo_lit_teq, eo_lit_streq]
  | succ j ih =>
      intro h
      cases c with
      | unit =>
          simp [__eo_dtc_substitute, __eo_typeof_dt_sel_return] at h
      | cons T c =>
          cases T with
          | DatatypeType s2 d2 =>
              simpa [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_lit_ite, eo_lit_streq] using
                ih c d0 (by
                  simpa [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_lit_ite, eo_lit_streq] using h)
          | _ =>
              simpa [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_lit_ite, eo_lit_teq] using
                ih c d0 (by
                  simpa [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_lit_ite, eo_lit_teq] using h)

private theorem eo_dt_sel_return_bool_of_substituted_datatype
    (s : eo_lit_String) (d : Datatype) :
    ∀ (d0 : Datatype) (i j : eo_lit_Nat),
      __eo_typeof_dt_sel_return (__eo_dt_substitute s d d0) i j = Term.Bool ->
        __eo_typeof_dt_sel_return d0 i j = Term.Bool := by
  intro d0 i j
  induction i generalizing d0 with
  | zero =>
      cases d0 with
      | null =>
          simp [__eo_dt_substitute, __eo_typeof_dt_sel_return]
      | sum c d0 =>
          intro h
          have h' :
              __eo_typeof_dt_sel_return
                  (Datatype.sum (__eo_dtc_substitute s d c) (__eo_dt_substitute s d d0))
                  eo_lit_nat_zero j = Term.Bool := by
            simpa [__eo_dt_substitute] using h
          exact eo_dt_sel_return_bool_of_substituted_constructor s d c d0 j h'
  | succ i ih =>
      cases d0 with
      | null =>
          simp [__eo_dt_substitute, __eo_typeof_dt_sel_return]
      | sum c d0 =>
          intro h
          simpa [__eo_typeof_dt_sel_return] using
            ih d0 (by
              simpa [__eo_dt_substitute, __eo_typeof_dt_sel_return] using h)

private theorem smtx_dt_sel_return_bool_of_constructor :
    ∀ (c : DatatypeCons) (d : Datatype) (j : eo_lit_Nat),
      __eo_typeof_dt_sel_return (Datatype.sum c d) eo_lit_nat_zero j = Term.Bool ->
        __smtx_ret_typeof_sel_rec
          (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
          eo_lit_nat_zero j = SmtType.Bool := by
  intro c d j
  induction j generalizing c d with
  | zero =>
      cases c with
      | unit =>
          simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec]
      | cons T c =>
          cases T <;>
            simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
              __eo_to_smt_datatype_cons, __eo_to_smt_type]
  | succ j ih =>
      intro h
      cases c with
      | unit =>
          simp [__eo_typeof_dt_sel_return] at h
      | cons T c =>
          simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
            __eo_to_smt_datatype_cons] using
            ih c d (by
              simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
                __eo_to_smt_datatype_cons] using h)

private theorem smtx_dt_sel_return_bool_of_datatype :
    ∀ (d : Datatype) (i j : eo_lit_Nat),
      __eo_typeof_dt_sel_return d i j = Term.Bool ->
        __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j = SmtType.Bool := by
  intro d i j
  induction i generalizing d with
  | zero =>
      cases d with
      | null =>
          simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec]
      | sum c d =>
          intro h
          exact smtx_dt_sel_return_bool_of_constructor c d j h
  | succ i ih =>
      cases d with
      | null =>
          simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec]
      | sum c d =>
          intro h
          simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype] using
            ih d (by
              simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec] using h)

private theorem smtx_dt_sel_return_bool_under_constructor_substitution
    (s : smt_lit_String) (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (d0 : SmtDatatype) (j : smt_lit_Nat),
      __smtx_ret_typeof_sel_rec (SmtDatatype.sum c d0) eo_lit_nat_zero j = SmtType.Bool ->
        __smtx_ret_typeof_sel_rec
          (SmtDatatype.sum (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d d0))
          eo_lit_nat_zero j = SmtType.Bool := by
  intro c d0 j
  induction j generalizing c d0 with
  | zero =>
      cases c with
      | unit =>
          simp [__smtx_ret_typeof_sel_rec]
      | cons T c =>
          cases T <;>
            simp [__smtx_ret_typeof_sel_rec, __smtx_dtc_substitute, smt_lit_ite,
              smt_lit_Teq]
  | succ j ih =>
      intro h
      cases c with
      | unit =>
          simp [__smtx_ret_typeof_sel_rec] at h
      | cons T c =>
          cases T with
          | Datatype s2 d2 =>
              simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec, smt_lit_ite, smt_lit_streq] using
                ih c d0 (by
                  simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec, smt_lit_ite, smt_lit_streq] using h)
          | _ =>
              simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec, smt_lit_ite, smt_lit_Teq] using
                ih c d0 (by
                  simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec, smt_lit_ite, smt_lit_Teq] using h)

private theorem smtx_dt_sel_return_bool_under_datatype_substitution
    (s : smt_lit_String) (d : SmtDatatype) :
    ∀ (d0 : SmtDatatype) (i j : smt_lit_Nat),
      __smtx_ret_typeof_sel_rec d0 i j = SmtType.Bool ->
        __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d0) i j = SmtType.Bool := by
  intro d0 i j
  induction i generalizing d0 with
  | zero =>
      cases d0 with
      | null =>
          simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec]
      | sum c d0 =>
          intro h
          have h' :
              __smtx_ret_typeof_sel_rec (SmtDatatype.sum c d0) eo_lit_nat_zero j =
                SmtType.Bool := by
            simpa [__smtx_ret_typeof_sel_rec] using h
          exact smtx_dt_sel_return_bool_under_constructor_substitution s d c d0 j h'
  | succ i ih =>
      cases d0 with
      | null =>
          simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec]
      | sum c d0 =>
          intro h
          simpa [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec] using
            ih d0 (by
              simpa [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec] using h)

theorem smtx_ret_typeof_sel_bool_of_eo_dt_sel_return_bool
    (s : eo_lit_String) (d : Datatype) (i j : eo_lit_Nat) :
    __eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j = Term.Bool ->
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j = SmtType.Bool := by
  intro hBool
  have hOrig : __eo_typeof_dt_sel_return d i j = Term.Bool :=
    eo_dt_sel_return_bool_of_substituted_datatype s d d i j hBool
  have hDirect :
      __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j = SmtType.Bool :=
    smtx_dt_sel_return_bool_of_datatype d i j hOrig
  unfold __smtx_ret_typeof_sel
  exact smtx_dt_sel_return_bool_under_datatype_substitution
    s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d) i j hDirect

private theorem eo_dt_sel_return_fun_ends_in_bool_of_substituted_constructor
    (s : eo_lit_String) (d : Datatype) :
    ∀ (c : DatatypeCons) (d0 : Datatype) (j : eo_lit_Nat),
      eo_fun_ends_in_bool
          (__eo_typeof_dt_sel_return
            (Datatype.sum (__eo_dtc_substitute s d c) (__eo_dt_substitute s d d0))
            eo_lit_nat_zero j) ->
        eo_fun_ends_in_bool (__eo_typeof_dt_sel_return (Datatype.sum c d0) eo_lit_nat_zero j) := by
  intro c d0 j
  induction j generalizing c d0 with
  | zero =>
      cases c with
      | unit =>
          simp [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_fun_ends_in_bool]
      | cons T c =>
          cases T with
          | DatatypeTypeRef a =>
              by_cases hEq : a = s <;>
                simp [__eo_typeof_dt_sel_return, __eo_dtc_substitute, eo_lit_ite,
                  eo_lit_teq, hEq, eo_fun_ends_in_bool]
          | _ =>
              simp [__eo_typeof_dt_sel_return, __eo_dtc_substitute, eo_lit_ite,
                eo_lit_teq, eo_lit_streq, eo_fun_ends_in_bool]
  | succ j ih =>
      intro h
      cases c with
      | unit =>
          simp [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_fun_ends_in_bool] at h
      | cons T c =>
          cases T with
          | DatatypeType s2 d2 =>
              simpa [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_lit_ite, eo_lit_streq] using
                ih c d0 (by
                  simpa [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_lit_ite, eo_lit_streq] using h)
          | _ =>
              simpa [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_lit_ite, eo_lit_teq] using
                ih c d0 (by
                  simpa [__eo_dtc_substitute, __eo_typeof_dt_sel_return, eo_lit_ite, eo_lit_teq] using h)

private theorem eo_dt_sel_return_fun_ends_in_bool_of_substituted_datatype
    (s : eo_lit_String) (d : Datatype) :
    ∀ (d0 : Datatype) (i j : eo_lit_Nat),
      eo_fun_ends_in_bool (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d0) i j) ->
        eo_fun_ends_in_bool (__eo_typeof_dt_sel_return d0 i j) := by
  intro d0 i j
  induction i generalizing d0 with
  | zero =>
      cases d0 with
      | null =>
          simp [__eo_dt_substitute, __eo_typeof_dt_sel_return, eo_fun_ends_in_bool]
      | sum c d0 =>
          intro h
          have h' :
              eo_fun_ends_in_bool
                (__eo_typeof_dt_sel_return
                  (Datatype.sum (__eo_dtc_substitute s d c) (__eo_dt_substitute s d d0))
                  eo_lit_nat_zero j) := by
            simpa [__eo_dt_substitute] using h
          exact eo_dt_sel_return_fun_ends_in_bool_of_substituted_constructor s d c d0 j h'
  | succ i ih =>
      cases d0 with
      | null =>
          simp [__eo_dt_substitute, __eo_typeof_dt_sel_return, eo_fun_ends_in_bool]
      | sum c d0 =>
          intro h
          simpa [__eo_typeof_dt_sel_return] using
            ih d0 (by
              simpa [__eo_dt_substitute, __eo_typeof_dt_sel_return] using h)

private theorem smtx_dt_sel_return_none_of_constructor :
    ∀ (c : DatatypeCons) (d : Datatype) (j : eo_lit_Nat),
      eo_fun_ends_in_bool (__eo_typeof_dt_sel_return (Datatype.sum c d) eo_lit_nat_zero j) ->
        __smtx_ret_typeof_sel_rec
          (SmtDatatype.sum (__eo_to_smt_datatype_cons c) (__eo_to_smt_datatype d))
          eo_lit_nat_zero j = SmtType.None := by
  intro c d j
  induction j generalizing c d with
  | zero =>
      cases c with
      | unit =>
          simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, eo_fun_ends_in_bool]
      | cons T c =>
          intro h
          have hT : eo_fun_ends_in_bool T := by
            simpa [__eo_typeof_dt_sel_return] using h
          have hNone : __eo_to_smt_type T = SmtType.None :=
            eo_to_smt_type_none_of_fun_ends_in_bool hT
          simpa [__smtx_ret_typeof_sel_rec,
            __eo_to_smt_datatype_cons, hNone] using hNone
  | succ j ih =>
      intro h
      cases c with
      | unit =>
          simp [__eo_typeof_dt_sel_return, eo_fun_ends_in_bool] at h
      | cons T c =>
          simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
            __eo_to_smt_datatype_cons] using
            ih c d (by
              simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec,
                __eo_to_smt_datatype_cons] using h)

private theorem smtx_dt_sel_return_none_of_datatype :
    ∀ (d : Datatype) (i j : eo_lit_Nat),
      eo_fun_ends_in_bool (__eo_typeof_dt_sel_return d i j) ->
        __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j = SmtType.None := by
  intro d i j
  induction i generalizing d with
  | zero =>
      cases d with
      | null =>
          simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, eo_fun_ends_in_bool]
      | sum c d =>
          intro h
          exact smtx_dt_sel_return_none_of_constructor c d j h
  | succ i ih =>
      cases d with
      | null =>
          simp [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, eo_fun_ends_in_bool]
      | sum c d =>
          intro h
          simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec, __eo_to_smt_datatype] using
            ih d (by
              simpa [__eo_typeof_dt_sel_return, __smtx_ret_typeof_sel_rec] using h)

private theorem smtx_dt_sel_return_none_under_constructor_substitution
    (s : smt_lit_String) (d : SmtDatatype) :
    ∀ (c : SmtDatatypeCons) (d0 : SmtDatatype) (j : smt_lit_Nat),
      __smtx_ret_typeof_sel_rec (SmtDatatype.sum c d0) eo_lit_nat_zero j = SmtType.None ->
        __smtx_ret_typeof_sel_rec
          (SmtDatatype.sum (__smtx_dtc_substitute s d c) (__smtx_dt_substitute s d d0))
          eo_lit_nat_zero j = SmtType.None := by
  intro c d0 j
  induction j generalizing c d0 with
  | zero =>
      cases c with
      | unit =>
          simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec]
      | cons T c =>
          intro h
          cases T <;>
            simp [__smtx_ret_typeof_sel_rec, __smtx_dtc_substitute, smt_lit_ite,
              smt_lit_Teq] at h ⊢
  | succ j ih =>
      intro h
      cases c with
      | unit =>
          simp [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec] at h ⊢
      | cons T c =>
          cases T with
          | Datatype s2 d2 =>
              simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec, smt_lit_ite, smt_lit_streq] using
                ih c d0 (by
                  simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec, smt_lit_ite, smt_lit_streq] using h)
          | _ =>
              simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec, smt_lit_ite, smt_lit_Teq] using
                ih c d0 (by
                  simpa [__smtx_dtc_substitute, __smtx_ret_typeof_sel_rec, smt_lit_ite, smt_lit_Teq] using h)

private theorem smtx_dt_sel_return_none_under_datatype_substitution
    (s : smt_lit_String) (d : SmtDatatype) :
    ∀ (d0 : SmtDatatype) (i j : smt_lit_Nat),
      __smtx_ret_typeof_sel_rec d0 i j = SmtType.None ->
        __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d0) i j = SmtType.None := by
  intro d0 i j
  induction i generalizing d0 with
  | zero =>
      cases d0 with
      | null =>
          simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec]
      | sum c d0 =>
          intro h
          have h' :
              __smtx_ret_typeof_sel_rec (SmtDatatype.sum c d0) eo_lit_nat_zero j =
                SmtType.None := by
            simpa [__smtx_ret_typeof_sel_rec] using h
          exact smtx_dt_sel_return_none_under_constructor_substitution s d c d0 j h'
  | succ i ih =>
      cases d0 with
      | null =>
          simp [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec]
      | sum c d0 =>
          intro h
          simpa [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec] using
            ih d0 (by
              simpa [__smtx_dt_substitute, __smtx_ret_typeof_sel_rec] using h)

theorem smtx_ret_typeof_sel_none_of_eo_dt_sel_return_fun_ends_in_bool
    (s : eo_lit_String) (d : Datatype) (i j : eo_lit_Nat) :
    eo_fun_ends_in_bool (__eo_typeof_dt_sel_return (__eo_dt_substitute s d d) i j) ->
      __smtx_ret_typeof_sel s (__eo_to_smt_datatype d) i j = SmtType.None := by
  intro hFun
  have hOrig : eo_fun_ends_in_bool (__eo_typeof_dt_sel_return d i j) :=
    eo_dt_sel_return_fun_ends_in_bool_of_substituted_datatype s d d i j hFun
  have hDirect :
      __smtx_ret_typeof_sel_rec (__eo_to_smt_datatype d) i j = SmtType.None :=
    smtx_dt_sel_return_none_of_datatype d i j hOrig
  unfold __smtx_ret_typeof_sel
  exact smtx_dt_sel_return_none_under_datatype_substitution
    s (__eo_to_smt_datatype d) (__eo_to_smt_datatype d) i j hDirect

end TranslationProofs
