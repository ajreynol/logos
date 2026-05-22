import Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

private abbrev mkDtCollapseSelectorGuard (s t : Term) : Term :=
  __assoc_nil_nth Term.__eo_List_cons (__dt_arg_list t)
    (__eo_list_find Term.__eo_List_cons
      (__dt_get_selectors_of_app (__eo_typeof t) t) s)

private theorem eo_to_smt_apply_dt_sel
    (s : native_String) (d : Datatype) (i j : native_Nat) (x : Term) :
    __eo_to_smt (Term.Apply (Term.DtSel s d i j) x) =
      SmtTerm.Apply (__eo_to_smt (Term.DtSel s d i j)) (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_apply_dt_cons
    (s : native_String) (d : Datatype) (i : native_Nat) (x : Term) :
    __eo_to_smt (Term.Apply (Term.DtCons s d i) x) =
      SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x) := by
  rfl

private theorem eo_to_smt_apply_apply_dt_cons
    (s : native_String) (d : Datatype) (i : native_Nat) (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply (Term.DtCons s d i) x) y) =
      SmtTerm.Apply
        (SmtTerm.Apply (__eo_to_smt (Term.DtCons s d i)) (__eo_to_smt x))
        (__eo_to_smt y) := by
  rfl

private theorem assoc_nil_nth_nil_stuck (f n : Term) :
    __assoc_nil_nth f Term.__eo_List_nil n = Term.Stuck := by
  cases f <;> cases n <;>
    simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth]

private theorem assoc_nil_nth_index_stuck (f xs : Term) :
    __assoc_nil_nth f xs Term.Stuck = Term.Stuck := by
  cases f <;> cases xs <;>
    simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth]

private theorem assoc_nil_nth_singleton_eq (x n ti : Term) :
    __assoc_nil_nth Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) Term.__eo_List_nil) n = ti ->
    ti ≠ Term.Stuck ->
    ti = x := by
  intro h hti
  cases n <;> try
    simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth, __eo_requires,
      __eo_eq, __eo_add, native_ite, native_teq, native_not,
      SmtEval.native_not] at h
  case Numeral z =>
    by_cases hz : z = 0
    · subst hz
      simp [__assoc_nil_nth, __eo_eq, native_ite, native_teq] at h
      exact h.symm
    · simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth, __eo_requires,
        __eo_eq, __eo_add, native_ite, native_teq, native_not,
        SmtEval.native_not, hz] at h
      exact False.elim (hti h.symm)
  all_goals exact False.elim (hti h.symm)

private def eoTermList : List Term -> Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoTermList xs)

private def appHead : Term -> Term
  | Term.Apply f _ => appHead f
  | t => t

private def appArgs : Term -> List Term
  | Term.Apply f x => appArgs f ++ [x]
  | _ => []

private theorem get_arg_list_rec_eoTermList_appArgs :
    ∀ (t : Term) (xs : List Term),
      appHead t ≠ Term.Stuck ->
      __get_arg_list_rec t (eoTermList xs) = eoTermList (appArgs t ++ xs)
  | Term.Apply f x, xs, hHead => by
      cases xs with
      | nil =>
          have hRec := get_arg_list_rec_eoTermList_appArgs f [x] hHead
          simpa [appArgs, eoTermList, __get_arg_list_rec] using hRec
      | cons y ys =>
          have hRec := get_arg_list_rec_eoTermList_appArgs f (x :: y :: ys) hHead
          simpa [appArgs, eoTermList, __get_arg_list_rec, List.append_assoc] using hRec
  | Term.UOp _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.UOp1 _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.UOp2 _ _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.UOp3 _ _ _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.__eo_List, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.__eo_List_nil, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.__eo_List_cons, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.Bool, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.Boolean _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.Numeral _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.Rational _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.String _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.Binary _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.Type, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.Stuck, xs, hHead => by simp [appHead] at hHead
  | Term.FunType, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.Var _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.DatatypeType _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.DatatypeTypeRef _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.DtcAppType _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.DtCons _ _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.DtSel _ _ _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.USort _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
  | Term.UConst _ _, xs, _ => by cases xs <;> simp [appHead, appArgs, __get_arg_list_rec, eoTermList]
termination_by t xs hHead => t

private theorem assoc_nil_nth_eoTermList_mem :
    ∀ (xs : List Term) (n ti : Term),
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs) n = ti ->
      ti ≠ Term.Stuck ->
      ti ∈ xs
  | [], n, ti, h, hti => by
      simp [eoTermList, assoc_nil_nth_nil_stuck] at h
      exact False.elim (hti h.symm)
  | x :: xs, n, ti, h, hti => by
      cases n <;> try
        simp [eoTermList, __assoc_nil_nth, __eo_l_1___assoc_nil_nth,
          __eo_requires, __eo_eq, __eo_add, native_ite, native_teq,
          native_not, SmtEval.native_not] at h
      case Numeral z =>
        by_cases hz : z = 0
        · subst z
          simp [eoTermList, __assoc_nil_nth, __eo_eq, native_ite,
            native_teq] at h
          simp [h.symm]
        · have hRec :
              __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
                  (__eo_add (Term.Numeral z) (Term.Numeral (-1 : native_Int))) =
                ti := by
            simpa [eoTermList, __assoc_nil_nth, __eo_l_1___assoc_nil_nth,
              __eo_requires, __eo_eq, __eo_add, native_ite, native_teq,
              native_not, SmtEval.native_not, hz] using h
          exact List.mem_cons_of_mem x
            (assoc_nil_nth_eoTermList_mem xs
              (__eo_add (Term.Numeral z) (Term.Numeral (-1 : native_Int)))
              ti hRec hti)
      all_goals
        try rw [assoc_nil_nth_index_stuck] at h
        exact False.elim (hti h.symm)

private theorem assoc_nil_nth_eoTermList_zero_eq (x ti : Term) (xs : List Term) :
    __assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
        (Term.Numeral 0) = ti ->
    ti = x := by
  intro h
  simp [eoTermList, __assoc_nil_nth, __eo_eq, native_ite, native_teq] at h
  exact h.symm

private theorem eo_list_find_cons_self_zero_of_ne_stuck (x xs : Term) :
    x ≠ Term.Stuck ->
    __eo_list_find Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) x ≠ Term.Stuck ->
    __eo_list_find Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) x =
      Term.Numeral 0 := by
  intro hx hFind
  let list := Term.Apply (Term.Apply Term.__eo_List_cons x) xs
  have hRec :
      __eo_list_find_rec list x (Term.Numeral 0) = Term.Numeral 0 := by
    cases x <;> simp [list, __eo_list_find_rec, __eo_eq, native_ite,
      native_teq] at hx ⊢
  have hReq :
      __eo_requires (__eo_is_list Term.__eo_List_cons list)
          (Term.Boolean true) (Term.Numeral 0) ≠ Term.Stuck := by
    simpa [__eo_list_find, __eo_list_find_rec, list, __eo_eq, native_ite,
      native_teq, hRec] using hFind
  have hRes := eo_requires_eq_result_of_ne_stuck
    (__eo_is_list Term.__eo_List_cons list) (Term.Boolean true)
    (Term.Numeral 0) hReq
  simpa [__eo_list_find, __eo_list_find_rec, list, __eo_eq, native_ite,
    native_teq, hRec] using hRes

private theorem assoc_nil_nth_pair_zero_eq (x y ti : Term) :
    __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
        (Term.Numeral 0) = ti ->
    ti = x := by
  intro h
  simp [eoTermList, __assoc_nil_nth, __eo_eq, native_ite,
    native_teq] at h
  exact h.symm

private theorem assoc_nil_nth_pair_one_eq (x y ti : Term) :
    __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
        (Term.Numeral 1) = ti ->
    ti = y := by
  intro h
  simp [eoTermList, __assoc_nil_nth, __eo_l_1___assoc_nil_nth,
    __eo_requires, __eo_eq, __eo_add, native_ite, native_teq,
    native_zplus, native_not, SmtEval.native_not] at h
  exact h.symm

private theorem assoc_nil_nth_pair_neg_one_stuck (x y : Term) :
    __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
        (Term.Numeral (-1 : native_Int)) = Term.Stuck := by
  simp [eoTermList, __assoc_nil_nth, __eo_l_1___assoc_nil_nth,
    __eo_requires, __eo_eq, __eo_add, native_ite, native_teq,
    native_zplus, native_not, SmtEval.native_not,
    assoc_nil_nth_nil_stuck]

private theorem eo_list_find_rec_cons_self_eq (x xs n : Term) :
    x ≠ Term.Stuck ->
    n ≠ Term.Stuck ->
    __eo_list_find_rec
        (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) x n = n := by
  intro hx hn
  cases x <;> cases n <;>
    simp [__eo_list_find_rec, __eo_eq, native_ite, native_teq] at hx hn ⊢

private theorem datatype_cons_selectors_rec_find_sel0_pair_eq_zero_of_assoc_ne_stuck
    (s : native_String) (d : Datatype) (i : native_Nat) :
    ∀ (rest : Datatype) (ci : native_Nat) (x y ti : Term),
      __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
        (__eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i rest ci native_nat_zero)
          (Term.DtSel s d i native_nat_zero)) = ti ->
      ti ≠ Term.Stuck ->
      __eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i rest ci native_nat_zero)
          (Term.DtSel s d i native_nat_zero) =
        Term.Numeral 0
  | Datatype.null, ci, x, y, ti, hAssoc, hTi => by
      have hFind :
          __eo_list_find Term.__eo_List_cons
              (__eo_datatype_cons_selectors_rec s d i Datatype.null ci
                native_nat_zero)
              (Term.DtSel s d i native_nat_zero) = Term.Stuck := by
        cases ci <;>
          simp [__eo_datatype_cons_selectors_rec, __eo_list_find,
            __eo_is_list, __eo_requires, native_ite, native_teq,
            SmtEval.native_not]
      rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
      exact False.elim (hTi hAssoc.symm)
  | Datatype.sum DatatypeCons.unit restTail, Nat.zero, x, y, ti, hAssoc, hTi => by
      have hFind :
          __eo_list_find Term.__eo_List_cons
              (__eo_datatype_cons_selectors_rec s d i
                (Datatype.sum DatatypeCons.unit restTail) Nat.zero
                native_nat_zero)
              (Term.DtSel s d i native_nat_zero) =
            Term.Numeral (-1 : native_Int) := by
        simp [__eo_datatype_cons_selectors_rec, __eo_list_find,
          __eo_list_find_rec, __eo_is_list, __eo_get_nil_rec,
          __eo_is_list_nil, __eo_requires, __eo_is_ok, native_ite,
          native_teq, SmtEval.native_not]
      rw [hFind] at hAssoc
      simp [eoTermList, __assoc_nil_nth, __eo_l_1___assoc_nil_nth,
        __eo_requires, __eo_eq, __eo_add, native_ite, native_teq,
        native_zplus, native_not, SmtEval.native_not,
        assoc_nil_nth_nil_stuck] at hAssoc
      exact False.elim (hTi hAssoc.symm)
  | Datatype.sum (DatatypeCons.cons U c) restTail, Nat.zero, x, y, ti,
      hAssoc, hTi => by
      let tail :=
        __eo_datatype_cons_selectors_rec s d i restTail Nat.zero
          (native_nat_succ native_nat_zero)
      have hFindNe :
          __eo_list_find Term.__eo_List_cons
              (__eo_datatype_cons_selectors_rec s d i
                (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero
                native_nat_zero)
              (Term.DtSel s d i native_nat_zero) ≠ Term.Stuck := by
        intro hFind
        rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
        exact hTi hAssoc.symm
      by_cases hTail : tail = Term.Stuck
      · have hFind :
            __eo_list_find Term.__eo_List_cons
                (__eo_datatype_cons_selectors_rec s d i
                  (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero
                  native_nat_zero)
                (Term.DtSel s d i native_nat_zero) = Term.Stuck := by
          simp [tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply,
            hTail, __eo_list_find, __eo_is_list, __eo_requires,
            native_ite, native_teq, SmtEval.native_not]
        exact False.elim (hFindNe hFind)
      · have hRec :
            __eo_datatype_cons_selectors_rec s d i
                (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero
                native_nat_zero =
              Term.Apply
                (Term.Apply Term.__eo_List_cons
                  (Term.DtSel s d i native_nat_zero)) tail := by
          simp [tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply,
            hTail]
        have hFindNe' :
            __eo_list_find Term.__eo_List_cons
                (Term.Apply
                  (Term.Apply Term.__eo_List_cons
                    (Term.DtSel s d i native_nat_zero)) tail)
                (Term.DtSel s d i native_nat_zero) ≠ Term.Stuck := by
          simpa [hRec] using hFindNe
        have hSelNe :
            Term.DtSel s d i native_nat_zero ≠ Term.Stuck := by
          intro h
          cases h
        simpa [hRec] using
          eo_list_find_cons_self_zero_of_ne_stuck
            (Term.DtSel s d i native_nat_zero) tail hSelNe hFindNe'
  | Datatype.sum c restTail, Nat.succ ci, x, y, ti, hAssoc, hTi => by
      have hAssoc' :
          __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
              (__eo_list_find Term.__eo_List_cons
                (__eo_datatype_cons_selectors_rec s d i restTail ci
                  native_nat_zero)
                (Term.DtSel s d i native_nat_zero)) =
            ti := by
        simpa [__eo_datatype_cons_selectors_rec] using hAssoc
      simpa [__eo_datatype_cons_selectors_rec] using
        datatype_cons_selectors_rec_find_sel0_pair_eq_zero_of_assoc_ne_stuck
          s d i restTail ci x y ti hAssoc' hTi

private theorem datatype_cons_selectors_rec_find_rec_self_pair_eq_index_of_assoc_ne_stuck
    (s : native_String) (d : Datatype) (i : native_Nat) :
    ∀ (rest : Datatype) (ci ai start : native_Nat) (x y ti : Term),
      __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
        (__eo_list_find_rec
          (__eo_datatype_cons_selectors_rec s d i rest ci ai)
          (Term.DtSel s d i ai) (Term.Numeral start)) = ti ->
      ti ≠ Term.Stuck ->
      __eo_list_find_rec
          (__eo_datatype_cons_selectors_rec s d i rest ci ai)
          (Term.DtSel s d i ai) (Term.Numeral start) =
        Term.Numeral start
  | Datatype.null, ci, ai, start, x, y, ti, hAssoc, hTi => by
      have hFind :
          __eo_list_find_rec
              (__eo_datatype_cons_selectors_rec s d i Datatype.null ci ai)
              (Term.DtSel s d i ai) (Term.Numeral start) = Term.Stuck := by
        cases ci <;>
          simp [__eo_datatype_cons_selectors_rec, __eo_list_find_rec]
      rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
      exact False.elim (hTi hAssoc.symm)
  | Datatype.sum DatatypeCons.unit restTail, Nat.zero, ai, start, x, y, ti,
      hAssoc, hTi => by
      have hFind :
          __eo_list_find_rec
              (__eo_datatype_cons_selectors_rec s d i
                (Datatype.sum DatatypeCons.unit restTail) Nat.zero ai)
              (Term.DtSel s d i ai) (Term.Numeral start) =
            Term.Numeral (-1 : native_Int) := by
        simp [__eo_datatype_cons_selectors_rec, __eo_list_find_rec]
      rw [hFind] at hAssoc
      rw [assoc_nil_nth_pair_neg_one_stuck] at hAssoc
      exact False.elim (hTi hAssoc.symm)
  | Datatype.sum (DatatypeCons.cons U c) restTail, Nat.zero, ai, start, x, y,
      ti, hAssoc, hTi => by
      let tail :=
        __eo_datatype_cons_selectors_rec s d i restTail Nat.zero
          (native_nat_succ ai)
      by_cases hTail : tail = Term.Stuck
      · have hFind :
            __eo_list_find_rec
                (__eo_datatype_cons_selectors_rec s d i
                  (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero ai)
                (Term.DtSel s d i ai) (Term.Numeral start) = Term.Stuck := by
          simp [tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply,
            hTail, __eo_list_find_rec]
        rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
        exact False.elim (hTi hAssoc.symm)
      · have hRec :
            __eo_datatype_cons_selectors_rec s d i
                (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero ai =
              Term.Apply (Term.Apply Term.__eo_List_cons
                (Term.DtSel s d i ai)) tail := by
          simp [tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply,
            hTail]
        have hSelNe : Term.DtSel s d i ai ≠ Term.Stuck := by
          intro h
          cases h
        have hStartNe : Term.Numeral start ≠ Term.Stuck := by
          intro h
          cases h
        simpa [hRec] using
          eo_list_find_rec_cons_self_eq (Term.DtSel s d i ai) tail
            (Term.Numeral start) hSelNe hStartNe
  | Datatype.sum c restTail, Nat.succ ci, ai, start, x, y, ti, hAssoc,
      hTi => by
      have hAssoc' :
          __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
            (__eo_list_find_rec
              (__eo_datatype_cons_selectors_rec s d i restTail ci ai)
              (Term.DtSel s d i ai) (Term.Numeral start)) = ti := by
        simpa [__eo_datatype_cons_selectors_rec] using hAssoc
      simpa [__eo_datatype_cons_selectors_rec] using
        datatype_cons_selectors_rec_find_rec_self_pair_eq_index_of_assoc_ne_stuck
          s d i restTail ci ai start x y ti hAssoc' hTi

private theorem datatype_cons_selectors_rec_find_sel1_pair_eq_one_of_assoc_ne_stuck
    (s : native_String) (d : Datatype) (i : native_Nat) :
    ∀ (rest : Datatype) (ci : native_Nat) (x y ti : Term),
      __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
        (__eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i rest ci native_nat_zero)
          (Term.DtSel s d i (native_nat_succ native_nat_zero))) = ti ->
      ti ≠ Term.Stuck ->
      __eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i rest ci native_nat_zero)
          (Term.DtSel s d i (native_nat_succ native_nat_zero)) =
        Term.Numeral 1
  | Datatype.null, ci, x, y, ti, hAssoc, hTi => by
      have hFind :
          __eo_list_find Term.__eo_List_cons
              (__eo_datatype_cons_selectors_rec s d i Datatype.null ci
                native_nat_zero)
              (Term.DtSel s d i (native_nat_succ native_nat_zero)) =
            Term.Stuck := by
        cases ci <;>
          simp [__eo_datatype_cons_selectors_rec, __eo_list_find,
            __eo_is_list, __eo_requires, native_ite, native_teq,
            SmtEval.native_not]
      rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
      exact False.elim (hTi hAssoc.symm)
  | Datatype.sum DatatypeCons.unit restTail, Nat.zero, x, y, ti, hAssoc,
      hTi => by
      have hFind :
          __eo_list_find Term.__eo_List_cons
              (__eo_datatype_cons_selectors_rec s d i
                (Datatype.sum DatatypeCons.unit restTail) Nat.zero
                native_nat_zero)
              (Term.DtSel s d i (native_nat_succ native_nat_zero)) =
            Term.Numeral (-1 : native_Int) := by
        simp [__eo_datatype_cons_selectors_rec, __eo_list_find,
          __eo_list_find_rec, __eo_is_list, __eo_get_nil_rec,
          __eo_is_list_nil, __eo_requires, __eo_is_ok, native_ite,
          native_teq, SmtEval.native_not]
      rw [hFind] at hAssoc
      rw [assoc_nil_nth_pair_neg_one_stuck] at hAssoc
      exact False.elim (hTi hAssoc.symm)
  | Datatype.sum (DatatypeCons.cons U c) restTail, Nat.zero, x, y, ti,
      hAssoc, hTi => by
      let target := Term.DtSel s d i (native_nat_succ native_nat_zero)
      let tail :=
        __eo_datatype_cons_selectors_rec s d i restTail Nat.zero
          (native_nat_succ native_nat_zero)
      let list :=
        Term.Apply
          (Term.Apply Term.__eo_List_cons (Term.DtSel s d i native_nat_zero))
          tail
      have hFindNe :
          __eo_list_find Term.__eo_List_cons
              (__eo_datatype_cons_selectors_rec s d i
                (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero
                native_nat_zero)
              target ≠ Term.Stuck := by
        intro hFind
        rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
        exact hTi hAssoc.symm
      by_cases hTail : tail = Term.Stuck
      · have hFind :
            __eo_list_find Term.__eo_List_cons
                (__eo_datatype_cons_selectors_rec s d i
                  (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero
                  native_nat_zero)
                target = Term.Stuck := by
          simp [target, tail, __eo_datatype_cons_selectors_rec,
            __eo_mk_apply, hTail, __eo_list_find, __eo_is_list,
            __eo_requires, native_ite, native_teq, SmtEval.native_not]
        exact False.elim (hFindNe hFind)
      · have hRec :
            __eo_datatype_cons_selectors_rec s d i
                (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero
                native_nat_zero = list := by
          simp [list, tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply,
            hTail]
        have hRecFind :
            __eo_list_find_rec list target (Term.Numeral 0) =
              __eo_list_find_rec tail target (Term.Numeral 1) := by
          simp [list, target, __eo_list_find_rec, __eo_eq, __eo_add,
            native_ite, native_teq, native_zplus]
        have hReqNe :
            __eo_requires (__eo_is_list Term.__eo_List_cons list)
                (Term.Boolean true)
                (__eo_list_find_rec tail target (Term.Numeral 1)) ≠
              Term.Stuck := by
          simpa [hRec, __eo_list_find, hRecFind] using hFindNe
        have hReqEq :=
          eo_requires_eq_result_of_ne_stuck
            (__eo_is_list Term.__eo_List_cons list) (Term.Boolean true)
            (__eo_list_find_rec tail target (Term.Numeral 1)) hReqNe
        have hFindEq :
            __eo_list_find Term.__eo_List_cons
                (__eo_datatype_cons_selectors_rec s d i
                  (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero
                  native_nat_zero)
                target =
              __eo_list_find_rec tail target (Term.Numeral 1) := by
          simpa [hRec, __eo_list_find, hRecFind] using hReqEq
        have hAssocTail :
            __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
                (__eo_list_find_rec tail target (Term.Numeral 1)) = ti := by
          rw [hFindEq] at hAssoc
          simpa [target] using hAssoc
        have hTailFind :
            __eo_list_find_rec tail target (Term.Numeral 1) =
              Term.Numeral 1 := by
          simpa [target, tail] using
            datatype_cons_selectors_rec_find_rec_self_pair_eq_index_of_assoc_ne_stuck
              s d i restTail Nat.zero (native_nat_succ native_nat_zero)
              (native_nat_succ native_nat_zero) x y ti hAssocTail hTi
        exact hFindEq.trans hTailFind
  | Datatype.sum c restTail, Nat.succ ci, x, y, ti, hAssoc, hTi => by
      have hAssoc' :
          __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
              (__eo_list_find Term.__eo_List_cons
                (__eo_datatype_cons_selectors_rec s d i restTail ci
                  native_nat_zero)
                (Term.DtSel s d i (native_nat_succ native_nat_zero))) =
            ti := by
        simpa [__eo_datatype_cons_selectors_rec] using hAssoc
      simpa [__eo_datatype_cons_selectors_rec] using
        datatype_cons_selectors_rec_find_sel1_pair_eq_one_of_assoc_ne_stuck
          s d i restTail ci x y ti hAssoc' hTi

private theorem model_eval_apply_dtcons_of_arg_ne_notvalue
    (M : SmtModel) (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (v : SmtValue) :
    v ≠ SmtValue.NotValue ->
    __smtx_model_eval_apply M (SmtValue.DtCons s d i) v =
      SmtValue.Apply (SmtValue.DtCons s d i) v := by
  intro hv
  cases v <;> simp [__smtx_model_eval_apply] at hv ⊢

private theorem model_eval_apply_smt_apply_of_arg_ne_notvalue
    (M : SmtModel) (f v a : SmtValue) :
    a ≠ SmtValue.NotValue ->
    __smtx_model_eval_apply M (SmtValue.Apply f v) a =
      SmtValue.Apply (SmtValue.Apply f v) a := by
  intro ha
  cases a <;> simp [__smtx_model_eval_apply] at ha ⊢

private theorem one_arg_count_of_apply_dtcons_datatype
    {v : SmtValue} {s : native_String} {d : SmtDatatype} {i : native_Nat}
    (hTy : __smtx_typeof_value (SmtValue.Apply (SmtValue.DtCons s d i) v) =
      SmtType.Datatype s d) :
    __smtx_dt_num_sels d i = 1 := by
  have hCountSub :
      vsm_num_apply_args (SmtValue.Apply (SmtValue.DtCons s d i) v) =
        __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
    exact vsm_num_apply_args_eq_dt_num_sels_of_datatype
      (v := SmtValue.Apply (SmtValue.DtCons s d i) v)
      (by simp [__vsm_apply_head]) hTy
  have hCount :
      vsm_num_apply_args (SmtValue.Apply (SmtValue.DtCons s d i) v) =
        __smtx_dt_num_sels d i := by
    rw [dt_num_sels_substitute s d d i] at hCountSub
    exact hCountSub
  simpa [vsm_num_apply_args] using hCount.symm

private theorem two_arg_count_of_apply_dtcons_datatype
    {v1 v2 : SmtValue} {s : native_String} {d : SmtDatatype}
    {i : native_Nat}
    (hTy :
      __smtx_typeof_value
          (SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s d i) v1) v2) =
        SmtType.Datatype s d) :
    __smtx_dt_num_sels d i = 2 := by
  have hCountSub :
      vsm_num_apply_args
          (SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s d i) v1) v2) =
        __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
    exact vsm_num_apply_args_eq_dt_num_sels_of_datatype
      (v := SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s d i) v1) v2)
      (by simp [__vsm_apply_head]) hTy
  have hCount :
      vsm_num_apply_args
          (SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s d i) v1) v2) =
        __smtx_dt_num_sels d i := by
    rw [dt_num_sels_substitute s d d i] at hCountSub
    exact hCountSub
  simpa [vsm_num_apply_args] using hCount.symm

private theorem dt_sel_cons_one_eval_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i : native_Nat) (x : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) x) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hBool
  let D := __eo_to_smt_datatype d
  let X := __eo_to_smt x
  let vx := __smtx_model_eval M X
  have hTypes := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x)) x hBool
  have hLeftNN :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) ≠
        SmtType.None := hTypes.2
  cases hReserved : TranslationProofs.__eo_reserved_datatype_name s
  · have hLeftTranslate :
        __eo_to_smt
            (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x)) =
          SmtTerm.Apply (SmtTerm.DtSel s D i 0)
            (SmtTerm.Apply (SmtTerm.DtCons s D i) X) := by
      simp [eo_to_smt_apply_dt_sel, eo_to_smt_apply_dt_cons,
        TranslationProofs.eo_to_smt_term_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_cons, D, X, native_ite, hReserved]
    have hApplyNN :
        term_has_non_none_type
          (SmtTerm.Apply (SmtTerm.DtSel s D i 0)
            (SmtTerm.Apply (SmtTerm.DtCons s D i) X)) := by
      unfold term_has_non_none_type
      rw [← hLeftTranslate]
      exact hLeftNN
    have hArgTy :
        __smtx_typeof (SmtTerm.Apply (SmtTerm.DtCons s D i) X) =
          SmtType.Datatype s D :=
      dt_sel_arg_datatype_of_non_none hApplyNN
    have hXNN : __smtx_typeof X ≠ SmtType.None := by
      have hConsNN :
          __smtx_typeof (SmtTerm.Apply (SmtTerm.DtCons s D i) X) ≠
            SmtType.None := by
        rw [hArgTy]
        simp
      have hApplyNN' :
          __smtx_typeof_apply (__smtx_typeof (SmtTerm.DtCons s D i))
              (__smtx_typeof X) ≠
            SmtType.None := by
        simpa [__smtx_typeof] using hConsNN
      rcases typeof_apply_non_none_cases hApplyNN' with
        ⟨_A, _B, _hF, hX, hA, _hB⟩
      rw [hX]
      exact hA
    have hPresX : __smtx_typeof_value vx = __smtx_typeof X :=
      smt_model_eval_preserves_type_of_non_none M hM X hXNN
    have hvxNN : vx ≠ SmtValue.NotValue := by
      intro hv
      have hNone : __smtx_typeof_value vx = SmtType.None := by
        simp [hv, __smtx_typeof_value]
      rw [hPresX] at hNone
      exact hXNN hNone
    have hEvalCons :
        __smtx_model_eval M (SmtTerm.Apply (SmtTerm.DtCons s D i) X) =
          SmtValue.Apply (SmtValue.DtCons s D i) vx := by
      simp [__smtx_model_eval, vx]
      exact model_eval_apply_dtcons_of_arg_ne_notvalue M s D i vx hvxNN
    have hConsValTy :
        __smtx_typeof_value (SmtValue.Apply (SmtValue.DtCons s D i) vx) =
          SmtType.Datatype s D := by
      rw [← hEvalCons]
      have hPres := smt_model_eval_preserves_type_of_non_none M hM
        (SmtTerm.Apply (SmtTerm.DtCons s D i) X) (by
          unfold term_has_non_none_type
          rw [hArgTy]
          simp)
      rw [hPres, hArgTy]
    have hNum : __smtx_dt_num_sels D i = 1 :=
      one_arg_count_of_apply_dtcons_datatype hConsValTy
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hLeftTranslate]
    simp [__smtx_model_eval, hEvalCons]
    unfold __smtx_model_eval_dt_sel
    have hHeadTrue :
        native_veq (__vsm_apply_head (SmtValue.Apply (SmtValue.DtCons s D i) vx))
            (SmtValue.DtCons s D i) = true := by
      simp [__vsm_apply_head, native_veq]
    simp [native_ite, hHeadTrue, hNum, __vsm_apply_arg_nth, native_nateq]
    simpa [vx] using RuleProofs.smt_value_rel_refl vx
  · exfalso
    apply hLeftNN
    have hTranslateNone :
        __eo_to_smt
            (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x)) =
          SmtTerm.Apply SmtTerm.None (SmtTerm.Apply SmtTerm.None (__eo_to_smt x)) := by
      simp [eo_to_smt_apply_dt_sel, eo_to_smt_apply_dt_cons,
        TranslationProofs.eo_to_smt_term_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_cons, native_ite, hReserved]
    rw [hTranslateNone]
    exact TranslationProofs.typeof_apply_none_eq
      (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))

private theorem dt_sel_cons_two_zero_eval_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i : native_Nat)
    (x y : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 0)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) x) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.DtSel s d i 0)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hBool
  let D := __eo_to_smt_datatype d
  let X := __eo_to_smt x
  let Y := __eo_to_smt y
  let vx := __smtx_model_eval M X
  let vy := __smtx_model_eval M Y
  let cons1 := SmtTerm.Apply (SmtTerm.DtCons s D i) X
  let cons2 := SmtTerm.Apply cons1 Y
  have hTypes := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    (Term.Apply (Term.DtSel s d i 0)
      (Term.Apply (Term.Apply (Term.DtCons s d i) x) y)) x hBool
  have hLeftNN :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.DtSel s d i 0)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) ≠
        SmtType.None := hTypes.2
  cases hReserved : TranslationProofs.__eo_reserved_datatype_name s
  · have hLeftTranslate :
        __eo_to_smt
            (Term.Apply (Term.DtSel s d i 0)
              (Term.Apply (Term.Apply (Term.DtCons s d i) x) y)) =
      SmtTerm.Apply (SmtTerm.DtSel s D i 0) cons2 := by
      simp [eo_to_smt_apply_dt_sel, eo_to_smt_apply_dt_cons,
        eo_to_smt_apply_apply_dt_cons,
        TranslationProofs.eo_to_smt_term_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_cons, D, X, Y, cons1, cons2,
        native_ite, hReserved]
    have hApplyNN :
        term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s D i 0) cons2) := by
      unfold term_has_non_none_type
      rw [← hLeftTranslate]
      exact hLeftNN
    have hArgTy : __smtx_typeof cons2 = SmtType.Datatype s D :=
      dt_sel_arg_datatype_of_non_none hApplyNN
    have hCons2NN : __smtx_typeof cons2 ≠ SmtType.None := by
      rw [hArgTy]
      simp
    have hOuterApplyNN :
        __smtx_typeof_apply (__smtx_typeof cons1) (__smtx_typeof Y) ≠
          SmtType.None := by
      simpa [cons2, __smtx_typeof] using hCons2NN
    rcases typeof_apply_non_none_cases hOuterApplyNN with
      ⟨A2, B2, hF2, hY, hA2, _hB2⟩
    have hYNN : __smtx_typeof Y ≠ SmtType.None := by
      rw [hY]
      exact hA2
    have hCons1NN : __smtx_typeof cons1 ≠ SmtType.None := by
      rcases hF2 with hF2 | hF2
      · rw [hF2]
        simp
      · rw [hF2]
        simp
    have hInnerApplyNN :
        __smtx_typeof_apply (__smtx_typeof (SmtTerm.DtCons s D i))
            (__smtx_typeof X) ≠
          SmtType.None := by
      simpa [cons1, __smtx_typeof] using hCons1NN
    rcases typeof_apply_non_none_cases hInnerApplyNN with
      ⟨A1, B1, hF1, hX, hA1, _hB1⟩
    have hXNN : __smtx_typeof X ≠ SmtType.None := by
      rw [hX]
      exact hA1
    have hPresX : __smtx_typeof_value vx = __smtx_typeof X :=
      smt_model_eval_preserves_type_of_non_none M hM X hXNN
    have hPresY : __smtx_typeof_value vy = __smtx_typeof Y :=
      smt_model_eval_preserves_type_of_non_none M hM Y hYNN
    have hvxNN : vx ≠ SmtValue.NotValue := by
      intro hv
      have hNone : __smtx_typeof_value vx = SmtType.None := by
        simp [hv, __smtx_typeof_value]
      rw [hPresX] at hNone
      exact hXNN hNone
    have hvyNN : vy ≠ SmtValue.NotValue := by
      intro hv
      have hNone : __smtx_typeof_value vy = SmtType.None := by
        simp [hv, __smtx_typeof_value]
      rw [hPresY] at hNone
      exact hYNN hNone
    have hEvalCons1 :
        __smtx_model_eval M cons1 =
          SmtValue.Apply (SmtValue.DtCons s D i) vx := by
      simp [cons1, __smtx_model_eval, vx]
      exact model_eval_apply_dtcons_of_arg_ne_notvalue M s D i vx hvxNN
    have hEvalCons2 :
        __smtx_model_eval M cons2 =
          SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s D i) vx) vy := by
      simp [cons2, __smtx_model_eval, hEvalCons1, vy]
      exact model_eval_apply_smt_apply_of_arg_ne_notvalue M
        (SmtValue.DtCons s D i) vx vy hvyNN
    have hConsValTy :
        __smtx_typeof_value
            (SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s D i) vx) vy) =
          SmtType.Datatype s D := by
      rw [← hEvalCons2]
      have hPres := smt_model_eval_preserves_type_of_non_none M hM cons2 (by
        unfold term_has_non_none_type
        rw [hArgTy]
        simp)
      rw [hPres, hArgTy]
    have hNum : __smtx_dt_num_sels D i = 2 :=
      two_arg_count_of_apply_dtcons_datatype hConsValTy
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hLeftTranslate]
    simp [__smtx_model_eval, hEvalCons2]
    unfold __smtx_model_eval_dt_sel
    have hHeadTrue :
        native_veq
            (__vsm_apply_head
              (SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s D i) vx) vy))
            (SmtValue.DtCons s D i) = true := by
      simp [__vsm_apply_head, native_veq]
    simp [native_ite, hHeadTrue, hNum, __vsm_apply_arg_nth, native_nateq]
    simpa [vx] using RuleProofs.smt_value_rel_refl vx
  · exfalso
    apply hLeftNN
    have hTranslateNone :
        __eo_to_smt
            (Term.Apply (Term.DtSel s d i 0)
              (Term.Apply (Term.Apply (Term.DtCons s d i) x) y)) =
          SmtTerm.Apply SmtTerm.None
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
              (__eo_to_smt y)) := by
      simp [eo_to_smt_apply_dt_sel, eo_to_smt_apply_dt_cons,
        eo_to_smt_apply_apply_dt_cons,
        TranslationProofs.eo_to_smt_term_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_cons, native_ite, hReserved]
    rw [hTranslateNone]
    exact TranslationProofs.typeof_apply_none_eq
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
        (__eo_to_smt y))

private theorem dt_sel_cons_two_one_eval_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i : native_Nat)
    (x y : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 1)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) y) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.DtSel s d i 1)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hBool
  let D := __eo_to_smt_datatype d
  let X := __eo_to_smt x
  let Y := __eo_to_smt y
  let vx := __smtx_model_eval M X
  let vy := __smtx_model_eval M Y
  let cons1 := SmtTerm.Apply (SmtTerm.DtCons s D i) X
  let cons2 := SmtTerm.Apply cons1 Y
  have hTypes := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    (Term.Apply (Term.DtSel s d i 1)
      (Term.Apply (Term.Apply (Term.DtCons s d i) x) y)) y hBool
  have hLeftNN :
      __smtx_typeof (__eo_to_smt
        (Term.Apply (Term.DtSel s d i 1)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) ≠
        SmtType.None := hTypes.2
  cases hReserved : TranslationProofs.__eo_reserved_datatype_name s
  · have hLeftTranslate :
        __eo_to_smt
            (Term.Apply (Term.DtSel s d i 1)
              (Term.Apply (Term.Apply (Term.DtCons s d i) x) y)) =
          SmtTerm.Apply (SmtTerm.DtSel s D i 1) cons2 := by
      simp [eo_to_smt_apply_dt_sel, eo_to_smt_apply_dt_cons,
        eo_to_smt_apply_apply_dt_cons,
        TranslationProofs.eo_to_smt_term_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_cons, D, X, Y, cons1, cons2,
        native_ite, hReserved]
    have hApplyNN :
        term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s D i 1) cons2) := by
      unfold term_has_non_none_type
      rw [← hLeftTranslate]
      exact hLeftNN
    have hArgTy : __smtx_typeof cons2 = SmtType.Datatype s D :=
      dt_sel_arg_datatype_of_non_none hApplyNN
    have hCons2NN : __smtx_typeof cons2 ≠ SmtType.None := by
      rw [hArgTy]
      simp
    have hOuterApplyNN :
        __smtx_typeof_apply (__smtx_typeof cons1) (__smtx_typeof Y) ≠
          SmtType.None := by
      simpa [cons2, __smtx_typeof] using hCons2NN
    rcases typeof_apply_non_none_cases hOuterApplyNN with
      ⟨A2, B2, hF2, hY, hA2, _hB2⟩
    have hYNN : __smtx_typeof Y ≠ SmtType.None := by
      rw [hY]
      exact hA2
    have hCons1NN : __smtx_typeof cons1 ≠ SmtType.None := by
      rcases hF2 with hF2 | hF2
      · rw [hF2]
        simp
      · rw [hF2]
        simp
    have hInnerApplyNN :
        __smtx_typeof_apply (__smtx_typeof (SmtTerm.DtCons s D i))
            (__smtx_typeof X) ≠
          SmtType.None := by
      simpa [cons1, __smtx_typeof] using hCons1NN
    rcases typeof_apply_non_none_cases hInnerApplyNN with
      ⟨A1, B1, hF1, hX, hA1, _hB1⟩
    have hXNN : __smtx_typeof X ≠ SmtType.None := by
      rw [hX]
      exact hA1
    have hPresX : __smtx_typeof_value vx = __smtx_typeof X :=
      smt_model_eval_preserves_type_of_non_none M hM X hXNN
    have hPresY : __smtx_typeof_value vy = __smtx_typeof Y :=
      smt_model_eval_preserves_type_of_non_none M hM Y hYNN
    have hvxNN : vx ≠ SmtValue.NotValue := by
      intro hv
      have hNone : __smtx_typeof_value vx = SmtType.None := by
        simp [hv, __smtx_typeof_value]
      rw [hPresX] at hNone
      exact hXNN hNone
    have hvyNN : vy ≠ SmtValue.NotValue := by
      intro hv
      have hNone : __smtx_typeof_value vy = SmtType.None := by
        simp [hv, __smtx_typeof_value]
      rw [hPresY] at hNone
      exact hYNN hNone
    have hEvalCons1 :
        __smtx_model_eval M cons1 =
          SmtValue.Apply (SmtValue.DtCons s D i) vx := by
      simp [cons1, __smtx_model_eval, vx]
      exact model_eval_apply_dtcons_of_arg_ne_notvalue M s D i vx hvxNN
    have hEvalCons2 :
        __smtx_model_eval M cons2 =
          SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s D i) vx) vy := by
      simp [cons2, __smtx_model_eval, hEvalCons1, vy]
      exact model_eval_apply_smt_apply_of_arg_ne_notvalue M
        (SmtValue.DtCons s D i) vx vy hvyNN
    have hConsValTy :
        __smtx_typeof_value
            (SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s D i) vx) vy) =
          SmtType.Datatype s D := by
      rw [← hEvalCons2]
      have hPres := smt_model_eval_preserves_type_of_non_none M hM cons2 (by
        unfold term_has_non_none_type
        rw [hArgTy]
        simp)
      rw [hPres, hArgTy]
    have hNum : __smtx_dt_num_sels D i = 2 :=
      two_arg_count_of_apply_dtcons_datatype hConsValTy
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hLeftTranslate]
    simp [__smtx_model_eval, hEvalCons2]
    unfold __smtx_model_eval_dt_sel
    have hHeadTrue :
        native_veq
            (__vsm_apply_head
              (SmtValue.Apply (SmtValue.Apply (SmtValue.DtCons s D i) vx) vy))
            (SmtValue.DtCons s D i) = true := by
      simp [__vsm_apply_head, native_veq]
    simp [native_ite, hHeadTrue, hNum, __vsm_apply_arg_nth, native_nateq]
    simpa [vy] using RuleProofs.smt_value_rel_refl vy
  · exfalso
    apply hLeftNN
    have hTranslateNone :
        __eo_to_smt
            (Term.Apply (Term.DtSel s d i 1)
              (Term.Apply (Term.Apply (Term.DtCons s d i) x) y)) =
          SmtTerm.Apply SmtTerm.None
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
              (__eo_to_smt y)) := by
      simp [eo_to_smt_apply_dt_sel, eo_to_smt_apply_dt_cons,
        eo_to_smt_apply_apply_dt_cons,
        TranslationProofs.eo_to_smt_term_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_cons, native_ite, hReserved]
    rw [hTranslateNone]
    exact TranslationProofs.typeof_apply_none_eq
      (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt x))
        (__eo_to_smt y))

private theorem dt_collapse_selector_direct_one_sound
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i : native_Nat) (x ti : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) ti) ->
    mkDtCollapseSelectorGuard (Term.DtSel s d i 0)
      (Term.Apply (Term.DtCons s d i) x) = ti ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) ti)
      true := by
  intro hBool hGuard
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))
      ti hBool
  have hTiTrans : RuleProofs.eo_has_smt_translation ti := by
    unfold RuleProofs.eo_has_smt_translation
    rw [← hTypes.1]
    exact hTypes.2
  have hTiNe : ti ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ti hTiTrans
  have hAssoc :
      __assoc_nil_nth Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) Term.__eo_List_nil)
        (__eo_list_find Term.__eo_List_cons
          (__dt_get_selectors_of_app (__eo_typeof (Term.Apply (Term.DtCons s d i) x))
            (Term.Apply (Term.DtCons s d i) x)) (Term.DtSel s d i 0)) = ti := by
    simpa [mkDtCollapseSelectorGuard, __dt_arg_list, __get_arg_list_rec] using
      hGuard
  have hTiEq : ti = x :=
    assoc_nil_nth_singleton_eq x _ ti hAssoc hTiNe
  have hBoolX :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.DtSel s d i 0) (Term.Apply (Term.DtCons s d i) x))) x) := by
    simpa [hTiEq] using hBool
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · rw [hTiEq]
    exact dt_sel_cons_one_eval_rel M hM s d i x hBoolX

private theorem dt_collapse_selector_direct_two_zero_sound
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i : native_Nat)
    (x y ti : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 0)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) ti) ->
    mkDtCollapseSelectorGuard (Term.DtSel s d i 0)
      (Term.Apply (Term.Apply (Term.DtCons s d i) x) y) = ti ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 0)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) ti)
      true := by
  intro hBool hGuard
  let t := Term.Apply (Term.Apply (Term.DtCons s d i) x) y
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.DtSel s d i 0) t) ti hBool
  have hTiTrans : RuleProofs.eo_has_smt_translation ti := by
    unfold RuleProofs.eo_has_smt_translation
    rw [← hTypes.1]
    exact hTypes.2
  have hTiNe : ti ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ti hTiTrans
  have hTypeNe : __eo_typeof t ≠ Term.Stuck := by
    intro hType
    have hGuardStuck :
        mkDtCollapseSelectorGuard (Term.DtSel s d i 0) t = Term.Stuck := by
      simp [mkDtCollapseSelectorGuard, t, __dt_arg_list, __get_arg_list_rec,
        __dt_get_selectors_of_app, hType, __eo_list_find, __eo_is_list,
        __eo_requires, assoc_nil_nth_index_stuck, native_ite, native_teq,
        SmtEval.native_not]
    rw [hGuardStuck] at hGuard
    exact hTiNe hGuard.symm
  have hAssoc :
      __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
        (__eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i d i native_nat_zero)
          (Term.DtSel s d i native_nat_zero)) = ti := by
    simpa [mkDtCollapseSelectorGuard, t, __dt_arg_list,
      __get_arg_list_rec, eoTermList, __dt_get_selectors_of_app,
      __dt_get_selectors, __eo_dt_selectors, hTypeNe] using hGuard
  have hFindZero :
      __eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i d i native_nat_zero)
          (Term.DtSel s d i native_nat_zero) =
        Term.Numeral 0 :=
    datatype_cons_selectors_rec_find_sel0_pair_eq_zero_of_assoc_ne_stuck
      s d i d i x y ti hAssoc hTiNe
  rw [hFindZero] at hAssoc
  have hTiEq : ti = x :=
    assoc_nil_nth_pair_zero_eq x y ti hAssoc
  have hBoolX :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.DtSel s d i 0)
            (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) x) := by
    simpa [hTiEq] using hBool
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · rw [hTiEq]
    exact dt_sel_cons_two_zero_eval_rel M hM s d i x y hBoolX

private theorem dt_collapse_selector_direct_two_one_sound
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i : native_Nat)
    (x y ti : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 1)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) ti) ->
    mkDtCollapseSelectorGuard (Term.DtSel s d i 1)
      (Term.Apply (Term.Apply (Term.DtCons s d i) x) y) = ti ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i 1)
          (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) ti)
      true := by
  intro hBool hGuard
  let t := Term.Apply (Term.Apply (Term.DtCons s d i) x) y
  have hTypes :=
    RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      (Term.Apply (Term.DtSel s d i 1) t) ti hBool
  have hTiTrans : RuleProofs.eo_has_smt_translation ti := by
    unfold RuleProofs.eo_has_smt_translation
    rw [← hTypes.1]
    exact hTypes.2
  have hTiNe : ti ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ti hTiTrans
  have hTypeNe : __eo_typeof t ≠ Term.Stuck := by
    intro hType
    have hGuardStuck :
        mkDtCollapseSelectorGuard (Term.DtSel s d i 1) t = Term.Stuck := by
      simp [mkDtCollapseSelectorGuard, t, __dt_arg_list, __get_arg_list_rec,
        __dt_get_selectors_of_app, hType, __eo_list_find, __eo_is_list,
        __eo_requires, assoc_nil_nth_index_stuck, native_ite, native_teq,
        SmtEval.native_not]
    rw [hGuardStuck] at hGuard
    exact hTiNe hGuard.symm
  have hAssoc :
      __assoc_nil_nth Term.__eo_List_cons (eoTermList [x, y])
        (__eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i d i native_nat_zero)
          (Term.DtSel s d i (native_nat_succ native_nat_zero))) = ti := by
    simpa [mkDtCollapseSelectorGuard, t, __dt_arg_list,
      __get_arg_list_rec, eoTermList, __dt_get_selectors_of_app,
      __dt_get_selectors, __eo_dt_selectors, hTypeNe] using hGuard
  have hFindOne :
      __eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i d i native_nat_zero)
          (Term.DtSel s d i (native_nat_succ native_nat_zero)) =
        Term.Numeral 1 :=
    datatype_cons_selectors_rec_find_sel1_pair_eq_one_of_assoc_ne_stuck
      s d i d i x y ti hAssoc hTiNe
  rw [hFindOne] at hAssoc
  have hTiEq : ti = y :=
    assoc_nil_nth_pair_one_eq x y ti hAssoc
  have hBoolY :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
          (Term.Apply (Term.DtSel s d i 1)
            (Term.Apply (Term.Apply (Term.DtCons s d i) x) y))) y) := by
    simpa [hTiEq] using hBool
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · rw [hTiEq]
    exact dt_sel_cons_two_one_eval_rel M hM s d i x y hBoolY

axiom dt_collapse_selector_sound
    (M : SmtModel) (hM : model_total_typed M) (s t ti : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply s t)) ti) ->
  mkDtCollapseSelectorGuard s t = ti ->
  eo_interprets M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply s t)) ti) true

private theorem eq_args_of_prog_dt_collapse_selector_ne_stuck
    (a1 : Term) :
  __eo_prog_dt_collapse_selector a1 ≠ Term.Stuck ->
  ∃ s t ti,
    a1 = Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply s t)) ti ∧
    mkDtCollapseSelectorGuard s t = ti ∧
    __eo_prog_dt_collapse_selector a1 = a1 := by
  intro hProg
  cases a1 with
  | Apply f ti =>
      cases f with
      | Apply g lhs =>
          cases g with
          | UOp op =>
              cases op with
              | eq =>
                  cases lhs with
                  | Apply s t =>
                      let guard := mkDtCollapseSelectorGuard s t
                      let body :=
                        Term.Apply (Term.Apply (Term.UOp UserOp.eq)
                          (Term.Apply s t)) ti
                      have hReq :
                          __eo_requires guard ti body ≠ Term.Stuck := by
                        simpa [__eo_prog_dt_collapse_selector, guard, body,
                          mkDtCollapseSelectorGuard] using hProg
                      have hGuard : guard = ti :=
                        eo_requires_eq_of_ne_stuck guard ti body hReq
                      have hProgEq :
                          __eo_prog_dt_collapse_selector body = body := by
                        simpa [__eo_prog_dt_collapse_selector, guard, body,
                          mkDtCollapseSelectorGuard] using
                            eo_requires_eq_result_of_ne_stuck guard ti body hReq
                      exact ⟨s, t, ti, rfl, by simpa [guard] using hGuard, hProgEq⟩
                  | _ =>
                      change Term.Stuck ≠ Term.Stuck at hProg
                      exact False.elim (hProg rfl)
              | _ =>
                  change Term.Stuck ≠ Term.Stuck at hProg
                  exact False.elim (hProg rfl)
          | _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
  | _ =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)

private theorem prog_dt_collapse_selector_eq_arg_of_typeof_bool
    (a1 : Term) :
  __eo_typeof (__eo_prog_dt_collapse_selector a1) = Term.Bool ->
  __eo_prog_dt_collapse_selector a1 = a1 := by
  intro hTy
  have hProg : __eo_prog_dt_collapse_selector a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hTy
  rcases eq_args_of_prog_dt_collapse_selector_ne_stuck a1 hProg with
    ⟨_s, _t, _ti, _hEq, _hGuard, hProgEq⟩
  exact hProgEq

private theorem typed___eo_prog_dt_collapse_selector_impl
    (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_selector a1) = Term.Bool ->
  RuleProofs.eo_has_bool_type (__eo_prog_dt_collapse_selector a1) := by
  intro hA1Trans hResultTy
  have hProgEq : __eo_prog_dt_collapse_selector a1 = a1 :=
    prog_dt_collapse_selector_eq_arg_of_typeof_bool a1 hResultTy
  have hA1Ty : __eo_typeof a1 = Term.Bool := by
    simpa [hProgEq] using hResultTy
  rw [hProgEq]
  exact RuleProofs.eo_typeof_bool_implies_has_bool_type a1 hA1Trans hA1Ty

private theorem facts___eo_prog_dt_collapse_selector_impl
    (M : SmtModel) (hM : model_total_typed M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_dt_collapse_selector a1) = Term.Bool ->
  eo_interprets M (__eo_prog_dt_collapse_selector a1) true := by
  intro hA1Trans hResultTy
  have hProg : __eo_prog_dt_collapse_selector a1 ≠ Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  rcases eq_args_of_prog_dt_collapse_selector_ne_stuck a1 hProg with
    ⟨sel, t, ti, hA1Eq, hGuard, hProgEq⟩
  have hBool :
      RuleProofs.eo_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply sel t)) ti) := by
    subst hA1Eq
    have hA1Ty :
        __eo_typeof
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply sel t)) ti) =
            Term.Bool := by
      simpa [hProgEq] using hResultTy
    exact RuleProofs.eo_typeof_bool_implies_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply sel t)) ti)
      hA1Trans hA1Ty
  rw [hProgEq]
  rw [hA1Eq]
  cases sel with
  | DtSel ss dd ii jj =>
      cases jj with
      | zero =>
          cases t with
          | Apply f x =>
              cases f with
              | Apply g y =>
                  cases g with
                  | DtCons ss' dd' ii' =>
                      by_cases hss : ss = ss'
                      · by_cases hdd : dd = dd'
                        · by_cases hii : ii = ii'
                          · subst ss'
                            subst dd'
                            subst ii'
                            exact dt_collapse_selector_direct_two_zero_sound
                              M hM ss dd ii y x ti hBool hGuard
                          · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
                        · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
                      · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
                  | _ =>
                      exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
              | DtCons ss' dd' ii' =>
                  by_cases hss : ss = ss'
                  · by_cases hdd : dd = dd'
                    · by_cases hii : ii = ii'
                      · subst ss'
                        subst dd'
                        subst ii'
                        exact dt_collapse_selector_direct_one_sound M hM
                          ss dd ii x ti hBool hGuard
                      · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
                    · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
                  · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
              | _ =>
                  exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
          | _ =>
              exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
      | succ jj' =>
          cases jj' with
          | zero =>
              cases t with
              | Apply f x =>
                  cases f with
                  | Apply g y =>
                      cases g with
                      | DtCons ss' dd' ii' =>
                          by_cases hss : ss = ss'
                          · by_cases hdd : dd = dd'
                            · by_cases hii : ii = ii'
                              · subst ss'
                                subst dd'
                                subst ii'
                                exact dt_collapse_selector_direct_two_one_sound
                                  M hM ss dd ii y x ti hBool hGuard
                              · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
                            · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
                          · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
                      | _ =>
                          exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
                  | _ =>
                      exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
              | _ =>
                  exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
          | succ _ =>
              exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
  | _ =>
      exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard

theorem cmd_step_dt_collapse_selector_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_collapse_selector args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_collapse_selector args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_collapse_selector args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_collapse_selector args premises ≠
      Term.Stuck :=
    term_ne_stuck_of_typeof_bool hResultTy
  cases args with
  | nil =>
      change Term.Stuck ≠ Term.Stuck at hProg
      exact False.elim (hProg rfl)
  | cons a1 args =>
      cases args with
      | nil =>
          cases premises with
          | nil =>
              have hA1TransPair :
                  RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 :=
                hA1TransPair.1
              change __eo_typeof (__eo_prog_dt_collapse_selector a1) =
                Term.Bool at hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_dt_collapse_selector a1) true
                exact facts___eo_prog_dt_collapse_selector_impl M hM a1
                  hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation
                  (__eo_prog_dt_collapse_selector a1)
                exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                  (__eo_prog_dt_collapse_selector a1)
                  (typed___eo_prog_dt_collapse_selector_impl a1
                    hA1Trans hResultTy)
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
