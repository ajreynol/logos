import Cpc.Proofs.RuleSupport.SequenceSupport
import Cpc.Proofs.Translation.EoTypeofCore

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

private def dtAppSpineRev : Term -> Term × List Term
  | Term.Apply f x =>
      let spine := dtAppSpineRev f
      (spine.1, x :: spine.2)
  | t => (t, [])

private def mkDtSmtAppSpineRev (head : SmtTerm) : List SmtTerm -> SmtTerm
  | [] => head
  | x :: xs => SmtTerm.Apply (mkDtSmtAppSpineRev head xs) x

private def mkDtSmtValueSpineRev (head : SmtValue) : List SmtValue -> SmtValue
  | [] => head
  | x :: xs => SmtValue.Apply (mkDtSmtValueSpineRev head xs) x

private def listGetOption : List Term -> Nat -> Option Term
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ n => listGetOption xs n

private theorem dtAppSpineRev_head_eq_appHead :
    ∀ t : Term, (dtAppSpineRev t).1 = appHead t
  | Term.Apply f x => by
      simp [dtAppSpineRev, appHead, dtAppSpineRev_head_eq_appHead f]
  | Term.UOp _ => rfl
  | Term.UOp1 _ _ => rfl
  | Term.UOp2 _ _ _ => rfl
  | Term.UOp3 _ _ _ _ => rfl
  | Term.__eo_List => rfl
  | Term.__eo_List_nil => rfl
  | Term.__eo_List_cons => rfl
  | Term.Bool => rfl
  | Term.Boolean _ => rfl
  | Term.Numeral _ => rfl
  | Term.Rational _ => rfl
  | Term.String _ => rfl
  | Term.Binary _ _ => rfl
  | Term.Type => rfl
  | Term.Stuck => rfl
  | Term.FunType => rfl
  | Term.Var _ _ => rfl
  | Term.DatatypeType _ _ => rfl
  | Term.DatatypeTypeRef _ => rfl
  | Term.DtcAppType _ _ => rfl
  | Term.DtCons _ _ _ => rfl
  | Term.DtSel _ _ _ _ => rfl
  | Term.USort _ => rfl
  | Term.UConst _ _ => rfl

private theorem dtAppSpineRev_args_eq_reverse_appArgs :
    ∀ t : Term, (dtAppSpineRev t).2 = (appArgs t).reverse
  | Term.Apply f x => by
      simp [dtAppSpineRev, appArgs, dtAppSpineRev_args_eq_reverse_appArgs f]
  | Term.UOp _ => rfl
  | Term.UOp1 _ _ => rfl
  | Term.UOp2 _ _ _ => rfl
  | Term.UOp3 _ _ _ _ => rfl
  | Term.__eo_List => rfl
  | Term.__eo_List_nil => rfl
  | Term.__eo_List_cons => rfl
  | Term.Bool => rfl
  | Term.Boolean _ => rfl
  | Term.Numeral _ => rfl
  | Term.Rational _ => rfl
  | Term.String _ => rfl
  | Term.Binary _ _ => rfl
  | Term.Type => rfl
  | Term.Stuck => rfl
  | Term.FunType => rfl
  | Term.Var _ _ => rfl
  | Term.DatatypeType _ _ => rfl
  | Term.DatatypeTypeRef _ => rfl
  | Term.DtcAppType _ _ => rfl
  | Term.DtCons _ _ _ => rfl
  | Term.DtSel _ _ _ _ => rfl
  | Term.USort _ => rfl
  | Term.UConst _ _ => rfl

private theorem eo_to_smt_apply_generic_of_dtAppSpineRev_dtcons
    (s : native_String) (d : Datatype) (i : native_Nat) (t x : Term)
    (hHead : (dtAppSpineRev t).1 = Term.DtCons s d i) :
    __eo_to_smt (Term.Apply t x) =
      SmtTerm.Apply (__eo_to_smt t) (__eo_to_smt x) := by
  cases t with
  | Apply f y =>
      dsimp [dtAppSpineRev] at hHead
      cases f with
      | Apply f' y' =>
          dsimp [dtAppSpineRev] at hHead
          cases f' with
          | Apply f'' y'' =>
              rfl
          | DtCons s' d' i' =>
              simp [dtAppSpineRev] at hHead
              rcases hHead with ⟨rfl, rfl, rfl⟩
              rfl
          | _ =>
              simp [dtAppSpineRev] at hHead
      | DtCons s' d' i' =>
          simp [dtAppSpineRev] at hHead
          rcases hHead with ⟨rfl, rfl, rfl⟩
          rfl
      | _ =>
          simp [dtAppSpineRev] at hHead
  | DtCons s' d' i' =>
      simp [dtAppSpineRev] at hHead
      rcases hHead with ⟨rfl, rfl, rfl⟩
      rfl
  | _ =>
      simp [dtAppSpineRev] at hHead

private theorem eo_to_smt_dtAppSpineRev_dtcons
    (s : native_String) (d : Datatype) (i : native_Nat) (t : Term)
    (hHead : (dtAppSpineRev t).1 = Term.DtCons s d i) :
    __eo_to_smt t =
      mkDtSmtAppSpineRev (__eo_to_smt (Term.DtCons s d i))
        ((dtAppSpineRev t).2.map __eo_to_smt) := by
  cases t with
  | Apply f x =>
      dsimp [dtAppSpineRev] at hHead ⊢
      have hF :
          (dtAppSpineRev f).1 = Term.DtCons s d i := hHead
      rw [eo_to_smt_apply_generic_of_dtAppSpineRev_dtcons s d i f x hF]
      have ihF := eo_to_smt_dtAppSpineRev_dtcons s d i f hF
      rw [ihF]
      rfl
  | DtCons s' d' i' =>
      simp [dtAppSpineRev] at hHead
      rcases hHead with ⟨rfl, rfl, rfl⟩
      rfl
  | _ =>
      simp [dtAppSpineRev] at hHead
termination_by t

private theorem vsm_apply_head_mkDtSmtValueSpineRev_dtcons
    (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    ∀ xs : List SmtValue,
      __vsm_apply_head
          (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) =
        SmtValue.DtCons s d i
  | [] => by
      simp [mkDtSmtValueSpineRev, __vsm_apply_head]
  | x :: xs => by
      simp [mkDtSmtValueSpineRev, __vsm_apply_head,
        vsm_apply_head_mkDtSmtValueSpineRev_dtcons s d i xs]

private theorem vsm_num_apply_args_mkDtSmtValueSpineRev_dtcons
    (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    ∀ xs : List SmtValue,
      vsm_num_apply_args
          (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) =
        xs.length
  | [] => by
      simp [mkDtSmtValueSpineRev, vsm_num_apply_args]
  | x :: xs => by
      simp [mkDtSmtValueSpineRev, vsm_num_apply_args,
        vsm_num_apply_args_mkDtSmtValueSpineRev_dtcons s d i xs]

private theorem mkDtSmtValueSpineRev_append_singleton
    (head x : SmtValue) :
    ∀ xs : List SmtValue,
      mkDtSmtValueSpineRev head (xs ++ [x]) =
        mkDtSmtValueSpineRev (SmtValue.Apply head x) xs
  | [] => by
      simp [mkDtSmtValueSpineRev]
  | y :: ys => by
      simp [mkDtSmtValueSpineRev,
        mkDtSmtValueSpineRev_append_singleton head x ys]

private theorem vsm_apply_arg_nth_mkDtSmtValueSpineRev_head_arg
    (head a : SmtValue) :
    ∀ ys : List SmtValue,
      __vsm_apply_arg_nth
          (mkDtSmtValueSpineRev (SmtValue.Apply head a) ys)
          0 (ys.length + 1) = a
  | [] => by
      simp [mkDtSmtValueSpineRev, __vsm_apply_arg_nth, native_nateq,
        native_ite]
  | y :: ys => by
      simp [mkDtSmtValueSpineRev, __vsm_apply_arg_nth, native_nateq,
        native_ite,
        vsm_apply_arg_nth_mkDtSmtValueSpineRev_head_arg head a ys]

private theorem vsm_apply_arg_nth_mkDtSmtValueSpineRev_succ
    (head a : SmtValue) :
    ∀ (ys : List SmtValue) (j : Nat),
      __vsm_apply_arg_nth
          (mkDtSmtValueSpineRev (SmtValue.Apply head a) ys)
          (Nat.succ j) (ys.length + 1) =
        __vsm_apply_arg_nth
          (mkDtSmtValueSpineRev head ys) j ys.length
  | [], j => by
      simp [mkDtSmtValueSpineRev, __vsm_apply_arg_nth, native_nateq,
        native_ite]
  | y :: ys, j => by
      by_cases hj : j = ys.length
      · subst j
        simp [mkDtSmtValueSpineRev, __vsm_apply_arg_nth, native_nateq,
          native_ite]
      · simp [mkDtSmtValueSpineRev, __vsm_apply_arg_nth, native_nateq,
          native_ite, hj,
          vsm_apply_arg_nth_mkDtSmtValueSpineRev_succ head a ys j]

private theorem vsm_apply_arg_nth_mkDtSmtValueSpineRev_reverse_map_get?
    (M : SmtModel) (head : SmtValue) :
    ∀ (xs : List Term) (j : Nat) (ti : Term),
      listGetOption xs j = some ti ->
      __vsm_apply_arg_nth
          (mkDtSmtValueSpineRev head
            (xs.reverse.map (fun x => __smtx_model_eval M (__eo_to_smt x))))
          j xs.length =
        __smtx_model_eval M (__eo_to_smt ti)
  | [], j, ti, h => by
      cases j <;> simp [listGetOption] at h
  | x :: xs, Nat.zero, ti, h => by
      simp [listGetOption] at h
      subst ti
      rw [List.reverse_cons, List.map_append]
      simp only [List.map, List.length_cons]
      rw [mkDtSmtValueSpineRev_append_singleton]
      simpa [List.length_reverse] using
        vsm_apply_arg_nth_mkDtSmtValueSpineRev_head_arg head
          (__smtx_model_eval M (__eo_to_smt x))
          ((List.map (fun x => __smtx_model_eval M (__eo_to_smt x)) xs).reverse)
  | x :: xs, Nat.succ j, ti, h => by
      have hRec :=
        vsm_apply_arg_nth_mkDtSmtValueSpineRev_reverse_map_get? M head
          xs j ti (by simpa [listGetOption] using h)
      rw [List.map_reverse] at hRec
      let ys :=
        (List.map (fun x => __smtx_model_eval M (__eo_to_smt x)) xs).reverse
      have hRecLen :
          __vsm_apply_arg_nth (mkDtSmtValueSpineRev head ys) j ys.length =
            __smtx_model_eval M (__eo_to_smt ti) := by
        simpa [ys, List.length_reverse] using hRec
      rw [List.reverse_cons, List.map_append]
      simp only [List.map, List.length_cons]
      rw [mkDtSmtValueSpineRev_append_singleton]
      simpa [ys, List.length_reverse] using
        (vsm_apply_arg_nth_mkDtSmtValueSpineRev_succ head
          (__smtx_model_eval M (__eo_to_smt x)) ys j).trans hRecLen

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

private theorem eo_add_nat_succ_minus_one (n : Nat) :
    __eo_add (Term.Numeral (Nat.succ n))
        (Term.Numeral (-1 : native_Int)) = Term.Numeral n := by
  change Term.Numeral (((Nat.succ n : Nat) : native_Int) + (-1 : native_Int)) =
    Term.Numeral ((n : Nat) : native_Int)
  congr
  rw [Int.natCast_succ]
  exact Int.add_neg_cancel_right ((n : Nat) : Int) 1

private theorem eo_add_nat_one (n : Nat) :
    __eo_add (Term.Numeral n) (Term.Numeral (1 : native_Int)) =
      Term.Numeral (Nat.succ n) := by
  change Term.Numeral (((n : Nat) : native_Int) + (1 : native_Int)) =
    Term.Numeral ((Nat.succ n : Nat) : native_Int)
  congr

private theorem term_num_nat_succ_ne_zero (n : Nat) :
    (Term.Numeral (Nat.succ n) : Term) ≠ Term.Numeral 0 := by
  intro hEq
  injection hEq with hInt
  have hIntNe : ((Nat.succ n : Nat) : native_Int) ≠ 0 := by
    exact Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero n)
  exact hIntNe hInt

private theorem term_num_ne_zero_of_int_ne {z : native_Int} (hz : z ≠ 0) :
    (Term.Numeral z : Term) ≠ Term.Numeral 0 := by
  intro hEq
  injection hEq with hInt
  exact hz hInt

private theorem assoc_nil_nth_eoTermList_cons_numeral_ne_zero
    (x : Term) (xs : List Term) (z : native_Int) (hz : z ≠ 0) :
    __assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
        (Term.Numeral z) =
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
        (__eo_add (Term.Numeral z) (Term.Numeral (-1 : native_Int))) := by
  have hAssoc :
      __assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
          (Term.Numeral z) =
        __eo_l_1___assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
          (Term.Numeral z) := by
    apply __assoc_nil_nth.eq_5
    · intro h
      cases h
    · intro h
      cases h
    · intro h
      cases h
    · intro _f _x1 _x2 _hList hZero
      exact term_num_ne_zero_of_int_ne hz hZero
  have hTail :
      __eo_l_1___assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
          (Term.Numeral z) =
        __eo_requires (__eo_eq Term.__eo_List_cons Term.__eo_List_cons)
          (Term.Boolean true)
          (__assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
            (__eo_add (Term.Numeral z) (Term.Numeral (-1 : native_Int)))) := by
    simpa [eoTermList] using
      (__eo_l_1___assoc_nil_nth.eq_3 Term.__eo_List_cons
        (Term.Numeral z) Term.__eo_List_cons x (eoTermList xs)
        (by intro h; cases h) (by intro h; cases h))
  calc
    __assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
        (Term.Numeral z) =
        __eo_l_1___assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
          (Term.Numeral z) := hAssoc
    _ =
        __eo_requires (__eo_eq Term.__eo_List_cons Term.__eo_List_cons)
          (Term.Boolean true)
          (__assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
            (__eo_add (Term.Numeral z) (Term.Numeral (-1 : native_Int)))) := hTail
    _ =
        __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
          (__eo_add (Term.Numeral z) (Term.Numeral (-1 : native_Int))) := by
      simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
        SmtEval.native_not]

private theorem assoc_nil_nth_eoTermList_cons_succ
    (x : Term) (xs : List Term) (n : Nat) :
    __assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
        (Term.Numeral (Nat.succ n)) =
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
        (Term.Numeral n) := by
  calc
    __assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
        (Term.Numeral (Nat.succ n)) =
        __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
          (__eo_add (Term.Numeral (Nat.succ n))
            (Term.Numeral (-1 : native_Int))) := by
      exact assoc_nil_nth_eoTermList_cons_numeral_ne_zero x xs
        ((Nat.succ n : Nat) : native_Int) (by
          exact Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero n))
    _ =
        __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
          (Term.Numeral n) := by
      rw [eo_add_nat_succ_minus_one n]

private theorem assoc_nil_nth_eoTermList_negSucc_stuck :
    forall (xs : List Term) (k : Nat),
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
          (Term.Numeral (Int.negSucc k)) = Term.Stuck
  | [], k => by
      simp [eoTermList, assoc_nil_nth_nil_stuck]
  | x :: xs, k => by
      calc
        __assoc_nil_nth Term.__eo_List_cons (eoTermList (x :: xs))
            (Term.Numeral (Int.negSucc k)) =
            __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
              (__eo_add (Term.Numeral (Int.negSucc k))
                (Term.Numeral (-1 : native_Int))) := by
          exact assoc_nil_nth_eoTermList_cons_numeral_ne_zero x xs
            (Int.negSucc k) (Int.negSucc_ne_zero k)
        _ =
            __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
              (Term.Numeral (Int.negSucc (k + 1))) := by
          rfl
        _ = Term.Stuck :=
          assoc_nil_nth_eoTermList_negSucc_stuck xs (k + 1)

private theorem assoc_nil_nth_eoTermList_get? :
    forall (xs : List Term) (n : Nat) (ti : Term),
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
          (Term.Numeral n) = ti ->
      ti ≠ Term.Stuck ->
      listGetOption xs n = some ti
  | [], n, ti, h, hTi => by
      simp [eoTermList, assoc_nil_nth_nil_stuck] at h
      exact False.elim (hTi h.symm)
  | x :: xs, 0, ti, h, _hTi => by
      simp [eoTermList, __assoc_nil_nth, __eo_eq, native_ite,
        native_teq] at h
      simp [listGetOption, h.symm]
  | x :: xs, Nat.succ n, ti, h, hTi => by
      have hRec :
          __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
              (Term.Numeral n) = ti := by
        rwa [assoc_nil_nth_eoTermList_cons_succ x xs n] at h
      simpa [listGetOption] using
        assoc_nil_nth_eoTermList_get? xs n ti hRec hTi

private theorem dt_arg_list_of_appHead_dtcons
    (s : native_String) (d : Datatype) (i : native_Nat) :
    forall (t : Term),
      appHead t = Term.DtCons s d i ->
      __dt_arg_list t = eoTermList (appArgs t)
  | Term.Apply f x, hHead => by
      have hHeadNe : appHead (Term.Apply f x) ≠ Term.Stuck := by
        rw [hHead]
        intro h
        cases h
      have hGet :=
        get_arg_list_rec_eoTermList_appArgs (Term.Apply f x) [] hHeadNe
      cases f with
      | Apply g y =>
          cases g with
          | UOp op =>
              cases op <;> simp [appHead] at hHead
          | Stuck =>
              simp [appHead] at hHead
          | _ =>
              simpa [__dt_arg_list] using hGet
      | Stuck =>
          simp [appHead] at hHead
      | _ =>
          simpa [__dt_arg_list] using hGet
  | Term.DtCons s' d' i', hHead => by
      simp [appHead] at hHead
      rcases hHead with ⟨rfl, rfl, rfl⟩
      simp [__dt_arg_list, __get_arg_list_rec, appArgs, eoTermList]
  | Term.Stuck, hHead => by
      simp [appHead] at hHead
  | Term.UOp op, hHead => by
      simp [appHead] at hHead
  | Term.UOp1 op a, hHead => by
      simp [appHead] at hHead
  | Term.UOp2 op a b, hHead => by
      simp [appHead] at hHead
  | Term.UOp3 op a b c, hHead => by
      simp [appHead] at hHead
  | Term.__eo_List, hHead => by
      simp [appHead] at hHead
  | Term.__eo_List_nil, hHead => by
      simp [appHead] at hHead
  | Term.__eo_List_cons, hHead => by
      simp [appHead] at hHead
  | Term.Bool, hHead => by
      simp [appHead] at hHead
  | Term.Boolean b, hHead => by
      simp [appHead] at hHead
  | Term.Numeral n, hHead => by
      simp [appHead] at hHead
  | Term.Rational q, hHead => by
      simp [appHead] at hHead
  | Term.String str, hHead => by
      simp [appHead] at hHead
  | Term.Binary w n, hHead => by
      simp [appHead] at hHead
  | Term.Type, hHead => by
      simp [appHead] at hHead
  | Term.FunType, hHead => by
      simp [appHead] at hHead
  | Term.Var n T, hHead => by
      simp [appHead] at hHead
  | Term.DatatypeType s' d', hHead => by
      simp [appHead] at hHead
  | Term.DatatypeTypeRef s', hHead => by
      simp [appHead] at hHead
  | Term.DtcAppType T U, hHead => by
      simp [appHead] at hHead
  | Term.DtSel s' d' i' j', hHead => by
      simp [appHead] at hHead
  | Term.USort n, hHead => by
      simp [appHead] at hHead
  | Term.UConst n T, hHead => by
      simp [appHead] at hHead

private theorem dt_get_selectors_of_app_of_appHead_dtcons
    (T : Term) (s : native_String) (d : Datatype) (i : native_Nat) :
    forall (t : Term),
      (T = Term.Stuck -> False) ->
      appHead t = Term.DtCons s d i ->
      __dt_get_selectors_of_app T t =
        __eo_dt_selectors (Term.DtCons s d i)
  | Term.Apply f x, hT, hHead => by
      simpa [__dt_get_selectors_of_app, appHead] using
        dt_get_selectors_of_app_of_appHead_dtcons T s d i f hT hHead
  | Term.DtCons s' d' i', hT, hHead => by
      simp [appHead] at hHead
      rcases hHead with ⟨rfl, rfl, rfl⟩
      cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors] at hT ⊢
  | Term.Stuck, _hT, hHead => by
      simp [appHead] at hHead
  | Term.UOp op, _hT, hHead => by
      simp [appHead] at hHead
  | Term.UOp1 op a, _hT, hHead => by
      simp [appHead] at hHead
  | Term.UOp2 op a b, _hT, hHead => by
      simp [appHead] at hHead
  | Term.UOp3 op a b c, _hT, hHead => by
      simp [appHead] at hHead
  | Term.__eo_List, _hT, hHead => by
      simp [appHead] at hHead
  | Term.__eo_List_nil, _hT, hHead => by
      simp [appHead] at hHead
  | Term.__eo_List_cons, _hT, hHead => by
      simp [appHead] at hHead
  | Term.Bool, _hT, hHead => by
      simp [appHead] at hHead
  | Term.Boolean b, _hT, hHead => by
      simp [appHead] at hHead
  | Term.Numeral n, _hT, hHead => by
      simp [appHead] at hHead
  | Term.Rational q, _hT, hHead => by
      simp [appHead] at hHead
  | Term.String str, _hT, hHead => by
      simp [appHead] at hHead
  | Term.Binary w n, _hT, hHead => by
      simp [appHead] at hHead
  | Term.Type, _hT, hHead => by
      simp [appHead] at hHead
  | Term.FunType, _hT, hHead => by
      simp [appHead] at hHead
  | Term.Var n T', _hT, hHead => by
      simp [appHead] at hHead
  | Term.DatatypeType s' d', _hT, hHead => by
      simp [appHead] at hHead
  | Term.DatatypeTypeRef s', _hT, hHead => by
      simp [appHead] at hHead
  | Term.DtcAppType T' U, _hT, hHead => by
      simp [appHead] at hHead
  | Term.DtSel s' d' i' j', _hT, hHead => by
      simp [appHead] at hHead
  | Term.USort n, _hT, hHead => by
      simp [appHead] at hHead
  | Term.UConst n T', _hT, hHead => by
      simp [appHead] at hHead
termination_by t => t

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

private theorem datatype_cons_selectors_rec_find_rec_eq_index_of_assoc_ne_stuck
    (s : native_String) (d : Datatype) (i : native_Nat) :
    ∀ (rest : Datatype) (ci ai start j : native_Nat) (xs : List Term) (ti : Term),
      ai = start ->
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
        (__eo_list_find_rec
          (__eo_datatype_cons_selectors_rec s d i rest ci ai)
          (Term.DtSel s d i j) (Term.Numeral start)) = ti ->
      ti ≠ Term.Stuck ->
      __eo_list_find_rec
          (__eo_datatype_cons_selectors_rec s d i rest ci ai)
          (Term.DtSel s d i j) (Term.Numeral start) =
        Term.Numeral j
  | Datatype.null, ci, ai, start, j, xs, ti, hStart, hAssoc, hTi => by
      have hFind :
          __eo_list_find_rec
              (__eo_datatype_cons_selectors_rec s d i Datatype.null ci ai)
              (Term.DtSel s d i j) (Term.Numeral start) = Term.Stuck := by
        cases ci <;> simp [__eo_datatype_cons_selectors_rec, __eo_list_find_rec]
      rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
      exact False.elim (hTi hAssoc.symm)
  | Datatype.sum DatatypeCons.unit restTail, Nat.zero, ai, start, j, xs, ti,
      hStart, hAssoc, hTi => by
      have hFind :
          __eo_list_find_rec
              (__eo_datatype_cons_selectors_rec s d i
                (Datatype.sum DatatypeCons.unit restTail) Nat.zero ai)
              (Term.DtSel s d i j) (Term.Numeral start) =
            Term.Numeral (-1 : native_Int) := by
        simp [__eo_datatype_cons_selectors_rec, __eo_list_find_rec]
      rw [hFind] at hAssoc
      rw [show (-1 : native_Int) = Int.negSucc 0 by rfl] at hAssoc
      rw [assoc_nil_nth_eoTermList_negSucc_stuck xs 0] at hAssoc
      exact False.elim (hTi hAssoc.symm)
  | Datatype.sum (DatatypeCons.cons U c) restTail, Nat.zero, ai, start, j,
      xs, ti, hStart, hAssoc, hTi => by
      subst start
      let target := Term.DtSel s d i j
      let current := Term.DtSel s d i ai
      let tail :=
        __eo_datatype_cons_selectors_rec s d i restTail Nat.zero
          (native_nat_succ ai)
      by_cases hTail : tail = Term.Stuck
      · have hFind :
            __eo_list_find_rec
                (__eo_datatype_cons_selectors_rec s d i
                  (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero ai)
                target (Term.Numeral ai) = Term.Stuck := by
          simp [target, current, tail, __eo_datatype_cons_selectors_rec,
            __eo_mk_apply, hTail, __eo_list_find_rec]
        rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
        exact False.elim (hTi hAssoc.symm)
      · have hList :
            __eo_datatype_cons_selectors_rec s d i
                (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero ai =
              Term.Apply (Term.Apply Term.__eo_List_cons current) tail := by
          simp [current, tail, __eo_datatype_cons_selectors_rec,
            __eo_mk_apply, hTail]
        by_cases hEq : j = ai
        · subst j
          have hCurrentNe : current ≠ Term.Stuck := by
            simp [current]
          have hStartNe : Term.Numeral ai ≠ Term.Stuck := by
            intro h
            cases h
          simpa [hList, target, current] using
            eo_list_find_rec_cons_self_eq current tail (Term.Numeral ai)
              hCurrentNe hStartNe
        · have hRecFind :
              __eo_list_find_rec
                  (Term.Apply (Term.Apply Term.__eo_List_cons current) tail)
                  target (Term.Numeral ai) =
                __eo_list_find_rec tail target (Term.Numeral (Nat.succ ai)) := by
            have hCurrentTarget : current ≠ target := by
              intro h
              simp [current, target] at h
              exact hEq h.symm
            simp [current, target, __eo_list_find_rec, __eo_eq, __eo_add,
              eo_add_nat_one, native_ite, native_teq, native_nateq,
              native_zplus, hEq, hCurrentTarget]
          have hAssocTail :
              __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
                (__eo_list_find_rec tail target
                  (Term.Numeral (Nat.succ ai))) = ti := by
            rw [hList] at hAssoc
            rw [hRecFind] at hAssoc
            exact hAssoc
          have hTailFind :
              __eo_list_find_rec tail target
                  (Term.Numeral (Nat.succ ai)) =
                Term.Numeral j := by
            simpa [target, tail] using
              datatype_cons_selectors_rec_find_rec_eq_index_of_assoc_ne_stuck
                s d i restTail Nat.zero (Nat.succ ai) (Nat.succ ai) j
                xs ti rfl hAssocTail hTi
          rw [hList]
          exact hRecFind.trans hTailFind
  | Datatype.sum c restTail, Nat.succ ci, ai, start, j, xs, ti, hStart,
      hAssoc, hTi => by
      have hAssoc' :
          __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
            (__eo_list_find_rec
              (__eo_datatype_cons_selectors_rec s d i restTail ci ai)
              (Term.DtSel s d i j) (Term.Numeral start)) = ti := by
        simpa [__eo_datatype_cons_selectors_rec] using hAssoc
      simpa [__eo_datatype_cons_selectors_rec] using
        datatype_cons_selectors_rec_find_rec_eq_index_of_assoc_ne_stuck
          s d i restTail ci ai start j xs ti hStart hAssoc' hTi

private theorem datatype_cons_selectors_rec_find_eq_index_of_assoc_ne_stuck
    (s : native_String) (d : Datatype) (i j : native_Nat)
    (xs : List Term) (ti : Term) :
    __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
      (__eo_list_find Term.__eo_List_cons
        (__eo_datatype_cons_selectors_rec s d i d i native_nat_zero)
        (Term.DtSel s d i j)) = ti ->
    ti ≠ Term.Stuck ->
    __eo_list_find Term.__eo_List_cons
        (__eo_datatype_cons_selectors_rec s d i d i native_nat_zero)
        (Term.DtSel s d i j) =
      Term.Numeral j := by
  intro hAssoc hTi
  let selectors := __eo_datatype_cons_selectors_rec s d i d i native_nat_zero
  let target := Term.DtSel s d i j
  have hFindNe :
      __eo_list_find Term.__eo_List_cons selectors target ≠ Term.Stuck := by
    intro hFind
    rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
    exact hTi hAssoc.symm
  have hReqEq :=
    eo_requires_eq_result_of_ne_stuck
      (__eo_is_list Term.__eo_List_cons selectors) (Term.Boolean true)
      (__eo_list_find_rec selectors target (Term.Numeral 0)) hFindNe
  have hAssocRec :
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
        (__eo_list_find_rec selectors target (Term.Numeral 0)) = ti := by
    rw [show __eo_list_find Term.__eo_List_cons selectors target =
        __eo_list_find_rec selectors target (Term.Numeral 0) by
      simpa [selectors, target, __eo_list_find] using hReqEq] at hAssoc
    exact hAssoc
  have hRec :
      __eo_list_find_rec selectors target (Term.Numeral 0) =
        Term.Numeral j := by
    simpa [selectors, target] using
      datatype_cons_selectors_rec_find_rec_eq_index_of_assoc_ne_stuck
        s d i d i native_nat_zero native_nat_zero j xs ti rfl hAssocRec hTi
  exact hReqEq.trans hRec

private theorem dt_collapse_selector_guard_get_arg_of_appHead_dtcons
    (s : native_String) (d : Datatype) (i j : native_Nat)
    (t ti : Term) :
    appHead t = Term.DtCons s d i ->
    mkDtCollapseSelectorGuard (Term.DtSel s d i j) t = ti ->
    ti ≠ Term.Stuck ->
    listGetOption (appArgs t) j = some ti := by
  intro hHead hGuard hTi
  have hTypeNe : __eo_typeof t ≠ Term.Stuck := by
    intro hType
    have hGuardStuck :
        mkDtCollapseSelectorGuard (Term.DtSel s d i j) t = Term.Stuck := by
      simp [mkDtCollapseSelectorGuard, __dt_get_selectors_of_app, hType,
        __eo_list_find, __eo_is_list, __eo_requires, assoc_nil_nth_index_stuck,
        native_ite, native_teq, SmtEval.native_not]
    rw [hGuardStuck] at hGuard
    exact hTi hGuard.symm
  have hArgList :
      __dt_arg_list t = eoTermList (appArgs t) :=
    dt_arg_list_of_appHead_dtcons s d i t hHead
  have hSelectors :
      __dt_get_selectors_of_app (__eo_typeof t) t =
        __eo_dt_selectors (Term.DtCons s d i) :=
    dt_get_selectors_of_app_of_appHead_dtcons
      (__eo_typeof t) s d i t (by exact hTypeNe) hHead
  have hAssoc :
      __assoc_nil_nth Term.__eo_List_cons (eoTermList (appArgs t))
        (__eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i d i native_nat_zero)
          (Term.DtSel s d i j)) = ti := by
    simpa [mkDtCollapseSelectorGuard, hArgList, hSelectors, __eo_dt_selectors]
      using hGuard
  have hFind :
      __eo_list_find Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i d i native_nat_zero)
          (Term.DtSel s d i j) =
        Term.Numeral j :=
    datatype_cons_selectors_rec_find_eq_index_of_assoc_ne_stuck
      s d i j (appArgs t) ti hAssoc hTi
  rw [hFind] at hAssoc
  exact assoc_nil_nth_eoTermList_get? (appArgs t) j ti hAssoc hTi

private theorem tuple_get_selectors_rec_stuck_of_not_tuple_or_unit
    (T n : Term) :
    T ≠ Term.UOp UserOp.UnitTuple ->
    (∀ T1 T2, T ≠ Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2) ->
    __tuple_get_selectors_rec T n = Term.Stuck := by
  intro hUnit hTuple
  cases n <;> try rfl
  all_goals
    cases T with
    | UOp op =>
        cases op <;> simp [__tuple_get_selectors_rec] at hUnit ⊢
    | Apply f x =>
        cases f with
        | Apply g y =>
            cases g with
            | UOp op =>
                cases op <;> simp [__tuple_get_selectors_rec] at hTuple ⊢
            | _ =>
                simp [__tuple_get_selectors_rec]
        | _ =>
            simp [__tuple_get_selectors_rec]
    | _ =>
        simp [__tuple_get_selectors_rec]

private theorem tuple_get_selectors_rec_find_rec_eq_index_of_assoc_ne_stuck :
    ∀ (T : Term) (start j : native_Nat) (xs : List Term) (ti : Term),
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
        (__eo_list_find_rec
          (__tuple_get_selectors_rec T (Term.Numeral start))
          (Term.UOp1 UserOp1.tuple_select (Term.Numeral j))
          (Term.Numeral start)) = ti ->
      ti ≠ Term.Stuck ->
      __eo_list_find_rec
          (__tuple_get_selectors_rec T (Term.Numeral start))
          (Term.UOp1 UserOp1.tuple_select (Term.Numeral j))
          (Term.Numeral start) =
        Term.Numeral j := by
  intro T start j xs ti hAssoc hTi
  by_cases hUnit : T = Term.UOp UserOp.UnitTuple
  · subst T
    have hFind :
        __eo_list_find_rec
            (__tuple_get_selectors_rec (Term.UOp UserOp.UnitTuple)
              (Term.Numeral start))
            (Term.UOp1 UserOp1.tuple_select (Term.Numeral j))
            (Term.Numeral start) =
          Term.Numeral (-1 : native_Int) := by
      simp [__tuple_get_selectors_rec, __eo_list_find_rec]
    rw [hFind] at hAssoc
    rw [show (-1 : native_Int) = Int.negSucc 0 by rfl] at hAssoc
    rw [assoc_nil_nth_eoTermList_negSucc_stuck xs 0] at hAssoc
    exact False.elim (hTi hAssoc.symm)
  · by_cases hTuple :
        ∃ T1 T2, T = Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2
    · rcases hTuple with ⟨T1, T2, rfl⟩
      let target := Term.UOp1 UserOp1.tuple_select (Term.Numeral j)
      let current := Term.UOp1 UserOp1.tuple_select (Term.Numeral start)
      let tail := __tuple_get_selectors_rec T2
        (__eo_add (Term.Numeral start) (Term.Numeral 1))
      by_cases hTail : tail = Term.Stuck
      · have hFind :
            __eo_list_find_rec
                (__tuple_get_selectors_rec
                  (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
                  (Term.Numeral start))
                target (Term.Numeral start) = Term.Stuck := by
          simp [target, current, tail, __tuple_get_selectors_rec,
            __eo_mk_apply, hTail, __eo_list_find_rec]
        rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
        exact False.elim (hTi hAssoc.symm)
      · have hList :
            __tuple_get_selectors_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
                (Term.Numeral start) =
              Term.Apply (Term.Apply Term.__eo_List_cons current) tail := by
          simp [current, tail, __tuple_get_selectors_rec, __eo_mk_apply,
            hTail]
        by_cases hEq : j = start
        · subst j
          have hCurrentNe : current ≠ Term.Stuck := by
            simp [current]
          have hStartNe : Term.Numeral start ≠ Term.Stuck := by
            intro h
            cases h
          simpa [hList, target, current] using
            eo_list_find_rec_cons_self_eq current tail (Term.Numeral start)
              hCurrentNe hStartNe
        · have hRecFind :
              __eo_list_find_rec
                  (Term.Apply (Term.Apply Term.__eo_List_cons current) tail)
                  target (Term.Numeral start) =
                __eo_list_find_rec tail target
                  (Term.Numeral (Nat.succ start)) := by
            have hCurrentTarget : current ≠ target := by
              intro h
              simp [current, target] at h
              exact hEq (Int.ofNat.inj (by simpa using h.symm))
            have hIntNe : ((j : Nat) : Int) ≠ ((start : Nat) : Int) := by
              intro h
              exact hEq (Int.ofNat.inj h)
            simp [current, target, __eo_list_find_rec, __eo_eq, __eo_add,
              eo_add_nat_one, native_ite, native_teq, native_nateq,
              native_zplus, hEq, hCurrentTarget, hIntNe]
          have hAssocTail :
              __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
                (__eo_list_find_rec tail target
                  (Term.Numeral (Nat.succ start))) = ti := by
            rw [hList] at hAssoc
            rw [hRecFind] at hAssoc
            exact hAssoc
          have hTailFind :
              __eo_list_find_rec tail target
                  (Term.Numeral (Nat.succ start)) =
                Term.Numeral j := by
            have hStartSucc :
                __eo_add (Term.Numeral start) (Term.Numeral 1) =
                  Term.Numeral (Nat.succ start) :=
              eo_add_nat_one start
            simpa [target, tail, hStartSucc] using
              tuple_get_selectors_rec_find_rec_eq_index_of_assoc_ne_stuck
                T2 (Nat.succ start) j xs ti hAssocTail hTi
          rw [hList]
          exact hRecFind.trans hTailFind
    · have hNotTuple :
          ∀ T1 T2,
            T ≠ Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2 := by
        intro T1 T2 h
        exact hTuple ⟨T1, T2, h⟩
      have hSelStuck :
          __tuple_get_selectors_rec T (Term.Numeral start) = Term.Stuck :=
        tuple_get_selectors_rec_stuck_of_not_tuple_or_unit
          T (Term.Numeral start) hUnit hNotTuple
      have hFind :
          __eo_list_find_rec
              (__tuple_get_selectors_rec T (Term.Numeral start))
              (Term.UOp1 UserOp1.tuple_select (Term.Numeral j))
              (Term.Numeral start) = Term.Stuck := by
        rw [hSelStuck]
        simp [__eo_list_find_rec]
      rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
      exact False.elim (hTi hAssoc.symm)
termination_by T start j xs ti hAssoc hTi => T

private theorem tuple_get_selectors_rec_find_eq_index_of_assoc_ne_stuck
    (T : Term) (j : native_Nat) (xs : List Term) (ti : Term) :
    __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
      (__eo_list_find Term.__eo_List_cons
        (__tuple_get_selectors_rec T (Term.Numeral 0))
        (Term.UOp1 UserOp1.tuple_select (Term.Numeral j))) = ti ->
    ti ≠ Term.Stuck ->
    __eo_list_find Term.__eo_List_cons
        (__tuple_get_selectors_rec T (Term.Numeral 0))
        (Term.UOp1 UserOp1.tuple_select (Term.Numeral j)) =
      Term.Numeral j := by
  intro hAssoc hTi
  let selectors := __tuple_get_selectors_rec T (Term.Numeral 0)
  let target := Term.UOp1 UserOp1.tuple_select (Term.Numeral j)
  have hFindNe :
      __eo_list_find Term.__eo_List_cons selectors target ≠ Term.Stuck := by
    intro hFind
    rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
    exact hTi hAssoc.symm
  have hReqEq :=
    eo_requires_eq_result_of_ne_stuck
      (__eo_is_list Term.__eo_List_cons selectors) (Term.Boolean true)
      (__eo_list_find_rec selectors target (Term.Numeral 0)) hFindNe
  have hAssocRec :
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
        (__eo_list_find_rec selectors target (Term.Numeral 0)) = ti := by
    rw [show __eo_list_find Term.__eo_List_cons selectors target =
        __eo_list_find_rec selectors target (Term.Numeral 0) by
      simpa [selectors, target, __eo_list_find] using hReqEq] at hAssoc
    exact hAssoc
  have hRec :
      __eo_list_find_rec selectors target (Term.Numeral 0) =
        Term.Numeral j := by
    simpa [selectors, target] using
      tuple_get_selectors_rec_find_rec_eq_index_of_assoc_ne_stuck
        T native_nat_zero j xs ti hAssocRec hTi
  exact hReqEq.trans hRec

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

private theorem model_eval_apply_mkDtSmtValueSpineRev_dtcons_of_arg_ne_notvalue
    (M : SmtModel) (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (xs : List SmtValue) (a : SmtValue) :
    a ≠ SmtValue.NotValue ->
    __smtx_model_eval_apply M
        (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) a =
      SmtValue.Apply (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) a := by
  intro ha
  cases xs with
  | nil =>
      simpa [mkDtSmtValueSpineRev] using
        model_eval_apply_dtcons_of_arg_ne_notvalue M s d i a ha
  | cons x xs =>
      simpa [mkDtSmtValueSpineRev] using
        model_eval_apply_smt_apply_of_arg_ne_notvalue M
          (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) x a ha

private theorem smtx_typeof_apply_mkDtSmtAppSpineRev_dtcons
    (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (xs : List SmtTerm) (x : SmtTerm) :
    __smtx_typeof
        (SmtTerm.Apply (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) x) =
      __smtx_typeof_apply
        (__smtx_typeof (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs))
        (__smtx_typeof x) := by
  cases xs with
  | nil =>
      simp [mkDtSmtAppSpineRev, __smtx_typeof]
  | cons y ys =>
      simp [mkDtSmtAppSpineRev, __smtx_typeof]

private theorem mkDtSmtAppSpineRev_args_non_none_of_non_none_type
    (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    ∀ xs : List SmtTerm,
      __smtx_typeof (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) ≠
        SmtType.None ->
      ∀ x ∈ xs, __smtx_typeof x ≠ SmtType.None
  | [], _hNN, x, hx => by
      simp at hx
  | x :: xs, hNN, y, hy => by
      have hApplyNN :
          __smtx_typeof_apply
              (__smtx_typeof
                (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs))
              (__smtx_typeof x) ≠ SmtType.None := by
        rw [← smtx_typeof_apply_mkDtSmtAppSpineRev_dtcons s d i xs x]
        simpa [mkDtSmtAppSpineRev] using hNN
      rcases typeof_apply_non_none_cases hApplyNN with
        ⟨A, B, hF, hX, hA, _hB⟩
      have hxNN : __smtx_typeof x ≠ SmtType.None := by
        rw [hX]
        exact hA
      have hHeadNN :
          __smtx_typeof
              (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) ≠
            SmtType.None := by
        intro hNone
        rcases hF with hF | hF <;> rw [hNone] at hF <;> cases hF
      cases hy with
      | head =>
          exact hxNN
      | tail _ hyTail =>
          exact mkDtSmtAppSpineRev_args_non_none_of_non_none_type
            s d i xs hHeadNN y hyTail

private theorem smtx_model_eval_apply_mkDtSmtAppSpineRev_dtcons
    (M : SmtModel) (s : native_String) (d : SmtDatatype) (i : native_Nat)
    (xs : List SmtTerm) (x : SmtTerm) :
    __smtx_model_eval M
        (SmtTerm.Apply (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) x) =
      __smtx_model_eval_apply M
        (__smtx_model_eval M
          (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs))
        (__smtx_model_eval M x) := by
  cases xs with
  | nil =>
      simp [mkDtSmtAppSpineRev, __smtx_model_eval]
  | cons y ys =>
      simp [mkDtSmtAppSpineRev, __smtx_model_eval]

private theorem smtx_model_eval_mkDtSmtAppSpineRev_dtcons
    (M : SmtModel) (s : native_String) (d : SmtDatatype) (i : native_Nat) :
    ∀ xs : List SmtTerm,
      (∀ x ∈ xs, __smtx_model_eval M x ≠ SmtValue.NotValue) ->
      __smtx_model_eval M
          (mkDtSmtAppSpineRev (SmtTerm.DtCons s d i) xs) =
        mkDtSmtValueSpineRev (SmtValue.DtCons s d i)
          (xs.map (__smtx_model_eval M))
  | [], _hArgs => by
      simp [mkDtSmtAppSpineRev, mkDtSmtValueSpineRev, __smtx_model_eval]
  | x :: xs, hArgs => by
      have hx : __smtx_model_eval M x ≠ SmtValue.NotValue :=
        hArgs x (by simp)
      have hxs :
          ∀ y ∈ xs, __smtx_model_eval M y ≠ SmtValue.NotValue := by
        intro y hy
        exact hArgs y (List.mem_cons_of_mem x hy)
      have hRec :=
        smtx_model_eval_mkDtSmtAppSpineRev_dtcons M s d i xs hxs
      simp only [mkDtSmtAppSpineRev, mkDtSmtValueSpineRev, List.map]
      rw [smtx_model_eval_apply_mkDtSmtAppSpineRev_dtcons M s d i xs x]
      rw [hRec]
      exact model_eval_apply_mkDtSmtValueSpineRev_dtcons_of_arg_ne_notvalue
        M s d i (xs.map (__smtx_model_eval M)) (__smtx_model_eval M x) hx

private theorem smt_model_eval_ne_notvalue_of_non_none
    (M : SmtModel) (hM : model_total_typed M) (x : SmtTerm) :
    __smtx_typeof x ≠ SmtType.None ->
    __smtx_model_eval M x ≠ SmtValue.NotValue := by
  intro hNN hEval
  have hPres := smt_model_eval_preserves_type_of_non_none M hM x hNN
  have hNone : __smtx_typeof_value (__smtx_model_eval M x) = SmtType.None := by
    simp [hEval, __smtx_typeof_value]
  rw [hPres] at hNone
  exact hNN hNone

private theorem dt_num_sels_eq_length_of_mkDtSmtValueSpineRev_datatype
    {s : native_String} {d : SmtDatatype} {i : native_Nat}
    {xs : List SmtValue}
    (hTy :
      __smtx_typeof_value
          (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) =
        SmtType.Datatype s d) :
    __smtx_dt_num_sels d i = xs.length := by
  have hCountSub :
      vsm_num_apply_args
          (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) =
        __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
    exact vsm_num_apply_args_eq_dt_num_sels_of_datatype
      (v := mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs)
      (vsm_apply_head_mkDtSmtValueSpineRev_dtcons s d i xs) hTy
  have hCount :
      vsm_num_apply_args
          (mkDtSmtValueSpineRev (SmtValue.DtCons s d i) xs) =
        __smtx_dt_num_sels d i := by
    rw [dt_num_sels_substitute s d d i] at hCountSub
    exact hCountSub
  rw [vsm_num_apply_args_mkDtSmtValueSpineRev_dtcons s d i xs] at hCount
  exact hCount.symm

private theorem dt_sel_appHead_dtcons_eval_rel
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i j : native_Nat)
    (t ti : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i j) t)) ti) ->
    appHead t = Term.DtCons s d i ->
    mkDtCollapseSelectorGuard (Term.DtSel s d i j) t = ti ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt
        (Term.Apply (Term.DtSel s d i j) t)))
      (__smtx_model_eval M (__eo_to_smt ti)) := by
  intro hBool hHead hGuard
  let D := __eo_to_smt_datatype d
  let X := __eo_to_smt t
  let xs := (dtAppSpineRev t).2.map __eo_to_smt
  let vals := xs.map (__smtx_model_eval M)
  have hTypes := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    (Term.Apply (Term.DtSel s d i j) t) ti hBool
  have hLeftNN :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.DtSel s d i j) t)) ≠
        SmtType.None := hTypes.2
  have hTiTrans : RuleProofs.eo_has_smt_translation ti := by
    unfold RuleProofs.eo_has_smt_translation
    rw [← hTypes.1]
    exact hTypes.2
  have hTiNe : ti ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ti hTiTrans
  have hGet :
      listGetOption (appArgs t) j = some ti :=
    dt_collapse_selector_guard_get_arg_of_appHead_dtcons
      s d i j t ti hHead hGuard hTiNe
  cases hReserved : TranslationProofs.__eo_reserved_datatype_name s
  · have hLeftTranslate :
        __eo_to_smt (Term.Apply (Term.DtSel s d i j) t) =
          SmtTerm.Apply (SmtTerm.DtSel s D i j) X := by
      simp [eo_to_smt_apply_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_sel, D, X, native_ite,
        hReserved]
    have hApplyNN :
        term_has_non_none_type (SmtTerm.Apply (SmtTerm.DtSel s D i j) X) := by
      unfold term_has_non_none_type
      rw [← hLeftTranslate]
      exact hLeftNN
    have hArgTy : __smtx_typeof X = SmtType.Datatype s D :=
      dt_sel_arg_datatype_of_non_none hApplyNN
    have hHeadSpine :
        (dtAppSpineRev t).1 = Term.DtCons s d i := by
      rw [dtAppSpineRev_head_eq_appHead, hHead]
    have hTTranslate :
        X = mkDtSmtAppSpineRev (SmtTerm.DtCons s D i) xs := by
      have h := eo_to_smt_dtAppSpineRev_dtcons s d i t hHeadSpine
      simpa [X, xs, D, TranslationProofs.eo_to_smt_term_dt_cons,
        native_ite, hReserved] using h
    have hTNN : __smtx_typeof X ≠ SmtType.None := by
      rw [hArgTy]
      simp
    have hSpineNN :
        __smtx_typeof
            (mkDtSmtAppSpineRev (SmtTerm.DtCons s D i) xs) ≠
          SmtType.None := by
      rw [← hTTranslate]
      exact hTNN
    have hArgsNN :
        ∀ x ∈ xs, __smtx_model_eval M x ≠ SmtValue.NotValue := by
      intro x hx
      exact smt_model_eval_ne_notvalue_of_non_none M hM x
        (mkDtSmtAppSpineRev_args_non_none_of_non_none_type
          s D i xs hSpineNN x hx)
    have hEvalT :
        __smtx_model_eval M X =
          mkDtSmtValueSpineRev (SmtValue.DtCons s D i) vals := by
      rw [hTTranslate]
      exact smtx_model_eval_mkDtSmtAppSpineRev_dtcons M s D i xs hArgsNN
    have hConsValTy :
        __smtx_typeof_value
            (mkDtSmtValueSpineRev (SmtValue.DtCons s D i) vals) =
          SmtType.Datatype s D := by
      rw [← hEvalT]
      have hPres := smt_model_eval_preserves_type_of_non_none M hM X hTNN
      rw [hPres, hArgTy]
    have hNumVals :
        __smtx_dt_num_sels D i = vals.length :=
      dt_num_sels_eq_length_of_mkDtSmtValueSpineRev_datatype hConsValTy
    have hValsLen : vals.length = (appArgs t).length := by
      simp [vals, xs, dtAppSpineRev_args_eq_reverse_appArgs t]
    have hNumArgs :
        __smtx_dt_num_sels D i = (appArgs t).length :=
      hNumVals.trans hValsLen
    have hValsEq :
        vals =
          (appArgs t).reverse.map
            (fun x => __smtx_model_eval M (__eo_to_smt x)) := by
      simp [vals, xs, dtAppSpineRev_args_eq_reverse_appArgs t,
        List.map_map]
    have hArgNth :
        __vsm_apply_arg_nth
            (mkDtSmtValueSpineRev (SmtValue.DtCons s D i) vals)
            j (__smtx_dt_num_sels D i) =
          __smtx_model_eval M (__eo_to_smt ti) := by
      rw [hNumArgs, hValsEq]
      exact vsm_apply_arg_nth_mkDtSmtValueSpineRev_reverse_map_get? M
        (SmtValue.DtCons s D i) (appArgs t) j ti hGet
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hLeftTranslate]
    simp [__smtx_model_eval]
    unfold __smtx_model_eval_dt_sel
    rw [hEvalT]
    have hHeadTrue :
        native_veq
            (__vsm_apply_head
              (mkDtSmtValueSpineRev (SmtValue.DtCons s D i) vals))
            (SmtValue.DtCons s D i) = true := by
      simp [vsm_apply_head_mkDtSmtValueSpineRev_dtcons, native_veq]
    simp [native_ite, hHeadTrue]
    rw [hArgNth]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt ti)))
  · exfalso
    apply hLeftNN
    have hTranslateNone :
        __eo_to_smt (Term.Apply (Term.DtSel s d i j) t) =
          SmtTerm.Apply SmtTerm.None X := by
      simp [eo_to_smt_apply_dt_sel,
        TranslationProofs.eo_to_smt_term_dt_sel, X, native_ite,
        hReserved]
    rw [hTranslateNone]
    exact TranslationProofs.typeof_apply_none_eq X

private theorem dt_collapse_selector_dt_sel_appHead_dtcons_sound
    (M : SmtModel) (hM : model_total_typed M)
    (s : native_String) (d : Datatype) (i j : native_Nat)
    (t ti : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i j) t)) ti) ->
    appHead t = Term.DtCons s d i ->
    mkDtCollapseSelectorGuard (Term.DtSel s d i j) t = ti ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.DtSel s d i j) t)) ti) true := by
  intro hBool hHead hGuard
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hBool
  · exact dt_sel_appHead_dtcons_eval_rel M hM s d i j t ti
      hBool hHead hGuard

private theorem tuple_select_translation_of_non_none
    (idx t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t)) ≠
      SmtType.None ->
    ∃ (d : SmtDatatype) (n : native_Int),
      __smtx_typeof (__eo_to_smt t) = SmtType.Datatype "@Tuple" d ∧
        __eo_to_smt idx = SmtTerm.Numeral n ∧
          native_zleq 0 n = true ∧
            __eo_to_smt
                (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t) =
              SmtTerm.Apply
                (SmtTerm.DtSel "@Tuple" d native_nat_zero
                  (native_int_to_nat n))
                (__eo_to_smt t) := by
  intro hNN
  change
    __smtx_typeof
        (__eo_to_smt_tuple_select
          (__smtx_typeof (__eo_to_smt t)) (__eo_to_smt idx)
          (__eo_to_smt t)) ≠
      SmtType.None at hNN
  cases hTy : __smtx_typeof (__eo_to_smt t) with
  | Datatype s d =>
      by_cases hs : s = "@Tuple"
      · subst s
        cases hIdx : __eo_to_smt idx with
        | Numeral n =>
            cases hNonneg : native_zleq 0 n
            · exfalso
              apply hNN
              simp [__eo_to_smt_tuple_select, hTy, hIdx, hNonneg,
                native_ite]
            · refine ⟨d, n, rfl, rfl, hNonneg, ?_⟩
              change
                __eo_to_smt_tuple_select
                    (__smtx_typeof (__eo_to_smt t)) (__eo_to_smt idx)
                    (__eo_to_smt t) =
                  SmtTerm.Apply
                    (SmtTerm.DtSel "@Tuple" d native_nat_zero
                      (native_int_to_nat n))
                    (__eo_to_smt t)
              simp [__eo_to_smt_tuple_select, hTy, hIdx, hNonneg,
                native_ite]
        | _ =>
            exfalso
            apply hNN
            simp [__eo_to_smt_tuple_select, hTy, hIdx]
      · exfalso
        apply hNN
        simp [__eo_to_smt_tuple_select, hTy, hs]
  | _ =>
      exfalso
      apply hNN
      simp [__eo_to_smt_tuple_select, hTy]

private theorem tuple_select_translation_of_non_none_nat
    (idx t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t)) ≠
      SmtType.None ->
    ∃ (d : SmtDatatype) (j : native_Nat),
      __smtx_typeof (__eo_to_smt t) = SmtType.Datatype "@Tuple" d ∧
        idx = Term.Numeral j ∧
          __eo_to_smt
              (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t) =
            SmtTerm.Apply
              (SmtTerm.DtSel "@Tuple" d native_nat_zero j)
              (__eo_to_smt t) := by
  intro hNN
  rcases tuple_select_translation_of_non_none idx t hNN with
    ⟨d, n, hTy, hIdx, hNonneg, hTranslate⟩
  have hIdxTerm : idx = Term.Numeral n :=
    TranslationProofs.eo_to_smt_eq_numeral idx n hIdx
  have hnNonneg : (0 : Int) ≤ n := by
    simpa [native_zleq, SmtEval.native_zleq] using hNonneg
  refine ⟨d, native_int_to_nat n, hTy, ?_, ?_⟩
  · rw [hIdxTerm]
    congr
    simp [native_int_to_nat, SmtEval.native_int_to_nat,
      Int.toNat_of_nonneg hnNonneg]
  · simpa using hTranslate

private theorem tuple_select_eval_hits_tuple_constructor
    (M : SmtModel) (idx t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t)) ≠
      SmtType.None ->
    ∃ (d : SmtDatatype) (n : native_Int),
      __smtx_model_eval M
          (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t)) =
        __smtx_model_eval_dt_sel M "@Tuple" d native_nat_zero
          (native_int_to_nat n)
          (__smtx_model_eval M (__eo_to_smt t)) := by
  intro hNN
  rcases tuple_select_translation_of_non_none idx t hNN with
    ⟨d, n, _hTy, _hIdx, _hNonneg, hTranslate⟩
  refine ⟨d, n, ?_⟩
  rw [hTranslate]
  simp [__smtx_model_eval]

private theorem tuple_select_eval_hits_tuple_constructor_nat
    (M : SmtModel) (idx t : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t)) ≠
      SmtType.None ->
    ∃ (d : SmtDatatype) (j : native_Nat),
      idx = Term.Numeral j ∧
        __smtx_model_eval M
            (__eo_to_smt (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t)) =
          __smtx_model_eval_dt_sel M "@Tuple" d native_nat_zero j
            (__smtx_model_eval M (__eo_to_smt t)) := by
  intro hNN
  rcases tuple_select_translation_of_non_none_nat idx t hNN with
    ⟨d, j, _hTy, hIdx, hTranslate⟩
  refine ⟨d, j, hIdx, ?_⟩
  rw [hTranslate]
  simp [__smtx_model_eval]

private theorem dt_collapse_selector_guard_ne_stuck_of_has_bool_type
    (s t ti : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply s t)) ti) ->
    mkDtCollapseSelectorGuard s t = ti ->
    mkDtCollapseSelectorGuard s t ≠ Term.Stuck := by
  intro hBool hGuard hStuck
  have hTypes := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    (Term.Apply s t) ti hBool
  have hTiTrans : RuleProofs.eo_has_smt_translation ti := by
    unfold RuleProofs.eo_has_smt_translation
    rw [← hTypes.1]
    exact hTypes.2
  have hTiNe : ti ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation ti hTiTrans
  exact hTiNe (hGuard.symm.trans hStuck)

private theorem tuple_select_index_nat_of_collapse_hypotheses
    (idx t ti : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t)) ti) ->
    ∃ (d : SmtDatatype) (j : native_Nat),
      __smtx_typeof (__eo_to_smt t) = SmtType.Datatype "@Tuple" d ∧
        idx = Term.Numeral j ∧
          __eo_to_smt
              (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t) =
            SmtTerm.Apply
              (SmtTerm.DtSel "@Tuple" d native_nat_zero j)
              (__eo_to_smt t) := by
  intro hBool
  have hTypes := RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
    (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t) ti hBool
  exact tuple_select_translation_of_non_none_nat idx t hTypes.2

private theorem dt_collapse_selector_tuple_select_sound
    (M : SmtModel) (hM : model_total_typed M) (idx t ti : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t)) ti) ->
    mkDtCollapseSelectorGuard (Term.UOp1 UserOp1.tuple_select idx) t = ti ->
    eo_interprets M
      (Term.Apply (Term.Apply (Term.UOp UserOp.eq)
        (Term.Apply (Term.UOp1 UserOp1.tuple_select idx) t)) ti) true := by
  intro hBool hGuard
  have hGuardNe :
      mkDtCollapseSelectorGuard (Term.UOp1 UserOp1.tuple_select idx) t ≠
        Term.Stuck :=
    dt_collapse_selector_guard_ne_stuck_of_has_bool_type
      (Term.UOp1 UserOp1.tuple_select idx) t ti hBool hGuard
  rcases tuple_select_index_nat_of_collapse_hypotheses idx t ti hBool with
    ⟨d, j, hTy, hIdx, hTranslate⟩
  -- Remaining tuple-specific obligation: use `hGuardNe` to recover the
  -- selected tuple argument, then show `__eo_to_smt_tuple_prepend` evaluates
  -- to the single `@Tuple` constructor spine so the selector cannot take the
  -- wrong-constructor branch.
  sorry

private theorem dt_collapse_selector_sound
    (M : SmtModel) (hM : model_total_typed M) (s t ti : Term) :
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply s t)) ti) ->
  mkDtCollapseSelectorGuard s t = ti ->
  eo_interprets M
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) (Term.Apply s t)) ti) true := by
  -- Remaining cases: tuple-selector collapse and impossible mismatched datatype
  -- selector/constructor guards.
  sorry

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
      cases hHead : appHead t with
      | DtCons ss' dd' ii' =>
          by_cases hss : ss = ss'
          · by_cases hdd : dd = dd'
            · by_cases hii : ii = ii'
              · subst ss'
                subst dd'
                subst ii'
                exact dt_collapse_selector_dt_sel_appHead_dtcons_sound
                  M hM ss dd ii jj t ti hBool hHead hGuard
              · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
            · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
          · exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
      | _ =>
          exact dt_collapse_selector_sound M hM _ _ _ hBool hGuard
  | UOp1 op idx =>
      cases op with
      | tuple_select =>
          exact dt_collapse_selector_tuple_select_sound
            M hM idx t ti hBool hGuard
      | _ =>
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
