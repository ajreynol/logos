module

public import Cpc.Proofs.RuleSupport.SequenceSupport
import all Cpc.Proofs.RuleSupport.SequenceSupport
public import Cpc.Proofs.Translation.EoTypeofCore
import all Cpc.Proofs.Translation.EoTypeofCore
public import Cpc.Proofs.Translation.Full
import all Cpc.Proofs.Translation.Full

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

attribute [local simp] native_streq native_and native_ite

private abbrev mkDtCollapseSelectorGuard (s t : Term) : Term :=
  __assoc_nil_nth Term.__eo_List_cons (__dt_arg_list t)
    (__eo_list_find Term.__eo_List_cons
      (__dt_get_selectors_of_app (__eo_typeof t) t) s)

private theorem assoc_nil_nth_nil_stuck (f n : Term) :
    __assoc_nil_nth f Term.__eo_List_nil n = Term.Stuck := by
  cases f <;> cases n <;>
    simp [__assoc_nil_nth, __eo_l_1___assoc_nil_nth]

private theorem assoc_nil_nth_index_stuck (f xs : Term) :
    __assoc_nil_nth f xs Term.Stuck = Term.Stuck := by
  cases f <;> cases xs <;>
    simp [__assoc_nil_nth]

private theorem assoc_nil_nth_list_stuck (f n : Term) :
    __assoc_nil_nth f Term.Stuck n = Term.Stuck := by
  cases f <;> cases n <;>
    simp [__assoc_nil_nth]

private def eoTermList : List Term -> Term
  | [] => Term.__eo_List_nil
  | x :: xs => Term.Apply (Term.Apply Term.__eo_List_cons x) (eoTermList xs)

private theorem eoTermList_ne_stuck :
    ∀ xs : List Term, eoTermList xs ≠ Term.Stuck
  | [] => by simp [eoTermList]
  | x :: xs => by simp [eoTermList]

private def appHead : Term -> Term
  | Term.Apply f _ => appHead f
  | t => t

private def appArgs : Term -> List Term
  | Term.Apply f x => appArgs f ++ [x]
  | _ => []

private def tupleArgs : Term -> List Term
  | Term.Apply (Term.Apply (Term.UOp UserOp.tuple) x) xs =>
      x :: tupleArgs xs
  | Term.UOp UserOp.tuple_unit => []
  | _ => []

private def isTupleValue : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.tuple) _) xs =>
      isTupleValue xs
  | Term.UOp UserOp.tuple_unit => True
  | _ => False

private theorem tuple_arg_list_eq_eoTermList_of_ne_stuck :
    ∀ (t : Term),
      __tuple_arg_list t ≠ Term.Stuck ->
      ∃ xs : List Term, isTupleValue t ∧ __tuple_arg_list t = eoTermList xs
  | Term.Apply f a, hArgs => by
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op <;> try
                simp [__tuple_arg_list] at hArgs
              case tuple =>
                have hTailNe : __tuple_arg_list a ≠ Term.Stuck := by
                  intro hTail
                  apply hArgs
                  simp [__eo_mk_apply, hTail]
                rcases tuple_arg_list_eq_eoTermList_of_ne_stuck a hTailNe with
                  ⟨xs, hTailTuple, hTailList⟩
                refine ⟨x :: xs, ?_, ?_⟩
                · simpa [isTupleValue] using hTailTuple
                · have hListNe : eoTermList xs ≠ Term.Stuck :=
                    eoTermList_ne_stuck xs
                  simp [__tuple_arg_list, hTailList, __eo_mk_apply,
                    eoTermList]
          | _ =>
              simp [__tuple_arg_list] at hArgs
      | _ =>
          simp [__tuple_arg_list] at hArgs
  | Term.UOp op, hArgs => by
      cases op <;> try
        simp [__tuple_arg_list] at hArgs
      case tuple_unit =>
        exact ⟨[], by simp [isTupleValue], by simp [__tuple_arg_list, eoTermList]⟩
  | Term.UOp1 _ _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.UOp2 _ _ _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.UOp3 _ _ _ _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.__eo_List, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.__eo_List_nil, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.__eo_List_cons, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.Bool, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.Boolean _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.Numeral _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.Rational _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.String _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.Binary _ _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.Type, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.Stuck, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.FunType, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.Var _ _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.DatatypeType _ _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.DatatypeTypeRef _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.DtcAppType _ _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.DtCons _ _ _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.DtSel _ _ _ _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.USort _, hArgs => by simp [__tuple_arg_list] at hArgs
  | Term.UConst _ _, hArgs => by simp [__tuple_arg_list] at hArgs
termination_by t hArgs => t

private theorem tuple_arg_list_tupleArgs_of_tuple_value :
    ∀ (t : Term),
      isTupleValue t ->
      __tuple_arg_list t ≠ Term.Stuck ->
      __tuple_arg_list t = eoTermList (tupleArgs t)
  | Term.Apply f tail, hTuple, hNe => by
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op <;> try simp [isTupleValue] at hTuple
              case tuple =>
                have hTailTuple : isTupleValue tail := by
                  simpa [isTupleValue] using hTuple
                have hTailNe : __tuple_arg_list tail ≠ Term.Stuck := by
                  intro hTail
                  apply hNe
                  simp [__tuple_arg_list, __eo_mk_apply, hTail]
                have hTail :=
                  tuple_arg_list_tupleArgs_of_tuple_value tail hTailTuple hTailNe
                have hListNe : eoTermList (tupleArgs tail) ≠ Term.Stuck :=
                  eoTermList_ne_stuck (tupleArgs tail)
                simp [__tuple_arg_list, hTail, __eo_mk_apply, tupleArgs, eoTermList]
          | _ =>
              simp [isTupleValue] at hTuple
      | _ =>
          simp [isTupleValue] at hTuple
  | Term.UOp op, hTuple, _hNe => by
      cases op <;> simp [isTupleValue, __tuple_arg_list, tupleArgs, eoTermList]
        at hTuple ⊢
  | Term.UOp1 _ _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.UOp2 _ _ _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.UOp3 _ _ _ _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.__eo_List, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.__eo_List_nil, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.__eo_List_cons, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.Bool, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.Boolean _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.Numeral _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.Rational _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.String _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.Binary _ _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.Type, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.Stuck, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.FunType, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.Var _ _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.DatatypeType _ _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.DatatypeTypeRef _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.DtcAppType _ _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.DtCons _ _ _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.DtSel _ _ _ _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.USort _, hTuple, _ => by simp [isTupleValue] at hTuple
  | Term.UConst _ _, hTuple, _ => by simp [isTupleValue] at hTuple
termination_by t hTuple hNe => t

private theorem dt_arg_list_eq_tuple_arg_list_of_tuple_value :
    ∀ (t : Term),
      isTupleValue t ->
      __dt_arg_list t = __tuple_arg_list t
  | Term.Apply f tail, hTuple => by
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op <;> try simp [isTupleValue] at hTuple
              case tuple =>
                rfl
          | _ =>
              simp [isTupleValue] at hTuple
      | _ =>
          simp [isTupleValue] at hTuple
  | Term.UOp op, hTuple => by
      cases op <;> simp [isTupleValue, __dt_arg_list, __tuple_arg_list,
        __get_arg_list_rec] at hTuple ⊢
  | Term.UOp1 _ _, hTuple => by simp [isTupleValue] at hTuple
  | Term.UOp2 _ _ _, hTuple => by simp [isTupleValue] at hTuple
  | Term.UOp3 _ _ _ _, hTuple => by simp [isTupleValue] at hTuple
  | Term.__eo_List, hTuple => by simp [isTupleValue] at hTuple
  | Term.__eo_List_nil, hTuple => by simp [isTupleValue] at hTuple
  | Term.__eo_List_cons, hTuple => by simp [isTupleValue] at hTuple
  | Term.Bool, hTuple => by simp [isTupleValue] at hTuple
  | Term.Boolean _, hTuple => by simp [isTupleValue] at hTuple
  | Term.Numeral _, hTuple => by simp [isTupleValue] at hTuple
  | Term.Rational _, hTuple => by simp [isTupleValue] at hTuple
  | Term.String _, hTuple => by simp [isTupleValue] at hTuple
  | Term.Binary _ _, hTuple => by simp [isTupleValue] at hTuple
  | Term.Type, hTuple => by simp [isTupleValue] at hTuple
  | Term.Stuck, hTuple => by simp [isTupleValue] at hTuple
  | Term.FunType, hTuple => by simp [isTupleValue] at hTuple
  | Term.Var _ _, hTuple => by simp [isTupleValue] at hTuple
  | Term.DatatypeType _ _, hTuple => by simp [isTupleValue] at hTuple
  | Term.DatatypeTypeRef _, hTuple => by simp [isTupleValue] at hTuple
  | Term.DtcAppType _ _, hTuple => by simp [isTupleValue] at hTuple
  | Term.DtCons _ _ _, hTuple => by simp [isTupleValue] at hTuple
  | Term.DtSel _ _ _ _, hTuple => by simp [isTupleValue] at hTuple
  | Term.USort _, hTuple => by simp [isTupleValue] at hTuple
  | Term.UConst _ _, hTuple => by simp [isTupleValue] at hTuple

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

private def tupleSelSmtArgsRev
    (d : SmtDatatype) (tail : SmtTerm) : native_Nat -> List SmtTerm
  | native_nat_zero => []
  | native_nat_succ k =>
      SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple") d native_nat_zero k) tail ::
        tupleSelSmtArgsRev d tail k

private def listGetOption : List Term -> Nat -> Option Term
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ n => listGetOption xs n

private def listGetOptionValue : List SmtValue -> Nat -> Option SmtValue
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, Nat.succ n => listGetOptionValue xs n

private theorem listGetOptionValue_append_left :
    ∀ (xs ys : List SmtValue) (j : Nat),
      j < xs.length ->
      listGetOptionValue (xs ++ ys) j = listGetOptionValue xs j
  | [], _ys, j, h => by
      exact False.elim (Nat.not_lt_zero j h)
  | _x :: xs, ys, 0, _h => by
      rfl
  | _x :: xs, ys, Nat.succ j, h => by
      have hj : j < xs.length := Nat.succ_lt_succ_iff.mp h
      exact listGetOptionValue_append_left xs ys j hj

private theorem listGetOptionValue_append_right :
    ∀ (xs ys : List SmtValue) (j : Nat),
      listGetOptionValue (xs ++ ys) (xs.length + j) =
        listGetOptionValue ys j
  | [], ys, j => by
      simp
  | _x :: xs, ys, j => by
      simpa [listGetOptionValue, Nat.succ_add] using
        listGetOptionValue_append_right xs ys j

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
      simp [mkDtSmtValueSpineRev, vsm_num_apply_args_dt_cons]
  | x :: xs => by
      simp [mkDtSmtValueSpineRev, vsm_num_apply_args_apply,
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

private theorem mkDtSmtAppSpineRev_append_singleton
    (head x : SmtTerm) :
    ∀ xs : List SmtTerm,
      mkDtSmtAppSpineRev head (xs ++ [x]) =
        mkDtSmtAppSpineRev (SmtTerm.Apply head x) xs
  | [] => by
      simp [mkDtSmtAppSpineRev]
  | y :: ys => by
      simp [mkDtSmtAppSpineRev,
        mkDtSmtAppSpineRev_append_singleton head x ys]

private theorem eo_to_smt_tuple_prepend_rec_eq_spine
    (tailD : SmtDatatype) (tail acc : SmtTerm) :
    ∀ k : native_Nat,
      __eo_to_smt_tuple_prepend_rec tailD tail k acc =
        mkDtSmtAppSpineRev acc (tupleSelSmtArgsRev tailD tail k)
  | native_nat_zero => by
      simp [__eo_to_smt_tuple_prepend_rec, tupleSelSmtArgsRev,
        mkDtSmtAppSpineRev]
  | native_nat_succ k => by
      simp [__eo_to_smt_tuple_prepend_rec, tupleSelSmtArgsRev,
        mkDtSmtAppSpineRev,
        eo_to_smt_tuple_prepend_rec_eq_spine tailD tail acc k]

private theorem eo_to_smt_tuple_prepend_rec_eq_dtcons_spine
    (fullD tailD : SmtDatatype) (tail head : SmtTerm) :
    ∀ k : native_Nat,
      __eo_to_smt_tuple_prepend_rec tailD tail k
          (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
            head) =
        mkDtSmtAppSpineRev
          (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
          (tupleSelSmtArgsRev tailD tail k ++ [head])
  | k => by
      rw [eo_to_smt_tuple_prepend_rec_eq_spine]
      exact (mkDtSmtAppSpineRev_append_singleton
        (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero) head
        (tupleSelSmtArgsRev tailD tail k)).symm

private theorem tupleSelSmtArgsRev_length
    (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ k : native_Nat,
      (tupleSelSmtArgsRev tailD tail k).length = k
  | native_nat_zero => by
      simp [tupleSelSmtArgsRev]
  | native_nat_succ k => by
      simp [tupleSelSmtArgsRev,
        tupleSelSmtArgsRev_length tailD tail k]

private theorem tupleSelSmtArgsRev_reverse_map_get_of_lt
    (M : SmtModel) (tailD : SmtDatatype) (tail : SmtTerm) :
    ∀ (k j : native_Nat),
      j < k ->
      listGetOptionValue
          ((tupleSelSmtArgsRev tailD tail k).reverse.map
            (__smtx_model_eval M))
          j =
        some
          (__smtx_model_eval M
            (SmtTerm.Apply
              (SmtTerm.DtSel (native_string_lit "@Tuple") tailD native_nat_zero j) tail))
  | native_nat_zero, j, h => by
      exact False.elim (Nat.not_lt_zero j h)
  | native_nat_succ k, j, h => by
      let xs :=
        (tupleSelSmtArgsRev tailD tail k).reverse.map
          (__smtx_model_eval M)
      let last :=
        __smtx_model_eval M
          (SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple") tailD native_nat_zero k)
            tail)
      have hList :
          (tupleSelSmtArgsRev tailD tail (Nat.succ k)).reverse.map
              (__smtx_model_eval M) =
            xs ++ [last] := by
        simp [xs, last, tupleSelSmtArgsRev, List.map_append]
      by_cases hj : j < k
      · have hLeft :
            listGetOptionValue (xs ++ [last]) j =
              listGetOptionValue xs j := by
          have hLen : xs.length = k := by
            simp [xs, tupleSelSmtArgsRev_length]
          exact listGetOptionValue_append_left xs [last] j
            (by simpa [hLen] using hj)
        rw [hList, hLeft]
        exact tupleSelSmtArgsRev_reverse_map_get_of_lt M tailD tail k j hj
      · have hjEq : j = k := Nat.eq_of_lt_succ_of_not_lt h hj
        subst j
        have hRight :
            listGetOptionValue (xs ++ [last]) (xs.length + 0) =
              listGetOptionValue [last] 0 :=
          listGetOptionValue_append_right xs [last] 0
        have hLen : xs.length = k := by
          simp [xs, tupleSelSmtArgsRev_length]
        rw [hList]
        simpa [hLen, last, listGetOptionValue] using hRight

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

private theorem vsm_apply_arg_nth_mkDtSmtValueSpineRev_reverse_get?
    (head : SmtValue) :
    ∀ (xs : List SmtValue) (j : Nat) (v : SmtValue),
      listGetOptionValue xs j = some v ->
      __vsm_apply_arg_nth
          (mkDtSmtValueSpineRev head xs.reverse) j xs.length = v
  | [], j, v, h => by
      cases j <;> simp [listGetOptionValue] at h
  | x :: xs, Nat.zero, v, h => by
      simp [listGetOptionValue] at h
      subst v
      rw [List.reverse_cons]
      rw [mkDtSmtValueSpineRev_append_singleton]
      simpa [List.length_reverse] using
        vsm_apply_arg_nth_mkDtSmtValueSpineRev_head_arg head x
          xs.reverse
  | x :: xs, Nat.succ j, v, h => by
      have hRec :=
        vsm_apply_arg_nth_mkDtSmtValueSpineRev_reverse_get? head
          xs j v (by simpa [listGetOptionValue] using h)
      have hRecLen :
          __vsm_apply_arg_nth (mkDtSmtValueSpineRev head xs.reverse)
              j xs.reverse.length = v := by
        simpa [List.length_reverse] using hRec
      rw [List.reverse_cons]
      rw [mkDtSmtValueSpineRev_append_singleton]
      simpa [List.length_reverse] using
        (vsm_apply_arg_nth_mkDtSmtValueSpineRev_succ head x xs.reverse j).trans
          hRecLen

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
  | Term.UOp _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.UOp1 _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.UOp2 _ _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.UOp3 _ _ _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.__eo_List, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.__eo_List_nil, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.__eo_List_cons, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.Bool, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.Boolean _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.Numeral _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.Rational _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.String _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.Binary _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.Type, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.Stuck, xs, hHead => by simp [appHead] at hHead
  | Term.FunType, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.Var _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.DatatypeType _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.DatatypeTypeRef _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.DtcAppType _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.DtCons _ _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.DtSel _ _ _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.USort _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
  | Term.UConst _ _, xs, _ => by cases xs <;> simp [appArgs, __get_arg_list_rec, eoTermList]
termination_by t xs hHead => t

private theorem get_arg_list_rec_stuck_of_appHead_stuck :
    ∀ (t acc : Term),
      appHead t = Term.Stuck ->
      __get_arg_list_rec t acc = Term.Stuck
  | Term.Apply f x, acc, hHead => by
      have hRec :=
        get_arg_list_rec_stuck_of_appHead_stuck f
          (Term.Apply (Term.Apply Term.__eo_List_cons x) acc) hHead
      cases acc <;> simp [__get_arg_list_rec] at hRec ⊢
      all_goals exact hRec
  | Term.UOp _, acc, hHead => by simp [appHead] at hHead
  | Term.UOp1 _ _, acc, hHead => by simp [appHead] at hHead
  | Term.UOp2 _ _ _, acc, hHead => by simp [appHead] at hHead
  | Term.UOp3 _ _ _ _, acc, hHead => by simp [appHead] at hHead
  | Term.__eo_List, acc, hHead => by simp [appHead] at hHead
  | Term.__eo_List_nil, acc, hHead => by simp [appHead] at hHead
  | Term.__eo_List_cons, acc, hHead => by simp [appHead] at hHead
  | Term.Bool, acc, hHead => by simp [appHead] at hHead
  | Term.Boolean _, acc, hHead => by simp [appHead] at hHead
  | Term.Numeral _, acc, hHead => by simp [appHead] at hHead
  | Term.Rational _, acc, hHead => by simp [appHead] at hHead
  | Term.String _, acc, hHead => by simp [appHead] at hHead
  | Term.Binary _ _, acc, hHead => by simp [appHead] at hHead
  | Term.Type, acc, hHead => by simp [appHead] at hHead
  | Term.Stuck, acc, _ => by simp [__get_arg_list_rec]
  | Term.FunType, acc, hHead => by simp [appHead] at hHead
  | Term.Var _ _, acc, hHead => by simp [appHead] at hHead
  | Term.DatatypeType _ _, acc, hHead => by simp [appHead] at hHead
  | Term.DatatypeTypeRef _, acc, hHead => by simp [appHead] at hHead
  | Term.DtcAppType _ _, acc, hHead => by simp [appHead] at hHead
  | Term.DtCons _ _ _, acc, hHead => by simp [appHead] at hHead
  | Term.DtSel _ _ _ _, acc, hHead => by simp [appHead] at hHead
  | Term.USort _, acc, hHead => by simp [appHead] at hHead
  | Term.UConst _ _, acc, hHead => by simp [appHead] at hHead
termination_by t acc hHead => t

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
          simp [__assoc_nil_nth, __eo_eq, native_ite,
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

private theorem assoc_nil_nth_cons_succ_any
    (x tailArgs : Term) (n : Nat) :
    __assoc_nil_nth Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) tailArgs)
        (Term.Numeral (Nat.succ n)) =
      __assoc_nil_nth Term.__eo_List_cons tailArgs
        (Term.Numeral n) := by
  calc
    __assoc_nil_nth Term.__eo_List_cons
        (Term.Apply (Term.Apply Term.__eo_List_cons x) tailArgs)
        (Term.Numeral (Nat.succ n)) =
        __eo_l_1___assoc_nil_nth Term.__eo_List_cons
          (Term.Apply (Term.Apply Term.__eo_List_cons x) tailArgs)
          (Term.Numeral (Nat.succ n)) := by
      apply __assoc_nil_nth.eq_5
      · intro h
        cases h
      · intro h
        cases h
      · intro h
        cases h
      · intro _f _x1 _x2 _hList hZero
        exact term_num_nat_succ_ne_zero n hZero
    _ =
        __eo_requires (__eo_eq Term.__eo_List_cons Term.__eo_List_cons)
          (Term.Boolean true)
          (__assoc_nil_nth Term.__eo_List_cons tailArgs
            (__eo_add (Term.Numeral (Nat.succ n))
              (Term.Numeral (-1 : native_Int)))) := by
      simpa using
        (__eo_l_1___assoc_nil_nth.eq_3 Term.__eo_List_cons
          (Term.Numeral (Nat.succ n)) Term.__eo_List_cons x tailArgs
          (by intro h; cases h) (by intro h; cases h))
    _ =
        __assoc_nil_nth Term.__eo_List_cons tailArgs
          (__eo_add (Term.Numeral (Nat.succ n))
            (Term.Numeral (-1 : native_Int))) := by
      simp [__eo_requires, __eo_eq, native_ite, native_teq, native_not,
        SmtEval.native_not]
    _ =
        __assoc_nil_nth Term.__eo_List_cons tailArgs
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

private theorem dt_get_selectors_of_app_eq_appHead :
    ∀ (T t : Term),
      __dt_get_selectors_of_app T t = __dt_get_selectors T (appHead t)
  | T, Term.Apply f x => by
      cases T <;> simp [__dt_get_selectors_of_app, appHead]
      all_goals first
        | exact dt_get_selectors_of_app_eq_appHead _ f
        | cases h : appHead f <;> simp [__dt_get_selectors]
  | T, Term.UOp _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.UOp1 _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.UOp2 _ _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.UOp3 _ _ _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.__eo_List => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.__eo_List_nil => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.__eo_List_cons => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.Bool => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.Boolean _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.Numeral _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.Rational _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.String _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.Binary _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.Type => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.Stuck => by
      cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.FunType => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.Var _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.DatatypeType _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.DatatypeTypeRef _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.DtcAppType _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.DtCons _ _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.DtSel _ _ _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.USort _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
  | T, Term.UConst _ _ => by cases T <;> simp [__dt_get_selectors_of_app, __dt_get_selectors, appHead]
termination_by T t => t

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

private theorem eo_eq_eq_false_of_ne {x y : Term} :
    x ≠ y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean false := by
  intro hNe hX hY
  by_cases hEq : x = y
  · exact False.elim (hNe hEq)
  · cases x <;> cases y <;>
      simp [__eo_eq, native_teq, eq_comm, hEq] at hNe hX hY ⊢ <;>
        contradiction

private theorem eo_list_find_rec_target_stuck (xs start : Term) :
    __eo_list_find_rec xs Term.Stuck start = Term.Stuck := by
  cases xs <;> simp [__eo_list_find_rec]

private theorem eo_list_find_rec_start_stuck (xs target : Term) :
    __eo_list_find_rec xs target Term.Stuck = Term.Stuck := by
  cases xs <;> cases target <;> simp [__eo_list_find_rec]

private theorem eo_list_find_rec_cons_ne_eq_tail
    (x xs target start : Term) :
    x ≠ target ->
    x ≠ Term.Stuck ->
    __eo_list_find_rec
        (Term.Apply (Term.Apply Term.__eo_List_cons x) xs) target start =
      __eo_list_find_rec xs target (__eo_add start (Term.Numeral 1)) := by
  intro hNe hx
  by_cases hTarget : target = Term.Stuck
  · subst target
    cases start <;>
      simp [__eo_list_find_rec, __eo_add, eo_list_find_rec_target_stuck]
  · have hEqFalse : __eo_eq x target = Term.Boolean false :=
      eo_eq_eq_false_of_ne hNe hx hTarget
    cases start <;>
      simp [__eo_list_find_rec, __eo_ite, __eo_add, hEqFalse, native_teq,
        eo_list_find_rec_start_stuck]

private theorem datatype_cons_selectors_rec_ctor_ne_stuck
    (s : native_String) (d : Datatype) (i : native_Nat) :
    ∀ (c : DatatypeCons) (rest : Datatype) (ai : native_Nat),
      __eo_datatype_cons_selectors_rec s d i (Datatype.sum c rest)
          native_nat_zero ai ≠
        Term.Stuck
  | DatatypeCons.unit, rest, ai => by
      simp [__eo_datatype_cons_selectors_rec]
  | DatatypeCons.cons U c, rest, ai => by
      have hTail :
          __eo_datatype_cons_selectors_rec s d i (Datatype.sum c rest)
              native_nat_zero (native_nat_succ ai) ≠
            Term.Stuck :=
        datatype_cons_selectors_rec_ctor_ne_stuck s d i c rest
          (native_nat_succ ai)
      simp [__eo_datatype_cons_selectors_rec, __eo_mk_apply]

private theorem datatype_cons_selectors_rec_ctor_is_list_true
    (s : native_String) (d : Datatype) (i : native_Nat) :
    ∀ (c : DatatypeCons) (rest : Datatype) (ai : native_Nat),
      __eo_is_list Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i (Datatype.sum c rest)
            native_nat_zero ai) =
        Term.Boolean true
  | DatatypeCons.unit, rest, ai => by
      simp [__eo_datatype_cons_selectors_rec, __eo_is_list,
        __eo_get_nil_rec, __eo_is_list_nil, __eo_is_ok, __eo_requires,
        native_ite, native_teq, native_not, SmtEval.native_not]
  | DatatypeCons.cons U c, rest, ai => by
      let tail :=
        __eo_datatype_cons_selectors_rec s d i (Datatype.sum c rest)
          native_nat_zero (native_nat_succ ai)
      have hTailNe : tail ≠ Term.Stuck := by
        dsimp [tail]
        exact datatype_cons_selectors_rec_ctor_ne_stuck s d i c rest
          (native_nat_succ ai)
      have hTailList :
          __eo_is_list Term.__eo_List_cons tail = Term.Boolean true := by
        dsimp [tail]
        exact datatype_cons_selectors_rec_ctor_is_list_true s d i c rest
          (native_nat_succ ai)
      simpa [tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply,
        hTailNe] using
        eo_is_list_cons_self_true_of_tail_list Term.__eo_List_cons
          (Term.DtSel s d i ai) tail (by simp) hTailList

private theorem datatype_cons_selectors_rec_is_list_true_of_smt_bound
    (s : native_String) (d : Datatype) (i : native_Nat) :
    ∀ (rest : Datatype) (ci ai j : native_Nat),
      ai ≤ j ->
      j < ai + __smtx_dt_num_sels (__eo_to_smt_datatype rest) ci ->
      __eo_is_list Term.__eo_List_cons
          (__eo_datatype_cons_selectors_rec s d i rest ci ai) =
        Term.Boolean true
  | Datatype.null, ci, ai, j, hLe, hLt => by
      exact False.elim
        ((Nat.not_lt_of_ge hLe) (by
          simpa [__eo_to_smt_datatype, __smtx_dt_num_sels] using hLt))
  | Datatype.sum DatatypeCons.unit restTail, Nat.zero, ai, j, hLe, hLt => by
      exact False.elim
        ((Nat.not_lt_of_ge hLe) (by
          simpa [__eo_to_smt_datatype, __eo_to_smt_datatype_cons,
            __smtx_dt_num_sels, __smtx_dtc_num_sels] using hLt))
  | Datatype.sum (DatatypeCons.cons U c) restTail, Nat.zero, ai, j, _hLe,
      _hLt => by
      exact datatype_cons_selectors_rec_ctor_is_list_true s d i
        (DatatypeCons.cons U c) restTail ai
  | Datatype.sum c restTail, Nat.succ ci, ai, j, hLe, hLt => by
      simpa [__eo_datatype_cons_selectors_rec, __eo_to_smt_datatype,
        __smtx_dt_num_sels] using
        datatype_cons_selectors_rec_is_list_true_of_smt_bound
          s d i restTail ci ai j hLe hLt

private theorem datatype_cons_selectors_rec_find_rec_eq_index_of_smt_bound
    (s : native_String) (d : Datatype) (i : native_Nat) :
    ∀ (rest : Datatype) (ci ai j : native_Nat),
      ai ≤ j ->
      j < ai + __smtx_dt_num_sels (__eo_to_smt_datatype rest) ci ->
      __eo_list_find_rec
          (__eo_datatype_cons_selectors_rec s d i rest ci ai)
          (Term.DtSel s d i j) (Term.Numeral ai) =
        Term.Numeral j
  | Datatype.null, ci, ai, j, hLe, hLt => by
      exact False.elim
        ((Nat.not_lt_of_ge hLe) (by
          simpa [__eo_to_smt_datatype, __smtx_dt_num_sels] using hLt))
  | Datatype.sum DatatypeCons.unit restTail, Nat.zero, ai, j, hLe, hLt => by
      exact False.elim
        ((Nat.not_lt_of_ge hLe) (by
          simpa [__eo_to_smt_datatype, __eo_to_smt_datatype_cons,
            __smtx_dt_num_sels, __smtx_dtc_num_sels] using hLt))
  | Datatype.sum (DatatypeCons.cons U c) restTail, Nat.zero, ai, j, hLe,
      hLt => by
      let target := Term.DtSel s d i j
      let current := Term.DtSel s d i ai
      let tail :=
        __eo_datatype_cons_selectors_rec s d i (Datatype.sum c restTail)
          native_nat_zero (native_nat_succ ai)
      have hTail : tail ≠ Term.Stuck := by
        exact datatype_cons_selectors_rec_ctor_ne_stuck s d i c restTail
          (native_nat_succ ai)
      have hList :
          __eo_datatype_cons_selectors_rec s d i
              (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero ai =
            Term.Apply (Term.Apply Term.__eo_List_cons current) tail := by
        simp [current, tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply]
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
      · have hCurrentTarget : current ≠ target := by
          intro h
          simp [current, target] at h
          exact hEq h.symm
        have hStep :
            __eo_list_find_rec
                (Term.Apply (Term.Apply Term.__eo_List_cons current) tail)
                target (Term.Numeral ai) =
              __eo_list_find_rec tail target (Term.Numeral (Nat.succ ai)) := by
          simp [current, target, __eo_list_find_rec, __eo_eq, __eo_add,
            native_ite, native_teq, native_zplus, hEq]
        have hLeTail : Nat.succ ai ≤ j := by
          exact Nat.succ_le_of_lt
            (Nat.lt_of_le_of_ne hLe (by
              intro h
              exact hEq h.symm))
        have hLtTail :
            j <
              Nat.succ ai +
                __smtx_dt_num_sels
                  (__eo_to_smt_datatype (Datatype.sum c restTail))
                  native_nat_zero := by
          simpa [__eo_to_smt_datatype, __eo_to_smt_datatype_cons,
            __smtx_dt_num_sels,
            __smtx_dtc_num_sels, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hLt
        have hTailFind :
            __eo_list_find_rec tail target (Term.Numeral (Nat.succ ai)) =
              Term.Numeral j := by
          simpa [target, tail] using
            datatype_cons_selectors_rec_find_rec_eq_index_of_smt_bound
              s d i (Datatype.sum c restTail) native_nat_zero
              (Nat.succ ai) j hLeTail hLtTail
        rw [hList]
        exact hStep.trans hTailFind
  | Datatype.sum c restTail, Nat.succ ci, ai, j, hLe, hLt => by
      simpa [__eo_datatype_cons_selectors_rec, __eo_to_smt_datatype,
        __smtx_dt_num_sels] using
        datatype_cons_selectors_rec_find_rec_eq_index_of_smt_bound
          s d i restTail ci ai j hLe hLt

private theorem datatype_cons_selectors_rec_find_eq_index_of_smt_bound
    (s : native_String) (d : Datatype) (i j : native_Nat) :
    j < __smtx_dt_num_sels (__eo_to_smt_datatype d) i ->
    __eo_list_find Term.__eo_List_cons
        (__eo_datatype_cons_selectors_rec s d i d i native_nat_zero)
        (Term.DtSel s d i j) =
      Term.Numeral j := by
  intro hLt
  let selectors := __eo_datatype_cons_selectors_rec s d i d i native_nat_zero
  let target := Term.DtSel s d i j
  have hRec :
      __eo_list_find_rec selectors target (Term.Numeral native_nat_zero) =
        Term.Numeral j := by
    simpa [selectors, target] using
      datatype_cons_selectors_rec_find_rec_eq_index_of_smt_bound
        s d i d i native_nat_zero j (Nat.zero_le j) (by simpa using hLt)
  have hList :
      __eo_is_list Term.__eo_List_cons selectors = Term.Boolean true :=
    datatype_cons_selectors_rec_is_list_true_of_smt_bound
      s d i d i native_nat_zero j (Nat.zero_le j) (by simpa using hLt)
  have hRec0 :
      __eo_list_find_rec selectors target (Term.Numeral 0) = Term.Numeral j := by
    simpa using hRec
  simp [selectors, target, __eo_list_find, hList, hRec0, __eo_requires, native_ite, native_teq, native_not,
    SmtEval.native_not]

private theorem assoc_nil_nth_eoTermList_find_rec_nil_stuck
    (xs : List Term) (target start : Term) :
    __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
        (__eo_list_find_rec Term.__eo_List_nil target start) =
      Term.Stuck := by
  by_cases hTarget : target = Term.Stuck
  · subst target
    simp [__eo_list_find_rec, assoc_nil_nth_index_stuck]
  · by_cases hStart : start = Term.Stuck
    · subst start
      simp [__eo_list_find_rec, assoc_nil_nth_index_stuck]
    · have hFind :
          __eo_list_find_rec Term.__eo_List_nil target start =
            Term.Numeral (-1 : native_Int) := by
        cases target <;> cases start <;>
          simp [__eo_list_find_rec] at hTarget hStart ⊢
      rw [hFind]
      simpa [show (-1 : native_Int) = Int.negSucc 0 by rfl] using
        assoc_nil_nth_eoTermList_negSucc_stuck xs 0

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
        __eo_datatype_cons_selectors_rec s d i (Datatype.sum c restTail)
          Nat.zero (native_nat_succ ai)
      by_cases hTail : tail = Term.Stuck
      · have hFind :
            __eo_list_find_rec
                (__eo_datatype_cons_selectors_rec s d i
                  (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero ai)
                target (Term.Numeral ai) = Term.Stuck := by
          simp [target, tail, __eo_datatype_cons_selectors_rec,
            __eo_mk_apply, hTail, __eo_list_find_rec]
        rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
        exact False.elim (hTi hAssoc.symm)
      · have hList :
            __eo_datatype_cons_selectors_rec s d i
                (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero ai =
              Term.Apply (Term.Apply Term.__eo_List_cons current) tail := by
          simp [current, tail, __eo_datatype_cons_selectors_rec,
            __eo_mk_apply]
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
              native_ite, native_teq, native_zplus, hEq]
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
                s d i (Datatype.sum c restTail) Nat.zero (Nat.succ ai) (Nat.succ ai) j
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

private theorem datatype_cons_selectors_rec_find_rec_assoc_ne_stuck_implies_dt_sel :
    ∀ (s : native_String) (d : Datatype) (i : native_Nat)
      (rest : Datatype) (ci ai : native_Nat) (start target : Term)
      (xs : List Term) (ti : Term),
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
        (__eo_list_find_rec
          (__eo_datatype_cons_selectors_rec s d i rest ci ai)
          target start) = ti ->
      ti ≠ Term.Stuck ->
      ∃ j, target = Term.DtSel s d i j
  | s, d, i, Datatype.null, ci, ai, start, target, xs, ti, hAssoc, hTi => by
      have hFind :
          __eo_list_find_rec
              (__eo_datatype_cons_selectors_rec s d i Datatype.null ci ai)
              target start = Term.Stuck := by
        cases ci <;> simp [__eo_datatype_cons_selectors_rec,
          __eo_list_find_rec]
      rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
      exact False.elim (hTi hAssoc.symm)
  | s, d, i, Datatype.sum DatatypeCons.unit restTail, Nat.zero, ai,
      start, target, xs, ti, hAssoc, hTi => by
      have hAssocStuck :
          __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
            (__eo_list_find_rec
              (__eo_datatype_cons_selectors_rec s d i
                (Datatype.sum DatatypeCons.unit restTail) Nat.zero ai)
              target start) = Term.Stuck := by
        simp [__eo_datatype_cons_selectors_rec,
          assoc_nil_nth_eoTermList_find_rec_nil_stuck]
      exact False.elim (hTi (hAssoc.symm.trans hAssocStuck))
  | s, d, i, Datatype.sum (DatatypeCons.cons U c) restTail, Nat.zero, ai,
      start, target, xs, ti, hAssoc, hTi => by
      let current := Term.DtSel s d i ai
      let tail :=
        __eo_datatype_cons_selectors_rec s d i (Datatype.sum c restTail)
          Nat.zero (native_nat_succ ai)
      by_cases hTarget : target = current
      · exact ⟨ai, hTarget⟩
      · by_cases hTail : tail = Term.Stuck
        · have hAssocStuck :
              __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
                (__eo_list_find_rec
                  (__eo_datatype_cons_selectors_rec s d i
                    (Datatype.sum (DatatypeCons.cons U c) restTail)
                    Nat.zero ai)
                  target start) = Term.Stuck := by
            simp [tail, __eo_datatype_cons_selectors_rec,
              __eo_mk_apply, hTail, __eo_list_find_rec,
              assoc_nil_nth_index_stuck]
          exact False.elim (hTi (hAssoc.symm.trans hAssocStuck))
        · have hList :
              __eo_datatype_cons_selectors_rec s d i
                  (Datatype.sum (DatatypeCons.cons U c) restTail)
                  Nat.zero ai =
                Term.Apply (Term.Apply Term.__eo_List_cons current) tail := by
            simp [current, tail, __eo_datatype_cons_selectors_rec,
              __eo_mk_apply]
          have hCurrentTarget : current ≠ target := by
            intro h
            exact hTarget h.symm
          have hStep :
              __eo_list_find_rec
                  (Term.Apply (Term.Apply Term.__eo_List_cons current) tail)
                  target start =
                __eo_list_find_rec tail target
                  (__eo_add start (Term.Numeral 1)) := by
            exact eo_list_find_rec_cons_ne_eq_tail
              current tail target start hCurrentTarget (by simp [current])
          have hAssocTail :
              __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
                (__eo_list_find_rec tail target
                  (__eo_add start (Term.Numeral 1))) = ti := by
            rw [hList] at hAssoc
            rw [hStep] at hAssoc
            exact hAssoc
          exact
            datatype_cons_selectors_rec_find_rec_assoc_ne_stuck_implies_dt_sel
              s d i (Datatype.sum c restTail) Nat.zero (native_nat_succ ai)
              (__eo_add start (Term.Numeral 1)) target xs ti
              hAssocTail hTi
  | s, d, i, Datatype.sum c restTail, Nat.succ ci, ai, start, target, xs,
      ti, hAssoc, hTi => by
      have hAssoc' :
          __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
            (__eo_list_find_rec
              (__eo_datatype_cons_selectors_rec s d i restTail ci ai)
              target start) = ti := by
        simpa [__eo_datatype_cons_selectors_rec] using hAssoc
      exact
        datatype_cons_selectors_rec_find_rec_assoc_ne_stuck_implies_dt_sel
          s d i restTail ci ai start target xs ti hAssoc' hTi

private theorem dt_eq_cons_dtcons_false_of_appHead_dtcons_ne
    (s : native_String) (d : Datatype) (i : native_Nat)
    (ss : native_String) (dd : Datatype) (ii : native_Nat) :
    ∀ (t : Term),
      appHead t = Term.DtCons ss dd ii ->
      Term.DtCons s d i ≠ Term.DtCons ss dd ii ->
      __eo_dt_selectors (Term.DtCons s d i) ≠ Term.Stuck ->
      __eo_dt_selectors (Term.DtCons ss dd ii) ≠ Term.Stuck ->
      __dt_eq_cons (Term.DtCons s d i) t = Term.Boolean false
  | Term.Apply f a, hHead, hNe, hTargetSel, hHeadSel => by
      simpa [__dt_eq_cons] using
        dt_eq_cons_dtcons_false_of_appHead_dtcons_ne
          s d i ss dd ii f (by simpa [appHead] using hHead)
          hNe hTargetSel hHeadSel
  | Term.DtCons ss' dd' ii', hHead, hNe, hTargetSel, hHeadSel => by
      simp [appHead] at hHead
      rcases hHead with ⟨rfl, rfl, rfl⟩
      have hTargetOk :
          __eo_is_ok (__eo_dt_selectors (Term.DtCons s d i)) =
            Term.Boolean true :=
        eo_is_ok_true_of_ne_stuck
          (__eo_dt_selectors (Term.DtCons s d i)) hTargetSel
      have hHeadOk :
          __eo_is_ok (__eo_dt_selectors (Term.DtCons ss' dd' ii')) =
            Term.Boolean true :=
        eo_is_ok_true_of_ne_stuck
          (__eo_dt_selectors (Term.DtCons ss' dd' ii')) hHeadSel
      have hEqFalse :
          __eo_eq (Term.DtCons s d i) (Term.DtCons ss' dd' ii') =
            Term.Boolean false :=
        eo_eq_eq_false_of_ne hNe (by simp) (by simp)
      simp [__dt_eq_cons, __eo_requires, __eo_ite, __eo_is_eq,
        hTargetOk, hHeadOk, hEqFalse, native_ite, native_teq,
        native_not, SmtEval.native_not]
  | Term.Stuck, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.UOp op, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.UOp1 op a, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.UOp2 op a b, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.UOp3 op a b c, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.__eo_List, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.__eo_List_nil, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.__eo_List_cons, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.Bool, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.Boolean b, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.Numeral n, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.Rational q, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.String str, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.Binary w n, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.Type, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.FunType, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.Var name T, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.DatatypeType name D, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.DatatypeTypeRef name, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.DtcAppType a b, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.DtSel name D ci cj, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.USort name, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead
  | Term.UConst name T, hHead, _hNe, _hTargetSel, _hHeadSel => by
      simp [appHead] at hHead

theorem dt_eq_cons_false_of_find_neg_dt_sel_of_updater_non_none
    (s : native_String) (d : Datatype) (i j : native_Nat)
    (t a : Term) :
    TranslationProofs.__eo_reserved_datatype_name s = false ->
    __smtx_typeof
        (__eo_to_smt_updater
          (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j)
          (__eo_to_smt t) (__eo_to_smt a)) ≠
      SmtType.None ->
    __eo_is_neg
        (__eo_list_find Term.__eo_List_cons
          (__dt_get_selectors_of_app (__eo_typeof t) t)
          (Term.DtSel s d i j)) =
      Term.Boolean true ->
    __dt_eq_cons (Term.DtCons s d i) t = Term.Boolean false := by
  intro hReserved hUpdaterNN hFindNeg
  have hIdx :
      native_zlt (native_nat_to_int j)
          (native_nat_to_int
            (__smtx_dt_num_sels (__eo_to_smt_datatype d) i)) =
        true :=
    TranslationProofs.eo_to_smt_updater_dt_sel_guard_of_non_none
      s (__eo_to_smt_datatype d) i j (__eo_to_smt t) (__eo_to_smt a)
      hUpdaterNN
  have hBound : j < __smtx_dt_num_sels (__eo_to_smt_datatype d) i := by
    have hInt :
        (j : Int) <
          (__smtx_dt_num_sels (__eo_to_smt_datatype d) i : Int) := by
      apply of_decide_eq_true
      simpa [native_zlt, SmtEval.native_zlt, native_nat_to_int,
        SmtEval.native_nat_to_int] using hIdx
    exact Int.ofNat_lt.mp hInt
  have hIteNN :
      term_has_non_none_type
        (SmtTerm.ite
          (SmtTerm.Apply
            (SmtTerm.DtTester s (__eo_to_smt_datatype d) i)
            (__eo_to_smt t))
          (__eo_to_smt_updater_rec
            (SmtTerm.DtSel s (__eo_to_smt_datatype d) i j)
            (__smtx_dt_num_sels (__eo_to_smt_datatype d) i)
            (__eo_to_smt t) (__eo_to_smt a)
            (SmtTerm.DtCons s (__eo_to_smt_datatype d) i))
          (__eo_to_smt t)) := by
    unfold term_has_non_none_type
    simpa [__eo_to_smt_updater, native_ite, hIdx] using hUpdaterNN
  rcases ite_args_of_non_none hIteNN with
    ⟨_T, hCond, _hThen, hElse, _hTNN⟩
  have hCondNN :
      term_has_non_none_type
        (SmtTerm.Apply
          (SmtTerm.DtTester s (__eo_to_smt_datatype d) i)
          (__eo_to_smt t)) := by
    unfold term_has_non_none_type
    rw [hCond]
    simp
  have hTType :
      __smtx_typeof (__eo_to_smt t) =
        SmtType.Datatype s (__eo_to_smt_datatype d) :=
    dt_tester_arg_datatype_of_non_none hCondNN
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [hTType]
    simp
  have hMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t hTNN
  have hEoTy :
      __eo_to_smt_type (__eo_typeof t) =
        SmtType.Datatype s (__eo_to_smt_datatype d) :=
    hMatch.symm.trans hTType
  rcases TranslationProofs.eo_to_smt_type_eq_datatype_non_tuple
      (TranslationProofs.eo_unreserved_datatype_name_ne_tuple hReserved)
      hEoTy with
    ⟨dT, hType, _hD⟩
  have hTypeNe : __eo_typeof t ≠ Term.Stuck := by
    rw [hType]
    simp
  cases hHead : appHead t with
  | DtCons ss dd ii =>
      have hHeadSelectors :
          __dt_get_selectors_of_app (__eo_typeof t) t =
            __eo_dt_selectors (Term.DtCons ss dd ii) :=
        dt_get_selectors_of_app_of_appHead_dtcons
          (__eo_typeof t) ss dd ii t (by exact hTypeNe) hHead
      by_cases hSame : Term.DtCons s d i = Term.DtCons ss dd ii
      · cases hSame
        have hFind :
            __eo_list_find Term.__eo_List_cons
                (__dt_get_selectors_of_app (__eo_typeof t) t)
                (Term.DtSel s d i j) =
              Term.Numeral j := by
          rw [hHeadSelectors]
          simpa [__eo_dt_selectors] using
            datatype_cons_selectors_rec_find_eq_index_of_smt_bound
              s d i j hBound
        rw [hFind] at hFindNeg
        simp [__eo_is_neg, native_zlt, SmtEval.native_zlt] at hFindNeg
        exact False.elim
          ((Int.not_lt_of_ge (Int.natCast_nonneg j)) hFindNeg)
      · have hTargetSelNe :
            __eo_dt_selectors (Term.DtCons s d i) ≠ Term.Stuck := by
          intro hSel
          have hFind :=
            datatype_cons_selectors_rec_find_eq_index_of_smt_bound
              s d i j hBound
          have hRecStuck :
              __eo_datatype_cons_selectors_rec s d i d i native_nat_zero =
                Term.Stuck := by
            simpa [__eo_dt_selectors] using hSel
          rw [hRecStuck] at hFind
          simp [__eo_list_find, __eo_requires, __eo_is_list,
            native_ite, native_teq] at hFind
        have hHeadSelNe :
            __eo_dt_selectors (Term.DtCons ss dd ii) ≠ Term.Stuck := by
          intro hSel
          rw [hHeadSelectors, hSel] at hFindNeg
          simp [__eo_list_find, __eo_is_neg, __eo_requires, __eo_is_list,
            native_ite, native_teq] at hFindNeg
        exact
          dt_eq_cons_dtcons_false_of_appHead_dtcons_ne
            s d i ss dd ii t hHead hSame hTargetSelNe hHeadSelNe
  | _ =>
      exfalso
      have hSelectors :
          __dt_get_selectors_of_app (__eo_typeof t) t = Term.Stuck := by
        rw [dt_get_selectors_of_app_eq_appHead, hHead, hType]
        simp [__dt_get_selectors, __eo_dt_selectors, __eo_dt_selectors_main]
      rw [hSelectors] at hFindNeg
      simp [__eo_list_find, __eo_is_neg, __eo_requires, __eo_is_list,
        native_ite, native_teq] at hFindNeg

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
          simp [target, tail, __tuple_get_selectors_rec,
            __eo_mk_apply, hTail, __eo_list_find_rec]
        rw [hFind, assoc_nil_nth_index_stuck] at hAssoc
        exact False.elim (hTi hAssoc.symm)
      · have hList :
            __tuple_get_selectors_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
                (Term.Numeral start) =
              Term.Apply (Term.Apply Term.__eo_List_cons current) tail := by
          simp [current, tail, __tuple_get_selectors_rec, __eo_mk_apply]
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
              native_ite, native_teq, native_zplus, hIntNe]
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

private theorem tuple_get_selectors_rec_find_rec_assoc_ne_stuck_implies_tuple_select :
    ∀ (T n start target : Term) (xs : List Term) (ti : Term),
      __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
        (__eo_list_find_rec (__tuple_get_selectors_rec T n) target start) = ti ->
      ti ≠ Term.Stuck ->
      ∃ idx, target = Term.UOp1 UserOp1.tuple_select idx
  | T, n, start, target, xs, ti, hAssoc, hTi => by
      by_cases hUnit : T = Term.UOp UserOp.UnitTuple
      · subst T
        have hAssocStuck :
            __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
              (__eo_list_find_rec
                (__tuple_get_selectors_rec (Term.UOp UserOp.UnitTuple) n)
                target start) = Term.Stuck := by
          cases n <;>
            simp [__tuple_get_selectors_rec, __eo_list_find_rec,
              assoc_nil_nth_index_stuck,
              assoc_nil_nth_eoTermList_find_rec_nil_stuck]
        exact False.elim (hTi (hAssoc.symm.trans hAssocStuck))
      · by_cases hTuple :
          ∃ T1 T2, T = Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2
        · rcases hTuple with ⟨T1, T2, rfl⟩
          let current := Term.UOp1 UserOp1.tuple_select n
          let tail := __tuple_get_selectors_rec T2
            (__eo_add n (Term.Numeral 1))
          by_cases hTarget : target = current
          · exact ⟨n, hTarget⟩
          · by_cases hN : n = Term.Stuck
            · subst n
              have hAssocStuck :
                  __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
                    (__eo_list_find_rec
                      (__tuple_get_selectors_rec
                        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
                        Term.Stuck)
                      target start) = Term.Stuck := by
                simp [__tuple_get_selectors_rec, __eo_list_find_rec,
                  assoc_nil_nth_index_stuck]
              exact False.elim (hTi (hAssoc.symm.trans hAssocStuck))
            · by_cases hTail : tail = Term.Stuck
              · have hAssocStuck :
                    __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
                      (__eo_list_find_rec
                        (__tuple_get_selectors_rec
                          (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
                          n)
                        target start) = Term.Stuck := by
                  simp [tail, __tuple_get_selectors_rec,
                    __eo_mk_apply, hTail, __eo_list_find_rec,
                    assoc_nil_nth_index_stuck]
                exact False.elim (hTi (hAssoc.symm.trans hAssocStuck))
              · have hList :
                    __tuple_get_selectors_rec
                        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2)
                        n =
                      Term.Apply (Term.Apply Term.__eo_List_cons current) tail := by
                  simp [current, tail, __tuple_get_selectors_rec, __eo_mk_apply]
                have hCurrentTarget : current ≠ target := by
                  intro h
                  exact hTarget h.symm
                have hStep :
                    __eo_list_find_rec
                        (Term.Apply (Term.Apply Term.__eo_List_cons current) tail)
                        target start =
                      __eo_list_find_rec tail target
                        (__eo_add start (Term.Numeral 1)) := by
                  exact eo_list_find_rec_cons_ne_eq_tail
                    current tail target start hCurrentTarget (by simp [current])
                have hAssocTail :
                    __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
                      (__eo_list_find_rec tail target
                        (__eo_add start (Term.Numeral 1))) = ti := by
                  rw [hList] at hAssoc
                  rw [hStep] at hAssoc
                  exact hAssoc
                exact
                  tuple_get_selectors_rec_find_rec_assoc_ne_stuck_implies_tuple_select
                    T2 (__eo_add n (Term.Numeral 1))
                    (__eo_add start (Term.Numeral 1)) target xs ti
                    hAssocTail hTi
        · have hNotTuple :
              ∀ T1 T2,
                T ≠ Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T1) T2 := by
            intro T1 T2 h
            exact hTuple ⟨T1, T2, h⟩
          have hSelStuck :
              __tuple_get_selectors_rec T n = Term.Stuck :=
            tuple_get_selectors_rec_stuck_of_not_tuple_or_unit
              T n hUnit hNotTuple
          have hAssocStuck :
              __assoc_nil_nth Term.__eo_List_cons (eoTermList xs)
                (__eo_list_find_rec (__tuple_get_selectors_rec T n) target start) =
              Term.Stuck := by
            rw [hSelStuck]
            simp [__eo_list_find_rec, assoc_nil_nth_index_stuck]
          exact False.elim (hTi (hAssoc.symm.trans hAssocStuck))
termination_by T n start target xs ti hAssoc hTi => T

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
            __eo_is_list, __eo_requires, native_ite, native_teq]
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
        __eo_datatype_cons_selectors_rec s d i (Datatype.sum c restTail)
          Nat.zero (native_nat_succ native_nat_zero)
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
            native_ite, native_teq]
        exact False.elim (hFindNe hFind)
      · have hRec :
            __eo_datatype_cons_selectors_rec s d i
                (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero
                native_nat_zero =
              Term.Apply
                (Term.Apply Term.__eo_List_cons
                  (Term.DtSel s d i native_nat_zero)) tail := by
          simp [tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply]
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
        __eo_datatype_cons_selectors_rec s d i (Datatype.sum c restTail)
          Nat.zero (native_nat_succ ai)
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
          simp [tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply]
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
            __eo_is_list, __eo_requires, native_ite, native_teq]
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
        __eo_datatype_cons_selectors_rec s d i (Datatype.sum c restTail)
          Nat.zero (native_nat_succ native_nat_zero)
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
          simp [tail, __eo_datatype_cons_selectors_rec,
            __eo_mk_apply, hTail, __eo_list_find, __eo_is_list,
            __eo_requires, native_ite, native_teq]
        exact False.elim (hFindNe hFind)
      · have hRec :
            __eo_datatype_cons_selectors_rec s d i
                (Datatype.sum (DatatypeCons.cons U c) restTail) Nat.zero
                native_nat_zero = list := by
          simp [list, tail, __eo_datatype_cons_selectors_rec, __eo_mk_apply]
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
              s d i (Datatype.sum c restTail) Nat.zero (native_nat_succ native_nat_zero)
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

private theorem smtx_model_eval_tuple_prepend_rec_dtcons_spine
    (M : SmtModel) (hM : model_total_typed M)
    (fullD tailD : SmtDatatype) (tail head : SmtTerm) (k : native_Nat) :
    __smtx_typeof
        (__eo_to_smt_tuple_prepend_rec tailD tail k
          (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
            head)) ≠ SmtType.None ->
    __smtx_model_eval M
        (__eo_to_smt_tuple_prepend_rec tailD tail k
          (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
            head)) =
      mkDtSmtValueSpineRev
        (SmtValue.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
        ((tupleSelSmtArgsRev tailD tail k ++ [head]).map
          (__smtx_model_eval M)) := by
  intro hNN
  let args := tupleSelSmtArgsRev tailD tail k ++ [head]
  have hTerm :
      __eo_to_smt_tuple_prepend_rec tailD tail k
          (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
            head) =
        mkDtSmtAppSpineRev
          (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero) args := by
    simpa [args] using
      eo_to_smt_tuple_prepend_rec_eq_dtcons_spine
        fullD tailD tail head k
  have hSpineNN :
      __smtx_typeof
          (mkDtSmtAppSpineRev
            (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero) args) ≠
        SmtType.None := by
    rw [← hTerm]
    exact hNN
  have hArgsNN :
      ∀ x ∈ args, __smtx_model_eval M x ≠ SmtValue.NotValue := by
    intro x hx
    exact smt_model_eval_ne_notvalue_of_non_none M hM x
      (mkDtSmtAppSpineRev_args_non_none_of_non_none_type
        (native_string_lit "@Tuple") fullD native_nat_zero args hSpineNN x hx)
  rw [hTerm]
  exact smtx_model_eval_mkDtSmtAppSpineRev_dtcons
    M (native_string_lit "@Tuple") fullD native_nat_zero args hArgsNN

private theorem tuple_prepend_rec_projection_of_get
    (M : SmtModel) (hM : model_total_typed M)
    (fullD tailD : SmtDatatype) (tail head : SmtTerm)
    (k j : native_Nat) (v : SmtValue) :
    __smtx_typeof
        (__eo_to_smt_tuple_prepend_rec tailD tail k
          (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
            head)) ≠ SmtType.None ->
    listGetOptionValue
        (__smtx_model_eval M head ::
          (tupleSelSmtArgsRev tailD tail k).reverse.map
            (__smtx_model_eval M))
        j = some v ->
    __vsm_apply_arg_nth
        (__smtx_model_eval M
          (__eo_to_smt_tuple_prepend_rec tailD tail k
            (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
              head)))
        j (Nat.succ (tupleSelSmtArgsRev tailD tail k).length) = v := by
  intro hNN hGet
  rw [smtx_model_eval_tuple_prepend_rec_dtcons_spine
    M hM fullD tailD tail head k hNN]
  let forwardVals :=
    __smtx_model_eval M head ::
      (tupleSelSmtArgsRev tailD tail k).reverse.map (__smtx_model_eval M)
  have hVals :
      ((tupleSelSmtArgsRev tailD tail k ++ [head]).map
          (__smtx_model_eval M)) =
        forwardVals.reverse := by
    simp [forwardVals, List.map_append, List.map_reverse]
  rw [hVals]
  have hNth :=
    vsm_apply_arg_nth_mkDtSmtValueSpineRev_reverse_get?
      (SmtValue.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
      forwardVals j v hGet
  simpa [forwardVals] using hNth

private theorem tuple_prepend_rec_succ_projection_of_get
    (M : SmtModel) (hM : model_total_typed M)
    (fullD tailD : SmtDatatype) (tail head : SmtTerm)
    (k j : native_Nat) (v : SmtValue) :
    __smtx_typeof
        (__eo_to_smt_tuple_prepend_rec tailD tail k
          (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
            head)) ≠ SmtType.None ->
    listGetOptionValue
        ((tupleSelSmtArgsRev tailD tail k).reverse.map
          (__smtx_model_eval M))
        j = some v ->
    __vsm_apply_arg_nth
        (__smtx_model_eval M
          (__eo_to_smt_tuple_prepend_rec tailD tail k
            (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
              head)))
        (Nat.succ j) (Nat.succ (tupleSelSmtArgsRev tailD tail k).length) =
      v := by
  intro hNN hGet
  exact tuple_prepend_rec_projection_of_get
    M hM fullD tailD tail head k (Nat.succ j) v hNN
    (by simpa [listGetOptionValue] using hGet)

theorem tuple_prepend_zero_projection
    (M : SmtModel) (hM : model_total_typed M)
    (head tail : SmtTerm) (headTy : SmtType) (c : SmtDatatypeCons) :
    __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null) ->
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
      SmtType.None ->
    __vsm_apply_arg_nth
        (__smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail))
        native_nat_zero
        (__smtx_dt_num_sels
          (SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null)
          native_nat_zero) =
      __smtx_model_eval M head := by
  intro hTailTy hNN
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD := SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null
  have hFullWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullD) = true := by
    cases hWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullD)
    · exfalso
      apply hNN
      unfold __eo_to_smt_tuple_prepend
      rw [hTailTy]
      simp [__eo_to_smt_tuple_prepend_of_type, native_ite, hWf,
        fullD]
    · rfl
  have hTerm :
      __eo_to_smt_tuple_prepend head headTy tail =
        __eo_to_smt_tuple_prepend_rec tailD tail
          (__smtx_dt_num_sels tailD native_nat_zero)
          (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
            head) := by
    unfold __eo_to_smt_tuple_prepend
    rw [hTailTy]
    simp [__eo_to_smt_tuple_prepend_of_type, native_ite, hFullWf,
      tailD, fullD]
  have hRecNN :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero)
            (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
              head)) ≠ SmtType.None := by
    rw [← hTerm]
    exact hNN
  rw [hTerm]
  have hProj :=
    tuple_prepend_rec_projection_of_get M hM fullD tailD tail head
      (__smtx_dt_num_sels tailD native_nat_zero) native_nat_zero
      (__smtx_model_eval M head) hRecNN
      (by simp [listGetOptionValue])
  simpa [tailD, fullD, __smtx_dt_num_sels, __smtx_dtc_num_sels,
    tupleSelSmtArgsRev_length] using hProj

private theorem tuple_prepend_succ_projection_of_get
    (M : SmtModel) (hM : model_total_typed M)
    (head tail : SmtTerm) (headTy : SmtType) (c : SmtDatatypeCons)
    (j : native_Nat) (v : SmtValue) :
    __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null) ->
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
      SmtType.None ->
    listGetOptionValue
        ((tupleSelSmtArgsRev (SmtDatatype.sum c SmtDatatype.null) tail
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero)).reverse.map (__smtx_model_eval M))
        j = some v ->
    __vsm_apply_arg_nth
        (__smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail))
        (Nat.succ j)
        (__smtx_dt_num_sels
          (SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null)
          native_nat_zero) =
      v := by
  intro hTailTy hNN hGet
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD := SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null
  have hFullWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullD) = true := by
    cases hWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullD)
    · exfalso
      apply hNN
      unfold __eo_to_smt_tuple_prepend
      rw [hTailTy]
      simp [__eo_to_smt_tuple_prepend_of_type, native_ite, hWf,
        fullD]
    · rfl
  have hTerm :
      __eo_to_smt_tuple_prepend head headTy tail =
        __eo_to_smt_tuple_prepend_rec tailD tail
          (__smtx_dt_num_sels tailD native_nat_zero)
          (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
            head) := by
    unfold __eo_to_smt_tuple_prepend
    rw [hTailTy]
    simp [__eo_to_smt_tuple_prepend_of_type, native_ite, hFullWf,
      tailD, fullD]
  have hRecNN :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero)
            (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
              head)) ≠ SmtType.None := by
    rw [← hTerm]
    exact hNN
  rw [hTerm]
  have hProj :=
    tuple_prepend_rec_succ_projection_of_get M hM fullD tailD tail head
      (__smtx_dt_num_sels tailD native_nat_zero) j v hRecNN
      (by simpa [tailD] using hGet)
  simpa [tailD, fullD, __smtx_dt_num_sels, __smtx_dtc_num_sels,
    tupleSelSmtArgsRev_length] using hProj

private theorem tuple_prepend_tail_type_of_non_none_local
    (head : SmtTerm) (headTy : SmtType) (tail : SmtTerm) :
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
      SmtType.None ->
    ∃ c,
      __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null) := by
  intro hNN
  unfold __eo_to_smt_tuple_prepend at hNN
  cases hTail : __smtx_typeof tail with
  | Datatype s d =>
      by_cases hs : s = (native_string_lit "@Tuple")
      · subst s
        cases d with
        | null =>
            exact False.elim (hNN (by
              simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
        | sum c rest =>
            cases rest with
            | null =>
                exact ⟨c, rfl⟩
            | sum c' rest' =>
                exact False.elim (hNN (by
                  simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
      · cases d with
        | null =>
            exact False.elim (hNN (by
              simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
        | sum c rest =>
            cases rest with
            | null =>
                exact False.elim (hNN (by
                  have hCond :
                      ¬ (s = native_string_lit "@Tuple" ∧
                        __smtx_type_wf
                            (SmtType.Datatype (native_string_lit "@Tuple")
                              (SmtDatatype.sum (SmtDatatypeCons.cons headTy c)
                                SmtDatatype.null)) =
                          true) := by
                    intro h
                    exact hs h.1
                  simp [hTail, __eo_to_smt_tuple_prepend_of_type, hCond]))
            | sum c' rest' =>
                exact False.elim (hNN (by
                  simp [hTail, __eo_to_smt_tuple_prepend_of_type]))
  | _ =>
      exact False.elim (hNN (by
        simp [hTail, __eo_to_smt_tuple_prepend_of_type]))

private def smtDatatypeNumCtorsLocal : SmtDatatype -> Nat
  | SmtDatatype.null => 0
  | SmtDatatype.sum _ d => Nat.succ (smtDatatypeNumCtorsLocal d)

private theorem smtDatatypeNumCtorsLocal_substitute
    (s : native_String) (d0 : SmtDatatype) :
    ∀ d : SmtDatatype,
      smtDatatypeNumCtorsLocal (__smtx_dt_substitute s d0 d) =
        smtDatatypeNumCtorsLocal d
  | SmtDatatype.null => by
      simp [smtDatatypeNumCtorsLocal, __smtx_dt_substitute]
  | SmtDatatype.sum c d => by
      simp [smtDatatypeNumCtorsLocal, __smtx_dt_substitute,
        smtDatatypeNumCtorsLocal_substitute s d0 d]

private theorem dt_cons_applied_type_rec_non_none_implies_lt_ctors_local
    (s : native_String) (d0 : SmtDatatype) :
    ∀ {d : SmtDatatype} {i n : Nat},
      dt_cons_applied_type_rec s d0 d i n ≠ SmtType.None ->
      i < smtDatatypeNumCtorsLocal d
  | SmtDatatype.null, i, n, h => by
      exact False.elim (h (dt_cons_applied_type_rec_null s d0 i n))
  | SmtDatatype.sum c d, 0, n, _h => by
      simp [smtDatatypeNumCtorsLocal]
  | SmtDatatype.sum c d, Nat.succ i, n, h => by
      have h' : dt_cons_applied_type_rec s d0 d i n ≠ SmtType.None := by
        simpa only [dt_cons_applied_type_rec_succ] using h
      have hlt := dt_cons_applied_type_rec_non_none_implies_lt_ctors_local
        s d0 (d := d) (i := i) (n := n) h'
      simpa [smtDatatypeNumCtorsLocal] using Nat.succ_lt_succ hlt

private theorem datatype_value_head_of_type_local
    {v : SmtValue} {s : native_String} {d : SmtDatatype}
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    ∃ i, __vsm_apply_head v = SmtValue.DtCons s d i := by
  by_cases hHead : ∃ s0 d0 i0, __vsm_apply_head v = SmtValue.DtCons s0 d0 i0
  · rcases hHead with ⟨s0, d0, i0, hHead⟩
    have hChain :=
      dt_cons_chain_type_of_non_none hHead (by rw [hTy]; simp)
    have hEq :
        dt_cons_applied_type_rec s0 d0 (__smtx_dt_substitute s0 d0 d0) i0
            (vsm_num_apply_args v) =
          SmtType.Datatype s d := by
      exact hChain.symm.trans hTy
    have hArgsZero :
        __smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0 -
            vsm_num_apply_args v =
          0 := by
      have hArgs := congrArg dt_cons_type_num_args hEq
      rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
      simpa only [dt_cons_type_num_args_datatype] using hArgs
    have hle :
        vsm_num_apply_args v ≤
          __smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0 :=
      dt_cons_applied_type_rec_non_none_implies_le s0 d0
        (__smtx_dt_substitute s0 d0 d0) i0
        (vsm_num_apply_args v) (by rw [hEq]; simp)
    have hCount :
        vsm_num_apply_args v =
          __smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0 := by
      have hge :
          __smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0 ≤
            vsm_num_apply_args v :=
        (Nat.sub_eq_zero_iff_le).1 hArgsZero
      exact Nat.le_antisymm hle hge
    have hFull :
        dt_cons_applied_type_rec s0 d0 (__smtx_dt_substitute s0 d0 d0) i0
            (__smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0) =
          SmtType.Datatype s0 d0 :=
      dt_cons_applied_type_rec_full_arity s0 d0
        (__smtx_dt_substitute s0 d0 d0) i0
        (by rw [← hCount, hEq]; simp)
    have hBase : SmtType.Datatype s0 d0 = SmtType.Datatype s d := by
      calc
        SmtType.Datatype s0 d0 =
            dt_cons_applied_type_rec s0 d0 (__smtx_dt_substitute s0 d0 d0) i0
              (__smtx_dt_num_sels (__smtx_dt_substitute s0 d0 d0) i0) := by
          exact hFull.symm
        _ =
            dt_cons_applied_type_rec s0 d0 (__smtx_dt_substitute s0 d0 d0) i0
              (vsm_num_apply_args v) := by rw [hCount]
        _ = SmtType.Datatype s d := hEq
    injection hBase with hs hd
    subst hs
    subst hd
    exact ⟨i0, hHead⟩
  · cases v with
    | NotValue => simp [__smtx_typeof_value] at hTy
    | Boolean _ => simp [__smtx_typeof_value] at hTy
    | Numeral _ => simp [__smtx_typeof_value] at hTy
    | Rational _ => simp [__smtx_typeof_value] at hTy
    | Binary w n =>
        cases hWidth : native_zleq 0 w <;>
          cases hMod : native_zeq n (native_mod_total n (native_int_pow2 w)) <;>
          simp [__smtx_typeof_value, native_ite, SmtEval.native_and,
            hWidth, hMod] at hTy
    | Map m =>
        cases typeof_map_value_shape m with
        | inl hMap =>
            rcases hMap with ⟨A, B, hMap⟩
            simp [__smtx_typeof_value, hMap] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, hNone] at hTy
    | Set m =>
        cases typeof_map_value_shape m with
        | inl hMap =>
            rcases hMap with ⟨A, B, hMap⟩
            cases B <;>
              simp [__smtx_typeof_value, __smtx_map_to_set_type, hMap] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, __smtx_map_to_set_type, hNone] at hTy
    | Fun _ _ _ => simp [__smtx_typeof_value] at hTy
    | Seq ss =>
        cases typeof_seq_value_shape ss with
        | inl hSeq =>
            rcases hSeq with ⟨A, hSeq⟩
            simp [__smtx_typeof_value, hSeq] at hTy
        | inr hNone =>
            simp [__smtx_typeof_value, hNone] at hTy
    | Char c =>
        cases hValid : native_char_valid c <;>
          simp [__smtx_typeof_value, native_ite, hValid] at hTy
    | UValue _ _ => simp [__smtx_typeof_value] at hTy
    | RegLan _ => simp [__smtx_typeof_value] at hTy
    | DtCons s0 d0 i0 =>
        exact False.elim (hHead ⟨s0, d0, i0, by simp [__vsm_apply_head]⟩)
    | Apply f a =>
        have hNone :
            __smtx_typeof_value (SmtValue.Apply f a) = SmtType.None :=
          typeof_value_apply_of_head_ne_dt_cons f a
            (by
              intro s0 d0 i0 hf
              exact hHead ⟨s0, d0, i0, by simpa [__vsm_apply_head] using hf⟩)
        rw [hNone] at hTy
        cases hTy

private theorem datatype_head_index_lt_local
    {v : SmtValue} {s : native_String} {d : SmtDatatype} {i : Nat}
    (hHead : __vsm_apply_head v = SmtValue.DtCons s d i)
    (hTy : __smtx_typeof_value v = SmtType.Datatype s d) :
    i < smtDatatypeNumCtorsLocal d := by
  have hChain := dt_cons_chain_type_of_non_none hHead (by rw [hTy]; simp)
  have hNN :
      dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (vsm_num_apply_args v) ≠ SmtType.None := by
    rw [← hChain, hTy]
    simp
  have hltSub := dt_cons_applied_type_rec_non_none_implies_lt_ctors_local
    s d (d := __smtx_dt_substitute s d d) (i := i)
    (n := vsm_num_apply_args v) hNN
  simpa [smtDatatypeNumCtorsLocal_substitute s d d] using hltSub

theorem tuple_datatype_value_head_zero
    {v : SmtValue} {c : SmtDatatypeCons}
    (hTy :
      __smtx_typeof_value v =
        SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null)) :
    __vsm_apply_head v =
      SmtValue.DtCons (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null)
        native_nat_zero := by
  rcases datatype_value_head_of_type_local hTy with ⟨i, hHead⟩
  have hlt : i < 1 := by
    simpa [smtDatatypeNumCtorsLocal] using
      datatype_head_index_lt_local hHead hTy
  cases i with
  | zero =>
      simpa using hHead
  | succ i =>
      have hlt0 : i < 0 := Nat.succ_lt_succ_iff.mp hlt
      exact False.elim (Nat.not_lt_zero i hlt0)

theorem smt_tuple_dt_sel_eval_uses_constructor
    (M : SmtModel) (hM : model_total_typed M)
    (tail : SmtTerm) (c : SmtDatatypeCons) (j : native_Nat) :
    __smtx_typeof tail =
      SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null) ->
    __smtx_model_eval M
        (SmtTerm.Apply
          (SmtTerm.DtSel (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero j) tail) =
      __vsm_apply_arg_nth
        (__smtx_model_eval M tail) j
        (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
          native_nat_zero) := by
  intro hTailTy
  have hTailNN : __smtx_typeof tail ≠ SmtType.None := by
    rw [hTailTy]
    simp
  have hEvalTy :
      __smtx_typeof_value (__smtx_model_eval M tail) =
        SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null) := by
    rw [smt_model_eval_preserves_type_of_non_none M hM tail hTailNN,
      hTailTy]
  have hHead :
      __vsm_apply_head (__smtx_model_eval M tail) =
        SmtValue.DtCons (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null)
          native_nat_zero :=
    tuple_datatype_value_head_zero hEvalTy
  simp [__smtx_model_eval]
  unfold __smtx_model_eval_dt_sel
  have hHeadTrue :
      native_veq
          (__vsm_apply_head (__smtx_model_eval M tail))
          (SmtValue.DtCons (native_string_lit "@Tuple")
            (SmtDatatype.sum c SmtDatatype.null) native_nat_zero) = true := by
    rw [hHead]
    simp [native_veq]
  simp [native_ite, hHeadTrue]

theorem tuple_prepend_succ_projection
    (M : SmtModel) (hM : model_total_typed M)
    (head tail : SmtTerm) (headTy : SmtType) (c : SmtDatatypeCons)
    (j : native_Nat) :
    __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null) ->
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
      SmtType.None ->
    j <
      __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
        native_nat_zero ->
    __vsm_apply_arg_nth
        (__smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail))
        (Nat.succ j)
        (__smtx_dt_num_sels
          (SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null)
          native_nat_zero) =
      __vsm_apply_arg_nth
        (__smtx_model_eval M tail) j
        (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
          native_nat_zero) := by
  intro hTailTy hNN hLt
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let selector :=
    SmtTerm.Apply (SmtTerm.DtSel (native_string_lit "@Tuple") tailD native_nat_zero j) tail
  have hGet :
      listGetOptionValue
          ((tupleSelSmtArgsRev tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero)).reverse.map
              (__smtx_model_eval M))
          j =
        some (__smtx_model_eval M selector) := by
    exact tupleSelSmtArgsRev_reverse_map_get_of_lt M tailD tail
      (__smtx_dt_num_sels tailD native_nat_zero) j
      (by simpa [tailD] using hLt)
  have hProj :=
    tuple_prepend_succ_projection_of_get M hM head tail headTy c j
      (__smtx_model_eval M selector) hTailTy hNN
      (by simpa [tailD, selector] using hGet)
  have hSel :
      __smtx_model_eval M selector =
        __vsm_apply_arg_nth
          (__smtx_model_eval M tail) j
          (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
            native_nat_zero) := by
    simpa [selector, tailD] using
      smt_tuple_dt_sel_eval_uses_constructor M hM tail c j hTailTy
  rw [hProj, hSel]

private theorem tuple_prepend_datatype_eq_of_type
    (M : SmtModel) (hM : model_total_typed M)
    (head tail : SmtTerm) (headTy : SmtType)
    (c : SmtDatatypeCons) (d : SmtDatatype) :
    __smtx_typeof tail =
        SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null) ->
    __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) =
        SmtType.Datatype (native_string_lit "@Tuple") d ->
    d = SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null := by
  intro hTailTy hTy
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD := SmtDatatype.sum (SmtDatatypeCons.cons headTy c) SmtDatatype.null
  have hNN :
      __smtx_typeof (__eo_to_smt_tuple_prepend head headTy tail) ≠
        SmtType.None := by
    rw [hTy]
    simp
  have hFullWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullD) = true := by
    cases hWf : __smtx_type_wf (SmtType.Datatype (native_string_lit "@Tuple") fullD)
    · exfalso
      apply hNN
      unfold __eo_to_smt_tuple_prepend
      rw [hTailTy]
      simp [__eo_to_smt_tuple_prepend_of_type, native_ite, hWf,
        fullD]
    · rfl
  have hTerm :
      __eo_to_smt_tuple_prepend head headTy tail =
        __eo_to_smt_tuple_prepend_rec tailD tail
          (__smtx_dt_num_sels tailD native_nat_zero)
          (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
            head) := by
    unfold __eo_to_smt_tuple_prepend
    rw [hTailTy]
    simp [__eo_to_smt_tuple_prepend_of_type, native_ite, hFullWf,
      tailD, fullD]
  have hRecNN :
      __smtx_typeof
          (__eo_to_smt_tuple_prepend_rec tailD tail
            (__smtx_dt_num_sels tailD native_nat_zero)
            (SmtTerm.Apply (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
              head)) ≠ SmtType.None := by
    rw [← hTerm]
    exact hNN
  have hEvalSpine :
      __smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail) =
        mkDtSmtValueSpineRev
          (SmtValue.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
          ((tupleSelSmtArgsRev tailD tail
              (__smtx_dt_num_sels tailD native_nat_zero) ++ [head]).map
            (__smtx_model_eval M)) := by
    rw [hTerm]
    exact smtx_model_eval_tuple_prepend_rec_dtcons_spine
      M hM fullD tailD tail head
      (__smtx_dt_num_sels tailD native_nat_zero) hRecNN
  have hEvalTy :
      __smtx_typeof_value
          (__smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail)) =
        SmtType.Datatype (native_string_lit "@Tuple") d := by
    rw [smt_model_eval_preserves_type_of_non_none M hM
      (__eo_to_smt_tuple_prepend head headTy tail) hNN, hTy]
  rcases datatype_value_head_of_type_local hEvalTy with ⟨i, hHeadD⟩
  have hHeadFull :
      __vsm_apply_head
          (__smtx_model_eval M (__eo_to_smt_tuple_prepend head headTy tail)) =
        SmtValue.DtCons (native_string_lit "@Tuple") fullD native_nat_zero := by
    rw [hEvalSpine]
    simp [vsm_apply_head_mkDtSmtValueSpineRev_dtcons]
  rw [hHeadFull] at hHeadD
  injection hHeadD with _hName hD _hIdx
  simpa [fullD] using hD.symm

private theorem tuple_projection_eq_of_tuple_value_assoc
    (M : SmtModel) (hM : model_total_typed M) :
    ∀ (tail ti : Term) (c : SmtDatatypeCons) (j : native_Nat),
      isTupleValue tail ->
      __smtx_typeof (__eo_to_smt tail) =
          SmtType.Datatype (native_string_lit "@Tuple") (SmtDatatype.sum c SmtDatatype.null) ->
      __assoc_nil_nth Term.__eo_List_cons (__dt_arg_list tail)
          (Term.Numeral j) = ti ->
      ti ≠ Term.Stuck ->
      j <
        __smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
          native_nat_zero ->
      __smtx_model_eval_eq
          (__vsm_apply_arg_nth
            (__smtx_model_eval M (__eo_to_smt tail)) j
            (__smtx_dt_num_sels (SmtDatatype.sum c SmtDatatype.null)
              native_nat_zero))
          (__smtx_model_eval M (__eo_to_smt ti)) =
        SmtValue.Boolean true
  | Term.Apply f rest, ti, c, j, hTuple, hTy, hAssoc, hTi, hLt => by
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op <;> try simp [isTupleValue] at hTuple
              case tuple =>
                let full := Term.Apply
                  (Term.Apply (Term.UOp UserOp.tuple) x) rest
                let head := __eo_to_smt x
                let tailSmt := __eo_to_smt rest
                let headTy := __smtx_typeof head
                have hFullNN :
                    __smtx_typeof (__eo_to_smt full) ≠ SmtType.None := by
                  rw [hTy]
                  simp
                have hPrependNN :
                    __smtx_typeof
                        (__eo_to_smt_tuple_prepend head headTy tailSmt) ≠
                      SmtType.None := by
                  change __smtx_typeof (__eo_to_smt full) ≠ SmtType.None
                  exact hFullNN
                rcases tuple_prepend_tail_type_of_non_none_local
                    head headTy tailSmt hPrependNN with
                  ⟨tailC, hTailTy⟩
                have hDatatype :
                    SmtDatatype.sum c SmtDatatype.null =
                      SmtDatatype.sum (SmtDatatypeCons.cons headTy tailC)
                        SmtDatatype.null := by
                  exact tuple_prepend_datatype_eq_of_type M hM head tailSmt
                    headTy tailC (SmtDatatype.sum c SmtDatatype.null)
                    hTailTy (by
                      change
                        __smtx_typeof
                            (__eo_to_smt_tuple_prepend head headTy tailSmt) =
                          SmtType.Datatype (native_string_lit "@Tuple")
                            (SmtDatatype.sum c SmtDatatype.null)
                      exact hTy)
                injection hDatatype with hC _hNull
                subst c
                have hTailEq :
                    __dt_arg_list rest = __tuple_arg_list rest :=
                  dt_arg_list_eq_tuple_arg_list_of_tuple_value rest
                    (by simpa [isTupleValue] using hTuple)
                have hTailTupleArgsNe :
                    __tuple_arg_list rest ≠ Term.Stuck := by
                  intro hTailArgs
                  have hArgsStuck : __dt_arg_list full = Term.Stuck := by
                    simp [full, __dt_arg_list, __tuple_arg_list,
                      __eo_mk_apply, hTailArgs]
                  have hAssocStuck :
                      __assoc_nil_nth Term.__eo_List_cons (__dt_arg_list full)
                          (Term.Numeral j) = Term.Stuck := by
                    rw [hArgsStuck]
                    exact assoc_nil_nth_list_stuck Term.__eo_List_cons
                      (Term.Numeral j)
                  exact hTi (hAssoc.symm.trans hAssocStuck)
                have hTailArgsNe : __dt_arg_list rest ≠ Term.Stuck := by
                  intro hTailArgs
                  exact hTailTupleArgsNe (hTailEq.symm.trans hTailArgs)
                have hArgs :
                    __dt_arg_list full =
                      Term.Apply (Term.Apply Term.__eo_List_cons x)
                        (__dt_arg_list rest) := by
                  rw [hTailEq]
                  simp [full, __dt_arg_list, __tuple_arg_list,
                    __eo_mk_apply]
                cases j with
                | zero =>
                    have hTiEq : ti = x := by
                      have hAssoc' :
                          __assoc_nil_nth Term.__eo_List_cons
                              (Term.Apply
                                (Term.Apply Term.__eo_List_cons x)
                                (__dt_arg_list rest))
                              (Term.Numeral native_nat_zero) = ti := by
                        simpa [full, hArgs] using hAssoc
                      simp [__assoc_nil_nth, __eo_eq, native_ite,
                        native_teq] at hAssoc'
                      exact hAssoc'.symm
                    rw [hTiEq]
                    have hProj :
                        __vsm_apply_arg_nth
                            (__smtx_model_eval M (__eo_to_smt full))
                            native_nat_zero
                            (__smtx_dt_num_sels
                              (SmtDatatype.sum
                                (SmtDatatypeCons.cons headTy tailC)
                                SmtDatatype.null)
                              native_nat_zero) =
                          __smtx_model_eval M (__eo_to_smt x) := by
                      change
                        __vsm_apply_arg_nth
                            (__smtx_model_eval M
                              (__eo_to_smt_tuple_prepend head headTy tailSmt))
                            native_nat_zero
                            (__smtx_dt_num_sels
                              (SmtDatatype.sum
                                (SmtDatatypeCons.cons headTy tailC)
                                SmtDatatype.null)
                              native_nat_zero) =
                          __smtx_model_eval M head
                      exact tuple_prepend_zero_projection M hM head tailSmt
                        headTy tailC hTailTy hPrependNN
                    rw [hProj]
                    exact RuleProofs.smtx_model_eval_eq_refl _
                | succ j =>
                    have hTailAssoc :
                        __assoc_nil_nth Term.__eo_List_cons
                            (__dt_arg_list rest) (Term.Numeral j) = ti := by
                      have hAssoc' :
                          __assoc_nil_nth Term.__eo_List_cons
                              (Term.Apply
                                (Term.Apply Term.__eo_List_cons x)
                                (__dt_arg_list rest))
                              (Term.Numeral (Nat.succ j)) = ti := by
                        simpa [full, hArgs] using hAssoc
                      simpa using
                        (assoc_nil_nth_cons_succ_any x
                          (__dt_arg_list rest) j).symm.trans hAssoc'
                    have hLtTail :
                        j <
                          __smtx_dt_num_sels
                            (SmtDatatype.sum tailC SmtDatatype.null)
                            native_nat_zero := by
                      simpa [__smtx_dt_num_sels, __smtx_dtc_num_sels]
                        using hLt
                    have hProj :
                        __vsm_apply_arg_nth
                            (__smtx_model_eval M (__eo_to_smt full))
                            (Nat.succ j)
                            (__smtx_dt_num_sels
                              (SmtDatatype.sum
                                (SmtDatatypeCons.cons headTy tailC)
                                SmtDatatype.null)
                              native_nat_zero) =
                          __vsm_apply_arg_nth
                            (__smtx_model_eval M tailSmt) j
                            (__smtx_dt_num_sels
                              (SmtDatatype.sum tailC SmtDatatype.null)
                              native_nat_zero) := by
                      change
                        __vsm_apply_arg_nth
                            (__smtx_model_eval M
                              (__eo_to_smt_tuple_prepend head headTy tailSmt))
                            (Nat.succ j)
                            (__smtx_dt_num_sels
                              (SmtDatatype.sum
                                (SmtDatatypeCons.cons headTy tailC)
                                SmtDatatype.null)
                              native_nat_zero) =
                          __vsm_apply_arg_nth
                            (__smtx_model_eval M tailSmt) j
                            (__smtx_dt_num_sels
                              (SmtDatatype.sum tailC SmtDatatype.null)
                              native_nat_zero)
                      exact tuple_prepend_succ_projection M hM head tailSmt
                        headTy tailC j hTailTy hPrependNN hLtTail
                    rw [hProj]
                    exact tuple_projection_eq_of_tuple_value_assoc M hM rest
                      ti tailC j (by simpa [isTupleValue] using hTuple)
                      hTailTy hTailAssoc hTi hLtTail
          | _ =>
              simp [isTupleValue] at hTuple
      | _ =>
          simp [isTupleValue] at hTuple
  | Term.UOp op, ti, c, j, hTuple, _hTy, hAssoc, hTi, _hLt => by
      cases op <;> simp [isTupleValue] at hTuple
      case tuple_unit =>
        simp [__dt_arg_list, __get_arg_list_rec, assoc_nil_nth_nil_stuck]
          at hAssoc
        exact False.elim (hTi hAssoc.symm)
  | Term.UOp1 _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.UOp2 _ _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.UOp3 _ _ _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.__eo_List, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.__eo_List_nil, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.__eo_List_cons, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.Bool, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.Boolean _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.Numeral _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.Rational _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.String _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.Binary _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.Type, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.Stuck, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.FunType, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.Var _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.DatatypeType _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.DatatypeTypeRef _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.DtcAppType _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.DtCons _ _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.DtSel _ _ _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.USort _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
  | Term.UConst _ _, _ti, _c, _j, hTuple, _hTy, _hAssoc, _hTi, _hLt => by
      simp [isTupleValue] at hTuple
termination_by tail ti c j hTuple hTy hAssoc hTi hLt => tail


private theorem datatype_cons_selectors_rec_find_rec_tuple_select_stuck_or_neg
    (s : native_String) (d : Datatype) (i : native_Nat) (idx : Term) :
    ∀ (rest : Datatype) (ci ai : native_Nat) (start : Term),
      __eo_list_find_rec
          (__eo_datatype_cons_selectors_rec s d i rest ci ai)
          (Term.UOp1 UserOp1.tuple_select idx) start = Term.Stuck ∨
        __eo_list_find_rec
          (__eo_datatype_cons_selectors_rec s d i rest ci ai)
          (Term.UOp1 UserOp1.tuple_select idx) start =
            Term.Numeral (-1 : native_Int)
  | Datatype.null, ci, ai, start => by
      cases ci <;>
        simp [__eo_datatype_cons_selectors_rec, __eo_list_find_rec]
  | Datatype.sum DatatypeCons.unit restTail, Nat.zero, ai, start => by
      cases start <;>
        simp [__eo_datatype_cons_selectors_rec, __eo_list_find_rec]
  | Datatype.sum (DatatypeCons.cons U c) restTail, Nat.zero, ai, start => by
      let current := Term.DtSel s d i ai
      let tail :=
        __eo_datatype_cons_selectors_rec s d i (Datatype.sum c restTail)
          Nat.zero (native_nat_succ ai)
      by_cases hTail : tail = Term.Stuck
      · left
        simp [tail, __eo_datatype_cons_selectors_rec,
          __eo_mk_apply, hTail, __eo_list_find_rec]
      · have hRec :=
          datatype_cons_selectors_rec_find_rec_tuple_select_stuck_or_neg
            s d i idx (Datatype.sum c restTail) Nat.zero (native_nat_succ ai)
            (__eo_add start (Term.Numeral 1))
        have hStep :
            __eo_list_find_rec
                (Term.Apply (Term.Apply Term.__eo_List_cons current) tail)
                (Term.UOp1 UserOp1.tuple_select idx) start =
              __eo_list_find_rec tail
                (Term.UOp1 UserOp1.tuple_select idx)
                (__eo_add start (Term.Numeral 1)) := by
          cases start <;>
            simp [current, tail, __eo_list_find_rec, __eo_eq,
              __eo_add, native_ite, native_teq]
        rcases hRec with hRec | hRec
        · left
          rw [show
            __eo_list_find_rec
                (__eo_datatype_cons_selectors_rec s d i
                  (Datatype.sum (DatatypeCons.cons U c) restTail)
                  Nat.zero ai)
                (Term.UOp1 UserOp1.tuple_select idx) start =
              __eo_list_find_rec
                (Term.Apply (Term.Apply Term.__eo_List_cons current) tail)
                (Term.UOp1 UserOp1.tuple_select idx) start by
              simp [current, tail, __eo_datatype_cons_selectors_rec,
                __eo_mk_apply]]
          rw [hStep]
          exact hRec
        · right
          rw [show
            __eo_list_find_rec
                (__eo_datatype_cons_selectors_rec s d i
                  (Datatype.sum (DatatypeCons.cons U c) restTail)
                  Nat.zero ai)
                (Term.UOp1 UserOp1.tuple_select idx) start =
              __eo_list_find_rec
                (Term.Apply (Term.Apply Term.__eo_List_cons current) tail)
                (Term.UOp1 UserOp1.tuple_select idx) start by
              simp [current, tail, __eo_datatype_cons_selectors_rec,
                __eo_mk_apply]]
          rw [hStep]
          exact hRec
  | Datatype.sum c restTail, Nat.succ ci, ai, start => by
      simpa [__eo_datatype_cons_selectors_rec] using
        datatype_cons_selectors_rec_find_rec_tuple_select_stuck_or_neg
          s d i idx restTail ci ai start

private theorem eo_typeof_apply_tuple_type_stuck (T U V : Term) :
    __eo_typeof_apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U) V =
      Term.Stuck := by
  cases V <;> simp [__eo_typeof_apply]

private theorem eo_typeof_apply_stuck_head (V : Term) :
    __eo_typeof_apply Term.Stuck V = Term.Stuck := by
  cases V <;> simp [__eo_typeof_apply]

private theorem eo_typeof_apply_requires_tuple_type_stuck
    (P T U V : Term) :
    __eo_typeof_apply
        (__eo_requires P (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U)) V =
      Term.Stuck := by
  cases hP : native_teq P (Term.Boolean true) <;>
    cases hStuck : native_not (native_teq P Term.Stuck) <;>
      simp [__eo_requires, native_ite, hP, hStuck,
        eo_typeof_apply_tuple_type_stuck, eo_typeof_apply_stuck_head]

private theorem eo_typeof_apply_typeof_tuple_stuck
    (T U V : Term) :
    __eo_typeof_apply (__eo_typeof_tuple T U) V = Term.Stuck := by
  unfold __eo_typeof_tuple
  split
  · cases V <;> simp [__eo_typeof_apply]
  · cases V <;> simp [__eo_typeof_apply]
  · exact eo_typeof_apply_requires_tuple_type_stuck
      (__eo_is_ok (__eo_list_len (Term.UOp UserOp.Tuple) U)) T U V

private theorem eo_typeof_tuple_head_extra_application_stuck :
    ∀ (g x tail : Term),
      appHead g = Term.UOp UserOp.tuple ->
      g ≠ Term.UOp UserOp.tuple ->
      __eo_typeof (((g.Apply x).Apply tail)) = Term.Stuck
  | Term.Apply f y, x, tail, hHead, _hNe => by
      cases f with
      | UOp op =>
          cases op with
          | tuple =>
              change
                __eo_typeof_apply
                    (__eo_typeof_tuple (__eo_typeof y) (__eo_typeof x))
                    (__eo_typeof tail) = Term.Stuck
              exact eo_typeof_apply_typeof_tuple_stuck
                (__eo_typeof y) (__eo_typeof x) (__eo_typeof tail)
          | _ =>
              simp [appHead] at hHead
      | Apply f' y' =>
          have hInner :
              __eo_typeof (((Term.Apply f' y').Apply y).Apply x) =
                Term.Stuck := by
            exact eo_typeof_tuple_head_extra_application_stuck
              (Term.Apply f' y') y x
              (by simpa [appHead] using hHead)
              (by intro h; cases h)
          change
            __eo_typeof_apply
                (__eo_typeof (((Term.Apply f' y').Apply y).Apply x))
                (__eo_typeof tail) = Term.Stuck
          rw [hInner]
          exact eo_typeof_apply_stuck_head (__eo_typeof tail)
      | _ =>
          cases hHead
  | Term.UOp op, x, tail, hHead, hNe => by
      exact False.elim (hNe (by simpa [appHead] using hHead))
  | Term.UOp1 _ _, x, tail, hHead, _hNe => by cases hHead
  | Term.UOp2 _ _ _, x, tail, hHead, _hNe => by cases hHead
  | Term.UOp3 _ _ _ _, x, tail, hHead, _hNe => by cases hHead
  | Term.__eo_List, x, tail, hHead, _hNe => by cases hHead
  | Term.__eo_List_nil, x, tail, hHead, _hNe => by cases hHead
  | Term.__eo_List_cons, x, tail, hHead, _hNe => by cases hHead
  | Term.Bool, x, tail, hHead, _hNe => by cases hHead
  | Term.Boolean _, x, tail, hHead, _hNe => by cases hHead
  | Term.Numeral _, x, tail, hHead, _hNe => by cases hHead
  | Term.Rational _, x, tail, hHead, _hNe => by cases hHead
  | Term.String _, x, tail, hHead, _hNe => by cases hHead
  | Term.Binary _ _, x, tail, hHead, _hNe => by cases hHead
  | Term.Type, x, tail, hHead, _hNe => by cases hHead
  | Term.Stuck, x, tail, hHead, _hNe => by cases hHead
  | Term.FunType, x, tail, hHead, _hNe => by cases hHead
  | Term.Var _ _, x, tail, hHead, _hNe => by cases hHead
  | Term.DatatypeType _ _, x, tail, hHead, _hNe => by cases hHead
  | Term.DatatypeTypeRef _, x, tail, hHead, _hNe => by cases hHead
  | Term.DtcAppType _ _, x, tail, hHead, _hNe => by cases hHead
  | Term.DtCons _ _ _, x, tail, hHead, _hNe => by cases hHead
  | Term.DtSel _ _ _ _, x, tail, hHead, _hNe => by cases hHead
  | Term.USort _, x, tail, hHead, _hNe => by cases hHead
  | Term.UConst _ _, x, tail, hHead, _hNe => by cases hHead
