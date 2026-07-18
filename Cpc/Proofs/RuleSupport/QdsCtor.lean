import Cpc.Proofs.RuleSupport.DatatypeSupport
import Cpc.Proofs.RuleSupport.SubstituteTranslatabilitySupport

open Eo
open SmtEval
open Smtm

namespace QuantDtSplitRule

attribute [local simp] Smtm.__smtx_type_wf_component

set_option maxHeartbeats 1000000000
set_option synthInstance.maxHeartbeats 1000000

inductive CH : Term -> Prop where
  | datatype (s : native_String) (d : Datatype) (i : native_Nat) :
      CH (Term.DtCons s d i)
  | tuple : CH (Term.UOp UserOp.tuple)
  | tupleUnit : CH (Term.UOp UserOp.tuple_unit)

inductive CS : Term -> Prop where
  | head {c : Term} : CH c -> CS c
  | apply {c : Term} {s : native_String} {T : Term} :
      CS c ->
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      CS (Term.Apply c (Term.Var (Term.String s) T))

inductive DCS : Term -> Prop where
  | head (s : native_String) (d : Datatype) (i : native_Nat) :
      DCS (Term.DtCons s d i)
  | apply {c : Term} {s : native_String} {T : Term} :
      DCS c ->
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      DCS (Term.Apply c (Term.Var (Term.String s) T))

inductive TCS : Term -> Prop where
  | head : TCS (Term.UOp UserOp.tuple)
  | apply {c : Term} {s : native_String} {T : Term} :
      TCS c ->
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      TCS (Term.Apply c (Term.Var (Term.String s) T))

inductive UCS : Term -> Prop where
  | head : UCS (Term.UOp UserOp.tuple_unit)
  | apply {c : Term} {s : native_String} {T : Term} :
      UCS c ->
      __smtx_type_wf (__eo_to_smt_type T) = true ->
      UCS (Term.Apply c (Term.Var (Term.String s) T))

theorem cs_cases {c : Term} (h : CS c) : DCS c ∨ TCS c ∨ UCS c := by
  induction h with
  | head hh =>
      cases hh with
      | datatype s d i => exact .inl (.head s d i)
      | tuple => exact .inr (.inl .head)
      | tupleUnit => exact .inr (.inr .head)
  | apply h wf ih =>
      rcases ih with ih | ih | ih
      · exact .inl (.apply ih wf)
      · exact .inr (.inl (.apply ih wf))
      · exact .inr (.inr (.apply ih wf))

/-! The generated SMT datatype typing functions expose selector types by
walking an application spine.  These small list views make that information
usable by the reverse quantifier proof. -/

def qdsSmtApplyHead : SmtTerm -> SmtTerm
  | SmtTerm.Apply f _ => qdsSmtApplyHead f
  | t => t

def qdsSmtNumApplyArgs : SmtTerm -> Nat
  | SmtTerm.Apply f _ => Nat.succ (qdsSmtNumApplyArgs f)
  | _ => 0

def qdsSmtApplyArgs : SmtTerm -> List SmtTerm
  | SmtTerm.Apply f a => qdsSmtApplyArgs f ++ [a]
  | _ => []

theorem qdsSmtApplyHead_foldl (f : SmtTerm) (args : List Term) :
    qdsSmtApplyHead
        (List.foldl (fun g a => SmtTerm.Apply g (__eo_to_smt a)) f args) =
      qdsSmtApplyHead f := by
  induction args generalizing f with
  | nil => rfl
  | cons a args ih => exact ih (SmtTerm.Apply f (__eo_to_smt a))

theorem qdsSmtApplyArgs_foldl (f : SmtTerm) (args : List Term) :
    qdsSmtApplyArgs
        (List.foldl (fun g a => SmtTerm.Apply g (__eo_to_smt a)) f args) =
      qdsSmtApplyArgs f ++ args.map __eo_to_smt := by
  induction args generalizing f with
  | nil => simp
  | cons a args ih =>
      rw [show List.foldl (fun g a => SmtTerm.Apply g (__eo_to_smt a)) f
        (a :: args) = List.foldl
          (fun g a => SmtTerm.Apply g (__eo_to_smt a))
          (SmtTerm.Apply f (__eo_to_smt a)) args from rfl]
      rw [ih]
      simp [qdsSmtApplyArgs, List.append_assoc]

theorem qds_foldl_prefix_non_none
    {f : SmtTerm} {s : native_String} {d : SmtDatatype} {i : Nat}
    (args : List Term)
    (hHead : qdsSmtApplyHead f = SmtTerm.DtCons s d i)
    (hNN : __smtx_typeof
        (List.foldl (fun g a => SmtTerm.Apply g (__eo_to_smt a)) f args) ≠
      SmtType.None) :
    __smtx_typeof f ≠ SmtType.None := by
  induction args generalizing f with
  | nil => exact hNN
  | cons a args ih =>
      have hHeadApply : qdsSmtApplyHead (SmtTerm.Apply f (__eo_to_smt a)) =
          SmtTerm.DtCons s d i := by simpa [qdsSmtApplyHead] using hHead
      have hApplyNN : __smtx_typeof (SmtTerm.Apply f (__eo_to_smt a)) ≠
          SmtType.None :=
        ih hHeadApply hNN
      have hNotSel : ∀ s₀ d₀ i₀ j₀, f ≠ SmtTerm.DtSel s₀ d₀ i₀ j₀ := by
        intro s₀ d₀ i₀ j₀ hf
        subst f
        simp [qdsSmtApplyHead] at hHead
      have hNotTester : ∀ s₀ d₀ i₀, f ≠ SmtTerm.DtTester s₀ d₀ i₀ := by
        intro s₀ d₀ i₀ hf
        subst f
        simp [qdsSmtApplyHead] at hHead
      have hGeneric : generic_apply_type f (__eo_to_smt a) :=
        generic_apply_type_of_non_datatype_head hNotSel hNotTester
      have hApplyTypeNN : __smtx_typeof_apply (__smtx_typeof f)
          (__smtx_typeof (__eo_to_smt a)) ≠ SmtType.None := by
        rw [← hGeneric]
        exact hApplyNN
      rcases typeof_apply_non_none_cases hApplyTypeNN with
        ⟨A, B, hFun, hArg, hA, hB⟩
      rcases hFun with hFun | hFun <;> rw [hFun] <;> simp

@[simp] theorem qdsSmtApplyArgs_length (t : SmtTerm) :
    (qdsSmtApplyArgs t).length = qdsSmtNumApplyArgs t := by
  cases t with
  | Apply f a =>
      simp [qdsSmtApplyArgs, qdsSmtNumApplyArgs, qdsSmtApplyArgs_length f]
  | _ => rfl
termination_by sizeOf t

private theorem qds_smt_typeof_apply_of_head_cases
    {F X A B : SmtType}
    (hHead : F = SmtType.FunType A B ∨ F = SmtType.DtcAppType A B)
    (hX : X = A) (hA : A ≠ SmtType.None) :
    __smtx_typeof_apply F X = B := by
  rcases hHead with hHead | hHead
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq,
      hA]
  · rw [hHead, hX]
    simp [__smtx_typeof_apply, __smtx_typeof_guard, native_ite, native_Teq,
      hA]

private theorem qds_smt_dt_cons_chain_type_aux :
    ∀ (n : Nat) (t : SmtTerm) (s : native_String) (d : SmtDatatype)
      (i : native_Nat),
      qdsSmtNumApplyArgs t = n ->
      qdsSmtApplyHead t = SmtTerm.DtCons s d i ->
      __smtx_typeof t ≠ SmtType.None ->
      __smtx_typeof t =
        dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i
          (qdsSmtNumApplyArgs t) := by
  intro n
  induction n with
  | zero =>
      intro t s d i hN hHead hNN
      cases t <;> simp [qdsSmtNumApplyArgs, qdsSmtApplyHead] at hN hHead
      case DtCons s' d' i' =>
        rcases hHead with ⟨rfl, hEq⟩
        rcases hEq with ⟨rfl, rfl⟩
        rw [Smtm.typeof_dt_cons_eq]
        have hGuard :
            __smtx_typeof_guard_wf (SmtType.Datatype s' d')
                (__smtx_typeof_dt_cons_rec (SmtType.Datatype s' d')
                  (__smtx_dt_substitute s' d' d') i') =
              __smtx_typeof_dt_cons_rec (SmtType.Datatype s' d')
                (__smtx_dt_substitute s' d' d') i' :=
          smtx_typeof_guard_wf_of_non_none _ _
            (by simpa [Smtm.typeof_dt_cons_eq] using hNN)
        simp [hGuard, qdsSmtNumApplyArgs, dt_cons_applied_type_rec,
          typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec]
  | succ n ih =>
      intro t s d i hN hHead hNN
      cases t <;> simp [qdsSmtNumApplyArgs, qdsSmtApplyHead] at hN hHead
      case Apply f a =>
        have hHeadF : qdsSmtApplyHead f = SmtTerm.DtCons s d i := by
          simpa using hHead
        have hNotSel : ∀ s₀ d₀ i₀ j₀, f ≠ SmtTerm.DtSel s₀ d₀ i₀ j₀ := by
          intro s₀ d₀ i₀ j₀ hf
          subst f
          simp [qdsSmtApplyHead] at hHeadF
        have hNotTester : ∀ s₀ d₀ i₀, f ≠ SmtTerm.DtTester s₀ d₀ i₀ := by
          intro s₀ d₀ i₀ hf
          subst f
          simp [qdsSmtApplyHead] at hHeadF
        have hGeneric : generic_apply_type f a :=
          generic_apply_type_of_non_datatype_head hNotSel hNotTester
        have hApplyNN :
            __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof a) ≠
              SmtType.None := by
          unfold generic_apply_type at hGeneric
          rw [hGeneric] at hNN
          exact hNN
        rcases typeof_apply_non_none_cases hApplyNN with
          ⟨A, B, hHeadTy, hArg, hA, _hB⟩
        have hFunNN : __smtx_typeof f ≠ SmtType.None := by
          rcases hHeadTy with hHeadTy | hHeadTy <;> rw [hHeadTy] <;> simp
        have ihEq := ih f s d i hN hHeadF hFunNN
        have hLt : qdsSmtNumApplyArgs f <
            __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
          rcases hHeadTy with hHeadTy | hHeadTy
          · have hArgs := congrArg dt_cons_type_num_args hHeadTy
            rw [ihEq, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp [dt_cons_type_num_args] at hArgs
            omega
          · have hArgs := congrArg dt_cons_type_num_args hHeadTy
            rw [ihEq, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp [dt_cons_type_num_args] at hArgs
            omega
        let R := __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
          (qdsSmtNumApplyArgs f)
        let Rest := dt_cons_applied_type_rec s d
          (__smtx_dt_substitute s d d) i (Nat.succ (qdsSmtNumApplyArgs f))
        have hStep : dt_cons_applied_type_rec s d
              (__smtx_dt_substitute s d d) i (qdsSmtNumApplyArgs f) =
            SmtType.DtcAppType R Rest := by
          simpa [R, Rest] using dt_cons_applied_type_rec_step s d
            (__smtx_dt_substitute s d d) i (qdsSmtNumApplyArgs f) hLt
        have hArgR : __smtx_typeof a = R := by
          rcases hHeadTy with hHeadTy | hHeadTy
          · have hBad : SmtType.DtcAppType R Rest = SmtType.FunType A B :=
              (ihEq.trans hStep).symm.trans hHeadTy
            cases hBad
          · have hCmp : SmtType.DtcAppType R Rest = SmtType.DtcAppType A B :=
              (ihEq.trans hStep).symm.trans hHeadTy
            injection hCmp with hAeq _
            exact hArg.trans hAeq.symm
        have hRNN : R ≠ SmtType.None := by
          rw [← hArgR, hArg]
          exact hA
        have hApplyTy : __smtx_typeof (SmtTerm.Apply f a) = Rest := by
          rw [hGeneric]
          exact qds_smt_typeof_apply_of_head_cases (Or.inr (ihEq.trans hStep))
            hArgR hRNN
        simpa [qdsSmtNumApplyArgs, Rest] using hApplyTy

theorem qds_smt_dt_cons_chain_type
    {t : SmtTerm} {s : native_String} {d : SmtDatatype} {i : native_Nat}
    (hHead : qdsSmtApplyHead t = SmtTerm.DtCons s d i)
    (hNN : __smtx_typeof t ≠ SmtType.None) :
    __smtx_typeof t =
      dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i
        (qdsSmtNumApplyArgs t) :=
  qds_smt_dt_cons_chain_type_aux (qdsSmtNumApplyArgs t) t s d i rfl hHead hNN

private theorem qds_smt_dt_cons_arg_types_aux :
    ∀ (n : Nat) (t : SmtTerm) (s : native_String) (d : SmtDatatype)
      (i : native_Nat),
      qdsSmtNumApplyArgs t = n ->
      qdsSmtApplyHead t = SmtTerm.DtCons s d i ->
      __smtx_typeof t ≠ SmtType.None ->
      ∀ j, j < (qdsSmtApplyArgs t).length ->
        __smtx_typeof (qdsSmtApplyArgs t)[j]! =
          __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i j := by
  intro n
  induction n with
  | zero =>
      intro t s d i hN hHead hNN j hJ
      have : (qdsSmtApplyArgs t).length = 0 := by
        rw [qdsSmtApplyArgs_length, hN]
      omega
  | succ n ih =>
      intro t s d i hN hHead hNN j hJ
      cases t <;> simp [qdsSmtNumApplyArgs, qdsSmtApplyHead] at hN hHead
      case Apply f a =>
        have hHeadF : qdsSmtApplyHead f = SmtTerm.DtCons s d i := by
          simpa using hHead
        have hNotSel : ∀ s₀ d₀ i₀ j₀, f ≠ SmtTerm.DtSel s₀ d₀ i₀ j₀ := by
          intro s₀ d₀ i₀ j₀ hf
          subst f
          simp [qdsSmtApplyHead] at hHeadF
        have hNotTester : ∀ s₀ d₀ i₀, f ≠ SmtTerm.DtTester s₀ d₀ i₀ := by
          intro s₀ d₀ i₀ hf
          subst f
          simp [qdsSmtApplyHead] at hHeadF
        have hGeneric : generic_apply_type f a :=
          generic_apply_type_of_non_datatype_head hNotSel hNotTester
        have hApplyNN : __smtx_typeof_apply (__smtx_typeof f)
            (__smtx_typeof a) ≠ SmtType.None := by
          unfold generic_apply_type at hGeneric
          rw [hGeneric] at hNN
          exact hNN
        rcases typeof_apply_non_none_cases hApplyNN with
          ⟨A, B, hHeadTy, hArg, hA, _hB⟩
        have hFunNN : __smtx_typeof f ≠ SmtType.None := by
          rcases hHeadTy with hHeadTy | hHeadTy <;> rw [hHeadTy] <;> simp
        have hChain := qds_smt_dt_cons_chain_type hHeadF hFunNN
        have hLt : qdsSmtNumApplyArgs f <
            __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
          rcases hHeadTy with hHeadTy | hHeadTy
          · have hArgs := congrArg dt_cons_type_num_args hHeadTy
            rw [hChain, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp [dt_cons_type_num_args] at hArgs
            omega
          · have hArgs := congrArg dt_cons_type_num_args hHeadTy
            rw [hChain, dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
            simp [dt_cons_type_num_args] at hArgs
            omega
        let R := __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i
          (qdsSmtNumApplyArgs f)
        let Rest := dt_cons_applied_type_rec s d
          (__smtx_dt_substitute s d d) i (Nat.succ (qdsSmtNumApplyArgs f))
        have hStep : dt_cons_applied_type_rec s d
              (__smtx_dt_substitute s d d) i (qdsSmtNumApplyArgs f) =
            SmtType.DtcAppType R Rest := by
          simpa [R, Rest] using dt_cons_applied_type_rec_step s d
            (__smtx_dt_substitute s d d) i (qdsSmtNumApplyArgs f) hLt
        have hArgR : __smtx_typeof a = R := by
          rcases hHeadTy with hHeadTy | hHeadTy
          · have hBad : SmtType.DtcAppType R Rest = SmtType.FunType A B :=
              (hChain.trans hStep).symm.trans hHeadTy
            cases hBad
          · have hCmp : SmtType.DtcAppType R Rest = SmtType.DtcAppType A B :=
              (hChain.trans hStep).symm.trans hHeadTy
            injection hCmp with hAeq _
            exact hArg.trans hAeq.symm
        rw [show qdsSmtApplyArgs (SmtTerm.Apply f a) =
          qdsSmtApplyArgs f ++ [a] from rfl] at hJ ⊢
        by_cases hLast : j = (qdsSmtApplyArgs f).length
        · subst j
          simpa [R] using hArgR
        · have hJ' : j < qdsSmtNumApplyArgs f + 1 := by
            simpa using hJ
          have hLast' : j ≠ qdsSmtNumApplyArgs f := by
            simpa using hLast
          have hPrefix' : j < qdsSmtNumApplyArgs f := by omega
          have hPrefix : j < (qdsSmtApplyArgs f).length := by
            simpa using hPrefix'
          have hGet : (qdsSmtApplyArgs f ++ [a])[j]! =
              (qdsSmtApplyArgs f)[j]! := by
            rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
              List.getElem?_append_left hPrefix]
          rw [hGet]
          exact ih f s d i hN hHeadF hFunNN j hPrefix

theorem qds_smt_dt_cons_arg_types
    {t : SmtTerm} {s : native_String} {d : SmtDatatype} {i : native_Nat}
    (hHead : qdsSmtApplyHead t = SmtTerm.DtCons s d i)
    (hNN : __smtx_typeof t ≠ SmtType.None) :
    ∀ j, j < (qdsSmtApplyArgs t).length ->
      __smtx_typeof (qdsSmtApplyArgs t)[j]! =
        __smtx_ret_typeof_sel_rec (__smtx_dt_substitute s d d) i j :=
  qds_smt_dt_cons_arg_types_aux (qdsSmtNumApplyArgs t) t s d i rfl
    hHead hNN

theorem qds_smt_dt_cons_num_args_of_datatype
    {t : SmtTerm} {s : native_String} {d : SmtDatatype} {i : native_Nat}
    (hHead : qdsSmtApplyHead t = SmtTerm.DtCons s d i)
    (hTy : __smtx_typeof t = SmtType.Datatype s d) :
    qdsSmtNumApplyArgs t =
      __smtx_dt_num_sels (__smtx_dt_substitute s d d) i := by
  have hNN : __smtx_typeof t ≠ SmtType.None := by rw [hTy]; simp
  have hChain := qds_smt_dt_cons_chain_type hHead hNN
  have hRes : dt_cons_applied_type_rec s d (__smtx_dt_substitute s d d) i
      (qdsSmtNumApplyArgs t) = SmtType.Datatype s d := hChain.symm.trans hTy
  have hArgsZero : __smtx_dt_num_sels (__smtx_dt_substitute s d d) i -
      qdsSmtNumApplyArgs t = 0 := by
    have hArgs := congrArg dt_cons_type_num_args hRes
    rw [dt_cons_type_num_args_dt_cons_applied_type_rec] at hArgs
    simpa [dt_cons_type_num_args] using hArgs
  have hLe : qdsSmtNumApplyArgs t ≤
      __smtx_dt_num_sels (__smtx_dt_substitute s d d) i :=
    dt_cons_applied_type_rec_non_none_implies_le s d
      (__smtx_dt_substitute s d d) i (qdsSmtNumApplyArgs t)
      (by rw [hRes]; simp)
  exact Nat.le_antisymm hLe (Nat.sub_eq_zero_iff_le.mp hArgsZero)

/-! A datatype-constructor spine has a particularly small EO type-state
machine: it is either still waiting for fields, has reached the constructor's
datatype, or is stuck.  Recording that invariant lets us use the well-formed
final type to rule out both incomplete and over-applied spines. -/

private inductive DcsTypeChain (s : native_String) (d : Datatype) : Term -> Prop where
  | base : DcsTypeChain s d (Term.DatatypeType s d)
  | field {A B : Term} : DcsTypeChain s d B ->
      DcsTypeChain s d (Term.DtcAppType A B)
  | stuck : DcsTypeChain s d Term.Stuck

mutual
  private theorem dcs_type_chain_cons (s : native_String) (d : Datatype)
      (c : DatatypeCons) (tail : Datatype) :
      DcsTypeChain s d
        (__eo_typeof_dt_cons_rec (Term.DatatypeType s d)
          (Datatype.sum c tail) 0) := by
    cases c with
    | unit =>
        simpa [__eo_typeof_dt_cons_rec] using (DcsTypeChain.base (s := s) (d := d))
    | cons A c =>
        simpa [__eo_typeof_dt_cons_rec] using
          (DcsTypeChain.field (dcs_type_chain_cons s d c tail))

  private theorem dcs_type_chain_rec (s : native_String) (d : Datatype) :
      ∀ (body : Datatype) (i : native_Nat),
        DcsTypeChain s d
          (__eo_typeof_dt_cons_rec (Term.DatatypeType s d) body i)
    | Datatype.null, i => by
        simpa [__eo_typeof_dt_cons_rec] using
          (DcsTypeChain.stuck (s := s) (d := d))
    | Datatype.sum c tail, 0 => dcs_type_chain_cons s d c tail
    | Datatype.sum c tail, Nat.succ i => by
        simpa [__eo_typeof_dt_cons_rec] using dcs_type_chain_rec s d tail i
end

private theorem dcs_type_chain_apply_var
    {s : native_String} {d : Datatype} {F A : Term}
    (h : DcsTypeChain s d F) :
    DcsTypeChain s d
      (__eo_typeof_apply F A) := by
  cases h with
  | base =>
      cases A <;> simpa [__eo_typeof_apply] using
        (DcsTypeChain.stuck (s := s) (d := d))
  | @field U V hTail =>
      by_cases hAStuck : A = Term.Stuck
      · subst A
        simpa [__eo_typeof_apply] using
          (DcsTypeChain.stuck (s := s) (d := d))
      · have hApply : __eo_typeof_apply (Term.DtcAppType U V) A =
            __eo_requires U A V := by
          cases A <;> simp_all [__eo_typeof_apply]
        rw [hApply]
        cases hEq : native_teq U A <;>
          cases hOk : native_not (native_teq U Term.Stuck) <;>
            simp [__eo_requires, native_ite, hEq, hOk]
        · exact DcsTypeChain.stuck
        · exact DcsTypeChain.stuck
        · exact DcsTypeChain.stuck
        · exact hTail
  | stuck =>
      cases A <;> simpa [__eo_typeof_apply] using
        (DcsTypeChain.stuck (s := s) (d := d))

private def qdsEoApplyHead : Term -> Term
  | Term.Apply f _ => qdsEoApplyHead f
  | t => t

private theorem dcs_typeof_apply_eq_of_head
    (f x : Term) {s : native_String} {d : Datatype} {i : native_Nat}
    (hHead : qdsEoApplyHead f = Term.DtCons s d i) :
    __eo_typeof (Term.Apply f x) =
      __eo_typeof_apply (__eo_typeof f) (__eo_typeof x) := by
  cases f <;> try rfl
  case __eo_List_cons => cases hHead
  case UOp op =>
    cases op <;> try rfl
    all_goals
      change Term.UOp _ = Term.DtCons _ _ _ at hHead
      cases hHead
  case UOp1 op j =>
    cases op <;> try rfl
    all_goals
      change Term.UOp1 _ _ = Term.DtCons _ _ _ at hHead
      cases hHead
  case UOp2 op j k =>
    cases op <;> try rfl
    all_goals
      change Term.UOp2 _ _ _ = Term.DtCons _ _ _ at hHead
      cases hHead
  case Apply f a =>
    cases f <;> try rfl
    case UOp op =>
      cases op <;> try rfl
      all_goals
        change Term.UOp _ = Term.DtCons _ _ _ at hHead
        cases hHead
    case UOp1 op j =>
      cases op <;> try rfl
      all_goals
        change Term.UOp1 _ _ = Term.DtCons _ _ _ at hHead
        cases hHead
    case FunType =>
      change Term.FunType = Term.DtCons _ _ _ at hHead
      cases hHead
    case Apply f' b =>
      cases f' <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        all_goals
          change Term.UOp _ = Term.DtCons _ _ _ at hHead
          cases hHead

private theorem dcs_type_chain {c : Term} (hs : DCS c) :
    ∃ (s : native_String) (d : Datatype) (i : native_Nat),
      qdsEoApplyHead c = Term.DtCons s d i ∧
      DcsTypeChain s d (__eo_typeof c) := by
  induction hs with
  | head s d i =>
      exact ⟨s, d, i, rfl,
        dcs_type_chain_rec s d (__eo_dt_substitute s d d) i⟩
  | @apply c sx A hs hA ih =>
      obtain ⟨s, d, i, hHead, hChain⟩ := ih
      refine ⟨s, d, i, hHead, ?_⟩
      rw [dcs_typeof_apply_eq_of_head c
        (Term.Var (Term.String sx) A) hHead]
      exact dcs_type_chain_apply_var hChain

private theorem dcs_type_chain_wf_base
    {s : native_String} {d : Datatype} {T : Term}
    (h : DcsTypeChain s d T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    T = Term.DatatypeType s d := by
  cases h with
  | base => rfl
  | @field A B hTail =>
      exfalso
      cases hA : __eo_to_smt_type A <;>
        cases hB : __eo_to_smt_type B <;>
          simp [__eo_to_smt_type, __smtx_typeof_guard,
            __smtx_type_wf, __smtx_type_wf_component,
            __smtx_type_wf_rec, native_and, native_ite, native_Teq,
            hA, hB] at hWf
  | stuck =>
      exfalso
      simp [__eo_to_smt_type, __smtx_type_wf,
        __smtx_type_wf_component, __smtx_type_wf_rec, native_and] at hWf

private theorem dcs_apply_head_non_stuck
    {c : Term} (hs : DCS c)
    (hFinal : __eo_typeof c ≠ Term.Stuck) :
    __eo_typeof (qdsEoApplyHead c) ≠ Term.Stuck := by
  induction hs with
  | head s d i => exact hFinal
  | @apply c sx A hs hA ih =>
      apply ih
      intro hStuck
      apply hFinal
      obtain ⟨s, d, i, hHead, hChain⟩ := dcs_type_chain hs
      rw [dcs_typeof_apply_eq_of_head c
        (Term.Var (Term.String sx) A) hHead]
      rw [hStuck]
      cases A <;> rfl

private theorem dcs_smt_rec_non_none_of_eo_rec_non_stuck
    (T : Term) (base : SmtType)
    (hBase : base ≠ SmtType.None) :
    ∀ (body : Datatype) (i : native_Nat),
      __eo_typeof_dt_cons_rec T body i ≠ Term.Stuck ->
      __smtx_typeof_dt_cons_rec base
          (__eo_to_smt_datatype body) i ≠ SmtType.None
  | Datatype.null, i, h => by
      exfalso
      apply h
      cases T <;> cases i <;> simp [__eo_typeof_dt_cons_rec]
  | Datatype.sum c tail, 0, h => by
      cases c with
      | unit =>
          simpa [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec] using hBase
      | cons A c =>
          simp [__eo_to_smt_datatype, __eo_to_smt_datatype_cons,
            __smtx_typeof_dt_cons_rec]
  | Datatype.sum c tail, Nat.succ i, h => by
      have hTail : __eo_typeof_dt_cons_rec T tail i ≠ Term.Stuck := by
        cases T <;> simpa [__eo_typeof_dt_cons_rec] using h
      simpa [__eo_to_smt_datatype, __smtx_typeof_dt_cons_rec] using
        dcs_smt_rec_non_none_of_eo_rec_non_stuck T base hBase tail i hTail

private theorem dcs_var_translation
    (sx : native_String) (A : Term)
    (hWf : __smtx_type_wf (__eo_to_smt_type A) = true) :
    RuleProofs.eo_has_smt_translation
      (Term.Var (Term.String sx) A) := by
  unfold RuleProofs.eo_has_smt_translation
  change __smtx_typeof_guard_wf (__eo_to_smt_type A)
      (__eo_to_smt_type A) ≠ SmtType.None
  have hNN : __eo_to_smt_type A ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hWf
    simp [__smtx_type_wf, __smtx_type_wf_component,
      __smtx_type_wf_rec, native_and] at hWf
  rw [show __smtx_typeof_guard_wf (__eo_to_smt_type A)
      (__eo_to_smt_type A) = __eo_to_smt_type A by
    unfold __smtx_typeof_guard_wf
    rw [hWf]
    rfl]
  exact hNN

private theorem dcs_translation_of_head
    {c : Term} (hs : DCS c)
    (hHead : RuleProofs.eo_has_smt_translation (qdsEoApplyHead c))
    (hFinal : __eo_typeof c ≠ Term.Stuck) :
    RuleProofs.eo_has_smt_translation c := by
  induction hs with
  | head s d i => exact hHead
  | @apply c sx A hs hA ih =>
      have hPrefix : __eo_typeof c ≠ Term.Stuck := by
        intro hStuck
        apply hFinal
        obtain ⟨s, d, i, hRoot, hChain⟩ := dcs_type_chain hs
        rw [dcs_typeof_apply_eq_of_head c
          (Term.Var (Term.String sx) A) hRoot]
        rw [hStuck]
        cases A <;> rfl
      have hHead' : RuleProofs.eo_has_smt_translation (qdsEoApplyHead c) := by
        simpa [qdsEoApplyHead] using hHead
      exact SubstituteTranslatabilitySupport.eo_has_smt_translation_apply_of_head_arg_translation_and_type
        c (Term.Var (Term.String sx) A) (ih hHead' hPrefix)
        (dcs_var_translation sx A hA) hFinal

theorem dcs_translation {c T : Term} (hs : DCS c)
    (hEq : __eo_typeof c = T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    RuleProofs.eo_has_smt_translation c := by
  subst T
  obtain ⟨s, d, i, hHead, hChain⟩ := dcs_type_chain hs
  have hBase := dcs_type_chain_wf_base hChain hWf
  have hFinal : __eo_typeof c ≠ Term.Stuck := by rw [hBase]; simp
  have hHeadNe := dcs_apply_head_non_stuck hs hFinal
  rw [hHead] at hHeadNe
  have hReserved : native_reserved_datatype_name s = false := by
    have hWf' := hWf
    rw [hBase] at hWf'
    cases hRes : native_reserved_datatype_name s <;>
      simp [__eo_to_smt_type, native_ite, hRes,
        __smtx_type_wf, __smtx_type_wf_component,
        __smtx_type_wf_rec, native_and] at hWf' ⊢
  let base := SmtType.Datatype s (__eo_to_smt_datatype d)
  have hBaseWf : __smtx_type_wf base = true := by
    rw [hBase] at hWf
    simpa [base, __eo_to_smt_type, native_ite, hReserved] using hWf
  have hRawNN :
      __smtx_typeof_dt_cons_rec base
          (__smtx_dt_substitute s (__eo_to_smt_datatype d)
            (__eo_to_smt_datatype d)) i ≠ SmtType.None := by
    have hDtWf :
        __smtx_dt_wf_rec
          (__smtx_dt_substitute s (__eo_to_smt_datatype d)
            (__eo_to_smt_datatype d)) (__eo_to_smt_datatype d) = true :=
      Smtm.datatype_wf_rec_of_type_wf (by simpa [base] using hBaseWf)
    have hValid : TranslationProofs.eo_datatype_valid_rec [s] d :=
      TranslationProofs.eo_datatype_valid_of_smt_self_wf_rec s d hDtWf
    have hNoDt : Smtm.noDtDt s (__eo_to_smt_datatype d) = true :=
      Smtm.noDtDt_of_no_alias s (__eo_to_smt_datatype d)
        (native_reflist_insert native_reflist_nil s)
        (by simp [native_reflist_contains, native_reflist_insert])
        (Smtm.datatype_no_alias_of_type_wf (by simpa [base] using hBaseWf))
    have hSubEq :
        __eo_to_smt_datatype (__eo_dt_substitute s d d) =
          __smtx_dt_substitute s (__eo_to_smt_datatype d)
            (__eo_to_smt_datatype d) :=
      TranslationProofs.corrDt s d d [s] hValid hValid hNoDt
    rw [← hSubEq]
    exact dcs_smt_rec_non_none_of_eo_rec_non_stuck
      (Term.DatatypeType s d) base (by simp [base])
      (__eo_dt_substitute s d d) i hHeadNe
  have hRootTrans : RuleProofs.eo_has_smt_translation
      (Term.DtCons s d i) := by
    unfold RuleProofs.eo_has_smt_translation
    change __smtx_typeof
        (native_ite (native_reserved_datatype_name s) SmtTerm.None
          (SmtTerm.DtCons s (__eo_to_smt_datatype d) i)) ≠ SmtType.None
    rw [hReserved]
    change __smtx_typeof_guard_wf
      (SmtType.Datatype s (__eo_to_smt_datatype d))
      (__smtx_typeof_dt_cons_rec
        (SmtType.Datatype s (__eo_to_smt_datatype d))
        (__smtx_dt_substitute s (__eo_to_smt_datatype d)
          (__eo_to_smt_datatype d)) i) ≠ SmtType.None
    unfold __smtx_typeof_guard_wf
    rw [show __smtx_type_wf
      (SmtType.Datatype s (__eo_to_smt_datatype d)) = true by
        simpa [base] using hBaseWf]
    exact hRawNN
  apply dcs_translation_of_head hs
  · simpa [hHead] using hRootTrans
  · exact hFinal

private theorem qds_stuck_type_not_wf :
    __smtx_type_wf (__eo_to_smt_type Term.Stuck) ≠ true := by
  native_decide

private theorem qds_eo_typeof_apply_stuck_head (V : Term) :
    __eo_typeof_apply Term.Stuck V = Term.Stuck := by
  cases V <;> simp [__eo_typeof_apply]

private theorem qds_eo_typeof_apply_unit_tuple_stuck (V : Term) :
    __eo_typeof_apply (Term.UOp UserOp.UnitTuple) V = Term.Stuck := by
  cases V <;> simp [__eo_typeof_apply]

private theorem qds_eo_typeof_tuple_partial_var_stuck
    (s : native_String) (U : Term) :
    __eo_typeof
        (Term.Apply (Term.UOp UserOp.tuple)
          (Term.Var (Term.String s) U)) = Term.Stuck := by
  change __eo_typeof_apply Term.Stuck U = Term.Stuck
  exact qds_eo_typeof_apply_stuck_head U

private theorem qds_eo_typeof_tuple_unit_apply_var_stuck
    (s : native_String) (U : Term) :
    __eo_typeof
        (Term.Apply (Term.UOp UserOp.tuple_unit)
          (Term.Var (Term.String s) U)) = Term.Stuck := by
  change __eo_typeof_apply (Term.UOp UserOp.UnitTuple) U = Term.Stuck
  exact qds_eo_typeof_apply_unit_tuple_stuck U

private theorem qds_eo_typeof_apply_tuple_type_stuck (T U V : Term) :
    __eo_typeof_apply
        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U) V =
      Term.Stuck := by
  cases V <;> simp [__eo_typeof_apply]

private theorem qds_eo_typeof_apply_requires_tuple_type_stuck
    (P T U V : Term) :
    __eo_typeof_apply
        (__eo_requires P (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) T) U)) V =
      Term.Stuck := by
  cases hP : native_teq P (Term.Boolean true) <;>
    cases hStuck : native_not (native_teq P Term.Stuck) <;>
      simp [__eo_requires, native_ite, hP, hStuck,
        qds_eo_typeof_apply_tuple_type_stuck,
        qds_eo_typeof_apply_stuck_head]

private theorem qds_eo_typeof_apply_typeof_tuple_stuck
    (T U V : Term) :
    __eo_typeof_apply (__eo_typeof_tuple T U) V = Term.Stuck := by
  unfold __eo_typeof_tuple
  split
  · cases V <;> simp [__eo_typeof_apply]
  · cases V <;> simp [__eo_typeof_apply]
  · exact qds_eo_typeof_apply_requires_tuple_type_stuck
      (__eo_is_ok (__eo_list_len (Term.UOp UserOp.Tuple) U)) T U V

private theorem tcs_apply3_stuck {c : Term} (hs : TCS c) :
    ∀ (a₀ a₁ a₂ : Term),
      __eo_typeof (Term.Apply (Term.Apply (Term.Apply c a₀) a₁) a₂) =
        Term.Stuck := by
  induction hs with
  | head =>
      intro a₀ a₁ a₂
      change __eo_typeof_apply
          (__eo_typeof_tuple (__eo_typeof a₀) (__eo_typeof a₁))
          (__eo_typeof a₂) = Term.Stuck
      exact qds_eo_typeof_apply_typeof_tuple_stuck _ _ _
  | @apply c s T hs hT ih =>
      intro a₀ a₁ a₂
      change __eo_typeof_apply
          (__eo_typeof
            (Term.Apply (Term.Apply (Term.Apply c
              (Term.Var (Term.String s) T)) a₀) a₁))
          (__eo_typeof a₂) = Term.Stuck
      rw [ih (Term.Var (Term.String s) T) a₀ a₁]
      exact qds_eo_typeof_apply_stuck_head (__eo_typeof a₂)

private def qdsAppHead : Term -> Term
  | Term.Apply f _ => qdsAppHead f
  | t => t

private theorem ucs_app_head {c : Term} (hs : UCS c) :
    qdsAppHead c = Term.UOp UserOp.tuple_unit := by
  induction hs with
  | head => rfl
  | apply hs hT ih => exact ih

private theorem qds_eo_typeof_unit_head_extra_application_stuck :
    ∀ (g x : Term),
      qdsAppHead g = Term.UOp UserOp.tuple_unit ->
      g ≠ Term.UOp UserOp.tuple_unit ->
      __eo_typeof (Term.Apply g x) = Term.Stuck
  | Term.Apply f y, x, hHead, _hNe => by
      cases f with
      | UOp op =>
          cases op with
          | tuple_unit =>
              change __eo_typeof_apply
                  (__eo_typeof_apply (Term.UOp UserOp.UnitTuple)
                    (__eo_typeof y)) (__eo_typeof x) = Term.Stuck
              rw [qds_eo_typeof_apply_unit_tuple_stuck]
              exact qds_eo_typeof_apply_stuck_head (__eo_typeof x)
          | _ => simp [qdsAppHead] at hHead
      | Apply f' y' =>
          cases f' with
          | UOp op =>
              cases op with
              | tuple_unit =>
                  change __eo_typeof_apply
                      (__eo_typeof_apply
                        (__eo_typeof_apply (Term.UOp UserOp.UnitTuple)
                          (__eo_typeof y')) (__eo_typeof y))
                      (__eo_typeof x) = Term.Stuck
                  rw [qds_eo_typeof_apply_unit_tuple_stuck,
                    qds_eo_typeof_apply_stuck_head]
                  exact qds_eo_typeof_apply_stuck_head (__eo_typeof x)
              | _ => simp [qdsAppHead] at hHead
          | Apply f'' z =>
              have hInner :
                  __eo_typeof
                    (Term.Apply (Term.Apply (Term.Apply f'' z) y') y) =
                      Term.Stuck :=
                qds_eo_typeof_unit_head_extra_application_stuck
                  (Term.Apply (Term.Apply f'' z) y') y
                  (by simpa [qdsAppHead] using hHead)
                  (by intro h; cases h)
              change __eo_typeof_apply
                  (__eo_typeof
                    (Term.Apply (Term.Apply (Term.Apply f'' z) y') y))
                  (__eo_typeof x) = Term.Stuck
              rw [hInner]
              exact qds_eo_typeof_apply_stuck_head (__eo_typeof x)
          | _ => cases hHead
      | _ => cases hHead
  | Term.UOp op, x, hHead, hNe => by
      exact False.elim (hNe (by simpa [qdsAppHead] using hHead))
  | Term.UOp1 _ _, x, hHead, _hNe => by cases hHead
  | Term.UOp2 _ _ _, x, hHead, _hNe => by cases hHead
  | Term.UOp3 _ _ _ _, x, hHead, _hNe => by cases hHead
  | Term.__eo_List, x, hHead, _hNe => by cases hHead
  | Term.__eo_List_nil, x, hHead, _hNe => by cases hHead
  | Term.__eo_List_cons, x, hHead, _hNe => by cases hHead
  | Term.Bool, x, hHead, _hNe => by cases hHead
  | Term.Boolean _, x, hHead, _hNe => by cases hHead
  | Term.Numeral _, x, hHead, _hNe => by cases hHead
  | Term.Rational _, x, hHead, _hNe => by cases hHead
  | Term.String _, x, hHead, _hNe => by cases hHead
  | Term.Binary _ _, x, hHead, _hNe => by cases hHead
  | Term.Type, x, hHead, _hNe => by cases hHead
  | Term.Stuck, x, hHead, _hNe => by cases hHead
  | Term.FunType, x, hHead, _hNe => by cases hHead
  | Term.Var _ _, x, hHead, _hNe => by cases hHead
  | Term.DatatypeType _ _, x, hHead, _hNe => by cases hHead
  | Term.DatatypeTypeRef _, x, hHead, _hNe => by cases hHead
  | Term.DtcAppType _ _, x, hHead, _hNe => by cases hHead
  | Term.DtCons _ _ _, x, hHead, _hNe => by cases hHead
  | Term.DtSel _ _ _ _, x, hHead, _hNe => by cases hHead
  | Term.USort _, x, hHead, _hNe => by cases hHead
  | Term.UConst _ _, x, hHead, _hNe => by cases hHead

private theorem ucs_apply_var_stuck {c : Term} (hs : UCS c)
    (s : native_String) (U : Term) :
    __eo_typeof (Term.Apply c (Term.Var (Term.String s) U)) =
      Term.Stuck := by
  cases hs with
  | head => exact qds_eo_typeof_tuple_unit_apply_var_stuck s U
  | @apply c s₀ U₀ hs hU₀ =>
      exact qds_eo_typeof_unit_head_extra_application_stuck
        (Term.Apply c (Term.Var (Term.String s₀) U₀))
        (Term.Var (Term.String s) U)
        (by simpa [qdsAppHead] using ucs_app_head hs)
        (by intro h; cases h)

theorem tcs_full {c T : Term} (hs : TCS c)
    (hEq : __eo_typeof c = T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    ∃ (s₁ : native_String) (U₁ : Term) (s₂ : native_String) (U₂ : Term),
      c = Term.Apply
        (Term.Apply (Term.UOp UserOp.tuple) (Term.Var (Term.String s₁) U₁))
        (Term.Var (Term.String s₂) U₂) ∧
      __smtx_type_wf (__eo_to_smt_type U₁) = true ∧
      __smtx_type_wf (__eo_to_smt_type U₂) = true := by
  subst T
  cases hs with
  | head =>
      exact False.elim (qds_stuck_type_not_wf hWf)
  | @apply c s₂ U₂ hs hU₂ =>
      cases hs with
      | head =>
          rw [qds_eo_typeof_tuple_partial_var_stuck] at hWf
          exact False.elim (qds_stuck_type_not_wf hWf)
      | @apply c s₁ U₁ hs hU₁ =>
          cases hs with
          | head => exact ⟨s₁, U₁, s₂, U₂, rfl, hU₁, hU₂⟩
          | @apply c s₀ U₀ hs hU₀ =>
              have hStuck := tcs_apply3_stuck hs
                (Term.Var (Term.String s₀) U₀)
                (Term.Var (Term.String s₁) U₁)
                (Term.Var (Term.String s₂) U₂)
              rw [hStuck] at hWf
              exact False.elim (qds_stuck_type_not_wf hWf)

theorem ucs_full {c T : Term} (hs : UCS c)
    (hEq : __eo_typeof c = T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    c = Term.UOp UserOp.tuple_unit := by
  subst T
  cases hs with
  | head => rfl
  | @apply c s U hs hU =>
      rw [ucs_apply_var_stuck hs s U] at hWf
      exact False.elim (qds_stuck_type_not_wf hWf)

private theorem qds_requires_true_cases (P X : Term) :
    __eo_requires P (Term.Boolean true) X = Term.Stuck ∨
      __eo_requires P (Term.Boolean true) X = X := by
  unfold __eo_requires
  cases hEq : native_teq P (Term.Boolean true) <;>
    cases hOk : native_not (native_teq P Term.Stuck) <;>
      simp [native_ite, hEq, hOk]

private theorem qds_typeof_tuple_cases (A B : Term) :
    __eo_typeof_tuple A B = Term.Stuck ∨
      __eo_typeof_tuple A B =
        Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B := by
  by_cases hA : A = Term.Stuck
  · subst A
    exact Or.inl rfl
  by_cases hB : B = Term.Stuck
  · subst B
    cases A <;> simp_all [__eo_typeof_tuple]
  have hDef : __eo_typeof_tuple A B =
      __eo_requires (__eo_is_ok (__eo_list_len (Term.UOp UserOp.Tuple) B))
        (Term.Boolean true)
        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B) := by
    cases A <;> cases B <;> simp_all [__eo_typeof_tuple]
  rw [hDef]
  exact qds_requires_true_cases _ _

theorem qds_typeof_tuple_eq_of_wf
    (A B : Term)
    (hWf : __smtx_type_wf (__eo_to_smt_type (__eo_typeof_tuple A B)) = true) :
    __eo_typeof_tuple A B =
      Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B := by
  rcases qds_typeof_tuple_cases A B with hStuck | hTuple
  · rw [hStuck] at hWf
    exact False.elim (qds_stuck_type_not_wf hWf)
  · exact hTuple

private theorem qds_smt_type_tuple_datatype_of_wf
    {A B : SmtType}
    (hWf : __smtx_type_wf (__eo_to_smt_type_tuple A B) = true) :
    ∃ d, __eo_to_smt_type_tuple A B =
      SmtType.Datatype (native_string_lit "@Tuple") d := by
  cases B <;> simp [__eo_to_smt_type_tuple, __smtx_type_wf,
    __smtx_type_wf_rec, native_and] at hWf ⊢
  case Datatype s d =>
    by_cases hs : s = native_string_lit "@Tuple"
    · subst s
      cases d with
      | null => simp [__smtx_type_wf_rec] at hWf
      | sum c rest =>
          cases rest with
          | null =>
              by_cases hComp :
                  (native_inhabited_type A = true ∧
                    __smtx_type_wf_rec A A = true) ∧
                      __smtx_type_no_alias_rec native_reflist_nil A = true
              · exact ⟨
                  SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null,
                  by
                    simp [hComp.1.1, hComp.1.2, hComp.2,
                      native_streq, native_ite]⟩
              · exfalso
                simp [hComp, __smtx_type_wf_rec, native_ite] at hWf
          | sum c' rest' => simp [__smtx_type_wf_rec] at hWf
    · cases d with
      | null => simp [__smtx_type_wf_rec] at hWf
      | sum c rest =>
          cases rest <;>
            simp [hs, __smtx_type_wf_rec, native_streq, native_ite] at hWf

private theorem qds_smt_type_tuple_shape_of_wf
    {A B : SmtType}
    (hWf : __smtx_type_wf (__eo_to_smt_type_tuple A B) = true) :
    ∃ c : SmtDatatypeCons,
      B = SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum c SmtDatatype.null) ∧
      __eo_to_smt_type_tuple A B =
        SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null) := by
  cases B <;> simp [__eo_to_smt_type_tuple, __smtx_type_wf,
    __smtx_type_wf_rec, native_and] at hWf ⊢
  case Datatype s tailD =>
    by_cases hs : s = native_string_lit "@Tuple"
    · subst s
      cases tailD with
      | null => simp [__smtx_type_wf_rec] at hWf
      | sum c rest =>
          cases rest with
          | null =>
              by_cases hComp :
                  (native_inhabited_type A = true ∧
                    __smtx_type_wf_rec A A = true) ∧
                      __smtx_type_no_alias_rec native_reflist_nil A = true
              · exact ⟨c, ⟨rfl, rfl⟩, by
                  simp [hComp.1.1, hComp.1.2, hComp.2,
                    native_streq, native_ite]⟩
              · exfalso
                simp [hComp, __smtx_type_wf_rec, native_ite] at hWf
          | sum c' rest' => simp [__smtx_type_wf_rec] at hWf
    · cases tailD with
      | null => simp [__smtx_type_wf_rec] at hWf
      | sum c rest =>
          cases rest <;>
            simp [hs, __smtx_type_wf_rec, native_streq, native_ite] at hWf

theorem qds_tuple_type_shape_of_wf
    (A B : Term)
    (hWf : __smtx_type_wf
      (__eo_to_smt_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B)) = true) :
    ∃ c : SmtDatatypeCons,
      __eo_to_smt_type B =
          SmtType.Datatype (native_string_lit "@Tuple")
            (SmtDatatype.sum c SmtDatatype.null) ∧
      __eo_to_smt_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) A) B) =
        SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum
            (SmtDatatypeCons.cons (__eo_to_smt_type A) c)
            SmtDatatype.null) := by
  let raw := __eo_to_smt_type_tuple (__eo_to_smt_type A) (__eo_to_smt_type B)
  have hGate : __smtx_type_wf raw = true := by
    cases hRawWf : __smtx_type_wf raw
    · exfalso
      rw [TranslationProofs.eo_to_smt_type_tuple_step] at hWf
      change __smtx_type_wf
        (native_ite (__smtx_type_wf raw) raw SmtType.None) = true at hWf
      rw [hRawWf] at hWf
      exact False.elim ((show __smtx_type_wf SmtType.None ≠ true by
        native_decide) hWf)
    · rfl
  obtain ⟨c, hTail, hRaw⟩ := qds_smt_type_tuple_shape_of_wf hGate
  refine ⟨c, hTail, ?_⟩
  rw [TranslationProofs.eo_to_smt_type_tuple_step]
  rw [show __smtx_type_wf raw = true from hGate]
  simpa [raw, native_ite] using hRaw

theorem qds_tuple_fields_no_free :
    ∀ {T : Term} {c : SmtDatatypeCons},
      __eo_to_smt_type T =
          SmtType.Datatype (native_string_lit "@Tuple")
            (SmtDatatype.sum c SmtDatatype.null) ->
        Smtm.hasFreeDtc (native_string_lit "@Tuple")
          native_reflist_nil c = false
  | T, c, hT => by
      rcases TranslationProofs.eo_to_smt_type_eq_tuple_datatype hT with
        hUnit | hCons
      · rcases hUnit with ⟨rfl, hC⟩
        injection hC with hC'
        subst c
        simp [Smtm.hasFreeDtc]
      · rcases hCons with ⟨head, tail, tailC, rfl, hTail, hC⟩
        injection hC with hC'
        subst c
        have hHeadFree :=
          TranslationProofs.hasFreeTy_reserved_of_translate
            (native_string_lit "@Tuple") (by native_decide) head
              native_reflist_nil
        have hTailFree := qds_tuple_fields_no_free hTail
        cases hHeadTy : __eo_to_smt_type head <;>
          simp [Smtm.hasFreeDtc, hHeadTy] at hHeadFree ⊢
        case TypeRef s =>
          have hs : s ≠ native_string_lit "@Tuple" := by
            intro hs
            subst s
            exact TranslationProofs.eo_to_smt_type_ne_tuple_typeref head hHeadTy
          simp [Smtm.hasFreeDtc, native_streq, hs, hTailFree,
            native_or, native_and, native_not, native_reflist_contains]
        all_goals simp_all [Smtm.hasFreeDtc, native_or]
termination_by T c hT => T

theorem qds_tuple_type_substitute_noop
    (T : SmtType) (d : SmtDatatype)
    (hNotTuple : T ≠ SmtType.TypeRef (native_string_lit "@Tuple"))
    (hFree : Smtm.hasFreeTy (native_string_lit "@Tuple")
      native_reflist_nil T = false) :
    __smtx_type_substitute (native_string_lit "@Tuple") d T = T := by
  cases T with
  | TypeRef s =>
      have hs : s ≠ native_string_lit "@Tuple" := by
        intro hs
        subst s
        exact hNotTuple rfl
      simp [__smtx_type_substitute, native_ite, native_streq, hs, hs.symm]
  | _ =>
      exact Smtm.subst_noop_no_free_ty (native_string_lit "@Tuple") _ d
        native_reflist_nil (by intro s h; cases h) (by native_decide) hFree

private theorem qds_tuple_ret_type_wf :
    ∀ (c : SmtDatatypeCons) (j : native_Nat),
      __smtx_dt_cons_wf_rec c c = true ->
      __smtx_dt_cons_no_alias_rec
        (native_reflist_insert native_reflist_nil
          (native_string_lit "@Tuple")) c = true ->
      j < __smtx_dtc_num_sels c ->
      __smtx_type_wf
        (__smtx_ret_typeof_sel_rec
          (SmtDatatype.sum c SmtDatatype.null) native_nat_zero j) = true
  | SmtDatatypeCons.unit, j, hWf, hNoAlias, hJ => by
      simp [__smtx_dtc_num_sels] at hJ
  | SmtDatatypeCons.cons U c, 0, hWf, hNoAlias, hJ => by
      have hParts : native_inhabited_type U = true ∧
          __smtx_type_wf_rec U U = true := by
        cases U <;>
          simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]
      have hHeadScoped : __smtx_type_no_alias_rec
          (native_reflist_insert native_reflist_nil
            (native_string_lit "@Tuple")) U = true := by
        cases hU : __smtx_type_no_alias_rec
            (native_reflist_insert native_reflist_nil
              (native_string_lit "@Tuple")) U <;>
          simp_all [__smtx_dt_cons_no_alias_rec, native_ite]
      have hHeadNoAlias :
          __smtx_type_no_alias_rec native_reflist_nil U = true :=
        Smtm.no_alias_ty_weaken U _ _ (fun x hx => by
          simp [native_reflist_contains, native_reflist_nil] at hx) hHeadScoped
      have hComp : __smtx_type_wf_component U = true :=
        Smtm.smtx_type_wf_component_of_parts hParts.1 hParts.2 hHeadNoAlias
      cases U <;>
        simp_all [__smtx_type_wf, __smtx_type_wf_component,
          __smtx_type_wf_rec, __smtx_ret_typeof_sel_rec, native_and]
  | SmtDatatypeCons.cons U c, Nat.succ j, hWf, hNoAlias, hJ => by
      have hTailWf : __smtx_dt_cons_wf_rec c c = true := by
        cases U <;>
          simp_all [__smtx_dt_cons_wf_rec, native_ite, native_and]
      have hTailNoAlias : __smtx_dt_cons_no_alias_rec
          (native_reflist_insert native_reflist_nil
            (native_string_lit "@Tuple")) c = true := by
        cases U <;>
          simp_all [__smtx_dt_cons_no_alias_rec, native_ite]
      have hTailJ : j < __smtx_dtc_num_sels c := by
        simpa [__smtx_dtc_num_sels] using hJ
      simpa [__smtx_ret_typeof_sel_rec] using
        qds_tuple_ret_type_wf c j hTailWf hTailNoAlias hTailJ

private theorem qds_tuple_selector_type
    (tail : SmtTerm) (c : SmtDatatypeCons) (j : native_Nat)
    (hTailTy : __smtx_typeof tail =
      SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum c SmtDatatype.null))
    (hTailWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum c SmtDatatype.null)) = true)
    (hCFree : Smtm.hasFreeDtc (native_string_lit "@Tuple")
      native_reflist_nil c = false)
    (hJ : j < __smtx_dtc_num_sels c) :
    __smtx_typeof
          (SmtTerm.Apply
            (SmtTerm.DtSel (native_string_lit "@Tuple")
              (SmtDatatype.sum c SmtDatatype.null) native_nat_zero j) tail) =
        __smtx_ret_typeof_sel_rec
          (SmtDatatype.sum c SmtDatatype.null) native_nat_zero j ∧
      __smtx_type_wf
          (__smtx_ret_typeof_sel_rec
            (SmtDatatype.sum c SmtDatatype.null) native_nat_zero j) = true := by
  let tailD := SmtDatatype.sum c SmtDatatype.null
  have hSubC := Smtm.subst_noop_no_free_dtc
    (native_string_lit "@Tuple") c tailD native_reflist_nil
    (by native_decide) hCFree
  have hSubD : __smtx_dt_substitute (native_string_lit "@Tuple") tailD tailD =
      tailD := by
    simp [tailD, __smtx_dt_substitute, hSubC]
  have hConsWf : __smtx_dt_cons_wf_rec c c = true := by
    have hDtWf := Smtm.datatype_wf_rec_of_type_wf hTailWf
    rw [hSubD] at hDtWf
    cases h : __smtx_dt_cons_wf_rec c c <;>
      simp [tailD, __smtx_dt_wf_rec, native_ite, h] at hDtWf ⊢
  have hNoAlias : __smtx_dt_cons_no_alias_rec
      (native_reflist_insert native_reflist_nil
        (native_string_lit "@Tuple")) c = true := by
    have hDtNoAlias := Smtm.datatype_no_alias_of_type_wf hTailWf
    simpa [tailD, __smtx_dt_no_alias_rec, native_ite] using hDtNoAlias
  have hRetWf := qds_tuple_ret_type_wf c j hConsWf hNoAlias hJ
  constructor
  · rw [Smtm.typeof_dt_sel_apply_eq]
    rw [show __smtx_ret_typeof_sel (native_string_lit "@Tuple") tailD
        native_nat_zero j =
        __smtx_ret_typeof_sel_rec tailD native_nat_zero j by
      unfold __smtx_ret_typeof_sel
      rw [hSubD]]
    simp [tailD, hTailTy,
      __smtx_typeof_apply, __smtx_typeof_guard,
      __smtx_typeof_guard_wf, hRetWf, native_ite, native_Teq]
  · exact hRetWf

theorem qds_tuple_ret_type_wf_of_eo_type
    (T : Term) (c : SmtDatatypeCons) (j : native_Nat)
    (hShape : __eo_to_smt_type T =
      SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum c SmtDatatype.null))
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true)
    (hJ : j < __smtx_dtc_num_sels c) :
    __smtx_type_wf
      (__smtx_ret_typeof_sel_rec
        (SmtDatatype.sum c SmtDatatype.null) native_nat_zero j) = true := by
  let tailTy := SmtType.Datatype (native_string_lit "@Tuple")
    (SmtDatatype.sum c SmtDatatype.null)
  let tail := SmtTerm.Var (native_string_lit "@qds-tail") tailTy
  have hTailWf : __smtx_type_wf tailTy = true :=
    (congrArg __smtx_type_wf hShape).symm.trans hWf
  have hTailTy : __smtx_typeof tail = tailTy := by
    simp [tail, smtx_typeof_var_term_eq, __smtx_typeof_guard_wf,
      hTailWf, native_ite]
  have hCFree := qds_tuple_fields_no_free hShape
  exact (qds_tuple_selector_type tail c j
    (by simpa [tailTy] using hTailTy)
    (by simpa [tailTy] using hTailWf) hCFree hJ).2

private theorem qds_tuple_prepend_rec_head
    (tailD : SmtDatatype) (tail acc : SmtTerm) : ∀ k,
    qdsSmtApplyHead (__eo_to_smt_tuple_prepend_rec tailD tail k acc) =
      qdsSmtApplyHead acc
  | 0 => by simp [__eo_to_smt_tuple_prepend_rec]
  | Nat.succ k => by
      simp [__eo_to_smt_tuple_prepend_rec, qdsSmtApplyHead,
        qds_tuple_prepend_rec_head tailD tail acc k]

private theorem qds_tuple_seed_type
    (head : SmtTerm) (A : SmtType) (c : SmtDatatypeCons)
    (hHeadTy : __smtx_typeof head = A)
    (hHeadWf : __smtx_type_wf A = true)
    (hANotTuple : A ≠ SmtType.TypeRef (native_string_lit "@Tuple"))
    (hAFree : Smtm.hasFreeTy (native_string_lit "@Tuple")
      native_reflist_nil A = false)
    (hCFree : Smtm.hasFreeDtc (native_string_lit "@Tuple")
      native_reflist_nil c = false)
    (hFullWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null)) = true) :
    let fullD := SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
    __smtx_typeof
        (SmtTerm.Apply
          (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
          head) =
      dt_cons_applied_type_rec (native_string_lit "@Tuple") fullD fullD
        native_nat_zero 1 := by
  intro fullD
  have hSubA := qds_tuple_type_substitute_noop A fullD hANotTuple hAFree
  have hFullFree : Smtm.hasFreeDtc (native_string_lit "@Tuple")
      native_reflist_nil (SmtDatatypeCons.cons A c) = false := by
    cases A <;>
      simp_all [Smtm.hasFreeDtc, native_or, native_and, native_not,
        native_reflist_contains, native_streq]
  have hSubFullC := Smtm.subst_noop_no_free_dtc
    (native_string_lit "@Tuple") (SmtDatatypeCons.cons A c) fullD
    native_reflist_nil (by native_decide) hFullFree
  have hSubD : __smtx_dt_substitute (native_string_lit "@Tuple") fullD fullD =
      fullD := by
    change SmtDatatype.sum
      (__smtx_dtc_substitute (native_string_lit "@Tuple") fullD
        (SmtDatatypeCons.cons A c)) SmtDatatype.null = fullD
    rw [hSubFullC]
  have hANone : A ≠ SmtType.None := by
    intro hNone
    rw [hNone] at hHeadWf
    exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) hHeadWf
  rw [show __smtx_typeof
      (SmtTerm.Apply
        (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero)
        head) =
      __smtx_typeof_apply
        (__smtx_typeof
          (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero))
        (__smtx_typeof head) by rfl]
  rw [Smtm.typeof_dt_cons_eq, hHeadTy]
  simp only [fullD, hFullWf, hSubD, hSubA,
    __smtx_typeof_guard_wf, __smtx_typeof_dt_cons_rec,
    __smtx_typeof_apply, __smtx_typeof_guard, hHeadWf,
    dt_cons_applied_type_rec, native_ite, native_Teq]
  simpa [__smtx_typeof_apply, __smtx_typeof_guard,
    native_ite, native_Teq, hANone] using
      (typeof_dt_cons_value_rec_eq_typeof_dt_cons_rec
        (SmtType.Datatype (native_string_lit "@Tuple") fullD)
        (SmtDatatype.sum c SmtDatatype.null) native_nat_zero).symm

private theorem qds_tuple_prepend_rec_type
    (head tail : SmtTerm) (A : SmtType) (c : SmtDatatypeCons)
    (hHeadTy : __smtx_typeof head = A)
    (hHeadWf : __smtx_type_wf A = true)
    (hTailTy : __smtx_typeof tail =
      SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum c SmtDatatype.null))
    (hTailWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum c SmtDatatype.null)) = true)
    (hANotTuple : A ≠ SmtType.TypeRef (native_string_lit "@Tuple"))
    (hAFree : Smtm.hasFreeTy (native_string_lit "@Tuple")
      native_reflist_nil A = false)
    (hCFree : Smtm.hasFreeDtc (native_string_lit "@Tuple")
      native_reflist_nil c = false)
    (hFullWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null)) = true) :
    let tailD := SmtDatatype.sum c SmtDatatype.null
    let fullD := SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
    let seed := SmtTerm.Apply
      (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero) head
    ∀ k, k ≤ __smtx_dtc_num_sels c ->
      __smtx_typeof (__eo_to_smt_tuple_prepend_rec tailD tail k seed) =
        dt_cons_applied_type_rec (native_string_lit "@Tuple") fullD fullD
          native_nat_zero (Nat.succ k) := by
  intro tailD fullD seed k hK
  induction k with
  | zero =>
      simpa [tailD, fullD, seed, __eo_to_smt_tuple_prepend_rec] using
        qds_tuple_seed_type head A c hHeadTy hHeadWf hANotTuple hAFree
          hCFree hFullWf
  | succ k ih =>
      have hKLe : k ≤ __smtx_dtc_num_sels c := Nat.le_trans (Nat.le_succ k) hK
      have hKLt : k < __smtx_dtc_num_sels c := Nat.lt_of_succ_le hK
      let recTerm := __eo_to_smt_tuple_prepend_rec tailD tail k seed
      let selTerm := SmtTerm.Apply
        (SmtTerm.DtSel (native_string_lit "@Tuple") tailD native_nat_zero k) tail
      have hRecTy : __smtx_typeof recTerm =
          dt_cons_applied_type_rec (native_string_lit "@Tuple") fullD fullD
            native_nat_zero (Nat.succ k) := ih hKLe
      have hChainLt : Nat.succ k < __smtx_dt_num_sels fullD native_nat_zero := by
        simpa [fullD, __smtx_dt_num_sels, __smtx_dtc_num_sels] using
          Nat.succ_lt_succ hKLt
      have hStep := dt_cons_applied_type_rec_step
        (native_string_lit "@Tuple") fullD fullD native_nat_zero
          (Nat.succ k) hChainLt
      have hSel := qds_tuple_selector_type tail c k hTailTy hTailWf hCFree hKLt
      have hSelTy : __smtx_typeof selTerm =
          __smtx_ret_typeof_sel_rec fullD native_nat_zero (Nat.succ k) := by
        simpa [selTerm, tailD, fullD, __smtx_ret_typeof_sel_rec] using hSel.1
      have hSelNN : __smtx_ret_typeof_sel_rec fullD native_nat_zero
          (Nat.succ k) ≠ SmtType.None := by
        intro hNone
        have hWf := hSel.2
        rw [show __smtx_ret_typeof_sel_rec
            (SmtDatatype.sum c SmtDatatype.null) native_nat_zero k =
              __smtx_ret_typeof_sel_rec fullD native_nat_zero (Nat.succ k) by
          simp [fullD, __smtx_ret_typeof_sel_rec]] at hWf
        rw [hNone] at hWf
        exact (show __smtx_type_wf SmtType.None ≠ true by native_decide) hWf
      have hRecHead : qdsSmtApplyHead recTerm =
          SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero := by
        simp [recTerm, qds_tuple_prepend_rec_head, seed, qdsSmtApplyHead]
      have hNotSel : ∀ s d i j,
          recTerm ≠ SmtTerm.DtSel s d i j := by
        intro s d i j hEq
        rw [hEq] at hRecHead
        simp [qdsSmtApplyHead] at hRecHead
      have hNotTester : ∀ s d i,
          recTerm ≠ SmtTerm.DtTester s d i := by
        intro s d i hEq
        rw [hEq] at hRecHead
        simp [qdsSmtApplyHead] at hRecHead
      have hGeneric : generic_apply_type recTerm selTerm :=
        generic_apply_type_of_non_datatype_head hNotSel hNotTester
      simp only [__eo_to_smt_tuple_prepend_rec, recTerm, selTerm]
      rw [hGeneric]
      exact qds_smt_typeof_apply_of_head_cases
        (Or.inr (hRecTy.trans hStep)) hSelTy hSelNN

theorem qds_dtc_full_arity
    (s : native_String) (d0 : SmtDatatype) : ∀ c : SmtDatatypeCons,
    dt_cons_applied_type_rec s d0 (SmtDatatype.sum c SmtDatatype.null)
        native_nat_zero (__smtx_dtc_num_sels c) =
      SmtType.Datatype s d0
  | SmtDatatypeCons.unit => by
      simp [dt_cons_applied_type_rec, __smtx_dtc_num_sels,
        __smtx_typeof_dt_cons_value_rec]
  | SmtDatatypeCons.cons U c => by
      simpa [dt_cons_applied_type_rec, __smtx_dtc_num_sels,
        __smtx_typeof_dt_cons_value_rec] using qds_dtc_full_arity s d0 c

private theorem qds_tuple_full_arity
    (A : SmtType) (c : SmtDatatypeCons) :
    let fullD := SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
    dt_cons_applied_type_rec (native_string_lit "@Tuple") fullD fullD
        native_nat_zero (__smtx_dt_num_sels fullD native_nat_zero) =
      SmtType.Datatype (native_string_lit "@Tuple") fullD := by
  intro fullD
  simpa [fullD, __smtx_dt_num_sels] using
    qds_dtc_full_arity (native_string_lit "@Tuple") fullD
      (SmtDatatypeCons.cons A c)

private theorem qds_tuple_prepend_non_none
    (head tail : SmtTerm) (A : SmtType) (c : SmtDatatypeCons)
    (hHeadTy : __smtx_typeof head = A)
    (hHeadWf : __smtx_type_wf A = true)
    (hTailTy : __smtx_typeof tail =
      SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum c SmtDatatype.null))
    (hTailWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum c SmtDatatype.null)) = true)
    (hANotTuple : A ≠ SmtType.TypeRef (native_string_lit "@Tuple"))
    (hAFree : Smtm.hasFreeTy (native_string_lit "@Tuple")
      native_reflist_nil A = false)
    (hCFree : Smtm.hasFreeDtc (native_string_lit "@Tuple")
      native_reflist_nil c = false)
    (hFullWf : __smtx_type_wf
      (SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null)) = true) :
    __smtx_typeof (__eo_to_smt_tuple_prepend head A tail) ≠ SmtType.None := by
  unfold __eo_to_smt_tuple_prepend
  rw [hTailTy]
  simp only [__eo_to_smt_tuple_prepend_of_type, native_streq, native_and,
    hFullWf, Bool.and_self, native_ite, if_true]
  simp only [Bool.and_true, decide_true, if_true]
  let tailD := SmtDatatype.sum c SmtDatatype.null
  let fullD := SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null
  let seed := SmtTerm.Apply
    (SmtTerm.DtCons (native_string_lit "@Tuple") fullD native_nat_zero) head
  have hRec := qds_tuple_prepend_rec_type head tail A c hHeadTy hHeadWf
    hTailTy hTailWf hANotTuple hAFree hCFree hFullWf
    (__smtx_dtc_num_sels c) (Nat.le_refl _)
  have hCount : Nat.succ (__smtx_dtc_num_sels c) =
      __smtx_dt_num_sels fullD native_nat_zero := by
    simp [fullD, __smtx_dt_num_sels, __smtx_dtc_num_sels]
  rw [show __smtx_dt_num_sels tailD native_nat_zero =
      __smtx_dtc_num_sels c by
    simp [tailD, __smtx_dt_num_sels]]
  rw [hRec, hCount, qds_tuple_full_arity A c]
  simp

theorem ctor_spine_translation {T c : Term} (hs : CS c)
    (hEq : __eo_typeof c = T)
    (hWf : __smtx_type_wf (__eo_to_smt_type T) = true) :
    RuleProofs.eo_has_smt_translation c := by
  rcases cs_cases hs with hD | hT | hU
  · exact dcs_translation hD hEq hWf
  · obtain ⟨s₁, U₁, s₂, U₂, hFull, hU₁Wf, hU₂Wf⟩ :=
      tcs_full hT hEq hWf
    subst c
    subst T
    have hTypeWf : __smtx_type_wf
        (__eo_to_smt_type (__eo_typeof_tuple U₁ U₂)) = true := by
      simpa using hWf
    have hTypeEq := qds_typeof_tuple_eq_of_wf U₁ U₂ hTypeWf
    have hExplicitWf : __smtx_type_wf
        (__eo_to_smt_type
          (Term.Apply (Term.Apply (Term.UOp UserOp.Tuple) U₁) U₂)) = true := by
      rw [← hTypeEq]
      exact hTypeWf
    obtain ⟨tailC, hTailShape, hFullShape⟩ :=
      qds_tuple_type_shape_of_wf U₁ U₂ hExplicitWf
    have hHeadTy : __smtx_typeof
        (__eo_to_smt (Term.Var (Term.String s₁) U₁)) =
          __eo_to_smt_type U₁ := by
      rw [TranslationProofs.eo_to_smt_var, smtx_typeof_var_term_eq]
      simp [__smtx_typeof_guard_wf, hU₁Wf, native_ite]
    have hTailTupleWf : __smtx_type_wf
        (SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum tailC SmtDatatype.null)) = true := by
      exact (congrArg __smtx_type_wf hTailShape).symm.trans hU₂Wf
    have hTailTy : __smtx_typeof
        (__eo_to_smt (Term.Var (Term.String s₂) U₂)) =
          SmtType.Datatype (native_string_lit "@Tuple")
            (SmtDatatype.sum tailC SmtDatatype.null) := by
      rw [TranslationProofs.eo_to_smt_var]
      rw [smtx_typeof_var_term_eq]
      simp [__smtx_typeof_guard_wf, hTailShape, hTailTupleWf, native_ite]
    have hFullTupleWf : __smtx_type_wf
        (SmtType.Datatype (native_string_lit "@Tuple")
          (SmtDatatype.sum
            (SmtDatatypeCons.cons (__eo_to_smt_type U₁) tailC)
            SmtDatatype.null)) = true := by
      exact (congrArg __smtx_type_wf hFullShape).symm.trans hExplicitWf
    have hANotTuple : __eo_to_smt_type U₁ ≠
        SmtType.TypeRef (native_string_lit "@Tuple") :=
      TranslationProofs.eo_to_smt_type_ne_tuple_typeref U₁
    have hAFree : Smtm.hasFreeTy (native_string_lit "@Tuple")
        native_reflist_nil (__eo_to_smt_type U₁) = false :=
      TranslationProofs.hasFreeTy_reserved_of_translate
        (native_string_lit "@Tuple") (by native_decide) U₁
          native_reflist_nil
    have hCFree := qds_tuple_fields_no_free hTailShape
    unfold RuleProofs.eo_has_smt_translation
    change __smtx_typeof
      (__eo_to_smt_tuple_prepend
        (__eo_to_smt (Term.Var (Term.String s₁) U₁))
        (__smtx_typeof (__eo_to_smt (Term.Var (Term.String s₁) U₁)))
        (__eo_to_smt (Term.Var (Term.String s₂) U₂))) ≠ SmtType.None
    rw [hHeadTy]
    exact qds_tuple_prepend_non_none
      (__eo_to_smt (Term.Var (Term.String s₁) U₁))
      (__eo_to_smt (Term.Var (Term.String s₂) U₂))
      (__eo_to_smt_type U₁) tailC hHeadTy hU₁Wf hTailTy hTailTupleWf
      hANotTuple hAFree hCFree hFullTupleWf
  · have hFull := ucs_full hU hEq hWf
    subst c
    unfold RuleProofs.eo_has_smt_translation
    rw [TranslationProofs.eo_to_smt_term_tuple_unit,
      TranslationProofs.smtx_typeof_tuple_unit_translation]
    simp

end QuantDtSplitRule
