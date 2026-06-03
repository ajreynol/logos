import Cpc.Proofs.RuleSupport.DtConsEqSupport
import Cpc.Proofs.RuleSupport.SequenceSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option maxHeartbeats 10000000

private theorem eo_to_smt_eq_eq (x y : Term) :
    __eo_to_smt (Term.Apply (Term.Apply Term.eq x) y) =
      SmtTerm.eq (__eo_to_smt x) (__eo_to_smt y) := by
  rfl

private inductive SmtValueProperSubterm : SmtValue -> SmtValue -> Prop where
  | app_fun_self {f a : SmtValue} :
      SmtValueProperSubterm f (SmtValue.Apply f a)
  | app_fun {v f a : SmtValue} :
      SmtValueProperSubterm v f ->
      SmtValueProperSubterm v (SmtValue.Apply f a)
  | app_arg {f a : SmtValue} :
      SmtValueProperSubterm a (SmtValue.Apply f a)
  | app_arg_sub {v f a : SmtValue} :
      SmtValueProperSubterm v a ->
      SmtValueProperSubterm v (SmtValue.Apply f a)

private theorem smtValueProperSubterm_size_lt
    {v w : SmtValue} :
    SmtValueProperSubterm v w -> sizeOf v < sizeOf w := by
  intro h
  induction h with
  | app_fun_self =>
      rename_i f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega
  | app_fun h ih =>
      rename_i v f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega
  | app_arg =>
      rename_i f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega
  | app_arg_sub h ih =>
      rename_i v f a
      rw [show sizeOf (SmtValue.Apply f a) = 1 + sizeOf f + sizeOf a by rfl]
      omega

private theorem smtValueProperSubterm_ne
    {v w : SmtValue} :
    SmtValueProperSubterm v w -> v ≠ w := by
  intro h hEq
  have hLt := smtValueProperSubterm_size_lt h
  subst w
  omega

private theorem smtValueProperSubterm_trans
    {u v w : SmtValue} :
    SmtValueProperSubterm u v ->
    SmtValueProperSubterm v w ->
    SmtValueProperSubterm u w := by
  intro hUV hVW
  induction hVW with
  | app_fun_self =>
      exact SmtValueProperSubterm.app_fun hUV
  | app_fun h ih =>
      exact SmtValueProperSubterm.app_fun (ih hUV)
  | app_arg =>
      exact SmtValueProperSubterm.app_arg_sub hUV
  | app_arg_sub h ih =>
      exact SmtValueProperSubterm.app_arg_sub (ih hUV)

private theorem smtValueProperSubterm_parent_ne_reglan
    {v w : SmtValue} :
    SmtValueProperSubterm v w -> ∀ r, w ≠ SmtValue.RegLan r := by
  intro h r
  induction h with
  | app_fun_self => simp
  | app_fun => simp
  | app_arg => simp
  | app_arg_sub => simp

private theorem smtx_model_eval_eq_false_of_ne_not_reglan_pair
    {v w : SmtValue}
    (hNe : v ≠ w)
    (hReg : ¬ ∃ r1 r2, v = SmtValue.RegLan r1 ∧ w = SmtValue.RegLan r2) :
    __smtx_model_eval_eq v w = SmtValue.Boolean false := by
  cases v <;> cases w <;>
    simp [__smtx_model_eval_eq, native_veq] at hNe hReg ⊢
  all_goals exact hNe

private theorem smtx_model_eval_eq_false_of_proper_subterm
    {v w : SmtValue}
    (hSub : SmtValueProperSubterm v w) :
    __smtx_model_eval_eq v w = SmtValue.Boolean false := by
  exact smtx_model_eval_eq_false_of_ne_not_reglan_pair
    (smtValueProperSubterm_ne hSub)
    (by
      rintro ⟨r1, r2, hV, hW⟩
      exact smtValueProperSubterm_parent_ne_reglan hSub r2 hW)

private theorem smtx_model_eval_eq_false_of_type_ne
    {v w : SmtValue} {T U : SmtType}
    (hVT : __smtx_typeof_value v = T)
    (hWU : __smtx_typeof_value w = U)
    (hTNe : T ≠ U)
    (hTReg : T ≠ SmtType.RegLan) :
    __smtx_model_eval_eq v w = SmtValue.Boolean false := by
  have hNe : v ≠ w := by
    intro hEq
    apply hTNe
    rw [← hVT, ← hWU, hEq]
  exact smtx_model_eval_eq_false_of_ne_not_reglan_pair hNe
    (by
      rintro ⟨r1, r2, hV, _hW⟩
      apply hTReg
      rw [← hVT, hV]
      simp [__smtx_typeof_value])

private theorem smt_type_ne_tuple_cons_self
    (A : SmtType) (c : SmtDatatypeCons) :
    A ≠
      SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null) := by
  intro h
  have hSize := congrArg sizeOf h
  simp at hSize
  omega

private theorem smt_datatype_cons_ne_cons_self
    (A : SmtType) (c : SmtDatatypeCons) :
    c ≠ SmtDatatypeCons.cons A c := by
  intro h
  have hSize := congrArg sizeOf h
  simp at hSize

private theorem smt_tuple_tail_type_ne_prepend_type
    (A : SmtType) (c : SmtDatatypeCons) :
    SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum c SmtDatatype.null) ≠
      SmtType.Datatype (native_string_lit "@Tuple")
        (SmtDatatype.sum (SmtDatatypeCons.cons A c) SmtDatatype.null) := by
  intro h
  injection h with _ hD
  injection hD with hC _
  exact smt_datatype_cons_ne_cons_self A c hC

private theorem smt_model_eval_type_of_non_none
    (M : SmtModel) (hM : model_total_typed M) (x : SmtTerm)
    (hNN : __smtx_typeof x ≠ SmtType.None) :
    __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x := by
  exact Smtm.smt_model_eval_preserves_type_of_non_none M hM x
    (by
      unfold term_has_non_none_type
      exact hNN)

private theorem eval_types_of_eq_has_bool_type
    (M : SmtModel) (hM : model_total_typed M) (s t : Term) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) ->
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt s)) =
        __smtx_typeof (__eo_to_smt s) ∧
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) ∧
      __smtx_typeof (__eo_to_smt s) =
        __smtx_typeof (__eo_to_smt t) ∧
      __smtx_typeof (__eo_to_smt s) ≠ SmtType.None := by
  intro hBool
  rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
      s t hBool with
    ⟨hTyEq, hSNN⟩
  have hTNN : __smtx_typeof (__eo_to_smt t) ≠ SmtType.None := by
    rw [← hTyEq]
    exact hSNN
  exact
    ⟨smt_model_eval_type_of_non_none M hM (__eo_to_smt s) hSNN,
      smt_model_eval_type_of_non_none M hM (__eo_to_smt t) hTNN,
      hTyEq, hSNN⟩

private theorem generic_apply_fun_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (f a : Term) :
    __is_cons_app (Term.Apply f a) = Term.Boolean true ->
    (∀ x, f ≠ Term.Apply (Term.UOp UserOp.tuple) x) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq f) (Term.Apply f a)) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply Term.eq f) (Term.Apply f a))) =
      SmtValue.Boolean false := by
  intro hCons hNotTuple hBool
  rcases eval_types_of_eq_has_bool_type M hM f (Term.Apply f a) hBool with
    ⟨_hFEvalTy, _hAppEvalTy, hTyEq, hFNN⟩
  have hAppNN :
      RuleProofs.eo_has_smt_translation (Term.Apply f a) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [← hTyEq]
    exact hFNN
  have hEval :=
    is_cons_app_apply_eval_eq_apply_of_not_tuple
      M hM f a hCons hNotTuple hAppNN
  rw [eo_to_smt_eq_eq, __smtx_model_eval.eq_134]
  rw [hEval]
  exact smtx_model_eval_eq_false_of_proper_subterm
    SmtValueProperSubterm.app_fun_self

private theorem generic_apply_arg_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (f a : Term) :
    __is_cons_app (Term.Apply f a) = Term.Boolean true ->
    (∀ x, f ≠ Term.Apply (Term.UOp UserOp.tuple) x) ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq a) (Term.Apply f a)) ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply Term.eq a) (Term.Apply f a))) =
      SmtValue.Boolean false := by
  intro hCons hNotTuple hBool
  rcases eval_types_of_eq_has_bool_type M hM a (Term.Apply f a) hBool with
    ⟨_hAEvalTy, _hAppEvalTy, hTyEq, hANN⟩
  have hAppNN :
      RuleProofs.eo_has_smt_translation (Term.Apply f a) := by
    unfold RuleProofs.eo_has_smt_translation
    rw [← hTyEq]
    exact hANN
  have hEval :=
    is_cons_app_apply_eval_eq_apply_of_not_tuple
      M hM f a hCons hNotTuple hAppNN
  rw [eo_to_smt_eq_eq, __smtx_model_eval.eq_134]
  rw [hEval]
  exact smtx_model_eval_eq_false_of_proper_subterm
    SmtValueProperSubterm.app_arg

private theorem tuple_apply_partial_type_none
    (head : Term) :
    __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.UOp UserOp.tuple) head)) =
      SmtType.None := by
  change
    __smtx_typeof (SmtTerm.Apply SmtTerm.None (__eo_to_smt head)) =
      SmtType.None
  exact TranslationProofs.typeof_apply_none_eq (__eo_to_smt head)

private theorem tuple_apply_head_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (head tail : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq head)
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail)) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply Term.eq head)
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail))) =
      SmtValue.Boolean false := by
  intro hBool
  let tupleTerm := Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail
  rcases eval_types_of_eq_has_bool_type M hM head tupleTerm hBool with
    ⟨_hHeadEvalTy, _hTupleEvalTy, hTyEq, hHeadNN⟩
  have hTupleNN :
      __smtx_typeof (__eo_to_smt tupleTerm) ≠ SmtType.None := by
    rw [← hTyEq]
    exact hHeadNN
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt head)
          (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)) ≠
      SmtType.None at hTupleNN
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      tail head hTupleNN with
    ⟨c, hTailTy⟩
  have hFullTy :=
    TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
      (__eo_to_smt tail) (__eo_to_smt head)
      (__smtx_typeof (__eo_to_smt head)) c hTailTy hTupleNN
  have hTyNe :
      __smtx_typeof (__eo_to_smt head) ≠
        __smtx_typeof (__eo_to_smt tupleTerm) := by
    intro hEq
    change
      __smtx_typeof (__eo_to_smt head) =
        __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt head)
            (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)) at hEq
    rw [hFullTy] at hEq
    exact smt_type_ne_tuple_cons_self
      (__smtx_typeof (__eo_to_smt head)) c hEq
  exact False.elim (hTyNe hTyEq)

private theorem tuple_apply_tail_eval_eq_false
    (M : SmtModel) (hM : model_total_typed M) (head tail : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply Term.eq tail)
        (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail)) ->
    __smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply Term.eq tail)
            (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail))) =
      SmtValue.Boolean false := by
  intro hBool
  let tupleTerm := Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) tail
  rcases eval_types_of_eq_has_bool_type M hM tail tupleTerm hBool with
    ⟨_hTailEvalTy, _hTupleEvalTy, hTyEq, hTailNN⟩
  have hTupleNN :
      __smtx_typeof (__eo_to_smt tupleTerm) ≠ SmtType.None := by
    rw [← hTyEq]
    exact hTailNN
  change
    __smtx_typeof
        (__eo_to_smt_tuple_prepend (__eo_to_smt head)
          (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)) ≠
      SmtType.None at hTupleNN
  rcases TranslationProofs.eo_to_smt_tuple_tail_type_of_non_none_from_checked
      tail head hTupleNN with
    ⟨c, hTailTy⟩
  have hFullTy :=
    TranslationProofs.smtx_tuple_prepend_typeof_of_tail_tuple_type
      (__eo_to_smt tail) (__eo_to_smt head)
      (__smtx_typeof (__eo_to_smt head)) c hTailTy hTupleNN
  have hTyNe :
      __smtx_typeof (__eo_to_smt tail) ≠
        __smtx_typeof (__eo_to_smt tupleTerm) := by
    intro hEq
    change
      __smtx_typeof (__eo_to_smt tail) =
        __smtx_typeof
          (__eo_to_smt_tuple_prepend (__eo_to_smt head)
            (__smtx_typeof (__eo_to_smt head)) (__eo_to_smt tail)) at hEq
    rw [hTailTy, hFullTy] at hEq
    exact smt_tuple_tail_type_ne_prepend_type
      (__smtx_typeof (__eo_to_smt head)) c hEq
  exact False.elim (hTyNe hTyEq)

private inductive CtorSpineRoot : Term -> Term -> Prop where
  | tuple :
      CtorSpineRoot (Term.UOp UserOp.tuple) (Term.UOp UserOp.tuple)
  | tupleUnit :
      CtorSpineRoot (Term.UOp UserOp.tuple_unit) (Term.UOp UserOp.tuple_unit)
  | dtCons (s : native_String) (d : Datatype) (i : native_Nat) :
      CtorSpineRoot (Term.DtCons s d i) (Term.DtCons s d i)
  | app {t root : Term} (x : Term) :
      CtorSpineRoot t root ->
      CtorSpineRoot (Term.Apply t x) root

private inductive DtCyclePath : Term -> Term -> Prop where
  | app_fun_self {f a : Term} :
      DtCyclePath f (Term.Apply f a)
  | app_fun_sub {s f a : Term} :
      DtCyclePath s f ->
      DtCyclePath s (Term.Apply f a)
  | app_arg_self {f a : Term} :
      DtCyclePath a (Term.Apply f a)
  | app_arg_sub {s f a : Term} :
      DtCyclePath s a ->
      DtCyclePath s (Term.Apply f a)

private theorem eo_eq_self_of_ne_stuck
    {t : Term} (hT : t ≠ Term.Stuck) :
    __eo_eq t t = Term.Boolean true := by
  cases t <;> simp [__eo_eq, native_teq] at hT ⊢

private theorem eo_eq_false_of_ne_stuck_ne
    {t s : Term} (hT : t ≠ Term.Stuck) (hS : s ≠ Term.Stuck)
    (hNe : t ≠ s) :
    __eo_eq t s = Term.Boolean false := by
  have hNeRev : s ≠ t := by
    intro hEq
    exact hNe hEq.symm
  cases t <;> cases s <;>
    simp [__eo_eq, native_teq, hNeRev] at hT hS hNe hNeRev ⊢
  all_goals contradiction

private theorem eo_ite_true_true_cases
    {x y : Term} :
    __eo_ite x (Term.Boolean true) y = Term.Boolean true ->
      x = Term.Boolean true ∨
        (x = Term.Boolean false ∧ y = Term.Boolean true) := by
  intro h
  cases x <;> simp [__eo_ite, native_ite, native_teq] at h
  case Boolean b =>
    cases b
    · right
      constructor
      · rfl
      · simpa [__eo_ite, native_ite, native_teq] using h
    · left
      rfl

private theorem dt_find_cycle_nonapply_eq_of_true
    (c s isC rec : Term)
    (hC : c ≠ Term.Stuck)
    (hNotApply : ∀ f a, c ≠ Term.Apply f a) :
    __dt_find_cycle c s isC rec = Term.Boolean true ->
      c = s ∧ rec = Term.Boolean true := by
  intro h
  have hS : s ≠ Term.Stuck := by
    intro hStuck
    subst s
    rw [__dt_find_cycle.eq_2 c isC rec hC] at h
    simp at h
  have hIsC : isC ≠ Term.Stuck := by
    intro hStuck
    subst isC
    rw [__dt_find_cycle.eq_3 c s rec hC hS] at h
    simp at h
  have hRec : rec ≠ Term.Stuck := by
    intro hStuck
    subst rec
    rw [__dt_find_cycle.eq_4 c s isC hC hS hIsC] at h
    simp at h
  rw [__dt_find_cycle.eq_5 c s isC rec hC hS hIsC hRec] at h
  by_cases hEq : c = s
  · constructor
    · exact hEq
    · subst s
      rw [eo_eq_self_of_ne_stuck hC] at h
      simpa [__eo_ite, native_ite, native_teq] using h
  · rw [eo_eq_false_of_ne_stuck_ne hC hS hEq] at h
    have hNoApp :
        ∀ f a, c = Term.Apply f a -> isC = Term.Boolean true -> False := by
      intro f a hApp _hTrue
      exact hNotApply f a hApp
    rw [__eo_l_1___dt_find_cycle.eq_6 c s isC rec hC hS hIsC hNoApp hRec] at h
    exfalso
    simpa [__eo_ite, native_ite, native_teq] using h

private theorem dt_find_cycle_path_or_eq_of_true
    (c s isC rec : Term) :
    __dt_find_cycle c s isC rec = Term.Boolean true ->
      (c = s ∧ rec = Term.Boolean true) ∨
        (isC = Term.Boolean true ∧ DtCyclePath s c) := by
  cases c with
  | Stuck =>
      intro h
      simp [__dt_find_cycle] at h
  | Apply f a =>
      intro h
      have hC : Term.Apply f a ≠ Term.Stuck := by simp
      have hS : s ≠ Term.Stuck := by
        intro hStuck
        subst s
        rw [__dt_find_cycle.eq_2 (Term.Apply f a) isC rec hC] at h
        simp at h
      have hIsC : isC ≠ Term.Stuck := by
        intro hStuck
        subst isC
        rw [__dt_find_cycle.eq_3 (Term.Apply f a) s rec hC hS] at h
        simp at h
      have hRec : rec ≠ Term.Stuck := by
        intro hStuck
        subst rec
        rw [__dt_find_cycle.eq_4 (Term.Apply f a) s isC hC hS hIsC] at h
        simp at h
      rw [__dt_find_cycle.eq_5 (Term.Apply f a) s isC rec hC hS hIsC hRec] at h
      by_cases hEq : Term.Apply f a = s
      · left
        constructor
        · exact hEq
        · subst s
          rw [eo_eq_self_of_ne_stuck hC] at h
          simpa [__eo_ite, native_ite, native_teq] using h
      · rw [eo_eq_false_of_ne_stuck_ne hC hS hEq] at h
        simp [__eo_ite, native_ite, native_teq] at h
        by_cases hIsTrue : isC = Term.Boolean true
        · subst isC
          rw [__eo_l_1___dt_find_cycle.eq_5 s rec f a hS hRec] at h
          right
          constructor
          · rfl
          · rcases eo_ite_true_true_cases h with
              hArgTrue | ⟨_hArgFalse, hFunTrue⟩
            · rcases dt_find_cycle_path_or_eq_of_true
                a s (__is_cons_app a) (Term.Boolean true) hArgTrue with
                hArgEq' | hArgPath
              · rw [hArgEq'.1]
                exact DtCyclePath.app_arg_self
              · exact DtCyclePath.app_arg_sub hArgPath.2
            · rcases dt_find_cycle_path_or_eq_of_true
                f s (Term.Boolean true) rec hFunTrue with
                hFunEq | hFunPath
              · rw [← hFunEq.1]
                exact DtCyclePath.app_fun_self
              · exact DtCyclePath.app_fun_sub hFunPath.2
        · have hNoApp :
              ∀ f' a',
                Term.Apply f a = Term.Apply f' a' ->
                  isC = Term.Boolean true -> False := by
            intro _ _ _ hTrue
            exact hIsTrue hTrue
          rw [__eo_l_1___dt_find_cycle.eq_6
              (Term.Apply f a) s isC rec hC hS hIsC hNoApp hRec] at h
          exfalso
          simpa [__eo_ite, native_ite, native_teq] using h
  | _ =>
      intro h
      left
      exact dt_find_cycle_nonapply_eq_of_true
        _ s isC rec
        (by simp)
        (by
          intro _ _ hApp
          cases hApp)
        h
termination_by sizeOf c
decreasing_by
  all_goals
    simp_wf
    omega

private theorem dt_find_cycle_path_of_false_rec
    (c s : Term) :
    __dt_find_cycle c s (__is_cons_app c) (Term.Boolean false) =
      Term.Boolean true ->
    DtCyclePath s c := by
  intro h
  rcases dt_find_cycle_path_or_eq_of_true
      c s (__is_cons_app c) (Term.Boolean false) h with
    hEq | hPath
  · cases hEq.2
  · exact hPath.2

private theorem dt_find_cycle_cons_path_of_false_rec
    (c s : Term) :
    __dt_find_cycle c s (__is_cons_app c) (Term.Boolean false) =
      Term.Boolean true ->
    __is_cons_app c = Term.Boolean true ∧ DtCyclePath s c := by
  intro h
  rcases dt_find_cycle_path_or_eq_of_true
      c s (__is_cons_app c) (Term.Boolean false) h with
    hEq | hPath
  · cases hEq.2
  · exact hPath

private theorem ctorSpineRoot_of_is_cons_app_true
    (t : Term) :
    __is_cons_app t = Term.Boolean true ->
    ∃ root, CtorSpineRoot t root := by
  cases t with
  | UOp op =>
      intro h
      cases op <;>
        simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
          __eo_dt_selectors_main, native_teq, native_ite, native_not,
          SmtEval.native_not, SmtEval.native_and] at h ⊢
      all_goals
        first
        | exact ⟨Term.UOp UserOp.tuple, CtorSpineRoot.tuple⟩
        | exact ⟨Term.UOp UserOp.tuple_unit, CtorSpineRoot.tupleUnit⟩
        | contradiction
  | Apply f a =>
      intro h
      rcases ctorSpineRoot_of_is_cons_app_true f
          (by simpa [__is_cons_app] using h) with
        ⟨root, hRoot⟩
      exact ⟨root, CtorSpineRoot.app a hRoot⟩
  | DtCons s d i =>
      intro _h
      exact ⟨Term.DtCons s d i, CtorSpineRoot.dtCons s d i⟩
  | Stuck =>
      intro h
      simp [__is_cons_app] at h
  | UOp1 op t =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | UOp2 op t u =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | UOp3 op t u v =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | __eo_List =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | __eo_List_nil =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | __eo_List_cons =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Bool =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Boolean b =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Numeral n =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Rational q =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | String str =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Binary w n =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | «Type» =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | FunType =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | Var n T =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DatatypeType s d =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DatatypeTypeRef s =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DtcAppType T U =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | DtSel s d i j =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | USort n =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
  | UConst n T =>
      intro h
      simp [__is_cons_app, __eo_is_eq, __eo_is_ok, __eo_dt_selectors,
        __eo_dt_selectors_main, native_teq, native_ite, native_not,
        SmtEval.native_not, SmtEval.native_and] at h
termination_by sizeOf t
decreasing_by
  simp_wf
  omega

private theorem prog_dt_cycle_shape_of_not_stuck
    (s t : Term) :
    __eo_prog_dt_cycle
        (Term.Apply
          (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false)) ≠
      Term.Stuck ->
    __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
        Term.Boolean true ∧
      __eo_prog_dt_cycle
          (Term.Apply
            (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
            (Term.Boolean false)) =
        Term.Apply
          (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
          (Term.Boolean false) := by
  intro hProg
  let guard := __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false)
  let body :=
    Term.Apply
      (Term.Apply Term.eq (Term.Apply (Term.Apply Term.eq s) t))
      (Term.Boolean false)
  have hReq : __eo_requires guard (Term.Boolean true) body ≠ Term.Stuck := by
    simpa [__eo_prog_dt_cycle, guard, body] using hProg
  constructor
  · exact eo_requires_eq_of_ne_stuck guard (Term.Boolean true) body hReq
  · simpa [__eo_prog_dt_cycle, guard, body] using
      eo_requires_eq_result_of_ne_stuck guard (Term.Boolean true) body hReq

private theorem dt_cycle_inner_eval_false
    (M : SmtModel) (hM : model_total_typed M) (s t : Term) :
    RuleProofs.eo_has_bool_type (Term.Apply (Term.Apply Term.eq s) t) ->
    __dt_find_cycle t s (__is_cons_app t) (Term.Boolean false) =
      Term.Boolean true ->
    __smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply Term.eq s) t)) =
      SmtValue.Boolean false := by
  intro hBool hCycle
  rcases dt_find_cycle_cons_path_of_false_rec t s hCycle with
    ⟨hCons, hPath⟩
  cases t with
  | Apply =>
      rename_i f a
      match hPath with
      | DtCyclePath.app_fun_self =>
          by_cases hTuple :
              ∃ head, s = Term.Apply (Term.UOp UserOp.tuple) head
          · rcases hTuple with ⟨head, rfl⟩
            rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
                (Term.Apply (Term.UOp UserOp.tuple) head)
                (Term.Apply (Term.Apply (Term.UOp UserOp.tuple) head) a)
                hBool with
              ⟨_hTyEq, hPrefixNN⟩
            exact False.elim (hPrefixNN (tuple_apply_partial_type_none head))
          · exact generic_apply_fun_eval_eq_false M hM s a hCons
              (by
                intro head hHead
                exact hTuple ⟨head, hHead⟩)
              hBool
      | DtCyclePath.app_fun_sub hSub =>
          sorry
      | DtCyclePath.app_arg_self =>
          by_cases hTuple :
              ∃ head, f = Term.Apply (Term.UOp UserOp.tuple) head
          · rcases hTuple with ⟨head, rfl⟩
            exact tuple_apply_tail_eval_eq_false M hM head s hBool
          · exact generic_apply_arg_eval_eq_false M hM f s hCons
              (by
                intro head hHead
                exact hTuple ⟨head, hHead⟩)
              hBool
      | DtCyclePath.app_arg_sub hSub =>
          sorry
  | _ =>
      cases hPath

theorem cmd_step_dt_cycle_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.dt_cycle args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.dt_cycle args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.dt_cycle args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.dt_cycle args premises ≠ Term.Stuck :=
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
              have hATransPair : RuleProofs.eo_has_smt_translation a1 ∧ True := by
                simpa [cmdTranslationOk, cArgListTranslationOk] using hCmdTrans
              have hATrans : RuleProofs.eo_has_smt_translation a1 := hATransPair.1
              have hProgRule : __eo_prog_dt_cycle a1 ≠ Term.Stuck := by
                simpa using hProg
              cases a1 with
              | Apply f B =>
                  cases B with
                  | Boolean b =>
                      cases b
                      · cases f with
                        | Apply g lhs =>
                            cases g with
                            | UOp op =>
                                cases op with
                                | eq =>
                                    cases lhs with
                                    | Apply f' s' =>
                                        cases f' with
                                        | Apply g' t' =>
                                            cases g' with
                                            | UOp op' =>
                                                cases op' with
                                                | eq =>
                                                    let proven :=
                                                      Term.Apply
                                                        (Term.Apply Term.eq
                                                          (Term.Apply
                                                            (Term.Apply Term.eq t') s'))
                                                        (Term.Boolean false)
                                                    have hShape :=
                                                      prog_dt_cycle_shape_of_not_stuck
                                                        t' s' hProgRule
                                                    have hCycle :
                                                        __dt_find_cycle s' t'
                                                            (__is_cons_app s')
                                                            (Term.Boolean false) =
                                                          Term.Boolean true :=
                                                      hShape.1
                                                    have hProgEq :
                                                        __eo_prog_dt_cycle proven = proven := by
                                                      simpa [proven] using hShape.2
                                                    have hAType : __eo_typeof proven = Term.Bool := by
                                                      have hResultTy' := hResultTy
                                                      change __eo_typeof
                                                          (__eo_prog_dt_cycle proven) =
                                                        Term.Bool at hResultTy'
                                                      rw [hProgEq] at hResultTy'
                                                      exact hResultTy'
                                                    have hABool :
                                                        RuleProofs.eo_has_bool_type proven :=
                                                      RuleProofs.eo_typeof_bool_implies_has_bool_type
                                                        _ hATrans hAType
                                                    refine ⟨?_, ?_⟩
                                                    · intro _hTrue
                                                      change eo_interprets M
                                                        (__eo_prog_dt_cycle proven) true
                                                      rw [hProgEq]
                                                      have hInnerBool :
                                                          RuleProofs.eo_has_bool_type
                                                            (Term.Apply
                                                              (Term.Apply Term.eq t') s') :=
                                                        eo_eq_has_bool_type_of_eq_has_bool_type
                                                          t' s' (Term.Boolean false) hABool
                                                      have hInnerEvalFalse :
                                                          __smtx_model_eval M
                                                              (__eo_to_smt
                                                                (Term.Apply
                                                                  (Term.Apply Term.eq t') s')) =
                                                            SmtValue.Boolean false :=
                                                        dt_cycle_inner_eval_false
                                                          M hM t' s' hInnerBool hCycle
                                                      have hFalseEval :
                                                          __smtx_model_eval M
                                                              (__eo_to_smt (Term.Boolean false)) =
                                                            SmtValue.Boolean false := by
                                                        simp [__smtx_model_eval]
                                                      have hRel :
                                                          RuleProofs.smt_value_rel
                                                            (__smtx_model_eval M
                                                              (__eo_to_smt
                                                                (Term.Apply
                                                                  (Term.Apply Term.eq t') s')))
                                                            (__smtx_model_eval M
                                                              (__eo_to_smt (Term.Boolean false))) := by
                                                        rw [hInnerEvalFalse, hFalseEval]
                                                        exact RuleProofs.smt_value_rel_refl
                                                          (SmtValue.Boolean false)
                                                      exact RuleProofs.eo_interprets_eq_of_rel
                                                        M
                                                        (Term.Apply
                                                          (Term.Apply Term.eq t') s')
                                                        (Term.Boolean false)
                                                        hABool hRel
                                                    · change RuleProofs.eo_has_smt_translation
                                                        (__eo_prog_dt_cycle proven)
                                                      rw [hProgEq]
                                                      exact RuleProofs.eo_has_smt_translation_of_has_bool_type
                                                        _ hABool
                                                | _ =>
                                                    simp [__eo_prog_dt_cycle] at hProgRule
                                            | _ =>
                                                simp [__eo_prog_dt_cycle] at hProgRule
                                        | _ =>
                                            simp [__eo_prog_dt_cycle] at hProgRule
                                    | _ =>
                                        simp [__eo_prog_dt_cycle] at hProgRule
                                | _ =>
                                    simp [__eo_prog_dt_cycle] at hProgRule
                            | _ =>
                                simp [__eo_prog_dt_cycle] at hProgRule
                        | _ =>
                            simp [__eo_prog_dt_cycle] at hProgRule
                      · simp [__eo_prog_dt_cycle] at hProgRule
                  | _ =>
                      simp [__eo_prog_dt_cycle] at hProgRule
              | _ =>
                  simp [__eo_prog_dt_cycle] at hProgRule
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
