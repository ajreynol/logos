import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.RuleSupport.StrConcatSupport

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 10000000

private theorem eo_typeof_stuck_ne_bool :
    __eo_typeof Term.Stuck ≠ Term.Bool := by
  native_decide

private theorem eo_requires_true_eq_of_type_bool (x body : Term) :
    __eo_typeof (__eo_requires x (Term.Boolean true) body) = Term.Bool ->
    __eo_requires x (Term.Boolean true) body = body := by
  intro hTy
  cases x <;>
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hTy ⊢
  case Boolean b =>
    cases b <;>
      simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hTy ⊢
    exact False.elim (eo_typeof_stuck_ne_bool hTy)
  all_goals
    exact False.elim (eo_typeof_stuck_ne_bool hTy)

private theorem eo_prog_aci_norm_eq_input_of_type_bool (a1 : Term) :
  __eo_typeof (__eo_prog_aci_norm a1) = Term.Bool ->
  __eo_prog_aci_norm a1 = a1 := by
  intro hTy
  cases a1
  all_goals try
    have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_aci_norm] using hTy
    exact False.elim (eo_typeof_stuck_ne_bool hStuck)
  case Apply f x =>
    cases f
    all_goals try
      have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
        simpa [__eo_prog_aci_norm] using hTy
      exact False.elim (eo_typeof_stuck_ne_bool hStuck)
    case Apply g y =>
      cases g
      all_goals try
        have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
          simpa [__eo_prog_aci_norm] using hTy
        exact False.elim (eo_typeof_stuck_ne_bool hStuck)
      case UOp op =>
        cases op <;> simp [__eo_prog_aci_norm] at hTy ⊢
        case eq =>
          exact eo_requires_true_eq_of_type_bool _ _ hTy
        all_goals
          exact False.elim (eo_typeof_stuck_ne_bool hTy)

private def aciNormGuard (a b : Term) : Term :=
  __eo_ite (__aci_norm_eq (__get_aci_normal_form a) b) (Term.Boolean true)
    (__eo_ite (__aci_norm_eq (__get_aci_normal_form b) a) (Term.Boolean true)
      (__aci_norm_eq (__get_aci_normal_form a) (__get_aci_normal_form b)))

private theorem aci_norm_guard_true_of_type_bool (a b : Term) :
    __eo_typeof
        (__eo_requires (aciNormGuard a b) (Term.Boolean true)
          (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b)) = Term.Bool ->
    aciNormGuard a b = Term.Boolean true := by
  intro hTy
  cases hGuard : aciNormGuard a b <;>
    simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not,
      hGuard] at hTy
  case Boolean v =>
    cases v
    · exact False.elim (eo_typeof_stuck_ne_bool hTy)
    · rfl
  all_goals
    exact False.elim (eo_typeof_stuck_ne_bool hTy)

private theorem smt_value_rel_of_eo_eq_true
    (M : SmtModel) (x y : Term) :
    __eo_eq x y = Term.Boolean true ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hEq
  have hyx : y = x := eq_of_eo_eq_true_local x y hEq
  subst y
  exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt x))

private theorem eo_ite_eq_true_cases (c t e : Term) :
    __eo_ite c t e = Term.Boolean true ->
    (c = Term.Boolean true ∧ t = Term.Boolean true) ∨
      (c = Term.Boolean false ∧ e = Term.Boolean true) := by
  intro h
  cases c <;> simp [__eo_ite, native_teq, native_ite] at h
  case Boolean b =>
    cases b <;> simp [__eo_ite, native_teq, native_ite] at h
    · exact Or.inr ⟨rfl, h⟩
    · exact Or.inl ⟨rfl, h⟩

private theorem eo_ite_else_eq_true_of_cond_ne_true
    (c t e : Term) :
    c ≠ Term.Boolean true ->
    __eo_ite c t e = Term.Boolean true ->
    c = Term.Boolean false ∧ e = Term.Boolean true := by
  intro hNe hIte
  rcases eo_ite_eq_true_cases c t e hIte with hThen | hElse
  · exact False.elim (hNe hThen.1)
  · exact hElse

private theorem generic_apply_type_of_non_special_head_local
    (f x : SmtTerm)
    (hSel : ∀ s d i j, f ≠ SmtTerm.DtSel s d i j)
    (hTester : ∀ s d i, f ≠ SmtTerm.DtTester s d i) :
    generic_apply_type f x := by
  unfold generic_apply_type
  exact __smtx_typeof.eq_140 f x hSel hTester

private theorem smtx_typeof_apply_none (x : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply SmtTerm.None x) = SmtType.None := by
  have hGeneric : generic_apply_type SmtTerm.None x := by
    exact generic_apply_type_of_non_special_head_local _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, TranslationProofs.smtx_typeof_none]
  simp [__smtx_typeof_apply]

private theorem smtx_typeof_apply_apply_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None y) x) =
      SmtType.None := by
  have hGeneric : generic_apply_type (SmtTerm.Apply SmtTerm.None y) x := by
    exact generic_apply_type_of_non_special_head_local _ _
      (by intro s d i j h; cases h)
      (by intro s d i h; cases h)
  rw [hGeneric, smtx_typeof_apply_none y]
  simp [__smtx_typeof_apply]

private theorem aci_sorted_marker_not_has_smt_translation (f t : Term) :
    ¬ RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) t) := by
  intro hTrans
  apply hTrans
  simpa using smtx_typeof_apply_apply_none (__eo_to_smt t) (__eo_to_smt f)

private theorem eo_has_smt_translation_ne_stuck (t : Term) :
    RuleProofs.eo_has_smt_translation t -> t ≠ Term.Stuck := by
  intro hTrans hStuck
  subst t
  exact hTrans TranslationProofs.smtx_typeof_none

private theorem aci_norm_eq_nonstuck (x y : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __aci_norm_eq x y =
      __eo_ite (__eo_eq x y) (Term.Boolean true)
        (__eo_l_1___aci_norm_eq x y) := by
  intro hx hy
  cases x <;> cases y <;> simp [__aci_norm_eq] at hx hy ⊢

private theorem aci_norm_eq_true_left_ne_stuck (x y : Term) :
    __aci_norm_eq x y = Term.Boolean true ->
    x ≠ Term.Stuck := by
  intro hEq hStuck
  subst x
  simp [__aci_norm_eq] at hEq

private theorem aci_norm_eq_true_right_ne_stuck (x y : Term) :
    __aci_norm_eq x y = Term.Boolean true ->
    y ≠ Term.Stuck := by
  intro hEq hStuck
  subst y
  cases x <;> simp [__aci_norm_eq] at hEq

private theorem aci_norm_l3_nonstuck_eq_false (x y : Term) :
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_l_3___aci_norm_eq x y = Term.Boolean false := by
  intro hx hy
  cases x <;> cases y <;> simp [__eo_l_3___aci_norm_eq] at hx hy ⊢

private theorem aci_norm_l2_marker_right_translation_ne_true
    (f payload y : Term) :
    RuleProofs.eo_has_smt_translation y ->
    __eo_l_2___aci_norm_eq
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) payload)
      y ≠ Term.Boolean true := by
  intro hYTrans hEq
  cases y <;>
    simp [__eo_l_2___aci_norm_eq, __eo_l_3___aci_norm_eq, __eo_ite,
      __eo_eq, native_teq, native_ite] at hEq hYTrans
  case Apply yf yPayload =>
    cases yf
    all_goals try
      simp [__eo_l_2___aci_norm_eq, __eo_l_3___aci_norm_eq, __eo_ite,
        __eo_eq, native_teq, native_ite] at hEq hYTrans
    case Apply yg yMarkerArg =>
      cases yg
      all_goals try
        simp [__eo_l_2___aci_norm_eq, __eo_l_3___aci_norm_eq, __eo_ite,
          __eo_eq, native_teq, native_ite] at hEq hYTrans
      case UOp op =>
        cases op
        all_goals try
          simp [__eo_l_2___aci_norm_eq, __eo_l_3___aci_norm_eq, __eo_ite,
            __eo_eq, native_teq, native_ite] at hEq hYTrans
        exact aci_sorted_marker_not_has_smt_translation yMarkerArg yPayload hYTrans

private theorem aci_norm_l2_nonmarker_left_eq_false
    (x y : Term) :
    (∀ f payload,
      x ≠ Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) payload) ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_l_2___aci_norm_eq x y = Term.Boolean false := by
  intro hNotMarker hx hy
  cases x <;> cases y <;>
    simp [__eo_l_2___aci_norm_eq, __eo_l_3___aci_norm_eq] at hx hy ⊢
  case Apply.Apply f payload yf yPayload =>
    cases f <;>
      simp [__eo_l_2___aci_norm_eq, __eo_l_3___aci_norm_eq] at hNotMarker ⊢
    case Apply g markerArg =>
      cases g <;>
        simp [__eo_l_2___aci_norm_eq, __eo_l_3___aci_norm_eq] at hNotMarker ⊢
      case UOp op =>
        cases op <;>
          simp [__eo_l_2___aci_norm_eq, __eo_l_3___aci_norm_eq] at hNotMarker ⊢

private theorem aci_norm_l1_nonmarker_left_eq_false
    (x y : Term) :
    (∀ f payload,
      x ≠ Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) payload) ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_l_1___aci_norm_eq x y = Term.Boolean false := by
  intro hNotMarker hx hy
  cases x <;> cases y <;>
    simp [__eo_l_1___aci_norm_eq, __eo_l_2___aci_norm_eq,
      __eo_l_3___aci_norm_eq] at hx hy ⊢
  case Apply.Apply f payload yf yPayload =>
    cases f <;>
      simp [__eo_l_1___aci_norm_eq, __eo_l_2___aci_norm_eq,
        __eo_l_3___aci_norm_eq] at hNotMarker ⊢
    case Apply g markerArg =>
      cases g <;>
        simp [__eo_l_1___aci_norm_eq, __eo_l_2___aci_norm_eq,
          __eo_l_3___aci_norm_eq] at hNotMarker ⊢
      case UOp op =>
        cases op <;>
          simp [__eo_l_1___aci_norm_eq, __eo_l_2___aci_norm_eq,
            __eo_l_3___aci_norm_eq] at hNotMarker ⊢

private theorem aci_norm_eq_true_nonmarker_left_false (x y : Term) :
    (∀ f payload,
      x ≠ Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) payload) ->
    __eo_eq x y ≠ Term.Boolean true ->
    __aci_norm_eq x y = Term.Boolean true ->
    False := by
  intro hNotMarker hTermEq hEq
  have hXNe : x ≠ Term.Stuck := aci_norm_eq_true_left_ne_stuck x y hEq
  have hYNe : y ≠ Term.Stuck := aci_norm_eq_true_right_ne_stuck x y hEq
  have hEqIte := hEq
  rw [aci_norm_eq_nonstuck x y hXNe hYNe] at hEqIte
  have hL1 :
      __eo_l_1___aci_norm_eq x y = Term.Boolean true :=
    (eo_ite_else_eq_true_of_cond_ne_true
      (__eo_eq x y) (Term.Boolean true)
      (__eo_l_1___aci_norm_eq x y) hTermEq hEqIte).2
  have hFalse :=
    aci_norm_l1_nonmarker_left_eq_false x y hNotMarker hXNe hYNe
  rw [hFalse] at hL1
  contradiction

private theorem smt_value_rel_of_aci_norm_l1_marker_eq_true_right_translation
    (M : SmtModel) (f payload y : Term) :
    RuleProofs.eo_has_smt_translation y ->
    __eo_l_1___aci_norm_eq
      (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) payload)
      y = Term.Boolean true ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt payload))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hYTrans hL1
  have hYNe : y ≠ Term.Stuck := eo_has_smt_translation_ne_stuck y hYTrans
  have hIte :
      __eo_ite (__eo_eq payload y) (Term.Boolean true)
          (__eo_l_2___aci_norm_eq
            (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) payload)
            y) =
        Term.Boolean true := by
    cases y <;> try
      simpa [__eo_l_1___aci_norm_eq] using hL1
  rcases eo_ite_eq_true_cases
      (__eo_eq payload y) (Term.Boolean true)
      (__eo_l_2___aci_norm_eq
        (Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) payload)
        y)
      hIte with hPayload | hL2
  · have hyp : y = payload := eq_of_eo_eq_true_local payload y hPayload.1
    subst y
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt payload))
  · exact False.elim
      (aci_norm_l2_marker_right_translation_ne_true f payload y hYTrans hL2.2)

private def aciNormPayload : Term -> Term
  | Term.Apply (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) _) t => t
  | t => t

private theorem aciNormPayload_has_smt_translation_of_has_smt_translation
    (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  RuleProofs.eo_has_smt_translation (aciNormPayload t) := by
  intro hEq
  cases t <;> try exact hEq
  case Apply f x =>
    cases f <;> try exact hEq
    case Apply g y =>
      cases g <;> try exact hEq
      case UOp op =>
        cases op <;> try exact hEq
        exact False.elim (aci_sorted_marker_not_has_smt_translation y x hEq)

private theorem aciNormPayload_eq_self_of_has_smt_translation
    (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  aciNormPayload t = t := by
  intro hTrans
  cases t <;> try rfl
  case Apply f x =>
    cases f <;> try rfl
    case Apply g y =>
      cases g <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        exact False.elim (aci_sorted_marker_not_has_smt_translation y x hTrans)

@[simp] private theorem aciNormPayload_mk_aci_sorted (f payload : Term) :
    aciNormPayload
        (__eo_mk_apply
          (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f) payload) =
      payload := by
  cases payload <;> simp [aciNormPayload, __eo_mk_apply]

private theorem aciNormPayload_eq_self_of_eval_seq
    (M : SmtModel) (t : Term) :
  (∃ s, __smtx_model_eval M (__eo_to_smt t) = SmtValue.Seq s) ->
  aciNormPayload t = t := by
  intro hSeq
  cases t <;> try rfl
  case Apply f x =>
    cases f <;> try rfl
    case Apply g y =>
      cases g <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        case _at__at_aci_sorted =>
          rcases hSeq with ⟨s, hEval⟩
          have hMarkerEval :
              __smtx_model_eval M
                  (__eo_to_smt
                    (Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) y) x)) =
                SmtValue.NotValue := by
            change __smtx_model_eval M
                (SmtTerm.Apply
                  (SmtTerm.Apply SmtTerm.None (__eo_to_smt y))
                  (__eo_to_smt x)) =
              SmtValue.NotValue
            cases hy : __smtx_model_eval M (__eo_to_smt y) <;>
              cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
                simp [__smtx_model_eval, __smtx_model_eval_apply, hy, hx]
          rw [hMarkerEval] at hEval
          cases hEval

private theorem aciNormPayload_eq_self_of_eval_not_notvalue
    (M : SmtModel) (t : Term) :
  __smtx_model_eval M (__eo_to_smt t) ≠ SmtValue.NotValue ->
  aciNormPayload t = t := by
  intro hEvalNe
  cases t <;> try rfl
  case Apply f x =>
    cases f <;> try rfl
    case Apply g y =>
      cases g <;> try rfl
      case UOp op =>
        cases op <;> try rfl
        case _at__at_aci_sorted =>
          exact False.elim (hEvalNe (by
            change __smtx_model_eval M
                (SmtTerm.Apply
                  (SmtTerm.Apply SmtTerm.None (__eo_to_smt y))
                  (__eo_to_smt x)) =
              SmtValue.NotValue
            cases hy : __smtx_model_eval M (__eo_to_smt y) <;>
              cases hx : __smtx_model_eval M (__eo_to_smt x) <;>
                simp [__smtx_model_eval, __smtx_model_eval_apply, hy, hx]))

private theorem eo_typeof_or_eq_bool_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x) ->
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x) =
      Term.Bool := by
  intro hTrans
  let s := SmtTerm.or (__eo_to_smt y) (__eo_to_smt x)
  have hNN : term_has_non_none_type s := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa [s] using hTrans
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt y) (__eo_to_smt x)) hNN
  have hSmtTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.or (__eo_to_smt y) (__eo_to_smt x)) =
      SmtType.Bool
    rw [typeof_or_eq]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x) hTrans
  exact TranslationProofs.eo_to_smt_type_eq_bool (hMatch.symm.trans hSmtTy)

private theorem eo_typeof_and_eq_bool_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x) ->
    __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x) =
      Term.Bool := by
  intro hTrans
  let s := SmtTerm.and (__eo_to_smt y) (__eo_to_smt x)
  have hNN : term_has_non_none_type s := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa [s] using hTrans
  have hArgs := bool_binop_args_bool_of_non_none (op := SmtTerm.and)
    (typeof_and_eq (__eo_to_smt y) (__eo_to_smt x)) hNN
  have hSmtTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.and (__eo_to_smt y) (__eo_to_smt x)) =
      SmtType.Bool
    rw [typeof_and_eq]
    simp [hArgs.1, hArgs.2, native_ite, native_Teq]
  have hMatch := TranslationProofs.eo_to_smt_typeof_matches_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x) hTrans
  exact TranslationProofs.eo_to_smt_type_eq_bool (hMatch.symm.trans hSmtTy)

private theorem eo_has_bool_type_or_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x) ->
    RuleProofs.eo_has_bool_type y ∧ RuleProofs.eo_has_bool_type x := by
  intro hTrans
  let s := SmtTerm.or (__eo_to_smt y) (__eo_to_smt x)
  have hNN : term_has_non_none_type s := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa [s] using hTrans
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt y) (__eo_to_smt x)) hNN

private theorem eo_has_bool_type_and_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x) ->
    RuleProofs.eo_has_bool_type y ∧ RuleProofs.eo_has_bool_type x := by
  intro hTrans
  let s := SmtTerm.and (__eo_to_smt y) (__eo_to_smt x)
  have hNN : term_has_non_none_type s := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa [s] using hTrans
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.and)
    (typeof_and_eq (__eo_to_smt y) (__eo_to_smt x)) hNN

private theorem eo_has_bool_type_false_local :
    RuleProofs.eo_has_bool_type (Term.Boolean false) := by
  unfold RuleProofs.eo_has_bool_type
  change __smtx_typeof (SmtTerm.Boolean false) = SmtType.Bool
  rw [__smtx_typeof.eq_1]

private theorem eo_has_bool_type_or_of_bool_args_local (A B : Term) :
    RuleProofs.eo_has_bool_type A ->
    RuleProofs.eo_has_bool_type B ->
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) := by
  intro hA hB
  unfold RuleProofs.eo_has_bool_type at hA hB ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool
  rw [typeof_or_eq]
  simp [hA, hB, native_ite, native_Teq]

private theorem eo_has_bool_type_or_left_local (A B : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) ->
    RuleProofs.eo_has_bool_type A := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).1

private theorem eo_has_bool_type_or_right_local (A B : Term) :
    RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) ->
    RuleProofs.eo_has_bool_type B := by
  intro hTy
  unfold RuleProofs.eo_has_bool_type at hTy ⊢
  change __smtx_typeof (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
    SmtType.Bool at hTy
  have hNN : term_has_non_none_type
      (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) := by
    unfold term_has_non_none_type
    rw [hTy]
    simp
  exact (bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq (__eo_to_smt A) (__eo_to_smt B)) hNN).2

private theorem eo_interprets_bool_cases_local
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  RuleProofs.eo_has_bool_type t ->
  eo_interprets M t true ∨ eo_interprets M t false := by
  intro hTy
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM t hTy with
    ⟨b, hEval⟩
  cases b
  · exact Or.inr (RuleProofs.eo_interprets_of_bool_eval M t false hTy hEval)
  · exact Or.inl (RuleProofs.eo_interprets_of_bool_eval M t true hTy hEval)

private theorem eo_interprets_or_left_intro_local
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
  eo_interprets M A true ->
  RuleProofs.eo_has_bool_type B ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B)
    true := by
  intro hATrue hBBool
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_of_interprets_true M A hATrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hATrue ⊢
  change smt_interprets M (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) true
  cases hATrue with
  | intro_true hTyA hEvalA =>
      refine smt_interprets.intro_true M _ ?_ ?_
      · simpa [RuleProofs.eo_has_bool_type] using
          eo_has_bool_type_or_of_bool_args_local A B hABool hBBool
      · rw [__smtx_model_eval.eq_7]
        rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with
          ⟨b, hEvalB⟩
        rw [hEvalA, hEvalB]
        cases b <;> simp [__smtx_model_eval_or, SmtEval.native_or]

private theorem eo_interprets_or_right_intro_local
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
  RuleProofs.eo_has_bool_type A ->
  eo_interprets M B true ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B)
    true := by
  intro hABool hBTrue
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_of_interprets_true M B hBTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hBTrue ⊢
  change smt_interprets M (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) true
  cases hBTrue with
  | intro_true hTyB hEvalB =>
      refine smt_interprets.intro_true M _ ?_ ?_
      · simpa [RuleProofs.eo_has_bool_type] using
          eo_has_bool_type_or_of_bool_args_local A B hABool hBBool
      · rw [__smtx_model_eval.eq_7]
        rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM A hABool with
          ⟨a, hEvalA⟩
        rw [hEvalA, hEvalB]
        cases a <;> simp [__smtx_model_eval_or, SmtEval.native_or]

private theorem eo_interprets_false_local (M : SmtModel) :
    eo_interprets M (Term.Boolean false) false := by
  rw [RuleProofs.eo_interprets_iff_smt_interprets]
  change smt_interprets M (SmtTerm.Boolean false) false
  refine smt_interprets.intro_false M (SmtTerm.Boolean false) ?_ ?_
  · rw [__smtx_typeof.eq_1]
  · rw [__smtx_model_eval.eq_1]

private theorem eo_interprets_or_right_of_left_false_local
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
  eo_interprets M A false ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) true ->
  eo_interprets M B true := by
  intro hAFalse hOrTrue
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse hOrTrue ⊢
  cases hAFalse with
  | intro_false _ hEvalA =>
      cases hOrTrue with
      | intro_true hTyOr hEvalOr =>
          have hBBool : RuleProofs.eo_has_bool_type B :=
            eo_has_bool_type_or_right_local A B
              (by simpa [RuleProofs.eo_has_bool_type] using hTyOr)
          refine smt_interprets.intro_true M (__eo_to_smt B) hBBool ?_
          change
            __smtx_model_eval M
                (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) =
              SmtValue.Boolean true at hEvalOr
          rw [__smtx_model_eval.eq_7] at hEvalOr
          rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM B hBBool with
            ⟨b, hEvalB⟩
          rw [hEvalA, hEvalB, __smtx_model_eval_or, SmtEval.native_or] at hEvalOr
          cases b <;> simp at hEvalOr
          exact hEvalB

private theorem eo_interprets_or_false_intro_local
    (M : SmtModel) (A B : Term) :
  eo_interprets M A false ->
  eo_interprets M B false ->
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B)
    false := by
  intro hAFalse hBFalse
  have hABool : RuleProofs.eo_has_bool_type A :=
    RuleProofs.eo_has_bool_type_of_interprets_false M A hAFalse
  have hBBool : RuleProofs.eo_has_bool_type B :=
    RuleProofs.eo_has_bool_type_of_interprets_false M B hBFalse
  rw [RuleProofs.eo_interprets_iff_smt_interprets] at hAFalse hBFalse ⊢
  change smt_interprets M (SmtTerm.or (__eo_to_smt A) (__eo_to_smt B)) false
  cases hAFalse with
  | intro_false _ hEvalA =>
      cases hBFalse with
      | intro_false _ hEvalB =>
          refine smt_interprets.intro_false M _ ?_ ?_
          · simpa [RuleProofs.eo_has_bool_type] using
              eo_has_bool_type_or_of_bool_args_local A B hABool hBBool
          · rw [__smtx_model_eval.eq_7, hEvalA, hEvalB]
            simp [__smtx_model_eval_or, SmtEval.native_or]

private theorem eo_interprets_or_false_left_local
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) false ->
  eo_interprets M A false := by
  intro hOrFalse
  have hOrBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) :=
    RuleProofs.eo_has_bool_type_of_interprets_false M _ hOrFalse
  have hABool : RuleProofs.eo_has_bool_type A :=
    eo_has_bool_type_or_left_local A B hOrBool
  have hBBool : RuleProofs.eo_has_bool_type B :=
    eo_has_bool_type_or_right_local A B hOrBool
  rcases eo_interprets_bool_cases_local M hM A hABool with hATrue | hAFalse
  · have hOrTrue :
        eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B)
          true :=
      eo_interprets_or_left_intro_local M hM A B hATrue hBBool
    exact False.elim
      ((RuleProofs.eo_interprets_true_not_false M _ hOrTrue) hOrFalse)
  · exact hAFalse

private theorem eo_interprets_or_false_right_local
    (M : SmtModel) (hM : model_total_typed M) (A B : Term) :
  eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) false ->
  eo_interprets M B false := by
  intro hOrFalse
  have hOrBool : RuleProofs.eo_has_bool_type
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B) :=
    RuleProofs.eo_has_bool_type_of_interprets_false M _ hOrFalse
  have hABool : RuleProofs.eo_has_bool_type A :=
    eo_has_bool_type_or_left_local A B hOrBool
  have hBBool : RuleProofs.eo_has_bool_type B :=
    eo_has_bool_type_or_right_local A B hOrBool
  rcases eo_interprets_bool_cases_local M hM B hBBool with hBTrue | hBFalse
  · have hOrTrue :
        eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) A) B)
          true :=
      eo_interprets_or_right_intro_local M hM A B hABool hBTrue
    exact False.elim
      ((RuleProofs.eo_interprets_true_not_false M _ hOrTrue) hOrFalse)
  · exact hBFalse

private inductive AciOrClause : Term -> Prop where
  | false : AciOrClause (Term.Boolean false)
  | cons (x xs : Term) : AciOrClause xs ->
      AciOrClause (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs)

private theorem aciOrClause_ne_stuck {c : Term} :
    AciOrClause c -> c ≠ Term.Stuck := by
  intro hClause
  cases hClause <;> simp

private theorem aciOrClause_get_nil_rec_ne_stuck {c : Term} :
    AciOrClause c ->
    __eo_get_nil_rec (Term.UOp UserOp.or) c ≠ Term.Stuck := by
  intro hClause
  induction hClause with
  | false =>
      simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | cons x xs hXs ih =>
      simpa [__eo_get_nil_rec, __eo_requires, native_ite, native_teq,
        native_not, SmtEval.native_not] using ih

private theorem is_ok_true_of_ne_stuck_local {x : Term} :
    x ≠ Term.Stuck ->
    __eo_is_ok x = Term.Boolean true := by
  intro hNe
  cases x <;> simp [__eo_is_ok, native_teq, native_not, SmtEval.native_not] at hNe ⊢

private theorem is_list_true_of_get_nil_rec_ne_stuck_local {f x : Term} :
    __eo_get_nil_rec f x ≠ Term.Stuck ->
    __eo_is_list f x = Term.Boolean true := by
  intro hRec
  have hF : f ≠ Term.Stuck := by
    intro hF
    subst f
    simpa [__eo_get_nil_rec] using hRec
  have hX : x ≠ Term.Stuck := by
    intro hX
    subst x
    simpa [__eo_get_nil_rec] using hRec
  simp [__eo_is_list, hF, hX, is_ok_true_of_ne_stuck_local hRec]

private theorem aciOrClause_is_list_true {c : Term} :
    AciOrClause c ->
    __eo_is_list (Term.UOp UserOp.or) c = Term.Boolean true := by
  intro hClause
  exact is_list_true_of_get_nil_rec_ne_stuck_local
    (aciOrClause_get_nil_rec_ne_stuck hClause)

private theorem aciOrClause_of_is_list_true {c : Term} :
    __eo_is_list (Term.UOp UserOp.or) c = Term.Boolean true ->
    AciOrClause c := by
  intro hList
  cases c with
  | Stuck =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, native_teq,
        native_not, SmtEval.native_not] at hList
  | Boolean b =>
      cases b
      · exact AciOrClause.false
      · simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
          __eo_is_list_nil, native_ite, native_teq, native_not,
          SmtEval.native_not] at hList
  | Apply f a =>
      cases f with
      | Apply g x =>
          cases g with
          | UOp op =>
              cases op <;>
                simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec,
                  __eo_requires, __eo_is_list_nil, native_ite, native_teq,
                  native_not, SmtEval.native_not] at hList
              case or =>
                exact AciOrClause.cons x a
                  (aciOrClause_of_is_list_true
                    (is_list_true_of_get_nil_rec_ne_stuck_local hList))
          | _ =>
              simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec,
                __eo_requires, __eo_is_list_nil, native_ite, native_teq,
                native_not, SmtEval.native_not] at hList
      | _ =>
          simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
            __eo_is_list_nil, native_ite, native_teq, native_not,
            SmtEval.native_not] at hList
  | _ =>
      simp [__eo_is_list, __eo_is_ok, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not] at hList

private theorem aciOr_concat_rec_cons (x xs z : Term) :
    __eo_list_concat_rec xs z ≠ Term.Stuck ->
    __eo_list_concat_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) z =
      Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
        (__eo_list_concat_rec xs z) := by
  intro hTail
  cases z with
  | Stuck =>
      have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
        cases xs <;> simp [__eo_list_concat_rec]
      exact False.elim (hTail hStuck)
  | _ =>
      simp [__eo_list_concat_rec, __eo_mk_apply]

private theorem aciOr_concat_rec_preserves_clause {c1 c2 : Term} :
    AciOrClause c1 ->
    AciOrClause c2 ->
    AciOrClause (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC2
  have hConcatFalse (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | false =>
      rw [hConcatFalse c2]
      exact hC2
  | cons x xs hXs ih =>
      have hTail : AciOrClause (__eo_list_concat_rec xs c2) := ih hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        aciOrClause_ne_stuck hTail
      rw [aciOr_concat_rec_cons x xs c2 hTailNe]
      exact AciOrClause.cons x (__eo_list_concat_rec xs c2) hTail

private theorem aciOr_concat_rec_preserves_bool_type {c1 c2 : Term} :
    AciOrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC1Bool hC2Bool
  have hConcatFalse (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | false =>
      rw [hConcatFalse c2]
      exact hC2Bool
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hC1Bool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        ih hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [aciOr_concat_rec_cons x xs c2 hTailNe]
      exact eo_has_bool_type_or_of_bool_args_local
        x (__eo_list_concat_rec xs c2) hXBool hTailBool

private theorem aciOr_concat_preserves_clause {c1 c2 : Term} :
    AciOrClause c1 ->
    AciOrClause c2 ->
    AciOrClause (__eo_list_concat (Term.UOp UserOp.or) c1 c2) := by
  intro hC1 hC2
  change AciOrClause
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [aciOrClause_is_list_true hC1, aciOrClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciOr_concat_rec_preserves_clause hC1 hC2

private theorem aciOr_concat_preserves_bool_type {c1 c2 : Term} :
    AciOrClause c1 ->
    AciOrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat (Term.UOp UserOp.or) c1 c2) := by
  intro hC1 hC2 hC1Bool hC2Bool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [aciOrClause_is_list_true hC1, aciOrClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciOr_concat_rec_preserves_bool_type hC1 hC1Bool hC2Bool

private theorem aciOr_concat_rec_true_of_left_true
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    AciOrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c1 true ->
    eo_interprets M (__eo_list_concat_rec c1 c2) true := by
  intro hC1 hC1Bool hC2Bool hC1True
  have hConcatFalse (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | false =>
      exact False.elim
        ((RuleProofs.eo_interprets_true_not_false M _ hC1True)
          (eo_interprets_false_local M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hC1Bool
      have hOrTrue :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs)
            true := by
        simpa using hC1True
      rcases eo_interprets_bool_cases_local M hM x hXBool with hXTrue | hXFalse
      · have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
          aciOr_concat_rec_preserves_bool_type hXs hXsBool hC2Bool
        have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rw [aciOr_concat_rec_cons x xs c2 hTailNe]
        exact eo_interprets_or_left_intro_local M hM
          x (__eo_list_concat_rec xs c2) hXTrue hTailBool
      · have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false_local M hM x xs hXFalse hOrTrue
        have hTailTrue : eo_interprets M (__eo_list_concat_rec xs c2) true :=
          ih hXsBool hC2Bool hXsTrue
        have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
          aciOr_concat_rec_preserves_bool_type hXs hXsBool hC2Bool
        have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
          RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
        rw [aciOr_concat_rec_cons x xs c2 hTailNe]
        exact eo_interprets_or_right_intro_local M hM
          x (__eo_list_concat_rec xs c2) hXBool hTailTrue

private theorem aciOr_concat_rec_true_of_right_true
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    AciOrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 true ->
    eo_interprets M (__eo_list_concat_rec c1 c2) true := by
  intro hC1 hC1Bool hC2Bool hC2True
  have hConcatFalse (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | false =>
      rw [hConcatFalse c2]
      exact hC2True
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hC1Bool
      have hTailTrue : eo_interprets M (__eo_list_concat_rec xs c2) true :=
        ih hXsBool hC2Bool hC2True
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        aciOr_concat_rec_preserves_bool_type hXs hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [aciOr_concat_rec_cons x xs c2 hTailNe]
      exact eo_interprets_or_right_intro_local M hM
        x (__eo_list_concat_rec xs c2) hXBool hTailTrue

private theorem aciOr_concat_true_of_left_true
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    AciOrClause c1 ->
    AciOrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c1 true ->
    eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2) true := by
  intro hC1 hC2 hC1Bool hC2Bool hC1True
  change eo_interprets M
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) true
  rw [aciOrClause_is_list_true hC1, aciOrClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciOr_concat_rec_true_of_left_true M hM hC1 hC1Bool hC2Bool hC1True

private theorem aciOr_concat_true_of_right_true
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    AciOrClause c1 ->
    AciOrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c2 true ->
    eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2) true := by
  intro hC1 hC2 hC1Bool hC2Bool hC2True
  change eo_interprets M
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) true
  rw [aciOrClause_is_list_true hC1, aciOrClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciOr_concat_rec_true_of_right_true M hM hC1 hC1Bool hC2Bool hC2True

private theorem aciOr_concat_false_implies_left_false
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    AciOrClause c1 ->
    AciOrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2) false ->
    eo_interprets M c1 false := by
  intro hC1 hC2 hC1Bool hC2Bool hConcatFalse
  rcases eo_interprets_bool_cases_local M hM c1 hC1Bool with hC1True | hC1False
  · have hConcatTrue :
        eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2) true :=
      aciOr_concat_true_of_left_true M hM hC1 hC2 hC1Bool hC2Bool hC1True
    exact False.elim
      ((RuleProofs.eo_interprets_true_not_false M _ hConcatTrue) hConcatFalse)
  · exact hC1False

private theorem aciOr_concat_false_implies_right_false
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    AciOrClause c1 ->
    AciOrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2) false ->
    eo_interprets M c2 false := by
  intro hC1 hC2 hC1Bool hC2Bool hConcatFalse
  rcases eo_interprets_bool_cases_local M hM c2 hC2Bool with hC2True | hC2False
  · have hConcatTrue :
        eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2) true :=
      aciOr_concat_true_of_right_true M hM hC1 hC2 hC1Bool hC2Bool hC2True
    exact False.elim
      ((RuleProofs.eo_interprets_true_not_false M _ hConcatTrue) hConcatFalse)
  · exact hC2False

private theorem aciOr_concat_rec_false_of_both_false
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    AciOrClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c1 false ->
    eo_interprets M c2 false ->
    eo_interprets M (__eo_list_concat_rec c1 c2) false := by
  intro hC1 hC1Bool hC2Bool hC1False hC2False
  have hConcatFalse (z : Term) :
      __eo_list_concat_rec (Term.Boolean false) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | false =>
      rw [hConcatFalse c2]
      exact hC2False
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hC1Bool
      have hOrFalse :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs)
            false := by
        simpa using hC1False
      have hXFalse : eo_interprets M x false :=
        eo_interprets_or_false_left_local M hM x xs hOrFalse
      have hXsFalse : eo_interprets M xs false :=
        eo_interprets_or_false_right_local M hM x xs hOrFalse
      have hTailFalse : eo_interprets M (__eo_list_concat_rec xs c2) false :=
        ih hXsBool hC2Bool hXsFalse hC2False
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        aciOr_concat_rec_preserves_bool_type hXs hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [aciOr_concat_rec_cons x xs c2 hTailNe]
      exact eo_interprets_or_false_intro_local M x
        (__eo_list_concat_rec xs c2) hXFalse hTailFalse

private theorem aciOr_concat_false_of_both_false
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    AciOrClause c1 ->
    AciOrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    eo_interprets M c1 false ->
    eo_interprets M c2 false ->
    eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2) false := by
  intro hC1 hC2 hC1Bool hC2Bool hC1False hC2False
  change eo_interprets M
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2))) false
  rw [aciOrClause_is_list_true hC1, aciOrClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciOr_concat_rec_false_of_both_false M hM hC1 hC1Bool hC2Bool
    hC1False hC2False

private theorem aciOr_concat_true_iff
    (M : SmtModel) (hM : model_total_typed M) {c1 c2 : Term} :
    AciOrClause c1 ->
    AciOrClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    (eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2) true ↔
      eo_interprets M c1 true ∨ eo_interprets M c2 true) := by
  intro hC1 hC2 hC1Bool hC2Bool
  constructor
  · intro hConcatTrue
    rcases eo_interprets_bool_cases_local M hM c1 hC1Bool with hC1True | hC1False
    · exact Or.inl hC1True
    · rcases eo_interprets_bool_cases_local M hM c2 hC2Bool with hC2True | hC2False
      · exact Or.inr hC2True
      · have hConcatFalse :
            eo_interprets M (__eo_list_concat (Term.UOp UserOp.or) c1 c2)
              false :=
          aciOr_concat_false_of_both_false M hM hC1 hC2 hC1Bool hC2Bool
            hC1False hC2False
        exact False.elim
          ((RuleProofs.eo_interprets_true_not_false M _ hConcatTrue)
            hConcatFalse)
  · intro hEither
    cases hEither with
    | inl hC1True =>
        exact aciOr_concat_true_of_left_true M hM hC1 hC2 hC1Bool hC2Bool
          hC1True
    | inr hC2True =>
        exact aciOr_concat_true_of_right_true M hM hC1 hC2 hC1Bool hC2Bool
          hC2True

private theorem eo_eq_eq_true_of_eq_local {x y : Term} :
    x = y ->
    x ≠ Term.Stuck ->
    y ≠ Term.Stuck ->
    __eo_eq x y = Term.Boolean true := by
  intro hEq hX hY
  subst y
  cases x <;> simp [__eo_eq, native_teq] at hX ⊢

private theorem eo_eq_eq_false_of_ne_local {x y : Term} :
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

private theorem aciOr_erase_all_rec_preserves_clause {c e : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    AciOrClause (__eo_list_erase_all_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_all_rec] using AciOrClause.false
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTail : AciOrClause (__eo_list_erase_all_rec xs e) :=
        ih hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        aciOrClause_ne_stuck hTail
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq_local hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact hTail
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
                (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact AciOrClause.cons x (__eo_list_erase_all_rec xs e) hTail

private theorem aciOr_erase_all_rec_preserves_bool_type {c e : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_all_rec] using eo_has_bool_type_false_local
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec xs e) :=
        ih hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq_local hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact hTailBool
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
                (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact eo_has_bool_type_or_of_bool_args_local
          x (__eo_list_erase_all_rec xs e) hXBool hTailBool

private theorem aciOr_erase_all_rec_true_of_lit_false
    (M : SmtModel) (hM : model_total_typed M) {c e : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type e ->
    eo_interprets M e false ->
    eo_interprets M c true ->
    eo_interprets M (__eo_list_erase_all_rec c e) true := by
  intro hClause hCBool hE hEBool hEFalse hCTrue
  induction hClause generalizing e with
  | false =>
      exact False.elim
        ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
          (eo_interprets_false_local M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hOrTrue :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs)
            true := by
        simpa using hCTrue
      have hTailBool :
          RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec xs e) :=
        aciOr_erase_all_rec_preserves_bool_type hXs hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      by_cases hEq : x = e
      · have hXFalse : eo_interprets M x false := by
          simpa [hEq] using hEFalse
        have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false_local M hM x xs hXFalse hOrTrue
        have hTailTrue : eo_interprets M (__eo_list_erase_all_rec xs e) true :=
          ih hXsBool hE hEBool hEFalse hXsTrue
        have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq_local hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact hTailTrue
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
                (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rcases eo_interprets_bool_cases_local M hM x hXBool with hXTrue | hXFalse
        · rw [hStep]
          exact eo_interprets_or_left_intro_local M hM x
            (__eo_list_erase_all_rec xs e) hXTrue hTailBool
        · have hXsTrue : eo_interprets M xs true :=
            eo_interprets_or_right_of_left_false_local M hM x xs hXFalse hOrTrue
          have hTailTrue : eo_interprets M (__eo_list_erase_all_rec xs e) true :=
            ih hXsBool hE hEBool hEFalse hXsTrue
          rw [hStep]
          exact eo_interprets_or_right_intro_local M hM x
            (__eo_list_erase_all_rec xs e) hXBool hTailTrue

private theorem aciOr_erase_all_rec_true_implies_original_true
    (M : SmtModel) (hM : model_total_typed M) {c e : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    eo_interprets M (__eo_list_erase_all_rec c e) true ->
    eo_interprets M c true := by
  intro hClause hCBool hE hEraseTrue
  induction hClause generalizing e with
  | false =>
      simpa [__eo_list_erase_all_rec] using hEraseTrue
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailBool :
          RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec xs e) :=
        aciOr_erase_all_rec_preserves_bool_type hXs hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq_local hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        have hTailTrue : eo_interprets M (__eo_list_erase_all_rec xs e) true := by
          simpa [hStep] using hEraseTrue
        have hXsTrue : eo_interprets M xs true := ih hXsBool hE hTailTrue
        exact eo_interprets_or_right_intro_local M hM x xs hXBool hXsTrue
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
                (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        have hEraseOr :
            eo_interprets M
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
                (__eo_list_erase_all_rec xs e)) true := by
          simpa [hStep] using hEraseTrue
        rcases eo_interprets_bool_cases_local M hM x hXBool with hXTrue | hXFalse
        · exact eo_interprets_or_left_intro_local M hM x xs hXTrue hXsBool
        · have hTailTrue : eo_interprets M (__eo_list_erase_all_rec xs e) true :=
            eo_interprets_or_right_of_left_false_local M hM x
              (__eo_list_erase_all_rec xs e) hXFalse hEraseOr
          have hXsTrue : eo_interprets M xs true := ih hXsBool hE hTailTrue
          exact eo_interprets_or_right_intro_local M hM x xs hXBool hXsTrue

private theorem aciOr_setof_rec_structural {c : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    AciOrClause (__eo_list_setof_rec c) ∧
      RuleProofs.eo_has_bool_type (__eo_list_setof_rec c) := by
  intro hClause hCBool
  induction hClause with
  | false =>
      exact ⟨by simpa [__eo_list_setof_rec] using AciOrClause.false,
        by simpa [__eo_list_setof_rec] using eo_has_bool_type_false_local⟩
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailClause : AciOrClause (__eo_list_setof_rec xs) := (ih hXsBool).1
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_setof_rec xs) :=
        (ih hXsBool).2
      have hEraseClause :
          AciOrClause (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        aciOr_erase_all_rec_preserves_clause hTailClause hTailBool hX
      have hEraseBool :
          RuleProofs.eo_has_bool_type
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        aciOr_erase_all_rec_preserves_bool_type hTailClause hTailBool hX
      have hEraseNe :
          __eo_list_erase_all_rec (__eo_list_setof_rec xs) x ≠ Term.Stuck :=
        aciOrClause_ne_stuck hEraseClause
      have hStep :
          __eo_list_setof_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) =
            Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) := by
        simp [__eo_list_setof_rec, __eo_mk_apply, hX, hEraseNe]
      rw [hStep]
      exact ⟨
        AciOrClause.cons x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hEraseClause,
        eo_has_bool_type_or_of_bool_args_local x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hXBool hEraseBool⟩

private theorem aciOr_setof_rec_true
    (M : SmtModel) (hM : model_total_typed M) {c : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    eo_interprets M (__eo_list_setof_rec c) true := by
  intro hClause hCBool hCTrue
  induction hClause with
  | false =>
      exact False.elim
        ((RuleProofs.eo_interprets_true_not_false M _ hCTrue)
          (eo_interprets_false_local M))
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hOrTrue :
          eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs)
            true := by
        simpa using hCTrue
      have hTailStruct := aciOr_setof_rec_structural hXs hXsBool
      have hEraseBool :
          RuleProofs.eo_has_bool_type
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        aciOr_erase_all_rec_preserves_bool_type hTailStruct.1 hTailStruct.2 hX
      have hEraseNe :
          __eo_list_erase_all_rec (__eo_list_setof_rec xs) x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hEraseBool
      have hStep :
          __eo_list_setof_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) =
            Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) := by
        simp [__eo_list_setof_rec, __eo_mk_apply, hX, hEraseNe]
      rcases eo_interprets_bool_cases_local M hM x hXBool with hXTrue | hXFalse
      · rw [hStep]
        exact eo_interprets_or_left_intro_local M hM x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hXTrue hEraseBool
      · have hXsTrue : eo_interprets M xs true :=
          eo_interprets_or_right_of_left_false_local M hM x xs hXFalse hOrTrue
        have hSetXsTrue : eo_interprets M (__eo_list_setof_rec xs) true :=
          ih hXsBool hXsTrue
        have hEraseTrue :
            eo_interprets M
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) true :=
          aciOr_erase_all_rec_true_of_lit_false M hM hTailStruct.1
            hTailStruct.2 hX hXBool hXFalse hSetXsTrue
        rw [hStep]
        exact eo_interprets_or_right_intro_local M hM x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hXBool hEraseTrue

private theorem aciOr_setof_rec_true_implies_original_true
    (M : SmtModel) (hM : model_total_typed M) {c : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M (__eo_list_setof_rec c) true ->
    eo_interprets M c true := by
  intro hClause hCBool hSetTrue
  induction hClause with
  | false =>
      simpa [__eo_list_setof_rec] using hSetTrue
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        eo_has_bool_type_or_right_local x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailStruct := aciOr_setof_rec_structural hXs hXsBool
      have hEraseBool :
          RuleProofs.eo_has_bool_type
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        aciOr_erase_all_rec_preserves_bool_type hTailStruct.1 hTailStruct.2 hX
      have hEraseNe :
          __eo_list_erase_all_rec (__eo_list_setof_rec xs) x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hEraseBool
      have hStep :
          __eo_list_setof_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.or) x) xs) =
            Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) := by
        simp [__eo_list_setof_rec, __eo_mk_apply, hX, hEraseNe]
      have hSetOr :
          eo_interprets M
            (Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x)) true := by
        simpa [hStep] using hSetTrue
      rcases eo_interprets_bool_cases_local M hM x hXBool with hXTrue | hXFalse
      · exact eo_interprets_or_left_intro_local M hM x xs hXTrue hXsBool
      · have hEraseTrue :
            eo_interprets M
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) true :=
          eo_interprets_or_right_of_left_false_local M hM x
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hXFalse hSetOr
        have hSetXsTrue : eo_interprets M (__eo_list_setof_rec xs) true :=
          aciOr_erase_all_rec_true_implies_original_true M hM
            hTailStruct.1 hTailStruct.2 hX hEraseTrue
        have hXsTrue : eo_interprets M xs true := ih hXsBool hSetXsTrue
        exact eo_interprets_or_right_intro_local M hM x xs hXBool hXsTrue

private theorem aciOr_setof_preserves_clause {c : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    AciOrClause (__eo_list_setof (Term.UOp UserOp.or) c) := by
  intro hClause hCBool
  change AciOrClause
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c) (Term.Boolean true)
      (__eo_list_setof_rec c))
  rw [aciOrClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact (aciOr_setof_rec_structural hClause hCBool).1

private theorem aciOr_setof_preserves_bool_type {c : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type (__eo_list_setof (Term.UOp UserOp.or) c) := by
  intro hClause hCBool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c) (Term.Boolean true)
      (__eo_list_setof_rec c))
  rw [aciOrClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact (aciOr_setof_rec_structural hClause hCBool).2

private theorem aciOr_setof_true
    (M : SmtModel) (hM : model_total_typed M) {c : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M c true ->
    eo_interprets M (__eo_list_setof (Term.UOp UserOp.or) c) true := by
  intro hClause hCBool hCTrue
  change eo_interprets M
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c) (Term.Boolean true)
      (__eo_list_setof_rec c)) true
  rw [aciOrClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciOr_setof_rec_true M hM hClause hCBool hCTrue

private theorem aciOr_setof_true_implies_original_true
    (M : SmtModel) (hM : model_total_typed M) {c : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    eo_interprets M (__eo_list_setof (Term.UOp UserOp.or) c) true ->
    eo_interprets M c true := by
  intro hClause hCBool hSetTrue
  change eo_interprets M
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c) (Term.Boolean true)
      (__eo_list_setof_rec c)) true at hSetTrue
  rw [aciOrClause_is_list_true hClause] at hSetTrue
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not] at hSetTrue
  exact aciOr_setof_rec_true_implies_original_true M hM hClause hCBool hSetTrue

private theorem aciOr_singleton_elim_preserves_bool_type {c : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type
      (__eo_list_singleton_elim (Term.UOp UserOp.or) c) := by
  intro hClause hCBool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c) (Term.Boolean true)
      (__eo_list_singleton_elim_2 c))
  rw [aciOrClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hClause with
  | false =>
      simpa [__eo_list_singleton_elim_2] using hCBool
  | cons x xs hXs =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hCBool
      cases hXs with
      | false =>
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hXBool
      | cons y ys hYs =>
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hCBool

private theorem aciOr_singleton_elim_true_iff
    (M : SmtModel) (hM : model_total_typed M) {c : Term} :
    AciOrClause c ->
    RuleProofs.eo_has_bool_type c ->
    (eo_interprets M (__eo_list_singleton_elim (Term.UOp UserOp.or) c) true ↔
      eo_interprets M c true) := by
  intro hClause hCBool
  change
    (eo_interprets M
        (__eo_requires (__eo_is_list (Term.UOp UserOp.or) c) (Term.Boolean true)
          (__eo_list_singleton_elim_2 c)) true ↔
      eo_interprets M c true)
  rw [aciOrClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hClause with
  | false =>
      simp [__eo_list_singleton_elim_2]
  | cons x xs hXs =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_left_local x xs hCBool
      cases hXs with
      | false =>
          have hIff :
              (eo_interprets M x true ↔
                eo_interprets M
                  (Term.Apply (Term.Apply (Term.UOp UserOp.or) x)
                    (Term.Boolean false)) true) := by
            constructor
            · intro hXTrue
              exact eo_interprets_or_left_intro_local M hM x (Term.Boolean false)
                hXTrue eo_has_bool_type_false_local
            · intro hOrTrue
              rcases eo_interprets_bool_cases_local M hM x hXBool with
                hXTrue | hXFalse
              · exact hXTrue
              · have hFalseTrue :
                    eo_interprets M (Term.Boolean false) true :=
                  eo_interprets_or_right_of_left_false_local M hM
                    x (Term.Boolean false) hXFalse hOrTrue
                exact False.elim
                  ((RuleProofs.eo_interprets_true_not_false M _ hFalseTrue)
                    (eo_interprets_false_local M))
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hIff
      | cons y ys hYs =>
          simp [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq]

private inductive AciAndClause : Term -> Prop where
  | true : AciAndClause (Term.Boolean true)
  | cons (x xs : Term) : AciAndClause xs ->
      AciAndClause (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs)

private theorem aciAndClause_ne_stuck {c : Term} :
    AciAndClause c -> c ≠ Term.Stuck := by
  intro hClause
  cases hClause <;> simp

private theorem aciAndClause_get_nil_rec_ne_stuck {c : Term} :
    AciAndClause c ->
    __eo_get_nil_rec (Term.UOp UserOp.and) c ≠ Term.Stuck := by
  intro hClause
  induction hClause with
  | true =>
      simp [__eo_get_nil_rec, __eo_requires, __eo_is_list_nil, native_ite,
        native_teq, native_not, SmtEval.native_not]
  | cons x xs hXs ih =>
      simpa [__eo_get_nil_rec, __eo_requires, native_ite, native_teq,
        native_not, SmtEval.native_not] using ih

private theorem aciAndClause_is_list_true {c : Term} :
    AciAndClause c ->
    __eo_is_list (Term.UOp UserOp.and) c = Term.Boolean true := by
  intro hClause
  exact is_list_true_of_get_nil_rec_ne_stuck_local
    (aciAndClause_get_nil_rec_ne_stuck hClause)

private theorem aciAnd_concat_rec_cons (x xs z : Term) :
    __eo_list_concat_rec xs z ≠ Term.Stuck ->
    __eo_list_concat_rec
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) z =
      Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
        (__eo_list_concat_rec xs z) := by
  intro hTail
  cases z with
  | Stuck =>
      have hStuck : __eo_list_concat_rec xs Term.Stuck = Term.Stuck := by
        cases xs <;> simp [__eo_list_concat_rec]
      exact False.elim (hTail hStuck)
  | _ =>
      simp [__eo_list_concat_rec, __eo_mk_apply]

private theorem aciAnd_concat_rec_preserves_clause {c1 c2 : Term} :
    AciAndClause c1 ->
    AciAndClause c2 ->
    AciAndClause (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC2
  have hConcatTrue (z : Term) :
      __eo_list_concat_rec (Term.Boolean true) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | true =>
      rw [hConcatTrue c2]
      exact hC2
  | cons x xs hXs ih =>
      have hTail : AciAndClause (__eo_list_concat_rec xs c2) := ih hC2
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        aciAndClause_ne_stuck hTail
      rw [aciAnd_concat_rec_cons x xs c2 hTailNe]
      exact AciAndClause.cons x (__eo_list_concat_rec xs c2) hTail

private theorem aciAnd_concat_rec_preserves_bool_type {c1 c2 : Term} :
    AciAndClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat_rec c1 c2) := by
  intro hC1 hC1Bool hC2Bool
  have hConcatTrue (z : Term) :
      __eo_list_concat_rec (Term.Boolean true) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | true =>
      rw [hConcatTrue c2]
      exact hC2Bool
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hC1Bool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        ih hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [aciAnd_concat_rec_cons x xs c2 hTailNe]
      exact RuleProofs.eo_has_bool_type_and_of_bool_args
        x (__eo_list_concat_rec xs c2) hXBool hTailBool

private theorem aciAnd_concat_preserves_clause {c1 c2 : Term} :
    AciAndClause c1 ->
    AciAndClause c2 ->
    AciAndClause (__eo_list_concat (Term.UOp UserOp.and) c1 c2) := by
  intro hC1 hC2
  change AciAndClause
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [aciAndClause_is_list_true hC1, aciAndClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciAnd_concat_rec_preserves_clause hC1 hC2

private theorem aciAnd_concat_preserves_bool_type {c1 c2 : Term} :
    AciAndClause c1 ->
    AciAndClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    RuleProofs.eo_has_bool_type (__eo_list_concat (Term.UOp UserOp.and) c1 c2) := by
  intro hC1 hC2 hC1Bool hC2Bool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c1) (Term.Boolean true)
      (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c2) (Term.Boolean true)
        (__eo_list_concat_rec c1 c2)))
  rw [aciAndClause_is_list_true hC1, aciAndClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciAnd_concat_rec_preserves_bool_type hC1 hC1Bool hC2Bool

private theorem aciAnd_concat_rec_true_iff
    (M : SmtModel) {c1 c2 : Term} :
    AciAndClause c1 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    (eo_interprets M (__eo_list_concat_rec c1 c2) true ↔
      eo_interprets M c1 true ∧ eo_interprets M c2 true) := by
  intro hC1 hC1Bool hC2Bool
  have hConcatTrue (z : Term) :
      __eo_list_concat_rec (Term.Boolean true) z = z := by
    cases z <;> simp [__eo_list_concat_rec]
  induction hC1 generalizing c2 with
  | true =>
      rw [hConcatTrue c2]
      constructor
      · intro hC2True
        exact ⟨RuleProofs.eo_interprets_true M, hC2True⟩
      · intro h
        exact h.2
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hC1Bool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hC1Bool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_concat_rec xs c2) :=
        aciAnd_concat_rec_preserves_bool_type hXs hXsBool hC2Bool
      have hTailNe : __eo_list_concat_rec xs c2 ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      rw [aciAnd_concat_rec_cons x xs c2 hTailNe]
      constructor
      · intro hConcatTrue'
        have hXTrue : eo_interprets M x true :=
          RuleProofs.eo_interprets_and_left M x
            (__eo_list_concat_rec xs c2) hConcatTrue'
        have hTailTrue : eo_interprets M (__eo_list_concat_rec xs c2) true :=
          RuleProofs.eo_interprets_and_right M x
            (__eo_list_concat_rec xs c2) hConcatTrue'
        have hTail := (ih hXsBool hC2Bool).mp hTailTrue
        exact ⟨RuleProofs.eo_interprets_and_intro M x xs hXTrue hTail.1,
          hTail.2⟩
      · intro h
        have hXTrue : eo_interprets M x true :=
          RuleProofs.eo_interprets_and_left M x xs h.1
        have hXsTrue : eo_interprets M xs true :=
          RuleProofs.eo_interprets_and_right M x xs h.1
        have hTailTrue : eo_interprets M (__eo_list_concat_rec xs c2) true :=
          (ih hXsBool hC2Bool).mpr ⟨hXsTrue, h.2⟩
        exact RuleProofs.eo_interprets_and_intro M x
          (__eo_list_concat_rec xs c2) hXTrue hTailTrue

private theorem aciAnd_concat_true_iff
    (M : SmtModel) {c1 c2 : Term} :
    AciAndClause c1 ->
    AciAndClause c2 ->
    RuleProofs.eo_has_bool_type c1 ->
    RuleProofs.eo_has_bool_type c2 ->
    (eo_interprets M (__eo_list_concat (Term.UOp UserOp.and) c1 c2) true ↔
      eo_interprets M c1 true ∧ eo_interprets M c2 true) := by
  intro hC1 hC2 hC1Bool hC2Bool
  change
    (eo_interprets M
      (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c1) (Term.Boolean true)
        (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c2) (Term.Boolean true)
          (__eo_list_concat_rec c1 c2))) true ↔
      eo_interprets M c1 true ∧ eo_interprets M c2 true)
  rw [aciAndClause_is_list_true hC1, aciAndClause_is_list_true hC2]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciAnd_concat_rec_true_iff M hC1 hC1Bool hC2Bool

private theorem aciAnd_erase_all_rec_preserves_clause {c e : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    AciAndClause (__eo_list_erase_all_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | true =>
      simpa [__eo_list_erase_all_rec] using AciAndClause.true
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTail : AciAndClause (__eo_list_erase_all_rec xs e) :=
        ih hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        aciAndClause_ne_stuck hTail
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq_local hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact hTail
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact AciAndClause.cons x (__eo_list_erase_all_rec xs e) hTail

private theorem aciAnd_erase_all_rec_preserves_bool_type {c e : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec c e) := by
  intro hClause hCBool hE
  induction hClause generalizing e with
  | true =>
      simpa [__eo_list_erase_all_rec] using RuleProofs.eo_has_bool_type_true
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec xs e) :=
        ih hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq_local hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact hTailBool
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact RuleProofs.eo_has_bool_type_and_of_bool_args
          x (__eo_list_erase_all_rec xs e) hXBool hTailBool

private theorem aciAnd_erase_all_rec_true_of_lit_true
    (M : SmtModel) {c e : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    eo_interprets M e true ->
    eo_interprets M c true ->
    eo_interprets M (__eo_list_erase_all_rec c e) true := by
  intro hClause hCBool hE hETrue hCTrue
  induction hClause generalizing e with
  | true =>
      simpa [__eo_list_erase_all_rec] using hCTrue
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hXTrue : eo_interprets M x true :=
        RuleProofs.eo_interprets_and_left M x xs hCTrue
      have hXsTrue : eo_interprets M xs true :=
        RuleProofs.eo_interprets_and_right M x xs hCTrue
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec xs e) :=
        aciAnd_erase_all_rec_preserves_bool_type hXs hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq_local hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact ih hXsBool hE hETrue hXsTrue
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        rw [hStep]
        exact RuleProofs.eo_interprets_and_intro M x
          (__eo_list_erase_all_rec xs e) hXTrue
          (ih hXsBool hE hETrue hXsTrue)

private theorem aciAnd_erase_all_rec_true_implies_original_true
    (M : SmtModel) {c e : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    e ≠ Term.Stuck ->
    eo_interprets M e true ->
    eo_interprets M (__eo_list_erase_all_rec c e) true ->
    eo_interprets M c true := by
  intro hClause hCBool hE hETrue hEraseTrue
  induction hClause generalizing e with
  | true =>
      exact RuleProofs.eo_interprets_true M
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_erase_all_rec xs e) :=
        aciAnd_erase_all_rec_preserves_bool_type hXs hXsBool hE
      have hTailNe : __eo_list_erase_all_rec xs e ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hTailBool
      by_cases hEq : x = e
      · have hEqTerm : __eo_eq e x = Term.Boolean true :=
          eo_eq_eq_true_of_eq_local hEq.symm hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) e =
              __eo_list_erase_all_rec xs e := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        have hTailTrue : eo_interprets M (__eo_list_erase_all_rec xs e) true := by
          simpa [hStep] using hEraseTrue
        have hXsTrue : eo_interprets M xs true := ih hXsBool hE hETrue hTailTrue
        have hXTrue : eo_interprets M x true := by
          simpa [hEq] using hETrue
        exact RuleProofs.eo_interprets_and_intro M x xs hXTrue hXsTrue
      · have hEqTerm : __eo_eq e x = Term.Boolean false :=
          eo_eq_eq_false_of_ne_local (by
            intro hEx
            apply hEq
            exact hEx.symm) hE hX
        have hStep :
            __eo_list_erase_all_rec
                (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) e =
              Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                (__eo_list_erase_all_rec xs e) := by
          simp [__eo_list_erase_all_rec, __eo_prepend_if, __eo_not, hEqTerm,
            native_not, native_teq, hTailNe]
        have hEraseAnd :
            eo_interprets M
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                (__eo_list_erase_all_rec xs e)) true := by
          simpa [hStep] using hEraseTrue
        have hXTrue : eo_interprets M x true :=
          RuleProofs.eo_interprets_and_left M x
            (__eo_list_erase_all_rec xs e) hEraseAnd
        have hTailTrue : eo_interprets M (__eo_list_erase_all_rec xs e) true :=
          RuleProofs.eo_interprets_and_right M x
            (__eo_list_erase_all_rec xs e) hEraseAnd
        have hXsTrue : eo_interprets M xs true :=
          ih hXsBool hE hETrue hTailTrue
        exact RuleProofs.eo_interprets_and_intro M x xs hXTrue hXsTrue

private theorem aciAnd_setof_rec_structural {c : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    AciAndClause (__eo_list_setof_rec c) ∧
      RuleProofs.eo_has_bool_type (__eo_list_setof_rec c) := by
  intro hClause hCBool
  induction hClause with
  | true =>
      exact ⟨by simpa [__eo_list_setof_rec] using AciAndClause.true,
        by simpa [__eo_list_setof_rec] using RuleProofs.eo_has_bool_type_true⟩
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailClause : AciAndClause (__eo_list_setof_rec xs) := (ih hXsBool).1
      have hTailBool : RuleProofs.eo_has_bool_type (__eo_list_setof_rec xs) :=
        (ih hXsBool).2
      have hEraseClause :
          AciAndClause (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        aciAnd_erase_all_rec_preserves_clause hTailClause hTailBool hX
      have hEraseBool :
          RuleProofs.eo_has_bool_type
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        aciAnd_erase_all_rec_preserves_bool_type hTailClause hTailBool hX
      have hEraseNe :
          __eo_list_erase_all_rec (__eo_list_setof_rec xs) x ≠ Term.Stuck :=
        aciAndClause_ne_stuck hEraseClause
      have hStep :
          __eo_list_setof_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) =
            Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) := by
        simp [__eo_list_setof_rec, __eo_mk_apply, hX, hEraseNe]
      rw [hStep]
      exact ⟨
        AciAndClause.cons x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hEraseClause,
        RuleProofs.eo_has_bool_type_and_of_bool_args x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hXBool hEraseBool⟩

private theorem aciAnd_setof_rec_true_iff
    (M : SmtModel) {c : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    (eo_interprets M (__eo_list_setof_rec c) true ↔ eo_interprets M c true) := by
  intro hClause hCBool
  induction hClause with
  | true =>
      simp [__eo_list_setof_rec]
  | cons x xs hXs ih =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      have hXsBool : RuleProofs.eo_has_bool_type xs :=
        RuleProofs.eo_has_bool_type_and_right x xs hCBool
      have hX : x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type x hXBool
      have hTailStruct := aciAnd_setof_rec_structural hXs hXsBool
      have hEraseBool :
          RuleProofs.eo_has_bool_type
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) :=
        aciAnd_erase_all_rec_preserves_bool_type hTailStruct.1 hTailStruct.2 hX
      have hEraseNe :
          __eo_list_erase_all_rec (__eo_list_setof_rec xs) x ≠ Term.Stuck :=
        RuleProofs.term_ne_stuck_of_has_bool_type _ hEraseBool
      have hStep :
          __eo_list_setof_rec
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) x) xs) =
            Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) := by
        simp [__eo_list_setof_rec, __eo_mk_apply, hX, hEraseNe]
      constructor
      · intro hSetTrue
        have hSetAnd :
            eo_interprets M
              (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x)) true := by
          simpa [hStep] using hSetTrue
        have hXTrue : eo_interprets M x true :=
          RuleProofs.eo_interprets_and_left M x
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hSetAnd
        have hEraseTrue :
            eo_interprets M
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) true :=
          RuleProofs.eo_interprets_and_right M x
            (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hSetAnd
        have hSetXsTrue : eo_interprets M (__eo_list_setof_rec xs) true :=
          aciAnd_erase_all_rec_true_implies_original_true M hTailStruct.1
            hTailStruct.2 hX hXTrue hEraseTrue
        have hXsTrue : eo_interprets M xs true := (ih hXsBool).mp hSetXsTrue
        exact RuleProofs.eo_interprets_and_intro M x xs hXTrue hXsTrue
      · intro hAndTrue
        have hXTrue : eo_interprets M x true :=
          RuleProofs.eo_interprets_and_left M x xs hAndTrue
        have hXsTrue : eo_interprets M xs true :=
          RuleProofs.eo_interprets_and_right M x xs hAndTrue
        have hSetXsTrue : eo_interprets M (__eo_list_setof_rec xs) true :=
          (ih hXsBool).mpr hXsTrue
        have hEraseTrue :
            eo_interprets M
              (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) true :=
          aciAnd_erase_all_rec_true_of_lit_true M hTailStruct.1
            hTailStruct.2 hX hXTrue hSetXsTrue
        rw [hStep]
        exact RuleProofs.eo_interprets_and_intro M x
          (__eo_list_erase_all_rec (__eo_list_setof_rec xs) x) hXTrue hEraseTrue

private theorem aciAnd_setof_preserves_clause {c : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    AciAndClause (__eo_list_setof (Term.UOp UserOp.and) c) := by
  intro hClause hCBool
  change AciAndClause
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c) (Term.Boolean true)
      (__eo_list_setof_rec c))
  rw [aciAndClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact (aciAnd_setof_rec_structural hClause hCBool).1

private theorem aciAnd_setof_preserves_bool_type {c : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type (__eo_list_setof (Term.UOp UserOp.and) c) := by
  intro hClause hCBool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c) (Term.Boolean true)
      (__eo_list_setof_rec c))
  rw [aciAndClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact (aciAnd_setof_rec_structural hClause hCBool).2

private theorem aciAnd_setof_true_iff
    (M : SmtModel) {c : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    (eo_interprets M (__eo_list_setof (Term.UOp UserOp.and) c) true ↔
      eo_interprets M c true) := by
  intro hClause hCBool
  change
    (eo_interprets M
      (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c) (Term.Boolean true)
        (__eo_list_setof_rec c)) true ↔
      eo_interprets M c true)
  rw [aciAndClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  exact aciAnd_setof_rec_true_iff M hClause hCBool

private theorem aciAnd_singleton_elim_preserves_bool_type {c : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    RuleProofs.eo_has_bool_type
      (__eo_list_singleton_elim (Term.UOp UserOp.and) c) := by
  intro hClause hCBool
  change RuleProofs.eo_has_bool_type
    (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c) (Term.Boolean true)
      (__eo_list_singleton_elim_2 c))
  rw [aciAndClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hClause with
  | true =>
      simpa [__eo_list_singleton_elim_2] using hCBool
  | cons x xs hXs =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      cases hXs with
      | true =>
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hXBool
      | cons y ys hYs =>
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hCBool

private theorem aciAnd_singleton_elim_true_iff
    (M : SmtModel) {c : Term} :
    AciAndClause c ->
    RuleProofs.eo_has_bool_type c ->
    (eo_interprets M (__eo_list_singleton_elim (Term.UOp UserOp.and) c) true ↔
      eo_interprets M c true) := by
  intro hClause hCBool
  change
    (eo_interprets M
        (__eo_requires (__eo_is_list (Term.UOp UserOp.and) c) (Term.Boolean true)
          (__eo_list_singleton_elim_2 c)) true ↔
      eo_interprets M c true)
  rw [aciAndClause_is_list_true hClause]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases hClause with
  | true =>
      simp [__eo_list_singleton_elim_2]
  | cons x xs hXs =>
      have hXBool : RuleProofs.eo_has_bool_type x :=
        RuleProofs.eo_has_bool_type_and_left x xs hCBool
      cases hXs with
      | true =>
          have hIff :
              (eo_interprets M x true ↔
                eo_interprets M
                  (Term.Apply (Term.Apply (Term.UOp UserOp.and) x)
                    (Term.Boolean true)) true) := by
            constructor
            · intro hXTrue
              exact RuleProofs.eo_interprets_and_intro M x (Term.Boolean true)
                hXTrue (RuleProofs.eo_interprets_true M)
            · intro hAndTrue
              exact RuleProofs.eo_interprets_and_left M x (Term.Boolean true)
                hAndTrue
          simpa [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq] using hIff
      | cons y ys hYs =>
          simp [__eo_list_singleton_elim_2, __eo_is_list_nil, __eo_ite,
            native_ite, native_teq]

private theorem smt_value_rel_of_bool_interprets_iff
    (M : SmtModel) (hM : model_total_typed M) (a b : Term) :
  RuleProofs.eo_has_bool_type a ->
  RuleProofs.eo_has_bool_type b ->
  (eo_interprets M a true ↔ eo_interprets M b true) ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hABool hBBool hIff
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM a hABool with
    ⟨av, hAEval⟩
  rcases RuleProofs.eo_eval_is_boolean_of_has_bool_type M hM b hBBool with
    ⟨bv, hBEval⟩
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  cases av <;> cases bv
  · rw [hAEval, hBEval]
    simp [__smtx_model_eval_eq, native_veq]
  · have hBTrue : eo_interprets M b true :=
      RuleProofs.eo_interprets_of_bool_eval M b true hBBool hBEval
    have hATrue : eo_interprets M a true := hIff.mpr hBTrue
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hATrue
    cases hATrue with
    | intro_true _ hAEvalTrue =>
        rw [hAEval] at hAEvalTrue
        cases hAEvalTrue
  · have hATrue : eo_interprets M a true :=
      RuleProofs.eo_interprets_of_bool_eval M a true hABool hAEval
    have hBTrue : eo_interprets M b true := hIff.mp hATrue
    rw [RuleProofs.eo_interprets_iff_smt_interprets] at hBTrue
    cases hBTrue with
    | intro_true _ hBEvalTrue =>
        rw [hBEval] at hBEvalTrue
        cases hBEvalTrue
  · rw [hAEval, hBEval]
    simp [__smtx_model_eval_eq, native_veq]

private theorem eo_interprets_or_false_iff
    (M : SmtModel) (hM : model_total_typed M) (a : Term) :
  RuleProofs.eo_has_bool_type a ->
  (eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.or) a)
      (Term.Boolean false)) true ↔
    eo_interprets M a true) := by
  intro hABool
  constructor
  · intro hOrTrue
    rcases eo_interprets_bool_cases_local M hM a hABool with
      hATrue | hAFalse
    · exact hATrue
    · exfalso
      rw [RuleProofs.eo_interprets_iff_smt_interprets] at hOrTrue hAFalse
      cases hAFalse with
      | intro_false _ hEvalA =>
          cases hOrTrue with
          | intro_true _ hEvalOr =>
              change
                __smtx_model_eval M
                  (SmtTerm.or (__eo_to_smt a) (SmtTerm.Boolean false)) =
                    SmtValue.Boolean true at hEvalOr
              rw [__smtx_model_eval.eq_7, hEvalA, __smtx_model_eval.eq_1] at hEvalOr
              simp [__smtx_model_eval_or, SmtEval.native_or] at hEvalOr
  · intro hATrue
    exact eo_interprets_or_left_intro_local M hM a (Term.Boolean false)
      hATrue eo_has_bool_type_false_local

private theorem eo_interprets_and_true_iff
    (M : SmtModel) (a : Term) :
  RuleProofs.eo_has_bool_type a ->
  (eo_interprets M (Term.Apply (Term.Apply (Term.UOp UserOp.and) a)
      (Term.Boolean true)) true ↔
    eo_interprets M a true) := by
  intro _hABool
  constructor
  · intro hAndTrue
    exact RuleProofs.eo_interprets_and_left M a (Term.Boolean true) hAndTrue
  · intro hATrue
    exact RuleProofs.eo_interprets_and_intro M a (Term.Boolean true) hATrue
      (RuleProofs.eo_interprets_true M)

private theorem aci_norm_l1_or_false_eq_of_ne_false (t : Term) :
  t ≠ Term.Stuck ->
  t ≠ Term.Boolean false ->
  __eo_l_1___get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t =
    Term.Apply (Term.Apply (Term.UOp UserOp.or) t) (Term.Boolean false) := by
  intro hStuck hFalse
  cases t <;> simp [__eo_l_1___get_ai_norm_rec, __eo_l_2___get_ai_norm_rec,
    __eo_ite, __eo_eq, native_ite, native_teq] at hStuck hFalse ⊢
  case Boolean b =>
    cases b <;> simp at hFalse ⊢

private theorem aci_norm_l1_and_true_eq_of_ne_true (t : Term) :
  t ≠ Term.Stuck ->
  t ≠ Term.Boolean true ->
  __eo_l_1___get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t =
    Term.Apply (Term.Apply (Term.UOp UserOp.and) t) (Term.Boolean true) := by
  intro hStuck hTrue
  cases t <;> simp [__eo_l_1___get_ai_norm_rec, __eo_l_2___get_ai_norm_rec,
    __eo_ite, __eo_eq, native_ite, native_teq] at hStuck hTrue ⊢
  case Boolean b =>
    cases b <;> simp at hTrue ⊢

private theorem smt_value_rel_l1_or_false
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  RuleProofs.eo_has_bool_type t ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.or)
          (Term.Boolean false) t))) := by
  intro hBool
  by_cases hFalse : t = Term.Boolean false
  · subst t
    simp [__eo_l_1___get_ai_norm_rec, __eo_ite, __eo_eq, native_ite, native_teq,
      RuleProofs.smt_value_rel_refl]
  · have hNe : t ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type t hBool
    rw [aci_norm_l1_or_false_eq_of_ne_false t hNe hFalse]
    apply smt_value_rel_of_bool_interprets_iff M hM
    · exact hBool
    · exact eo_has_bool_type_or_of_bool_args_local _ _ hBool
        eo_has_bool_type_false_local
    · exact (eo_interprets_or_false_iff M hM t hBool).symm

private theorem smt_value_rel_l1_and_true
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  RuleProofs.eo_has_bool_type t ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.and)
          (Term.Boolean true) t))) := by
  intro hBool
  by_cases hTrue : t = Term.Boolean true
  · subst t
    simp [__eo_l_1___get_ai_norm_rec, __eo_ite, __eo_eq, native_ite, native_teq,
      RuleProofs.smt_value_rel_refl]
  · have hNe : t ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type t hBool
    rw [aci_norm_l1_and_true_eq_of_ne_true t hNe hTrue]
    apply smt_value_rel_of_bool_interprets_iff M hM
    · exact hBool
    · exact RuleProofs.eo_has_bool_type_and_of_bool_args _ _ hBool
        RuleProofs.eo_has_bool_type_true
    · exact (eo_interprets_and_true_iff M t hBool).symm

private theorem get_ai_norm_rec_or_eq_l1_of_not_or (t : Term) :
  RuleProofs.eo_has_bool_type t ->
  (∀ y x, t ≠ Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x) ->
  __get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t =
    __eo_l_1___get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t := by
  intro hBool hNotOr
  cases t <;> try rfl
  case Apply f x =>
    cases f <;> try rfl
    case Apply g y =>
      cases g <;> try
        (simp [RuleProofs.eo_has_bool_type] at hBool)
        <;> simp [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
      case Stuck =>
        have hBad :
            __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.Apply Term.Stuck y) x)) =
              SmtType.None := by
          change __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y))
              (__eo_to_smt x)) = SmtType.None
          exact smtx_typeof_apply_apply_none (__eo_to_smt x) (__eo_to_smt y)
        rw [hBad] at hBool
        cases hBool
      case UOp op =>
        cases op <;> simp [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite,
          native_teq]
        case or =>
          exact False.elim (hNotOr y x rfl)

private theorem get_ai_norm_rec_and_eq_l1_of_not_and (t : Term) :
  RuleProofs.eo_has_bool_type t ->
  (∀ y x, t ≠ Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x) ->
  __get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t =
    __eo_l_1___get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t := by
  intro hBool hNotAnd
  cases t <;> try rfl
  case Apply f x =>
    cases f <;> try rfl
    case Apply g y =>
      cases g <;> try
        (simp [RuleProofs.eo_has_bool_type] at hBool)
        <;> simp [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
      case Stuck =>
        have hBad :
            __smtx_typeof
              (__eo_to_smt (Term.Apply (Term.Apply Term.Stuck y) x)) =
              SmtType.None := by
          change __smtx_typeof
            (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y))
              (__eo_to_smt x)) = SmtType.None
          exact smtx_typeof_apply_apply_none (__eo_to_smt x) (__eo_to_smt y)
        rw [hBad] at hBool
        cases hBool
      case UOp op =>
        cases op <;> simp [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite,
          native_teq]
        case and =>
          exact False.elim (hNotAnd y x rfl)

private theorem smt_value_rel_get_ai_norm_rec_or_non_or
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  RuleProofs.eo_has_bool_type t ->
  (∀ y x, t ≠ Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x) ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M
      (__eo_to_smt
        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t))) := by
  intro hBool hNotOr
  rw [get_ai_norm_rec_or_eq_l1_of_not_or t hBool hNotOr]
  exact smt_value_rel_l1_or_false M hM t hBool

private theorem smt_value_rel_get_ai_norm_rec_and_non_and
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  RuleProofs.eo_has_bool_type t ->
  (∀ y x, t ≠ Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x) ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M
      (__eo_to_smt
        (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t))) := by
  intro hBool hNotAnd
  rw [get_ai_norm_rec_and_eq_l1_of_not_and t hBool hNotAnd]
  exact smt_value_rel_l1_and_true M hM t hBool

private theorem aciOr_l1_or_false_structural (t : Term) :
    RuleProofs.eo_has_bool_type t ->
    AciOrClause
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.or)
          (Term.Boolean false) t) ∧
      RuleProofs.eo_has_bool_type
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.or)
          (Term.Boolean false) t) := by
  intro hBool
  by_cases hFalse : t = Term.Boolean false
  · subst t
    exact ⟨by
      simpa [__eo_l_1___get_ai_norm_rec, __eo_ite, __eo_eq, native_ite,
        native_teq] using AciOrClause.false,
      by
        simpa [__eo_l_1___get_ai_norm_rec, __eo_ite, __eo_eq, native_ite,
          native_teq] using eo_has_bool_type_false_local⟩
  · have hNe : t ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type t hBool
    rw [aci_norm_l1_or_false_eq_of_ne_false t hNe hFalse]
    exact ⟨AciOrClause.cons t (Term.Boolean false) AciOrClause.false,
      eo_has_bool_type_or_of_bool_args_local t (Term.Boolean false) hBool
        eo_has_bool_type_false_local⟩

private theorem aciOr_l1_or_false_true_iff
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
    RuleProofs.eo_has_bool_type t ->
    (eo_interprets M
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.or)
          (Term.Boolean false) t) true ↔
      eo_interprets M t true) := by
  intro hBool
  by_cases hFalse : t = Term.Boolean false
  · subst t
    simp [__eo_l_1___get_ai_norm_rec, __eo_ite, __eo_eq, native_ite,
      native_teq]
  · have hNe : t ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type t hBool
    rw [aci_norm_l1_or_false_eq_of_ne_false t hNe hFalse]
    exact eo_interprets_or_false_iff M hM t hBool

private theorem aciOr_get_ai_norm_rec_structural :
    (t : Term) ->
    RuleProofs.eo_has_bool_type t ->
    AciOrClause (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t) ∧
      RuleProofs.eo_has_bool_type
        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t)
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x, hBool => by
      have hYBool : RuleProofs.eo_has_bool_type y :=
        eo_has_bool_type_or_left_local y x hBool
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_right_local y x hBool
      have hYStruct := aciOr_get_ai_norm_rec_structural y hYBool
      have hXStruct := aciOr_get_ai_norm_rec_structural x hXBool
      have hConcatClause :
          AciOrClause
            (__eo_list_concat (Term.UOp UserOp.or)
              (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
              (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)) :=
        aciOr_concat_preserves_clause hYStruct.1 hXStruct.1
      have hConcatBool :
          RuleProofs.eo_has_bool_type
            (__eo_list_concat (Term.UOp UserOp.or)
              (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
              (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)) :=
        aciOr_concat_preserves_bool_type hYStruct.1 hXStruct.1
          hYStruct.2 hXStruct.2
      have hSetClause :
          AciOrClause
            (__eo_list_setof (Term.UOp UserOp.or)
              (__eo_list_concat (Term.UOp UserOp.or)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))) :=
        aciOr_setof_preserves_clause hConcatClause hConcatBool
      have hSetBool :
          RuleProofs.eo_has_bool_type
            (__eo_list_setof (Term.UOp UserOp.or)
              (__eo_list_concat (Term.UOp UserOp.or)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))) :=
        aciOr_setof_preserves_bool_type hConcatClause hConcatBool
      simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
        using And.intro hSetClause hSetBool
  | t, hBool => by
      cases t
      case Apply f x =>
        cases f
        case Apply g y =>
          cases g
          case UOp op =>
            cases op
            case or =>
              have hYBool : RuleProofs.eo_has_bool_type y :=
                eo_has_bool_type_or_left_local y x hBool
              have hXBool : RuleProofs.eo_has_bool_type x :=
                eo_has_bool_type_or_right_local y x hBool
              have hYStruct := aciOr_get_ai_norm_rec_structural y hYBool
              have hXStruct := aciOr_get_ai_norm_rec_structural x hXBool
              have hConcatClause :
                  AciOrClause
                    (__eo_list_concat (Term.UOp UserOp.or)
                      (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                      (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)) :=
                aciOr_concat_preserves_clause hYStruct.1 hXStruct.1
              have hConcatBool :
                  RuleProofs.eo_has_bool_type
                    (__eo_list_concat (Term.UOp UserOp.or)
                      (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                      (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)) :=
                aciOr_concat_preserves_bool_type hYStruct.1 hXStruct.1
                  hYStruct.2 hXStruct.2
              have hSetClause :
                  AciOrClause
                    (__eo_list_setof (Term.UOp UserOp.or)
                      (__eo_list_concat (Term.UOp UserOp.or)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))) :=
                aciOr_setof_preserves_clause hConcatClause hConcatBool
              have hSetBool :
                  RuleProofs.eo_has_bool_type
                    (__eo_list_setof (Term.UOp UserOp.or)
                      (__eo_list_concat (Term.UOp UserOp.or)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))) :=
                aciOr_setof_preserves_bool_type hConcatClause hConcatBool
              simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
                using And.intro hSetClause hSetBool
            all_goals
              rw [get_ai_norm_rec_or_eq_l1_of_not_or _ hBool (by
                intro y' x' hEq
                cases hEq)]
              exact aciOr_l1_or_false_structural _ hBool
          all_goals
            rw [get_ai_norm_rec_or_eq_l1_of_not_or _ hBool (by
              intro y' x' hEq
              cases hEq)]
            exact aciOr_l1_or_false_structural _ hBool
        all_goals
          rw [get_ai_norm_rec_or_eq_l1_of_not_or _ hBool (by
            intro y x hEq
            cases hEq)]
          exact aciOr_l1_or_false_structural _ hBool
      all_goals
        rw [get_ai_norm_rec_or_eq_l1_of_not_or _ hBool (by
          intro y x hEq
          cases hEq)]
        exact aciOr_l1_or_false_structural _ hBool

private theorem aciOr_get_ai_norm_rec_true_iff
    (M : SmtModel) (hM : model_total_typed M) :
    (t : Term) ->
    (hBool : RuleProofs.eo_has_bool_type t) ->
    (eo_interprets M
        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t) true ↔
      eo_interprets M t true)
  | Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x, hBool => by
      have hYBool : RuleProofs.eo_has_bool_type y :=
        eo_has_bool_type_or_left_local y x hBool
      have hXBool : RuleProofs.eo_has_bool_type x :=
        eo_has_bool_type_or_right_local y x hBool
      have hYStruct := aciOr_get_ai_norm_rec_structural y hYBool
      have hXStruct := aciOr_get_ai_norm_rec_structural x hXBool
      have hConcatClause :
          AciOrClause
            (__eo_list_concat (Term.UOp UserOp.or)
              (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
              (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)) :=
        aciOr_concat_preserves_clause hYStruct.1 hXStruct.1
      have hConcatBool :
          RuleProofs.eo_has_bool_type
            (__eo_list_concat (Term.UOp UserOp.or)
              (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
              (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)) :=
        aciOr_concat_preserves_bool_type hYStruct.1 hXStruct.1
          hYStruct.2 hXStruct.2
      have hYIff := aciOr_get_ai_norm_rec_true_iff M hM y hYBool
      have hXIff := aciOr_get_ai_norm_rec_true_iff M hM x hXBool
      have hConcatIff :=
        aciOr_concat_true_iff M hM hYStruct.1 hXStruct.1 hYStruct.2 hXStruct.2
      have hSetForward :
          eo_interprets M
              (__eo_list_setof (Term.UOp UserOp.or)
                (__eo_list_concat (Term.UOp UserOp.or)
                  (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                  (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)))
              true ->
            eo_interprets M
              (__eo_list_concat (Term.UOp UserOp.or)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))
              true :=
        aciOr_setof_true_implies_original_true M hM hConcatClause hConcatBool
      have hSetBackward :
          eo_interprets M
              (__eo_list_concat (Term.UOp UserOp.or)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))
              true ->
            eo_interprets M
              (__eo_list_setof (Term.UOp UserOp.or)
                (__eo_list_concat (Term.UOp UserOp.or)
                  (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                  (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)))
              true :=
        aciOr_setof_true M hM hConcatClause hConcatBool
      constructor
      · intro hNormTrue
        have hSetTrue :
            eo_interprets M
              (__eo_list_setof (Term.UOp UserOp.or)
                (__eo_list_concat (Term.UOp UserOp.or)
                  (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                  (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)))
              true := by
          simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
            using hNormTrue
        have hConcatTrue := hSetForward hSetTrue
        rcases hConcatIff.mp hConcatTrue with hYNormTrue | hXNormTrue
        · exact eo_interprets_or_left_intro_local M hM y x
            (hYIff.mp hYNormTrue) hXBool
        · exact eo_interprets_or_right_intro_local M hM y x
            hYBool (hXIff.mp hXNormTrue)
      · intro hOrTrue
        have hConcatTrue :
            eo_interprets M
              (__eo_list_concat (Term.UOp UserOp.or)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))
              true := by
          rcases eo_interprets_bool_cases_local M hM y hYBool with hYTrue | hYFalse
          · exact hConcatIff.mpr (Or.inl (hYIff.mpr hYTrue))
          · have hXTrue : eo_interprets M x true :=
              eo_interprets_or_right_of_left_false_local M hM y x hYFalse hOrTrue
            exact hConcatIff.mpr (Or.inr (hXIff.mpr hXTrue))
        have hSetTrue := hSetBackward hConcatTrue
        simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
          using hSetTrue
  | t, hBool => by
      cases t
      case Apply f x =>
        cases f
        case Apply g y =>
          cases g
          case UOp op =>
            cases op
            case or =>
              have hYBool : RuleProofs.eo_has_bool_type y :=
                eo_has_bool_type_or_left_local y x hBool
              have hXBool : RuleProofs.eo_has_bool_type x :=
                eo_has_bool_type_or_right_local y x hBool
              have hYStruct := aciOr_get_ai_norm_rec_structural y hYBool
              have hXStruct := aciOr_get_ai_norm_rec_structural x hXBool
              have hConcatClause :
                  AciOrClause
                    (__eo_list_concat (Term.UOp UserOp.or)
                      (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                      (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)) :=
                aciOr_concat_preserves_clause hYStruct.1 hXStruct.1
              have hConcatBool :
                  RuleProofs.eo_has_bool_type
                    (__eo_list_concat (Term.UOp UserOp.or)
                      (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                      (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)) :=
                aciOr_concat_preserves_bool_type hYStruct.1 hXStruct.1
                  hYStruct.2 hXStruct.2
              have hYIff := aciOr_get_ai_norm_rec_true_iff M hM y hYBool
              have hXIff := aciOr_get_ai_norm_rec_true_iff M hM x hXBool
              have hConcatIff :=
                aciOr_concat_true_iff M hM hYStruct.1 hXStruct.1
                  hYStruct.2 hXStruct.2
              have hSetForward :
                  eo_interprets M
                      (__eo_list_setof (Term.UOp UserOp.or)
                        (__eo_list_concat (Term.UOp UserOp.or)
                          (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                          (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)))
                      true ->
                    eo_interprets M
                      (__eo_list_concat (Term.UOp UserOp.or)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))
                      true :=
                aciOr_setof_true_implies_original_true M hM hConcatClause hConcatBool
              have hSetBackward :
                  eo_interprets M
                      (__eo_list_concat (Term.UOp UserOp.or)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))
                      true ->
                    eo_interprets M
                      (__eo_list_setof (Term.UOp UserOp.or)
                        (__eo_list_concat (Term.UOp UserOp.or)
                          (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                          (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)))
                      true :=
                aciOr_setof_true M hM hConcatClause hConcatBool
              constructor
              · intro hNormTrue
                have hSetTrue :
                    eo_interprets M
                      (__eo_list_setof (Term.UOp UserOp.or)
                        (__eo_list_concat (Term.UOp UserOp.or)
                          (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                          (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x)))
                      true := by
                  simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
                    using hNormTrue
                have hConcatTrue := hSetForward hSetTrue
                rcases hConcatIff.mp hConcatTrue with hYNormTrue | hXNormTrue
                · exact eo_interprets_or_left_intro_local M hM y x
                    (hYIff.mp hYNormTrue) hXBool
                · exact eo_interprets_or_right_intro_local M hM y x
                    hYBool (hXIff.mp hXNormTrue)
              · intro hOrTrue
                have hConcatTrue :
                    eo_interprets M
                      (__eo_list_concat (Term.UOp UserOp.or)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) y)
                        (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) x))
                      true := by
                  rcases eo_interprets_bool_cases_local M hM y hYBool with hYTrue | hYFalse
                  · exact hConcatIff.mpr (Or.inl (hYIff.mpr hYTrue))
                  · have hXTrue : eo_interprets M x true :=
                      eo_interprets_or_right_of_left_false_local M hM y x hYFalse
                        hOrTrue
                    exact hConcatIff.mpr (Or.inr (hXIff.mpr hXTrue))
                have hSetTrue := hSetBackward hConcatTrue
                simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
                  using hSetTrue
            all_goals
              rw [get_ai_norm_rec_or_eq_l1_of_not_or _ hBool (by
                intro y' x' hEq
                cases hEq)]
              exact aciOr_l1_or_false_true_iff M hM _ hBool
          all_goals
            rw [get_ai_norm_rec_or_eq_l1_of_not_or _ hBool (by
              intro y' x' hEq
              cases hEq)]
            exact aciOr_l1_or_false_true_iff M hM _ hBool
        all_goals
          rw [get_ai_norm_rec_or_eq_l1_of_not_or _ hBool (by
            intro y x hEq
            cases hEq)]
          exact aciOr_l1_or_false_true_iff M hM _ hBool
      all_goals
        rw [get_ai_norm_rec_or_eq_l1_of_not_or _ hBool (by
          intro y x hEq
          cases hEq)]
        exact aciOr_l1_or_false_true_iff M hM _ hBool

private theorem smt_value_rel_get_ai_norm_or
    (M : SmtModel) (hM : model_total_typed M) (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x)))
      (__smtx_model_eval M
        (__eo_to_smt
          (__get_ai_norm (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x)))) := by
  intro hTrans
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x
  have hTypeof : __eo_typeof t = Term.Bool :=
    eo_typeof_or_eq_bool_of_has_smt_translation y x hTrans
  have hBool : RuleProofs.eo_has_bool_type t :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type t hTrans hTypeof
  have hRecStruct :
      AciOrClause (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t) ∧
        RuleProofs.eo_has_bool_type
          (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t) :=
    aciOr_get_ai_norm_rec_structural t hBool
  have hNormBool :
      RuleProofs.eo_has_bool_type (__get_ai_norm t) := by
    change RuleProofs.eo_has_bool_type
      (__eo_list_singleton_elim (Term.UOp UserOp.or)
        (__get_ai_norm_rec (Term.UOp UserOp.or) (__eo_nil (Term.UOp UserOp.or)
          (__eo_typeof t)) t))
    rw [hTypeof]
    simpa [__eo_nil] using
      aciOr_singleton_elim_preserves_bool_type hRecStruct.1 hRecStruct.2
  apply smt_value_rel_of_bool_interprets_iff M hM
  · exact hBool
  · exact hNormBool
  · have hSingletonIff :
        (eo_interprets M
            (__eo_list_singleton_elim (Term.UOp UserOp.or)
              (__get_ai_norm_rec (Term.UOp UserOp.or) (Term.Boolean false) t))
            true ↔
          eo_interprets M t true) :=
      (aciOr_singleton_elim_true_iff M hM hRecStruct.1 hRecStruct.2).trans
        (aciOr_get_ai_norm_rec_true_iff M hM t hBool)
    change
      (eo_interprets M t true ↔
        eo_interprets M
          (__eo_list_singleton_elim (Term.UOp UserOp.or)
            (__get_ai_norm_rec (Term.UOp UserOp.or) (__eo_nil (Term.UOp UserOp.or)
              (__eo_typeof t)) t)) true)
    rw [hTypeof]
    simpa [__eo_nil] using hSingletonIff.symm

private theorem aciAnd_l1_and_true_structural (t : Term) :
    RuleProofs.eo_has_bool_type t ->
    AciAndClause
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.and)
          (Term.Boolean true) t) ∧
      RuleProofs.eo_has_bool_type
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.and)
          (Term.Boolean true) t) := by
  intro hBool
  by_cases hTrue : t = Term.Boolean true
  · subst t
    exact ⟨by
      simpa [__eo_l_1___get_ai_norm_rec, __eo_ite, __eo_eq, native_ite,
        native_teq] using AciAndClause.true,
      by
        simpa [__eo_l_1___get_ai_norm_rec, __eo_ite, __eo_eq, native_ite,
          native_teq] using RuleProofs.eo_has_bool_type_true⟩
  · have hNe : t ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type t hBool
    rw [aci_norm_l1_and_true_eq_of_ne_true t hNe hTrue]
    exact ⟨AciAndClause.cons t (Term.Boolean true) AciAndClause.true,
      RuleProofs.eo_has_bool_type_and_of_bool_args t (Term.Boolean true) hBool
        RuleProofs.eo_has_bool_type_true⟩

private theorem aciAnd_l1_and_true_true_iff
    (M : SmtModel) (t : Term) :
    RuleProofs.eo_has_bool_type t ->
    (eo_interprets M
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.and)
          (Term.Boolean true) t) true ↔
      eo_interprets M t true) := by
  intro hBool
  by_cases hTrue : t = Term.Boolean true
  · subst t
    simp [__eo_l_1___get_ai_norm_rec, __eo_ite, __eo_eq, native_ite,
      native_teq]
  · have hNe : t ≠ Term.Stuck := RuleProofs.term_ne_stuck_of_has_bool_type t hBool
    rw [aci_norm_l1_and_true_eq_of_ne_true t hNe hTrue]
    exact eo_interprets_and_true_iff M t hBool

private theorem aciAnd_get_ai_norm_rec_structural :
    (t : Term) ->
    RuleProofs.eo_has_bool_type t ->
    AciAndClause (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t) ∧
      RuleProofs.eo_has_bool_type
        (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t)
  | t, hBool => by
      cases t
      case Apply f x =>
        cases f
        case Apply g y =>
          cases g
          case UOp op =>
            cases op
            case and =>
              have hYBool : RuleProofs.eo_has_bool_type y :=
                RuleProofs.eo_has_bool_type_and_left y x hBool
              have hXBool : RuleProofs.eo_has_bool_type x :=
                RuleProofs.eo_has_bool_type_and_right y x hBool
              have hYStruct := aciAnd_get_ai_norm_rec_structural y hYBool
              have hXStruct := aciAnd_get_ai_norm_rec_structural x hXBool
              have hConcatClause :
                  AciAndClause
                    (__eo_list_concat (Term.UOp UserOp.and)
                      (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) y)
                      (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) x)) :=
                aciAnd_concat_preserves_clause hYStruct.1 hXStruct.1
              have hConcatBool :
                  RuleProofs.eo_has_bool_type
                    (__eo_list_concat (Term.UOp UserOp.and)
                      (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) y)
                      (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) x)) :=
                aciAnd_concat_preserves_bool_type hYStruct.1 hXStruct.1
                  hYStruct.2 hXStruct.2
              have hSetClause :
                  AciAndClause
                    (__eo_list_setof (Term.UOp UserOp.and)
                      (__eo_list_concat (Term.UOp UserOp.and)
                        (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) y)
                        (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) x))) :=
                aciAnd_setof_preserves_clause hConcatClause hConcatBool
              have hSetBool :
                  RuleProofs.eo_has_bool_type
                    (__eo_list_setof (Term.UOp UserOp.and)
                      (__eo_list_concat (Term.UOp UserOp.and)
                        (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) y)
                        (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) x))) :=
                aciAnd_setof_preserves_bool_type hConcatClause hConcatBool
              simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
                using And.intro hSetClause hSetBool
            all_goals
              rw [get_ai_norm_rec_and_eq_l1_of_not_and _ hBool (by
                intro y' x' hEq
                cases hEq)]
              exact aciAnd_l1_and_true_structural _ hBool
          all_goals
            rw [get_ai_norm_rec_and_eq_l1_of_not_and _ hBool (by
              intro y' x' hEq
              cases hEq)]
            exact aciAnd_l1_and_true_structural _ hBool
        all_goals
          rw [get_ai_norm_rec_and_eq_l1_of_not_and _ hBool (by
            intro y x hEq
            cases hEq)]
          exact aciAnd_l1_and_true_structural _ hBool
      all_goals
        rw [get_ai_norm_rec_and_eq_l1_of_not_and _ hBool (by
          intro y x hEq
          cases hEq)]
        exact aciAnd_l1_and_true_structural _ hBool

private theorem aciAnd_get_ai_norm_rec_true_iff
    (M : SmtModel) :
    (t : Term) ->
    (hBool : RuleProofs.eo_has_bool_type t) ->
    (eo_interprets M
        (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t) true ↔
      eo_interprets M t true)
  | t, hBool => by
      cases t
      case Apply f x =>
        cases f
        case Apply g y =>
          cases g
          case UOp op =>
            cases op
            case and =>
              have hYBool : RuleProofs.eo_has_bool_type y :=
                RuleProofs.eo_has_bool_type_and_left y x hBool
              have hXBool : RuleProofs.eo_has_bool_type x :=
                RuleProofs.eo_has_bool_type_and_right y x hBool
              have hYStruct := aciAnd_get_ai_norm_rec_structural y hYBool
              have hXStruct := aciAnd_get_ai_norm_rec_structural x hXBool
              have hYIff := aciAnd_get_ai_norm_rec_true_iff M y hYBool
              have hXIff := aciAnd_get_ai_norm_rec_true_iff M x hXBool
              have hConcatIff :=
                aciAnd_concat_true_iff M hYStruct.1 hXStruct.1
                  hYStruct.2 hXStruct.2
              have hConcatClause :
                  AciAndClause
                    (__eo_list_concat (Term.UOp UserOp.and)
                      (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) y)
                      (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) x)) :=
                aciAnd_concat_preserves_clause hYStruct.1 hXStruct.1
              have hConcatBool :
                  RuleProofs.eo_has_bool_type
                    (__eo_list_concat (Term.UOp UserOp.and)
                      (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) y)
                      (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) x)) :=
                aciAnd_concat_preserves_bool_type hYStruct.1 hXStruct.1
                  hYStruct.2 hXStruct.2
              have hSetIff :=
                aciAnd_setof_true_iff M hConcatClause hConcatBool
              constructor
              · intro hNormTrue
                have hSetTrue :
                    eo_interprets M
                      (__eo_list_setof (Term.UOp UserOp.and)
                        (__eo_list_concat (Term.UOp UserOp.and)
                          (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) y)
                          (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) x)))
                      true := by
                  simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
                    using hNormTrue
                have hConcatTrue := hSetIff.mp hSetTrue
                have hParts := hConcatIff.mp hConcatTrue
                exact RuleProofs.eo_interprets_and_intro M y x
                  (hYIff.mp hParts.1) (hXIff.mp hParts.2)
              · intro hAndTrue
                have hYTrue : eo_interprets M y true :=
                  RuleProofs.eo_interprets_and_left M y x hAndTrue
                have hXTrue : eo_interprets M x true :=
                  RuleProofs.eo_interprets_and_right M y x hAndTrue
                have hConcatTrue :=
                  hConcatIff.mpr ⟨hYIff.mpr hYTrue, hXIff.mpr hXTrue⟩
                have hSetTrue := hSetIff.mpr hConcatTrue
                simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite, native_teq]
                  using hSetTrue
            all_goals
              rw [get_ai_norm_rec_and_eq_l1_of_not_and _ hBool (by
                intro y' x' hEq
                cases hEq)]
              exact aciAnd_l1_and_true_true_iff M _ hBool
          all_goals
            rw [get_ai_norm_rec_and_eq_l1_of_not_and _ hBool (by
              intro y' x' hEq
              cases hEq)]
            exact aciAnd_l1_and_true_true_iff M _ hBool
        all_goals
          rw [get_ai_norm_rec_and_eq_l1_of_not_and _ hBool (by
            intro y x hEq
            cases hEq)]
          exact aciAnd_l1_and_true_true_iff M _ hBool
      all_goals
        rw [get_ai_norm_rec_and_eq_l1_of_not_and _ hBool (by
          intro y x hEq
          cases hEq)]
        exact aciAnd_l1_and_true_true_iff M _ hBool

private theorem smt_value_rel_get_ai_norm_and
    (M : SmtModel) (hM : model_total_typed M) (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x)))
      (__smtx_model_eval M
        (__eo_to_smt
          (__get_ai_norm (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x)))) := by
  intro hTrans
  let t := Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x
  have hTypeof : __eo_typeof t = Term.Bool :=
    eo_typeof_and_eq_bool_of_has_smt_translation y x hTrans
  have hBool : RuleProofs.eo_has_bool_type t :=
    RuleProofs.eo_typeof_bool_implies_has_bool_type t hTrans hTypeof
  have hRecStruct :
      AciAndClause (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t) ∧
        RuleProofs.eo_has_bool_type
          (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t) :=
    aciAnd_get_ai_norm_rec_structural t hBool
  have hNormBool :
      RuleProofs.eo_has_bool_type (__get_ai_norm t) := by
    change RuleProofs.eo_has_bool_type
      (__eo_list_singleton_elim (Term.UOp UserOp.and)
        (__get_ai_norm_rec (Term.UOp UserOp.and) (__eo_nil (Term.UOp UserOp.and)
          (__eo_typeof t)) t))
    rw [hTypeof]
    simpa [__eo_nil] using
      aciAnd_singleton_elim_preserves_bool_type hRecStruct.1 hRecStruct.2
  apply smt_value_rel_of_bool_interprets_iff M hM
  · exact hBool
  · exact hNormBool
  · have hSingletonIff :
        (eo_interprets M
            (__eo_list_singleton_elim (Term.UOp UserOp.and)
              (__get_ai_norm_rec (Term.UOp UserOp.and) (Term.Boolean true) t))
            true ↔
          eo_interprets M t true) :=
      (aciAnd_singleton_elim_true_iff M hRecStruct.1 hRecStruct.2).trans
        (aciAnd_get_ai_norm_rec_true_iff M t hBool)
    change
      (eo_interprets M t true ↔
        eo_interprets M
          (__eo_list_singleton_elim (Term.UOp UserOp.and)
            (__get_ai_norm_rec (Term.UOp UserOp.and) (__eo_nil (Term.UOp UserOp.and)
              (__eo_typeof t)) t)) true)
    rw [hTypeof]
    simpa [__eo_nil] using hSingletonIff.symm

private abbrev mkStrConcat (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.str_concat) x) y

private abbrev mkBvConcat (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y

private abbrev mkBvAnd (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) y

private abbrev mkBvOr (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvor) x) y

private abbrev mkBvXor (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) x) y

private def BvEvalCanonical (M : SmtModel) (t : Term) : Prop :=
  ∃ w n,
    __smtx_model_eval M (__eo_to_smt t) = SmtValue.Binary w n ∧
      native_zleq 0 w = true ∧
      native_zeq n (native_mod_total n (native_int_pow2 w)) = true

private def BvConcatListCanonical (M : SmtModel) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) xs =>
      BvEvalCanonical M x ∧ BvConcatListCanonical M xs
  | t => BvEvalCanonical M t

private theorem term_ne_stuck_of_smt_seq_type {t : Term} {T : SmtType} :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    t ≠ Term.Stuck := by
  intro hTy hStuck
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.Seq T at hTy
  rw [TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

private theorem term_ne_stuck_of_smt_bitvec_type {t : Term} {w : native_Nat} :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    t ≠ Term.Stuck := by
  intro hTy hStuck
  subst t
  change __smtx_typeof SmtTerm.None = SmtType.BitVec w at hTy
  rw [TranslationProofs.smtx_typeof_none] at hTy
  cases hTy

private theorem strConcat_nil_is_list_nil_of_type {ty : Term} {T : SmtType}
    (hTy : __eo_to_smt_type ty = SmtType.Seq T) :
    __eo_is_list_nil (Term.UOp UserOp.str_concat)
        (__eo_nil (Term.UOp UserOp.str_concat) ty) =
      Term.Boolean true := by
  rcases TranslationProofs.eo_to_smt_type_eq_seq hTy with ⟨V, hTyEq, _hV⟩
  subst ty
  cases V <;>
    simp [__eo_nil, __eo_nil_str_concat, __seq_empty, __eo_is_list_nil,
      __eo_is_list_nil_str_concat, __eo_eq, native_teq]
  case UOp op =>
    cases op <;>
      simp [__eo_nil, __eo_nil_str_concat, __seq_empty, __eo_is_list_nil,
        __eo_is_list_nil_str_concat, __eo_eq, native_teq]

private theorem strConcat_nil_eq_seq_empty_of_type {ty : Term} {T : SmtType}
    (hTy : __eo_to_smt_type ty = SmtType.Seq T) :
    __eo_nil (Term.UOp UserOp.str_concat) ty = __seq_empty ty := by
  rcases TranslationProofs.eo_to_smt_type_eq_seq hTy with ⟨V, hTyEq, _hV⟩
  subst ty
  rfl

private theorem strConcat_l1_eq_self_of_eq (id : Term) :
    id ≠ Term.Stuck ->
    __eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id id = id := by
  intro hId
  have hEq : __eo_eq id id = Term.Boolean true :=
    eo_eq_eq_true_of_eq_local rfl hId hId
  simp [__eo_l_1___get_a_norm_rec, hEq, __eo_ite, native_ite, native_teq]

private theorem strConcat_l1_eq_concat_of_ne_id (id t : Term) :
    id ≠ Term.Stuck ->
    t ≠ Term.Stuck ->
    t ≠ id ->
    __eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t =
      mkStrConcat t id := by
  intro hId hT hNe
  have hEq : __eo_eq id t = Term.Boolean false :=
    eo_eq_eq_false_of_ne_local
      (x := id) (y := t) (by
        intro h
        exact hNe h.symm) hId hT
  rw [show __eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t =
      __eo_ite (__eo_eq id t) id
        (__eo_l_2___get_a_norm_rec (Term.UOp UserOp.str_concat) id t) by
    cases id <;> cases t <;>
      simp [__eo_l_1___get_a_norm_rec] at hId hT ⊢]
  rw [hEq]
  cases id <;> cases t <;>
    simp [__eo_l_2___get_a_norm_rec, __eo_ite, native_ite, native_teq] at hId hT ⊢ <;>
    contradiction

private theorem strConcat_l1_rel_struct
    (M : SmtModel) (hM : model_total_typed M) (id : Term) (T : SmtType)
    (hIdNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) id = Term.Boolean true)
    (hIdList :
      __eo_is_list (Term.UOp UserOp.str_concat) id = Term.Boolean true)
    (hIdTy : __smtx_typeof (__eo_to_smt id) = SmtType.Seq T)
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t) =
        Term.Boolean true ∧
      __smtx_typeof
          (__eo_to_smt
            (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t)) =
        SmtType.Seq T ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t)))
        (__smtx_model_eval M (__eo_to_smt t)) := by
  intro hTy
  have hIdNe : id ≠ Term.Stuck := term_ne_stuck_of_smt_seq_type hIdTy
  have hTNe : t ≠ Term.Stuck := term_ne_stuck_of_smt_seq_type hTy
  by_cases hEq : t = id
  · subst t
    rw [strConcat_l1_eq_self_of_eq id hIdNe]
    exact ⟨hIdList, hIdTy, RuleProofs.smt_value_rel_refl _⟩
  · rw [strConcat_l1_eq_concat_of_ne_id id t hIdNe hTNe hEq]
    exact ⟨
      strConcat_is_list_cons_true_of_tail_list t id hIdList,
      strConcat_typeof_concat_of_seq t id T hTy hIdTy,
      strConcat_smt_value_rel_list_nil_right_empty M hM t id T
        hTy hIdNil hIdTy⟩

private theorem strConcat_l1_rel_eval_empty
    (M : SmtModel) (hM : model_total_typed M) (id : Term) (T : SmtType)
    (hIdList :
      __eo_is_list (Term.UOp UserOp.str_concat) id = Term.Boolean true)
    (hIdEval :
      __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Seq (SmtSeq.empty T))
    (hIdNe : id ≠ Term.Stuck)
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t) =
        Term.Boolean true ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t)))
        (__smtx_model_eval M (__eo_to_smt t)) := by
  intro hTy
  have hTNe : t ≠ Term.Stuck := term_ne_stuck_of_smt_seq_type hTy
  by_cases hEq : t = id
  · subst t
    rw [strConcat_l1_eq_self_of_eq id hIdNe]
    exact ⟨hIdList, RuleProofs.smt_value_rel_refl _⟩
  · rw [strConcat_l1_eq_concat_of_ne_id id t hIdNe hTNe hEq]
    exact ⟨
      strConcat_is_list_cons_true_of_tail_list t id hIdList,
      strConcat_smt_value_rel_right_eval_empty M hM t id T hTy hIdEval⟩

private theorem strConcat_singleton_elim_rel
    (M : SmtModel) (hM : model_total_typed M) (c : Term) (T : SmtType) :
    __eo_is_list (Term.UOp UserOp.str_concat) c = Term.Boolean true ->
    __smtx_typeof (__eo_to_smt c) = SmtType.Seq T ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.str_concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hcTy
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.str_concat :=
            strConcat_is_list_cons_head_eq_of_true g head tail hList
          subst g
          have hTailList :
              __eo_is_list (Term.UOp UserOp.str_concat) tail =
                Term.Boolean true :=
            strConcat_is_list_tail_true_of_cons_self head tail hList
          have hTypes := strConcat_args_of_seq_type head tail T hcTy
          cases hNil : __eo_is_list_nil (Term.UOp UserOp.str_concat) tail
          all_goals
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
              native_teq]
          case Boolean b =>
            cases b
            · exact RuleProofs.smt_value_rel_refl
                (__smtx_model_eval M (__eo_to_smt (mkStrConcat head tail)))
            · exact RuleProofs.smt_value_rel_symm
                (__smtx_model_eval M (__eo_to_smt (mkStrConcat head tail)))
                (__smtx_model_eval M (__eo_to_smt head))
                (strConcat_smt_value_rel_list_nil_right_empty M hM
                  head tail T hTypes.1 hNil hTypes.2)
          all_goals
            have hTailNe : tail ≠ Term.Stuck :=
              term_ne_stuck_of_smt_seq_type hTypes.2
            cases tail <;>
              simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
                __eo_eq, native_teq] at hNil hTailNe
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

private theorem smt_seq_ne_none (T : SmtType) : SmtType.Seq T ≠ SmtType.None := by
  intro h
  cases h

private theorem smt_bitvec_ne_none (w : native_Nat) :
    SmtType.BitVec w ≠ SmtType.None := by
  intro h
  cases h

private theorem smt_reglan_ne_none : SmtType.RegLan ≠ SmtType.None := by
  intro h
  cases h

private theorem strConcat_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation (mkStrConcat y x) ->
    ∃ T : SmtType,
      __smtx_typeof (__eo_to_smt y) = SmtType.Seq T ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.Seq T := by
  intro hTrans
  let s := SmtTerm.str_concat (__eo_to_smt y) (__eo_to_smt x)
  have hNN : term_has_non_none_type s := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa [s, mkStrConcat] using hTrans
  exact seq_binop_args_of_non_none (op := SmtTerm.str_concat)
    (typeof_str_concat_eq (__eo_to_smt y) (__eo_to_smt x)) hNN

private theorem bvand_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvand) y) x) ->
    ∃ w : native_Nat,
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTrans
  let s := SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)
  have hNN : term_has_non_none_type s := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa [s] using hTrans
  exact bv_binop_args_of_non_none (op := SmtTerm.bvand)
    (show
      __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_38]) hNN

private theorem bvAnd_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (mkBvAnd y x)) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    simpa [mkBvAnd] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvand)
      (show
        __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_38]) hNN with
    ⟨w', hyTy, hxTy⟩
  have hWidth : w' = w := by
    have hResult :
        SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show
          __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) by
          rw [__smtx_typeof.eq_38]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hyTy, hxTy, native_ite, native_nateq,
        SmtEval.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hyTy, hxTy⟩

private theorem bvor_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvor) y) x) ->
    ∃ w : native_Nat,
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTrans
  let s := SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)
  have hNN : term_has_non_none_type s := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa [s] using hTrans
  exact bv_binop_args_of_non_none (op := SmtTerm.bvor)
    (show
      __smtx_typeof (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt x)) by
      rw [__smtx_typeof.eq_39]) hNN

private theorem bvOr_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (mkBvOr y x)) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    simpa [mkBvOr] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvor)
      (show
        __smtx_typeof (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_39]) hNN with
    ⟨w', hyTy, hxTy⟩
  have hWidth : w' = w := by
    have hResult :
        SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show
          __smtx_typeof (SmtTerm.bvor (__eo_to_smt y) (__eo_to_smt x)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) by
          rw [__smtx_typeof.eq_39]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hyTy, hxTy, native_ite, native_nateq,
        SmtEval.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hyTy, hxTy⟩

private theorem bvxor_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.bvxor) y) x) ->
    ∃ w : native_Nat,
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTrans
  let s := SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)
  have hNN : term_has_non_none_type s := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa [s] using hTrans
  exact bv_binop_args_of_non_none (op := SmtTerm.bvxor)
    (show
      __smtx_typeof (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)) =
        __smtx_typeof_bv_op_2
          (__smtx_typeof (__eo_to_smt y))
          (__smtx_typeof (__eo_to_smt x)) by
      rw [__smtx_typeof.eq_42]) hNN

private theorem bvXor_args_of_bitvec_type (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (mkBvXor y x)) = SmtType.BitVec w ->
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec w ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w := by
  intro hTy
  have hTy' :
      __smtx_typeof (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w := by
    simpa [mkBvXor] using hTy
  have hNN :
      term_has_non_none_type
        (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    rw [hTy']
    intro h
    cases h
  rcases bv_binop_args_of_non_none (op := SmtTerm.bvxor)
      (show
        __smtx_typeof (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)) =
          __smtx_typeof_bv_op_2
            (__smtx_typeof (__eo_to_smt y))
            (__smtx_typeof (__eo_to_smt x)) by
        rw [__smtx_typeof.eq_42]) hNN with
    ⟨w', hyTy, hxTy⟩
  have hWidth : w' = w := by
    have hResult :
        SmtType.BitVec w' = SmtType.BitVec w := by
      rw [show
          __smtx_typeof (SmtTerm.bvxor (__eo_to_smt y) (__eo_to_smt x)) =
            __smtx_typeof_bv_op_2
              (__smtx_typeof (__eo_to_smt y))
              (__smtx_typeof (__eo_to_smt x)) by
          rw [__smtx_typeof.eq_42]] at hTy'
      simpa [__smtx_typeof_bv_op_2, hyTy, hxTy, native_ite, native_nateq,
        SmtEval.native_nateq] using hTy'
    cases hResult
    rfl
  subst w'
  exact ⟨hyTy, hxTy⟩

private theorem bvConcat_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.concat) y) x) ->
    ∃ wy wx : native_Nat,
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx := by
  intro hTrans
  let s := SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)
  have hNN : term_has_non_none_type s := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa [s] using hTrans
  exact bv_concat_args_of_non_none hNN

private theorem reConcat_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_concat) y) x) ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan := by
  intro hTrans
  have hNN : term_has_non_none_type
      (SmtTerm.re_concat (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa using hTrans
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_concat)
    (typeof_re_concat_eq (__eo_to_smt y) (__eo_to_smt x)) hNN

private theorem reInter_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_inter) y) x) ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan := by
  intro hTrans
  have hNN : term_has_non_none_type
      (SmtTerm.re_inter (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa using hTrans
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_inter)
    (typeof_re_inter_eq (__eo_to_smt y) (__eo_to_smt x)) hNN

private theorem reUnion_args_of_has_smt_translation (y x : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.re_union) y) x) ->
    __smtx_typeof (__eo_to_smt y) = SmtType.RegLan ∧
      __smtx_typeof (__eo_to_smt x) = SmtType.RegLan := by
  intro hTrans
  have hNN : term_has_non_none_type
      (SmtTerm.re_union (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    unfold RuleProofs.eo_has_smt_translation at hTrans
    simpa using hTrans
  exact reglan_binop_args_of_non_none (op := SmtTerm.re_union)
    (typeof_re_union_eq (__eo_to_smt y) (__eo_to_smt x)) hNN

private theorem smt_eval_seq_of_smt_type_seq
    (M : SmtModel) (hM : model_total_typed M) (t : SmtTerm) (T : SmtType) :
    __smtx_typeof t = SmtType.Seq T ->
    ∃ s, __smtx_model_eval M t = SmtValue.Seq s := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact smt_seq_ne_none T
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.Seq T := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact seq_value_canonical hValTy

private theorem smt_eval_binary_of_smt_type_bitvec
    (M : SmtModel) (hM : model_total_typed M) (t : SmtTerm)
    (w : native_Nat) :
    __smtx_typeof t = SmtType.BitVec w ->
    ∃ n, __smtx_model_eval M t =
      SmtValue.Binary (native_nat_to_int w) n := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact smt_bitvec_ne_none w
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.BitVec w := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact bitvec_value_canonical hValTy

private theorem smt_eval_reglan_of_smt_type_reglan
    (M : SmtModel) (hM : model_total_typed M) (t : SmtTerm) :
    __smtx_typeof t = SmtType.RegLan ->
    ∃ r, __smtx_model_eval M t = SmtValue.RegLan r := by
  intro hTy
  have hNN : term_has_non_none_type t := by
    unfold term_has_non_none_type
    rw [hTy]
    exact smt_reglan_ne_none
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M t) = SmtType.RegLan := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM t hNN
  exact reglan_value_canonical hValTy

private theorem smt_value_rel_eval_seq_left
    {v w : SmtValue} :
    RuleProofs.smt_value_rel v w ->
    (∃ s, w = SmtValue.Seq s) ->
    ∃ s, v = SmtValue.Seq s := by
  intro hRel hSeq
  rcases hSeq with ⟨s, rfl⟩
  cases v <;>
    simp [RuleProofs.smt_value_rel, RuleProofs.smt_seq_rel,
      __smtx_model_eval_eq, native_veq] at hRel ⊢

private theorem smt_value_rel_eval_seq_right
    {v w : SmtValue} :
    RuleProofs.smt_value_rel v w ->
    (∃ s, v = SmtValue.Seq s) ->
    ∃ s, w = SmtValue.Seq s := by
  intro hRel hSeq
  exact smt_value_rel_eval_seq_left
    (RuleProofs.smt_value_rel_symm v w hRel) hSeq

private theorem smt_value_rel_eval_binary_left
    {v w : SmtValue} {bw : native_Int} :
    RuleProofs.smt_value_rel v w ->
    (∃ n, w = SmtValue.Binary bw n) ->
    ∃ n, v = SmtValue.Binary bw n := by
  intro hRel hBin
  rcases hBin with ⟨n, rfl⟩
  cases v <;>
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq,
      native_and, native_zeq] at hRel ⊢
  case Binary w' n' =>
    exact hRel.1

private theorem smt_value_rel_eval_binary_right
    {v w : SmtValue} {bw : native_Int} :
    RuleProofs.smt_value_rel v w ->
    (∃ n, v = SmtValue.Binary bw n) ->
    ∃ n, w = SmtValue.Binary bw n := by
  intro hRel hBin
  exact smt_value_rel_eval_binary_left
    (RuleProofs.smt_value_rel_symm v w hRel) hBin

private theorem smt_value_rel_eval_reglan_left
    {v w : SmtValue} :
    RuleProofs.smt_value_rel v w ->
    (∃ r, w = SmtValue.RegLan r) ->
    ∃ r, v = SmtValue.RegLan r := by
  intro hRel hRe
  rcases hRe with ⟨r, rfl⟩
  cases v <;>
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq] at hRel ⊢

private theorem smt_value_rel_eval_reglan_right
    {v w : SmtValue} :
    RuleProofs.smt_value_rel v w ->
    (∃ r, v = SmtValue.RegLan r) ->
    ∃ r, w = SmtValue.RegLan r := by
  intro hRel hRe
  exact smt_value_rel_eval_reglan_left
    (RuleProofs.smt_value_rel_symm v w hRel) hRe

private theorem smt_eval_ne_notvalue_of_has_smt_translation
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
    RuleProofs.eo_has_smt_translation t ->
    __smtx_model_eval M (__eo_to_smt t) ≠ SmtValue.NotValue := by
  intro hTrans hEval
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        __smtx_typeof (__eo_to_smt t) :=
    smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hTrans
  rw [hEval] at hValTy
  simp [__smtx_typeof_value] at hValTy
  exact hTrans hValTy.symm

private theorem smt_value_rel_ne_notvalue_right
    {v w : SmtValue} :
    RuleProofs.smt_value_rel v w ->
    v ≠ SmtValue.NotValue ->
    w ≠ SmtValue.NotValue := by
  intro hRel hvNe hw
  subst w
  cases v <;>
    simp [RuleProofs.smt_value_rel, __smtx_model_eval_eq, native_veq] at hRel hvNe

private theorem smt_value_rel_ne_notvalue_left
    {v w : SmtValue} :
    RuleProofs.smt_value_rel v w ->
    w ≠ SmtValue.NotValue ->
    v ≠ SmtValue.NotValue := by
  intro hRel hwNe
  exact smt_value_rel_ne_notvalue_right
    (RuleProofs.smt_value_rel_symm v w hRel) hwNe

private theorem smt_value_rel_aciNormPayload_right_of_rel_has_translation
    (M : SmtModel) (hM : model_total_typed M) (t norm : Term) :
    RuleProofs.eo_has_smt_translation t ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M (__eo_to_smt norm)) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt t))
      (__smtx_model_eval M (__eo_to_smt (aciNormPayload norm))) := by
  intro hTrans hRel
  have htNe : __smtx_model_eval M (__eo_to_smt t) ≠ SmtValue.NotValue :=
    smt_eval_ne_notvalue_of_has_smt_translation M hM t hTrans
  have hNormNe : __smtx_model_eval M (__eo_to_smt norm) ≠ SmtValue.NotValue :=
    smt_value_rel_ne_notvalue_right hRel htNe
  rw [aciNormPayload_eq_self_of_eval_not_notvalue M norm hNormNe]
  exact hRel

private theorem bvConcat_smt_value_rel_right_empty_eval
    (M : SmtModel) (hM : model_total_typed M)
    (x nil : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec w ->
    __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Binary 0 0 ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hxTy hNilEval
  have hNN : term_has_non_none_type (__eo_to_smt x) := by
    unfold term_has_non_none_type
    rw [hxTy]
    intro h
    cases h
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt x)) =
        SmtType.BitVec w := by
    simpa [hxTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt x) hNN
  rcases bitvec_value_canonical hValTy with ⟨n, hxEval⟩
  have hMod :
      native_zeq n
          (native_mod_total n (native_int_pow2 (native_nat_to_int w))) =
        true := by
    exact bitvec_payload_canonical (by simpa [hxEval] using hValTy)
  have hModEq :
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) = n := by
    have hEq :
        n = native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
      simpa [SmtEval.native_zeq] using hMod
    exact hEq.symm
  have hPow0 : native_int_pow2 0 = 1 := by
    native_decide
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt nil)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_concat, hxEval, hNilEval]
  simp only [SmtEval.native_binary_concat, SmtEval.native_zplus,
    SmtEval.native_zmult, hPow0, Int.add_zero, Int.mul_one]
  rw [hModEq]
  simp [__smtx_model_eval_eq, native_veq]

private theorem bvConcat_eval_concat_binary_of_args_eval_binary
    (M : SmtModel) (x y : Term) (wx wy : native_Int) :
    (∃ nx,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary wx nx) ->
    (∃ ny,
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Binary wy ny) ->
    ∃ n,
      __smtx_model_eval M
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y)) =
        SmtValue.Binary (native_zplus wx wy) n := by
  intro hxBin hyBin
  rcases hxBin with ⟨nx, hxEval⟩
  rcases hyBin with ⟨ny, hyEval⟩
  refine ⟨native_mod_total (native_binary_concat wx nx wy ny)
      (native_int_pow2 (native_zplus wx wy)), ?_⟩
  change __smtx_model_eval M
      (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y)) =
    SmtValue.Binary (native_zplus wx wy)
      (native_mod_total (native_binary_concat wx nx wy ny)
        (native_int_pow2 (native_zplus wx wy)))
  simp [__smtx_model_eval, __smtx_model_eval_concat, hxEval, hyEval]

private theorem bvConcat_smt_value_rel_congr_eval
    (M : SmtModel) (x x' y y' : Term) (wx wy : native_Int) :
    (∃ nx,
      __smtx_model_eval M (__eo_to_smt x) = SmtValue.Binary wx nx) ->
    (∃ ny,
      __smtx_model_eval M (__eo_to_smt y) = SmtValue.Binary wy ny) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt x')) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt y')) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x) y)))
      (__smtx_model_eval M
        (__eo_to_smt
          (Term.Apply (Term.Apply (Term.UOp UserOp.concat) x') y'))) := by
  intro hxBin hyBin hxRel hyRel
  rcases hxBin with ⟨nx, hxEval⟩
  rcases hyBin with ⟨ny, hyEval⟩
  rcases smt_value_rel_eval_binary_right hxRel ⟨nx, hxEval⟩ with
    ⟨nx', hxEval'⟩
  rcases smt_value_rel_eval_binary_right hyRel ⟨ny, hyEval⟩ with
    ⟨ny', hyEval'⟩
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y)))
      (__smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x') (__eo_to_smt y'))) =
    SmtValue.Boolean true
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hxRel hyRel
  simp [__smtx_model_eval, __smtx_model_eval_concat, hxEval, hyEval,
    hxEval', hyEval', __smtx_model_eval_eq, native_veq] at hxRel hyRel ⊢
  subst nx'
  subst ny'
  rfl

private theorem bvEvalCanonical_of_smt_type_bitvec
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    ∃ n,
      __smtx_model_eval M (__eo_to_smt t) =
          SmtValue.Binary (native_nat_to_int w) n ∧
        native_zleq 0 (native_nat_to_int w) = true ∧
        native_zeq n
            (native_mod_total n (native_int_pow2 (native_nat_to_int w))) =
          true := by
  intro hTy
  have hNN : term_has_non_none_type (__eo_to_smt t) := by
    unfold term_has_non_none_type
    rw [hTy]
    intro h
    cases h
  have hValTy :
      __smtx_typeof_value (__smtx_model_eval M (__eo_to_smt t)) =
        SmtType.BitVec w := by
    simpa [hTy] using
      smt_model_eval_preserves_type_of_non_none M hM (__eo_to_smt t) hNN
  rcases bitvec_value_canonical hValTy with ⟨n, hEval⟩
  refine ⟨n, hEval, ?_, ?_⟩
  · exact bitvec_width_nonneg (by simpa [hEval] using hValTy)
  · exact bitvec_payload_canonical (by simpa [hEval] using hValTy)

private theorem bvEvalCanonical_of_smt_type_bitvec_any
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    BvEvalCanonical M t := by
  intro hTy
  rcases bvEvalCanonical_of_smt_type_bitvec M hM t w hTy with
    ⟨n, hEval, hWidth, hMod⟩
  exact ⟨native_nat_to_int w, n, hEval, hWidth, hMod⟩

private theorem native_int_pow2_pos_of_nonneg {w : native_Int}
    (hw : 0 <= w) :
    0 < native_int_pow2 w := by
  have hnot : ¬ w < 0 := Int.not_lt_of_ge hw
  simp [native_int_pow2, native_zexp_total, hnot]
  exact Int.pow_pos (by decide)

private theorem native_int_pow2_add_of_nonneg {a b : native_Int}
    (ha : 0 <= a) (hb : 0 <= b) :
    native_int_pow2 (native_zplus a b) =
      native_int_pow2 a * native_int_pow2 b := by
  have hab : ¬ a + b < 0 := Int.not_lt_of_ge (Int.add_nonneg ha hb)
  have haNot : ¬ a < 0 := Int.not_lt_of_ge ha
  have hbNot : ¬ b < 0 := Int.not_lt_of_ge hb
  simp [native_int_pow2, native_zexp_total, native_zplus, hab, haNot, hbNot]
  have hNat : (a + b).toNat = a.toNat + b.toNat := by
    have htoa := Int.toNat_of_nonneg ha
    have htob := Int.toNat_of_nonneg hb
    have htoab := Int.toNat_of_nonneg (Int.add_nonneg ha hb)
    omega
  rw [hNat]
  exact Int.pow_add 2 a.toNat b.toNat

private theorem bitvec_toInt_emod_pow (w : Nat) (x : BitVec w) :
    x.toInt % (2 ^ w : Int) = x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  by_cases h : 2 * x.toNat < 2 ^ w
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)
  · simp [h]
    exact Int.emod_eq_of_lt (by exact Int.natCast_nonneg _)
      (by exact_mod_cast x.isLt)

private theorem native_int_pow2_nat (w : Nat) :
    native_int_pow2 (native_nat_to_int w) = (2 ^ w : Int) := by
  have h : ¬ (↑w : Int) < 0 := by simp
  simp [native_int_pow2, native_zexp_total, native_nat_to_int, h]

private theorem native_mod_pow2_eq_bitvec_toNat (w : Nat) (n : Int) :
    native_mod_total n (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n).toNat : Int) := by
  rw [native_int_pow2_nat]
  change n % (2 ^ w : Int) = ((BitVec.ofInt w n).toNat : Int)
  rw [BitVec.toNat_ofInt]
  have hpow : 0 < (2 ^ w : Int) := by exact_mod_cast Nat.two_pow_pos w
  exact (Int.toNat_of_nonneg (Int.emod_nonneg n (Int.ne_of_gt hpow))).symm

private theorem native_binary_and_mod_eq_toNat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_and (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      ((BitVec.ofInt w n1 &&& BitVec.ofInt w n2).toNat : Int) := by
  cases w with
  | zero =>
      simp [native_binary_and, native_piand, native_mod_total,
        native_int_pow2_nat]
  | succ w =>
      simp [native_binary_and, native_piand, native_mod_total,
        native_int_pow2_nat, native_nat_to_int, native_ite, native_zeq]
      exact bitvec_toInt_emod_pow (Nat.succ w)
        (BitVec.ofInt (Nat.succ w) n1 &&& BitVec.ofInt (Nat.succ w) n2)

private theorem bitvec_ofInt_natCast_toNat {w : Nat} (x : BitVec w) :
    BitVec.ofInt w (x.toNat : Int) = x := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp

private theorem native_binary_and_comm_mod_nat
    (w : Nat) (n1 n2 : Int) :
    native_mod_total (native_binary_and (native_nat_to_int w) n1 n2)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total (native_binary_and (native_nat_to_int w) n2 n1)
        (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_binary_and_mod_eq_toNat, native_binary_and_mod_eq_toNat]
  rw [BitVec.and_comm]

private theorem native_binary_and_self_mod_nat (w : Nat) (n : Int) :
    native_mod_total (native_binary_and (native_nat_to_int w) n n)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_binary_and_mod_eq_toNat, native_mod_pow2_eq_bitvec_toNat]
  simp

private theorem native_binary_and_assoc_mod_nat
    (w : Nat) (n1 n2 n3 : Int) :
    native_mod_total
        (native_binary_and (native_nat_to_int w)
          (native_mod_total (native_binary_and (native_nat_to_int w) n1 n2)
            (native_int_pow2 (native_nat_to_int w))) n3)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total
        (native_binary_and (native_nat_to_int w) n1
          (native_mod_total (native_binary_and (native_nat_to_int w) n2 n3)
            (native_int_pow2 (native_nat_to_int w))))
        (native_int_pow2 (native_nat_to_int w)) := by
  have h12 :
      BitVec.ofInt w
          (native_mod_total (native_binary_and (native_nat_to_int w) n1 n2)
            (native_int_pow2 (native_nat_to_int w))) =
        (BitVec.ofInt w n1 &&& BitVec.ofInt w n2) := by
    rw [native_binary_and_mod_eq_toNat]
    exact bitvec_ofInt_natCast_toNat _
  have h23 :
      BitVec.ofInt w
          (native_mod_total (native_binary_and (native_nat_to_int w) n2 n3)
            (native_int_pow2 (native_nat_to_int w))) =
        (BitVec.ofInt w n2 &&& BitVec.ofInt w n3) := by
    rw [native_binary_and_mod_eq_toNat]
    exact bitvec_ofInt_natCast_toNat _
  calc
    native_mod_total
        (native_binary_and (native_nat_to_int w)
          (native_mod_total (native_binary_and (native_nat_to_int w) n1 n2)
            (native_int_pow2 (native_nat_to_int w))) n3)
        (native_int_pow2 (native_nat_to_int w))
        =
      ((BitVec.ofInt w
          (native_mod_total (native_binary_and (native_nat_to_int w) n1 n2)
            (native_int_pow2 (native_nat_to_int w))) &&&
        BitVec.ofInt w n3).toNat : Int) := by
          rw [native_binary_and_mod_eq_toNat]
    _ = (((BitVec.ofInt w n1 &&& BitVec.ofInt w n2) &&&
          BitVec.ofInt w n3).toNat : Int) := by
          rw [h12]
    _ = ((BitVec.ofInt w n1 &&& (BitVec.ofInt w n2 &&&
          BitVec.ofInt w n3)).toNat : Int) := by
          rw [BitVec.and_assoc]
    _ =
      ((BitVec.ofInt w n1 &&&
        BitVec.ofInt w
          (native_mod_total (native_binary_and (native_nat_to_int w) n2 n3)
            (native_int_pow2 (native_nat_to_int w)))).toNat : Int) := by
          rw [h23]
    _ =
      native_mod_total
        (native_binary_and (native_nat_to_int w) n1
          (native_mod_total (native_binary_and (native_nat_to_int w) n2 n3)
            (native_int_pow2 (native_nat_to_int w))))
        (native_int_pow2 (native_nat_to_int w)) := by
          symm
          rw [native_binary_and_mod_eq_toNat]

private theorem bvAnd_smt_value_rel_comm_eval
    (M : SmtModel) (x y : Term) (w : Nat) (nx ny : Int) :
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (native_nat_to_int w) ny ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x y)))
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd y x))) := by
  intro hxEval hyEval
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y)))
      (__smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x))) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_bvand, hxEval, hyEval]
  rw [native_binary_and_comm_mod_nat]
  exact RuleProofs.smtx_model_eval_eq_refl _

private theorem bvAnd_smt_value_rel_self_eval
    (M : SmtModel) (x : Term) (w : Nat) (nx : Int) :
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) =
      true ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hxEval hxMod
  have hModEq :
      native_mod_total nx (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq :
        nx =
          native_mod_total nx (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hxMod
    exact hEq.symm
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt x)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_bvand, hxEval]
  rw [native_binary_and_self_mod_nat, hModEq]
  exact RuleProofs.smtx_model_eval_eq_refl _

private theorem bvAnd_smt_value_rel_assoc_eval
    (M : SmtModel) (x y z : Term) (w : Nat) (nx ny nz : Int) :
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (native_nat_to_int w) ny ->
    __smtx_model_eval M (__eo_to_smt z) =
        SmtValue.Binary (native_nat_to_int w) nz ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd x y) z)))
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x (mkBvAnd y z)))) := by
  intro hxEval hyEval hzEval
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.bvand
          (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y))
          (__eo_to_smt z)))
      (__smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt x)
          (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt z)))) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_bvand, hxEval, hyEval,
    hzEval]
  rw [native_binary_and_assoc_mod_nat]
  exact RuleProofs.smtx_model_eval_eq_refl _

private def BvEvalCanonicalWidth (M : SmtModel) (w : Nat) (t : Term) : Prop :=
  ∃ n,
    __smtx_model_eval M (__eo_to_smt t) =
        SmtValue.Binary (native_nat_to_int w) n ∧
      native_zeq n
          (native_mod_total n (native_int_pow2 (native_nat_to_int w))) =
        true

private def BvAndListCanonical (M : SmtModel) (w : Nat) : Term -> Prop
  | Term.Apply (Term.Apply (Term.UOp UserOp.bvand) x) xs =>
      BvEvalCanonicalWidth M w x ∧ BvAndListCanonical M w xs
  | t => BvEvalCanonicalWidth M w t

private theorem bvEvalCanonicalWidth_of_smt_type_bitvec
    (M : SmtModel) (hM : model_total_typed M) (t : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    BvEvalCanonicalWidth M w t := by
  intro hTy
  rcases bvEvalCanonical_of_smt_type_bitvec M hM t w hTy with
    ⟨n, hEval, _hWidth, hMod⟩
  exact ⟨n, hEval, hMod⟩

private theorem bvAnd_eval_canonical_width_of_canonical_args
    (M : SmtModel) (x y : Term) (w : Nat) :
    BvEvalCanonicalWidth M w x ->
    BvEvalCanonicalWidth M w y ->
    BvEvalCanonicalWidth M w (mkBvAnd x y) := by
  intro hx hy
  rcases hx with ⟨nx, hxEval, _hxMod⟩
  rcases hy with ⟨ny, hyEval, _hyMod⟩
  refine ⟨
    native_mod_total
      (native_binary_and (native_nat_to_int w) nx ny)
      (native_int_pow2 (native_nat_to_int w)), ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.Binary (native_nat_to_int w)
        (native_mod_total
          (native_binary_and (native_nat_to_int w) nx ny)
          (native_int_pow2 (native_nat_to_int w)))
    simp [__smtx_model_eval, __smtx_model_eval_bvand, hxEval, hyEval]
  · exact native_mod_total_canonical (native_nat_to_int w)
      (native_binary_and (native_nat_to_int w) nx ny)

private theorem bvAndListCanonical_eval
    (M : SmtModel) (w : Nat) :
    (t : Term) -> BvAndListCanonical M w t -> BvEvalCanonicalWidth M w t
  | t, h => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case bvand =>
                    exact bvAnd_eval_canonical_width_of_canonical_args
                      M x xs w h.1 (bvAndListCanonical_eval M w xs h.2)
                  all_goals
                    simpa [BvAndListCanonical] using h
              | _ =>
                  simpa [BvAndListCanonical] using h
          | _ =>
              simpa [BvAndListCanonical] using h
      | _ =>
          simpa [BvAndListCanonical] using h

private theorem bvEvalCanonicalWidth_ne_stuck
    {M : SmtModel} {w : Nat} {t : Term} :
    BvEvalCanonicalWidth M w t -> t ≠ Term.Stuck := by
  intro hCan hStuck
  rcases hCan with ⟨n, hEval, _hMod⟩
  subst t
  rw [show __eo_to_smt Term.Stuck = SmtTerm.None by rfl] at hEval
  rw [smtx_model_eval_none] at hEval
  cases hEval

private theorem bvAnd_is_list_true_ne_stuck {t : Term} :
    __eo_is_list (Term.UOp UserOp.bvand) t = Term.Boolean true ->
    t ≠ Term.Stuck := by
  intro hList hStuck
  subst t
  simp [__eo_is_list] at hList

private theorem bvAnd_smt_value_rel_congr_eval
    (M : SmtModel) (x x' y y' : Term) (w : Nat) :
    (∃ nx,
      __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx) ->
    (∃ ny,
      __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (native_nat_to_int w) ny) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt x')) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt y))
      (__smtx_model_eval M (__eo_to_smt y')) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x y)))
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x' y'))) := by
  intro hxBin hyBin hxRel hyRel
  rcases hxBin with ⟨nx, hxEval⟩
  rcases hyBin with ⟨ny, hyEval⟩
  rcases smt_value_rel_eval_binary_right hxRel ⟨nx, hxEval⟩ with
    ⟨nx', hxEval'⟩
  rcases smt_value_rel_eval_binary_right hyRel ⟨ny, hyEval⟩ with
    ⟨ny', hyEval'⟩
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt y)))
      (__smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt x') (__eo_to_smt y'))) =
    SmtValue.Boolean true
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true] at hxRel hyRel
  simp [__smtx_model_eval, __smtx_model_eval_bvand, hxEval, hyEval,
    hxEval', hyEval', __smtx_model_eval_eq, native_veq] at hxRel hyRel ⊢
  subst nx'
  subst ny'
  rfl

private theorem bvAnd_smt_value_rel_left_rotate_eval
    (M : SmtModel) (a b c : Term) (w : Nat) (na nb nc : Int) :
    __smtx_model_eval M (__eo_to_smt a) =
        SmtValue.Binary (native_nat_to_int w) na ->
    __smtx_model_eval M (__eo_to_smt b) =
        SmtValue.Binary (native_nat_to_int w) nb ->
    __smtx_model_eval M (__eo_to_smt c) =
        SmtValue.Binary (native_nat_to_int w) nc ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd a (mkBvAnd b c))))
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd b (mkBvAnd a c)))) := by
  intro haEval hbEval hcEval
  let nab :=
    native_mod_total
      (native_binary_and (native_nat_to_int w) na nb)
      (native_int_pow2 (native_nat_to_int w))
  have habEval :
      __smtx_model_eval M (__eo_to_smt (mkBvAnd a b)) =
        SmtValue.Binary (native_nat_to_int w) nab := by
    change __smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt a) (__eo_to_smt b)) =
      SmtValue.Binary (native_nat_to_int w) nab
    simp [nab, __smtx_model_eval, __smtx_model_eval_bvand, haEval, hbEval]
  have hAssoc₁ :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd a (mkBvAnd b c))))
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd a b) c))) :=
    RuleProofs.smt_value_rel_symm _ _
      (bvAnd_smt_value_rel_assoc_eval M a b c w na nb nc
        haEval hbEval hcEval)
  have hComm :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd a b) c)))
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd b a) c))) :=
    bvAnd_smt_value_rel_congr_eval M (mkBvAnd a b) (mkBvAnd b a) c c
      w ⟨nab, habEval⟩ ⟨nc, hcEval⟩
      (bvAnd_smt_value_rel_comm_eval M a b w na nb haEval hbEval)
      (RuleProofs.smt_value_rel_refl
        (__smtx_model_eval M (__eo_to_smt c)))
  have hAssoc₂ :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd b a) c)))
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd b (mkBvAnd a c)))) :=
    bvAnd_smt_value_rel_assoc_eval M b a c w nb na nc
      hbEval haEval hcEval
  exact RuleProofs.smt_value_rel_trans
    (__smtx_model_eval M (__eo_to_smt (mkBvAnd a (mkBvAnd b c))))
    (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd a b) c)))
    (__smtx_model_eval M (__eo_to_smt (mkBvAnd b (mkBvAnd a c))))
    hAssoc₁
    (RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd a b) c)))
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd b a) c)))
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd b (mkBvAnd a c))))
      hComm hAssoc₂)

private theorem bvAnd_smt_value_rel_insert_duplicate_eval
    (M : SmtModel) (x y : Term) (w : Nat) (nx ny : Int) :
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    __smtx_model_eval M (__eo_to_smt y) =
        SmtValue.Binary (native_nat_to_int w) ny ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) =
      true ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x y)))
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x (mkBvAnd x y)))) := by
  intro hxEval hyEval hxMod
  have hXXCan :
      BvEvalCanonicalWidth M w (mkBvAnd x x) :=
    bvAnd_eval_canonical_width_of_canonical_args M x x w
      ⟨nx, hxEval, hxMod⟩ ⟨nx, hxEval, hxMod⟩
  rcases hXXCan with ⟨nxx, hxxEval, _hxxMod⟩
  have hAssoc :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd x (mkBvAnd x y))))
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd x x) y))) :=
    RuleProofs.smt_value_rel_symm _ _
      (bvAnd_smt_value_rel_assoc_eval M x x y w nx nx ny
        hxEval hxEval hyEval)
  have hSelf :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd x x) y)))
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd x y))) :=
    bvAnd_smt_value_rel_congr_eval M (mkBvAnd x x) x y y w
      ⟨nxx, hxxEval⟩ ⟨ny, hyEval⟩
      (bvAnd_smt_value_rel_self_eval M x w nx hxEval hxMod)
      (RuleProofs.smt_value_rel_refl
        (__smtx_model_eval M (__eo_to_smt y)))
  exact RuleProofs.smt_value_rel_symm _ _
    (RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x (mkBvAnd x y))))
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd (mkBvAnd x x) y)))
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x y)))
      hAssoc hSelf)

private theorem native_binary_and_right_allOnes_mod_nat
    (w : Nat) (n id : Int) :
    BitVec.ofInt w id = BitVec.allOnes w ->
    native_mod_total (native_binary_and (native_nat_to_int w) n id)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  intro hId
  rw [native_binary_and_mod_eq_toNat, native_mod_pow2_eq_bitvec_toNat]
  rw [hId, BitVec.and_allOnes]

private theorem native_binary_and_left_allOnes_mod_nat
    (w : Nat) (id n : Int) :
    BitVec.ofInt w id = BitVec.allOnes w ->
    native_mod_total (native_binary_and (native_nat_to_int w) id n)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  intro hId
  rw [native_binary_and_mod_eq_toNat, native_mod_pow2_eq_bitvec_toNat]
  rw [hId, BitVec.allOnes_and]

private theorem bvAnd_smt_value_rel_right_allOnes_eval
    (M : SmtModel) (x id : Term) (w : Nat) (nx nid : Int) :
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Binary (native_nat_to_int w) nid ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) =
      true ->
    BitVec.ofInt w nid = BitVec.allOnes w ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd x id)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hxEval hIdEval hxMod hIdAllOnes
  have hModEq :
      native_mod_total nx (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq :
        nx =
          native_mod_total nx (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hxMod
    exact hEq.symm
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt x) (__eo_to_smt id)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_bvand, hxEval, hIdEval]
  rw [native_binary_and_right_allOnes_mod_nat w nx nid hIdAllOnes, hModEq]
  exact RuleProofs.smtx_model_eval_eq_refl _

private theorem bvAnd_smt_value_rel_left_allOnes_eval
    (M : SmtModel) (id x : Term) (w : Nat) (nid nx : Int) :
    __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Binary (native_nat_to_int w) nid ->
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) =
      true ->
    BitVec.ofInt w nid = BitVec.allOnes w ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd id x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hIdEval hxEval hxMod hIdAllOnes
  have hModEq :
      native_mod_total nx (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq :
        nx =
          native_mod_total nx (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hxMod
    exact hEq.symm
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.bvand (__eo_to_smt id) (__eo_to_smt x)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_bvand, hIdEval, hxEval]
  rw [native_binary_and_left_allOnes_mod_nat w nid nx hIdAllOnes, hModEq]
  exact RuleProofs.smtx_model_eval_eq_refl _

private theorem bvAnd_l1_eq_self_of_eq (id : Term) :
    id ≠ Term.Stuck ->
    __eo_l_1___get_ai_norm_rec (Term.UOp UserOp.bvand) id id = id := by
  intro hId
  have hEq : __eo_eq id id = Term.Boolean true :=
    eo_eq_eq_true_of_eq_local rfl hId hId
  simp [__eo_l_1___get_ai_norm_rec, hEq, __eo_ite, native_ite, native_teq]

private theorem bvAnd_l1_eq_and_of_ne_id (id t : Term) :
    id ≠ Term.Stuck ->
    t ≠ Term.Stuck ->
    t ≠ id ->
    __eo_l_1___get_ai_norm_rec (Term.UOp UserOp.bvand) id t =
      mkBvAnd t id := by
  intro hId hT hNe
  have hEq : __eo_eq id t = Term.Boolean false :=
    eo_eq_eq_false_of_ne_local
      (x := id) (y := t) (by
        intro h
        exact hNe h.symm) hId hT
  rw [show __eo_l_1___get_ai_norm_rec (Term.UOp UserOp.bvand) id t =
      __eo_ite (__eo_eq id t) id
        (__eo_l_2___get_ai_norm_rec (Term.UOp UserOp.bvand) id t) by
    cases id <;> cases t <;>
      simp [__eo_l_1___get_ai_norm_rec] at hId hT ⊢]
  rw [hEq]
  cases id <;> cases t <;>
    simp [__eo_l_2___get_ai_norm_rec, __eo_ite, native_ite, native_teq] at hId hT ⊢ <;>
    contradiction

private theorem bvAnd_l1_norm_rec_rel_eval
    (M : SmtModel) (hM : model_total_typed M) (id : Term) (w : Nat)
    (hIdList :
      __eo_is_list (Term.UOp UserOp.bvand) id = Term.Boolean true)
    (hIdEval :
      __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Binary (native_nat_to_int w) (native_int_pow2 (native_nat_to_int w) - 1))
    (hIdCan : BvAndListCanonical M w id)
    (hIdNe : id ≠ Term.Stuck)
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.bvand)
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.bvand) id t) =
        Term.Boolean true ∧
      BvAndListCanonical M w
        (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.bvand) id t) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_l_1___get_ai_norm_rec (Term.UOp UserOp.bvand) id t)))
        (__smtx_model_eval M (__eo_to_smt t)) := by
  intro hTy
  have hTNe : t ≠ Term.Stuck := term_ne_stuck_of_smt_bitvec_type hTy
  by_cases hEq : t = id
  · subst t
    rw [bvAnd_l1_eq_self_of_eq id hIdNe]
    exact ⟨hIdList, hIdCan, RuleProofs.smt_value_rel_refl _⟩
  · rw [bvAnd_l1_eq_and_of_ne_id id t hIdNe hTNe hEq]
    have htCan : BvEvalCanonicalWidth M w t :=
      bvEvalCanonicalWidth_of_smt_type_bitvec M hM t w hTy
    rcases htCan with ⟨nt, htEval, htMod⟩
    have hIdAllOnes :
        BitVec.ofInt w (native_int_pow2 (native_nat_to_int w) - 1) =
          BitVec.allOnes w := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofInt, BitVec.toNat_allOnes, native_int_pow2_nat]
      have hPowPos : 0 < (2 ^ w : Int) := by
        exact_mod_cast Nat.two_pow_pos w
      have hLower : 0 <= (2 ^ w : Int) - 1 := by
        omega
      have hUpper : (2 ^ w : Int) - 1 < (2 ^ w : Int) := by
        omega
      change (((2 ^ w : Int) - 1) % (2 ^ w : Int)).toNat = 2 ^ w - 1
      rw [Int.emod_eq_of_lt hLower hUpper]
      have hToNat :
          (((2 ^ w : Int) - 1).toNat : Int) = (2 ^ w : Int) - 1 :=
        Int.toNat_of_nonneg hLower
      have hRhs :
          ((2 ^ w - 1 : Nat) : Int) = (2 ^ w : Int) - 1 :=
        Int.ofNat_sub Nat.one_le_two_pow
      exact Int.ofNat.inj (hToNat.trans hRhs.symm)
    exact ⟨
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.bvand) t id (by decide) hIdList,
      ⟨⟨nt, htEval, htMod⟩, hIdCan⟩,
      bvAnd_smt_value_rel_right_allOnes_eval M t id w nt
        (native_int_pow2 (native_nat_to_int w) - 1)
        htEval hIdEval htMod hIdAllOnes⟩

private theorem bvAnd_list_concat_rec_rel_eval
    (M : SmtModel) (w : Nat) :
    (a z : Term) ->
    __eo_is_list (Term.UOp UserOp.bvand) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.bvand) z = Term.Boolean true ->
    BvAndListCanonical M w a ->
    BvAndListCanonical M w z ->
    BvAndListCanonical M w (__eo_list_concat_rec a z) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)))
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd a z)))
  | a, z, hAList, hZList, hACan, hZCan => by
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z =>
          cases (Term.UOp UserOp.bvand) <;> simp [__eo_is_list] at hAList
      | case2 a hA =>
          cases (Term.UOp UserOp.bvand) <;> simp [__eo_is_list] at hZList
      | case3 g x y z hZ ih =>
          have hg : g = Term.UOp UserOp.bvand :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.bvand) g x y hAList
          subst g
          have hYList :
              __eo_is_list (Term.UOp UserOp.bvand) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.bvand) x y hAList
          have hTailNe :
              __eo_list_concat_rec y z ≠ Term.Stuck :=
            eo_list_concat_rec_ne_stuck_of_list
              (Term.UOp UserOp.bvand) y z hYList hZ
          have hXCan : BvEvalCanonicalWidth M w x := hACan.1
          have hYCanList : BvAndListCanonical M w y := hACan.2
          have hYCan : BvEvalCanonicalWidth M w y :=
            bvAndListCanonical_eval M w y hYCanList
          have hZCanEval : BvEvalCanonicalWidth M w z :=
            bvAndListCanonical_eval M w z hZCan
          have hIH := ih hYList hZList hYCanList hZCan
          rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
            (Term.UOp UserOp.bvand) x y z hTailNe]
          have hTailCan :
              BvEvalCanonicalWidth M w (__eo_list_concat_rec y z) :=
            bvAndListCanonical_eval M w (__eo_list_concat_rec y z) hIH.1
          rcases hXCan with ⟨nx, hxEval, hxMod⟩
          rcases hTailCan with ⟨nyz, hTailEval, _hTailMod⟩
          have hCongr :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvAnd x (__eo_list_concat_rec y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvAnd x (mkBvAnd y z)))) :=
            bvAnd_smt_value_rel_congr_eval M x x
              (__eo_list_concat_rec y z) (mkBvAnd y z) w
              ⟨nx, hxEval⟩ ⟨nyz, hTailEval⟩
              (RuleProofs.smt_value_rel_refl
                (__smtx_model_eval M (__eo_to_smt x)))
              hIH.2
          rcases hYCan with ⟨ny, hyEval, _hyMod⟩
          rcases hZCanEval with ⟨nz, hzEval, _hzMod⟩
          have hAssoc :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvAnd x (mkBvAnd y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvAnd (mkBvAnd x y) z))) :=
            RuleProofs.smt_value_rel_symm _ _
              (bvAnd_smt_value_rel_assoc_eval M x y z w nx ny nz
                hxEval hyEval hzEval)
          exact ⟨
            ⟨⟨nx, hxEval, hxMod⟩, hIH.1⟩,
            RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M
                (__eo_to_smt (mkBvAnd x (__eo_list_concat_rec y z))))
              (__smtx_model_eval M
                (__eo_to_smt (mkBvAnd x (mkBvAnd y z))))
              (__smtx_model_eval M
                (__eo_to_smt (mkBvAnd (mkBvAnd x y) z)))
              hCongr hAssoc⟩
      | case4 nil z hNil hZ hNot =>
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.bvand) nil =
                Term.Boolean true := by
            have hGet :=
              eo_get_nil_rec_ne_stuck_of_is_list_true
                (Term.UOp UserOp.bvand) nil hAList
            have hReq :
                __eo_requires
                    (__eo_is_list_nil (Term.UOp UserOp.bvand) nil)
                    (Term.Boolean true) nil ≠ Term.Stuck := by
              simpa [__eo_get_nil_rec] using hGet
            exact eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.bvand) nil)
              (Term.Boolean true) nil hReq
          have hNilCan : BvEvalCanonicalWidth M w nil :=
            bvAndListCanonical_eval M w nil hACan
          rcases hNilCan with ⟨nnil, hNilEval, hNilMod⟩
          have hNilAllOnes :
              BitVec.ofInt w nnil = BitVec.allOnes w := by
            cases nil <;>
              simp [__eo_is_list_nil, __eo_is_list_nil_bvand, __eo_to_z,
                __eo_not, __eo_is_eq, native_and, native_not, native_teq,
                native_zeq] at hNilTrue
            case Binary wb nb =>
              have hEvalEq :
                  SmtValue.Binary wb nb =
                    SmtValue.Binary (native_nat_to_int w) nnil := by
                rw [show __eo_to_smt (Term.Binary wb nb) =
                    SmtTerm.Binary wb nb by rfl] at hNilEval
                rw [__smtx_model_eval] at hNilEval
                exact hNilEval
              injection hEvalEq with hWidthEq hPayloadEq
              subst wb
              subst nnil
              have hNotModZero :
                  native_mod_total
                      (native_binary_not (native_nat_to_int w) nb)
                      (native_int_pow2 (native_nat_to_int w)) =
                    0 := by
                exact hNilTrue.symm
              have hWidthNonneg :
                  native_zleq 0 (native_nat_to_int w) = true := by
                simp [native_zleq, native_nat_to_int]
              have hNbRange :=
                bitvec_payload_range_of_canonical hWidthNonneg hNilMod
              have hNbNonneg : 0 <= nb := hNbRange.1
              have hNbLt : nb < native_int_pow2 (native_nat_to_int w) :=
                hNbRange.2
              have hWidthNonnegInt : 0 <= native_nat_to_int w := by
                simp [native_nat_to_int]
              have hPowPos :
                  0 < native_int_pow2 (native_nat_to_int w) :=
                native_int_pow2_pos_of_nonneg hWidthNonnegInt
              have hNotRaw :
                  native_binary_not (native_nat_to_int w) nb =
                    native_int_pow2 (native_nat_to_int w) - (nb + 1) := by
                simp [native_binary_not, native_zplus, native_zneg,
                  Int.sub_eq_add_neg]
              have hNotLower :
                  0 <= native_binary_not (native_nat_to_int w) nb := by
                rw [hNotRaw]
                exact Int.sub_nonneg.mpr (Int.add_one_le_of_lt hNbLt)
              have hNotUpper :
                  native_binary_not (native_nat_to_int w) nb <
                    native_int_pow2 (native_nat_to_int w) := by
                rw [hNotRaw]
                exact Int.sub_lt_self _ (Int.lt_add_one_of_le hNbNonneg)
              have hNotModSelf :
                  native_mod_total
                      (native_binary_not (native_nat_to_int w) nb)
                      (native_int_pow2 (native_nat_to_int w)) =
                    native_binary_not (native_nat_to_int w) nb := by
                simpa [native_mod_total] using
                  Int.emod_eq_of_lt hNotLower hNotUpper
              have hNotEq :
                  native_binary_not (native_nat_to_int w) nb = 0 := by
                rw [← hNotModSelf]
                exact hNotModZero
              have hPayload :
                  nb = (2 ^ w : Int) - 1 := by
                rw [hNotRaw] at hNotEq
                rw [native_int_pow2_nat] at hNotEq
                have hEqPow : (2 ^ w : Int) = nb + 1 :=
                  Int.sub_eq_zero.mp hNotEq
                symm
                exact (Int.sub_eq_iff_eq_add).mpr hEqPow
              apply BitVec.eq_of_toNat_eq
              rw [BitVec.toNat_ofInt, BitVec.toNat_allOnes]
              rw [hPayload]
              have hLower : 0 <= (2 ^ w : Int) - 1 := by
                have hPowPos : 0 < (2 ^ w : Int) := by
                  exact_mod_cast Nat.two_pow_pos w
                omega
              have hUpper : (2 ^ w : Int) - 1 < (2 ^ w : Int) := by
                omega
              change (((2 ^ w : Int) - 1) % (2 ^ w : Int)).toNat = 2 ^ w - 1
              rw [Int.emod_eq_of_lt hLower hUpper]
              have hToNat :
                  (((2 ^ w : Int) - 1).toNat : Int) = (2 ^ w : Int) - 1 :=
                Int.toNat_of_nonneg hLower
              have hRhs :
                  ((2 ^ w - 1 : Nat) : Int) = (2 ^ w : Int) - 1 :=
                Int.ofNat_sub Nat.one_le_two_pow
              exact Int.ofNat.inj (hToNat.trans hRhs.symm)
          rw [show __eo_list_concat_rec nil z = z by
            cases nil <;> cases z <;>
              simp [__eo_is_list_nil, __eo_list_concat_rec] at hNilTrue ⊢]
          exact ⟨hZCan,
            RuleProofs.smt_value_rel_symm _ _
              (bvAnd_smt_value_rel_left_allOnes_eval M nil z w nnil
                (Classical.choose (bvAndListCanonical_eval M w z hZCan))
                hNilEval
                (Classical.choose_spec
                  (bvAndListCanonical_eval M w z hZCan)).1
                (Classical.choose_spec
                  (bvAndListCanonical_eval M w z hZCan)).2
                hNilAllOnes)⟩

private theorem bvAnd_list_erase_all_rec_rel_eval
    (M : SmtModel) (w : Nat) :
    (c e : Term) ->
    __eo_is_list (Term.UOp UserOp.bvand) c = Term.Boolean true ->
    BvAndListCanonical M w c ->
    BvEvalCanonicalWidth M w e ->
    __eo_is_list (Term.UOp UserOp.bvand) (__eo_list_erase_all_rec c e) =
        Term.Boolean true ∧
      BvAndListCanonical M w (__eo_list_erase_all_rec c e) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (mkBvAnd e (__eo_list_erase_all_rec c e))))
        (__smtx_model_eval M (__eo_to_smt (mkBvAnd e c)))
  | c, e, hCList, hCCan, hECan => by
      induction c, e using __eo_list_erase_all_rec.induct with
      | case1 e =>
          simp [__eo_is_list] at hCList
      | case2 c hC =>
          exact False.elim ((bvEvalCanonicalWidth_ne_stuck hECan) rfl)
      | case3 f x y e hENotStuck ih =>
          have hf : f = Term.UOp UserOp.bvand :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.bvand) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.bvand) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.bvand) x y hCList
          have hXCan : BvEvalCanonicalWidth M w x := hCCan.1
          have hYCan : BvAndListCanonical M w y := hCCan.2
          have hIH := ih hYList hYCan hECan
          have hRecNe :
              __eo_list_erase_all_rec y e ≠ Term.Stuck :=
            bvAnd_is_list_true_ne_stuck hIH.1
          have hXNe : x ≠ Term.Stuck :=
            bvEvalCanonicalWidth_ne_stuck hXCan
          have hENe : e ≠ Term.Stuck :=
            bvEvalCanonicalWidth_ne_stuck hECan
          by_cases hEq : e = x
          · subst e
            have hEqTerm : __eo_eq x x = Term.Boolean true :=
              eo_eq_eq_true_of_eq_local rfl hXNe hXNe
            have hEraseEq :
                __eo_list_erase_all_rec (mkBvAnd x y) x =
                  __eo_list_erase_all_rec y x := by
              simp [mkBvAnd, __eo_list_erase_all_rec, __eo_prepend_if,
                hEqTerm, __eo_not, native_not, SmtEval.native_not, hRecNe]
            rw [hEraseEq]
            have hYEval : BvEvalCanonicalWidth M w y :=
              bvAndListCanonical_eval M w y hYCan
            rcases hXCan with ⟨nx, hxEval, hxMod⟩
            rcases hYEval with ⟨ny, hyEval, _hyMod⟩
            have hDup :
                RuleProofs.smt_value_rel
                  (__smtx_model_eval M (__eo_to_smt (mkBvAnd x y)))
                  (__smtx_model_eval M
                    (__eo_to_smt (mkBvAnd x (mkBvAnd x y)))) :=
              bvAnd_smt_value_rel_insert_duplicate_eval M x y w nx ny
                hxEval hyEval hxMod
            exact ⟨hIH.1, hIH.2.1,
              RuleProofs.smt_value_rel_trans
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvAnd x (__eo_list_erase_all_rec y x))))
                (__smtx_model_eval M (__eo_to_smt (mkBvAnd x y)))
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvAnd x (mkBvAnd x y))))
                hIH.2.2 hDup⟩
          · have hEqTerm : __eo_eq e x = Term.Boolean false :=
              eo_eq_eq_false_of_ne_local (x := e) (y := x) hEq hENe hXNe
            have hEraseEq :
                __eo_list_erase_all_rec (mkBvAnd x y) e =
                  mkBvAnd x (__eo_list_erase_all_rec y e) := by
              simp [mkBvAnd, __eo_list_erase_all_rec, __eo_prepend_if,
                hEqTerm, __eo_not, native_not, SmtEval.native_not, hRecNe]
            rw [hEraseEq]
            have hEraseCanEval :
                BvEvalCanonicalWidth M w (__eo_list_erase_all_rec y e) :=
              bvAndListCanonical_eval M w
                (__eo_list_erase_all_rec y e) hIH.2.1
            have hYCanEval : BvEvalCanonicalWidth M w y :=
              bvAndListCanonical_eval M w y hYCan
            rcases hECan with ⟨ne, heEval, heMod⟩
            rcases hXCan with ⟨nx, hxEval, hxMod⟩
            rcases hEraseCanEval with ⟨nerase, hEraseEval, hEraseMod⟩
            rcases hYCanEval with ⟨ny, hyEval, _hyMod⟩
            have hRotLeft :
                RuleProofs.smt_value_rel
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (mkBvAnd e
                        (mkBvAnd x (__eo_list_erase_all_rec y e)))))
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (mkBvAnd x
                        (mkBvAnd e (__eo_list_erase_all_rec y e))))) :=
              bvAnd_smt_value_rel_left_rotate_eval M e x
                (__eo_list_erase_all_rec y e) w ne nx nerase
                heEval hxEval hEraseEval
            have hEEraseCan :
              BvEvalCanonicalWidth M w
                  (mkBvAnd e (__eo_list_erase_all_rec y e)) :=
              bvAnd_eval_canonical_width_of_canonical_args M e
                (__eo_list_erase_all_rec y e) w
                ⟨ne, heEval, heMod⟩
                ⟨nerase, hEraseEval, hEraseMod⟩
            rcases hEEraseCan with ⟨neerase, hEEraseEval, _hEEraseMod⟩
            have hInner :
                RuleProofs.smt_value_rel
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (mkBvAnd x
                        (mkBvAnd e (__eo_list_erase_all_rec y e)))))
                  (__smtx_model_eval M
                    (__eo_to_smt (mkBvAnd x (mkBvAnd e y)))) :=
              bvAnd_smt_value_rel_congr_eval M x x
                (mkBvAnd e (__eo_list_erase_all_rec y e)) (mkBvAnd e y) w
                ⟨nx, hxEval⟩ ⟨neerase, hEEraseEval⟩
                (RuleProofs.smt_value_rel_refl
                  (__smtx_model_eval M (__eo_to_smt x)))
                hIH.2.2
            have hRotRight :
                RuleProofs.smt_value_rel
                  (__smtx_model_eval M (__eo_to_smt (mkBvAnd e (mkBvAnd x y))))
                  (__smtx_model_eval M (__eo_to_smt (mkBvAnd x (mkBvAnd e y)))) :=
              bvAnd_smt_value_rel_left_rotate_eval M e x y w ne nx ny
                heEval hxEval hyEval
            exact ⟨
              eo_is_list_cons_self_true_of_tail_list
                (Term.UOp UserOp.bvand) x (__eo_list_erase_all_rec y e)
                (by decide) hIH.1,
              ⟨⟨nx, hxEval, hxMod⟩, hIH.2.1⟩,
              RuleProofs.smt_value_rel_trans
                (__smtx_model_eval M
                  (__eo_to_smt
                    (mkBvAnd e
                      (mkBvAnd x (__eo_list_erase_all_rec y e)))))
                (__smtx_model_eval M
                  (__eo_to_smt
                    (mkBvAnd x
                      (mkBvAnd e (__eo_list_erase_all_rec y e)))))
                (__smtx_model_eval M (__eo_to_smt (mkBvAnd e (mkBvAnd x y))))
                hRotLeft
                (RuleProofs.smt_value_rel_trans
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (mkBvAnd x
                        (mkBvAnd e (__eo_list_erase_all_rec y e)))))
                  (__smtx_model_eval M
                    (__eo_to_smt (mkBvAnd x (mkBvAnd e y))))
                  (__smtx_model_eval M
                    (__eo_to_smt (mkBvAnd e (mkBvAnd x y))))
                  hInner (RuleProofs.smt_value_rel_symm _ _ hRotRight))⟩
      | case4 nil e hNil hE hNot =>
          simpa [__eo_list_erase_all_rec] using
            (And.intro hCList
              (And.intro hCCan
                  (RuleProofs.smt_value_rel_refl
                  (__smtx_model_eval M (__eo_to_smt (mkBvAnd e nil))))))

private theorem bvAnd_list_setof_rec_rel_eval
    (M : SmtModel) (w : Nat) :
    (c : Term) ->
    __eo_is_list (Term.UOp UserOp.bvand) c = Term.Boolean true ->
    BvAndListCanonical M w c ->
    __eo_is_list (Term.UOp UserOp.bvand) (__eo_list_setof_rec c) =
        Term.Boolean true ∧
      BvAndListCanonical M w (__eo_list_setof_rec c) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__eo_list_setof_rec c)))
        (__smtx_model_eval M (__eo_to_smt c))
  | c, hCList, hCCan => by
      induction c using __eo_list_setof_rec.induct with
      | case1 =>
          simp [__eo_is_list] at hCList
      | case2 f x y ih =>
          have hf : f = Term.UOp UserOp.bvand :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.bvand) f x y hCList
          subst f
          have hYList :
              __eo_is_list (Term.UOp UserOp.bvand) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.bvand) x y hCList
          have hXCan : BvEvalCanonicalWidth M w x := hCCan.1
          have hYCan : BvAndListCanonical M w y := hCCan.2
          have hIH := ih hYList hYCan
          have hErase :=
            bvAnd_list_erase_all_rec_rel_eval M w (__eo_list_setof_rec y) x
              hIH.1 hIH.2.1 hXCan
          have hEraseNe :
              __eo_list_erase_all_rec (__eo_list_setof_rec y) x ≠ Term.Stuck :=
            bvAnd_is_list_true_ne_stuck hErase.1
          have hSetEq :
              __eo_list_setof_rec (mkBvAnd x y) =
                mkBvAnd x
                  (__eo_list_erase_all_rec (__eo_list_setof_rec y) x) := by
            simp [mkBvAnd, __eo_list_setof_rec, __eo_mk_apply, hEraseNe]
          rw [hSetEq]
          have hSetCanEval :
              BvEvalCanonicalWidth M w (__eo_list_setof_rec y) :=
            bvAndListCanonical_eval M w (__eo_list_setof_rec y) hIH.2.1
          rcases hXCan with ⟨nx, hxEval, hxMod⟩
          rcases hSetCanEval with ⟨nset, hSetEval, _hSetMod⟩
          have hCongr :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvAnd x (__eo_list_setof_rec y))))
                (__smtx_model_eval M (__eo_to_smt (mkBvAnd x y))) :=
            bvAnd_smt_value_rel_congr_eval M x x (__eo_list_setof_rec y) y w
              ⟨nx, hxEval⟩ ⟨nset, hSetEval⟩
              (RuleProofs.smt_value_rel_refl
                (__smtx_model_eval M (__eo_to_smt x)))
              hIH.2.2
          exact ⟨
            eo_is_list_cons_self_true_of_tail_list
              (Term.UOp UserOp.bvand) x
              (__eo_list_erase_all_rec (__eo_list_setof_rec y) x)
              (by decide) hErase.1,
            ⟨⟨nx, hxEval, hxMod⟩, hErase.2.1⟩,
            RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M
                (__eo_to_smt
                  (mkBvAnd x
                    (__eo_list_erase_all_rec (__eo_list_setof_rec y) x))))
              (__smtx_model_eval M
                (__eo_to_smt (mkBvAnd x (__eo_list_setof_rec y))))
              (__smtx_model_eval M (__eo_to_smt (mkBvAnd x y)))
              hErase.2.2 hCongr⟩
      | case3 nil hNil hNot =>
          simpa [__eo_list_setof_rec] using
            (And.intro hCList
              (And.intro hCCan
                (RuleProofs.smt_value_rel_refl
                  (__smtx_model_eval M (__eo_to_smt nil)))))

private theorem bvAnd_get_ai_norm_rec_rel_eval
    (M : SmtModel) (hM : model_total_typed M) (id : Term) (w : Nat)
    (hIdList :
      __eo_is_list (Term.UOp UserOp.bvand) id = Term.Boolean true)
    (hIdEval :
      __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1))
    (hIdCan : BvAndListCanonical M w id)
    (hIdNe : id ≠ Term.Stuck) :
    (t : Term) ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.bvand)
        (__get_ai_norm_rec (Term.UOp UserOp.bvand) id t) =
        Term.Boolean true ∧
      BvAndListCanonical M w
        (__get_ai_norm_rec (Term.UOp UserOp.bvand) id t) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__get_ai_norm_rec (Term.UOp UserOp.bvand) id t)))
        (__smtx_model_eval M (__eo_to_smt t))
  | t, hTy => by
      cases t
      case Apply f x =>
        cases f
        case Apply g y =>
          cases g
          case Stuck =>
            have hBad :
                __smtx_typeof
                  (__eo_to_smt (Term.Apply (Term.Apply Term.Stuck y) x)) =
                  SmtType.None := by
              change __smtx_typeof
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y))
                  (__eo_to_smt x)) = SmtType.None
              exact smtx_typeof_apply_apply_none (__eo_to_smt x) (__eo_to_smt y)
            rw [hBad] at hTy
            cases hTy
          case UOp op =>
            cases op
            case bvand =>
              have hTypes := bvAnd_args_of_bitvec_type y x w hTy
              have hYRec :=
                bvAnd_get_ai_norm_rec_rel_eval M hM id w
                  hIdList hIdEval hIdCan hIdNe y hTypes.1
              have hXRec :=
                bvAnd_get_ai_norm_rec_rel_eval M hM id w
                  hIdList hIdEval hIdCan hIdNe x hTypes.2
              let ry := __get_ai_norm_rec (Term.UOp UserOp.bvand) id y
              let rx := __get_ai_norm_rec (Term.UOp UserOp.bvand) id x
              have hListConcat :
                  __eo_is_list (Term.UOp UserOp.bvand)
                      (__eo_list_concat_rec ry rx) =
                    Term.Boolean true :=
                eo_list_concat_rec_is_list_true_of_lists
                  (Term.UOp UserOp.bvand) ry rx hYRec.1 hXRec.1
              have hListConcatRaw :
                  __eo_is_list (Term.UOp UserOp.bvand)
                      (__eo_list_concat_rec
                        (__get_ai_norm_rec (Term.UOp UserOp.bvand) id y)
                        (__get_ai_norm_rec (Term.UOp UserOp.bvand) id x)) =
                    Term.Boolean true := by
                simpa [ry, rx] using hListConcat
              have hRecEq :
                  __get_ai_norm_rec (Term.UOp UserOp.bvand) id
                      (mkBvAnd y x) =
                    __eo_list_setof_rec (__eo_list_concat_rec ry rx) := by
                dsimp [ry, rx, mkBvAnd]
                simp [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite,
                  native_teq, native_not, SmtEval.native_not,
                  __eo_list_concat, __eo_list_setof, __eo_requires,
                  hYRec.1, hXRec.1, hListConcatRaw]
              have hListRel :=
                bvAnd_list_concat_rec_rel_eval M w ry rx hYRec.1 hXRec.1
                  hYRec.2.1 hXRec.2.1
              have hSetRel :=
                bvAnd_list_setof_rec_rel_eval M w
                  (__eo_list_concat_rec ry rx) hListConcat hListRel.1
              have hRyCan : BvEvalCanonicalWidth M w ry :=
                bvAndListCanonical_eval M w ry hYRec.2.1
              have hRxCan : BvEvalCanonicalWidth M w rx :=
                bvAndListCanonical_eval M w rx hXRec.2.1
              rcases hRyCan with ⟨nry, hryEval, _hryMod⟩
              rcases hRxCan with ⟨nrx, hrxEval, _hrxMod⟩
              have hCongr :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt (mkBvAnd ry rx)))
                    (__smtx_model_eval M (__eo_to_smt (mkBvAnd y x))) :=
                bvAnd_smt_value_rel_congr_eval M ry y rx x w
                  ⟨nry, hryEval⟩ ⟨nrx, hrxEval⟩
                  hYRec.2.2 hXRec.2.2
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M
                      (__eo_to_smt
                        (__eo_list_setof_rec (__eo_list_concat_rec ry rx))))
                    (__smtx_model_eval M (__eo_to_smt (mkBvAnd y x))) :=
                RuleProofs.smt_value_rel_trans
                  (__smtx_model_eval M
                    (__eo_to_smt
                      (__eo_list_setof_rec (__eo_list_concat_rec ry rx))))
                  (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec ry rx)))
                  (__smtx_model_eval M (__eo_to_smt (mkBvAnd y x)))
                  hSetRel.2.2
                  (RuleProofs.smt_value_rel_trans
                    (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec ry rx)))
                    (__smtx_model_eval M (__eo_to_smt (mkBvAnd ry rx)))
                    (__smtx_model_eval M (__eo_to_smt (mkBvAnd y x)))
                    hListRel.2 hCongr)
              rw [hRecEq]
              exact ⟨hSetRel.1, hSetRel.2.1, hRel⟩
            all_goals
              simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite,
                native_teq] using
                bvAnd_l1_norm_rec_rel_eval M hM id w hIdList hIdEval
                  hIdCan hIdNe _ hTy
          all_goals
            simpa [__get_ai_norm_rec, __eo_eq, __eo_ite, native_ite,
              native_teq, __eo_l_1___get_ai_norm_rec] using
              bvAnd_l1_norm_rec_rel_eval M hM id w hIdList hIdEval
                hIdCan hIdNe _ hTy
        all_goals
          simpa [__get_ai_norm_rec, __eo_l_1___get_ai_norm_rec] using
            bvAnd_l1_norm_rec_rel_eval M hM id w hIdList hIdEval
              hIdCan hIdNe _ hTy
      all_goals
        simpa [__get_ai_norm_rec, __eo_l_1___get_ai_norm_rec] using
          bvAnd_l1_norm_rec_rel_eval M hM id w hIdList hIdEval hIdCan hIdNe
            _ hTy

private theorem bvAnd_nil_allOnes_of_is_list_nil_true
    (M : SmtModel) (nil : Term) (w : Nat) (nnil : Int) :
    __eo_is_list_nil (Term.UOp UserOp.bvand) nil = Term.Boolean true ->
    __smtx_model_eval M (__eo_to_smt nil) =
      SmtValue.Binary (native_nat_to_int w) nnil ->
    native_zeq nnil
        (native_mod_total nnil (native_int_pow2 (native_nat_to_int w))) =
      true ->
    BitVec.ofInt w nnil = BitVec.allOnes w := by
  intro hNilTrue hNilEval hNilMod
  cases nil <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_bvand, __eo_to_z,
      __eo_not, __eo_is_eq, native_and, native_not, native_teq,
      native_zeq] at hNilTrue
  case Binary wb nb =>
    have hEvalEq :
        SmtValue.Binary wb nb =
          SmtValue.Binary (native_nat_to_int w) nnil := by
      rw [show __eo_to_smt (Term.Binary wb nb) =
          SmtTerm.Binary wb nb by rfl] at hNilEval
      rw [__smtx_model_eval] at hNilEval
      exact hNilEval
    injection hEvalEq with hWidthEq hPayloadEq
    subst wb
    subst nnil
    have hNotModZero :
        native_mod_total
            (native_binary_not (native_nat_to_int w) nb)
            (native_int_pow2 (native_nat_to_int w)) =
          0 := by
      exact hNilTrue.symm
    have hWidthNonneg :
        native_zleq 0 (native_nat_to_int w) = true := by
      simp [native_zleq, native_nat_to_int]
    have hNbRange :=
      bitvec_payload_range_of_canonical hWidthNonneg hNilMod
    have hNbNonneg : 0 <= nb := hNbRange.1
    have hNbLt : nb < native_int_pow2 (native_nat_to_int w) :=
      hNbRange.2
    have hWidthNonnegInt : 0 <= native_nat_to_int w := by
      simp [native_nat_to_int]
    have hPowPos :
        0 < native_int_pow2 (native_nat_to_int w) :=
      native_int_pow2_pos_of_nonneg hWidthNonnegInt
    have hNotRaw :
        native_binary_not (native_nat_to_int w) nb =
          native_int_pow2 (native_nat_to_int w) - (nb + 1) := by
      simp [native_binary_not, native_zplus, native_zneg,
        Int.sub_eq_add_neg]
    have hNotLower :
        0 <= native_binary_not (native_nat_to_int w) nb := by
      rw [hNotRaw]
      exact Int.sub_nonneg.mpr (Int.add_one_le_of_lt hNbLt)
    have hNotUpper :
        native_binary_not (native_nat_to_int w) nb <
          native_int_pow2 (native_nat_to_int w) := by
      rw [hNotRaw]
      exact Int.sub_lt_self _ (Int.lt_add_one_of_le hNbNonneg)
    have hNotModSelf :
        native_mod_total
            (native_binary_not (native_nat_to_int w) nb)
            (native_int_pow2 (native_nat_to_int w)) =
          native_binary_not (native_nat_to_int w) nb := by
      simpa [native_mod_total] using
        Int.emod_eq_of_lt hNotLower hNotUpper
    have hNotEq :
        native_binary_not (native_nat_to_int w) nb = 0 := by
      rw [← hNotModSelf]
      exact hNotModZero
    have hPayload :
        nb = (2 ^ w : Int) - 1 := by
      rw [hNotRaw] at hNotEq
      rw [native_int_pow2_nat] at hNotEq
      have hEqPow : (2 ^ w : Int) = nb + 1 :=
        Int.sub_eq_zero.mp hNotEq
      symm
      exact (Int.sub_eq_iff_eq_add).mpr hEqPow
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofInt, BitVec.toNat_allOnes]
    rw [hPayload]
    have hLower : 0 <= (2 ^ w : Int) - 1 := by
      have hPowPos : 0 < (2 ^ w : Int) := by
        exact_mod_cast Nat.two_pow_pos w
      omega
    have hUpper : (2 ^ w : Int) - 1 < (2 ^ w : Int) := by
      omega
    change (((2 ^ w : Int) - 1) % (2 ^ w : Int)).toNat = 2 ^ w - 1
    rw [Int.emod_eq_of_lt hLower hUpper]
    have hToNat :
        (((2 ^ w : Int) - 1).toNat : Int) = (2 ^ w : Int) - 1 :=
      Int.toNat_of_nonneg hLower
    have hRhs :
        ((2 ^ w - 1 : Nat) : Int) = (2 ^ w : Int) - 1 :=
      Int.ofNat_sub Nat.one_le_two_pow
    exact Int.ofNat.inj (hToNat.trans hRhs.symm)

private theorem bvAnd_is_list_nil_boolean_of_ne_stuck (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.bvand) t = Term.Boolean b := by
  intro hNe
  cases t <;>
    simp [__eo_is_list_nil, __eo_is_list_nil_bvand, __eo_to_z, __eo_not,
      __eo_is_eq, native_and, native_not, native_teq, native_zeq] at hNe ⊢

private theorem bvAnd_singleton_elim_rel_eval
    (M : SmtModel) (c : Term) (w : Nat) :
    __eo_is_list (Term.UOp UserOp.bvand) c = Term.Boolean true ->
    BvAndListCanonical M w c ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.bvand) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hCan
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.bvand) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.bvand :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.bvand) g head tail hList
          subst g
          have hHeadCan : BvEvalCanonicalWidth M w head := hCan.1
          have hTailCanList : BvAndListCanonical M w tail := hCan.2
          have hTailList :
              __eo_is_list (Term.UOp UserOp.bvand) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.bvand) head tail hList
          have hTailNe : tail ≠ Term.Stuck :=
            bvAnd_is_list_true_ne_stuck hTailList
          rcases bvAnd_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact RuleProofs.smt_value_rel_refl
              (__smtx_model_eval M (__eo_to_smt (mkBvAnd head tail)))
          · have hTailCan : BvEvalCanonicalWidth M w tail :=
              bvAndListCanonical_eval M w tail hTailCanList
            rcases hHeadCan with ⟨nhead, hHeadEval, hHeadMod⟩
            rcases hTailCan with ⟨ntail, hTailEval, hTailMod⟩
            have hTailAllOnes :
                BitVec.ofInt w ntail = BitVec.allOnes w :=
              bvAnd_nil_allOnes_of_is_list_nil_true M tail w ntail
                hNil hTailEval hTailMod
            exact RuleProofs.smt_value_rel_symm _ _
              (bvAnd_smt_value_rel_right_allOnes_eval M head tail w
                nhead ntail hHeadEval hTailEval hHeadMod hTailAllOnes)
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

private theorem native_pow2_minus_one_mod_self_nat (w : Nat) :
    native_mod_total
        (native_int_pow2 (native_nat_to_int w) - 1)
        (native_int_pow2 (native_nat_to_int w)) =
      native_int_pow2 (native_nat_to_int w) - 1 := by
  have hPowPos :
      0 < native_int_pow2 (native_nat_to_int w) :=
    native_int_pow2_pos_of_nonneg (by simp [native_nat_to_int])
  have hLower :
      0 <= native_int_pow2 (native_nat_to_int w) - 1 := by
    exact Int.sub_nonneg.mpr (Int.add_one_le_iff.mpr hPowPos)
  have hUpper :
      native_int_pow2 (native_nat_to_int w) - 1 <
        native_int_pow2 (native_nat_to_int w) := by
    exact Int.sub_lt_self _ (by decide : (0 : Int) < 1)
  simpa [native_mod_total] using Int.emod_eq_of_lt hLower hUpper

private theorem bvAnd_allOnes_is_list_nil (w : Nat) :
    __eo_is_list_nil (Term.UOp UserOp.bvand)
        (Term.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1)) =
      Term.Boolean true := by
  simp [__eo_is_list_nil, __eo_is_list_nil_bvand, __eo_to_z, __eo_not,
    __eo_is_eq, native_binary_not, native_zplus, native_zneg,
    native_mod_total, native_zeq, native_and, native_not, SmtEval.native_not,
    native_teq]

private theorem bvAnd_nil_eq_allOnes_of_type
    {ty : Term} (w : Nat) :
    __eo_to_smt_type ty = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvand) ty ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvand) ty =
      Term.Binary (native_nat_to_int w)
        (native_int_pow2 (native_nat_to_int w) - 1) := by
  intro hTy hNe
  have hTyEq :
      ty =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hTy
  subst ty
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · have hMod :
        native_mod_total
            (native_binary_not (native_nat_to_int w) 0)
            (native_int_pow2 (native_nat_to_int w)) =
          native_int_pow2 (native_nat_to_int w) - 1 := by
      simpa [native_binary_not, native_zplus, native_zneg] using
        native_pow2_minus_one_mod_self_nat w
    have hBoundProp : native_nat_to_int w <= 4294967296 := by
      simpa [native_zleq] using hBound
    have hWidthNonneg : 0 <= native_nat_to_int w := by
      simp [native_nat_to_int]
    have hToBin :
        __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
          Term.Binary (native_nat_to_int w) 0 := by
      simp [__eo_to_bin, __eo_mk_binary, hBound, native_ite, native_zleq,
        hBoundProp, hWidthNonneg, native_mod_total]
    change __eo_not
        (__eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0)) =
      Term.Binary (native_nat_to_int w)
        (native_int_pow2 (native_nat_to_int w) - 1)
    rw [hToBin]
    simp [__eo_not, hMod]
  · have hStuck :
        __eo_nil (Term.UOp UserOp.bvand)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w))) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_nil, __eo_nil_bvand, __eo_to_bin, hBound, hBoundFalse,
        native_ite, native_zleq, __eo_not]
    exact False.elim (hNe hStuck)

private theorem bvZero_to_bin_eq_of_bound (w : Nat) :
    native_zleq (native_nat_to_int w) 4294967296 = true ->
    __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hBound
  have hBoundProp : native_nat_to_int w <= 4294967296 := by
    simpa [native_zleq] using hBound
  have hWidthNonneg : 0 <= native_nat_to_int w := by
    simp [native_nat_to_int]
  simp [__eo_to_bin, __eo_mk_binary, hBound, native_ite, native_zleq,
    hBoundProp, hWidthNonneg, native_mod_total]

private theorem bvOr_zero_is_list_nil (w : Nat) :
    __eo_is_list_nil (Term.UOp UserOp.bvor)
        (Term.Binary (native_nat_to_int w) 0) =
      Term.Boolean true := by
  simp [__eo_is_list_nil, __eo_is_list_nil_bvor, __eo_to_z, __eo_is_eq,
    native_and, native_not, SmtEval.native_not, native_teq, native_zeq]

private theorem bvXor_zero_is_list_nil (w : Nat) :
    __eo_is_list_nil (Term.UOp UserOp.bvxor)
        (Term.Binary (native_nat_to_int w) 0) =
      Term.Boolean true := by
  simp [__eo_is_list_nil, __eo_is_list_nil_bvxor, __eo_to_z, __eo_is_eq,
    native_and, native_not, SmtEval.native_not, native_teq, native_zeq]

private theorem bvOr_nil_eq_zero_of_type
    {ty : Term} (w : Nat) :
    __eo_to_smt_type ty = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvor) ty ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvor) ty =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hTy hNe
  have hTyEq :
      ty =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hTy
  subst ty
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · change
      __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
        Term.Binary (native_nat_to_int w) 0
    exact bvZero_to_bin_eq_of_bound w hBound
  · have hStuck :
        __eo_nil (Term.UOp UserOp.bvor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w))) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_nil, __eo_nil_bvor, __eo_to_bin, hBound, hBoundFalse,
        native_ite, native_zleq]
    exact False.elim (hNe hStuck)

private theorem bvXor_nil_eq_zero_of_type
    {ty : Term} (w : Nat) :
    __eo_to_smt_type ty = SmtType.BitVec w ->
    __eo_nil (Term.UOp UserOp.bvxor) ty ≠ Term.Stuck ->
    __eo_nil (Term.UOp UserOp.bvxor) ty =
      Term.Binary (native_nat_to_int w) 0 := by
  intro hTy hNe
  have hTyEq :
      ty =
        Term.Apply (Term.UOp UserOp.BitVec)
          (Term.Numeral (native_nat_to_int w)) :=
    TranslationProofs.eo_to_smt_type_eq_bitvec hTy
  subst ty
  by_cases hBound : native_zleq (native_nat_to_int w) 4294967296 = true
  · change
      __eo_to_bin (Term.Numeral (native_nat_to_int w)) (Term.Numeral 0) =
        Term.Binary (native_nat_to_int w) 0
    exact bvZero_to_bin_eq_of_bound w hBound
  · have hStuck :
        __eo_nil (Term.UOp UserOp.bvxor)
            (Term.Apply (Term.UOp UserOp.BitVec)
              (Term.Numeral (native_nat_to_int w))) =
          Term.Stuck := by
      have hBoundFalse : ¬ native_nat_to_int w <= 4294967296 := by
        simpa [native_zleq] using hBound
      simp [__eo_nil, __eo_nil_bvxor, __eo_to_bin, hBound, hBoundFalse,
        native_ite, native_zleq]
    exact False.elim (hNe hStuck)

private theorem native_binary_or_right_zero_mod_nat
    (w : Nat) (n : Int) :
    native_mod_total (native_binary_or (native_nat_to_int w) n 0)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_mod_pow2_eq_bitvec_toNat, native_mod_pow2_eq_bitvec_toNat]
  apply congrArg (fun x : BitVec w => (x.toNat : Int))
  cases w with
  | zero =>
      exact Subsingleton.elim _ _
  | succ w =>
      have hNe : ((w : Int) + 1) ≠ 0 := by omega
      have hAndZero :
          (BitVec.ofInt (w + 1) n &&& 0#(w + 1)) = 0#(w + 1) := by
        exact BitVec.and_zero
      have hAndZeroToInt :
          (BitVec.ofInt (w + 1) n &&& 0#(w + 1)).toInt =
            (0#(w + 1)).toInt :=
        congrArg BitVec.toInt hAndZero
      have hCore :
          BitVec.ofInt (w + 1)
              (n + -(BitVec.ofInt (w + 1) n &&& 0#(w + 1)).toInt) =
            BitVec.ofInt (w + 1) n := by
        simpa [hAndZeroToInt]
      simp [native_binary_or, native_piand, native_nat_to_int, native_ite,
        native_zeq, native_zplus, native_zneg, hNe]
      change
        BitVec.ofInt (w + 1)
            (n + -(BitVec.ofInt (w + 1) n &&& 0#(w + 1)).toInt) =
          BitVec.ofInt (w + 1) n
      exact hCore

private theorem native_binary_or_left_zero_mod_nat
    (w : Nat) (n : Int) :
    native_mod_total (native_binary_or (native_nat_to_int w) 0 n)
        (native_int_pow2 (native_nat_to_int w)) =
      native_mod_total n (native_int_pow2 (native_nat_to_int w)) := by
  rw [native_mod_pow2_eq_bitvec_toNat, native_mod_pow2_eq_bitvec_toNat]
  apply congrArg (fun x : BitVec w => (x.toNat : Int))
  cases w with
  | zero =>
      exact Subsingleton.elim _ _
  | succ w =>
      have hNe : ((w : Int) + 1) ≠ 0 := by omega
      have hAndZero :
          (0#(w + 1) &&& BitVec.ofInt (w + 1) n) = 0#(w + 1) := by
        exact BitVec.zero_and
      have hAndZeroToInt :
          (0#(w + 1) &&& BitVec.ofInt (w + 1) n).toInt =
            (0#(w + 1)).toInt :=
        congrArg BitVec.toInt hAndZero
      have hCore :
          BitVec.ofInt (w + 1)
              (n + -(0#(w + 1) &&& BitVec.ofInt (w + 1) n).toInt) =
            BitVec.ofInt (w + 1) n := by
        simpa [hAndZeroToInt]
      simp [native_binary_or, native_piand, native_nat_to_int, native_ite,
        native_zeq, native_zplus, native_zneg, hNe, Int.add_comm]
      change
        BitVec.ofInt (w + 1)
            (n + -(0#(w + 1) &&& BitVec.ofInt (w + 1) n).toInt) =
          BitVec.ofInt (w + 1) n
      exact hCore

private theorem bvOr_smt_value_rel_right_zero_eval
    (M : SmtModel) (x id : Term) (w : Nat) (nx : Int) :
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Binary (native_nat_to_int w) 0 ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) =
      true ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvOr x id)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hxEval hIdEval hxMod
  have hModEq :
      native_mod_total nx (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq :
        nx =
          native_mod_total nx (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hxMod
    exact hEq.symm
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.bvor (__eo_to_smt x) (__eo_to_smt id)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_bvor, hxEval, hIdEval]
  rw [native_binary_or_right_zero_mod_nat w nx, hModEq]
  exact RuleProofs.smtx_model_eval_eq_refl _

private theorem bvOr_smt_value_rel_left_zero_eval
    (M : SmtModel) (id x : Term) (w : Nat) (nx : Int) :
    __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Binary (native_nat_to_int w) 0 ->
    __smtx_model_eval M (__eo_to_smt x) =
        SmtValue.Binary (native_nat_to_int w) nx ->
    native_zeq nx
        (native_mod_total nx (native_int_pow2 (native_nat_to_int w))) =
      true ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvOr id x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hIdEval hxEval hxMod
  have hModEq :
      native_mod_total nx (native_int_pow2 (native_nat_to_int w)) = nx := by
    have hEq :
        nx =
          native_mod_total nx (native_int_pow2 (native_nat_to_int w)) := by
      simpa [native_zeq] using hxMod
    exact hEq.symm
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.bvor (__eo_to_smt id) (__eo_to_smt x)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_bvor, hIdEval, hxEval]
  rw [native_binary_or_left_zero_mod_nat w nx, hModEq]
  exact RuleProofs.smtx_model_eval_eq_refl _

private theorem smt_value_rel_get_ai_norm_bvand
    (M : SmtModel) (hM : model_total_typed M) (y x : Term) :
    RuleProofs.eo_has_smt_translation (mkBvAnd y x) ->
    __get_ai_norm (mkBvAnd y x) ≠ Term.Stuck ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvAnd y x)))
      (__smtx_model_eval M (__eo_to_smt (__get_ai_norm (mkBvAnd y x)))) := by
  intro hTrans hAINe
  let t := mkBvAnd y x
  rcases bvand_args_of_has_smt_translation y x hTrans with
    ⟨w, hyTy, hxTy⟩
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
    dsimp [t, mkBvAnd]
    change __smtx_typeof (SmtTerm.bvand (__eo_to_smt y) (__eo_to_smt x)) =
      SmtType.BitVec w
    rw [__smtx_typeof.eq_38]
    simp [__smtx_typeof_bv_op_2, hyTy, hxTy, native_ite, native_nateq,
      SmtEval.native_nateq]
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t (by
      rw [htTy]
      exact smt_bitvec_ne_none w)
  have hTypeBitVec :
      __eo_to_smt_type (__eo_typeof t) = SmtType.BitVec w := by
    rw [← hTypeMatch, htTy]
  let id := __eo_nil (Term.UOp UserOp.bvand) (__eo_typeof t)
  have hIdNe : id ≠ Term.Stuck := by
    intro hIdStuck
    apply hAINe
    dsimp [t, id, mkBvAnd] at hIdStuck ⊢
    simp [__get_ai_norm, __get_ai_norm_rec, __eo_list_singleton_elim,
      __eo_is_list, __eo_requires, hIdStuck, native_ite, native_teq,
      native_not, SmtEval.native_not]
  have hIdEq :
      id =
        Term.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1) := by
    dsimp [id]
    exact bvAnd_nil_eq_allOnes_of_type w hTypeBitVec hIdNe
  have hIdNil :
      __eo_is_list_nil (Term.UOp UserOp.bvand) id = Term.Boolean true := by
    rw [hIdEq]
    exact bvAnd_allOnes_is_list_nil w
  have hIdList :
      __eo_is_list (Term.UOp UserOp.bvand) id = Term.Boolean true := by
    rw [hIdEq]
    have hNilConcrete := bvAnd_allOnes_is_list_nil w
    simp [__eo_is_list, __eo_get_nil_rec, hNilConcrete,
      __eo_requires, __eo_is_ok, native_ite, native_teq, native_not,
      SmtEval.native_not]
  have hIdEval :
      __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1) := by
    rw [hIdEq]
    rw [show __eo_to_smt
        (Term.Binary (native_nat_to_int w)
          (native_int_pow2 (native_nat_to_int w) - 1)) =
      SmtTerm.Binary (native_nat_to_int w)
        (native_int_pow2 (native_nat_to_int w) - 1) by rfl]
    rw [__smtx_model_eval]
  have hIdCan : BvAndListCanonical M w id := by
    rw [hIdEq]
    exact ⟨native_int_pow2 (native_nat_to_int w) - 1,
      by simpa [hIdEq] using hIdEval, by
      simp [native_zeq, native_pow2_minus_one_mod_self_nat]⟩
  have hRec :=
    bvAnd_get_ai_norm_rec_rel_eval M hM id w hIdList hIdEval hIdCan hIdNe
      t htTy
  have hElim :=
    bvAnd_singleton_elim_rel_eval M
      (__get_ai_norm_rec (Term.UOp UserOp.bvand) id t) w hRec.1 hRec.2.1
  have hNormRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.bvand)
            (__get_ai_norm_rec (Term.UOp UserOp.bvand) id t))))
        (__smtx_model_eval M (__eo_to_smt t)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.bvand)
          (__get_ai_norm_rec (Term.UOp UserOp.bvand) id t))))
      (__smtx_model_eval M
        (__eo_to_smt (__get_ai_norm_rec (Term.UOp UserOp.bvand) id t)))
      (__smtx_model_eval M (__eo_to_smt t))
      hElim hRec.2.2
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_list_singleton_elim (Term.UOp UserOp.bvand)
          (__get_ai_norm_rec (Term.UOp UserOp.bvand)
            (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof t)) t))))
  dsimp [id] at hNormRel
  exact RuleProofs.smt_value_rel_symm
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_list_singleton_elim (Term.UOp UserOp.bvand)
          (__get_ai_norm_rec (Term.UOp UserOp.bvand)
            (__eo_nil (Term.UOp UserOp.bvand) (__eo_typeof t)) t))))
    (__smtx_model_eval M (__eo_to_smt t))
    hNormRel

private theorem native_binary_concat_range_of_canonical
    {w1 w2 n1 n2 : native_Int}
    (hw1 : native_zleq 0 w1 = true)
    (hw2 : native_zleq 0 w2 = true)
    (hn1 :
      native_zeq n1 (native_mod_total n1 (native_int_pow2 w1)) = true)
    (hn2 :
      native_zeq n2 (native_mod_total n2 (native_int_pow2 w2)) = true) :
    0 <= native_binary_concat w1 n1 w2 n2 ∧
      native_binary_concat w1 n1 w2 n2 <
        native_int_pow2 (native_zplus w1 w2) := by
  have hw1i : 0 <= w1 := by
    simpa [native_zleq] using hw1
  have hw2i : 0 <= w2 := by
    simpa [native_zleq] using hw2
  have r1 := bitvec_payload_range_of_canonical hw1 hn1
  have r2 := bitvec_payload_range_of_canonical hw2 hn2
  have hp2pos : 0 < native_int_pow2 w2 :=
    native_int_pow2_pos_of_nonneg hw2i
  have hp2nonneg : 0 <= native_int_pow2 w2 := Int.le_of_lt hp2pos
  constructor
  · simp [native_binary_concat, native_zmult, native_zplus]
    exact Int.add_nonneg (Int.mul_nonneg r1.1 hp2nonneg) r2.1
  · have hltAdd :
        n1 * native_int_pow2 w2 + n2 <
          n1 * native_int_pow2 w2 + native_int_pow2 w2 :=
      Int.add_lt_add_left r2.2 (n1 * native_int_pow2 w2)
    have hSuccLe : n1 + 1 <= native_int_pow2 w1 :=
      Int.add_one_le_of_lt r1.2
    have hMulLe :
        (n1 + 1) * native_int_pow2 w2 <=
          native_int_pow2 w1 * native_int_pow2 w2 :=
      Int.mul_le_mul_of_nonneg_right hSuccLe hp2nonneg
    have hEq :
        n1 * native_int_pow2 w2 + native_int_pow2 w2 =
          (n1 + 1) * native_int_pow2 w2 := by
      simp [Int.add_mul, Int.add_comm]
    have hlt :
        n1 * native_int_pow2 w2 + n2 <
          native_int_pow2 w1 * native_int_pow2 w2 :=
      Int.lt_of_lt_of_le (by simpa [hEq] using hltAdd) hMulLe
    have hpAdd := native_int_pow2_add_of_nonneg hw1i hw2i
    rw [hpAdd]
    simpa [native_binary_concat, native_zmult, native_zplus] using hlt

private theorem native_binary_concat_mod_eq_of_canonical
    {w1 w2 n1 n2 : native_Int}
    (hw1 : native_zleq 0 w1 = true)
    (hw2 : native_zleq 0 w2 = true)
    (hn1 :
      native_zeq n1 (native_mod_total n1 (native_int_pow2 w1)) = true)
    (hn2 :
      native_zeq n2 (native_mod_total n2 (native_int_pow2 w2)) = true) :
    native_mod_total (native_binary_concat w1 n1 w2 n2)
        (native_int_pow2 (native_zplus w1 w2)) =
      native_binary_concat w1 n1 w2 n2 := by
  have hRange := native_binary_concat_range_of_canonical hw1 hw2 hn1 hn2
  simpa [native_mod_total] using Int.emod_eq_of_lt hRange.1 hRange.2

private theorem native_binary_concat_assoc_mod_of_canonical
    (w1 w2 w3 n1 n2 n3 : native_Int)
    (hw1 : native_zleq 0 w1 = true)
    (hw2 : native_zleq 0 w2 = true)
    (hw3 : native_zleq 0 w3 = true)
    (hn1 :
      native_zeq n1 (native_mod_total n1 (native_int_pow2 w1)) = true)
    (hn2 :
      native_zeq n2 (native_mod_total n2 (native_int_pow2 w2)) = true)
    (hn3 :
      native_zeq n3 (native_mod_total n3 (native_int_pow2 w3)) = true) :
    native_mod_total
        (native_binary_concat (native_zplus w1 w2)
          (native_mod_total (native_binary_concat w1 n1 w2 n2)
            (native_int_pow2 (native_zplus w1 w2))) w3 n3)
        (native_int_pow2 (native_zplus (native_zplus w1 w2) w3)) =
      native_mod_total
        (native_binary_concat w1 n1 (native_zplus w2 w3)
          (native_mod_total (native_binary_concat w2 n2 w3 n3)
            (native_int_pow2 (native_zplus w2 w3))))
        (native_int_pow2 (native_zplus w1 (native_zplus w2 w3))) := by
  have h12 := native_binary_concat_mod_eq_of_canonical hw1 hw2 hn1 hn2
  have h23 := native_binary_concat_mod_eq_of_canonical hw2 hw3 hn2 hn3
  rw [h12, h23]
  have hw1i : 0 <= w1 := by
    simpa [native_zleq] using hw1
  have hw2i : 0 <= w2 := by
    simpa [native_zleq] using hw2
  have hw3i : 0 <= w3 := by
    simpa [native_zleq] using hw3
  have hRaw :
      native_binary_concat (native_zplus w1 w2)
          (native_binary_concat w1 n1 w2 n2) w3 n3 =
        native_binary_concat w1 n1 (native_zplus w2 w3)
          (native_binary_concat w2 n2 w3 n3) := by
    have hp23 :
        native_int_pow2 (w2 + w3) =
          native_int_pow2 w2 * native_int_pow2 w3 := by
      simpa [native_zplus] using native_int_pow2_add_of_nonneg hw2i hw3i
    simp [native_binary_concat, native_zplus, native_zmult, hp23,
      Int.add_mul, Int.mul_assoc, Int.add_assoc, Int.add_comm,
      Int.add_left_comm]
  have hPow :
      native_int_pow2 (native_zplus (native_zplus w1 w2) w3) =
        native_int_pow2 (native_zplus w1 (native_zplus w2 w3)) := by
    congr 1
    simp [native_zplus, Int.add_assoc]
  rw [hRaw, hPow]

private theorem bvConcat_smt_value_rel_assoc_of_canonical_eval
    (M : SmtModel) (x y z : Term) :
    BvEvalCanonical M x ->
    BvEvalCanonical M y ->
    BvEvalCanonical M z ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvConcat (mkBvConcat x y) z)))
      (__smtx_model_eval M (__eo_to_smt (mkBvConcat x (mkBvConcat y z)))) := by
  intro hx hy hz
  rcases hx with ⟨wx, nx, hxEval, hxWidth, hxMod⟩
  rcases hy with ⟨wy, ny, hyEval, hyWidth, hyMod⟩
  rcases hz with ⟨wz, nz, hzEval, hzWidth, hzMod⟩
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.concat
          (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y))
          (__eo_to_smt z)))
      (__smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x)
          (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt z)))) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_concat, hxEval, hyEval,
    hzEval]
  have hWidth :
      native_zplus (native_zplus wx wy) wz =
        native_zplus wx (native_zplus wy wz) := by
    simp [native_zplus, Int.add_assoc]
  have hPayload :=
    native_binary_concat_assoc_mod_of_canonical
      wx wy wz nx ny nz hxWidth hyWidth hzWidth hxMod hyMod hzMod
  have hPayload' :
      native_mod_total
          (native_binary_concat (native_zplus wx wy)
            (native_mod_total (native_binary_concat wx nx wy ny)
              (native_int_pow2 (native_zplus wx wy))) wz nz)
          (native_int_pow2 (native_zplus wx (native_zplus wy wz))) =
        native_mod_total
          (native_binary_concat wx nx (native_zplus wy wz)
            (native_mod_total (native_binary_concat wy ny wz nz)
              (native_int_pow2 (native_zplus wy wz))))
          (native_int_pow2 (native_zplus wx (native_zplus wy wz))) := by
    simpa [hWidth] using hPayload
  have hVal :
      SmtValue.Binary (native_zplus (native_zplus wx wy) wz)
          (native_mod_total
            (native_binary_concat (native_zplus wx wy)
              (native_mod_total (native_binary_concat wx nx wy ny)
                (native_int_pow2 (native_zplus wx wy))) wz nz)
            (native_int_pow2 (native_zplus (native_zplus wx wy) wz))) =
        SmtValue.Binary (native_zplus wx (native_zplus wy wz))
          (native_mod_total
            (native_binary_concat wx nx (native_zplus wy wz)
              (native_mod_total (native_binary_concat wy ny wz nz)
                (native_int_pow2 (native_zplus wy wz))))
            (native_int_pow2 (native_zplus wx (native_zplus wy wz)))) :=
    by
      rw [hWidth, hPayload']
  rw [hVal]
  exact RuleProofs.smtx_model_eval_eq_refl _

private theorem bvConcat_eval_canonical_of_canonical_args
    (M : SmtModel) (x y : Term) :
    BvEvalCanonical M x ->
    BvEvalCanonical M y ->
    BvEvalCanonical M (mkBvConcat x y) := by
  intro hx hy
  rcases hx with ⟨wx, nx, hxEval, hxWidth, _hxMod⟩
  rcases hy with ⟨wy, ny, hyEval, hyWidth, _hyMod⟩
  refine ⟨native_zplus wx wy,
    native_mod_total (native_binary_concat wx nx wy ny)
      (native_int_pow2 (native_zplus wx wy)), ?_, ?_, ?_⟩
  · change __smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt y)) =
      SmtValue.Binary (native_zplus wx wy)
        (native_mod_total (native_binary_concat wx nx wy ny)
          (native_int_pow2 (native_zplus wx wy)))
    simp [__smtx_model_eval, __smtx_model_eval_concat, hxEval, hyEval]
  · have hxw : 0 <= wx := by
      simpa [native_zleq] using hxWidth
    have hyw : 0 <= wy := by
      simpa [native_zleq] using hyWidth
    have hsum : 0 <= native_zplus wx wy := by
      simpa [native_zplus] using Int.add_nonneg hxw hyw
    simpa [native_zleq] using hsum
  · exact native_mod_total_canonical (native_zplus wx wy)
      (native_binary_concat wx nx wy ny)

private theorem bvConcatListCanonical_eval
    (M : SmtModel) :
    (t : Term) -> BvConcatListCanonical M t -> BvEvalCanonical M t
  | t, h => by
      cases t with
      | Apply f xs =>
          cases f with
          | Apply g x =>
              cases g with
              | UOp op =>
                  cases op
                  case concat =>
                    exact bvConcat_eval_canonical_of_canonical_args M x xs h.1
                      (bvConcatListCanonical_eval M xs h.2)
                  all_goals
                    simpa [BvConcatListCanonical] using h
              | _ =>
                  simpa [BvConcatListCanonical] using h
          | _ =>
              simpa [BvConcatListCanonical] using h
      | _ =>
          simpa [BvConcatListCanonical] using h

private theorem bvConcat_l1_eq_self_of_eq (id : Term) :
    id ≠ Term.Stuck ->
    __eo_l_1___get_a_norm_rec (Term.UOp UserOp.concat) id id = id := by
  intro hId
  have hEq : __eo_eq id id = Term.Boolean true :=
    eo_eq_eq_true_of_eq_local rfl hId hId
  simp [__eo_l_1___get_a_norm_rec, hEq, __eo_ite, native_ite, native_teq]

private theorem bvConcat_l1_eq_concat_of_ne_id (id t : Term) :
    id ≠ Term.Stuck ->
    t ≠ Term.Stuck ->
    t ≠ id ->
    __eo_l_1___get_a_norm_rec (Term.UOp UserOp.concat) id t =
      mkBvConcat t id := by
  intro hId hT hNe
  have hEq : __eo_eq id t = Term.Boolean false :=
    eo_eq_eq_false_of_ne_local
      (x := id) (y := t) (by
        intro h
        exact hNe h.symm) hId hT
  rw [show __eo_l_1___get_a_norm_rec (Term.UOp UserOp.concat) id t =
      __eo_ite (__eo_eq id t) id
        (__eo_l_2___get_a_norm_rec (Term.UOp UserOp.concat) id t) by
    cases id <;> cases t <;>
      simp [__eo_l_1___get_a_norm_rec] at hId hT ⊢]
  rw [hEq]
  cases id <;> cases t <;>
    simp [__eo_l_2___get_a_norm_rec, __eo_ite, native_ite, native_teq] at hId hT ⊢ <;>
    contradiction

private theorem eo_list_concat_rec_bvConcat_nil_eq_of_nil_true
    (nil z : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.concat) nil = Term.Boolean true) :
    __eo_list_concat_rec nil z = z := by
  cases nil <;>
    simp [__eo_is_list_nil, __eo_list_concat_rec] at hNil ⊢
  case Binary w n =>
    cases z <;> rfl

private theorem bvConcat_nil_eval_binary_zero_of_is_list_nil_true
    (M : SmtModel) (nil : Term)
    (hNil :
      __eo_is_list_nil (Term.UOp UserOp.concat) nil = Term.Boolean true) :
    __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Binary 0 0 := by
  cases nil
  all_goals try simp [__eo_is_list_nil] at hNil
  all_goals try contradiction
  case Binary w n =>
    split at hNil <;> simp_all
    rw [show __eo_to_smt (Term.Binary 0 0) = SmtTerm.Binary 0 0 by rfl]
    rw [__smtx_model_eval]

private theorem bvConcat_is_list_nil_binary_is_boolean
    (w n : native_Int) :
    ∃ b,
      __eo_is_list_nil (Term.UOp UserOp.concat) (Term.Binary w n) =
        Term.Boolean b := by
  by_cases h : w = 0 ∧ n = 0
  · rcases h with ⟨rfl, rfl⟩
    exact ⟨true, by simp [__eo_is_list_nil]⟩
  · have hTerm : Term.Binary w n ≠ Term.Binary 0 0 := by
      intro hEq
      cases hEq
      exact h ⟨rfl, rfl⟩
    exact ⟨false, by simp [__eo_is_list_nil, hTerm]⟩

private theorem bvConcat_is_list_nil_boolean_of_ne_stuck
    (t : Term) :
    t ≠ Term.Stuck ->
    ∃ b, __eo_is_list_nil (Term.UOp UserOp.concat) t = Term.Boolean b := by
  intro hNe
  cases t
  case Stuck =>
    exact False.elim (hNe rfl)
  case Binary w n =>
    exact bvConcat_is_list_nil_binary_is_boolean w n
  all_goals
    exact ⟨false, by simp [__eo_is_list_nil]⟩

private theorem bvConcat_smt_value_rel_left_empty_eval
    (M : SmtModel) (nil x : Term) :
    __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Binary 0 0 ->
    BvEvalCanonical M x ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvConcat nil x)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hNilEval hxCan
  rcases hxCan with ⟨wx, nx, hxEval, _hxWidth, hxMod⟩
  have hModEq :
      native_mod_total nx (native_int_pow2 wx) = nx := by
    have hEq :
        nx = native_mod_total nx (native_int_pow2 wx) := by
      simpa [SmtEval.native_zeq] using hxMod
    exact hEq.symm
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt nil) (__eo_to_smt x)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_concat, hNilEval, hxEval]
  simp [SmtEval.native_binary_concat, SmtEval.native_zplus,
    SmtEval.native_zmult, hModEq, __smtx_model_eval_eq, native_veq]

private theorem bvConcat_smt_value_rel_right_empty_canonical_eval
    (M : SmtModel) (x nil : Term) :
    BvEvalCanonical M x ->
    __smtx_model_eval M (__eo_to_smt nil) = SmtValue.Binary 0 0 ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvConcat x nil)))
      (__smtx_model_eval M (__eo_to_smt x)) := by
  intro hxCan hNilEval
  rcases hxCan with ⟨wx, nx, hxEval, _hxWidth, hxMod⟩
  have hModEq :
      native_mod_total nx (native_int_pow2 wx) = nx := by
    have hEq :
        nx = native_mod_total nx (native_int_pow2 wx) := by
      simpa [SmtEval.native_zeq] using hxMod
    exact hEq.symm
  have hPow0 : native_int_pow2 0 = 1 := by
    native_decide
  rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
  change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.concat (__eo_to_smt x) (__eo_to_smt nil)))
      (__smtx_model_eval M (__eo_to_smt x)) =
    SmtValue.Boolean true
  simp only [__smtx_model_eval, __smtx_model_eval_concat, hxEval, hNilEval]
  simp only [SmtEval.native_binary_concat, SmtEval.native_zplus,
    SmtEval.native_zmult, hPow0, Int.add_zero, Int.mul_one]
  rw [hModEq]
  simp [__smtx_model_eval_eq, native_veq]

private theorem bvConcat_l1_norm_rec_rel_eval
    (M : SmtModel) (hM : model_total_typed M) (id : Term)
    (hIdList :
      __eo_is_list (Term.UOp UserOp.concat) id = Term.Boolean true)
    (hIdEval :
      __smtx_model_eval M (__eo_to_smt id) = SmtValue.Binary 0 0)
    (hIdCan : BvConcatListCanonical M id)
    (hIdNe : id ≠ Term.Stuck)
    (t : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.concat)
        (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.concat) id t) =
        Term.Boolean true ∧
      BvConcatListCanonical M
        (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.concat) id t) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.concat) id t)))
        (__smtx_model_eval M (__eo_to_smt t)) := by
  intro hTy
  have hTNe : t ≠ Term.Stuck := term_ne_stuck_of_smt_bitvec_type hTy
  by_cases hEq : t = id
  · subst t
    rw [bvConcat_l1_eq_self_of_eq id hIdNe]
    exact ⟨hIdList, hIdCan, RuleProofs.smt_value_rel_refl _⟩
  · rw [bvConcat_l1_eq_concat_of_ne_id id t hIdNe hTNe hEq]
    exact ⟨
      eo_is_list_cons_self_true_of_tail_list
        (Term.UOp UserOp.concat) t id (by decide) hIdList,
      ⟨bvEvalCanonical_of_smt_type_bitvec_any M hM t w hTy, hIdCan⟩,
      bvConcat_smt_value_rel_right_empty_eval M hM t id w hTy hIdEval⟩

private theorem bvConcat_args_of_bitvec_type
    (y x : Term) (w : native_Nat) :
    __smtx_typeof (__eo_to_smt (mkBvConcat y x)) = SmtType.BitVec w ->
    ∃ wy wx : native_Nat,
      __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ∧
        __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx := by
  intro hTy
  have hNN : term_has_non_none_type
      (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) := by
    unfold term_has_non_none_type
    change __smtx_typeof (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) ≠
      SmtType.None
    rw [show
      __smtx_typeof (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) =
        SmtType.BitVec w by
      simpa [mkBvConcat] using hTy]
    exact smt_bitvec_ne_none w
  exact bv_concat_args_of_non_none hNN

private theorem bvConcat_typeof_concat_of_bitvec
    (y x : Term) (wy wx : native_Nat) :
    __smtx_typeof (__eo_to_smt y) = SmtType.BitVec wy ->
    __smtx_typeof (__eo_to_smt x) = SmtType.BitVec wx ->
    __smtx_typeof (__eo_to_smt (mkBvConcat y x)) =
      SmtType.BitVec
        (native_int_to_nat
          (native_zplus (native_nat_to_int wy) (native_nat_to_int wx))) := by
  intro hyTy hxTy
  change __smtx_typeof (SmtTerm.concat (__eo_to_smt y) (__eo_to_smt x)) =
    SmtType.BitVec
      (native_int_to_nat
        (native_zplus (native_nat_to_int wy) (native_nat_to_int wx)))
  rw [typeof_concat_eq]
  simp [__smtx_typeof_concat, hyTy, hxTy]

private theorem bvConcat_list_concat_rec_rel_eval
    (M : SmtModel) :
    (a z : Term) ->
    __eo_is_list (Term.UOp UserOp.concat) a = Term.Boolean true ->
    __eo_is_list (Term.UOp UserOp.concat) z = Term.Boolean true ->
    BvConcatListCanonical M a ->
    BvConcatListCanonical M z ->
    BvConcatListCanonical M (__eo_list_concat_rec a z) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec a z)))
        (__smtx_model_eval M (__eo_to_smt (mkBvConcat a z)))
  | a, z, hAList, hZList, hACan, hZCan => by
      induction a, z using __eo_list_concat_rec.induct with
      | case1 z =>
          cases (Term.UOp UserOp.concat) <;> simp [__eo_is_list] at hAList
      | case2 a hA =>
          cases (Term.UOp UserOp.concat) <;> simp [__eo_is_list] at hZList
      | case3 g x y z hZ ih =>
          have hg : g = Term.UOp UserOp.concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.concat) g x y hAList
          subst g
          have hYList :
              __eo_is_list (Term.UOp UserOp.concat) y =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.concat) x y hAList
          have hTailNe :
              __eo_list_concat_rec y z ≠ Term.Stuck :=
            eo_list_concat_rec_ne_stuck_of_list
              (Term.UOp UserOp.concat) y z hYList hZ
          have hXCan : BvEvalCanonical M x := hACan.1
          have hYCanList : BvConcatListCanonical M y := hACan.2
          have hYCan : BvEvalCanonical M y :=
            bvConcatListCanonical_eval M y hYCanList
          have hZCanEval : BvEvalCanonical M z :=
            bvConcatListCanonical_eval M z hZCan
          have hIH := ih hYList hZList hYCanList hZCan
          rw [eo_list_concat_rec_cons_eq_of_tail_ne_stuck
            (Term.UOp UserOp.concat) x y z hTailNe]
          have hTailCan : BvEvalCanonical M (__eo_list_concat_rec y z) :=
            bvConcatListCanonical_eval M (__eo_list_concat_rec y z) hIH.1
          have hYZCan : BvEvalCanonical M (mkBvConcat y z) :=
            bvConcat_eval_canonical_of_canonical_args M y z hYCan hZCanEval
          rcases hXCan with ⟨wx, nx, hxEval, hxWidth, hxMod⟩
          rcases hTailCan with ⟨wyz, nyz, hTailEval, hTailWidth, hTailMod⟩
          have hCongr :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvConcat x (__eo_list_concat_rec y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvConcat x (mkBvConcat y z)))) :=
            bvConcat_smt_value_rel_congr_eval M x x
              (__eo_list_concat_rec y z) (mkBvConcat y z) wx wyz
              ⟨nx, hxEval⟩ ⟨nyz, hTailEval⟩
              (RuleProofs.smt_value_rel_refl
                (__smtx_model_eval M (__eo_to_smt x)))
              hIH.2
          have hAssoc :
              RuleProofs.smt_value_rel
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvConcat x (mkBvConcat y z))))
                (__smtx_model_eval M
                  (__eo_to_smt (mkBvConcat (mkBvConcat x y) z))) :=
            RuleProofs.smt_value_rel_symm _ _
              (bvConcat_smt_value_rel_assoc_of_canonical_eval
                M x y z
                ⟨wx, nx, hxEval, hxWidth, hxMod⟩ hYCan hZCanEval)
          exact ⟨
            ⟨⟨wx, nx, hxEval, hxWidth, hxMod⟩, hIH.1⟩,
            RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M
                (__eo_to_smt (mkBvConcat x (__eo_list_concat_rec y z))))
              (__smtx_model_eval M
                (__eo_to_smt (mkBvConcat x (mkBvConcat y z))))
              (__smtx_model_eval M
                (__eo_to_smt (mkBvConcat (mkBvConcat x y) z)))
              hCongr hAssoc⟩
      | case4 nil z hNil hZ hNot =>
          have hNilTrue :
              __eo_is_list_nil (Term.UOp UserOp.concat) nil =
                Term.Boolean true := by
            have hGet :=
              eo_get_nil_rec_ne_stuck_of_is_list_true
                (Term.UOp UserOp.concat) nil hAList
            have hReq :
                __eo_requires
                    (__eo_is_list_nil (Term.UOp UserOp.concat) nil)
                    (Term.Boolean true) nil ≠ Term.Stuck := by
              simpa [__eo_get_nil_rec] using hGet
            exact eo_requires_eq_of_ne_stuck
              (__eo_is_list_nil (Term.UOp UserOp.concat) nil)
              (Term.Boolean true) nil hReq
          rw [eo_list_concat_rec_bvConcat_nil_eq_of_nil_true nil z hNilTrue]
          have hNilEval :=
            bvConcat_nil_eval_binary_zero_of_is_list_nil_true M nil hNilTrue
          exact ⟨hZCan,
            RuleProofs.smt_value_rel_symm _ _
              (bvConcat_smt_value_rel_left_empty_eval M nil z hNilEval
                (bvConcatListCanonical_eval M z hZCan))⟩

private theorem bvConcat_get_a_norm_rec_rel_eval
    (M : SmtModel) (hM : model_total_typed M) (id : Term)
    (hIdList :
      __eo_is_list (Term.UOp UserOp.concat) id = Term.Boolean true)
    (hIdEval :
      __smtx_model_eval M (__eo_to_smt id) = SmtValue.Binary 0 0)
    (hIdCan : BvConcatListCanonical M id)
    (hIdNe : id ≠ Term.Stuck) :
    (t : Term) -> (w : native_Nat) ->
    __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w ->
    __eo_is_list (Term.UOp UserOp.concat)
        (__get_a_norm_rec (Term.UOp UserOp.concat) id t) =
        Term.Boolean true ∧
      BvConcatListCanonical M
        (__get_a_norm_rec (Term.UOp UserOp.concat) id t) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__get_a_norm_rec (Term.UOp UserOp.concat) id t)))
        (__smtx_model_eval M (__eo_to_smt t))
  | t, w, hTy => by
      cases t
      case Apply f x =>
        cases f
        case Apply g y =>
          cases g
          case Stuck =>
            have hBad :
                __smtx_typeof
                  (__eo_to_smt (Term.Apply (Term.Apply Term.Stuck y) x)) =
                  SmtType.None := by
              change __smtx_typeof
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y))
                  (__eo_to_smt x)) = SmtType.None
              exact smtx_typeof_apply_apply_none (__eo_to_smt x) (__eo_to_smt y)
            rw [hBad] at hTy
            cases hTy
          case UOp op =>
            cases op
            case concat =>
              rcases bvConcat_args_of_bitvec_type y x w hTy with
                ⟨wy, wx, hyTy, hxTy⟩
              have hYRec :=
                bvConcat_get_a_norm_rec_rel_eval M hM id hIdList hIdEval
                  hIdCan hIdNe y wy hyTy
              have hXRec :=
                bvConcat_get_a_norm_rec_rel_eval M hM id hIdList hIdEval
                  hIdCan hIdNe x wx hxTy
              let ry := __get_a_norm_rec (Term.UOp UserOp.concat) id y
              let rx := __get_a_norm_rec (Term.UOp UserOp.concat) id x
              have hRecEq :
                  __get_a_norm_rec (Term.UOp UserOp.concat) id
                      (mkBvConcat y x) =
                    __eo_list_concat_rec ry rx := by
                dsimp [ry, rx, mkBvConcat]
                simp [__get_a_norm_rec, __eo_eq, __eo_ite, native_ite,
                  native_teq, native_not, SmtEval.native_not,
                  __eo_list_concat, __eo_requires, hYRec.1, hXRec.1]
              have hListConcat :
                  __eo_is_list (Term.UOp UserOp.concat)
                      (__eo_list_concat_rec ry rx) =
                    Term.Boolean true :=
                eo_list_concat_rec_is_list_true_of_lists
                  (Term.UOp UserOp.concat) ry rx hYRec.1 hXRec.1
              have hListRel :=
                bvConcat_list_concat_rec_rel_eval M ry rx hYRec.1 hXRec.1
                  hYRec.2.1 hXRec.2.1
              have hRyCan : BvEvalCanonical M ry :=
                bvConcatListCanonical_eval M ry hYRec.2.1
              have hRxCan : BvEvalCanonical M rx :=
                bvConcatListCanonical_eval M rx hXRec.2.1
              rcases hRyCan with ⟨wry, nry, hryEval, _hryWidth, _hryMod⟩
              rcases hRxCan with ⟨wrx, nrx, hrxEval, _hrxWidth, _hrxMod⟩
              have hCongr :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt (mkBvConcat ry rx)))
                    (__smtx_model_eval M (__eo_to_smt (mkBvConcat y x))) :=
                bvConcat_smt_value_rel_congr_eval M ry y rx x wry wrx
                  ⟨nry, hryEval⟩ ⟨nrx, hrxEval⟩
                  hYRec.2.2 hXRec.2.2
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec ry rx)))
                    (__smtx_model_eval M (__eo_to_smt (mkBvConcat y x))) :=
                RuleProofs.smt_value_rel_trans
                  (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec ry rx)))
                  (__smtx_model_eval M (__eo_to_smt (mkBvConcat ry rx)))
                  (__smtx_model_eval M (__eo_to_smt (mkBvConcat y x)))
                  hListRel.2 hCongr
              rw [hRecEq]
              exact ⟨hListConcat, hListRel.1, hRel⟩
            all_goals
              simpa [__get_a_norm_rec, __eo_eq, __eo_ite, native_ite,
                native_teq] using
                bvConcat_l1_norm_rec_rel_eval M hM id hIdList hIdEval
                  hIdCan hIdNe _ w hTy
          all_goals
            simpa [__get_a_norm_rec, __eo_eq, __eo_ite, native_ite,
              native_teq, __eo_l_1___get_a_norm_rec] using
              bvConcat_l1_norm_rec_rel_eval M hM id hIdList hIdEval
                hIdCan hIdNe _ w hTy
        all_goals
          simpa [__get_a_norm_rec, __eo_l_1___get_a_norm_rec] using
            bvConcat_l1_norm_rec_rel_eval M hM id hIdList hIdEval
              hIdCan hIdNe _ w hTy
      all_goals
        simpa [__get_a_norm_rec, __eo_l_1___get_a_norm_rec] using
          bvConcat_l1_norm_rec_rel_eval M hM id hIdList hIdEval hIdCan hIdNe
            _ w hTy

private theorem bvConcat_singleton_elim_rel_eval
    (M : SmtModel) (c : Term) :
    __eo_is_list (Term.UOp UserOp.concat) c = Term.Boolean true ->
    BvConcatListCanonical M c ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hCan
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.concat :=
            eo_is_list_cons_head_eq_of_true
              (Term.UOp UserOp.concat) g head tail hList
          subst g
          have hHeadCan : BvEvalCanonical M head := hCan.1
          have hTailCanList : BvConcatListCanonical M tail := hCan.2
          have hTailList :
              __eo_is_list (Term.UOp UserOp.concat) tail =
                Term.Boolean true :=
            eo_is_list_tail_true_of_cons_self
              (Term.UOp UserOp.concat) head tail hList
          have hTailNe : tail ≠ Term.Stuck := by
            intro h
            subst tail
            simp [__eo_is_list] at hTailList
          rcases bvConcat_is_list_nil_boolean_of_ne_stuck tail hTailNe with
            ⟨b, hNil⟩
          simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
            native_teq]
          cases b
          · exact RuleProofs.smt_value_rel_refl
              (__smtx_model_eval M (__eo_to_smt (mkBvConcat head tail)))
          · exact RuleProofs.smt_value_rel_symm _ _
              (bvConcat_smt_value_rel_right_empty_canonical_eval M
                head tail hHeadCan
                (bvConcat_nil_eval_binary_zero_of_is_list_nil_true M tail hNil))
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_get_a_norm_concat
    (M : SmtModel) (hM : model_total_typed M) (y x : Term) :
    RuleProofs.eo_has_smt_translation (mkBvConcat y x) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkBvConcat y x)))
      (__smtx_model_eval M (__eo_to_smt (__get_a_norm (mkBvConcat y x)))) := by
  intro hTrans
  let t := mkBvConcat y x
  rcases bvConcat_args_of_has_smt_translation y x hTrans with
    ⟨wy, wx, hyTy, hxTy⟩
  let w :=
    native_int_to_nat
      (native_zplus (native_nat_to_int wy) (native_nat_to_int wx))
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.BitVec w := by
    dsimp [t, w]
    exact bvConcat_typeof_concat_of_bitvec y x wy wx hyTy hxTy
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t (by
      rw [htTy]
      exact smt_bitvec_ne_none w)
  have hTypeBitVec : __eo_to_smt_type (__eo_typeof t) = SmtType.BitVec w := by
    rw [← hTypeMatch, htTy]
  have hTypeNe : __eo_typeof t ≠ Term.Stuck := by
    intro h
    rw [h] at hTypeBitVec
    simp [__eo_to_smt_type] at hTypeBitVec
  let id := __eo_nil (Term.UOp UserOp.concat) (__eo_typeof t)
  have hIdEq : id = Term.Binary 0 0 := by
    dsimp [id]
    cases hTy : __eo_typeof t
    case Stuck =>
      exact False.elim (hTypeNe hTy)
    all_goals rfl
  have hIdList :
      __eo_is_list (Term.UOp UserOp.concat) id = Term.Boolean true := by
    rw [hIdEq]
    simp [__eo_is_list, __eo_get_nil_rec, __eo_is_list_nil, __eo_requires,
      __eo_is_ok, native_teq, native_ite, native_not, SmtEval.native_not]
  have hIdEval :
      __smtx_model_eval M (__eo_to_smt id) = SmtValue.Binary 0 0 := by
    rw [hIdEq]
    rw [show __eo_to_smt (Term.Binary 0 0) = SmtTerm.Binary 0 0 by rfl]
    rw [__smtx_model_eval]
  have hIdCan : BvConcatListCanonical M id := by
    rw [hIdEq]
    exact ⟨0, 0, by simpa [hIdEq] using hIdEval,
      by native_decide, by native_decide⟩
  have hIdNe : id ≠ Term.Stuck := by
    rw [hIdEq]
    intro h
    cases h
  have hRec :=
    bvConcat_get_a_norm_rec_rel_eval M hM id hIdList hIdEval hIdCan hIdNe
      t w htTy
  have hElim :=
    bvConcat_singleton_elim_rel_eval M
      (__get_a_norm_rec (Term.UOp UserOp.concat) id t) hRec.1 hRec.2.1
  have hNormRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.concat)
            (__get_a_norm_rec (Term.UOp UserOp.concat) id t))))
        (__smtx_model_eval M (__eo_to_smt t)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.concat)
          (__get_a_norm_rec (Term.UOp UserOp.concat) id t))))
      (__smtx_model_eval M
        (__eo_to_smt (__get_a_norm_rec (Term.UOp UserOp.concat) id t)))
      (__smtx_model_eval M (__eo_to_smt t))
      hElim hRec.2.2
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_list_singleton_elim (Term.UOp UserOp.concat)
          (__get_a_norm_rec (Term.UOp UserOp.concat)
            (__eo_nil (Term.UOp UserOp.concat) (__eo_typeof t)) t))))
  dsimp [id] at hNormRel
  exact RuleProofs.smt_value_rel_symm
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_list_singleton_elim (Term.UOp UserOp.concat)
          (__get_a_norm_rec (Term.UOp UserOp.concat)
            (__eo_nil (Term.UOp UserOp.concat) (__eo_typeof t)) t))))
    (__smtx_model_eval M (__eo_to_smt t))
    hNormRel

private theorem native_re_mk_union_self (r : native_RegLan) :
    native_re_mk_union r r = r := by
  cases r <;> simp [native_re_mk_union]

private theorem native_re_mk_inter_self (r : native_RegLan) :
    native_re_mk_inter r r = r := by
  cases r <;> simp [native_re_mk_inter]

private theorem native_re_nullable_mk_union (r s : native_RegLan) :
    native_re_nullable (native_re_mk_union r s) =
      (native_re_nullable r || native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_union, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem native_re_nullable_mk_inter (r s : native_RegLan) :
    native_re_nullable (native_re_mk_inter r s) =
      (native_re_nullable r && native_re_nullable s) := by
  cases r <;> cases s <;>
    simp [native_re_mk_inter, native_re_nullable]
  all_goals
    split <;> simp_all [native_re_nullable]

private theorem term_ne_stuck_of_strConcat_is_list_true {t : Term} :
    __eo_is_list (Term.UOp UserOp.str_concat) t = Term.Boolean true ->
    t ≠ Term.Stuck := by
  intro hList hStuck
  subst t
  simp [__eo_is_list] at hList

private theorem strConcat_l1_norm_rec_rel_eval
    (M : SmtModel) (hM : model_total_typed M) (id : Term) (T : SmtType)
    (hIdList :
      __eo_is_list (Term.UOp UserOp.str_concat) id = Term.Boolean true)
    (hIdEval :
      __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Seq (SmtSeq.empty T))
    (hIdNe : id ≠ Term.Stuck)
    (t : Term) :
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t) =
        Term.Boolean true ∧
      (∃ s,
        __smtx_model_eval M
          (__eo_to_smt
            (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t)) =
          SmtValue.Seq s) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt
            (__eo_l_1___get_a_norm_rec (Term.UOp UserOp.str_concat) id t)))
        (__smtx_model_eval M (__eo_to_smt t)) := by
  intro hTy
  have hL1 :=
    strConcat_l1_rel_eval_empty M hM id T hIdList hIdEval hIdNe t hTy
  have htSeq := smt_eval_seq_of_smt_type_seq M hM (__eo_to_smt t) T hTy
  exact ⟨hL1.1, smt_value_rel_eval_seq_left hL1.2 htSeq, hL1.2⟩

private theorem strConcat_get_a_norm_rec_rel_eval
    (M : SmtModel) (hM : model_total_typed M) (id : Term) (T : SmtType)
    (hIdList :
      __eo_is_list (Term.UOp UserOp.str_concat) id = Term.Boolean true)
    (hIdEval :
      __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Seq (SmtSeq.empty T))
    (hIdNe : id ≠ Term.Stuck) :
    (t : Term) ->
    __smtx_typeof (__eo_to_smt t) = SmtType.Seq T ->
    __eo_is_list (Term.UOp UserOp.str_concat)
        (__get_a_norm_rec (Term.UOp UserOp.str_concat) id t) =
        Term.Boolean true ∧
      (∃ s,
        __smtx_model_eval M
          (__eo_to_smt (__get_a_norm_rec (Term.UOp UserOp.str_concat) id t)) =
          SmtValue.Seq s) ∧
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__get_a_norm_rec (Term.UOp UserOp.str_concat) id t)))
        (__smtx_model_eval M (__eo_to_smt t))
  | t, hTy => by
      cases t
      case Apply f x =>
        cases f
        case Apply g y =>
          cases g
          case Stuck =>
            have hBad :
                __smtx_typeof
                  (__eo_to_smt (Term.Apply (Term.Apply Term.Stuck y) x)) =
                  SmtType.None := by
              change __smtx_typeof
                (SmtTerm.Apply (SmtTerm.Apply SmtTerm.None (__eo_to_smt y))
                  (__eo_to_smt x)) = SmtType.None
              exact smtx_typeof_apply_apply_none (__eo_to_smt x) (__eo_to_smt y)
            rw [hBad] at hTy
            cases hTy
          case UOp op =>
            cases op
            case str_concat =>
              have hTypes := strConcat_args_of_seq_type y x T hTy
              have hYRec :=
                strConcat_get_a_norm_rec_rel_eval M hM id T
                  hIdList hIdEval hIdNe y hTypes.1
              have hXRec :=
                strConcat_get_a_norm_rec_rel_eval M hM id T
                  hIdList hIdEval hIdNe x hTypes.2
              let ry := __get_a_norm_rec (Term.UOp UserOp.str_concat) id y
              let rx := __get_a_norm_rec (Term.UOp UserOp.str_concat) id x
              have hRecEq :
                  __get_a_norm_rec (Term.UOp UserOp.str_concat) id
                      (mkStrConcat y x) =
                    __eo_list_concat_rec ry rx := by
                dsimp [ry, rx, mkStrConcat]
                simp [__get_a_norm_rec, __eo_eq, __eo_ite, native_ite,
                  native_teq, native_not, SmtEval.native_not,
                  __eo_list_concat, __eo_requires, hYRec.1, hXRec.1]
              have hListConcat :
                  __eo_is_list (Term.UOp UserOp.str_concat)
                      (__eo_list_concat_rec ry rx) =
                    Term.Boolean true :=
                strConcat_is_list_concat_rec_of_lists ry rx hYRec.1 hXRec.1
              have hListRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec ry rx)))
                    (__smtx_model_eval M (__eo_to_smt (mkStrConcat ry rx))) :=
                strConcat_smt_value_rel_list_concat_rec_eval M ry rx
                  hYRec.1 hYRec.2.1 hXRec.2.1
              have hConcatRecSeq :
                  ∃ s,
                    __smtx_model_eval M (__eo_to_smt (mkStrConcat ry rx)) =
                      SmtValue.Seq s :=
                strConcat_eval_concat_seq_of_args_eval_seq M ry rx
                  hYRec.2.1 hXRec.2.1
              have hListSeq :=
                smt_value_rel_eval_seq_left hListRel hConcatRecSeq
              rcases smt_eval_seq_of_smt_type_seq M hM (__eo_to_smt y) T
                  hTypes.1 with
                ⟨sy, hyEval⟩
              rcases smt_eval_seq_of_smt_type_seq M hM (__eo_to_smt x) T
                  hTypes.2 with
                ⟨sx, hxEval⟩
              have hCongr :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt (mkStrConcat ry rx)))
                    (__smtx_model_eval M (__eo_to_smt (mkStrConcat y x))) :=
                strConcat_smt_value_rel_congr_eval M ry y rx x sy sx
                  hyEval hxEval hYRec.2.2 hXRec.2.2
              have hRel :
                  RuleProofs.smt_value_rel
                    (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec ry rx)))
                    (__smtx_model_eval M (__eo_to_smt (mkStrConcat y x))) :=
                RuleProofs.smt_value_rel_trans
                  (__smtx_model_eval M (__eo_to_smt (__eo_list_concat_rec ry rx)))
                  (__smtx_model_eval M (__eo_to_smt (mkStrConcat ry rx)))
                  (__smtx_model_eval M (__eo_to_smt (mkStrConcat y x)))
                  hListRel hCongr
              rw [hRecEq]
              exact ⟨hListConcat, hListSeq, hRel⟩
            all_goals
              simpa [__get_a_norm_rec, __eo_eq, __eo_ite, native_ite,
                native_teq] using
                strConcat_l1_norm_rec_rel_eval M hM id T hIdList hIdEval
                  hIdNe _ hTy
          all_goals
            simpa [__get_a_norm_rec, __eo_eq, __eo_ite, native_ite,
              native_teq, __eo_l_1___get_a_norm_rec] using
              strConcat_l1_norm_rec_rel_eval M hM id T hIdList hIdEval
                hIdNe _ hTy
        all_goals
          simpa [__get_a_norm_rec, __eo_l_1___get_a_norm_rec] using
            strConcat_l1_norm_rec_rel_eval M hM id T hIdList hIdEval
              hIdNe _ hTy
      all_goals
        simpa [__get_a_norm_rec, __eo_l_1___get_a_norm_rec] using
          strConcat_l1_norm_rec_rel_eval M hM id T hIdList hIdEval hIdNe
            _ hTy

private theorem strConcat_singleton_elim_rel_eval
    (M : SmtModel) (c : Term) :
    __eo_is_list (Term.UOp UserOp.str_concat) c = Term.Boolean true ->
    (∃ s, __smtx_model_eval M (__eo_to_smt c) = SmtValue.Seq s) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.str_concat) c)))
      (__smtx_model_eval M (__eo_to_smt c)) := by
  intro hList hcSeq
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_requires (__eo_is_list (Term.UOp UserOp.str_concat) c)
          (Term.Boolean true) (__eo_list_singleton_elim_2 c))))
    (__smtx_model_eval M (__eo_to_smt c))
  rw [hList]
  simp [__eo_requires, native_ite, native_teq, native_not, SmtEval.native_not]
  cases c with
  | Apply f tail =>
      cases f with
      | Apply g head =>
          have hg :
              g = Term.UOp UserOp.str_concat :=
            strConcat_is_list_cons_head_eq_of_true g head tail hList
          subst g
          rcases strConcat_args_eval_seq_of_concat_eval_seq M head tail hcSeq with
            ⟨hHeadSeq, hTailSeq⟩
          cases hNil : __eo_is_list_nil (Term.UOp UserOp.str_concat) tail
          all_goals
            simp [__eo_list_singleton_elim_2, hNil, __eo_ite, native_ite,
              native_teq]
          case Boolean b =>
            cases b
            · exact RuleProofs.smt_value_rel_refl
                (__smtx_model_eval M (__eo_to_smt (mkStrConcat head tail)))
            · exact RuleProofs.smt_value_rel_symm
                (__smtx_model_eval M (__eo_to_smt (mkStrConcat head tail)))
                (__smtx_model_eval M (__eo_to_smt head))
                (strConcat_smt_value_rel_list_nil_right_empty_eval M
                  head tail hNil hHeadSeq hTailSeq)
          all_goals
            have hTailNe : tail ≠ Term.Stuck :=
              term_ne_stuck_of_strConcat_is_list_true
                (strConcat_is_list_tail_true_of_cons_self head tail hList)
            cases tail <;>
              simp [__eo_is_list_nil, __eo_is_list_nil_str_concat,
                __eo_eq, native_teq] at hNil hTailNe
      | _ =>
          simpa [__eo_list_singleton_elim_2] using
            RuleProofs.smt_value_rel_refl _
  | _ =>
      simpa [__eo_list_singleton_elim_2] using
        RuleProofs.smt_value_rel_refl _

private theorem smt_value_rel_get_a_norm_str_concat
    (M : SmtModel) (hM : model_total_typed M) (y x : Term) :
    RuleProofs.eo_has_smt_translation (mkStrConcat y x) ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (mkStrConcat y x)))
      (__smtx_model_eval M (__eo_to_smt (__get_a_norm (mkStrConcat y x)))) := by
  intro hTrans
  let t := mkStrConcat y x
  rcases strConcat_args_of_has_smt_translation y x hTrans with
    ⟨T, hyTy, hxTy⟩
  have htTy : __smtx_typeof (__eo_to_smt t) = SmtType.Seq T := by
    exact strConcat_typeof_concat_of_seq y x T hyTy hxTy
  have hTypeMatch :=
    TranslationProofs.eo_to_smt_typeof_matches_translation t (by
      rw [htTy]
      exact smt_seq_ne_none T)
  have hTypeSeq : __eo_to_smt_type (__eo_typeof t) = SmtType.Seq T := by
    rw [← hTypeMatch, htTy]
  let id := __eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof t)
  have hIdNil :
      __eo_is_list_nil (Term.UOp UserOp.str_concat) id = Term.Boolean true := by
    dsimp [id]
    exact strConcat_nil_is_list_nil_of_type hTypeSeq
  have hIdList :
      __eo_is_list (Term.UOp UserOp.str_concat) id = Term.Boolean true :=
    strConcat_is_list_nil_true_of_nil_true id hIdNil
  have hIdEq : id = __seq_empty (__eo_typeof t) := by
    dsimp [id]
    exact strConcat_nil_eq_seq_empty_of_type hTypeSeq
  have hIdEval :
      __smtx_model_eval M (__eo_to_smt id) =
        SmtValue.Seq (SmtSeq.empty T) := by
    rw [hIdEq]
    exact strConcat_eval_seq_empty_typeof M t T htTy
  have hIdNe : id ≠ Term.Stuck :=
    term_ne_stuck_of_strConcat_is_list_true hIdList
  have hRec :=
    strConcat_get_a_norm_rec_rel_eval M hM id T hIdList hIdEval hIdNe t htTy
  have hElim :=
    strConcat_singleton_elim_rel_eval M
      (__get_a_norm_rec (Term.UOp UserOp.str_concat) id t) hRec.1 hRec.2.1
  have hNormRel :
      RuleProofs.smt_value_rel
        (__smtx_model_eval M
          (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
            (__get_a_norm_rec (Term.UOp UserOp.str_concat) id t))))
        (__smtx_model_eval M (__eo_to_smt t)) :=
    RuleProofs.smt_value_rel_trans
      (__smtx_model_eval M
        (__eo_to_smt (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__get_a_norm_rec (Term.UOp UserOp.str_concat) id t))))
      (__smtx_model_eval M
        (__eo_to_smt (__get_a_norm_rec (Term.UOp UserOp.str_concat) id t)))
      (__smtx_model_eval M (__eo_to_smt t))
      hElim hRec.2.2
  change RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__get_a_norm_rec (Term.UOp UserOp.str_concat)
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof t)) t))))
  dsimp [id] at hNormRel
  exact RuleProofs.smt_value_rel_symm
    (__smtx_model_eval M
      (__eo_to_smt
        (__eo_list_singleton_elim (Term.UOp UserOp.str_concat)
          (__get_a_norm_rec (Term.UOp UserOp.str_concat)
            (__eo_nil (Term.UOp UserOp.str_concat) (__eo_typeof t)) t))))
    (__smtx_model_eval M (__eo_to_smt t))
    hNormRel

private theorem smt_value_rel_aciNormPayload_self
    (M : SmtModel) (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload t)))
    (__smtx_model_eval M (__eo_to_smt t)) := by
  intro hTrans
  rw [aciNormPayload_eq_self_of_has_smt_translation t hTrans]
  exact RuleProofs.smt_value_rel_refl (__smtx_model_eval M (__eo_to_smt t))

private theorem smt_value_rel_of_aci_norm_eq_true_right_translation
    (M : SmtModel) (x y : Term) :
  RuleProofs.eo_has_smt_translation y ->
  __aci_norm_eq x y = Term.Boolean true ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload x)))
    (__smtx_model_eval M (__eo_to_smt y)) := by
  intro hYTrans hEq
  by_cases hTermEq : __eo_eq x y = Term.Boolean true
  · have hyx : y = x := eq_of_eo_eq_true_local x y hTermEq
    subst y
    exact smt_value_rel_aciNormPayload_self M x hYTrans
  · have hYNe : y ≠ Term.Stuck := eo_has_smt_translation_ne_stuck y hYTrans
    have hXNe : x ≠ Term.Stuck := by
      intro hX
      subst x
      simp [__aci_norm_eq] at hEq
    have hEqIte := hEq
    rw [aci_norm_eq_nonstuck x y hXNe hYNe] at hEqIte
    have hL1 :
        __eo_l_1___aci_norm_eq x y = Term.Boolean true :=
      (eo_ite_else_eq_true_of_cond_ne_true
        (__eo_eq x y) (Term.Boolean true)
        (__eo_l_1___aci_norm_eq x y) hTermEq hEqIte).2
    let x0 := x
    change __eo_l_1___aci_norm_eq x0 y = Term.Boolean true at hL1
    change RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt (aciNormPayload x0)))
      (__smtx_model_eval M (__eo_to_smt y))
    cases x
    case neg.Stuck =>
      exact False.elim (hXNe rfl)
    case neg.Apply f payload =>
      change RuleProofs.smt_value_rel
        (__smtx_model_eval M (__eo_to_smt (aciNormPayload x0)))
        (__smtx_model_eval M (__eo_to_smt y))
      cases f
      case Apply g markerArg =>
        cases g
        case UOp op =>
          cases op
          case _at__at_aci_sorted =>
            exact
              smt_value_rel_of_aci_norm_l1_marker_eq_true_right_translation
                M markerArg payload y hYTrans hL1
          all_goals
            have hNotMarker :
                ∀ markerOp markerPayload,
                  x0 ≠
                    Term.Apply
                      (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) markerOp)
                      markerPayload := by
              intro markerOp markerPayload h
              unfold x0 at h
              cases h
            have hFalse :=
              aci_norm_l1_nonmarker_left_eq_false
                x0 y hNotMarker hXNe hYNe
            rw [hFalse] at hL1
            contradiction
        all_goals
          have hNotMarker :
              ∀ markerOp markerPayload,
                x0 ≠
                  Term.Apply
                    (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) markerOp)
                    markerPayload := by
            intro markerOp markerPayload h
            unfold x0 at h
            cases h
          have hFalse :=
            aci_norm_l1_nonmarker_left_eq_false
              x0 y hNotMarker hXNe hYNe
          rw [hFalse] at hL1
          contradiction
      all_goals
        have hNotMarker :
            ∀ markerArg markerPayload,
              x0 ≠
                Term.Apply
                  (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) markerArg)
                  markerPayload := by
          intro markerArg markerPayload h
          unfold x0 at h
          cases h
        have hFalse :=
          aci_norm_l1_nonmarker_left_eq_false
            x0 y hNotMarker hXNe hYNe
        rw [hFalse] at hL1
        contradiction
    all_goals
      have hNotMarker :
          ∀ markerArg markerPayload,
            x0 ≠
              Term.Apply
                (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) markerArg)
                markerPayload := by
        intro markerArg markerPayload h
        unfold x0 at h
        cases h
      have hFalse :=
        aci_norm_l1_nonmarker_left_eq_false x0 y hNotMarker hXNe hYNe
      rw [hFalse] at hL1
      contradiction

private theorem smt_value_rel_of_aci_norm_eq_true_normal_forms
    (M : SmtModel) (hM : model_total_typed M) (a b : Term) :
  RuleProofs.eo_has_smt_translation a ->
  RuleProofs.eo_has_smt_translation b ->
  __aci_norm_eq (__get_aci_normal_form a) (__get_aci_normal_form b) = Term.Boolean true ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form a))))
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form b)))) := by
  intro hATrans hBTrans hEq
  by_cases hTermEq :
      __eo_eq (__get_aci_normal_form a) (__get_aci_normal_form b) = Term.Boolean true
  · have hba := eq_of_eo_eq_true_local
      (__get_aci_normal_form a) (__get_aci_normal_form b) hTermEq
    rw [hba]
    exact RuleProofs.smt_value_rel_refl
      (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form a))))
  · by_cases hBnfTrans :
        RuleProofs.eo_has_smt_translation (__get_aci_normal_form b)
    · have hRel :=
        smt_value_rel_of_aci_norm_eq_true_right_translation M
          (__get_aci_normal_form a) (__get_aci_normal_form b)
          hBnfTrans hEq
      rw [aciNormPayload_eq_self_of_has_smt_translation
        (__get_aci_normal_form b) hBnfTrans]
      exact hRel
    · by_cases hAnfTrans :
          RuleProofs.eo_has_smt_translation (__get_aci_normal_form a)
      · have hNotMarker :
            ∀ f payload,
              __get_aci_normal_form a ≠
                Term.Apply
                  (Term.Apply (Term.UOp UserOp._at__at_aci_sorted) f)
                  payload := by
          intro f payload hMarker
          exact aci_sorted_marker_not_has_smt_translation f payload (by
            rw [← hMarker]
            exact hAnfTrans)
        exact False.elim
          (aci_norm_eq_true_nonmarker_left_false
            (__get_aci_normal_form a) (__get_aci_normal_form b)
            hNotMarker hTermEq hEq)
      · -- The remaining cases are generated marker/list cases.
        sorry

private theorem smt_value_rel_get_aci_normal_form_payload
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  __get_aci_normal_form t ≠ Term.Stuck ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form t)))) := by
  intro hTrans hNFNe
  cases t <;> simp [__get_aci_normal_form, aciNormPayload] <;>
    try exact RuleProofs.smt_value_rel_refl _
  case Apply f x =>
    cases f <;> try exact RuleProofs.smt_value_rel_refl _
    case Apply g y =>
      cases g <;> try exact RuleProofs.smt_value_rel_refl _
      case UOp op =>
        cases op <;> simp [__get_aci_normal_form] <;>
          try exact RuleProofs.smt_value_rel_refl _
        case or =>
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x)))
            (__smtx_model_eval M
              (__eo_to_smt
                (aciNormPayload
                  (__eo_mk_apply
                    (Term.Apply (Term.UOp UserOp._at__at_aci_sorted)
                      (Term.UOp UserOp.or))
                    (__get_ai_norm
                      (Term.Apply (Term.Apply (Term.UOp UserOp.or) y) x))))))
          rw [aciNormPayload_mk_aci_sorted]
          exact smt_value_rel_get_ai_norm_or M hM y x hTrans
        case and =>
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M
              (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x)))
            (__smtx_model_eval M
              (__eo_to_smt
                (aciNormPayload
                  (__eo_mk_apply
                    (Term.Apply (Term.UOp UserOp._at__at_aci_sorted)
                      (Term.UOp UserOp.and))
                    (__get_ai_norm
                      (Term.Apply (Term.Apply (Term.UOp UserOp.and) y) x))))))
          rw [aciNormPayload_mk_aci_sorted]
          exact smt_value_rel_get_ai_norm_and M hM y x hTrans
        case concat =>
          have hNormRel :=
            smt_value_rel_get_a_norm_concat M hM y x hTrans
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (mkBvConcat y x)))
            (__smtx_model_eval M
              (__eo_to_smt
                (aciNormPayload (__get_a_norm (mkBvConcat y x)))))
          exact smt_value_rel_aciNormPayload_right_of_rel_has_translation
            M hM (mkBvConcat y x) (__get_a_norm (mkBvConcat y x)) hTrans
            hNormRel
        case bvand =>
          have hNormRel :=
            smt_value_rel_get_ai_norm_bvand M hM y x hTrans (by
              intro hAIStuck
              apply hNFNe
              change __eo_mk_apply
                  (Term.Apply (Term.UOp UserOp._at__at_aci_sorted)
                    (Term.UOp UserOp.bvand))
                  (__get_ai_norm (mkBvAnd y x)) = Term.Stuck
              rw [hAIStuck]
              simp [__eo_mk_apply])
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (mkBvAnd y x)))
            (__smtx_model_eval M
              (__eo_to_smt
                (aciNormPayload
                  (__eo_mk_apply
                    (Term.Apply (Term.UOp UserOp._at__at_aci_sorted)
                      (Term.UOp UserOp.bvand))
                    (__get_ai_norm (mkBvAnd y x))))))
          rw [aciNormPayload_mk_aci_sorted]
          exact hNormRel
        case bvor =>
          -- AI normalizer case.
          sorry
        case bvxor =>
          -- A normalizer case.
          sorry
        case str_concat =>
          have hNormRel :=
            smt_value_rel_get_a_norm_str_concat M hM y x hTrans
          change RuleProofs.smt_value_rel
            (__smtx_model_eval M (__eo_to_smt (mkStrConcat y x)))
            (__smtx_model_eval M
              (__eo_to_smt
                (aciNormPayload (__get_a_norm (mkStrConcat y x)))))
          exact smt_value_rel_aciNormPayload_right_of_rel_has_translation
            M hM (mkStrConcat y x) (__get_a_norm (mkStrConcat y x)) hTrans
            hNormRel
        case re_concat =>
          -- A normalizer case.
          sorry
        case re_inter =>
          -- AI normalizer case.
          sorry
        case re_union =>
          -- AI normalizer case.
          sorry
        case _at__at_aci_sorted =>
          exact False.elim (aci_sorted_marker_not_has_smt_translation y x hTrans)

private theorem smt_value_rel_of_aci_norm_guard_true
    (M : SmtModel) (hM : model_total_typed M) (a b : Term) :
  RuleProofs.eo_has_smt_translation
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  RuleProofs.eo_has_bool_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.eq) a) b) ->
  aciNormGuard a b = Term.Boolean true ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt a))
    (__smtx_model_eval M (__eo_to_smt b)) := by
  intro hEqTrans hEqBool hGuard
  have hAHas : RuleProofs.eo_has_smt_translation a := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hEqBool with
      ⟨_, hNonNone⟩
    exact hNonNone
  have hBHas : RuleProofs.eo_has_smt_translation b := by
    rcases RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type a b hEqBool with
      ⟨hTy, hNonNone⟩
    rw [hTy] at hNonNone
    exact hNonNone
  cases hLeft : __aci_norm_eq (__get_aci_normal_form a) b
  all_goals
    simp [aciNormGuard, __eo_ite, native_teq, hLeft] at hGuard
  case Boolean left =>
    cases left
    · cases hRight : __aci_norm_eq (__get_aci_normal_form b) a
      all_goals
        simp [aciNormGuard, __eo_ite, native_teq, hLeft, hRight] at hGuard
      case Boolean right =>
        cases right
        · have hNFARel :=
            smt_value_rel_get_aci_normal_form_payload M hM a hAHas
              (aci_norm_eq_true_left_ne_stuck
                (__get_aci_normal_form a) (__get_aci_normal_form b) hGuard)
          have hNFBRel :=
            smt_value_rel_get_aci_normal_form_payload M hM b hBHas
              (aci_norm_eq_true_right_ne_stuck
                (__get_aci_normal_form a) (__get_aci_normal_form b) hGuard)
          have hNFRel :=
            smt_value_rel_of_aci_norm_eq_true_normal_forms M hM
              a b hAHas hBHas hGuard
          exact RuleProofs.smt_value_rel_trans
            (__smtx_model_eval M (__eo_to_smt a))
            (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form a))))
            (__smtx_model_eval M (__eo_to_smt b))
            hNFARel
            (RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form a))))
              (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form b))))
              (__smtx_model_eval M (__eo_to_smt b))
              hNFRel
              (RuleProofs.smt_value_rel_symm _ _ hNFBRel))
        · have hNFBRel :=
            smt_value_rel_get_aci_normal_form_payload M hM b hBHas
              (aci_norm_eq_true_left_ne_stuck
                (__get_aci_normal_form b) a hRight)
          have hRel :=
            smt_value_rel_of_aci_norm_eq_true_right_translation M
              (__get_aci_normal_form b) a hAHas hRight
          have hBA : RuleProofs.smt_value_rel
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt a)) :=
            RuleProofs.smt_value_rel_trans
              (__smtx_model_eval M (__eo_to_smt b))
              (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form b))))
              (__smtx_model_eval M (__eo_to_smt a))
              hNFBRel hRel
          exact RuleProofs.smt_value_rel_symm
            (__smtx_model_eval M (__eo_to_smt b))
            (__smtx_model_eval M (__eo_to_smt a))
            hBA
      all_goals
        contradiction
    · have hNFARel :=
        smt_value_rel_get_aci_normal_form_payload M hM a hAHas
          (aci_norm_eq_true_left_ne_stuck
            (__get_aci_normal_form a) b hLeft)
      have hRel :=
        smt_value_rel_of_aci_norm_eq_true_right_translation M
          (__get_aci_normal_form a) b hBHas hLeft
      exact RuleProofs.smt_value_rel_trans
        (__smtx_model_eval M (__eo_to_smt a))
        (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form a))))
        (__smtx_model_eval M (__eo_to_smt b))
        hNFARel hRel
  all_goals
    contradiction

private theorem facts___eo_prog_aci_norm_impl
    (M : SmtModel) (hM : model_total_typed M) (a1 : Term) :
  RuleProofs.eo_has_smt_translation a1 ->
  __eo_typeof (__eo_prog_aci_norm a1) = Term.Bool ->
  eo_interprets M (__eo_prog_aci_norm a1) true := by
  intro hTrans hResultTy
  have hProgEq : __eo_prog_aci_norm a1 = a1 :=
    eo_prog_aci_norm_eq_input_of_type_bool a1 hResultTy
  cases a1
  all_goals try
    have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
      simpa [__eo_prog_aci_norm] using hResultTy
    exact False.elim (eo_typeof_stuck_ne_bool hStuck)
  case Apply f x =>
    cases f
    all_goals try
      have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
        simpa [__eo_prog_aci_norm] using hResultTy
      exact False.elim (eo_typeof_stuck_ne_bool hStuck)
    case Apply g y =>
      cases g
      all_goals try
        have hStuck : __eo_typeof Term.Stuck = Term.Bool := by
          simpa [__eo_prog_aci_norm] using hResultTy
        exact False.elim (eo_typeof_stuck_ne_bool hStuck)
      case UOp op =>
        cases op <;> simp [__eo_prog_aci_norm] at hResultTy hProgEq ⊢
        case eq =>
          have hEqTrans :
              RuleProofs.eo_has_smt_translation
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) := hTrans
          have hEqTypeof : __eo_typeof (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) =
              Term.Bool := by
            simpa [hProgEq] using hResultTy
          have hEqBool :
              RuleProofs.eo_has_bool_type
                (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) :=
            RuleProofs.eo_typeof_bool_implies_has_bool_type
              (Term.Apply (Term.Apply (Term.UOp UserOp.eq) y) x) hEqTrans hEqTypeof
          have hGuard :
              aciNormGuard y x = Term.Boolean true := by
            apply aci_norm_guard_true_of_type_bool y x
            simpa [aciNormGuard] using hResultTy
          rw [hProgEq]
          exact RuleProofs.eo_interprets_eq_of_rel M y x hEqBool
            (smt_value_rel_of_aci_norm_guard_true M hM y x hEqTrans hEqBool hGuard)
        all_goals
          exact False.elim (eo_typeof_stuck_ne_bool hResultTy)

theorem cmd_step_aci_norm_properties
    (M : SmtModel) (hM : model_total_typed M)
    (s : CState) (args : CArgList) (premises : CIndexList) :
  cmdTranslationOk (CCmd.step CRule.aci_norm args premises) ->
  AllHaveBoolType (premiseTermList s premises) ->
  __eo_typeof (__eo_cmd_step_proven s CRule.aci_norm args premises) = Term.Bool ->
  StepRuleProperties M (premiseTermList s premises)
    (__eo_cmd_step_proven s CRule.aci_norm args premises) :=
by
  intro hCmdTrans _hPremisesBool hResultTy
  have hProg : __eo_cmd_step_proven s CRule.aci_norm args premises ≠ Term.Stuck :=
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
              have hArgsTrans :
                  cArgListTranslationOk (CArgList.cons a1 CArgList.nil) := by
                simpa [cmdTranslationOk] using hCmdTrans
              have hA1Trans : RuleProofs.eo_has_smt_translation a1 := by
                simpa [cArgListTranslationOk] using hArgsTrans
              change __eo_typeof (__eo_prog_aci_norm a1) = Term.Bool at hResultTy
              have hProgEq : __eo_prog_aci_norm a1 = a1 :=
                eo_prog_aci_norm_eq_input_of_type_bool a1 hResultTy
              refine ⟨?_, ?_⟩
              · intro _hTrue
                change eo_interprets M (__eo_prog_aci_norm a1) true
                exact facts___eo_prog_aci_norm_impl M hM a1 hA1Trans hResultTy
              · change RuleProofs.eo_has_smt_translation (__eo_prog_aci_norm a1)
                rw [hProgEq]
                exact hA1Trans
          | cons _ _ =>
              change Term.Stuck ≠ Term.Stuck at hProg
              exact False.elim (hProg rfl)
      | cons _ _ =>
          change Term.Stuck ≠ Term.Stuck at hProg
          exact False.elim (hProg rfl)
