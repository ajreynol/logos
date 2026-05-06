import Cpc.Proofs.RuleSupport.Support

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

private theorem eq_of_eo_eq_true_local (x y : Term)
    (h : __eo_eq x y = Term.Boolean true) :
    y = x := by
  by_cases hx : x = Term.Stuck
  · subst x
    simp [__eo_eq] at h
  · by_cases hy : y = Term.Stuck
    · subst y
      simp [__eo_eq] at h
    · have hDec : native_teq y x = true := by
        simpa [__eo_eq, hx, hy] using h
      simpa [native_teq] using hDec

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
  · -- The remaining cases are generated marker/list cases.
    sorry

private theorem smt_value_rel_get_aci_normal_form_payload
    (M : SmtModel) (hM : model_total_typed M) (t : Term) :
  RuleProofs.eo_has_smt_translation t ->
  RuleProofs.smt_value_rel
    (__smtx_model_eval M (__eo_to_smt t))
    (__smtx_model_eval M (__eo_to_smt (aciNormPayload (__get_aci_normal_form t)))) := by
  intro hTrans
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
          -- AI normalizer case.
          sorry
        case and =>
          -- AI normalizer case.
          sorry
        case concat =>
          -- A normalizer case.
          sorry
        case bvand =>
          -- AI normalizer case.
          sorry
        case bvor =>
          -- AI normalizer case.
          sorry
        case bvxor =>
          -- A normalizer case.
          sorry
        case str_concat =>
          -- A normalizer case.
          sorry
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
          have hNFBRel :=
            smt_value_rel_get_aci_normal_form_payload M hM b hBHas
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
