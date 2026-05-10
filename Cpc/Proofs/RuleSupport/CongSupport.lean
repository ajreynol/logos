import Cpc.Proofs.RuleSupport.Support
import Cpc.Proofs.Translation.Apply
import Cpc.Proofs.Translation.Inversions

open Eo
open SmtEval
open Smtm

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 10000000

namespace CongSupport

private abbrev mkEq (x y : Term) : Term :=
  Term.Apply (Term.Apply (Term.UOp UserOp.eq) x) y

private theorem eo_mk_apply_eq_of_ne_stuck (f x : Term) :
    f ≠ Term.Stuck ->
    x ≠ Term.Stuck ->
    __eo_mk_apply f x = Term.Apply f x := by
  intro hf hx
  cases f <;> cases x <;> simp [__eo_mk_apply] at hf hx ⊢

private theorem eo_mk_apply_left_ne_stuck_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    f ≠ Term.Stuck := by
  intro h hF
  subst hF
  exact h (by simp [__eo_mk_apply])

private theorem eo_mk_apply_right_ne_stuck_of_ne_stuck (f x : Term) :
    __eo_mk_apply f x ≠ Term.Stuck ->
    x ≠ Term.Stuck := by
  intro h hX
  subst hX
  cases f <;> simp [__eo_mk_apply] at h

private theorem eq_of_eo_eq_true (x y : Term) :
    __eo_eq x y = Term.Boolean true ->
    y = x := by
  intro h
  cases x <;> cases y <;> simp [__eo_eq, native_teq] at h ⊢
  all_goals exact h

private theorem eo_get_nil_rec_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_get_nil_rec (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        Term.Boolean true := by
  intro ps
  induction ps with
  | nil =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires,
        __eo_is_list_nil, native_ite, native_teq, native_not,
        SmtEval.native_not]
  | cons p ps ih =>
      simp [premiseAndFormulaList, __eo_get_nil_rec, __eo_requires, ih,
        native_ite, native_teq, native_not, SmtEval.native_not]

private theorem eo_list_rev_rec_and_premiseAndFormulaList :
    ∀ xs ys : List Term,
      __eo_list_rev_rec (premiseAndFormulaList xs) (premiseAndFormulaList ys) =
        premiseAndFormulaList (xs.reverse ++ ys) := by
  intro xs ys
  induction xs generalizing ys with
  | nil =>
      cases ys <;> rfl
  | cons p xs ih =>
      cases ys with
      | nil =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih [p]
      | cons y ys =>
          simpa [premiseAndFormulaList, __eo_list_rev_rec, List.reverse_cons,
            List.append_assoc] using ih (p :: y :: ys)

private theorem eo_list_rev_and_premiseAndFormulaList :
    ∀ ps : List Term,
      __eo_list_rev (Term.UOp UserOp.and) (premiseAndFormulaList ps) =
        premiseAndFormulaList ps.reverse := by
  intro ps
  unfold __eo_list_rev
  simp [__eo_requires, premiseAndFormulaList_is_and_list,
    eo_get_nil_rec_and_premiseAndFormulaList, native_ite, native_teq,
    native_not, SmtEval.native_not]
  simpa using eo_list_rev_rec_and_premiseAndFormulaList ps []

private theorem all_interpreted_true_reverse
    (M : SmtModel) (ps : List Term) :
    AllInterpretedTrue M ps ->
    AllInterpretedTrue M ps.reverse := by
  intro h t ht
  exact h t (by simpa using List.mem_reverse.mp ht)

private theorem all_have_bool_type_reverse
    (ps : List Term) :
    AllHaveBoolType ps ->
    AllHaveBoolType ps.reverse := by
  intro h t ht
  exact h t (by simpa using List.mem_reverse.mp ht)

inductive CongTrueSpine (M : SmtModel) : Term -> Term -> Prop where
  | refl (t : Term) : CongTrueSpine M t t
  | app {f g x y : Term} :
      CongTrueSpine M f g ->
      eo_interprets M (mkEq x y) true ->
      CongTrueSpine M (Term.Apply f x) (Term.Apply g y)

inductive CongTypeSpine : Term -> Term -> Prop where
  | refl (t : Term) : CongTypeSpine t t
  | app {f g x y : Term} :
      CongTypeSpine f g ->
      RuleProofs.eo_has_bool_type (mkEq x y) ->
      CongTypeSpine (Term.Apply f x) (Term.Apply g y)

private def appSpineRev : Term -> Term × List Term
  | Term.Apply f x =>
      let spine := appSpineRev f
      (spine.1, x :: spine.2)
  | t => (t, [])

private def EqTrueOrSame (M : SmtModel) (x y : Term) : Prop :=
  x = y ∨ eo_interprets M (mkEq x y) true

private def EqBoolOrSame (x y : Term) : Prop :=
  x = y ∨ RuleProofs.eo_has_bool_type (mkEq x y)

private inductive ListRel (R : Term -> Term -> Prop) :
    List Term -> List Term -> Prop where
  | nil : ListRel R [] []
  | cons {x y : Term} {xs ys : List Term} :
      R x y -> ListRel R xs ys -> ListRel R (x :: xs) (y :: ys)

private theorem forall₂_eq_true_or_same_refl
    (M : SmtModel) :
    ∀ xs : List Term, ListRel (EqTrueOrSame M) xs xs
  | [] => ListRel.nil
  | x :: xs =>
      ListRel.cons (by exact Or.inl rfl)
        (forall₂_eq_true_or_same_refl M xs)

private theorem forall₂_eq_bool_or_same_refl :
    ∀ xs : List Term, ListRel EqBoolOrSame xs xs
  | [] => ListRel.nil
  | x :: xs =>
      ListRel.cons (by exact Or.inl rfl)
        (forall₂_eq_bool_or_same_refl xs)

private theorem congTrueSpine_appSpineRev
    (M : SmtModel) :
    ∀ {t rhs : Term},
      CongTrueSpine M t rhs ->
      (appSpineRev t).1 = (appSpineRev rhs).1 ∧
        ListRel (EqTrueOrSame M) (appSpineRev t).2 (appSpineRev rhs).2
  | _, _, CongTrueSpine.refl t => by
      exact ⟨rfl, forall₂_eq_true_or_same_refl M (appSpineRev t).2⟩
  | _, _, CongTrueSpine.app hRec hArg => by
      rcases congTrueSpine_appSpineRev M hRec with ⟨hHead, hArgs⟩
      exact ⟨hHead, ListRel.cons (by exact Or.inr hArg) hArgs⟩

private theorem congTypeSpine_appSpineRev :
    ∀ {t rhs : Term},
      CongTypeSpine t rhs ->
      (appSpineRev t).1 = (appSpineRev rhs).1 ∧
        ListRel EqBoolOrSame (appSpineRev t).2 (appSpineRev rhs).2
  | _, _, CongTypeSpine.refl t => by
      exact ⟨rfl, forall₂_eq_bool_or_same_refl (appSpineRev t).2⟩
  | _, _, CongTypeSpine.app hRec hArg => by
      rcases congTypeSpine_appSpineRev hRec with ⟨hHead, hArgs⟩
      exact ⟨hHead, ListRel.cons (by exact Or.inr hArg) hArgs⟩

private theorem congTrueSpine_uop_eq
    (M : SmtModel) (op : UserOp) (rhs : Term) :
    CongTrueSpine M (Term.UOp op) rhs ->
    rhs = Term.UOp op := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTypeSpine_uop_eq
    (op : UserOp) (rhs : Term) :
    CongTypeSpine (Term.UOp op) rhs ->
    rhs = Term.UOp op := by
  intro h
  cases h with
  | refl _ => rfl

private theorem congTrueSpine_unary_uop_inv
    (M : SmtModel) (op : UserOp) (x rhs : Term) :
    CongTrueSpine M (Term.Apply (Term.UOp op) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp op) y ∧
        EqTrueOrSame M x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTrueSpine_uop_eq M op _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTypeSpine_unary_uop_inv
    (op : UserOp) (x rhs : Term) :
    CongTypeSpine (Term.Apply (Term.UOp op) x) rhs ->
    ∃ y,
      rhs = Term.Apply (Term.UOp op) y ∧
        EqBoolOrSame x y := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x, rfl, Or.inl rfl⟩
  | app hHead hArg =>
      have hg : _ := congTypeSpine_uop_eq op _ hHead
      subst hg
      exact ⟨_, rfl, Or.inr hArg⟩

private theorem congTrueSpine_binary_uop_inv
    (M : SmtModel) (op : UserOp) (x₁ x₂ rhs : Term) :
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) rhs ->
    ∃ y₁ y₂,
      rhs = Term.Apply (Term.Apply (Term.UOp op) y₁) y₂ ∧
        EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTrueSpine_unary_uop_inv M op x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTypeSpine_binary_uop_inv
    (op : UserOp) (x₁ x₂ rhs : Term) :
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) rhs ->
    ∃ y₁ y₂,
      rhs = Term.Apply (Term.Apply (Term.UOp op) y₁) y₂ ∧
        EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₂ =>
      rcases congTypeSpine_unary_uop_inv op x₁ _ hHead with
        ⟨y₁, hHeadEq, hArg₁⟩
      subst hHeadEq
      exact ⟨y₁, _, rfl, hArg₁, Or.inr hArg₂⟩

private theorem congTrueSpine_ternary_uop_inv
    (M : SmtModel) (op : UserOp) (x₁ x₂ x₃ rhs : Term) :
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) x₃)
      rhs ->
    ∃ y₁ y₂ y₃,
      rhs =
        Term.Apply (Term.Apply (Term.Apply (Term.UOp op) y₁) y₂) y₃ ∧
        EqTrueOrSame M x₁ y₁ ∧ EqTrueOrSame M x₂ y₂ ∧
          EqTrueOrSame M x₃ y₃ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ =>
      rcases congTrueSpine_binary_uop_inv M op x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem congTypeSpine_ternary_uop_inv
    (op : UserOp) (x₁ x₂ x₃ rhs : Term) :
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp op) x₁) x₂) x₃)
      rhs ->
    ∃ y₁ y₂ y₃,
      rhs =
        Term.Apply (Term.Apply (Term.Apply (Term.UOp op) y₁) y₂) y₃ ∧
        EqBoolOrSame x₁ y₁ ∧ EqBoolOrSame x₂ y₂ ∧
          EqBoolOrSame x₃ y₃ := by
  intro h
  cases h with
  | refl _ =>
      exact ⟨x₁, x₂, x₃, rfl, Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
  | app hHead hArg₃ =>
      rcases congTypeSpine_binary_uop_inv op x₁ x₂ _ hHead with
        ⟨y₁, y₂, hHeadEq, hArg₁, hArg₂⟩
      subst hHeadEq
      exact ⟨y₁, y₂, _, rfl, hArg₁, hArg₂, Or.inr hArg₃⟩

private theorem smt_value_rel_of_eq_true_or_same
    (M : SmtModel) (x y : Term) :
    EqTrueOrSame M x y ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M (__eo_to_smt x))
      (__smtx_model_eval M (__eo_to_smt y)) := by
  intro h
  rcases h with hEq | hTrue
  · subst hEq
    exact RuleProofs.smt_value_rel_refl _
  · exact RuleProofs.eo_interprets_eq_rel M x y hTrue

private theorem smt_type_eq_of_eq_true_or_same
    (M : SmtModel) (x y : Term) :
    EqTrueOrSame M x y ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) := by
  intro h
  rcases h with hEq | hTrue
  · subst hEq
    rfl
  · exact (RuleProofs.eo_eq_operands_same_smt_type M x y hTrue).1

private theorem smt_type_eq_of_eq_bool_or_same
    (x y : Term) :
    EqBoolOrSame x y ->
    __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) := by
  intro h
  rcases h with hEq | hBool
  · subst hEq
    rfl
  · exact (RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type x y hBool).1

private theorem smt_model_eval_eq_of_rel_at_non_reglan_type
    (M : SmtModel) (hM : model_total_typed M) (x y : SmtTerm)
    (T : SmtType) :
    __smtx_typeof x = T ->
    __smtx_typeof y = T ->
    T ≠ SmtType.None ->
    T ≠ SmtType.RegLan ->
    RuleProofs.smt_value_rel
      (__smtx_model_eval M x) (__smtx_model_eval M y) ->
    __smtx_model_eval M x = __smtx_model_eval M y := by
  intro hxTy hyTy hTNN hTReg hRel
  have hxNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hxTy]
    exact hTNN
  have hyNN : term_has_non_none_type y := by
    unfold term_has_non_none_type
    rw [hyTy]
    exact hTNN
  have hxValTy :
      __smtx_typeof_value (__smtx_model_eval M x) = T := by
    simpa [hxTy] using smt_model_eval_preserves_type_of_non_none M hM x hxNN
  have hyValTy :
      __smtx_typeof_value (__smtx_model_eval M y) = T := by
    simpa [hyTy] using smt_model_eval_preserves_type_of_non_none M hM y hyNN
  exact RuleProofs.smt_value_rel_eq_of_type_ne_reglan
    hxValTy hyValTy hTReg hRel

private theorem eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type
    (M : SmtModel) (hM : model_total_typed M) (x y : Term)
    (T : SmtType) :
    __smtx_typeof (__eo_to_smt x) = T ->
    __smtx_typeof (__eo_to_smt y) = T ->
    T ≠ SmtType.None ->
    T ≠ SmtType.RegLan ->
    EqTrueOrSame M x y ->
    __smtx_model_eval M (__eo_to_smt x) =
      __smtx_model_eval M (__eo_to_smt y) := by
  intro hxTy hyTy hTNN hTReg hRel
  exact smt_model_eval_eq_of_rel_at_non_reglan_type M hM
    (__eo_to_smt x) (__eo_to_smt y) T hxTy hyTy hTNN hTReg
    (smt_value_rel_of_eq_true_or_same M x y hRel)

private theorem smt_typeof_not_arg_bool_of_non_none (x : SmtTerm) :
    __smtx_typeof (SmtTerm.not x) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool := by
  intro hNN
  rw [typeof_not_eq] at hNN
  cases h : __smtx_typeof x <;>
    simp [native_ite, native_Teq, h] at hNN ⊢

private theorem smt_typeof_and_args_bool_of_non_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.and x y) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.and x y) := by
    unfold term_has_non_none_type
    exact hNN
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.and)
    (typeof_and_eq x y) hTerm

private theorem smt_typeof_or_args_bool_of_non_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.or x y) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.or x y) := by
    unfold term_has_non_none_type
    exact hNN
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.or)
    (typeof_or_eq x y) hTerm

private theorem smt_typeof_imp_args_bool_of_non_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.imp x y) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.imp x y) := by
    unfold term_has_non_none_type
    exact hNN
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.imp)
    (typeof_imp_eq x y) hTerm

private theorem smt_typeof_xor_args_bool_of_non_none (x y : SmtTerm) :
    __smtx_typeof (SmtTerm.xor x y) ≠ SmtType.None ->
    __smtx_typeof x = SmtType.Bool ∧ __smtx_typeof y = SmtType.Bool := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.xor x y) := by
    unfold term_has_non_none_type
    exact hNN
  exact bool_binop_args_bool_of_non_none (op := SmtTerm.xor)
    (typeof_xor_eq x y) hTerm

private theorem mk_cong_rhs_step_eq_of_eo_eq_true
    (f x y z tail : Term) :
    __eo_eq x y = Term.Boolean true ->
    __mk_cong_rhs (Term.Apply f x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (mkEq y z)) tail) =
      __eo_mk_apply (__mk_cong_rhs f tail) z := by
  intro hEq
  simp [mkEq, __mk_cong_rhs, __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
    native_teq, native_ite]

private theorem mk_cong_rhs_false_branch_stuck
    (f x y z tail : Term) :
    __eo_l_1___mk_cong_rhs (Term.Apply f x)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) (mkEq y z)) tail) =
      Term.Stuck := by
  simp [mkEq, __eo_l_1___mk_cong_rhs]

private theorem mk_cong_rhs_congTrueSpine_of_list
    (M : SmtModel) :
    ∀ (ps : List Term) (t : Term),
      AllInterpretedTrue M ps ->
      __mk_cong_rhs t (premiseAndFormulaList ps) ≠ Term.Stuck ->
      CongTrueSpine M t (__mk_cong_rhs t (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro t _ hProg
      cases t <;>
        simp [premiseAndFormulaList, __mk_cong_rhs, __eo_l_1___mk_cong_rhs] at hProg ⊢
      all_goals exact CongTrueSpine.refl _
  | cons p ps ih =>
      intro t hTrue hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    cases t with
                    | Apply f x =>
                        have hHeadTrue :
                            eo_interprets M (mkEq lhs tail) true := by
                          simpa [premiseAndFormulaList, mkEq] using
                            hTrue (mkEq lhs tail) (by simp [mkEq])
                        have hRestTrue : AllInterpretedTrue M ps := by
                          intro q hq
                          exact hTrue q (by simp [premiseAndFormulaList, hq])
                        have hCond :
                            __eo_eq x lhs = Term.Boolean true := by
                          cases hEq : __eo_eq x lhs <;>
                            simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                              __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                              native_teq, native_ite] at hProg
                          case Boolean b =>
                            cases b with
                            | false =>
                                simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                                  __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                                  native_teq, native_ite] at hProg
                            | true =>
                                rfl
                        have hStepEq :=
                          mk_cong_rhs_step_eq_of_eo_eq_true f x lhs tail
                            (premiseAndFormulaList ps) hCond
                        have hMkApplyNN :
                            __eo_mk_apply
                                (__mk_cong_rhs f (premiseAndFormulaList ps)) tail ≠
                              Term.Stuck := by
                          rw [← hStepEq]
                          exact hProg
                        have hRecNN :
                            __mk_cong_rhs f (premiseAndFormulaList ps) ≠
                              Term.Stuck :=
                          eo_mk_apply_left_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hTailNN : tail ≠ Term.Stuck :=
                          eo_mk_apply_right_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hRec :=
                          ih f hRestTrue hRecNN
                        have hLhs : lhs = x :=
                          eq_of_eo_eq_true x lhs hCond
                        subst lhs
                        change CongTrueSpine M (Term.Apply f x)
                          (__mk_cong_rhs (Term.Apply f x)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                              (mkEq x tail)) (premiseAndFormulaList ps)))
                        rw [hStepEq]
                        rw [eo_mk_apply_eq_of_ne_stuck
                          (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                          hRecNN hTailNN]
                        exact CongTrueSpine.app hRec hHeadTrue
                    | _ =>
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                            __eo_l_1___mk_cong_rhs]))
                  all_goals
                    exact False.elim (hProg (by
                      cases t <;>
                        simp [premiseAndFormulaList, __mk_cong_rhs,
                          __eo_l_1___mk_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    cases t <;>
                      simp [premiseAndFormulaList, __mk_cong_rhs,
                        __eo_l_1___mk_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                cases t <;>
                  simp [premiseAndFormulaList, __mk_cong_rhs,
                    __eo_l_1___mk_cong_rhs]))
      | _ =>
          exact False.elim (hProg (by
            cases t <;>
              simp [premiseAndFormulaList, __mk_cong_rhs,
                __eo_l_1___mk_cong_rhs]))

private theorem mk_cong_rhs_congTypeSpine_of_list :
    ∀ (ps : List Term) (t : Term),
      AllHaveBoolType ps ->
      __mk_cong_rhs t (premiseAndFormulaList ps) ≠ Term.Stuck ->
      CongTypeSpine t (__mk_cong_rhs t (premiseAndFormulaList ps)) := by
  intro ps
  induction ps with
  | nil =>
      intro t _ hProg
      cases t <;>
        simp [premiseAndFormulaList, __mk_cong_rhs, __eo_l_1___mk_cong_rhs] at hProg ⊢
      all_goals exact CongTypeSpine.refl _
  | cons p ps ih =>
      intro t hBool hProg
      cases p with
      | Apply pf tail =>
          cases pf with
          | Apply pg lhs =>
              cases pg with
              | UOp op =>
                  cases op
                  case eq =>
                    cases t with
                    | Apply f x =>
                        have hHeadBool :
                            RuleProofs.eo_has_bool_type (mkEq lhs tail) := by
                          simpa [premiseAndFormulaList, mkEq] using
                            hBool (mkEq lhs tail) (by simp [mkEq])
                        have hRestBool : AllHaveBoolType ps := by
                          intro q hq
                          exact hBool q (by simp [premiseAndFormulaList, hq])
                        have hCond :
                            __eo_eq x lhs = Term.Boolean true := by
                          cases hEq : __eo_eq x lhs <;>
                            simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                              __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                              native_teq, native_ite] at hProg
                          case Boolean b =>
                            cases b with
                            | false =>
                                simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                                  __eo_l_1___mk_cong_rhs, __eo_ite, hEq,
                                  native_teq, native_ite] at hProg
                            | true =>
                                rfl
                        have hStepEq :=
                          mk_cong_rhs_step_eq_of_eo_eq_true f x lhs tail
                            (premiseAndFormulaList ps) hCond
                        have hMkApplyNN :
                            __eo_mk_apply
                                (__mk_cong_rhs f (premiseAndFormulaList ps)) tail ≠
                              Term.Stuck := by
                          rw [← hStepEq]
                          exact hProg
                        have hRecNN :
                            __mk_cong_rhs f (premiseAndFormulaList ps) ≠
                              Term.Stuck :=
                          eo_mk_apply_left_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hTailNN : tail ≠ Term.Stuck :=
                          eo_mk_apply_right_ne_stuck_of_ne_stuck
                            (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                            hMkApplyNN
                        have hRec :=
                          ih f hRestBool hRecNN
                        have hLhs : lhs = x :=
                          eq_of_eo_eq_true x lhs hCond
                        subst lhs
                        change CongTypeSpine (Term.Apply f x)
                          (__mk_cong_rhs (Term.Apply f x)
                            (Term.Apply (Term.Apply (Term.UOp UserOp.and)
                              (mkEq x tail)) (premiseAndFormulaList ps)))
                        rw [hStepEq]
                        rw [eo_mk_apply_eq_of_ne_stuck
                          (__mk_cong_rhs f (premiseAndFormulaList ps)) tail
                          hRecNN hTailNN]
                        exact CongTypeSpine.app hRec hHeadBool
                    | _ =>
                        exact False.elim (hProg (by
                          simp [premiseAndFormulaList, mkEq, __mk_cong_rhs,
                            __eo_l_1___mk_cong_rhs]))
                  all_goals
                    exact False.elim (hProg (by
                      cases t <;>
                        simp [premiseAndFormulaList, __mk_cong_rhs,
                          __eo_l_1___mk_cong_rhs]))
              | _ =>
                  exact False.elim (hProg (by
                    cases t <;>
                      simp [premiseAndFormulaList, __mk_cong_rhs,
                        __eo_l_1___mk_cong_rhs]))
          | _ =>
              exact False.elim (hProg (by
                cases t <;>
                  simp [premiseAndFormulaList, __mk_cong_rhs,
                    __eo_l_1___mk_cong_rhs]))
      | _ =>
          exact False.elim (hProg (by
            cases t <;>
              simp [premiseAndFormulaList, __mk_cong_rhs,
                __eo_l_1___mk_cong_rhs]))

private theorem eo_prog_cong_pf_eq_of_ne_stuck (t E : Term) :
    t ≠ Term.Stuck ->
    __eo_prog_cong t (Proof.pf E) =
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_cong_rhs t (__eo_list_rev (Term.UOp UserOp.and) E)) := by
  intro ht
  cases t <;> simp [__eo_prog_cong] at ht ⊢

private theorem eo_typeof_eq_bool_operands_eq (A B : Term)
    (h : __eo_typeof_eq A B = Term.Bool) :
    A = B := by
  by_cases hA : A = Term.Stuck
  · subst A
    simp [__eo_typeof_eq] at h
  · by_cases hB : B = Term.Stuck
    · subst B
      simp [__eo_typeof_eq] at h
    · simp [__eo_typeof_eq, __eo_requires, __eo_eq, native_ite, native_teq,
        native_not] at h
      exact h.symm

private theorem mkEq_typeof_bool_operands_typeof_eq (x y : Term)
    (h : __eo_typeof (mkEq x y) = Term.Bool) :
  __eo_typeof x = __eo_typeof y := by
  change __eo_typeof_eq (__eo_typeof x) (__eo_typeof y) = Term.Bool at h
  exact eo_typeof_eq_bool_operands_eq (__eo_typeof x) (__eo_typeof y) h

private theorem congTrueSpine_not_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.not) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.not) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.not) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M UserOp.not x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp UserOp.not) x)
        (Term.Apply (Term.UOp UserOp.not) y) hEqBool
    have hxNotNN :
        __smtx_typeof (SmtTerm.not (__eo_to_smt x)) ≠ SmtType.None := by
      simpa using hTypes.2
    have hyNotNN :
        __smtx_typeof (SmtTerm.not (__eo_to_smt y)) ≠ SmtType.None := by
      rw [hTypes.1] at hTypes
      simpa using hTypes.2
    have hxBool :
        __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      smt_typeof_not_arg_bool_of_non_none (__eo_to_smt x) hxNotNN
    have hyBool :
        __smtx_typeof (__eo_to_smt y) = SmtType.Bool :=
      smt_typeof_not_arg_bool_of_non_none (__eo_to_smt y) hyNotNN
    have hEvalXY :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        SmtType.Bool hxBool hyBool (by simp) (by simp) hArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change __smtx_model_eval_eq
      (__smtx_model_eval M (SmtTerm.not (__eo_to_smt x)))
      (__smtx_model_eval M (SmtTerm.not (__eo_to_smt y))) =
        SmtValue.Boolean true
    rw [__smtx_model_eval.eq_6, __smtx_model_eval.eq_6]
    rw [hEvalXY]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

private theorem congTypeSpine_not_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.not) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.not) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.not) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_unary_uop_inv UserOp.not x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hxNotTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) x)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.not (__eo_to_smt x)) = SmtType.Bool
    have hxBool :
        __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      smt_typeof_not_arg_bool_of_non_none (__eo_to_smt x) (by
        change __smtx_typeof (SmtTerm.not (__eo_to_smt x)) ≠ SmtType.None
        exact hTrans)
    rw [typeof_not_eq, hxBool]
    simp [native_ite, native_Teq]
  have hxyType :
      __smtx_typeof (__eo_to_smt x) = __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hyNotTy :
      __smtx_typeof (__eo_to_smt (Term.Apply (Term.UOp UserOp.not) y)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.not (__eo_to_smt y)) = SmtType.Bool
    have hxBool :
        __smtx_typeof (__eo_to_smt x) = SmtType.Bool :=
      smt_typeof_not_arg_bool_of_non_none (__eo_to_smt x) (by
        change __smtx_typeof (SmtTerm.not (__eo_to_smt x)) ≠ SmtType.None
        exact hTrans)
    have hyBool :
        __smtx_typeof (__eo_to_smt y) = SmtType.Bool := by
      rw [← hxyType]
      exact hxBool
    rw [typeof_not_eq, hyBool]
    simp [native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp UserOp.not) x)
    (Term.Apply (Term.UOp UserOp.not) y)
    (by rw [hxNotTy, hyNotTy])
    (by rw [hxNotTy]; simp)

private theorem congTrueSpine_and_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M UserOp.and x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp UserOp.and) y₁) y₂) hEqBool
    have hxAndNN :
        __smtx_typeof (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
          SmtType.None := by
      simpa using hTypes.2
    rcases smt_typeof_and_args_bool_of_non_none
        (__eo_to_smt x₁) (__eo_to_smt x₂) hxAndNN with
      ⟨hx₁Bool, hx₂Bool⟩
    have hy₁Bool : __smtx_typeof (__eo_to_smt y₁) = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁Bool
    have hy₂Bool : __smtx_typeof (__eo_to_smt y₂) = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂Bool
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        SmtType.Bool hx₁Bool hy₁Bool (by simp) (by simp) hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        SmtType.Bool hx₂Bool hy₂Bool (by simp) (by simp) hArg₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    change __smtx_model_eval_eq
      (__smtx_model_eval M
        (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)))
      (__smtx_model_eval M
        (SmtTerm.and (__eo_to_smt y₁) (__eo_to_smt y₂))) =
        SmtValue.Boolean true
    rw [__smtx_model_eval.eq_8, __smtx_model_eval.eq_8]
    rw [hEval₁, hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

private theorem congTypeSpine_and_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv UserOp.and x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hxAndTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) =
      SmtType.Bool
    rcases smt_typeof_and_args_bool_of_non_none
        (__eo_to_smt x₁) (__eo_to_smt x₂) (by
          change __smtx_typeof
            (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠ SmtType.None
          exact hTrans) with
      ⟨hx₁Bool, hx₂Bool⟩
    rw [typeof_and_eq, hx₁Bool, hx₂Bool]
    simp [native_ite, native_Teq]
  have hx₁Bool : __smtx_typeof (__eo_to_smt x₁) = SmtType.Bool := by
    rcases smt_typeof_and_args_bool_of_non_none
        (__eo_to_smt x₁) (__eo_to_smt x₂) (by
          change __smtx_typeof
            (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠ SmtType.None
          exact hTrans) with
      ⟨h, _⟩
    exact h
  have hx₂Bool : __smtx_typeof (__eo_to_smt x₂) = SmtType.Bool := by
    rcases smt_typeof_and_args_bool_of_non_none
        (__eo_to_smt x₁) (__eo_to_smt x₂) (by
          change __smtx_typeof
            (SmtTerm.and (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠ SmtType.None
          exact hTrans) with
      ⟨_, h⟩
    exact h
  have hy₁Bool : __smtx_typeof (__eo_to_smt y₁) = SmtType.Bool := by
    rw [← smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁]
    exact hx₁Bool
  have hy₂Bool : __smtx_typeof (__eo_to_smt y₂) = SmtType.Bool := by
    rw [← smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂]
    exact hx₂Bool
  have hyAndTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp UserOp.and) y₁) y₂)) =
        SmtType.Bool := by
    change __smtx_typeof (SmtTerm.and (__eo_to_smt y₁) (__eo_to_smt y₂)) =
      SmtType.Bool
    rw [typeof_and_eq, hy₁Bool, hy₂Bool]
    simp [native_ite, native_Teq]
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UOp UserOp.and) y₁) y₂)
    (by rw [hxAndTy, hyAndTy])
    (by rw [hxAndTy]; simp)

private theorem congTrueSpine_bool_binop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hArgsOfNN :
      ∀ a b,
        __smtx_typeof (smtOp a b) ≠ SmtType.None ->
          __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
          SmtType.None := by
      rw [← hToSmt x₁ x₂]
      exact hTypes.2
    rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
      ⟨hx₁Bool, hx₂Bool⟩
    have hy₁Bool : __smtx_typeof (__eo_to_smt y₁) = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁Bool
    have hy₂Bool : __smtx_typeof (__eo_to_smt y₂) = SmtType.Bool := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂Bool
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        SmtType.Bool hx₁Bool hy₁Bool (by simp) (by simp) hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        SmtType.Bool hx₂Bool hy₂Bool (by simp) (by simp) hArg₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    rw [hEval, hEval]
    rw [hEval₁, hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

private theorem congTypeSpine_bool_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hArgsOfNN :
      ∀ a b,
        __smtx_typeof (smtOp a b) ≠ SmtType.None ->
          __smtx_typeof a = SmtType.Bool ∧ __smtx_typeof b = SmtType.Bool)
    (hTypeBool :
      ∀ a b,
        __smtx_typeof a = SmtType.Bool ->
        __smtx_typeof b = SmtType.Bool ->
        __smtx_typeof (smtOp a b) = SmtType.Bool)
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hxOpNN :
      __smtx_typeof (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
        SmtType.None := by
    rw [← hToSmt x₁ x₂]
    exact hTrans
  rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
    ⟨hx₁Bool, hx₂Bool⟩
  have hy₁Bool : __smtx_typeof (__eo_to_smt y₁) = SmtType.Bool := by
    rw [← smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁]
    exact hx₁Bool
  have hy₂Bool : __smtx_typeof (__eo_to_smt y₂) = SmtType.Bool := by
    rw [← smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂]
    exact hx₂Bool
  have hxOpTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)) =
        SmtType.Bool := by
    rw [hToSmt]
    exact hTypeBool (__eo_to_smt x₁) (__eo_to_smt x₂) hx₁Bool hx₂Bool
  have hyOpTy :
      __smtx_typeof
        (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)) =
        SmtType.Bool := by
    rw [hToSmt]
    exact hTypeBool (__eo_to_smt y₁) (__eo_to_smt y₂) hy₁Bool hy₂Bool
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)
    (by rw [hxOpTy, hyOpTy])
    (by rw [hxOpTy]; simp)

private theorem congTrueSpine_non_reg_unop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hArgOfNN :
      ∀ a,
        __smtx_typeof (smtOp a) ≠ SmtType.None ->
          ∃ A,
            __smtx_typeof a = A ∧
              A ≠ SmtType.None ∧ A ≠ SmtType.RegLan)
    (hEval :
      ∀ a,
        __smtx_model_eval M (smtOp a) =
          evalOp (__smtx_model_eval M a))
    (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp eoOp) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_unary_uop_inv M eoOp x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.UOp eoOp) x)
        (Term.Apply (Term.UOp eoOp) y) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x)) ≠ SmtType.None := by
      rw [← hToSmt x]
      exact hTypes.2
    rcases hArgOfNN (__eo_to_smt x) hxOpNN with
      ⟨A, hxA, hANN, hAReg⟩
    have hyA : __smtx_typeof (__eo_to_smt y) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x y hArg]
      exact hxA
    have hEvalArg :
        __smtx_model_eval M (__eo_to_smt x) =
          __smtx_model_eval M (__eo_to_smt y) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x y
        A hxA hyA hANN hAReg hArg
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x, hToSmt y]
    rw [hEval, hEval]
    rw [hEvalArg]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

private theorem congTypeSpine_typecongr_unop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a,
        __eo_to_smt (Term.Apply (Term.UOp eoOp) a) =
          smtOp (__eo_to_smt a))
    (hTypeCong :
      ∀ a b,
        __smtx_typeof a = __smtx_typeof b ->
          __smtx_typeof (smtOp a) = __smtx_typeof (smtOp b))
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp eoOp) x) ->
    CongTypeSpine (Term.Apply (Term.UOp eoOp) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp eoOp) x) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_unary_uop_inv eoOp x rhs hSpine with
    ⟨y, hRhs, hArg⟩
  subst hRhs
  have hArgTy :
      __smtx_typeof (__eo_to_smt x) =
        __smtx_typeof (__eo_to_smt y) :=
    smt_type_eq_of_eq_bool_or_same x y hArg
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp eoOp) x)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.UOp eoOp) y)) := by
    rw [hToSmt x, hToSmt y]
    exact hTypeCong (__eo_to_smt x) (__eo_to_smt y) hArgTy
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.UOp eoOp) x)
    (Term.Apply (Term.UOp eoOp) y)
    hOpTy
    hTrans

private theorem congTrueSpine_non_reg_binop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hArgsOfNN :
      ∀ a b,
        __smtx_typeof (smtOp a b) ≠ SmtType.None ->
          ∃ A B,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan)
    (hEval :
      ∀ a b,
        __smtx_model_eval M (smtOp a b) =
          evalOp (__smtx_model_eval M a) (__smtx_model_eval M b))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_binary_uop_inv M eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
        (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) hEqBool
    have hxOpNN :
        __smtx_typeof (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂)) ≠
          SmtType.None := by
      rw [← hToSmt x₁ x₂]
      exact hTypes.2
    rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) hxOpNN with
      ⟨A, B, hx₁A, hx₂B, hANN, hBNN, hAReg, hBReg⟩
    have hy₁A : __smtx_typeof (__eo_to_smt y₁) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁A
    have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂B
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        A hx₁A hy₁A hANN hAReg hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        B hx₂B hy₂B hBNN hBReg hArg₂
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    rw [hEval, hEval]
    rw [hEval₁, hEval₂]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

private theorem congTypeSpine_typecongr_binop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b,
        __eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) =
          smtOp (__eo_to_smt a) (__eo_to_smt b))
    (hTypeCong :
      ∀ a b a' b',
        __smtx_typeof a = __smtx_typeof a' ->
        __smtx_typeof b = __smtx_typeof b' ->
          __smtx_typeof (smtOp a b) = __smtx_typeof (smtOp a' b'))
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_binary_uop_inv eoOp x₁ x₂ rhs hSpine with
    ⟨y₁, y₂, hRhs, hArg₁, hArg₂⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)) =
        __smtx_typeof
          (__eo_to_smt (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)) := by
    rw [hToSmt x₁ x₂, hToSmt y₁ y₂]
    exact hTypeCong (__eo_to_smt x₁) (__eo_to_smt x₂)
      (__eo_to_smt y₁) (__eo_to_smt y₂) hArgTy₁ hArgTy₂
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂)
    (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂)
    hOpTy
    hTrans

private theorem congTrueSpine_non_reg_ternop_eq_true
    (M : SmtModel) (hM : model_total_typed M)
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (evalOp : SmtValue -> SmtValue -> SmtValue -> SmtValue)
    (hToSmt :
      ∀ a b c,
        __eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) c) =
          smtOp (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c))
    (hArgsOfNN :
      ∀ a b c,
        __smtx_typeof (smtOp a b c) ≠ SmtType.None ->
          ∃ A B C,
            __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
              __smtx_typeof c = C ∧
              A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
              C ≠ SmtType.None ∧
              A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan ∧
              C ≠ SmtType.RegLan)
    (hEval :
      ∀ a b c,
        __smtx_model_eval M (smtOp a b c) =
          evalOp (__smtx_model_eval M a)
            (__smtx_model_eval M b) (__smtx_model_eval M c))
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
      rhs ->
    eo_interprets M
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        rhs) true := by
  intro hEqBool hSpine
  rcases congTrueSpine_ternary_uop_inv M eoOp x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  apply RuleProofs.eo_interprets_eq_of_rel M
  · exact hEqBool
  · have hTypes :=
      RuleProofs.eo_eq_operands_same_smt_type_of_has_bool_type
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) y₃)
        hEqBool
    have hxOpNN :
        __smtx_typeof
            (smtOp (__eo_to_smt x₁) (__eo_to_smt x₂) (__eo_to_smt x₃)) ≠
          SmtType.None := by
      rw [← hToSmt x₁ x₂ x₃]
      exact hTypes.2
    rcases hArgsOfNN (__eo_to_smt x₁) (__eo_to_smt x₂) (__eo_to_smt x₃)
        hxOpNN with
      ⟨A, B, C, hx₁A, hx₂B, hx₃C, hANN, hBNN, hCNN,
        hAReg, hBReg, hCReg⟩
    have hy₁A : __smtx_typeof (__eo_to_smt y₁) = A := by
      rw [← smt_type_eq_of_eq_true_or_same M x₁ y₁ hArg₁]
      exact hx₁A
    have hy₂B : __smtx_typeof (__eo_to_smt y₂) = B := by
      rw [← smt_type_eq_of_eq_true_or_same M x₂ y₂ hArg₂]
      exact hx₂B
    have hy₃C : __smtx_typeof (__eo_to_smt y₃) = C := by
      rw [← smt_type_eq_of_eq_true_or_same M x₃ y₃ hArg₃]
      exact hx₃C
    have hEval₁ :
        __smtx_model_eval M (__eo_to_smt x₁) =
          __smtx_model_eval M (__eo_to_smt y₁) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₁ y₁
        A hx₁A hy₁A hANN hAReg hArg₁
    have hEval₂ :
        __smtx_model_eval M (__eo_to_smt x₂) =
          __smtx_model_eval M (__eo_to_smt y₂) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₂ y₂
        B hx₂B hy₂B hBNN hBReg hArg₂
    have hEval₃ :
        __smtx_model_eval M (__eo_to_smt x₃) =
          __smtx_model_eval M (__eo_to_smt y₃) :=
      eo_model_eval_eq_of_eq_true_or_same_at_non_reglan_type M hM x₃ y₃
        C hx₃C hy₃C hCNN hCReg hArg₃
    rw [RuleProofs.smt_value_rel_iff_model_eval_eq_true]
    rw [hToSmt x₁ x₂ x₃, hToSmt y₁ y₂ y₃]
    rw [hEval, hEval]
    rw [hEval₁, hEval₂, hEval₃]
    exact (RuleProofs.smt_value_rel_iff_model_eval_eq_true _ _).mp
      (RuleProofs.smt_value_rel_refl _)

private theorem congTypeSpine_typecongr_ternop_eq_has_bool_type
    (eoOp : UserOp) (smtOp : SmtTerm -> SmtTerm -> SmtTerm -> SmtTerm)
    (hToSmt :
      ∀ a b c,
        __eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) a) b) c) =
          smtOp (__eo_to_smt a) (__eo_to_smt b) (__eo_to_smt c))
    (hTypeCong :
      ∀ a b c a' b' c',
        __smtx_typeof a = __smtx_typeof a' ->
        __smtx_typeof b = __smtx_typeof b' ->
        __smtx_typeof c = __smtx_typeof c' ->
          __smtx_typeof (smtOp a b c) =
            __smtx_typeof (smtOp a' b' c'))
    (x₁ x₂ x₃ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
      rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq
        (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
        rhs) := by
  intro hTrans hSpine
  rcases congTypeSpine_ternary_uop_inv eoOp x₁ x₂ x₃ rhs hSpine with
    ⟨y₁, y₂, y₃, hRhs, hArg₁, hArg₂, hArg₃⟩
  subst hRhs
  have hArgTy₁ :
      __smtx_typeof (__eo_to_smt x₁) =
        __smtx_typeof (__eo_to_smt y₁) :=
    smt_type_eq_of_eq_bool_or_same x₁ y₁ hArg₁
  have hArgTy₂ :
      __smtx_typeof (__eo_to_smt x₂) =
        __smtx_typeof (__eo_to_smt y₂) :=
    smt_type_eq_of_eq_bool_or_same x₂ y₂ hArg₂
  have hArgTy₃ :
      __smtx_typeof (__eo_to_smt x₃) =
        __smtx_typeof (__eo_to_smt y₃) :=
    smt_type_eq_of_eq_bool_or_same x₃ y₃ hArg₃
  have hOpTy :
      __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)) =
        __smtx_typeof
          (__eo_to_smt
            (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) y₃)) := by
    rw [hToSmt x₁ x₂ x₃, hToSmt y₁ y₂ y₃]
    exact hTypeCong (__eo_to_smt x₁) (__eo_to_smt x₂) (__eo_to_smt x₃)
      (__eo_to_smt y₁) (__eo_to_smt y₂) (__eo_to_smt y₃)
      hArgTy₁ hArgTy₂ hArgTy₃
  exact RuleProofs.eo_has_bool_type_eq_of_same_smt_type
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) x₁) x₂) x₃)
    (Term.Apply (Term.Apply (Term.Apply (Term.UOp eoOp) y₁) y₂) y₃)
    hOpTy
    hTrans

private theorem congTrueSpine_or_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs) true :=
  congTrueSpine_bool_binop_eq_true M hM UserOp.or SmtTerm.or
    __smtx_model_eval_or
    (by intro a b; rfl)
    smt_typeof_or_args_bool_of_non_none
    (by intro a b; rw [__smtx_model_eval.eq_7])
    x₁ x₂ rhs

private theorem congTypeSpine_or_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.or) x₁) x₂) rhs) :=
  congTypeSpine_bool_binop_eq_has_bool_type UserOp.or SmtTerm.or
    (by intro a b; rfl)
    smt_typeof_or_args_bool_of_non_none
    (by
      intro a b ha hb
      rw [typeof_or_eq, ha, hb]
      simp [native_ite, native_Teq])
    x₁ x₂ rhs

private theorem congTrueSpine_imp_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs) true :=
  congTrueSpine_bool_binop_eq_true M hM UserOp.imp SmtTerm.imp
    __smtx_model_eval_imp
    (by intro a b; rfl)
    smt_typeof_imp_args_bool_of_non_none
    (by intro a b; rw [__smtx_model_eval.eq_9])
    x₁ x₂ rhs

private theorem congTypeSpine_imp_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.imp) x₁) x₂) rhs) :=
  congTypeSpine_bool_binop_eq_has_bool_type UserOp.imp SmtTerm.imp
    (by intro a b; rfl)
    smt_typeof_imp_args_bool_of_non_none
    (by
      intro a b ha hb
      rw [typeof_imp_eq, ha, hb]
      simp [native_ite, native_Teq])
    x₁ x₂ rhs

private theorem congTrueSpine_xor_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs) true :=
  congTrueSpine_bool_binop_eq_true M hM UserOp.xor SmtTerm.xor
    __smtx_model_eval_xor
    (by intro a b; rfl)
    smt_typeof_xor_args_bool_of_non_none
    (by intro a b; rw [__smtx_model_eval.eq_10])
    x₁ x₂ rhs

private theorem congTypeSpine_xor_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.xor) x₁) x₂) rhs) :=
  congTypeSpine_bool_binop_eq_has_bool_type UserOp.xor SmtTerm.xor
    (by intro a b; rfl)
    smt_typeof_xor_args_bool_of_non_none
    (by
      intro a b ha hb
      rw [typeof_xor_eq, ha, hb]
      simp [native_ite, native_Teq])
    x₁ x₂ rhs

private theorem arith_overload_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2
            (__smtx_typeof a) (__smtx_typeof b))
    (a b : SmtTerm) :
    __smtx_typeof (op a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases arith_binop_args_of_non_none (op := op) (hTy a b) hTerm with
    hInt | hReal
  · exact ⟨SmtType.Int, SmtType.Int, hInt.1, hInt.2,
      by simp, by simp, by simp, by simp⟩
  · exact ⟨SmtType.Real, SmtType.Real, hReal.1, hReal.2,
      by simp, by simp, by simp, by simp⟩

private theorem arith_overload_ret_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          __smtx_typeof_arith_overload_op_2_ret
            (__smtx_typeof a) (__smtx_typeof b) R)
    (a b : SmtTerm) :
    __smtx_typeof (op a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    exact hNN
  rcases arith_binop_ret_args_of_non_none (op := op) (R := R)
      (hTy a b) hTerm with
    hInt | hReal
  · exact ⟨SmtType.Int, SmtType.Int, hInt.1, hInt.2,
      by simp, by simp, by simp, by simp⟩
  · exact ⟨SmtType.Real, SmtType.Real, hReal.1, hReal.2,
      by simp, by simp, by simp, by simp⟩

private theorem int_binop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a b,
        __smtx_typeof (op a b) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Int)
            (native_ite (native_Teq (__smtx_typeof b) SmtType.Int)
              R SmtType.None)
            SmtType.None)
    (a b : SmtTerm) :
    __smtx_typeof (op a b) ≠ SmtType.None ->
      ∃ A B,
        __smtx_typeof a = A ∧ __smtx_typeof b = B ∧
          A ≠ SmtType.None ∧ B ≠ SmtType.None ∧
          A ≠ SmtType.RegLan ∧ B ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a b) := by
    unfold term_has_non_none_type
    exact hNN
  have hArgs := int_binop_args_of_non_none (op := op) (R := R)
    (hTy a b) hTerm
  exact ⟨SmtType.Int, SmtType.Int, hArgs.1, hArgs.2,
    by simp, by simp, by simp, by simp⟩

private theorem arith_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          __smtx_typeof_arith_overload_op_1 (__smtx_typeof a))
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases arith_unop_arg_of_non_none (op := op) (hTy a) hTerm with
    hInt | hReal
  · exact ⟨SmtType.Int, hInt, by simp, by simp⟩
  · exact ⟨SmtType.Real, hReal, by simp, by simp⟩

private theorem int_ret_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Int)
            R SmtType.None)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  have hArg := int_ret_arg_of_non_none (op := op) (R := R)
    (hTy a) hTerm
  exact ⟨SmtType.Int, hArg, by simp, by simp⟩

private theorem real_ret_unop_args_non_reg_of_non_none
    (op : SmtTerm -> SmtTerm)
    (R : SmtType)
    (hTy :
      ∀ a,
        __smtx_typeof (op a) =
          native_ite (native_Teq (__smtx_typeof a) SmtType.Real)
            R SmtType.None)
    (a : SmtTerm) :
    __smtx_typeof (op a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (op a) := by
    unfold term_has_non_none_type
    exact hNN
  have hArg := real_arg_of_non_none (op := op) (Tout := R)
    (hTy a) hTerm
  exact ⟨SmtType.Real, hArg, by simp, by simp⟩

private theorem to_real_args_non_reg_of_non_none
    (a : SmtTerm) :
    __smtx_typeof (SmtTerm.to_real a) ≠ SmtType.None ->
      ∃ A,
        __smtx_typeof a = A ∧
          A ≠ SmtType.None ∧ A ≠ SmtType.RegLan := by
  intro hNN
  have hTerm : term_has_non_none_type (SmtTerm.to_real a) := by
    unfold term_has_non_none_type
    exact hNN
  rcases to_real_arg_of_non_none hTerm with hInt | hReal
  · exact ⟨SmtType.Int, hInt, by simp, by simp⟩
  · exact ⟨SmtType.Real, hReal, by simp, by simp⟩

private noncomputable abbrev smtEvalDiv
    (M : SmtModel) (x₁ x₂ : SmtValue) : SmtValue :=
  let _v0 := x₂
  let _v1 := x₁
  __smtx_model_eval_ite
    (__smtx_model_eval_eq _v0 (SmtValue.Numeral 0))
    (__smtx_model_eval_apply
      (__smtx_model_lookup M native_div_by_zero_id
        (SmtType.FunType SmtType.Int SmtType.Int))
      _v1)
    (__smtx_model_eval_div_total _v1 _v0)

private noncomputable abbrev smtEvalMod
    (M : SmtModel) (x₁ x₂ : SmtValue) : SmtValue :=
  let _v0 := x₂
  let _v1 := x₁
  __smtx_model_eval_ite
    (__smtx_model_eval_eq _v0 (SmtValue.Numeral 0))
    (__smtx_model_eval_apply
      (__smtx_model_lookup M native_mod_by_zero_id
        (SmtType.FunType SmtType.Int SmtType.Int))
      _v1)
    (__smtx_model_eval_mod_total _v1 _v0)

private noncomputable abbrev smtEvalMultmult
    (M : SmtModel) (x₁ x₂ : SmtValue) : SmtValue :=
  let _v0 := x₂
  let _v1 := SmtValue.Numeral 0
  let _v2 := x₁
  let _v3 := SmtValue.Numeral 1
  __smtx_model_eval_ite
    (__smtx_model_eval_geq _v0 _v1)
    (__smtx_model_eval_multmult_total _v2 _v0)
    (__smtx_model_eval_ite
      (__smtx_model_eval_eq _v2 _v1)
      (__smtx_model_eval_apply
        (__smtx_model_lookup M native_div_by_zero_id
          (SmtType.FunType SmtType.Int SmtType.Int))
        _v3)
      (__smtx_model_eval_div_total _v3
        (__smtx_model_eval_multmult_total _v2
          (__smtx_model_eval__ _v1 _v0))))

private theorem congTrueSpine_plus_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.plus SmtTerm.plus
    __smtx_model_eval_plus
    (by intro a b; rfl)
    (arith_overload_binop_args_non_reg_of_non_none SmtTerm.plus
      (by intro a b; exact typeof_plus_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_11])
    x₁ x₂ rhs

private theorem congTypeSpine_plus_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.plus) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.plus SmtTerm.plus
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_plus_eq, typeof_plus_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_neg_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.neg SmtTerm.neg
    __smtx_model_eval__
    (by intro a b; rfl)
    (arith_overload_binop_args_non_reg_of_non_none SmtTerm.neg
      (by intro a b; exact typeof_neg_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_12])
    x₁ x₂ rhs

private theorem congTypeSpine_neg_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.neg) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.neg SmtTerm.neg
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_neg_eq, typeof_neg_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_mult_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.mult SmtTerm.mult
    __smtx_model_eval_mult
    (by intro a b; rfl)
    (arith_overload_binop_args_non_reg_of_non_none SmtTerm.mult
      (by intro a b; exact typeof_mult_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_13])
    x₁ x₂ rhs

private theorem congTypeSpine_mult_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mult) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.mult SmtTerm.mult
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_mult_eq, typeof_mult_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_lt_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.lt SmtTerm.lt
    __smtx_model_eval_lt
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.lt SmtType.Bool
      (by intro a b; exact typeof_lt_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_14])
    x₁ x₂ rhs

private theorem congTypeSpine_lt_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.lt) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.lt SmtTerm.lt
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_lt_eq, typeof_lt_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_leq_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.leq SmtTerm.leq
    __smtx_model_eval_leq
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.leq SmtType.Bool
      (by intro a b; exact typeof_leq_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_15])
    x₁ x₂ rhs

private theorem congTypeSpine_leq_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.leq) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.leq SmtTerm.leq
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_leq_eq, typeof_leq_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_gt_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.gt SmtTerm.gt
    __smtx_model_eval_gt
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.gt SmtType.Bool
      (by intro a b; exact typeof_gt_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_16])
    x₁ x₂ rhs

private theorem congTypeSpine_gt_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.gt) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.gt SmtTerm.gt
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_gt_eq, typeof_gt_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_geq_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.geq SmtTerm.geq
    __smtx_model_eval_geq
    (by intro a b; rfl)
    (arith_overload_ret_binop_args_non_reg_of_non_none SmtTerm.geq SmtType.Bool
      (by intro a b; exact typeof_geq_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_17])
    x₁ x₂ rhs

private theorem congTypeSpine_geq_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.geq) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.geq SmtTerm.geq
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_geq_eq, typeof_geq_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_to_real_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.to_real) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.to_real) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.to_real) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.to_real SmtTerm.to_real
    __smtx_model_eval_to_real
    (by intro a; rfl)
    to_real_args_non_reg_of_non_none
    (by intro a; rw [__smtx_model_eval.eq_18])
    x rhs

private theorem congTypeSpine_to_real_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.to_real) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.to_real) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.to_real) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.to_real SmtTerm.to_real
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_to_real_eq, typeof_to_real_eq, h])
    x rhs

private theorem congTrueSpine_to_int_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.to_int) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.to_int) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.to_int) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.to_int SmtTerm.to_int
    __smtx_model_eval_to_int
    (by intro a; rfl)
    (real_ret_unop_args_non_reg_of_non_none SmtTerm.to_int SmtType.Int
      (by intro a; exact typeof_to_int_eq a))
    (by intro a; rw [__smtx_model_eval.eq_19])
    x rhs

private theorem congTypeSpine_to_int_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.to_int) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.to_int) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.to_int) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.to_int SmtTerm.to_int
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_to_int_eq, typeof_to_int_eq, h])
    x rhs

private theorem congTrueSpine_is_int_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.is_int) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.is_int) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.is_int) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.is_int SmtTerm.is_int
    __smtx_model_eval_is_int
    (by intro a; rfl)
    (real_ret_unop_args_non_reg_of_non_none SmtTerm.is_int SmtType.Bool
      (by intro a; exact typeof_is_int_eq a))
    (by intro a; rw [__smtx_model_eval.eq_20])
    x rhs

private theorem congTypeSpine_is_int_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.is_int) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.is_int) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.is_int) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.is_int SmtTerm.is_int
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_is_int_eq, typeof_is_int_eq, h])
    x rhs

private theorem congTrueSpine_abs_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.abs) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.abs) x) rhs ->
    eo_interprets M (mkEq (Term.Apply (Term.UOp UserOp.abs) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.abs SmtTerm.abs
    __smtx_model_eval_abs
    (by intro a; rfl)
    (int_ret_unop_args_non_reg_of_non_none SmtTerm.abs SmtType.Int
      (by intro a; exact typeof_abs_eq a))
    (by intro a; rw [__smtx_model_eval.eq_21])
    x rhs

private theorem congTypeSpine_abs_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation (Term.Apply (Term.UOp UserOp.abs) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.abs) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.abs) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.abs SmtTerm.abs
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_abs_eq, typeof_abs_eq, h])
    x rhs

private theorem congTrueSpine_uneg_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.__eoo_neg_2 SmtTerm.uneg
    __smtx_model_eval_uneg
    (by intro a; rfl)
    (arith_unop_args_non_reg_of_non_none SmtTerm.uneg
      (by intro a; exact typeof_uneg_eq a))
    (by intro a; rw [__smtx_model_eval.eq_22])
    x rhs

private theorem congTypeSpine_uneg_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.__eoo_neg_2) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.__eoo_neg_2 SmtTerm.uneg
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_uneg_eq, typeof_uneg_eq, h])
    x rhs

private theorem congTrueSpine_div_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.div SmtTerm.div
    (smtEvalDiv M)
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.div SmtType.Int
      (by intro a b; exact typeof_div_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_23])
    x₁ x₂ rhs

private theorem congTypeSpine_div_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.div SmtTerm.div
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_div_eq, typeof_div_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_mod_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.mod SmtTerm.mod
    (smtEvalMod M)
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.mod SmtType.Int
      (by intro a b; exact typeof_mod_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_24])
    x₁ x₂ rhs

private theorem congTypeSpine_mod_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.mod SmtTerm.mod
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_mod_eq, typeof_mod_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_multmult_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.multmult SmtTerm.multmult
    (smtEvalMultmult M)
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.multmult SmtType.Int
      (by intro a b; exact typeof_multmult_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_25])
    x₁ x₂ rhs

private theorem congTypeSpine_multmult_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.multmult) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.multmult SmtTerm.multmult
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_multmult_eq, typeof_multmult_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_div_total_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.div_total SmtTerm.div_total
    __smtx_model_eval_div_total
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.div_total SmtType.Int
      (by intro a b; exact typeof_div_total_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_29])
    x₁ x₂ rhs

private theorem congTypeSpine_div_total_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.div_total) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.div_total SmtTerm.div_total
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_div_total_eq, typeof_div_total_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_mod_total_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.mod_total SmtTerm.mod_total
    __smtx_model_eval_mod_total
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.mod_total SmtType.Int
      (by intro a b; exact typeof_mod_total_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_30])
    x₁ x₂ rhs

private theorem congTypeSpine_mod_total_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.mod_total) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.mod_total SmtTerm.mod_total
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_mod_total_eq, typeof_mod_total_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_multmult_total_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.multmult_total
    SmtTerm.multmult_total
    __smtx_model_eval_multmult_total
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.multmult_total SmtType.Int
      (by intro a b; exact typeof_multmult_total_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_31])
    x₁ x₂ rhs

private theorem congTypeSpine_multmult_total_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.multmult_total) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.multmult_total
    SmtTerm.multmult_total
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_multmult_total_eq, typeof_multmult_total_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_divisible_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs) ->
    CongTrueSpine M
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs) true :=
  congTrueSpine_non_reg_binop_eq_true M hM UserOp.divisible SmtTerm.divisible
    __smtx_model_eval_divisible
    (by intro a b; rfl)
    (int_binop_args_non_reg_of_non_none SmtTerm.divisible SmtType.Bool
      (by intro a b; exact typeof_divisible_eq a b))
    (by intro a b; rw [__smtx_model_eval.eq_26])
    x₁ x₂ rhs

private theorem congTypeSpine_divisible_eq_has_bool_type
    (x₁ x₂ rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) ->
    CongTypeSpine
      (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.Apply (Term.UOp UserOp.divisible) x₁) x₂) rhs) :=
  congTypeSpine_typecongr_binop_eq_has_bool_type UserOp.divisible SmtTerm.divisible
    (by intro a b; rfl)
    (by
      intro a b a' b' ha hb
      rw [typeof_divisible_eq, typeof_divisible_eq, ha, hb])
    x₁ x₂ rhs

private theorem congTrueSpine_int_pow2_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.int_pow2 SmtTerm.int_pow2
    __smtx_model_eval_int_pow2
    (by intro a; rfl)
    (int_ret_unop_args_non_reg_of_non_none SmtTerm.int_pow2 SmtType.Int
      (by intro a; exact typeof_int_pow2_eq a))
    (by intro a; rw [__smtx_model_eval.eq_27])
    x rhs

private theorem congTypeSpine_int_pow2_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.int_pow2) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_pow2) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.int_pow2 SmtTerm.int_pow2
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_int_pow2_eq, typeof_int_pow2_eq, h])
    x rhs

private theorem congTrueSpine_int_log2_eq_true
    (M : SmtModel) (hM : model_total_typed M) (x rhs : Term) :
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_log2) x) rhs) ->
    CongTrueSpine M (Term.Apply (Term.UOp UserOp.int_log2) x) rhs ->
    eo_interprets M
      (mkEq (Term.Apply (Term.UOp UserOp.int_log2) x) rhs) true :=
  congTrueSpine_non_reg_unop_eq_true M hM UserOp.int_log2 SmtTerm.int_log2
    __smtx_model_eval_int_log2
    (by intro a; rfl)
    (int_ret_unop_args_non_reg_of_non_none SmtTerm.int_log2 SmtType.Int
      (by intro a; exact typeof_int_log2_eq a))
    (by intro a; rw [__smtx_model_eval.eq_28])
    x rhs

private theorem congTypeSpine_int_log2_eq_has_bool_type
    (x rhs : Term) :
    RuleProofs.eo_has_smt_translation
      (Term.Apply (Term.UOp UserOp.int_log2) x) ->
    CongTypeSpine (Term.Apply (Term.UOp UserOp.int_log2) x) rhs ->
    RuleProofs.eo_has_bool_type
      (mkEq (Term.Apply (Term.UOp UserOp.int_log2) x) rhs) :=
  congTypeSpine_typecongr_unop_eq_has_bool_type UserOp.int_log2 SmtTerm.int_log2
    (by intro a; rfl)
    (by
      intro a b h
      rw [typeof_int_log2_eq, typeof_int_log2_eq, h])
    x rhs

/--
The remaining typing core for congruence: once the generated program has been
reduced to a spine of congruent applications, the equality between the original
spine and the rewritten spine is Boolean.
-/
private axiom congTypeSpine_eq_has_bool_type (t rhs : Term) :
  RuleProofs.eo_has_smt_translation t ->
  CongTypeSpine t rhs ->
  __eo_typeof (mkEq t rhs) = Term.Bool ->
  RuleProofs.eo_has_bool_type (mkEq t rhs)

/--
The remaining semantic core for congruence: a syntactic congruence spine
preserves SMT equality in a total typed model.
-/
private axiom congTrueSpine_eq_true
    (M : SmtModel) (hM : model_total_typed M) (t rhs : Term) :
  RuleProofs.eo_has_bool_type (mkEq t rhs) ->
  CongTrueSpine M t rhs ->
  eo_interprets M (mkEq t rhs) true

/-- Typing for the generated EO implementation of `cong` over a premise list. -/
theorem typed___eo_prog_cong_impl (t : Term) (premises : List Term) :
  RuleProofs.eo_has_smt_translation t ->
  AllHaveBoolType premises ->
  __eo_prog_cong t (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  __eo_typeof (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) =
    Term.Bool ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) := by
  intro hTrans hPremisesBool hProg hProgType
  have htNN : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTrans
  let rhs := __mk_cong_rhs t (premiseAndFormulaList premises.reverse)
  have hProgEq :=
    eo_prog_cong_pf_eq_of_ne_stuck t (premiseAndFormulaList premises) htNN
  have hProgNN :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs ≠ Term.Stuck := by
    change
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_cong_rhs t (premiseAndFormulaList premises.reverse)) ≠
        Term.Stuck
    rw [← eo_list_rev_and_premiseAndFormulaList premises]
    rw [← hProgEq]
    exact hProg
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) rhs hProgNN
  have hSpine :
      CongTypeSpine t rhs := by
    simpa [rhs] using
      mk_cong_rhs_congTypeSpine_of_list premises.reverse t
        (all_have_bool_type_reverse premises hPremisesBool) hRhsNN
  have hMkEqType : __eo_typeof (mkEq t rhs) = Term.Bool := by
    have hProgType' := hProgType
    rw [hProgEq] at hProgType'
    rw [eo_list_rev_and_premiseAndFormulaList] at hProgType'
    change __eo_typeof
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs) = Term.Bool
      at hProgType'
    rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
      (by simp) hRhsNN] at hProgType'
    exact hProgType'
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs) :=
    congTypeSpine_eq_has_bool_type t rhs hTrans hSpine hMkEqType
  rw [hProgEq]
  rw [eo_list_rev_and_premiseAndFormulaList]
  change RuleProofs.eo_has_bool_type
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs)
  rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
    (by simp) hRhsNN]
  exact hEqBool

/-- Correctness for the generated EO implementation of `cong` over a premise list. -/
theorem facts___eo_prog_cong_impl
    (M : SmtModel) (hM : model_total_typed M) (t : Term)
    (premises : List Term) :
  RuleProofs.eo_has_smt_translation t ->
  AllInterpretedTrue M premises ->
  RuleProofs.eo_has_bool_type
    (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) ->
  __eo_prog_cong t (Proof.pf (premiseAndFormulaList premises)) ≠ Term.Stuck ->
  eo_interprets M
    (__eo_prog_cong t (Proof.pf (premiseAndFormulaList premises))) true := by
  intro hTrans hPremisesTrue hProgBool hProg
  have htNN : t ≠ Term.Stuck :=
    RuleProofs.term_ne_stuck_of_has_smt_translation t hTrans
  let rhs := __mk_cong_rhs t (premiseAndFormulaList premises.reverse)
  have hProgEq :=
    eo_prog_cong_pf_eq_of_ne_stuck t (premiseAndFormulaList premises) htNN
  have hProgNN :
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs ≠ Term.Stuck := by
    change
      __eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t)
        (__mk_cong_rhs t (premiseAndFormulaList premises.reverse)) ≠
        Term.Stuck
    rw [← eo_list_rev_and_premiseAndFormulaList premises]
    rw [← hProgEq]
    exact hProg
  have hRhsNN : rhs ≠ Term.Stuck :=
    eo_mk_apply_right_ne_stuck_of_ne_stuck
      (Term.Apply (Term.UOp UserOp.eq) t) rhs hProgNN
  have hSpine :
      CongTrueSpine M t rhs := by
    simpa [rhs] using
      mk_cong_rhs_congTrueSpine_of_list M premises.reverse t
        (all_interpreted_true_reverse M premises hPremisesTrue) hRhsNN
  have hEqBool : RuleProofs.eo_has_bool_type (mkEq t rhs) := by
    have hProgBool' := hProgBool
    rw [hProgEq] at hProgBool'
    rw [eo_list_rev_and_premiseAndFormulaList] at hProgBool'
    change RuleProofs.eo_has_bool_type
      (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs)
      at hProgBool'
    rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
      (by simp) hRhsNN] at hProgBool'
    exact hProgBool'
  have hEqTrue : eo_interprets M (mkEq t rhs) true :=
    congTrueSpine_eq_true M hM t rhs hEqBool hSpine
  rw [hProgEq]
  rw [eo_list_rev_and_premiseAndFormulaList]
  change eo_interprets M
    (__eo_mk_apply (Term.Apply (Term.UOp UserOp.eq) t) rhs) true
  rw [eo_mk_apply_eq_of_ne_stuck (Term.Apply (Term.UOp UserOp.eq) t) rhs
    (by simp) hRhsNN]
  exact hEqTrue

theorem smt_value_rel_model_eval_apply_of_rel
    (M : SmtModel) (hM : model_total_typed M)
    (f g x y : SmtTerm)
    (hAppNN : __smtx_typeof_apply (__smtx_typeof f) (__smtx_typeof x) ≠ SmtType.None)
    (hFy : __smtx_typeof f = __smtx_typeof g)
    (hXy : __smtx_typeof x = __smtx_typeof y)
    (hFRel : RuleProofs.smt_value_rel (__smtx_model_eval M f) (__smtx_model_eval M g))
    (hXRel : RuleProofs.smt_value_rel (__smtx_model_eval M x) (__smtx_model_eval M y)) :
    RuleProofs.smt_value_rel
      (__smtx_model_eval_apply (__smtx_model_eval M f) (__smtx_model_eval M x))
      (__smtx_model_eval_apply (__smtx_model_eval M g) (__smtx_model_eval M y)) := by
  rcases typeof_apply_non_none_cases hAppNN with
    ⟨A, B, hHead, hX, hA, _hB⟩
  have hFNN : term_has_non_none_type f := by
    unfold term_has_non_none_type
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hGNN : term_has_non_none_type g := by
    unfold term_has_non_none_type
    rw [← hFy]
    exact hFNN
  have hXNN : term_has_non_none_type x := by
    unfold term_has_non_none_type
    rw [hX]
    exact hA
  have hYNN : term_has_non_none_type y := by
    unfold term_has_non_none_type
    rw [← hXy]
    exact hXNN
  have hFPres :
      __smtx_typeof_value (__smtx_model_eval M f) = __smtx_typeof f :=
    smt_model_eval_preserves_type_of_non_none M hM f hFNN
  have hGPres :
      __smtx_typeof_value (__smtx_model_eval M g) = __smtx_typeof g :=
    smt_model_eval_preserves_type_of_non_none M hM g hGNN
  have hXPres :
      __smtx_typeof_value (__smtx_model_eval M x) = __smtx_typeof x :=
    smt_model_eval_preserves_type_of_non_none M hM x hXNN
  have hYPres :
      __smtx_typeof_value (__smtx_model_eval M y) = __smtx_typeof y :=
    smt_model_eval_preserves_type_of_non_none M hM y hYNN
  have hFNeReg : __smtx_typeof f ≠ SmtType.RegLan := by
    rcases hHead with hHead | hHead <;> rw [hHead] <;> simp
  have hArgField :
      TranslationProofs.smtx_type_field_wf_rec A native_reflist_nil := by
    have hDomains :=
      TranslationProofs.smtx_term_fun_like_domains_wf_of_non_none f hFNN
    exact TranslationProofs.smtx_type_fun_like_arg_field_wf_of_domains_wf hDomains hHead
  have hANeReg : A ≠ SmtType.RegLan :=
    TranslationProofs.smtx_type_field_wf_rec_ne_reglan hArgField
  have hFEq : __smtx_model_eval M f = __smtx_model_eval M g :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      hFPres (by simpa [hFy] using hGPres) hFNeReg hFRel
  have hXEq : __smtx_model_eval M x = __smtx_model_eval M y :=
    RuleProofs.smt_value_rel_eq_of_type_ne_reglan
      (by simpa [hX] using hXPres)
      (by
        rw [← hXy, hX] at hYPres
        exact hYPres)
      hANeReg hXRel
  rw [hFEq, hXEq]
  exact RuleProofs.smt_value_rel_refl _

end CongSupport
